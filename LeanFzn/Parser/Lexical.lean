/-
Purpose: Independent character-level relation for the declared non-float lexer.
Dependencies: Token's shared datatype and Lean core strings/UTF-8 encoding only.
DAG: Token -> Lexical; lexical correctness proofs import Lexical + Lexer.
No definition here calls a Lexer function, scanner, recognizer or byte decoder.
Policy: ASCII words; lowercase radix prefixes; greedy bounded escapes; comments
end at LF/EOF; raw LF and CR are excluded inside strings (R11). The executable
lexer is proved equivalent by Proofs/LexerCorrectness, including raw-CR rejection.
This specification is a declared subset/policy, not proved upstream equivalence.
-/
import LeanFzn.Parser.Token

namespace LeanFzn.Parser.Lexical
open LeanFzn.Parser.Lexer (Token)

/-- Explicit character classes, independent of implementation predicates. -/
def Space (c : Char) : Prop := c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '\r'
def Letter (c : Char) : Prop := ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z')
def Decimal (c : Char) : Prop := '0' ≤ c ∧ c ≤ '9'
def WordStart (c : Char) : Prop := Letter c ∨ c = '_'
def WordContinue (c : Char) : Prop := WordStart c ∨ Decimal c

/-- A run is maximal for its character class, or ends at EOF. -/
def Boundary (p : Char → Prop) : List Char → Prop
  | [] => True
  | c :: _ => ¬ p c

/-- Relational digit values. No call to digitValue or parseNatBase. -/
def Digit (base : Nat) (c : Char) (d : Nat) : Prop :=
  d < base ∧
    ((Decimal c ∧ d = c.toNat - '0'.toNat) ∨
     ('A' ≤ c ∧ c ≤ 'F' ∧ d = c.toNat - 'A'.toNat + 10) ∨
     ('a' ≤ c ∧ c ≤ 'f' ∧ d = c.toNat - 'a'.toNat + 10))

def BaseDigit (base : Nat) (c : Char) : Prop := ∃ d, Digit base c d

/-- Positional numeral meaning, rather than an accumulator-based scanner. -/
inductive Digits (base : Nat) : List Char → Nat → Prop where
  | nil : Digits base [] 0
  | cons (hd : Digit base c d) (ht : Digits base cs n) :
      Digits base (c :: cs) (d * base ^ cs.length + n)

/-- Prefix recognition commits to a radix even if subsequent digits are bad. -/
def RadixPrefix : List Char → Prop
  | '0' :: 'x' :: _ => True
  | '0' :: 'o' :: _ => True
  | _ => False

/-- Nonempty maximal magnitude. Decimal cannot steal the initial zero of a
radix literal; an incomplete radix prefix therefore has no lexical derivation.
Adjacent token spellings need no extra separator after numeric digits. -/
inductive Magnitude : List Char → Nat → List Char → Prop where
  | decimal (hne : ds ≠ []) (hd : Digits 10 ds n)
      (hstop : Boundary (BaseDigit 10) rest) (hp : ¬ RadixPrefix (ds ++ rest)) :
      Magnitude (ds ++ rest) n rest
  | hex (hne : ds ≠ []) (hd : Digits 16 ds n)
      (hstop : Boundary (BaseDigit 16) rest) :
      Magnitude ('0' :: 'x' :: (ds ++ rest)) n rest
  | octal (hne : ds ≠ []) (hd : Digits 8 ds n)
      (hstop : Boundary (BaseDigit 8) rest) :
      Magnitude ('0' :: 'o' :: (ds ++ rest)) n rest

/-- Entire-word classification from the pinned reserved-word inventory. -/
def Keywords : List (String × Token) :=
  [("predicate", .kwPredicate), ("array", .kwArray), ("of", .kwOf),
   ("var", .kwVar), ("set", .kwSet), ("constraint", .kwConstraint),
   ("solve", .kwSolve), ("satisfy", .kwSatisfy), ("minimize", .kwMinimize),
   ("maximize", .kwMaximize), ("bool", .kwBool), ("int", .kwInt),
   ("par", .kwPar), ("string", .kwString), ("annotation", .kwAnnotation),
   ("true", .boolLit true), ("false", .boolLit false)]

def Reserved : List String :=
  ["any", "case", "diff", "div", "else", "elseif", "endif", "enum", "float",
   "function", "if", "in", "include", "intersect", "let", "list", "mod",
   "not", "output", "record", "subset", "superset", "symdiff", "test",
   "then", "tuple", "type", "union", "where", "xor"]

inductive WordToken (word : List Char) : Token → Prop where
  | keyword (h : (String.ofList word, tok) ∈ Keywords) : WordToken word tok
  | identifier (hk : ∀ tok, (String.ofList word, tok) ∉ Keywords)
      (hr : String.ofList word ∉ Reserved) : WordToken word (.ident (String.ofList word))

/-- R11 escape bodies, starting AFTER the backslash. At most two hex digits
and three octal digits, greedily: a shorter spelling cannot leave an eligible
digit unread below the length limit. Octal overflow is rejected, not wrapped. -/
inductive Escape : List Char → UInt8 → List Char → Prop where
  | newline : Escape ('n' :: rest) 10 rest
  | tab : Escape ('t' :: rest) 9 rest
  | quote : Escape ('"' :: rest) 34 rest
  | backslash : Escape ('\\' :: rest) 92 rest
  | hex (hlen : 1 ≤ ds.length ∧ ds.length ≤ 2) (hd : Digits 16 ds n)
      (hstop : ds.length < 2 → Boundary (BaseDigit 16) rest) :
      Escape ('x' :: (ds ++ rest)) (UInt8.ofNat n) rest
  | octal (hlen : 1 ≤ ds.length ∧ ds.length ≤ 3) (hd : Digits 8 ds n)
      (hstop : ds.length < 3 → Boundary (BaseDigit 8) rest) (hbyte : n ≤ 255) :
      Escape (ds ++ rest) (UInt8.ofNat n) rest

/-- Canonical library UTF-8 ENCODING fixes byte meaning. The relation does
not call String.fromUTF8? or the lexer's decoding/validation routines. Proofs/LexerUTF8
establishes the decoder/encoder bridge constructively. -/
def EncodesUTF8 (bytes : List UInt8) (value : String) : Prop :=
  value.toUTF8.data.toList = bytes

/-- A quoted body's spelling yields bytes and consumes its closing quote.
Escaped newlines are permitted; literal LF/CR characters are not. Raw Unicode
characters contribute their canonical UTF-8 bytes. -/
inductive StringBody : List Char → List UInt8 → List Char → Prop where
  | close : StringBody ('"' :: rest) [] rest
  | plain (hq : c ≠ '"') (hb : c ≠ '\\') (hlf : c ≠ '\n') (hcr : c ≠ '\r')
      (hbody : StringBody cs bytes rest) :
      StringBody (c :: cs) ((String.singleton c).toUTF8.data.toList ++ bytes) rest
  | escape (he : Escape cs byte tail) (hbody : StringBody tail bytes rest) :
      StringBody ('\\' :: cs) (byte :: bytes) rest

/-- Single-character punctuation excludes ':' and '.', whose longest-match
rules are stated separately in Lexeme. -/
def Punctuation : List (Char × Token) :=
  [('(', .lParen), (')', .rParen), ('[', .lBrack), (']', .rBrack),
   ('{', .lBrace), ('}', .rBrace), (',', .comma), (';', .semi), ('=', .eq)]

/-- A significant lexical unit consumes a prefix and leaves the exact suffix.
There is no fallback constructor for bad characters, prefixes or escapes. -/
inductive Lexeme : List Char → Token → List Char → Prop where
  | punctuation (hp : (c, tok) ∈ Punctuation) : Lexeme (c :: rest) tok rest
  | colon (hnext : Boundary (fun c => c = ':') rest) : Lexeme (':' :: rest) .colon rest
  | colonColon : Lexeme (':' :: ':' :: rest) .colonColon rest
  | dotDot : Lexeme ('.' :: '.' :: rest) .dotDot rest
  | word (hstart : WordStart c) (hbody : ∀ d ∈ cs, WordContinue d)
      (hstop : Boundary WordContinue rest) (ht : WordToken (c :: cs) tok) :
      Lexeme ((c :: cs) ++ rest) tok rest
  | natural (hm : Magnitude cs n rest) : Lexeme cs (.intLit (n : Int)) rest
  | negative (hm : Magnitude cs n rest) : Lexeme ('-' :: cs) (.intLit (-(n : Int))) rest
  | string (hbody : StringBody cs bytes rest) (hu : EncodesUTF8 bytes value) :
      Lexeme ('"' :: cs) (.stringLit value) rest

/-- Whitespace and percent comments. LF ends a comment; CRLF is supported
because CR is part of the comment body before LF. A final comment consumes
through EOF. Quote/escape characters in comments have no lexical meaning. -/
inductive Trivia : List Char → List Char → Prop where
  | refl : Trivia cs cs
  | space (hs : Space c) (ht : Trivia cs rest) : Trivia (c :: cs) rest
  | commentLine (hbody : ∀ c ∈ body, c ≠ '\n') (ht : Trivia tail rest) :
      Trivia ('%' :: (body ++ '\n' :: tail)) rest
  | commentEOF (hbody : ∀ c ∈ body, c ≠ '\n') : Trivia ('%' :: body) []

/-- A whole source consumes ALL characters, including trailing trivia.
Trivia need not have a separate maximality premise: a significant Lexeme
cannot start on whitespace or '%', and the final constructor consumes to EOF. -/
inductive LexesChars : List Char → List Token → Prop where
  | done (ht : Trivia cs []) : LexesChars cs []
  | next (ht : Trivia cs significant) (hl : Lexeme significant tok tail)
      (hs : LexesChars tail toks) : LexesChars cs (tok :: toks)

/-- The external relation uses the actual tokenizer's result datatype, but
its definition mentions only characters, independent relations and token data. -/
def Lexes (text : String) (tokens : Array Token) : Prop :=
  LexesChars text.toList tokens.toList

end LeanFzn.Parser.Lexical

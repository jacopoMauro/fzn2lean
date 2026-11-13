/-
# FlatZinc Lexer (integer/Boolean fragment)

A total tokenizer for the non-float fragment of FlatZinc source text,
following the lexical rules of the vendored FlatZinc specification
(`specification/minizinc-2.10.0/fzn-spec.md`):

- Comments start with `%` and extend to the end of the line; they can appear
  anywhere.
- Syntax is insensitive to whitespace.
- Identifiers: `[A-Za-z][A-Za-z0-9_]*` (`<identifier>`) and
  `[A-Za-z_][A-Za-z0-9_]*` (`<var-par-identifier>`).  The lexer accepts the
  more permissive form; the parser checks the leading-underscore restriction
  where the grammar requires `<identifier>`.
- Int literals: `[-]?[0-9]+`, `[-]?0x[0-9A-Fa-f]+`, `[-]?0o[0-7]+`.
- Reserved keywords may not be used as identifiers.

- String escapes follow assumption R11 (`lexEscape`): `\"`, `\\`, `\n`,
  `\t`, `\x` with one or two hexadecimal digits, and one to three octal
  digits; any other escape (including `\(`), a physical newline, an
  unterminated literal, or decoded bytes that are not valid UTF-8 is an
  error.

Every function is total; termination is proved by the decreasing measure
`s.size - pos` (the number of unconsumed characters), and every successful
lexing step strictly advances the position: `lexUnsigned`, `lexInt`,
`lexEscape`, `lexString` and `lexToken` return the new position paired
with a proof `pos < p`.

The lexer is part of the trusted base of the recognition theorem:
`ValidFlatZinc` (in `FznGrammar.lean`) is defined over the token list
this lexer produces, so the parser/grammar correspondence is proved at
the token level and lexical validity is defined by this module.
-/

namespace LeanFzn.Parser.Lexer

/-- Token type for the non-float FlatZinc fragment. -/
inductive Token where
  -- punctuation
  | lParen | rParen          -- ( )
  | lBrack | rBrack          -- [ ]
  | lBrace | rBrace          -- { }
  | comma                    -- ,
  | colon                    -- :
  | semi                     -- ;
  | colonColon               -- ::
  | dotDot                   -- ..
  | eq                       -- =
  -- keywords used by FlatZinc
  | kwPredicate | kwArray | kwOf | kwVar | kwSet | kwConstraint
  | kwSolve | kwSatisfy | kwMinimize | kwMaximize
  | kwBool | kwInt | kwPar | kwString | kwAnnotation
  -- literals / identifiers
  | boolLit (b : Bool)       -- true / false
  | intLit (i : Int)
  | stringLit (s : String)   -- decoded contents
  | ident (s : String)       -- includes var-par identifiers (may start with _)
  deriving Repr, Inhabited, BEq, DecidableEq

/-- The reserved keywords of the spec that are *not* used in FlatZinc.
    An identifier matching one of these is rejected. -/
def reservedNonFzn : List String :=
  [ "any", "case", "diff", "div", "else", "elseif", "endif", "enum", "float",
    "function", "if", "in", "include", "intersect", "let", "list", "mod",
    "not", "output", "record", "subset", "superset", "symdiff", "test",
    "then", "tuple", "type", "union", "where", "xor" ]

/-- Map a word to a keyword token, or `none` if it is an identifier. -/
def keywordToken (w : String) : Option Token :=
  match w with
  | "predicate"  => some .kwPredicate
  | "array"      => some .kwArray
  | "of"         => some .kwOf
  | "var"        => some .kwVar
  | "set"        => some .kwSet
  | "constraint" => some .kwConstraint
  | "solve"      => some .kwSolve
  | "satisfy"    => some .kwSatisfy
  | "minimize"   => some .kwMinimize
  | "maximize"   => some .kwMaximize
  | "bool"       => some .kwBool
  | "int"        => some .kwInt
  | "par"        => some .kwPar
  | "string"     => some .kwString
  | "annotation" => some .kwAnnotation
  | "true"       => some (.boolLit true)
  | "false"      => some (.boolLit false)
  | _            => none

/-- Character classes. -/
def isAlpha (c : Char) : Bool := ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z')
def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'
def isHexDigit (c : Char) : Bool :=
  isDigit c || ('A' ≤ c && c ≤ 'F') || ('a' ≤ c && c ≤ 'f')
def isOctDigit (c : Char) : Bool := '0' ≤ c && c ≤ '7'
def isIdentChar (c : Char) : Bool := isAlpha c || isDigit c || c == '_'
def isWhitespace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- The input string as an array of characters, for simple index arithmetic. -/
abbrev Input := Array Char

/-- Skip to just past the next newline (or end of input). -/
def skipToNewline (s : Input) (pos : Nat) : Nat :=
  if h : pos < s.size then
    if s[pos] == '\n' then pos + 1
    else skipToNewline s (pos + 1)
  else pos
termination_by s.size - pos

theorem skipToNewline_ge (s : Input) (pos : Nat) : pos ≤ skipToNewline s pos := by
  induction pos using skipToNewline.induct (s := s) with
  | case1 pos h hn => rw [skipToNewline.eq_def]; simp [h, hn]
  | case2 pos h hn ih =>
      rw [skipToNewline.eq_def]; simp [h, hn]
      exact Nat.le_trans (Nat.le_succ _) ih
  | case3 pos h => rw [skipToNewline.eq_def]; simp [h]

/-- Skip whitespace and `%`-comments starting at position `pos`.
    Returns the position of the next significant character. -/
def skipTrivia (s : Input) (pos : Nat) : Nat :=
  if h : pos < s.size then
    let c := s[pos]
    if isWhitespace c then
      skipTrivia s (pos + 1)
    else if c == '%' then
      skipTrivia s (skipToNewline s (pos + 1))
    else
      pos
  else
    pos
termination_by s.size - pos
decreasing_by
  · exact Nat.sub_lt_sub_left h (Nat.lt_succ_self _)
  · have hge := skipToNewline_ge s (pos + 1)
    exact Nat.sub_lt_sub_left h (by omega)

/-- `skipTrivia` never moves the position backwards. -/
theorem skipTrivia_ge (s : Input) (pos : Nat) : pos ≤ skipTrivia s pos := by
  induction pos using skipTrivia.induct (s := s) with
  | case1 pos h c hw ih =>
      rw [skipTrivia.eq_def]; simp only [h, dif_pos]
      change pos ≤ (if isWhitespace c = true then skipTrivia s (pos + 1)
        else if (c == '%') = true then skipTrivia s (skipToNewline s (pos + 1)) else pos)
      rw [if_pos hw]
      exact Nat.le_trans (Nat.le_succ _) ih
  | case2 pos h c hw hc ih =>
      rw [skipTrivia.eq_def]; simp only [h, dif_pos]
      change pos ≤ (if isWhitespace c = true then skipTrivia s (pos + 1)
        else if (c == '%') = true then skipTrivia s (skipToNewline s (pos + 1)) else pos)
      rw [if_neg hw, if_pos hc]
      exact Nat.le_trans (Nat.le_succ _) (Nat.le_trans (skipToNewline_ge s _) ih)
  | case3 pos h c hw hc =>
      rw [skipTrivia.eq_def]; simp only [h, dif_pos]
      change pos ≤ (if isWhitespace c = true then skipTrivia s (pos + 1)
        else if (c == '%') = true then skipTrivia s (skipToNewline s (pos + 1)) else pos)
      rw [if_neg hw, if_neg hc]
      exact Nat.le_refl _
  | case4 pos h =>
      rw [skipTrivia.eq_def]
      split
      · rename_i hf; exact absurd hf (by simp [h])
      · exact Nat.le_refl _

/-- Scan an identifier/keyword body: `[A-Za-z0-9_]*`. -/
def takeWhile (p : Char → Bool) (s : Input) (pos : Nat) (acc : String) : String × Nat :=
  if h : pos < s.size then
    let c := s[pos]
    if p c then
      takeWhile p s (pos + 1) (acc.push c)
    else
      (acc, pos)
  else
    (acc, pos)
termination_by s.size - pos

/-- `takeWhile` never moves the end position before the start. -/
theorem takeWhile_ge (p : Char → Bool) (s : Input) (pos : Nat) (acc : String) :
    pos ≤ (takeWhile p s pos acc).2 := by
  induction pos, acc using takeWhile.induct (p := p) (s := s) with
  | case1 pos acc h c hp ih =>
      rw [takeWhile.eq_def]; simp only [h, dif_pos]
      change pos ≤ (if p c = true then takeWhile p s (pos + 1) (acc.push c) else (acc, pos)).2
      rw [if_pos hp]
      exact Nat.le_trans (Nat.le_succ _) ih
  | case2 pos acc h c hp =>
      rw [takeWhile.eq_def]; simp only [h, dif_pos]
      change pos ≤ (if p c = true then takeWhile p s (pos + 1) (acc.push c) else (acc, pos)).2
      rw [if_neg hp]
      exact Nat.le_refl _
  | case3 pos acc h =>
      rw [takeWhile.eq_def]
      split
      · rename_i hf; exact absurd hf (by simp [h])
      · exact Nat.le_refl _

/-- The length of the string produced by `takeWhile` equals the accumulator
    length plus the number of characters consumed. -/
theorem takeWhile_length (p : Char → Bool) (s : Input) (pos : Nat) (acc : String) :
    (takeWhile p s pos acc).1.length = acc.length + ((takeWhile p s pos acc).2 - pos) := by
  induction pos, acc using takeWhile.induct (p := p) (s := s) with
  | case1 pos acc h c hp ih =>
      rw [takeWhile.eq_def]; simp only [h, dif_pos]
      change (if p c = true then takeWhile p s (pos + 1) (acc.push c) else (acc, pos)).1.length
        = acc.length + ((if p c = true then takeWhile p s (pos + 1) (acc.push c) else (acc, pos)).2 - pos)
      rw [if_pos hp]
      have hlp : (acc.push c).length = acc.length + 1 := String.length_push c
      have hrec := ih
      have hge : pos + 1 ≤ (takeWhile p s (pos + 1) (acc.push c)).2 :=
        takeWhile_ge p s (pos + 1) (acc.push c)
      omega
  | case2 pos acc h c hp =>
      rw [takeWhile.eq_def]; simp only [h, dif_pos]
      change (if p c = true then takeWhile p s (pos + 1) (acc.push c) else (acc, pos)).1.length
        = acc.length + ((if p c = true then takeWhile p s (pos + 1) (acc.push c) else (acc, pos)).2 - pos)
      rw [if_neg hp]; simp
  | case3 pos acc h =>
      rw [takeWhile.eq_def]
      split
      · rename_i hf; exact absurd hf (by simp [h])
      · simp

/-- The value of a digit character (decimal or hexadecimal, either case). -/
def digitValue (c : Char) : Nat :=
  if isDigit c then c.toNat - '0'.toNat
  else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else c.toNat - 'a'.toNat + 10

/-- Parse a natural number from a string of digits in the given base
    (no prefix). -/
def parseNatBase (base : Nat) (ds : String) : Nat :=
  ds.foldl (fun n c => n * base + digitValue c) 0

/-- The digit class, base, prefix length and name of the integer literal
    whose magnitude starts at `pos`: hexadecimal after `0x`, octal after
    `0o`, decimal otherwise. -/
def intFormat (s : Input) (pos : Nat) : (Char → Bool) × Nat × Nat × String :=
  if pos + 1 < s.size && s[pos]! == '0' && s[pos+1]! == 'x' then
    (isHexDigit, 16, 2, "hexadecimal")
  else if pos + 1 < s.size && s[pos]! == '0' && s[pos+1]! == 'o' then
    (isOctDigit, 8, 2, "octal")
  else
    (isDigit, 10, 0, "integer")

/-- A non-empty `takeWhile` result means the scan advanced. -/
theorem takeWhile_gt_of_ne_empty (p : Char → Bool) (s : Input) (pos : Nat)
    (h : (takeWhile p s pos "").1.isEmpty = false) : pos < (takeWhile p s pos "").2 := by
  have hlen := takeWhile_length p s pos ""
  have hpos : (takeWhile p s pos "").1.length ≠ 0 := by
    intro hl
    have : (takeWhile p s pos "").1 = "" := String.length_eq_zero_iff.mp hl
    rw [this] at h
    simp at h
  simp only [String.length_empty, Nat.zero_add] at hlen
  omega

/-- Lex the unsigned magnitude of an integer literal starting at `pos`
    (which must be a digit).  Handles decimal, hexadecimal (`0x`) and octal
    (`0o`) forms.  Returns the value and the position after it, which is
    strictly greater than `pos`. -/
def lexUnsigned (s : Input) (pos : Nat) : Except String (Int × { p : Nat // pos < p }) :=
  let (digit, base, offset, kind) := intFormat s pos
  if hne : (takeWhile digit s (pos + offset) "").1.isEmpty then
    .error s!"invalid {kind} literal at position {pos}"
  else
    .ok ((parseNatBase base (takeWhile digit s (pos + offset) "").1 : Int),
      ⟨(takeWhile digit s (pos + offset) "").2, by
        have := takeWhile_gt_of_ne_empty digit s (pos + offset) (by simpa using hne)
        omega⟩)

/-- Lex an integer literal starting at `pos` (first char is a digit or `-`).
    Returns the token and the position after it. -/
def lexInt (s : Input) (pos : Nat) : Except String (Token × { p : Nat // pos < p }) :=
  if pos < s.size && s[pos]! == '-' then
    match lexUnsigned s (pos + 1) with
    | .ok (n, ⟨p, hp⟩) => .ok (.intLit (-n), ⟨p, by omega⟩)
    | .error e => .error e
  else
    match lexUnsigned s pos with
    | .ok (n, p) => .ok (.intLit n, p)
    | .error e => .error e

/-- Up to `n` consecutive characters satisfying `p`, starting at `pos`. -/
def digitsUpTo (p : Char → Bool) (s : Input) (pos : Nat) : Nat → List Char
  | 0 => []
  | n + 1 =>
    if h : pos < s.size then
      if p s[pos] then s[pos] :: digitsUpTo p s (pos + 1) n else []
    else []

/-- Decode the escape sequence whose body starts at `pos` (just after the
    backslash), following R11: `\"`, `\\`, `\n`, `\t`, `\x` with one or
    two hexadecimal digits, and one to three octal digits (at most 255).
    Returns the decoded byte and the position after the escape, or `none`
    for any other escape — including `\(` (MiniZinc string interpolation)
    and a backslash before a newline or the end of input. -/
def lexEscape (s : Input) (pos : Nat) : Option (UInt8 × { p : Nat // pos < p }) :=
  if h : pos < s.size then
    match s[pos] with
    | 'n' => some (10, ⟨pos + 1, by omega⟩)
    | 't' => some (9, ⟨pos + 1, by omega⟩)
    | '"' => some (34, ⟨pos + 1, by omega⟩)
    | '\\' => some (92, ⟨pos + 1, by omega⟩)
    | 'x' =>
      let ds := digitsUpTo isHexDigit s (pos + 1) 2
      if ds.isEmpty then none
      else some ((parseNatBase 16 (String.ofList ds)).toUInt8, ⟨pos + 1 + ds.length, by omega⟩)
    | c =>
      if isOctDigit c then
        let ds := digitsUpTo isOctDigit s pos 3
        let v := parseNatBase 8 (String.ofList ds)
        if v ≤ 255 then some (v.toUInt8, ⟨pos + max ds.length 1, by omega⟩) else none
      else none
  else none

/-- Lex a string literal starting just after the opening quote (R11).
    Decoded bytes accumulate in `acc`; at the closing quote they must form
    valid UTF-8.  Physical newlines, invalid escapes and unterminated
    literals are errors.  Returns the decoded contents and the position
    after the closing quote. -/
def lexString (s : Input) (pos : Nat) (acc : ByteArray) :
    Except String (String × { p : Nat // pos < p }) :=
  if h : pos < s.size then
    let c := s[pos]
    if c == '"' then
      match String.fromUTF8? acc with
      | some str => .ok (str, ⟨pos + 1, by omega⟩)
      | none => .error s!"string literal ending at position {pos} is not valid UTF-8"
    else if c == '\\' then
      match lexEscape s (pos + 1) with
      | some (b, ⟨p, hp⟩) =>
        match lexString s p (acc.push b) with
        | .ok (str, ⟨p', hp'⟩) => .ok (str, ⟨p', by omega⟩)
        | .error e => .error e
      | none => .error s!"invalid escape sequence in string literal at position {pos}"
    else if c == '\n' then
      .error s!"newline in string literal at position {pos}"
    else
      match lexString s (pos + 1) (acc ++ (String.singleton c).toUTF8) with
      | .ok (str, ⟨p', hp'⟩) => .ok (str, ⟨p', by omega⟩)
      | .error e => .error e
  else
    .error s!"unterminated string literal at position {pos}"
termination_by s.size - pos

/-- Lex a single token starting at a significant (non-trivia) position.
    The returned position is strictly greater than `pos` (progress). -/
def lexToken (s : Input) (pos : Nat) (h : pos < s.size) :
    Except String (Token × { p : Nat // pos < p }) := do
  let c := s[pos]
  match c with
  | '(' => return (.lParen, ⟨pos + 1, Nat.lt_succ_self pos⟩)
  | ')' => return (.rParen, ⟨pos + 1, Nat.lt_succ_self pos⟩)
  | '[' => return (.lBrack, ⟨pos + 1, Nat.lt_succ_self pos⟩)
  | ']' => return (.rBrack, ⟨pos + 1, Nat.lt_succ_self pos⟩)
  | '{' => return (.lBrace, ⟨pos + 1, Nat.lt_succ_self pos⟩)
  | '}' => return (.rBrace, ⟨pos + 1, Nat.lt_succ_self pos⟩)
  | ',' => return (.comma, ⟨pos + 1, Nat.lt_succ_self pos⟩)
  | ';' => return (.semi, ⟨pos + 1, Nat.lt_succ_self pos⟩)
  | '=' => return (.eq, ⟨pos + 1, Nat.lt_succ_self pos⟩)
  | ':' =>
    if pos + 1 < s.size && s[pos + 1]! == ':' then
      return (.colonColon, ⟨pos + 2, by omega⟩)
    else
      return (.colon, ⟨pos + 1, Nat.lt_succ_self pos⟩)
  | '.' =>
    if pos + 1 < s.size && s[pos + 1]! == '.' then
      return (.dotDot, ⟨pos + 2, by omega⟩)
    else
      throw s!"unexpected character '.' at position {pos}"
  | '"' =>
    match lexString s (pos + 1) .empty with
    | .ok (str, ⟨p, hp⟩) => .ok (.stringLit str, ⟨p, by omega⟩)
    | .error e => .error e
  | _ =>
    if isAlpha c || c == '_' then
      match ht : takeWhile isIdentChar s (pos + 1) (String.singleton c) with
      | (w, p) =>
      have hp : pos < p := by
        have hge : pos + 1 ≤ (takeWhile isIdentChar s (pos + 1) (String.singleton c)).2 :=
          takeWhile_ge isIdentChar s (pos + 1) (String.singleton c)
        rw [ht] at hge
        simp only at hge
        omega
      match keywordToken w with
      | some t => return (t, ⟨p, hp⟩)
      | none =>
        if reservedNonFzn.contains w then
          throw s!"reserved keyword '{w}' cannot be used as an identifier (position {pos})"
        else
          return (.ident w, ⟨p, hp⟩)
    else if isDigit c || c == '-' then
      lexInt s pos
    else
      throw s!"unexpected character '{c}' at position {pos}"

/-- Tokenize the whole input.  Total: each iteration consumes at least one
    character, so `s.size - pos` strictly decreases. -/
def tokenizeAux (s : Input) (pos : Nat) (acc : Array Token) :
    Except String (Array Token) := do
  let p := skipTrivia s pos
  if h : p < s.size then
    let (tok, ⟨p', hp'⟩) ← lexToken s p h
    have : s.size - p' < s.size - pos := by
      have hge : pos ≤ p := skipTrivia_ge s pos
      omega
    tokenizeAux s p' (acc.push tok)
  else
    return acc
termination_by s.size - pos

/-- Tokenize a FlatZinc source string.  The source is decoded directly to
    the `Array Char` the lexer consumes: `String.toList.toArray` would build
    an intermediate `List Char` and a second array, dominating the parse peak
    on large inputs.  The direct decode is definitionally equal to the old
    body (`String.toList` unfolds to `(String.Internal.toArray s).toList`,
    and `Array.toArray_toList` is `rfl`), so the token sequence and every
    parser proof are unchanged. -/
def tokenize (src : String) : Except String (Array Token) :=
  tokenizeAux (String.Internal.toArray src) 0 #[]

end LeanFzn.Parser.Lexer

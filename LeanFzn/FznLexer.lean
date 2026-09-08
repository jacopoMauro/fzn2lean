/-
# FlatZinc Lexer (integer/Boolean fragment)

A total tokenizer for the non-float fragment of FlatZinc source text,
following the lexical rules of `specification/flatzinc_specification.rst`:

- Comments start with `%` and extend to the end of the line; they can appear
  anywhere.
- Syntax is insensitive to whitespace.
- Identifiers: `[A-Za-z][A-Za-z0-9_]*` (`<identifier>`) and
  `[A-Za-z_][A-Za-z0-9_]*` (`<var-par-identifier>`).  The lexer accepts the
  more permissive form; the parser checks the leading-underscore restriction
  where the grammar requires `<identifier>`.
- Int literals: `[-]?[0-9]+`, `[-]?0x[0-9A-Fa-f]+`, `[-]?0o[0-7]+`.
- String literals: C-style, double-quoted, with backslash escapes.
- Reserved keywords may not be used as identifiers.

Every function is total; termination is proved by the decreasing measure
`s.size - pos` (the number of unconsumed characters), and every successful
lexing step strictly advances the position (proved in `lexToken_gt`).
-/

namespace LeanFzn.Lexer

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

/-- Parse a decimal natural from a string of digits. -/
def parseDecNat (ds : String) : Nat :=
  ds.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0

/-- Parse a hexadecimal natural (digits only, no `0x` prefix). -/
def parseHexNat (ds : String) : Nat :=
  ds.foldl (fun n c =>
    let d :=
      if isDigit c then c.toNat - '0'.toNat
      else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
      else c.toNat - 'a'.toNat + 10
    n * 16 + d) 0

/-- Parse an octal natural (digits only, no `0o` prefix). -/
def parseOctNat (ds : String) : Nat :=
  ds.foldl (fun n c => n * 8 + (c.toNat - '0'.toNat)) 0

/-- Lex the unsigned magnitude of an integer literal starting at `pos`
    (which must be a digit).  Handles decimal, hexadecimal (`0x`) and octal
    (`0o`) forms.  Returns the value and the position after it. -/
def lexUnsigned (s : Input) (pos : Nat) : Except String (Int × Nat) :=
  if pos + 1 < s.size && s[pos]! == '0' && s[pos+1]! == 'x' then
    if (takeWhile isHexDigit s (pos + 2) "").1.isEmpty then
      .error s!"invalid hexadecimal literal at position {pos}"
    else
      .ok ((parseHexNat (takeWhile isHexDigit s (pos + 2) "").1 : Int),
           (takeWhile isHexDigit s (pos + 2) "").2)
  else if pos + 1 < s.size && s[pos]! == '0' && s[pos+1]! == 'o' then
    if (takeWhile isOctDigit s (pos + 2) "").1.isEmpty then
      .error s!"invalid octal literal at position {pos}"
    else
      .ok ((parseOctNat (takeWhile isOctDigit s (pos + 2) "").1 : Int),
           (takeWhile isOctDigit s (pos + 2) "").2)
  else
    if (takeWhile isDigit s pos "").1.isEmpty then
      .error s!"invalid integer literal at position {pos}"
    else
      .ok ((parseDecNat (takeWhile isDigit s pos "").1 : Int),
           (takeWhile isDigit s pos "").2)

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

/-- If `takeWhile` produces a string longer than the accumulator, it advanced. -/
theorem takeWhile_gt_of_longer (p : Char → Bool) (s : Input) (pos : Nat) (acc : String) :
    acc.length < (takeWhile p s pos acc).1.length → pos < (takeWhile p s pos acc).2 := by
  intro hlen
  have hlen_eq := takeWhile_length p s pos acc
  omega

/-- `lexUnsigned` strictly advances the position when it succeeds (it consumes
    at least one digit, or the `0x`/`0o` prefix plus digits). -/
theorem lexUnsigned_gt (s : Input) (pos : Nat) (n : Int) (p : Nat) :
    lexUnsigned s pos = .ok (n, p) → pos < p := by
  intro h
  rw [lexUnsigned.eq_def] at h
  split at h
  · -- hex
    split at h
    · contradiction
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      have := takeWhile_ge isHexDigit s (pos + 2) ""
      omega
  · split at h
    · -- octal
      split at h
      · contradiction
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        have := takeWhile_ge isOctDigit s (pos + 2) ""
        omega
    · -- decimal: the digit string is non-empty, so takeWhile advanced
      split at h
      · contradiction
      · rename_i hne
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        apply takeWhile_gt_of_longer
        -- the result string is non-empty, hence longer than the empty accumulator
        have hne' : (takeWhile isDigit s pos "").1.isEmpty = false :=
          Bool.not_eq_true _ ▸ hne
        have hpos : (takeWhile isDigit s pos "").1 ≠ "" := by
          intro he
          have : (takeWhile isDigit s pos "").1.isEmpty = true :=
            String.isEmpty_iff.mpr he
          rw [this] at hne'
          simp at hne'
        have hlen : (takeWhile isDigit s pos "").1.length ≠ 0 := by
          intro hl
          exact hpos (String.length_eq_zero_iff.mp hl)
        have : 0 < (takeWhile isDigit s pos "").1.length := Nat.pos_of_ne_zero hlen
        simpa using this

/-- Lex an integer literal starting at `pos` (first char is a digit or `-`).
    Returns the token and the position after it. -/
def lexInt (s : Input) (pos : Nat) : Except String (Token × Nat) :=
  if pos < s.size && s[pos]! == '-' then
    match lexUnsigned s (pos + 1) with
    | .ok (n, p1) => .ok (.intLit (-n), p1)
    | .error e => .error e
  else
    match lexUnsigned s pos with
    | .ok (n, p1) => .ok (.intLit n, p1)
    | .error e => .error e

/-- `lexInt` strictly advances the position when it succeeds. -/
theorem lexInt_gt (s : Input) (pos : Nat) (t : Token) (p : Nat) :
    lexInt s pos = .ok (t, p) → pos < p := by
  intro h
  rw [lexInt.eq_def] at h
  split at h
  · -- leading '-'
    split at h
    · rename_i n p1 hu
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      have := lexUnsigned_gt s (pos + 1) n p1 hu
      omega
    · contradiction
  · -- no '-'
    split at h
    · rename_i n p1 hu
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      have := lexUnsigned_gt s pos n p1 hu
      omega
    · contradiction

/-- Lex a string literal starting just after the opening quote.
    Returns the decoded contents and the position after the closing quote. -/
def lexString (s : Input) (pos : Nat) (acc : String) : Except String (String × Nat) := do
  if h : pos < s.size then
    let c := s[pos]
    if c == '"' then
      return (acc, pos + 1)
    else if c == '\\' then
      if pos + 1 < s.size then
        let e := s[pos + 1]!
        let decoded : Char :=
          match e with
          | 'n' => '\n'
          | 't' => '\t'
          | 'r' => '\r'
          | '\\' => '\\'
          | '"' => '"'
          | '\'' => '\''
          | _ => e  -- other escapes: keep the escaped character literally
        lexString s (pos + 2) (acc.push decoded)
      else
        throw s!"unterminated string literal at position {pos}"
    else if c == '\n' then
      throw s!"newline in string literal at position {pos}"
    else
      lexString s (pos + 1) (acc.push c)
  else
    throw s!"unterminated string literal at position {pos}"
termination_by s.size - pos

/-- `lexString` never moves the end position before the start. -/
theorem lexString_ge (s : Input) (pos : Nat) (acc : String) (w : String) (p : Nat) :
    lexString s pos acc = .ok (w, p) → pos ≤ p := by
  induction pos, acc using lexString.induct (s := s) with
  | case1 pos acc h c hq =>
    intro hr
    rw [lexString.eq_def] at hr
    simp only [h, dif_pos] at hr
    change (if (c == '"') = true then Except.ok (acc, pos + 1) else _) = Except.ok (w, p) at hr
    rw [if_pos hq] at hr
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨_, rfl⟩ := hr
    exact Nat.le_succ _
  | case2 pos acc h c hq hbs ih1 =>
    rename_i e ihs
    intro hr
    rw [lexString.eq_def] at hr
    simp only [h, dif_pos] at hr
    change (if (c == '"') = true then Except.ok (acc, pos + 1)
      else if (c == '\\') = true then _ else _) = Except.ok (w, p) at hr
    rw [if_neg hq, if_pos hbs] at hr
    split at hr
    · exact Nat.le_trans (by omega) (ihs hr)
    · contradiction
  | case3 pos acc h c hq hbs =>
    intro hr
    rw [lexString.eq_def] at hr
    simp only [h, dif_pos] at hr
    change (if (c == '"') = true then Except.ok (acc, pos + 1)
      else if (c == '\\') = true then _ else _) = Except.ok (w, p) at hr
    rw [if_neg hq, if_pos hbs] at hr
    split at hr
    · rename_i hlt; exact absurd hlt (by assumption)
    · contradiction
  | case4 pos acc h c hq hbs hn =>
    intro hr
    rw [lexString.eq_def] at hr
    simp only [h, dif_pos] at hr
    change (if (c == '"') = true then Except.ok (acc, pos + 1)
      else if (c == '\\') = true then _
      else if (c == '\n') = true then _
      else _) = Except.ok (w, p) at hr
    rw [if_neg hq, if_neg hbs, if_pos hn] at hr
    contradiction
  | case5 pos acc h c hq hbs hn ih =>
    intro hr
    rw [lexString.eq_def] at hr
    simp only [h, dif_pos] at hr
    change (if (c == '"') = true then Except.ok (acc, pos + 1)
      else if (c == '\\') = true then _
      else if (c == '\n') = true then _
      else _) = Except.ok (w, p) at hr
    rw [if_neg hq, if_neg hbs, if_neg hn] at hr
    exact Nat.le_trans (Nat.le_succ _) (ih hr)
  | case6 pos acc h =>
    intro hr
    rw [lexString.eq_def] at hr
    split at hr
    · rename_i hf; exact absurd hf (by simp [h])
    · contradiction

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
    match hs : lexString s (pos + 1) "" with
    | .ok (str, p) =>
      .ok (.stringLit str, ⟨p, by
        have hge := lexString_ge s (pos + 1) "" str p hs
        omega⟩)
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
      match hi : lexInt s pos with
      | .ok (t, p) => .ok (t, ⟨p, lexInt_gt s pos t p hi⟩)
      | .error e => .error e
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

/-- Tokenize a FlatZinc source string. -/
def tokenize (src : String) : Except String (Array Token) :=
  tokenizeAux src.toList.toArray 0 #[]

end LeanFzn.Lexer

import LeanFzn.FznAST
import LeanFzn.FznLexer

/-
# FlatZinc Parser (integer/Boolean fragment)

A recursive-descent parser over the token array produced by `Lexer.tokenize`.
There is one parsing function per non-terminal of the grammar, following the
BNF of `fzn-grammar.mzn` literally.

## Totality via fuel

The grammar is mutually recursive (expressions contain arrays of expressions;
annotations contain annotation expressions which may be nested annotations).
Rather than proving a decreasing measure through the mutual recursion, every
parsing function takes a `fuel : Nat` and is structurally recursive on it.
This makes totality immediate: each function either consumes a token or
decreases the fuel.

Because the token stream is finite, a sufficiently large fuel always exists
(`parseModel` uses `toks.size + 1` fuel per token, which bounds the recursion
depth).  The correctness theorems in `FznCorrectness.lean` relate the fuelled
parser to the grammar.
-/

namespace LeanFzn.Parser

open LeanFzn.Lexer

/-- Parser state: the token array and the current position. -/
structure State where
  toks : Array Token
  pos : Nat
  deriving Inhabited

/-- Advance the position by one. -/
def State.advance (st : State) : State := { st with pos := st.pos + 1 }

/-- Peek at the current token, if any. -/
def State.peek? (st : State) : Option Token :=
  if h : st.pos < st.toks.size then some st.toks[st.pos] else none

/-- The remaining (unconsumed) tokens of a parser state, as a list.  This is
    the bridge between the array-based parser state and the list-based grammar
    relation. -/
def State.remaining (st : State) : List Token := st.toks.toList.drop st.pos

/-- `remaining` of a state with position `0` is the whole token list. -/
theorem State.remaining_zero (st : State) (h : st.pos = 0) :
    st.remaining = st.toks.toList := by
  unfold State.remaining; rw [h, List.drop_zero]

/-- Advancing consumes exactly one token from the front of `remaining`. -/
theorem State.remaining_advance (st : State) (_h : st.pos < st.toks.size) :
    st.advance.remaining = st.remaining.tail := by
  unfold State.remaining State.advance
  simp [List.tail_drop]

/-- Consume the current token if it satisfies `pred`, failing otherwise. -/
def expect (pred : Token → Bool) (what : String) (st : State) : Except String (Token × State) :=
  if h : st.pos < st.toks.size then
    let t := st.toks[st.pos]
    if pred t then
      .ok (t, st.advance)
    else
      .error s!"expected {what} at token {st.pos}"
  else
    .error s!"unexpected end of input, expected {what}"

/-! ## BEq/decEq bridge for `Token`

The lexer's `Token` has both a derived `BEq` and a derived `DecidableEq`;
they agree (both are structural).  `token_beq_eq_decide` is the reusable
bridge, needed to relate the parser's decidable-equality checks with
Boolean equality tests. -/

private theorem boolPair (x y : Bool) :
    (Token.boolLit x == Token.boolLit y) = decide (Token.boolLit x = Token.boolLit y) := by
  cases x <;> cases y <;> rfl

private theorem intPair (x y : Int) :
    (Token.intLit x == Token.intLit y) = decide (Token.intLit x = Token.intLit y) := by
  rw [show (Token.intLit x == Token.intLit y) = (x == y) from rfl,
      show decide (Token.intLit x = Token.intLit y) = decide (x = y) from by
        simp only [Token.intLit.injEq]]
  cases x <;> cases y <;> rfl

private theorem strPair (x y : String) :
    (Token.stringLit x == Token.stringLit y) =
      decide (Token.stringLit x = Token.stringLit y) := by
  rw [show (Token.stringLit x == Token.stringLit y) = (x == y) from rfl,
      show decide (Token.stringLit x = Token.stringLit y) = decide (x = y) from by
        simp only [Token.stringLit.injEq]]
  cases x <;> cases y <;> rfl

private theorem identPair (x y : String) :
    (Token.ident x == Token.ident y) = decide (Token.ident x = Token.ident y) := by
  rw [show (Token.ident x == Token.ident y) = (x == y) from rfl,
      show decide (Token.ident x = Token.ident y) = decide (x = y) from by
        simp only [Token.ident.injEq]]
  cases x <;> cases y <;> rfl

/-- The derived `BEq` and `DecidableEq` on `Token` agree. -/
theorem token_beq_eq_decide (a b : Token) : (a == b) = decide (a = b) := by
  cases a <;> cases b <;> first
    | rfl
    | (rename_i x y; exact boolPair x y)
    | (rename_i x y; exact intPair x y)
    | (rename_i x y; exact strPair x y)
    | (rename_i x y; exact identPair x y)

/-! ### Compilation safeguard for `expectTok`

`expectTok` is the workhorse of the parser: several calls per item,
each on the hot path.  Its body decides equality through
`DecidableEq Token`, whose derived implementation dispatches on
constructor indices; the fast twin below decides the same through the
derived `BEq` (also structural).  `expectTokFast_eq` proves the two
bodies equal, and `@[implemented_by]` swaps the compiled code — the
kernel and every proof keep seeing the original definition.  (Same
trust model as the `StoreBox`/`completedBox` fix in
`FznSolution.lean`.) -/

/-- Fast twin of `expectTok` (BEq-decided). -/
private def expectTokFast (t : Token) (what : String) (st : State) : Except String State :=
  if h : st.pos < st.toks.size then
    if st.toks[st.pos] == t then
      .ok { st with pos := st.pos + 1 }
    else
      .error s!"expected {what} at token {st.pos}"
  else
    .error s!"unexpected end of input, expected {what}"

/-- The fast twin computes the same function as the `expectTok` body
    (restated here; the real `expectTok` is defined below). -/
private theorem expectTokFast_eq (t : Token) (what : String) (st : State) :
    expectTokFast t what st =
      (if h : st.pos < st.toks.size then
        if st.toks[st.pos] = t then
          .ok st.advance
        else
          .error s!"expected {what} at token {st.pos}"
      else
        .error s!"unexpected end of input, expected {what}") := by
  unfold expectTokFast
  split
  · next hlt =>
      have hb := token_beq_eq_decide st.toks[st.pos] t
      rw [hb]
      cases hdec : decide (st.toks[st.pos] = t)
      · rw [if_neg (decide_eq_false_iff_not.mp hdec)]
        simp
      · rw [if_pos (decide_eq_true_iff.mp hdec)]
        simp [State.advance]
  · simp

/-- Consume a specific token, matching by decidable equality. -/
@[implemented_by expectTokFast]
def expectTok (t : Token) (what : String) (st : State) : Except String State :=
  if h : st.pos < st.toks.size then
    if st.toks[st.pos] = t then
      .ok st.advance
    else
      .error s!"expected {what} at token {st.pos}"
  else
    .error s!"unexpected end of input, expected {what}"

theorem expectTok_eq_fast (t : Token) (what : String) (st : State) :
    expectTok t what st = expectTokFast t what st := by
  unfold expectTok
  exact (expectTokFast_eq t what st).symm

/-- Parse an identifier token (any `[A-Za-z_][A-Za-z0-9_]*`). -/
def parseIdent (st : State) : Except String (Ident × State) :=
  match expect (fun t => match t with | .ident _ => true | _ => false) "identifier" st with
  | .ok (.ident s, st') => .ok (⟨s⟩, st')
  | .ok _ => .error "impossible"
  | .error e => .error e

/-- Parse a `<identifier>` (no leading underscore). -/
def parsePredIdent (st : State) : Except String (Ident × State) :=
  match parseIdent st with
  | .ok (x, st') =>
    if x.name.startsWith "_" then
      .error s!"identifier '{x.name}' may not start with an underscore here"
    else
      .ok (x, st')
  | .error e => .error e

/-- Parse an integer literal token. -/
def parseIntLit (st : State) : Except String (Int × State) :=
  match expect (fun t => match t with | .intLit _ => true | _ => false) "integer literal" st with
  | .ok (.intLit i, st') => .ok (i, st')
  | .ok _ => .error "impossible"
  | .error e => .error e

/-- Parse a boolean literal token. -/
def parseBoolLit (st : State) : Except String (Bool × State) :=
  match expect (fun t => match t with | .boolLit _ => true | _ => false) "boolean literal" st with
  | .ok (.boolLit b, st') => .ok (b, st')
  | .ok _ => .error "impossible"
  | .error e => .error e

/-- Parse a string literal token. -/
def parseStringLit (st : State) : Except String (String × State) :=
  match expect (fun t => match t with | .stringLit _ => true | _ => false) "string literal" st with
  | .ok (.stringLit s, st') => .ok (s, st')
  | .ok _ => .error "impossible"
  | .error e => .error e

/-- Is the current token the given one? -/
def check (t : Token) (st : State) : Bool :=
  match st.peek? with
  | some t' => t' = t
  | none => false

/- The fuelled, mutually-recursive parser functions. -/
mutual

/-- `<set-literal>` (int fragment): `"{" [ ints ] "}"` or `i ".." j`. -/
def parseSetLiteral (fuel : Nat) (st : State) : Except String (SetLiteral × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  match st.peek? with
  | some .lBrace =>
    let st ← expectTok .lBrace "'{'" st
    let (elems, st) ← parseIntList fuel st
    let st ← expectTok .rBrace "'}'" st
    return (.intSet elems, st)
  | some (.intLit _) =>
    let (lo, st) ← parseIntLit st
    let st ← expectTok .dotDot "'..'" st
    let (hi, st) ← parseIntLit st
    return (.intRange lo hi, st)
  | _ => .error s!"expected set literal at token {st.pos}"

/-- A comma-separated list of integer literals (possibly empty). -/
def parseIntList (fuel : Nat) (st : State) : Except String ((List Int) × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  match st.peek? with
  | some (.intLit _) =>
    let (i, st) ← parseIntLit st
    let (rest, st) ← parseIntListTail fuel st
    return (i :: rest, st)
  | _ => return ([], st)

/-- The `"," int` continuation of an integer list. -/
def parseIntListTail (fuel : Nat) (st : State) : Except String ((List Int) × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  match st.peek? with
  | some .comma =>
    let st ← expectTok .comma "','" st
    let (i, st) ← parseIntLit st
    let (rest, st) ← parseIntListTail fuel st
    return (i :: rest, st)
  | _ => return ([], st)

/-- A comma-separated, non-empty list of integer literals. -/
def parseNonemptyIntList (fuel : Nat) (st : State) : Except String ((List Int) × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
    let (i, st) ← parseIntLit st
    let (rest, st) ← parseIntListTail fuel st
    return (i :: rest, st)

/-- `<basic-literal-expr>` (int fragment). -/
def parseBasicLiteral (fuel : Nat) (st : State) : Except String (BasicLiteral × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  match st.peek? with
  | some (.boolLit _) =>
    let (b, st) ← parseBoolLit st
    return (.bool b, st)
  | some (.intLit _) =>
    -- could be an int or the start of an int range set
    let (i, st₁) ← parseIntLit st
    if check .dotDot st₁ then
      let st₂ ← expectTok .dotDot "'..'" st₁
      let (hi, st₃) ← parseIntLit st₂
      return (.set (.intRange i hi), st₃)
    else
      return (.int i, st₁)
  | some .lBrace =>
    let (s, st) ← parseSetLiteral fuel st
    return (.set s, st)
  | _ => .error s!"expected literal at token {st.pos}"

/-- `<basic-expr>`. -/
def parseBasicExpr (fuel : Nat) (st : State) : Except String (BasicExpr × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  match st.peek? with
  | some (.ident _) =>
    let (x, st) ← parseIdent st
    return (.ident x, st)
  | _ =>
    let (l, st) ← parseBasicLiteral fuel st
    return (.lit l, st)

/-- `<array-literal> ::= "[" [ <basic-expr> "," ... ] "]"`. -/
def parseArrayLiteral (fuel : Nat) (st : State) : Except String (ArrayLiteral × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  let st ← expectTok .lBrack "'['" st
  let (elems, st) ← parseBasicExprList fuel st
  let st ← expectTok .rBrack "']'" st
  return (elems, st)

/-- A comma-separated list of basic expressions (possibly empty). -/
def parseBasicExprList (fuel : Nat) (st : State) : Except String ((List BasicExpr) × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  match st.peek? with
  | some .rBrack => return ([], st)
  | _ =>
    let (e, st) ← parseBasicExpr fuel st
    let (rest, st) ← parseBasicExprListTail fuel st
    return (e :: rest, st)

/-- The `"," basic-expr` continuation of an expression list. -/
def parseBasicExprListTail (fuel : Nat) (st : State) : Except String ((List BasicExpr) × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  match st.peek? with
  | some .comma =>
    let st ← expectTok .comma "','" st
    let (e, st) ← parseBasicExpr fuel st
    let (rest, st) ← parseBasicExprListTail fuel st
    return (e :: rest, st)
  | _ => return ([], st)

/-- `<expr>`. -/
def parseExpr (fuel : Nat) (st : State) : Except String (Expr × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  match st.peek? with
  | some .lBrack =>
    let (elems, st) ← parseArrayLiteral fuel st
    return (.array elems, st)
  | _ =>
    let (b, st) ← parseBasicExpr fuel st
    return (.basic b, st)

/-- `<par-array-literal> ::= "[" [ <basic-literal-expr> "," ... ] "]"`. -/
def parseParArrayLiteral (fuel : Nat) (st : State) : Except String (ParArrayLiteral × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  let st ← expectTok .lBrack "'['" st
  let (elems, st) ← parseBasicLiteralList fuel st
  let st ← expectTok .rBrack "']'" st
  return (elems, st)

/-- A comma-separated list of basic literals (possibly empty). -/
def parseBasicLiteralList (fuel : Nat) (st : State) : Except String ((List BasicLiteral) × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  match st.peek? with
  | some .rBrack => return ([], st)
  | _ =>
    let (l, st) ← parseBasicLiteral fuel st
    let (rest, st) ← parseBasicLiteralListTail fuel st
    return (l :: rest, st)

/-- The `"," basic-literal` continuation of a literal list. -/
def parseBasicLiteralListTail (fuel : Nat) (st : State) : Except String ((List BasicLiteral) × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  match st.peek? with
  | some .comma =>
    let st ← expectTok .comma "','" st
    let (l, st) ← parseBasicLiteral fuel st
    let (rest, st) ← parseBasicLiteralListTail fuel st
    return (l :: rest, st)
  | _ => return ([], st)

/-- `<annotation> ::= <identifier> | <identifier> "(" <ann-expr> "," ... ")"`. -/
def parseAnnotation (fuel : Nat) (st : State) : Except String (Annotation × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  let (x, st) ← parsePredIdent st
  match st.peek? with
  | some .lParen =>
    let st ← expectTok .lParen "'('" st
    let (args, st) ← parseAnnExprList fuel st
    let st ← expectTok .rParen "')'" st
    return (.call x args, st)
  | _ => return (.ident x, st)

/-- A comma-separated, non-empty list of annotation expressions. -/
def parseAnnExprList (fuel : Nat) (st : State) : Except String ((List AnnExpr) × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  let (a, st) ← parseAnnExpr fuel st
  let (rest, st) ← parseAnnExprListTail fuel st
  return (a :: rest, st)

/-- The `"," ann-expr` continuation of an annotation list. -/
def parseAnnExprListTail (fuel : Nat) (st : State) : Except String ((List AnnExpr) × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  match st.peek? with
  | some .comma =>
    let st ← expectTok .comma "','" st
    let (a, st) ← parseAnnExpr fuel st
    let (rest, st) ← parseAnnExprListTail fuel st
    return (a :: rest, st)
  | _ => return ([], st)

/-- `<ann-expr>`. -/
def parseAnnExpr (fuel : Nat) (st : State) : Except String (AnnExpr × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  match st.peek? with
  | some (.stringLit _) =>
    let (s, st) ← parseStringLit st
    return (.string s, st)
  | some .lBrack =>
    let st ← expectTok .lBrack "'['" st
    let (elems, st) ← parseAnnExprArrayContents fuel st
    let st ← expectTok .rBrack "']'" st
    return (.array elems, st)
  | some (.ident _) =>
    -- identifier: either a plain identifier or a nested annotation call
    let (x, st₁) ← parseIdent st
    match st₁.peek? with
    | some .lParen =>
      if x.name.startsWith "_" then
        .error s!"identifier '{x.name}' may not start with an underscore here"
      else
      let st₂ ← expectTok .lParen "'('" st₁
      let (args, st₃) ← parseAnnExprList fuel st₂
      let st₄ ← expectTok .rParen "')'" st₃
      return (.ann (.call x args), st₄)
    | _ => return (.ident x, st₁)
  | _ =>
    let (l, st) ← parseBasicLiteral fuel st
    return (.lit l, st)

/-- The contents of an annotation array (possibly empty). -/
def parseAnnExprArrayContents (fuel : Nat) (st : State) : Except String ((List AnnExpr) × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  match st.peek? with
  | some .rBrack => return ([], st)
  | _ =>
    let (a, st) ← parseAnnExpr fuel st
    let (rest, st) ← parseAnnExprListTail fuel st
    return (a :: rest, st)

/-- `<annotations> ::= [ "::" <annotation> ]*`. -/
def parseAnnotations (fuel : Nat) (st : State) : Except String ((List Annotation) × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  match st.peek? with
  | some .colonColon =>
    let st ← expectTok .colonColon "'::'" st
    let (a, st) ← parseAnnotation fuel st
    let (rest, st) ← parseAnnotations fuel st
    return (a :: rest, st)
  | _ => return ([], st)

/-- `<basic-par-type>` (int fragment). -/
def parseBasicParType (fuel : Nat) (st : State) : Except String (BasicParType × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | _ =>
  match st.peek? with
  | some .kwBool =>
    let st ← expectTok .kwBool "'bool'" st
    return (.bool, st)
  | some .kwInt =>
    let st ← expectTok .kwInt "'int'" st
    return (.int, st)
  | some .kwSet =>
    let st ← expectTok .kwSet "'set'" st
    let st ← expectTok .kwOf "'of'" st
    let st ← expectTok .kwInt "'int'" st
    return (.setOfInt, st)
  | _ => .error s!"expected parameter type at token {st.pos}"

/-- `<basic-var-type>` (int fragment). -/
def parseBasicVarType (fuel : Nat) (st : State) : Except String (BasicVarType × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  let st ← expectTok .kwVar "'var'" st
  match st.peek? with
  | some .kwBool =>
    let st ← expectTok .kwBool "'bool'" st
    return (.par .bool, st)
  | some .kwInt =>
    let st ← expectTok .kwInt "'int'" st
    return (.par .int, st)
  | some .kwSet =>
    let st ← expectTok .kwSet "'set'" st
    let st ← expectTok .kwOf "'of'" st
    match st.peek? with
    | some .kwInt =>
      let st ← expectTok .kwInt "'int'" st
      return (.par .setOfInt, st)
    | some (.intLit _) =>
      let (lo, st) ← parseIntLit st
      let st ← expectTok .dotDot "'..'" st
      let (hi, st) ← parseIntLit st
      return (.setOfIntRange lo hi, st)
    | some .lBrace =>
      let st ← expectTok .lBrace "'{'" st
      let (elems, st) ← parseIntList fuel st
      let st ← expectTok .rBrace "'}'" st
      return (.setOfIntSet elems, st)
    | _ => .error s!"expected 'int', int range, or int set after 'var set of' at token {st.pos}"
  | some (.intLit _) =>
    let (lo, st) ← parseIntLit st
    let st ← expectTok .dotDot "'..'" st
    let (hi, st) ← parseIntLit st
    return (.intRange lo hi, st)
  | some .lBrace =>
    let st ← expectTok .lBrace "'{'" st
    let (elems, st) ← parseNonemptyIntList fuel st
    let st ← expectTok .rBrace "'}'" st
    return (.intSet elems, st)
  | _ => .error s!"expected variable type at token {st.pos}"

/-- `<index-set> ::= "1" ".." <int-literal>`. -/
def parseIndexSet (st : State) : Except String (IndexSet × State) := do
  let (lo, st) ← parseIntLit st
  if lo != 1 then
    .error s!"array index set must start at 1 at token {st.pos}"
  else
    let st ← expectTok .dotDot "'..'" st
    let (hi, st) ← parseIntLit st
    return (⟨hi⟩, st)

/-- `<basic-pred-param-type>` (int fragment). -/
def parseBasicPredParamType (fuel : Nat) (st : State) : Except String (BasicPredParamType × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  match st.peek? with
  | some .kwVar =>
    let (t, st) ← parseBasicVarType fuel st
    return (.var t, st)
  | some .kwSet =>
    let st ← expectTok .kwSet "'set'" st
    let st ← expectTok .kwOf "'of'" st
    match st.peek? with
    | some .kwInt =>
      let st ← expectTok .kwInt "'int'" st
      return (.par .setOfInt, st)
    | some (.intLit _) =>
      let (lo, st) ← parseIntLit st
      let st ← expectTok .dotDot "'..'" st
      let (hi, st) ← parseIntLit st
      return (.setOfIntRange lo hi, st)
    | some .lBrace =>
      let st ← expectTok .lBrace "'{'" st
      let (elems, st) ← parseIntList fuel st
      let st ← expectTok .rBrace "'}'" st
      return (.setOfIntSet elems, st)
    | _ => .error s!"expected set type at token {st.pos}"
  | some .kwBool =>
    let st ← expectTok .kwBool "'bool'" st
    return (.par .bool, st)
  | some .kwInt =>
    let st ← expectTok .kwInt "'int'" st
    return (.par .int, st)
  | some (.intLit _) =>
    let (lo, st) ← parseIntLit st
    let st ← expectTok .dotDot "'..'" st
    let (hi, st) ← parseIntLit st
    return (.intRange lo hi, st)
  | some .lBrace =>
    let st ← expectTok .lBrace "'{'" st
    let (elems, st) ← parseNonemptyIntList fuel st
    let st ← expectTok .rBrace "'}'" st
    return (.intSet elems, st)
  | _ => .error s!"expected predicate parameter type at token {st.pos}"

/-- `<pred-index-set> ::= <index-set> | "int"`. -/
def parsePredIndexSet (st : State) : Except String (PredIndexSet × State) := do
  match st.peek? with
  | some .kwInt =>
    let st ← expectTok .kwInt "'int'" st
    return (.int, st)
  | _ =>
    let (i, st) ← parseIndexSet st
    return (.range i, st)

/-- `<pred-param-type>`. -/
def parsePredParamType (fuel : Nat) (st : State) : Except String (PredParamType × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  match st.peek? with
  | some .kwArray =>
    let st ← expectTok .kwArray "'array'" st
    let st ← expectTok .lBrack "'['" st
    let (idx, st) ← parsePredIndexSet st
    let st ← expectTok .rBrack "']'" st
    let st ← expectTok .kwOf "'of'" st
    let (elem, st) ← parseBasicPredParamType fuel st
    return (.array idx elem, st)
  | _ =>
    let (t, st) ← parseBasicPredParamType fuel st
    return (.basic t, st)

/-- One predicate parameter: `<pred-param-type> ":" <identifier>`. -/
def parsePredParam (fuel : Nat) (st : State) : Except String (PredParam × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  let (t, st) ← parsePredParamType fuel st
  let st ← expectTok .colon "':'" st
  let (x, st) ← parsePredIdent st
  return (⟨t, x⟩, st)

/-- A comma-separated list of predicate parameters (possibly empty). -/
def parsePredParamList (fuel : Nat) (st : State) : Except String (List PredParam × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  match st.peek? with
  | some .rParen => return ([], st)
  | _ =>
    let (p, st) ← parsePredParam fuel st
    let (rest, st) ← parsePredParamListTail fuel st
    return (p :: rest, st)

/-- The `"," pred-param` continuation. -/
def parsePredParamListTail (fuel : Nat) (st : State) : Except String (List PredParam × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  match st.peek? with
  | some .comma =>
    let st ← expectTok .comma "','" st
    let (p, st) ← parsePredParam fuel st
    let (rest, st) ← parsePredParamListTail fuel st
    return (p :: rest, st)
  | _ => return ([], st)

/-- `<predicate-item>`. -/
def parsePredicateItem (fuel : Nat) (st : State) : Except String (PredicateItem × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  let st ← expectTok .kwPredicate "'predicate'" st
  let (x, st) ← parsePredIdent st
  let st ← expectTok .lParen "'('" st
  let (params, st) ← parsePredParamList fuel st
  let st ← expectTok .rParen "')'" st
  let st ← expectTok .semi "';'" st
  return (⟨x, params⟩, st)

/-- `<par-decl-item>` (int fragment). -/
def parseParDeclItem (fuel : Nat) (st : State) : Except String (ParDeclItem × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  match st.peek? with
  | some .kwArray =>
    let st ← expectTok .kwArray "'array'" st
    let st ← expectTok .lBrack "'['" st
    let (idx, st) ← parseIndexSet st
    let st ← expectTok .rBrack "']'" st
    let st ← expectTok .kwOf "'of'" st
    let (t, st) ← parseBasicParType fuel st
    let st ← expectTok .colon "':'" st
    let (x, st) ← parseIdent st
    let st ← expectTok .eq "'='" st
    let (v, st) ← parseParArrayLiteral fuel st
    let st ← expectTok .semi "';'" st
    return (.array idx t x v, st)
  | _ =>
    let (t, st) ← parseBasicParType fuel st
    let st ← expectTok .colon "':'" st
    let (x, st) ← parseIdent st
    let st ← expectTok .eq "'='" st
    let (v, st) ← parseBasicLiteral fuel st
    let st ← expectTok .semi "';'" st
    return (.basic t x v, st)

/-- `<var-decl-item>` (int fragment). -/
def parseVarDeclItem (fuel : Nat) (st : State) : Except String (VarDeclItem × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  match st.peek? with
  | some .kwArray =>
    let st ← expectTok .kwArray "'array'" st
    let st ← expectTok .lBrack "'['" st
    let (idx, st) ← parseIndexSet st
    let st ← expectTok .rBrack "']'" st
    let st ← expectTok .kwOf "'of'" st
    let (t, st) ← parseBasicVarType fuel st
    let st ← expectTok .colon "':'" st
    let (x, st) ← parseIdent st
    let (anns, st) ← parseAnnotations fuel st
    let st ← expectTok .eq "'='" st
    let (v, st) ← parseArrayLiteral fuel st
    let st ← expectTok .semi "';'" st
    return (.array ⟨idx, t⟩ x anns v, st)
  | _ =>
    let (t, st) ← parseBasicVarType fuel st
    let st ← expectTok .colon "':'" st
    let (x, st) ← parseIdent st
    let (anns, st) ← parseAnnotations fuel st
    match st.peek? with
    | some .eq =>
      let st ← expectTok .eq "'='" st
      let (v, st) ← parseBasicExpr fuel st
      let st ← expectTok .semi "';'" st
      return (.basic t x anns (some v), st)
    | _ =>
      let st ← expectTok .semi "';'" st
      return (.basic t x anns none, st)

/-- `<constraint-item>`. -/
def parseConstraintItem (fuel : Nat) (st : State) : Except String (ConstraintItem × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  let st ← expectTok .kwConstraint "'constraint'" st
  let (x, st) ← parsePredIdent st
  let st ← expectTok .lParen "'('" st
  let (args, st) ← parseExprList fuel st
  let st ← expectTok .rParen "')'" st
  let (anns, st) ← parseAnnotations fuel st
  let st ← expectTok .semi "';'" st
  return (⟨x, args, anns⟩, st)

/-- A comma-separated list of expressions (possibly empty). -/
def parseExprList (fuel : Nat) (st : State) : Except String (List Expr × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  match st.peek? with
  | some .rParen => return ([], st)
  | _ =>
    let (e, st) ← parseExpr fuel st
    let (rest, st) ← parseExprListTail fuel st
    return (e :: rest, st)

/-- The `"," expr` continuation. -/
def parseExprListTail (fuel : Nat) (st : State) : Except String (List Expr × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  match st.peek? with
  | some .comma =>
    let st ← expectTok .comma "','" st
    let (e, st) ← parseExpr fuel st
    let (rest, st) ← parseExprListTail fuel st
    return (e :: rest, st)
  | _ => return ([], st)

/-- `<solve-item>`. -/
def parseSolveItem (fuel : Nat) (st : State) : Except String (SolveItem × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  let st ← expectTok .kwSolve "'solve'" st
  let (anns, st) ← parseAnnotations fuel st
  match st.peek? with
  | some .kwSatisfy =>
    let st ← expectTok .kwSatisfy "'satisfy'" st
    let st ← expectTok .semi "';'" st
    return (.satisfy anns, st)
  | some .kwMinimize =>
    let st ← expectTok .kwMinimize "'minimize'" st
    let (e, st) ← parseBasicExpr fuel st
    let st ← expectTok .semi "';'" st
    return (.minimize anns e, st)
  | some .kwMaximize =>
    let st ← expectTok .kwMaximize "'maximize'" st
    let (e, st) ← parseBasicExpr fuel st
    let st ← expectTok .semi "';'" st
    return (.maximize anns e, st)
  | _ => .error s!"expected 'satisfy', 'minimize' or 'maximize' at token {st.pos}"

end

/-- Parse a list of items of the same kind, until the current token no longer
    starts such an item. -/
def parseMany (start : State → Bool)
    (parseOne : Nat → State → Except String (α × State))
    (fuel : Nat) (st : State) : Except String (List α × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  if start st then
    let (x, st) ← parseOne fuel st
    let (rest, st) ← parseMany start parseOne fuel st
    return (x :: rest, st)
  else
    return ([], st)

/-- Does the current token start a predicate item? -/
def atPredicate (st : State) : Bool := st.peek? == some .kwPredicate

/-- Look ahead past `array [ <int-lit> .. <int-lit> ] of` to the token that
    follows, which distinguishes an array parameter declaration (a basic par
    type) from an array variable declaration (`var ...`).  Returns the token
    at that offset, if the prefix matches. -/
def arrayElemToken (st : State) : Option Token :=
  -- tokens: array [ int .. int ] of <tok>
  match st.toks[st.pos]?, st.toks[st.pos+1]?, st.toks[st.pos+2]?,
        st.toks[st.pos+3]?, st.toks[st.pos+4]?, st.toks[st.pos+5]?,
        st.toks[st.pos+6]? with
  | some .kwArray, some .lBrack, some (.intLit _), some .dotDot,
    some (.intLit _), some .rBrack, some .kwOf =>
    st.toks[st.pos+7]?
  | _, _, _, _, _, _, _ => none

/-- Does the current token start a parameter declaration? -/
def atParDecl (st : State) : Bool :=
  match st.peek? with
  | some .kwBool | some .kwInt | some .kwSet => true
  | some .kwArray =>
    -- array par-decl iff the element type is a basic par type (not `var`)
    match arrayElemToken st with
    | some .kwBool | some .kwInt | some .kwSet => true
    | _ => false
  | _ => false

/-- Does the current token start a variable declaration? -/
def atVarDecl (st : State) : Bool :=
  match st.peek? with
  | some .kwVar => true
  | some .kwArray =>
    match arrayElemToken st with
    | some .kwVar => true
    | _ => false
  | _ => false

/-- Does the current token start a constraint item? -/
def atConstraint (st : State) : Bool := st.peek? == some .kwConstraint

/-- `<model>`: predicates, then parameters, then variables, then constraints,
    then exactly one solve item. -/
def parseModelAux (fuel : Nat) (st : State) : Except String (Model × State) := do
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
  let (preds, st) ← parseMany atPredicate parsePredicateItem fuel st
  let (params, st) ← parseMany atParDecl parseParDeclItem fuel st
  let (vars, st) ← parseMany atVarDecl parseVarDeclItem fuel st
  let (cons, st) ← parseMany atConstraint parseConstraintItem fuel st
  let (solve, st) ← parseSolveItem fuel st
  return (⟨preds, params, vars, cons, solve⟩, st)

/-- The fuel bound for parsing.  Every recursive parser call either consumes a
    token or strictly decreases fuel, and the nesting depth of the grammar is
    bounded by a constant per token, so `8 * (toks.size + 1)` fuel is always
    sufficient to parse any valid model (see `FznCorrectness.lean`). -/
def parseFuel (toks : Array Token) : Nat := 8 * (toks.size + 1)

/-- The remaining tokens are empty iff the position reached (or passed)
    the end of the array.  (Used by `parseModelTokens` as an O(1) end
    check; `remaining` itself would convert the whole array to a list
    first, an O(n) allocation per parse.) -/
theorem State.remaining_isEmpty_iff (st : State) :
    st.remaining.isEmpty = true ↔ ¬ (st.pos < st.toks.size) := by
  have hlen : st.toks.toList.length = st.toks.size :=
    (Array.size_eq_length_toList (xs := st.toks)).symm
  unfold State.remaining
  simp only [List.isEmpty_iff, List.drop_eq_nil_iff, hlen]
  omega

/-- Parse a whole FlatZinc model from a token array.  Succeeds only if the
    entire token stream is consumed. -/
def parseModelTokens (toks : Array Token) : Except String Model :=
  match parseModelAux (parseFuel toks) ⟨toks, 0⟩ with
  | .ok (m, st) =>
    -- O(1) end check (see `State.remaining_isEmpty_iff`): converting the
    -- array to a list just to test emptiness is O(n)
    if st.pos < st.toks.size then
      .error s!"trailing tokens after solve item at token {st.pos}"
    else
      .ok m
  | .error e => .error e

/-- Parse a whole FlatZinc model from a source string. -/
def parseModel (src : String) : Except String Model :=
  match tokenize src with
  | .error e => .error e
  | .ok toks => parseModelTokens toks

end LeanFzn.Parser

import LeanFzn.FznAST

/-
# FlatZinc Pretty-Printer

A canonical pretty-printer for the FlatZinc abstract syntax tree
(`LeanFzn.FznAST`): `pretty m` renders a `Model` as FlatZinc source text.

## Canonical form

The printer is *canonical* in the sense that its output re-parses to the
model it was printed from:

* every item is printed on its own line, sections in the fixed order
  (predicates, parameters, variables, constraints, solve);
* `IndexSet` is printed as `1..hi` (the grammar fixes the lower bound to 1),
  so an empty index set prints as `1..0`;
* annotations are printed with a leading `::` in annotation-list positions
  (variable declarations, constraints, solve items) and without it when they
  appear as annotation arguments;
* string literals are re-escaped (`\` and `"`) so the lexer recovers the
  original contents;
* identifiers are printed verbatim (the lexer/parser already validated them).

Together with the parser (`LeanFzn.Parser.parseModel`) this supports
round-tripping: `parse (pretty (parse src)) = parse src` for every `src`
accepted by the parser, and `pretty` is idempotent on parsed models.
-/

namespace LeanFzn

/-! ## Identifiers and literals -/

/-- An identifier is printed verbatim; the lexer has already validated it. -/
def Ident.pp (x : Ident) : String := x.name

/-- A comma-separated rendering of a list of integers, e.g. `1, 2, 3`. -/
private def ppIntList (xs : List Int) : String :=
  ", ".intercalate (xs.map toString)

/-- `<set-literal>`: `{a, b}` or `lo..hi`; the empty set prints as `{}`. -/
def SetLiteral.pp : SetLiteral → String
  | .intSet elems => "{" ++ ppIntList elems ++ "}"
  | .intRange lo hi => s!"{lo}..{hi}"

/-- `<basic-literal-expr>`: `true`/`false`, an integer, or a set literal. -/
def BasicLiteral.pp : BasicLiteral → String
  | .bool b => if b then "true" else "false"
  | .int i => toString i
  | .set s => s.pp

/-- `<basic-expr>`: a literal or an identifier. -/
def BasicExpr.pp : BasicExpr → String
  | .lit l => l.pp
  | .ident x => x.pp

/-! ## Expressions -/

/-- `<array-literal>`: `[e1, e2, ...]`; the empty array prints as `[]`. -/
def ppArrayLiteral (elems : ArrayLiteral) : String :=
  "[" ++ ", ".intercalate (elems.map (·.pp)) ++ "]"

/-- `<expr>`: a basic expression or an array literal. -/
def Expr.pp : Expr → String
  | .basic b => b.pp
  | .array elems => ppArrayLiteral elems

/-! ## Types -/

/-- `<basic-par-type>`: `bool`, `int`, or `set of int`. -/
def BasicParType.pp : BasicParType → String
  | .bool => "bool"
  | .int => "int"
  | .setOfInt => "set of int"

/-- `<basic-var-type>`: `var t`, `var lo..hi`, `var {..}`,
    `var set of lo..hi`, or `var set of {..}`. -/
def BasicVarType.pp : BasicVarType → String
  | .par t => "var " ++ t.pp
  | .intRange lo hi => s!"var {lo}..{hi}"
  | .intSet elems => "var {" ++ ppIntList elems ++ "}"
  | .setOfIntRange lo hi => s!"var set of {lo}..{hi}"
  | .setOfIntSet elems => "var set of {" ++ ppIntList elems ++ "}"

/-- `<index-set>`: the lower bound is fixed to 1 by the grammar, so this
    prints `1..hi`; `hi = 0` yields the (valid, empty) `1..0`. -/
def IndexSet.pp (i : IndexSet) : String := s!"1..{i.hi}"

/-- `<array-var-type>`: `array [1..hi] of <basic-var-type>`. -/
def ArrayVarType.pp (t : ArrayVarType) : String :=
  "array [" ++ t.idx.pp ++ "] of " ++ t.elem.pp

/-- `<basic-pred-param-type>`: par types carry no `var` keyword, var types
    are printed as in declarations; ranges and sets may also appear bare. -/
def BasicPredParamType.pp : BasicPredParamType → String
  | .par t => t.pp
  | .var t => t.pp
  | .intRange lo hi => s!"{lo}..{hi}"
  | .intSet elems => "{" ++ ppIntList elems ++ "}"
  | .setOfIntRange lo hi => s!"set of {lo}..{hi}"
  | .setOfIntSet elems => "set of {" ++ ppIntList elems ++ "}"

/-- `<pred-index-set>`: `1..hi` or `int`. -/
def PredIndexSet.pp : PredIndexSet → String
  | .range idx => idx.pp
  | .int => "int"

/-- `<pred-param-type>`: a basic type or `array [idx] of <basic type>`. -/
def PredParamType.pp : PredParamType → String
  | .basic t => t.pp
  | .array idx t => "array [" ++ idx.pp ++ "] of " ++ t.pp

/-! ## Predicate declarations -/

/-- One predicate parameter: `<pred-param-type> : <identifier>`. -/
def PredParam.pp (p : PredParam) : String :=
  p.type.pp ++ ": " ++ p.name.pp

/-- `<predicate-item>`: `predicate p(t1: x1, ...);`. -/
def PredicateItem.pp (p : PredicateItem) : String :=
  "predicate " ++ p.name.pp ++ "(" ++ ", ".intercalate (p.params.map (·.pp)) ++ ");"

/-! ## Parameter declarations -/

/-- `<par-decl-item>`: `t: x = v;` or `array [1..hi] of t: x = [..];`. -/
def ParDeclItem.pp : ParDeclItem → String
  | .basic t x v => t.pp ++ ": " ++ x.pp ++ " = " ++ v.pp ++ ";"
  | .array idx t x vs =>
      "array [" ++ idx.pp ++ "] of " ++ t.pp ++ ": " ++ x.pp ++ " = ["
        ++ ", ".intercalate (vs.map (·.pp)) ++ "];"

/-! ## Annotations -/

/-- Escape a string literal's contents for printing: `\` becomes `\\` and
    `"` becomes `\"` (the two escapes the lexer decodes). -/
private def escapeString (s : String) : String :=
  let rec go (cs : List Char) (acc : String) : String :=
    match cs with
    | [] => acc
    | '\\' :: rest => go rest (acc.push '\\' |>.push '\\')
    | '"' :: rest => go rest (acc.push '\\' |>.push '"')
    | c :: rest => go rest (acc.push c)
  go s.toList ""

mutual

/-- `<annotation>`: `x` or `x(a1, a2)`.  The leading `::` of
    annotation-list positions is added by `ppAnns`, not here. -/
def Annotation.pp : Annotation → String
  | .ident x => x.pp
  | .call x args => x.pp ++ "(" ++ ", ".intercalate (args.map (·.pp)) ++ ")"

/-- `<ann-expr>`: a literal, an identifier, a re-escaped string literal, a
    nested annotation (without `::`), or an array of annotation expressions. -/
def AnnExpr.pp : AnnExpr → String
  | .lit l => l.pp
  | .ident x => x.pp
  | .string s => "\"" ++ escapeString s ++ "\""
  | .ann a => a.pp
  | .array elems => "[" ++ ", ".intercalate (elems.map (·.pp)) ++ "]"

end

/-- Annotation-list position: each annotation prefixed with `::`, separated
    by single spaces.  An empty list contributes nothing (in particular, no
    stray space). -/
private def ppAnns (anns : List Annotation) : String :=
  if anns.isEmpty then ""
  else " " ++ String.intercalate " " (anns.map (fun a => ":: " ++ a.pp))

/-! ## Variable declarations -/

/-- `<var-decl-item>`: `t: x [anns] [= v];` — the initializer is optional for
    basic declarations and required for arrays. -/
def VarDeclItem.pp : VarDeclItem → String
  | .basic t x anns none =>
      t.pp ++ ": " ++ x.pp ++ ppAnns anns ++ ";"
  | .basic t x anns (some v) =>
      t.pp ++ ": " ++ x.pp ++ ppAnns anns ++ " = " ++ v.pp ++ ";"
  | .array t x anns vs =>
      t.pp ++ ": " ++ x.pp ++ ppAnns anns ++ " = " ++ ppArrayLiteral vs ++ ";"

/-! ## Constraints and solve items -/

/-- `<constraint-item>`: `constraint p(a1, ...) [anns];`. -/
def ConstraintItem.pp (c : ConstraintItem) : String :=
  "constraint " ++ c.name.pp ++ "("
    ++ ", ".intercalate (c.args.map (·.pp)) ++ ")" ++ ppAnns c.anns ++ ";"

/-- `<solve-item>`: `solve [anns] satisfy;` or
    `solve [anns] minimize/maximize obj;`. -/
def SolveItem.pp : SolveItem → String
  | .satisfy anns =>
      "solve" ++ ppAnns anns ++ " satisfy;"
  | .minimize anns obj =>
      "solve" ++ ppAnns anns ++ " minimize " ++ obj.pp ++ ";"
  | .maximize anns obj =>
      "solve" ++ ppAnns anns ++ " maximize " ++ obj.pp ++ ";"

/-! ## Models -/

/-- `<model>`: the five sections in order, one item per line.  Empty sections
    contribute nothing (no blank lines). -/
def Model.pp (m : Model) : String :=
  let items :=
    m.predicates.map (·.pp)
      ++ m.parameters.map (·.pp)
      ++ m.variables.map (·.pp)
      ++ m.constraints.map (·.pp)
      ++ [m.solve.pp]
  "\n".intercalate items

/-- Canonical FlatZinc rendering of a model. -/
def pretty (m : Model) : String := m.pp

end LeanFzn

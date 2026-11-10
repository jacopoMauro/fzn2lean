/-
File: LeanFzn/Compiler/LiteralFold.lean

Purpose:
  Literal folding for the certified compiler (PLAN.md tasks L1, L2 and L3).

  L1 (`foldGroundModel`): a constraint whose arguments are all literals is
  decided by the existing executable semantics `fullInterpB`.  A true
  constraint is dropped; a false one is replaced by the always-false accepted
  row `int_lin_le([], [], -1)`, never dropped.  The pass is guarded on
  `fullCheckableNames`, the domain of `fullInterpB_iff`.

  L2 (`foldReifModel`): a reified predicate whose result argument is a
  Boolean literal is rewritten to the plain form (`true`) or its checked
  negation (`false`).  The scalar integer table is `int_eq`, `int_ne`,
  `int_le`, `int_lt`, `int_ge`, `int_gt`; the linear table's `true` cases drop
  the result argument.  Linear `false` cases and set reifications are left
  unchanged (see `tmp/design/l1-l2-literal-fold.md`): the former have a
  length-shape semantic trap, and `restrictSetInModel` already handles the
  latter.

  L3 (`foldSetCardModel`): `set_card(R, x)` with a literal set `R` becomes
  `int_eq(x, |R|)` using `IntSetValue.card` (duplicates counted once, reversed
  ranges zero).  Parameter-set arguments are left unchanged; the flattener
  emits literal/range sets for this shape.

  The three passes are model-to-model and change only `constraints`;
  variables, parameters and `solveAnn` are untouched.  `compileModelFull`
  runs them between `normalizeModel` and `restrictSetInModel`, in the order
  set-card, ground, reified result.  The correctness proofs are in
  `Proofs/LiteralFold`; the public `solveModel_*` statements are unchanged.

Dependencies:
  - LeanFzn.Compiler.Compile: `compileModel`, `CompiledProblem`.
  - LeanFzn.Semantics.Globals: `fullInterp`, `fullInterpB`,
    `fullCheckableNames`.
-/

import LeanFzn.Compiler.Compile

namespace LeanFzn.Compiler
open LeanFzn LeanFzn.Semantics LeanFzn.Semantics.Globals

/-! ## Constant-set cardinality -/

/-- Rewrite `set_card(R, x)` with a literal set `R` to `int_eq(x, |R|)`.
    The cardinality is `IntSetValue.card`: duplicate enumeration elements
    count once and a reversed range is empty.  Any other shape is kept. -/
def setCardFold (c : ConstraintItem) : List ConstraintItem :=
  match c.name.name, c.args with
  | "set_card", [.basic (.lit (.set s)), .basic x] =>
      [{ name := Ident.mk "int_eq"
         args := [.basic x, .basic (.lit (.int (s.denote.card)))]
         anns := c.anns }]
  | _, _ => [c]

/-- The constant-set cardinality pass.  Only the constraint list changes. -/
def foldSetCardModel (m : Model) : Model :=
  { m with constraints := m.constraints.flatMap setCardFold }

/-! ## Ground arguments -/

/-- Decode a literal basic expression.  Identifiers are deliberately not
    ground: their value depends on the store. -/
def groundBasic : BasicExpr → Option Value
  | .lit l => some l.denote
  | .ident _ => none

/-- Decode an all-literal expression (a literal or an array of literals). -/
def groundExpr : Expr → Option Value
  | .basic e => groundBasic e
  | .array es => (es.mapM groundBasic).map Value.array

/-- Decode an all-literal argument list. -/
def groundArgs (args : List Expr) : Option (List Value) :=
  args.mapM groundExpr

/-- The always-false constraint used for a false ground decision.  It is an
    accepted `int_lin_le` row whose empty dot product is `0 > -1`. -/
def falseConstraint : ConstraintItem :=
  { name := Ident.mk "int_lin_le"
    args := [.array [], .array [], .basic (.lit (.int (-1)))]
    anns := [] }

/-- One constraint after ground decision: dropped when true, the false row
    when false, unchanged when the arguments are not all literals or the
    predicate has no executable twin. -/
def groundFold (c : ConstraintItem) : List ConstraintItem :=
  match groundArgs c.args with
  | some vals =>
      if _h : c.name.name ∈ fullCheckableNames then
        if fullInterpB c.name vals then [] else [falseConstraint]
      else [c]
  | none => [c]

/-- The ground-decision pass.  Only the constraint list changes. -/
def foldGroundModel (m : Model) : Model :=
  { m with constraints := m.constraints.flatMap groundFold }

/-! ## Literal reification results -/

/-- The scalar integer reification table.  `true` selects the plain
    predicate, `false` its negation; the argument order is swapped where the
    negation needs it (`int_le`/`int_lt` and `int_ge`/`int_gt`). -/
def reifScalar (c : ConstraintItem) : Option ConstraintItem :=
  match c.name.name, c.args with
  | "int_eq_reif", [a, b, .basic (.lit (.bool r))] =>
      some { name := Ident.mk (if r then "int_eq" else "int_ne")
             args := [a, b], anns := [] }
  | "int_ne_reif", [a, b, .basic (.lit (.bool r))] =>
      some { name := Ident.mk (if r then "int_ne" else "int_eq")
             args := [a, b], anns := [] }
  | "int_le_reif", [a, b, .basic (.lit (.bool r))] =>
      some { name := Ident.mk (if r then "int_le" else "int_lt")
             args := if r then [a, b] else [b, a], anns := [] }
  | "int_lt_reif", [a, b, .basic (.lit (.bool r))] =>
      some { name := Ident.mk (if r then "int_lt" else "int_le")
             args := if r then [a, b] else [b, a], anns := [] }
  | "int_ge_reif", [a, b, .basic (.lit (.bool r))] =>
      some { name := Ident.mk (if r then "int_le" else "int_lt")
             args := if r then [b, a] else [a, b], anns := [] }
  | "int_gt_reif", [a, b, .basic (.lit (.bool r))] =>
      some { name := Ident.mk (if r then "int_lt" else "int_le")
             args := if r then [b, a] else [a, b], anns := [] }
  | "int_lin_eq_reif", [a, b, k, .basic (.lit (.bool true))] =>
      some { name := Ident.mk "int_lin_eq", args := [a, b, k], anns := [] }
  | "int_lin_le_reif", [a, b, k, .basic (.lit (.bool true))] =>
      some { name := Ident.mk "int_lin_le", args := [a, b, k], anns := [] }
  | "int_lin_ne_reif", [a, b, k, .basic (.lit (.bool true))] =>
      some { name := Ident.mk "int_lin_ne", args := [a, b, k], anns := [] }
  | _, _ => none

/-- One constraint after literal-result folding. -/
def reifFold (c : ConstraintItem) : List ConstraintItem :=
  match reifScalar c with
  | some d => [d]
  | none => [c]

/-- The literal-result reification pass.  Only the constraint list changes.
    `set_in_reif` is intentionally absent: `restrictSetInModel` handles its
    constant-set finite-variable shapes after this pass. -/
def foldReifModel (m : Model) : Model :=
  { m with constraints := m.constraints.flatMap reifFold }

/-- All literal passes.  The constant-set cardinality runs first, then the
    ground decision, then literal reification results.  The ground-first
    order among the latter two is essential: a ground reified literal such
    as `int_eq_reif(3,3,false)` is a false ground fact (certified UNSAT),
    not a literal-result rewrite. -/
def foldLiteralsModel (m : Model) : Model :=
  foldReifModel (foldGroundModel (foldSetCardModel m))

end LeanFzn.Compiler

/-
File: solver/Direct/Compile.lean

Purpose:
  Contains only executable compilation and constraint-evaluation code for the
  direct solver: the FlatZinc-fragment compiler to `Core.Problem`
  (`DomConstraint` payloads) and its Boolean leaf evaluator. Semantic
  correspondence proofs live in Proofs/Compile.

The accepted fragment (each case accompanied by exact
semantic-correspondence theorems in Proofs/Compile):

* parameters: scalar `int`/`bool` literals (used by constraint arguments);
* variables: initializer-free basic `var` declarations with finite domains
  (`var bool`, `var lo..hi`, `var {..}`) — the same slot extraction as
  `solver/Domain.lean`'s `slotsChecked`;
* constraints: the 21 extractable shapes of `solver/Extract.lean`
  (`int_eq`/`int_ne`/`int_le`/`int_plus`/`all_different`/`int_lin_eq`/
  `int_lin_le`/`int_times`/`int_min`/`int_max`/`int_abs`/`int_lt`/
  `bool_not`/`bool_and`/`bool_or` on slot and literal arguments);
* solve item: `solve satisfy`.

Anything else (predicate items, array parameters/variables, set
variables, other predicate names, failed extraction) is rejected with
`unsupported` before search.

Dependencies:
  - solver.Direct.Types: compiled representations.
  - solver.Domain: slot extraction.
  - solver.Extract: constraint-shape extraction.
  - solver.Propagators: `DomConstraint` and `satisfiedB`.
  - LeanFzn.FznStdLib: store-level predicate semantics bridge.

DAG:
  solver.Direct.Types + solver.Domain + solver.Extract
  + solver.Propagators -> solver.Direct.Compile
-/

import solver.Direct.Types
import solver.Domain
import solver.Extract
import solver.Propagators

namespace LeanFzn.Solver.Direct

open LeanFzn LeanFzn.Solver

/-- Evaluate all compiled constraints on a complete assignment. -/
def accepts (problem : CompiledProblem DomConstraint) (assignment : List Value) : Bool :=
  problem.constraints.all fun constraint => constraint.satisfiedB assignment

open LeanFzn.Solver in
/-- The `k`-th constraint argument as a basic expression (helper for
    the 2/3-ary predicates; array arguments are REJECTED here, so
    the fallback shapes never compile a mis-read array argument). -/
def argOf (c : ConstraintItem) (k : Nat) : Except String BasicExpr :=
  match c.args[k]! with
  | .basic b => .ok b
  | .array _ => .error "array argument in a scalar position"

/-- The `k`-th constraint argument, as an `Expr` (for the array arms). -/
def exprOf (c : ConstraintItem) (k : Nat) : Expr := c.args[k]!

/-! ## Parameter environments

Scalar `int`/`bool` parameters of the accepted fragment. The
constraint shapes below read parameters as literals: an argument
that is a parameter identifier is resolved to its declared literal
value. Array parameters, set parameters, and parameter references in
variable positions are rejected. -/

/-- The declared literal value of a parameter declaration, if it is a
    scalar `int`/`bool` literal (the fragment's parameter shapes). -/
def parDeclValue : ParDeclItem → Option Value
  | .basic .int _ (.int i) => some (.int i)
  | .basic .bool _ (.bool b) => some (.bool b)
  | _ => none

/-- The parameter environment of a model: name → value for every
    scalar int/bool parameter. -/
def parEnv (m : Model) : Store :=
  fun x =>
    match lookupIdent x (m.parameters.filterMap
      (fun d => parDeclValue d |>.map (fun v => (d.name, v)))) with
    | some v => some v
    | none => none

/-! ## Total constraint compilation

`compileConstraint` is the TOTAL version of `Extract.extractConstraint`
for the certified fragment: a model constraint is compiled only when
its arguments are slot identifiers or fragment literals; anything
else returns `.error` (unsupported), so no model is silently
mis-compiled. Slot arguments are resolved against the slot-name list;
parameter identifiers are resolved through `parEnv`. -/

/-- One compiled constraint argument: a slot position or a literal
    value (parameters are already resolved to their literal values). -/
inductive ArgVal where
  | slotRef (i : Nat)
  | litVal (v : Value)

/-- Evaluate a constraint argument: slot identifiers resolve to their
    positions, parameters to their declared literal values, literals
    denote themselves. Anything else is unsupported. -/
def compileArgVal (env : Store) (names : List String)
    (e : BasicExpr) : Except String ArgVal :=
  match e with
  | .lit (.int i) => .ok (.litVal (.int i))
  | .lit (.bool b) => .ok (.litVal (.bool b))
  | .lit (.set _) => .error "set literal in a constraint argument"
  | .ident x =>
      match nameIndex names x.name with
      | some i => .ok (.slotRef i)
      | none =>
          match env x with
          | some v => .ok (.litVal v)
          | none => .error s!"unresolved argument '{x.name}'"

/-- The slot positions of an `all_different` array's elements: every
    element must be a slot name (parameters and literals are not
    slots in the certified fragment). -/
private def allDiffSlots (env : Store) (names : List String) :
    List BasicExpr → Except String (List Nat)
  | [] => .ok []
  | .ident x :: rest =>
      match nameIndex names x.name with
      | some i => (allDiffSlots env names rest).map (fun is => i :: is)
      | none =>
          match env x with
          | some _ => .error "all_different over a parameter"
          | none => .error s!"unresolved name '{x.name}' in all_different"
  | _ :: _ => .error "non-identifier in all_different array"

/-- The slot positions of a linear constraint's variable array. -/
private def linSlots (env : Store) (names : List String) :
    List BasicExpr → Except String (List Nat)
  | [] => .ok []
  | .ident x :: rest =>
      match nameIndex names x.name with
      | some i => (linSlots env names rest).map (fun is => i :: is)
      | none =>
          match env x with
          | some _ => .error "linear constraint over a parameter"
          | none => .error s!"unresolved name '{x.name}' in linear array"
  | _ :: _ => .error "non-identifier in linear array"

/-- Compile one model constraint to a `DomConstraint` over slot
    positions, or reject as unsupported. The constraint shapes are
    EXACTLY the extracted ones (`solver/Extract.lean`'s 21 shapes);
    anything else is rejected with a reason, so the proved
    correspondence (`extractConstraint_holds` and its converse in
    `Proofs/Compile`) applies verbatim. -/
def compileConstraint (env : Store) (names : List String)
    (c : ConstraintItem) : Except String DomConstraint :=
  match extractConstraint names c with
  | some dc => .ok dc
  | none =>
      -- fall back to the literal-bound shapes that extraction also
      -- understands but pattern-matches differently (parameters
      -- resolved to literals); all other shapes are unsupported
      if c.name.name = "int_plus" ∧ c.args.length = 3 then
        do
        let a0 ← argOf c 0
        let a1 ← argOf c 1
        let a2 ← argOf c 2
        match compileArgVal env names a0, compileArgVal env names a1,
            compileArgVal env names a2 with
        | .ok (.slotRef i), .ok (.slotRef j), .ok (.litVal (.int k)) =>
            .ok (.linEq [1, 1] [i, j] k)
        | .error e, _, _ => .error e
        | _, .error e, _ => .error e
        | _, _, .error e => .error e
        | _, _, _ => .error "unsupported int_plus argument shapes"
      else if c.name.name = "int_le" ∧ c.args.length = 2 then
        do
        let a0 ← argOf c 0
        let a1 ← argOf c 1
        match compileArgVal env names a0, compileArgVal env names a1 with
        | .ok (.slotRef i), .ok (.litVal (.int k)) => .ok (.leConstHi i k)
        | .ok (.litVal (.int k)), .ok (.slotRef j) => .ok (.leConstLo j k)
        | .error e, _ => .error e
        | _, .error e => .error e
        | _, _ => .error "unsupported int_le argument shapes"
      else if c.name.name = "int_lt" ∧ c.args.length = 2 then
        do
        let a0 ← argOf c 0
        let a1 ← argOf c 1
        match compileArgVal env names a0, compileArgVal env names a1 with
        | .ok (.slotRef i), .ok (.litVal (.int k)) => .ok (.ltConstHi i k)
        | .ok (.litVal (.int k)), .ok (.slotRef j) => .ok (.ltConstLo j k)
        | .error e, _ => .error e
        | _, .error e => .error e
        | _, _ => .error "unsupported int_lt argument shapes"
      else if c.name.name = "int_gt" ∧ c.args.length = 2 then
        -- int_gt(x, c) = int_lt(c, x); int_gt(c, x) = int_lt(x, c)
        do
        let a0 ← argOf c 0
        let a1 ← argOf c 1
        match compileArgVal env names a0, compileArgVal env names a1 with
        | .ok (.slotRef i), .ok (.litVal (.int k)) => .ok (.ltConstLo i k)
        | .ok (.litVal (.int k)), .ok (.slotRef j) => .ok (.ltConstHi j k)
        | .error e, _ => .error e
        | _, .error e => .error e
        | _, _ => .error "unsupported int_gt argument shapes"
      else if c.name.name = "int_ge" ∧ c.args.length = 2 then
        -- int_ge(x, c) = int_le(c, x); int_ge(c, x) = int_le(x, c)
        do
        let a0 ← argOf c 0
        let a1 ← argOf c 1
        match compileArgVal env names a0, compileArgVal env names a1 with
        | .ok (.slotRef i), .ok (.litVal (.int k)) => .ok (.leConstLo i k)
        | .ok (.litVal (.int k)), .ok (.slotRef j) => .ok (.leConstHi j k)
        | .error e, _ => .error e
        | _, .error e => .error e
        | _, _ => .error "unsupported int_ge argument shapes"
      else
        .error s!"unsupported predicate '{c.name.name}'"

/-- Compile a list of model constraints. -/
def compileConstraints (env : Store) (names : List String) :
    List ConstraintItem → Except String (List DomConstraint)
  | [] => .ok []
  | c :: rest => do
      let dc ← compileConstraint env names c
      let dcs ← compileConstraints env names rest
      return dc :: dcs

/-! ## The compiler -/

/-- The final assembly of a successful compile: the slot names,
    domains, and the compiled constraints. -/
def assemble (model : Model) (slots : List (String × List Value))
    (dcs : List DomConstraint) : CompiledProblem DomConstraint :=
  { names := slots.map Prod.fst
    domains := slots.map Prod.snd
    constraints := dcs
    objective := ()
    source := model
    toStore := fun a x =>
      match nameIndex (slots.map Prod.fst) x.name with
      | some i => a[i]?
      | none => parEnv model x }

/-- Compile the explicitly supported FlatZinc fragment to the shared
    `Core.Problem` with `DomConstraint` payloads. Every rejection
    carries a reason. -/
def compileModel (model : Model) : Except String (CompiledProblem DomConstraint) :=
  if model.predicates ≠ [] then
    .error "predicate items are outside the certified fragment"
  else match model.parameters.filter (fun d => parDeclValue d = none) with
  | (_ :: _) => .error "non-scalar parameter in the certified fragment"
  | [] =>
    match model.variables.filter (fun d => match d with
      | .basic _ _ _ none => false
      | _ => true) with
    | (_ :: _) => .error "non-basic variable in the certified fragment"
    | [] =>
      match model.solve with
      | .satisfy _ =>
          match slotsChecked model with
          | .error e => .error e
          | .ok slots =>
              match compileConstraints (parEnv model)
                  (slots.map Prod.fst) model.constraints with
              | .error e => .error e
              | .ok dcs => .ok (assemble model slots dcs)
      | _ => .error "optimize items are outside the certified fragment"

/-- A model belongs to the direct solver fragment exactly when compilation
    succeeds. -/
def SupportedModel (model : Model) : Prop :=
  ∃ problem : CompiledProblem DomConstraint, compileModel model = .ok problem

end LeanFzn.Solver.Direct

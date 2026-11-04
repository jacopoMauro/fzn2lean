/-
File: LeanFzn/Compiler/Compile.lean

Purpose:
  Contains only executable compilation and constraint-evaluation code for the
  direct LeanFzn.Solver: the FlatZinc-fragment compiler to `Core.Problem`
  (`DomConstraint` payloads) and its Boolean leaf evaluator. Semantic
  correspondence proofs live in Proofs/Compile.

The accepted fragment (each case accompanied by exact
semantic-correspondence theorems in Proofs/Compile):

* parameters: scalar `int`/`bool` literals (used by constraint arguments);
* variables: initializer-free basic `var` declarations with finite domains
  (`var bool`, `var lo..hi`, `var {..}`) — the same slot extraction as
  `LeanFzn/Compiler/Domain.lean`'s `slotsChecked`;
* constraints: the 21 extractable shapes of `LeanFzn.Solver/Extract.lean`
  (`int_eq`/`int_ne`/`int_le`/`int_plus`/`all_different`/`int_lin_eq`/
  `int_lin_le`/`int_times`/`int_min`/`int_max`/`int_abs`/`int_lt`/
  `bool_not`/`bool_and`/`bool_or` on slot and literal arguments), PLUS
  the auxiliary-slot literal shapes of the expansion below
  (`int_times(x,y,k)` / `int_times(x,k,y)` / `int_times(k,x,y)` /
  the two-literal times shapes `int_times(x,k,k')` /
  `int_times(k,x,k')` / `int_times(k,k',x)` / `int_ne(x,k)` /
  `int_ne(k,x)` / `bool_and(x,y,true)` / `bool_and(x,y,false)` /
  `bool_or(x,y,true)` / `bool_or(x,y,false)`);
* solve item: `solve satisfy`.

Anything else (predicate items, array parameters/variables, set
variables, other predicate names, failed extraction) is rejected with
`unsupported` before search. (The two-literal times shapes above
are the ONE exception to the old "int_times with TWO literal
arguments" rejection: their restatement over two pinned aux slots is
sound for every `k` — including the `k = 0` corner, where the
timesSlot leaf check itself decides the (un)satisfiability.)

## The auxiliary-slot expansion (the literal-argument shapes)

A FlatZinc call such as `int_times(x, y, 6)` pins its result argument
to the literal `6`: its FlatZinc semantics `z = x*y` composes with
`z = 6` to `x*y = 6`. The compiler expresses such pins through
AUXILIARY SLOTS: fresh slots (one per pinning constraint, in
constraint order) whose domains are singletons carrying the pinned
value. The pre-pass `expandPlan` computes the aux slots and rewrites
each pinning constraint into constraints of the ALREADY-CERTIFIED
shapes over the aux slot names (`int_times(x,y,k)` becomes
`int_times(x,y,AUX)` with `AUX`'s domain `{k}`; `bool_and(x,y,false)`
becomes `bool_and(x,y,AUX)` + `bool_not(AUX,true)` with `AUX`'s
domain `{false}`; `bool_and(x,y,true)` becomes `bool_not(x,false)` +
`bool_not(y,false)`; etc. — each compiled shape is exactly the
DomConstraint the aux design prescribes: `timesSlot i j AUX`,
`neSlot i AUX`, `boolAndSlot i j AUX` + the `constEq AUX` pin, or two
`constEq` pin constraints). The rewritten constraint list is compiled
by the UNCHANGED `compileConstraints`/`compileConstraint`, so every
existing compiler inversion (including the frozen LCG consumers)
applies verbatim.

Aux slot names: `_aux_` followed by a run of `$` characters whose
length dominates every model slot/parameter name length (and encodes
the slot's index). `$` cannot appear in a lexed identifier, and the
length domination makes the name fresh even against hand-built
models; a model variable or parameter can never collide with an aux
slot name.

Dependencies:
  - LeanFzn.Compiler.Types: compiled representations.
  - LeanFzn.Compiler.Domain: slot extraction.
  - LeanFzn.Compiler.Extract: constraint-shape extraction.
  - LeanFzn.Solver.Propagation.DomainConstraints: `DomConstraint` and `satisfiedB`.
  - LeanFzn.Semantics.StdLib: store-level predicate semantics bridge.

DAG:
  LeanFzn.Compiler.Types + LeanFzn.Compiler.Domain + LeanFzn.Compiler.Extract
  + LeanFzn.Solver.Propagation.DomainConstraints -> LeanFzn.Compiler.Compile
-/

import LeanFzn.Compiler.Types
import LeanFzn.Compiler.Domain
import LeanFzn.Compiler.Extract
import LeanFzn.Solver.Propagation.DomainConstraints
open LeanFzn.Compiler.Domains


namespace LeanFzn.Compiler
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation
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
    EXACTLY the extracted ones (`LeanFzn.Solver/Extract.lean`'s 21 shapes);
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
      else if c.name.name = "bool_not" ∧ c.args.length = 2 then
        -- bool_not(x, b) means x = !b: the slot is pinned to the
        -- negated literal (the literal may also be a parameter
        -- resolved to its declared bool value)
        do
        let a0 ← argOf c 0
        let a1 ← argOf c 1
        match compileArgVal env names a0, compileArgVal env names a1 with
        | .ok (.slotRef i), .ok (.litVal (.bool b)) =>
            .ok (.constEq i (.bool (!b)))
        | .ok (.litVal (.bool b)), .ok (.slotRef j) =>
            .ok (.constEq j (.bool (!b)))
        | .error e, _ => .error e
        | _, .error e => .error e
        | _, _ => .error "unsupported bool_not argument shapes"
      else if c.name.name = "bool_and" ∧ c.args.length = 3 then
        -- bool_and with a bool-literal operand: a false operand
        -- forces the result slot to false; a true operand identifies
        -- the result with the other operand's slot
        do
        let a0 ← argOf c 0
        let a1 ← argOf c 1
        let a2 ← argOf c 2
        match compileArgVal env names a0, compileArgVal env names a1,
            compileArgVal env names a2 with
        | .ok (.slotRef i), .ok (.litVal (.bool true)), .ok (.slotRef k) =>
            .ok (.eqSlot i k)
        | .ok (.slotRef _i), .ok (.litVal (.bool false)), .ok (.slotRef k) =>
            .ok (.constEq k (.bool false))
        | .ok (.litVal (.bool true)), .ok (.slotRef j), .ok (.slotRef k) =>
            .ok (.eqSlot j k)
        | .ok (.litVal (.bool false)), .ok (.slotRef _j), .ok (.slotRef k) =>
            .ok (.constEq k (.bool false))
        | .error e, _, _ => .error e
        | _, .error e, _ => .error e
        | _, _, .error e => .error e
        | _, _, _ => .error "unsupported bool_and argument shapes"
      else if c.name.name = "bool_or" ∧ c.args.length = 3 then
        -- bool_or with a bool-literal operand: a true operand forces
        -- the result slot to true; a false operand identifies the
        -- result with the other operand's slot
        do
        let a0 ← argOf c 0
        let a1 ← argOf c 1
        let a2 ← argOf c 2
        match compileArgVal env names a0, compileArgVal env names a1,
            compileArgVal env names a2 with
        | .ok (.slotRef _i), .ok (.litVal (.bool true)), .ok (.slotRef k) =>
            .ok (.constEq k (.bool true))
        | .ok (.slotRef i), .ok (.litVal (.bool false)), .ok (.slotRef k) =>
            .ok (.eqSlot i k)
        | .ok (.litVal (.bool true)), .ok (.slotRef _j), .ok (.slotRef k) =>
            .ok (.constEq k (.bool true))
        | .ok (.litVal (.bool false)), .ok (.slotRef j), .ok (.slotRef k) =>
            .ok (.eqSlot j k)
        | .error e, _, _ => .error e
        | _, .error e, _ => .error e
        | _, _, .error e => .error e
        | _, _, _ => .error "unsupported bool_or argument shapes"
      else if c.name.name = "set_in" ∧ c.args.length = 2 then
        -- C0 set membership over a constant set: a slot identifier
        -- against a set literal (or a parameter resolved to one)
        do
        let a0 ← argOf c 0
        let a1 ← argOf c 1
        match a0, a1 with
        | .ident xa, .lit (.set sa) =>
            match nameIndex names xa.name with
            | some i => .ok (.setInSlot i sa.denote)
            | none => .error s!"unresolved name '{xa.name}' in set_in"
        | .ident xa, .ident pa =>
            match nameIndex names xa.name with
            | some i =>
                match nameIndex names pa.name with
                | none =>
                    match env pa with
                    | some (.setOfInt sv) => .ok (.setInSlot i sv)
                    | _ => .error "set_in over a non-set parameter"
                | some _ =>
                    .error "set_in over a slot-typed set argument"
            | none => .error s!"unresolved name '{xa.name}' in set_in"
        | _, _ => .error "unsupported set_in argument shapes"
      else if c.name.name = "set_in_reif" ∧ c.args.length = 3 then
        -- C0 reified set membership over a constant set: the reif
        -- operand may be a slot identifier or a Boolean literal (a
        -- literal false forces non-membership, a literal true
        -- membership, expressed as the unreified constraint)
        do
        let a0 ← argOf c 0
        let a1 ← argOf c 1
        let a2 ← argOf c 2
        match a0, a1, a2 with
        | .ident xa, .lit (.set sa), .ident ra =>
            match nameIndex names xa.name, nameIndex names ra.name with
            | some i, some k => .ok (.setInReifSlot i sa.denote k)
            | some _, none => .error s!"unresolved name '{ra.name}' in set_in_reif"
            | none, _ => .error s!"unresolved name '{xa.name}' in set_in_reif"
        | .ident xa, .lit (.set sa), .lit (.bool true) =>
            match nameIndex names xa.name with
            | some i => .ok (.setInSlot i sa.denote)
            | none => .error s!"unresolved name '{xa.name}' in set_in_reif"
        | .ident xa, .lit (.set sa), .lit (.bool false) =>
            -- x ∉ S: the COMPLEMENT of a finite set is infinite, so
            -- no constant payload can express it; the certified route
            -- would need one disequality piece per element (the aux
            -- expansion's pinning machinery), reported precisely for
            -- now.
            .error "set_in_reif with a false literal is outside the certified fragment (complement of a finite set)"
        | .ident xa, .ident pa, .ident ra =>
            match nameIndex names xa.name with
            | some i =>
                match nameIndex names ra.name with
                | some k =>
                    match nameIndex names pa.name, env pa with
                    | none, some (.setOfInt sv) =>
                        .ok (.setInReifSlot i sv k)
                    | some _, _ =>
                        .error "set_in_reif over a slot-typed set argument"
                    | none, _ =>
                        .error "set_in_reif over a non-set parameter"
                | none => .error s!"unresolved name '{ra.name}' in set_in_reif"
            | none => .error s!"unresolved name '{xa.name}' in set_in_reif"
        | _, _, _ => .error "unsupported set_in_reif argument shapes"
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

/-! ## The auxiliary-slot expansion (the literal-argument shapes)

The nine literal-argument shapes that pin a predicate's operand to a
scalar literal. Each is classified syntactically (`auxShapeOf`),
rewritten into already-certified constraint shapes over a FRESH aux
slot name (`AuxShape.expand`), and pinned by giving that aux slot a
SINGLETON domain (`AuxShape.pin`). `expandPlan` performs the
constraint-list pre-pass: it computes, in one walk, the aux slots
(the two-pass design's slot-list extension) and the expanded
constraint list, keeping the aux counter consistent between the two
by construction. -/

/-- The auxiliary-slot shape classification of one constraint item
    (purely syntactic: the predicate name and the argument shapes;
    no name resolution). `none` means the constraint is not one of
    the nine pinning shapes (it passes through the expansion
    unchanged, to be compiled — or rejected — by the existing
    paths). -/
inductive AuxShape where
  /-- `int_times(x, y, k)`: an aux slot carries `x*y`, pinned to
      `k` (domain `[.int k]`). -/
  | timesRK (x y : Ident) (k : Int)
  /-- `int_times(x, k, y)`: an aux slot carries the literal `k`
      (domain `[.int k]`). -/
  | timesKR (x y : Ident) (k : Int)
  /-- `int_times(k, x, y)`: an aux slot carries the literal `k`
      (domain `[.int k]`). -/
  | timesKR' (x y : Ident) (k : Int)
  /-- `int_times(x, k, k')`: the first aux slot carries the literal
      `k` (domain `[.int k]`), the second the literal `k'` (domain
      `[.int k']`) — the restatement `timesSlot x AUX₁ AUX₂` is the
      uniform compilation for every `k` (including `k = 0`, where
      `x·0 = k'` either refutes at the leaf — `k' ≠ 0` — or is
      vacuous — `k' = 0`, every `x`). -/
  | timesRKK (x : Ident) (k k' : Int)
  /-- `int_times(k, x, k')`: the first aux slot carries the literal
      `k` (domain `[.int k]`), the second the literal `k'` (domain
      `[.int k']`). -/
  | timesKRR (x : Ident) (k k' : Int)
  /-- `int_times(k, k', x)`: the first aux slot carries the literal
      `k` (domain `[.int k]`), the second the literal `k'` (domain
      `[.int k']`) — the result slot is `x` itself. -/
  | timesKKR (x : Ident) (k k' : Int)
  /-- `int_ne(x, k)`: an aux slot carries the literal `k` (domain
      `[.int k]`). -/
  | neRK (x : Ident) (k : Int)
  /-- `int_ne(k, x)`: an aux slot carries the literal `k` (domain
      `[.int k]`). -/
  | neKR (x : Ident) (k : Int)
  /-- `bool_and(x, y, true)`: `x ∧ y = true` forces both operands
      true — no aux slot. -/
  | andTrue (x y : Ident)
  /-- `bool_and(x, y, false)`: an aux slot carries `x ∧ y`, pinned
      to `false` (domain `[.bool false]`). -/
  | andFalse (x y : Ident)
  /-- `bool_or(x, y, true)`: an aux slot carries `x ∨ y`, pinned
      to `true` (domain `[.bool true]`). -/
  | orTrue (x y : Ident)
  /-- `bool_or(x, y, false)`: `x ∨ y = false` forces both operands
      false — no aux slot. -/
  | orFalse (x y : Ident)
  /-- `int_eq_reif(x, k, r)` (PLAN C5b): an aux slot carries the
      literal `k` (domain `[.int k]`), rewritten to
      `int_eq_reif(x, AUX, r)`. -/
  | eqReifRK (x r : Ident) (k : Int)
  /-- `int_eq_reif(k, x, r)` (PLAN C5b): an aux slot carries the
      literal `k` (domain `[.int k]`). -/
  | eqReifKR (x r : Ident) (k : Int)
  /-- `int_le_reif(x, k, r)` (PLAN C5b): an aux slot carries the
      literal `k` (domain `[.int k]`). -/
  | leReifRK (x r : Ident) (k : Int)
  /-- `int_le_reif(k, x, r)` (PLAN C5b): an aux slot carries the
      literal `k` (domain `[.int k]`). -/
  | leReifKR (x r : Ident) (k : Int)
  /-- `int_ne_reif(x, k, r)` (PLAN C5b): an aux slot carries the
      literal `k` (domain `[.int k]`). -/
  | neReifRK (x r : Ident) (k : Int)
  /-- `int_ne_reif(k, x, r)` (PLAN C5b): an aux slot carries the
      literal `k` (domain `[.int k]`). -/
  | neReifKR (x r : Ident) (k : Int)
  /-- `int_min(x, k, z)` (PLAN C9): an aux slot carries the literal
      `k` (domain `[.int k]`), rewritten to `int_min(x, AUX, z)`
      (`minSlot`, the explained `propMin`). -/
  | minRK (x z : Ident) (k : Int)
  /-- `int_min(k, x, z)` (PLAN C9). -/
  | minKR (x z : Ident) (k : Int)
  /-- `int_max(x, k, z)` (PLAN C9). -/
  | maxRK (x z : Ident) (k : Int)
  /-- `int_max(k, x, z)` (PLAN C9). -/
  | maxKR (x z : Ident) (k : Int)
  /-- `int_min(x, y, k)` (PLAN C9 remainder): the LITERAL is the
      RESULT operand (third position). An aux slot carries the literal
      `k` (domain `[.int k]`), rewritten to `int_min(x, y, AUX)`
      (`minSlot`, the explained `propMin`). -/
  | minRRK (x y : Ident) (k : Int)
  /-- `int_max(x, y, k)` (PLAN C9 remainder): the literal RESULT
      operand, rewritten to `int_max(x, y, AUX)` (`maxSlot`). -/
  | maxRRK (x y : Ident) (k : Int)
  /-- `array_int_minimum(r, [e₁, e₂])` (PLAN C9 remainder): the
      two-element array minimum, rewritten into the CHAIN of binary
      `int_min(e₁, e₂, r)` over the element slots themselves
      (`minSlot`, the explained `propMin`) — no aux slot at all. -/
  | minGen2 (e1 e2 r : Ident)
  /-- `array_int_maximum(r, [e₁, e₂])` (PLAN C9 remainder): the
      two-element array maximum, rewritten into the chain
      `int_max(e₁, e₂, r)` (`maxSlot`). -/
  | maxGen2 (e1 e2 r : Ident)
  /-- `bool_xor(x, y, z)` (PLAN C0): the Boolean XOR channel
      `z = (x ^^ y)`, rewritten into the FOUR certified `bool_clause`
      shapes (whose positive/negative literal lists select the
      equivalence clauses `x ∨ y ∨ ¬z`, `¬x ∨ ¬y ∨ ¬z`,
      `¬x ∨ y ∨ z`, `x ∨ ¬y ∨ z`) — no aux slot at all.  Each clause
      compiles to `boolClauseSlot`, is seeded into the clause
      database, and is proved equivalent by the truth-table bridges
      (`bool_xor_of_clauses` / `bool_xor_to_clauses`). -/
  | xorSlots (x y z : Ident)
  /-- `array_int_element(x, [k₁..kₙ], k)` (PLAN C0 element values):
      the table is all integer literals and the VALUE operand is a
      literal. An aux slot carries `k` (domain `[.int k]`), and the
      constraint is rewritten to the certified all-slot-table shape
      `array_int_element(x, [k₁..kₙ], AUX)`. -/
  | constElemValL (x : Ident) (xs : List Int) (k : Int)
  /-- `array_var_int_element(x, pre ++ [k] ++ post, y)` (PLAN C0
      element values): the table has EXACTLY ONE integer-literal
      element. An aux slot carries `k` (domain `[.int k]`), and the
      table is rewritten to the all-slot shape
      `array_var_int_element(x, pre ++ [AUX] ++ post, y)` — the
      already-certified `arrayVarIntElementSlot` route. -/
  | varElemTabLit (x y : Ident) (pre : List Ident) (k : Int)
      (post : List Ident)
  /-- `array_var_int_element(x, pre ++ [k] ++ post, k')` (PLAN C0
      element values): the table has exactly one literal element AND
      the VALUE operand is a literal. The FIRST aux slot carries `k`,
      the SECOND carries `k'` (its successor aux name); the rewrite is
      `array_var_int_element(x, pre ++ [AUX] ++ post, AUX₂)`. -/
  | varElemTabValLit (x : Ident) (pre : List Ident) (k : Int)
      (post : List Ident) (k' : Int)
  /-- `array_var_int_element(x, tab, y)` (PLAN C0 element values,
      k-LITERAL generalization): `tab` is slot identifiers mixed with
      k ≥ 2 integer literals and the value operand is a slot. One aux
      slot per literal (in table order, named by position) is pinned
      to it, and the table is rewritten to the all-slot shape
      `array_var_int_element(x, tab', y)` — the already-certified
      `arrayVarIntElementSlot` route. -/
  | varElemTabKs (x y : Ident) (tab : ArrayLiteral)
  /-- `array_var_int_element(x, tab, k')` (PLAN C0 element values,
      k-literal generalization): as `varElemTabKs` with the VALUE
      operand a literal, which the LAST pinned aux (the k-th
      successor slot) carries. -/
  | varElemTabValKs (x : Ident) (tab : ArrayLiteral) (k' : Int)
  /-- `array_var_bool_element(x, tab, y)` (PLAN C0 element values, bool
      tables): `tab` is slot identifiers mixed with k ≥ 1 Boolean
      literals and the value operand is a slot. One aux slot per
      literal (in table order, named by position) is pinned to it, and
      the table is rewritten to the all-slot shape
      `array_var_bool_element(x, tab', y)` — the already-certified
      `arrayVarBoolElementSlot` route. -/
  | varBoolTabLits (x y : Ident) (tab : ArrayLiteral)
  /-- `array_var_bool_element(x, tab, b')` (PLAN C0 element values,
      bool tables): `tab` is slot identifiers and Boolean literals
      (k ≥ 0) and the VALUE operand is the Boolean literal `b'`, which
      the LAST pinned aux (the k-th successor slot) carries. -/
  | varBoolTabValLit (x : Ident) (tab : ArrayLiteral) (b' : Bool)

/-- Every element of an array literal is a slot identifier, in order
    (PLAN C0 element values). -/
def allIdents : ArrayLiteral → Option (List Ident)
  | [] => some []
  | .ident x :: rest => (allIdents rest).map (fun is => x :: is)
  | _ => none

/-- Split an element table at its unique integer-literal element
    (PLAN C0 element values): the slot identifiers before it, the
    literal, and the slot identifiers after it. Returns `none` unless
    the table is slot identifiers with EXACTLY ONE integer literal in
    one position. -/
def splitOneLit : ArrayLiteral → Option (List Ident × Int × List Ident)
  | [] => none
  | .lit (.int k) :: rest => (allIdents rest).map (fun is => ([], k, is))
  | .ident x :: rest =>
      (splitOneLit rest).map (fun t => (x :: t.1, t.2.1, t.2.2))
  | _ => none

/-- The integer literals of a mixed element table, in order (PLAN C0
    element values, k-literal generalization): the entries that are
    integer literals; the other entries contribute nothing. -/
def tabLitVals : ArrayLiteral → List Int
  | [] => []
  | .lit (.int k) :: rest => k :: tabLitVals rest
  | _ :: rest => tabLitVals rest

/-- The k-literal mixed-table classifier (PLAN C0 element values,
    k-literal generalization): every entry is a slot identifier or an
    integer literal, and there are AT LEAST TWO integer literals. -/
def mixTabOkB (elems : ArrayLiteral) : Bool :=
  elems.all (fun b => match b with
    | .ident _ => true
    | .lit (.int _) => true
    | _ => false) &&
  decide (2 ≤ (tabLitVals elems).length)

/-- The mixed table with each integer-literal entry replaced, in
    order, by the corresponding aux identifier (PLAN C0 element
    values, k-literal generalization). -/
def mixSubst : ArrayLiteral → List Ident → ArrayLiteral
  | [], _ => []
  | .lit (.int _) :: rest, a :: as => .ident a :: mixSubst rest as
  | .lit (.int k) :: rest, [] => .lit (.int k) :: mixSubst rest []
  | .ident x :: rest, as => .ident x :: mixSubst rest as
  | .lit l :: rest, as => .lit l :: mixSubst rest as

/-- The identifier list underlying `mixSubst`: the same table with each
    integer-literal entry replaced by the corresponding aux NAME. -/
def mixIdents : ArrayLiteral → List Ident → List Ident
  | [], _ => []
  | .lit (.int _) :: rest, a :: as => a :: mixIdents rest as
  | .lit (.int _) :: rest, [] => mixIdents rest []
  | .ident x :: rest, as => x :: mixIdents rest as
  | .lit _ :: rest, as => mixIdents rest as

/-- The Boolean literals of a mixed element table, in order (the bool
    twin of `tabLitVals`). -/
def tabBoolVals : ArrayLiteral → List Bool
  | [] => []
  | .lit (.bool b) :: rest => b :: tabBoolVals rest
  | _ :: rest => tabBoolVals rest

/-- The bool-literal mixed-table classifier with a SLOT value: every
    entry is a slot identifier or a Boolean literal, with AT LEAST ONE
    Boolean literal. -/
def boolLitTabOkB (elems : ArrayLiteral) : Bool :=
  elems.all (fun b => match b with
    | .ident _ => true
    | .lit (.bool _) => true
    | _ => false) &&
  decide (1 ≤ (tabBoolVals elems).length)

/-- The bool-literal mixed-table classifier with a LITERAL value: every
    entry is a slot identifier or a Boolean literal (ANY number of
    literals, including none). -/
def boolTabOkB (elems : ArrayLiteral) : Bool :=
  elems.all (fun b => match b with
    | .ident _ => true
    | .lit (.bool _) => true
    | _ => false)

/-- The mixed bool table with each Boolean-literal entry replaced, in
    order, by the corresponding aux identifier. -/
def mixSubstB : ArrayLiteral → List Ident → ArrayLiteral
  | [], _ => []
  | .lit (.bool _) :: rest, a :: as => .ident a :: mixSubstB rest as
  | .lit (.bool b) :: rest, [] => .lit (.bool b) :: mixSubstB rest []
  | .ident x :: rest, as => .ident x :: mixSubstB rest as
  | .lit l :: rest, as => .lit l :: mixSubstB rest as

/-- The identifier list underlying `mixSubstB`. -/
def mixIdentsB : ArrayLiteral → List Ident → List Ident
  | [], _ => []
  | .lit (.bool _) :: rest, a :: as => a :: mixIdentsB rest as
  | .lit (.bool _) :: rest, [] => mixIdentsB rest []
  | .ident x :: rest, as => x :: mixIdentsB rest as
  | .lit _ :: rest, as => mixIdentsB rest as

/-- The all-literal integer table of the `constElemValL` shape. -/
def litTab (xs : List Int) : ArrayLiteral :=
  xs.map (fun k => .lit (.int k))

/-- The mixed table with the literal at the split position replaced by
    a slot name (PLAN C0 element values). -/
def auxTab (pre : List Ident) (aux : Ident) (post : List Ident) : ArrayLiteral :=
  pre.map (fun x => .ident x) ++ [.ident aux] ++ post.map (fun x => .ident x)

/-- The mixed table with the literal at the split position (PLAN C0
    element values). -/
def litSplitTab (pre : List Ident) (k : Int) (post : List Ident) : ArrayLiteral :=
  pre.map (fun x => .ident x) ++ [.lit (.int k)] ++ post.map (fun x => .ident x)

/-- The int literal-value element tables with ANY number of literal
    table entries: two or more literals, or an all-slot table (the
    value rides its own pinned slot in either case). -/
def intValTabOkB (elems : ArrayLiteral) : Bool :=
  mixTabOkB elems || (allIdents elems).isSome

/-- The PLAN C0 element-value shapes: the value-literal
    `array_int_element` over an all-literal table, and the one-literal
    mixed `array_var_int_element` tables (slot or literal value
    operand; both classified, with their exactness cases in
    `Proofs/Exact`). Kept as a separate classifier so the `auxShapeOf`
    inversions of the older shapes stay shallow; the new arms of
    `auxShapeOf` hand the element names over to this function. -/
def elemAuxShapeOf (c : ConstraintItem) : Option AuxShape :=
  match c.name.name with
  | "array_int_element" =>
      match c.args with
      | [.basic (.ident x), .array elems, .basic (.lit (.int k))] =>
          match intLits elems with
          | some xs => some (.constElemValL x xs k)
          | none => none
      | _ => none
  -- PLAN C0 element values: the `array_var_int_element` mixed tables
  -- with a slot value (`varElemTabLit`/`varElemTabKs`) or a literal
  -- value (`varElemTabValLit`/`varElemTabValKs`). The pinned aux slots
  -- fill the table's literal positions, so the rewritten table is the
  -- all-slot shape the unchanged extraction path already compiles.
  -- EXACTLY ONE literal uses the one-slot shapes (the k = 1
  -- instance); TWO OR MORE literals use the k-literal list-of-pins
  -- shapes.
  | "array_var_int_element" =>
      match c.args with
      | [.basic (.ident x), .array elems, .basic (.ident y)] =>
          match splitOneLit elems with
          | some (pre, k, post) => some (.varElemTabLit x y pre k post)
          | none =>
              if mixTabOkB elems then some (.varElemTabKs x y elems)
              else none
      | [.basic (.ident x), .array elems, .basic (.lit (.int k'))] =>
          match splitOneLit elems with
          | some (pre, k, post) => some (.varElemTabValLit x pre k post k')
          | none =>
              if intValTabOkB elems then some (.varElemTabValKs x elems k')
              else none
      | _ => none
  -- PLAN C0 element values, bool tables: the `array_var_bool_element`
  -- mixed tables with a slot value (`varBoolTabLits`, at least one
  -- Boolean literal) or a literal value (`varBoolTabValLit`, any
  -- number of literals including none). The pinned aux slots fill the
  -- table's literal positions, so the rewritten table is the all-slot
  -- shape the unchanged extraction path already compiles.
  | "array_var_bool_element" =>
      match c.args with
      | [.basic (.ident x), .array elems, .basic (.ident y)] =>
          if boolLitTabOkB elems then some (.varBoolTabLits x y elems)
          else none
      | [.basic (.ident x), .array elems, .basic (.lit (.bool b'))] =>
          if boolTabOkB elems then some (.varBoolTabValLit x elems b')
          else none
      | _ => none
  | _ => none

/-- The syntactic classification of the nine pinning shapes. -/
def auxShapeOf (c : ConstraintItem) : Option AuxShape :=
  match c.name.name with
  | "int_times" =>
      match c.args with
      | [.basic (.ident x), .basic (.ident y), .basic (.lit (.int k))] =>
          some (.timesRK x y k)
      | [.basic (.ident x), .basic (.lit (.int k)), .basic (.ident y)] =>
          some (.timesKR x y k)
      | [.basic (.lit (.int k)), .basic (.ident x), .basic (.ident y)] =>
          some (.timesKR' x y k)
      | [.basic (.ident x), .basic (.lit (.int k)), .basic (.lit (.int k'))] =>
          some (.timesRKK x k k')
      | [.basic (.lit (.int k)), .basic (.ident x), .basic (.lit (.int k'))] =>
          some (.timesKRR x k k')
      | [.basic (.lit (.int k)), .basic (.lit (.int k')), .basic (.ident x)] =>
          some (.timesKKR x k k')
      | _ => none
  | "int_ne" =>
      match c.args with
      | [.basic (.ident x), .basic (.lit (.int k))] => some (.neRK x k)
      | [.basic (.lit (.int k)), .basic (.ident x)] => some (.neKR x k)
      | _ => none
  | "bool_and" =>
      match c.args with
      | [.basic (.ident x), .basic (.ident y), .basic (.lit (.bool true))] =>
          some (.andTrue x y)
      | [.basic (.ident x), .basic (.ident y), .basic (.lit (.bool false))] =>
          some (.andFalse x y)
      | _ => none
  | "bool_or" =>
      match c.args with
      | [.basic (.ident x), .basic (.ident y), .basic (.lit (.bool true))] =>
          some (.orTrue x y)
      | [.basic (.ident x), .basic (.ident y), .basic (.lit (.bool false))] =>
          some (.orFalse x y)
      | _ => none
  -- PLAN C5b: the reified families with ONE literal operand. `r` stays
  -- a slot identifier; the literal is pinned into a fresh aux slot.
  | "int_eq_reif" =>
      match c.args with
      | [.basic (.ident x), .basic (.lit (.int k)), .basic (.ident r)] =>
          some (.eqReifRK x r k)
      | [.basic (.lit (.int k)), .basic (.ident x), .basic (.ident r)] =>
          some (.eqReifKR x r k)
      | _ => none
  | "int_le_reif" =>
      match c.args with
      | [.basic (.ident x), .basic (.lit (.int k)), .basic (.ident r)] =>
          some (.leReifRK x r k)
      | [.basic (.lit (.int k)), .basic (.ident x), .basic (.ident r)] =>
          some (.leReifKR x r k)
      | _ => none
  | "int_ne_reif" =>
      match c.args with
      | [.basic (.ident x), .basic (.lit (.int k)), .basic (.ident r)] =>
          some (.neReifRK x r k)
      | [.basic (.lit (.int k)), .basic (.ident x), .basic (.ident r)] =>
          some (.neReifKR x r k)
      | _ => none
  -- PLAN C9: min/max with ONE literal operand (slot form over a pinned aux).
  | "int_min" =>
      match c.args with
      | [.basic (.ident x), .basic (.lit (.int k)), .basic (.ident z)] =>
          some (.minRK x z k)
      | [.basic (.lit (.int k)), .basic (.ident x), .basic (.ident z)] =>
          some (.minKR x z k)
      -- PLAN C9 remainder: the LITERAL is the RESULT operand
      | [.basic (.ident x), .basic (.ident y), .basic (.lit (.int k))] =>
          some (.minRRK x y k)
      | _ => none
  | "int_max" =>
      match c.args with
      | [.basic (.ident x), .basic (.lit (.int k)), .basic (.ident z)] =>
          some (.maxRK x z k)
      | [.basic (.lit (.int k)), .basic (.ident x), .basic (.ident z)] =>
          some (.maxKR x z k)
      -- PLAN C9 remainder: the LITERAL is the RESULT operand
      | [.basic (.ident x), .basic (.ident y), .basic (.lit (.int k))] =>
          some (.maxRRK x y k)
      | _ => none
  -- PLAN C9 remainder: the two-element ARRAY shapes chain over the
  -- element slots themselves (no aux slot, no pin).
  | "array_int_maximum" =>
      match c.args with
      | [.basic (.ident r), .array [.ident e1, .ident e2]] =>
          some (.maxGen2 e1 e2 r)
      | _ => none
  | "array_int_minimum" =>
      match c.args with
      | [.basic (.ident r), .array [.ident e1, .ident e2]] =>
          some (.minGen2 e1 e2 r)
      | _ => none
  -- PLAN C0: the Boolean XOR channel over three slot identifiers.
  | "bool_xor" =>
      match c.args with
      | [.basic (.ident x), .basic (.ident y), .basic (.ident z)] =>
          some (.xorSlots x y z)
      | _ => none
  -- PLAN C0 element values: the value-literal `array_int_element` over
  -- an all-literal table, and the one-literal mixed tables of
  -- `array_var_int_element` (with a slot or a literal value operand).
  | _ => elemAuxShapeOf c

/-- The aux slot's pinned value: `some v` means the shape consumes an
    aux slot whose domain is the singleton `[v]`; `none` means no aux
    slot (the rewrite is purely over the model's own names). The
    TWO-literal times shapes pin their FIRST aux slot here (the
    operand literal `k`) and the SECOND through `pin2`; all other
    shapes have `pin2 = none`. -/
def AuxShape.pin : AuxShape → Option Value
  | .timesRK _ _ k => some (.int k)
  | .timesKR _ _ k => some (.int k)
  | .timesKR' _ _ k => some (.int k)
  | .timesRKK _ k _ => some (.int k)
  | .timesKRR _ k _ => some (.int k)
  | .timesKKR _ k _ => some (.int k)
  | .neRK _ k => some (.int k)
  | .neKR _ k => some (.int k)
  | .eqReifRK _ _ k => some (.int k)
  | .eqReifKR _ _ k => some (.int k)
  | .leReifRK _ _ k => some (.int k)
  | .leReifKR _ _ k => some (.int k)
  | .neReifRK _ _ k => some (.int k)
  | .neReifKR _ _ k => some (.int k)
  | .minRK _ _ k => some (.int k)
  | .minKR _ _ k => some (.int k)
  | .maxRK _ _ k => some (.int k)
  | .maxKR _ _ k => some (.int k)
  | .minRRK _ _ k => some (.int k)
  | .maxRRK _ _ k => some (.int k)
  | .andFalse _ _ => some (.bool false)
  | .orTrue _ _ => some (.bool true)
  | .andTrue _ _ => none
  | .orFalse _ _ => none
  | .minGen2 _ _ _ => none
  | .maxGen2 _ _ _ => none
  | .xorSlots _ _ _ => none
  | .constElemValL _ _ k => some (.int k)
  | .varElemTabLit _ _ _ k _ => some (.int k)
  | .varElemTabValLit _ _ k _ _ => some (.int k)
  | .varElemTabKs _ _ _ => none
  | .varElemTabValKs _ _ _ => none
  | .varBoolTabLits _ _ _ => none
  | .varBoolTabValLit _ _ _ => none

/-- The SECOND aux slot's pinned value (`some v` only for the
    two-literal times shapes, whose second literal `k'` needs its own
    pinned slot). -/
def AuxShape.pin2 : AuxShape → Option Value
  | .timesRKK _ _ k' => some (.int k')
  | .timesKRR _ _ k' => some (.int k')
  | .timesKKR _ _ k' => some (.int k')
  | .varElemTabValLit _ _ _ _ k' => some (.int k')
  | _ => none

/-- The pinned values of a shape whose expansion consumes ONE aux slot
    PER PIN (PLAN C0 element values, k-literal generalization): the
    table's integer literals in order, plus the value literal where
    the value operand is a literal. Empty for every other shape (whose
    pins are consumed through `pin`/`pin2`). -/
def AuxShape.pinsK : AuxShape → List Value
  | .varElemTabKs _ _ tab => (tabLitVals tab).map Value.int
  | .varElemTabValKs _ tab k' => (tabLitVals tab).map Value.int ++ [.int k']
  | .varBoolTabLits _ _ tab => (tabBoolVals tab).map Value.bool
  | .varBoolTabValLit _ tab b' => (tabBoolVals tab).map Value.bool ++ [.bool b']
  | _ => []

/-- The successor aux identifier: the second aux slot's name is the
    first's name with one more `$` (its dollar-run is one longer, so
    it encodes the next position). -/
def nextAuxIdent (aux : Ident) : Ident :=
  Ident.mk (aux.name.push '$')

/-- The first `k` aux identifiers of the successor chain from `aux`:
    `[aux, aux⁺, aux⁺⁺, …]` (the k-literal element tables' pinned
    slots, in table order). -/
def auxChain (aux : Ident) : Nat → List Ident
  | 0 => []
  | k + 1 => aux :: auxChain (nextAuxIdent aux) k

/-- The `k`-th aux identifier of the successor chain from `aux`
    (0-based: `auxChainLast aux 0 = aux`). -/
def auxChainLast (aux : Ident) : Nat → Ident
  | 0 => aux
  | k + 1 => auxChainLast (nextAuxIdent aux) k

/-- The rewritten constraints of a pinning shape, as a function of
    the aux slot's identifier (ignored by the two no-slot shapes).
    Every rewritten constraint is of an already-certified shape: the
    compiler's `extractConstraint`/`compileConstraint` paths compile
    each one exactly as the aux design prescribes. The TWO-literal
    times shapes place their second operand (or both operands, for
    the result-position shape) on the successor aux identifier. -/
def AuxShape.expand : AuxShape → Ident → List ConstraintItem
  | .timesRK x y _, aux =>
      [{ name := Ident.mk "int_times"
       , args := [.basic (.ident x), .basic (.ident y), .basic (.ident aux)]
       , anns := [] }]
  | .timesKR x y _, aux =>
      [{ name := Ident.mk "int_times"
       , args := [.basic (.ident x), .basic (.ident aux), .basic (.ident y)]
       , anns := [] }]
  | .timesKR' x y _, aux =>
      [{ name := Ident.mk "int_times"
       , args := [.basic (.ident aux), .basic (.ident x), .basic (.ident y)]
       , anns := [] }]
  | .timesRKK x _ _, aux =>
      [{ name := Ident.mk "int_times"
       , args := [.basic (.ident x), .basic (.ident aux),
           .basic (.ident (nextAuxIdent aux))]
       , anns := [] }]
  | .timesKRR x _ _, aux =>
      [{ name := Ident.mk "int_times"
       , args := [.basic (.ident aux), .basic (.ident x),
           .basic (.ident (nextAuxIdent aux))]
       , anns := [] }]
  | .timesKKR x _ _, aux =>
      [{ name := Ident.mk "int_times"
       , args := [.basic (.ident aux), .basic (.ident (nextAuxIdent aux)),
           .basic (.ident x)]
       , anns := [] }]
  | .neRK x _, aux =>
      [{ name := Ident.mk "int_ne"
       , args := [.basic (.ident x), .basic (.ident aux)]
       , anns := [] }]
  | .neKR x _, aux =>
      [{ name := Ident.mk "int_ne"
       , args := [.basic (.ident aux), .basic (.ident x)]
       , anns := [] }]
  | .andTrue x y, _ =>
      [{ name := Ident.mk "bool_not"
       , args := [.basic (.ident x), .basic (.lit (.bool false))]
       , anns := [] }
      ,{ name := Ident.mk "bool_not"
       , args := [.basic (.ident y), .basic (.lit (.bool false))]
       , anns := [] }]
  | .andFalse x y, aux =>
      [{ name := Ident.mk "bool_and"
       , args := [.basic (.ident x), .basic (.ident y), .basic (.ident aux)]
       , anns := [] }
      ,{ name := Ident.mk "bool_not"
       , args := [.basic (.ident aux), .basic (.lit (.bool true))]
       , anns := [] }]
  | .orTrue x y, aux =>
      [{ name := Ident.mk "bool_or"
       , args := [.basic (.ident x), .basic (.ident y), .basic (.ident aux)]
       , anns := [] }
      ,{ name := Ident.mk "bool_not"
       , args := [.basic (.ident aux), .basic (.lit (.bool false))]
       , anns := [] }]
  | .orFalse x y, _ =>
      [{ name := Ident.mk "bool_not"
       , args := [.basic (.ident x), .basic (.lit (.bool true))]
       , anns := [] }
      ,{ name := Ident.mk "bool_not"
       , args := [.basic (.ident y), .basic (.lit (.bool true))]
       , anns := [] }]
  | .eqReifRK x r _, aux =>
      [{ name := Ident.mk "int_eq_reif"
       , args := [.basic (.ident x), .basic (.ident aux), .basic (.ident r)]
       , anns := [] }]
  | .eqReifKR x r _, aux =>
      [{ name := Ident.mk "int_eq_reif"
       , args := [.basic (.ident aux), .basic (.ident x), .basic (.ident r)]
       , anns := [] }]
  | .leReifRK x r _, aux =>
      [{ name := Ident.mk "int_le_reif"
       , args := [.basic (.ident x), .basic (.ident aux), .basic (.ident r)]
       , anns := [] }]
  | .leReifKR x r _, aux =>
      [{ name := Ident.mk "int_le_reif"
       , args := [.basic (.ident aux), .basic (.ident x), .basic (.ident r)]
       , anns := [] }]
  | .neReifRK x r _, aux =>
      [{ name := Ident.mk "int_ne_reif"
       , args := [.basic (.ident x), .basic (.ident aux), .basic (.ident r)]
       , anns := [] }]
  | .neReifKR x r _, aux =>
      [{ name := Ident.mk "int_ne_reif"
       , args := [.basic (.ident aux), .basic (.ident x), .basic (.ident r)]
       , anns := [] }]
  | .minRK x z _, aux =>
      [{ name := Ident.mk "int_min"
       , args := [.basic (.ident x), .basic (.ident aux), .basic (.ident z)]
       , anns := [] }]
  | .minKR x z _, aux =>
      [{ name := Ident.mk "int_min"
       , args := [.basic (.ident aux), .basic (.ident x), .basic (.ident z)]
       , anns := [] }]
  | .maxRK x z _, aux =>
      [{ name := Ident.mk "int_max"
       , args := [.basic (.ident x), .basic (.ident aux), .basic (.ident z)]
       , anns := [] }]
  | .maxKR x z _, aux =>
      [{ name := Ident.mk "int_max"
       , args := [.basic (.ident aux), .basic (.ident x), .basic (.ident z)]
       , anns := [] }]
  | .minRRK x y _, aux =>
      [{ name := Ident.mk "int_min"
       , args := [.basic (.ident x), .basic (.ident y), .basic (.ident aux)]
       , anns := [] }]
  | .maxRRK x y _, aux =>
      [{ name := Ident.mk "int_max"
       , args := [.basic (.ident x), .basic (.ident y), .basic (.ident aux)]
       , anns := [] }]
  | .minGen2 e1 e2 r, _ =>
      [{ name := Ident.mk "int_min"
       , args := [.basic (.ident e1), .basic (.ident e2), .basic (.ident r)]
       , anns := [] }]
  | .maxGen2 e1 e2 r, _ =>
      [{ name := Ident.mk "int_max"
       , args := [.basic (.ident e1), .basic (.ident e2), .basic (.ident r)]
       , anns := [] }]
  | .xorSlots x y z, _ =>
      [{ name := Ident.mk "bool_clause"
       , args := [.array [.ident x, .ident y], .array [.ident z]]
       , anns := [] }
      ,{ name := Ident.mk "bool_clause"
       , args := [.array [], .array [.ident x, .ident y, .ident z]]
       , anns := [] }
      ,{ name := Ident.mk "bool_clause"
       , args := [.array [.ident y, .ident z], .array [.ident x]]
       , anns := [] }
      ,{ name := Ident.mk "bool_clause"
       , args := [.array [.ident x, .ident z], .array [.ident y]]
       , anns := [] }]
  | .constElemValL x xs _, aux =>
      [{ name := Ident.mk "array_int_element"
       , args := [.basic (.ident x), .array (litTab xs), .basic (.ident aux)]
       , anns := [] }]
  | .varElemTabLit x y pre _ post, aux =>
      [{ name := Ident.mk "array_var_int_element"
       , args := [.basic (.ident x), .array (auxTab pre aux post),
           .basic (.ident y)]
       , anns := [] }]
  | .varElemTabValLit x pre _ post _, aux =>
      [{ name := Ident.mk "array_var_int_element"
       , args := [.basic (.ident x), .array (auxTab pre aux post),
           .basic (.ident (nextAuxIdent aux))]
       , anns := [] }]
  | .varElemTabKs x y tab, aux =>
      [{ name := Ident.mk "array_var_int_element"
       , args := [.basic (.ident x),
           .array (mixSubst tab (auxChain aux (tabLitVals tab).length)),
           .basic (.ident y)]
       , anns := [] }]
  | .varElemTabValKs x tab _, aux =>
      [{ name := Ident.mk "array_var_int_element"
       , args := [.basic (.ident x),
           .array (mixSubst tab (auxChain aux (tabLitVals tab).length)),
           .basic (.ident (auxChainLast aux (tabLitVals tab).length))]
       , anns := [] }]
  | .varBoolTabLits x y tab, aux =>
      [{ name := Ident.mk "array_var_bool_element"
       , args := [.basic (.ident x),
           .array (mixSubstB tab (auxChain aux (tabBoolVals tab).length)),
           .basic (.ident y)]
       , anns := [] }]
  | .varBoolTabValLit x tab _, aux =>
      [{ name := Ident.mk "array_var_bool_element"
       , args := [.basic (.ident x),
           .array (mixSubstB tab (auxChain aux (tabBoolVals tab).length)),
           .basic (.ident (auxChainLast aux (tabBoolVals tab).length))]
       , anns := [] }]

/-- The longest string length of a list (the aux-name freshness
    fuel: an aux name is made strictly longer than every taken
    name). -/
def maxStrLength : List String → Nat
  | [] => 0
  | t :: rest => max t.length (maxStrLength rest)

/-- A run of `n` `$` characters (the aux-name freshness suffix). -/
def dollarRun : Nat → String
  | 0 => ""
  | n + 1 => (dollarRun n).push '$'

/-- The n-th aux slot's name: `_aux_` followed by a `$`-run whose
    length strictly dominates every taken name's length (and encodes
    `n`, so distinct slots get distinct names). `$` cannot appear in
    a lexed identifier, and the length domination keeps the name
    fresh even against hand-built models. -/
def auxName (taken : List String) (n : Nat) : String :=
  "_aux_" ++ dollarRun (maxStrLength taken + 1 + n)

/-- The fresh aux slots for a LIST of pinned values (PLAN C0 element
    values, k-literal generalization): one slot per value, named by
    its position (the same naming the one- and two-pin machinery
    uses). -/
def auxSlotsK (taken : List String) : Nat → List Value →
    List (String × List Value)
  | _, [] => []
  | base, v :: ps =>
      (auxName taken base, [v]) :: auxSlotsK taken (base + 1) ps

/-- The expansion pre-pass: walks the constraint list with an
    accumulator of already-emitted aux slots, classifying each
    constraint. Non-pinning constraints pass through unchanged; a
    pinning shape consumes ONE fresh aux slot (appended to the
    accumulator, so the slot's counter — the accumulator's length —
    is its final position in the aux slot list) and contributes its
    rewritten constraints; a TWO-literal times shape consumes TWO
    (the second's name is the first's with one more `$`, so it
    occupies the next counter position); a k-literal element table
    consumes ONE aux slot per pin (`pinsK`, again named by position).
    The result is (aux slots, expanded constraints). -/
def expandPlan (taken : List String) :
    List (String × List Value) → List ConstraintItem →
    List (String × List Value) × List ConstraintItem
  | auxs, [] => (auxs, [])
  | auxs, c :: rest =>
      match auxShapeOf c with
      | none =>
          let (auxs', cs') := expandPlan taken auxs rest
          (auxs', c :: cs')
      | some sh =>
          let aux := Ident.mk (auxName taken auxs.length)
          match sh.pin, sh.pin2 with
          | some v, some v2 =>
              let auxs2 := auxs ++
                [(auxName taken auxs.length, [v]),
                 ((auxName taken auxs.length).push '$', [v2])]
              let (auxs', cs') := expandPlan taken auxs2 rest
              (auxs', sh.expand aux ++ cs')
          | some v, none =>
              let (auxs', cs') := expandPlan taken
                (auxs ++ [(auxName taken auxs.length, [v])]) rest
              (auxs', sh.expand aux ++ cs')
          | _, _ =>
              match sh.pinsK with
              | [] =>
                  let (auxs', cs') := expandPlan taken auxs rest
                  (auxs', sh.expand aux ++ cs')
              | v :: vs =>
                  let (auxs', cs') := expandPlan taken
                    (auxs ++ auxSlotsK taken auxs.length (v :: vs)) rest
                  (auxs', sh.expand aux ++ cs')

/-- The model's search slots as a plain list (the empty list when
    slot extraction fails; the certified compile then rejects the
    model before the expansion is consulted). -/
def modelSlots (m : Model) : List (String × List Value) :=
  (slotsChecked m).toOption.getD []

/-- The taken-name list for aux-name freshness: the model's slot
    names and its parameter names (the only names a constraint
    argument can mention). -/
def auxTaken (m : Model) (slots0 : List (String × List Value)) : List String :=
  slots0.map Prod.fst ++ m.parameters.map (fun d => d.name.name)

/-- The model's aux slots (the expansion pre-pass's first
    component), as a function of the model alone. -/
def modelAuxSlots (m : Model) : List (String × List Value) :=
  (expandPlan (auxTaken m (modelSlots m)) [] m.constraints).1

/-- The model's expanded constraint list (the expansion pre-pass's
    second component), as a function of the model alone. -/
def modelExpand (m : Model) : List ConstraintItem :=
  (expandPlan (auxTaken m (modelSlots m)) [] m.constraints).2

/-! ## Direct-`Dom` compiler path (S6)

`compileModel` materializes every slot as a `List Value` and then
canonicalizes it; on wide intervals the same value list is rebuilt
again for the aux-name table and for `modelExpand`.  The twins below
mirror the same control flow but compute the aux-name table from the
slot *names* only and build every large interval with
`Dom.ofIntRange`. -/

/-- The model's search slots as compact domains (empty when extraction
    fails; the compiler rejects before consulting it). -/
def modelSlotsDom (m : Model) : List (String × Dom) :=
  (slotsCheckedDom m).toOption.getD []

/-- The taken-name list for aux-name freshness, from compact slots. -/
def auxTakenDom (m : Model) (slots0 : List (String × Dom)) : List String :=
  slots0.map Prod.fst ++ m.parameters.map (fun d => d.name.name)

/-- One expansion pre-pass on compact slots: the aux value slots are
    mapped to `Dom` once and the two projections are shared, so the
    caller never recomputes the plan. -/
def expandDomOf (m : Model) (slots0 : List (String × Dom)) :
    List (String × Dom) × List ConstraintItem :=
  let ep := expandPlan (auxTakenDom m slots0) [] m.constraints
  (ep.1.map ofListSlot, ep.2)

/-- The expansion pre-pass's first component, from explicit slots. -/
def modelAuxSlotsDomOf (m : Model) (slots0 : List (String × Dom)) :
    List (String × Dom) :=
  (expandDomOf m slots0).1

/-- The expansion pre-pass's second component, from explicit slots. -/
def modelExpandDomOf (m : Model) (slots0 : List (String × Dom)) :
    List ConstraintItem :=
  (expandDomOf m slots0).2

/-- The expansion pre-pass's first component on the compact path. -/
def modelAuxSlotsDom (m : Model) : List (String × Dom) :=
  modelAuxSlotsDomOf m (modelSlotsDom m)

/-- The expansion pre-pass's second component on the compact path. -/
def modelExpandDom (m : Model) : List ConstraintItem :=
  modelExpandDomOf m (modelSlotsDom m)

/-- The compact slot list enumerates like the legacy one. -/
theorem modelSlotsDom_eq (m : Model) :
    (modelSlotsDom m).map enumSlot = modelSlots m := by
  unfold modelSlotsDom modelSlots
  have h := slotsCheckedDom_eq m
  cases hs : slotsChecked m with
  | error e =>
      cases hd : slotsCheckedDom m with
      | error e' => simp [Except.toOption, Option.getD, Except.map, hd, hs] at h ⊢
      | ok slots => simp [Except.toOption, Option.getD, Except.map, hd, hs] at h
  | ok slots =>
      cases hd : slotsCheckedDom m with
      | error e => simp [Except.toOption, Option.getD, Except.map, hd, hs] at h
      | ok slotsDom => simpa [Except.toOption, Option.getD, Except.map, hd, hs] using h

/-- The compact slot list has the legacy slot names. -/
theorem modelSlotsDom_names (m : Model) :
    (modelSlotsDom m).map Prod.fst = (modelSlots m).map Prod.fst := by
  have h := modelSlotsDom_eq m
  rw [← h]
  simp only [List.map_map, Function.comp_def, enumSlot]

/-- The two expansion pre-passes agree (they read the same names). -/
theorem expandPlanDom_eq (m : Model) :
    expandPlan (auxTakenDom m (modelSlotsDom m)) [] m.constraints =
      expandPlan (auxTaken m (modelSlots m)) [] m.constraints := by
  have hn := modelSlotsDom_names m
  simp only [auxTaken, auxTakenDom, hn]

/-- The compact aux slots enumerate like the legacy aux slots. -/
theorem modelAuxSlotsDom_eq (m : Model) :
    (modelAuxSlotsDom m).map enumSlot = modelAuxSlots m := by
  unfold modelAuxSlotsDom modelAuxSlotsDomOf expandDomOf modelAuxSlots
  rw [expandPlanDom_eq, List.map_map]
  simp only [Function.comp_def, enumSlot_ofListSlot]
  rw [show (fun x => x) = id from rfl]
  rw [List.map_id]

/-- The compact aux slots are canonical. -/
theorem modelAuxSlotsDom_canonical (m : Model) :
    (modelAuxSlotsDom m).map canonSlot = modelAuxSlotsDom m := by
  unfold modelAuxSlotsDom modelAuxSlotsDomOf expandDomOf
  rw [List.map_map]
  simp only [Function.comp_def, canonSlot_ofListSlot, List.map_id]

/-- The compact expansion produces the legacy constraints. -/
theorem modelExpandDom_eq (m : Model) : modelExpandDom m = modelExpand m := by
  unfold modelExpandDom modelExpandDomOf expandDomOf modelExpand
  rw [expandPlanDom_eq]

/-! ## The compiler -/

/-- The final assembly of a successful compile: the slot names,
    domains, and the compiled constraints. -/
def assemble (model : Model) (slots : List (String × List Value))
    (dcs : List DomConstraint) : CompiledProblem DomConstraint :=
  { names := slots.map Prod.fst
    domains := slots.map (fun p => Dom.ofList p.2)
    constraints := dcs
    objective := ()
    source := model
    toStore := fun a x =>
      match nameIndex (slots.map Prod.fst) x.name with
      | some i => a[i]?
      | none => parEnv model x }

/-- Fast twin of `assemble`: the same problem shape, with the slot
    domains already in compact form. -/
def assembleDom (model : Model) (slots : List (String × Dom))
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

/-- `assembleDom` and `assemble` build the same problem whenever the
    compact slots enumerate to the legacy slots and are canonical. -/
theorem assembleDom_eq (model : Model) (slots : List (String × Dom))
    (slotValues : List (String × List Value)) (dcs : List DomConstraint)
    (henum : slots.map enumSlot = slotValues)
    (hcanon : slots.map canonSlot = slots) :
    assembleDom model slots dcs = assemble model slotValues dcs := by
  unfold assembleDom assemble
  have hnames : slots.map Prod.fst = slotValues.map Prod.fst := by
    rw [← henum]
    simp only [List.map_map, Function.comp_def, enumSlot]
  have hdom : slots.map Prod.snd =
      slotValues.map (fun p => Dom.ofList p.2) := by
    rw [← henum, List.map_map]
    have hc := congrArg (List.map Prod.snd) hcanon
    simpa [List.map_map, Function.comp_def, enumSlot, canonSlot] using hc.symm
  rw [hnames, hdom]

/-- Compile the explicitly supported FlatZinc fragment to the shared
    `Core.Problem` with `DomConstraint` payloads. Every rejection
    carries a reason. The literal-argument pinning shapes are
    expanded first (fresh aux slots with singleton pinned domains,
    appended to the model's slot list); the expanded constraint list
    is then compiled by the unchanged `compileConstraints`, so the
    aux shapes reach the search through the already-certified
    DomConstraint constructors (`timesSlot`, `neSlot`,
    `boolAndSlot`, `boolOrSlot`, `constEq`). -/
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
              let allSlots := slots ++ modelAuxSlots model
              match compileConstraints (parEnv model)
                  (allSlots.map Prod.fst) (modelExpand model) with
              | .error e => .error e
              | .ok dcs => .ok (assemble model allSlots dcs)
      | _ => .error "optimize items are outside the certified fragment"

/-- Fast twin of `compileModel`: identical guards, rejection reasons
    and expansion, but slot domains are built directly as compact
    `Dom`s and the aux-name table is read from their names only. -/
def compileModelFast (model : Model) :
    Except String (CompiledProblem DomConstraint) :=
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
          match slotsCheckedDom model with
          | .error e => .error e
          | .ok slots =>
              let ep := expandDomOf model slots
              let allSlots := slots ++ ep.1
              match compileConstraints (parEnv model)
                  (allSlots.map Prod.fst) ep.2 with
              | .error e => .error e
              | .ok dcs => .ok (assembleDom model allSlots dcs)
      | _ => .error "optimize items are outside the certified fragment"

/-- **Compiler fast-path equality (S6)**: the direct-`Dom` compiler is
    the logical `compileModel` on every model, including every
    rejection.  This is the kernel equality behind the
    `@[implemented_by]` seam below. -/
theorem compileModelFast_eq (model : Model) :
    compileModelFast model = compileModel model := by
  unfold compileModelFast compileModel
  by_cases hp : model.predicates ≠ []
  · simp [hp]
  · simp only [if_neg hp]
    cases hpar : model.parameters.filter (fun d => parDeclValue d = none) with
    | cons d ds => simp
    | nil =>
        simp only
        cases hvar : model.variables.filter (fun d => match d with
          | .basic _ _ _ none => false
          | _ => true) with
        | cons d ds => simp
        | nil =>
            simp only
            cases hsol : model.solve with
            | satisfy anns =>
                simp only
                cases hs : slotsChecked model with
                | error e =>
                    have hd := slotsCheckedDom_eq model
                    rw [hs] at hd
                    cases hsd : slotsCheckedDom model with
                    | error e' =>
                        simp only [Except.map, hsd] at hd
                        have he : e' = e := by simpa using hd
                        subst he
                        simp [hsd]
                    | ok slotsDom => exact absurd hd (by simp [Except.map, hsd])
                | ok slots =>
                    have hd := slotsCheckedDom_eq model
                    rw [hs] at hd
                    cases hsd : slotsCheckedDom model with
                    | error e => exact absurd hd (by simp [Except.map, hsd])
                    | ok slotsDom =>
                        dsimp only
                        have hms : modelSlotsDom model = slotsDom := by
                          simp [modelSlotsDom, hsd, Except.toOption, Option.getD]
                        have hep1 : (expandDomOf model slotsDom).1 = modelAuxSlotsDom model := by
                          rw [← hms]
                          rfl
                        have hep2 : (expandDomOf model slotsDom).2 = modelExpandDom model := by
                          rw [← hms]
                          rfl
                        simp only [hep1, hep2]
                        have hdenum : slotsDom.map enumSlot = slots := by
                          simpa [Except.map, hsd, enumSlot] using hd
                        have hnames1 : slotsDom.map Prod.fst = slots.map Prod.fst := by
                          rw [← hdenum]
                          simp only [List.map_map, Function.comp_def, enumSlot]
                        have hnames2 : (modelAuxSlotsDom model).map Prod.fst =
                            (modelAuxSlots model).map Prod.fst := by
                          rw [← modelAuxSlotsDom_eq model]
                          simp only [List.map_map, Function.comp_def, enumSlot]
                        have hallnames :
                            (slotsDom ++ modelAuxSlotsDom model).map Prod.fst =
                              (slots ++ modelAuxSlots model).map Prod.fst := by
                          simp only [List.map_append, hnames1, hnames2]
                        simp only [hallnames, modelExpandDom_eq]
                        cases hc : compileConstraints (parEnv model)
                            ((slots ++ modelAuxSlots model).map Prod.fst)
                            (modelExpand model) with
                        | error e => simp [hc]
                        | ok dcs =>
                            simp only [hc]
                            have hen : (slotsDom ++ modelAuxSlotsDom model).map enumSlot =
                                slots ++ modelAuxSlots model := by
                              rw [List.map_append, hdenum, modelAuxSlotsDom_eq]
                            have hcan : (slotsDom ++ modelAuxSlotsDom model).map canonSlot =
                                slotsDom ++ modelAuxSlotsDom model := by
                              rw [List.map_append, slotsCheckedDom_canonical model hsd,
                                modelAuxSlotsDom_canonical model]
                            rw [assembleDom_eq model (slotsDom ++ modelAuxSlotsDom model)
                              (slots ++ modelAuxSlots model) dcs hen hcan]
            | minimize anns obj => simp
            | maximize anns obj => simp

/- The compiled `compileModel` runs the direct-`Dom` twin.  The kernel
   (and every theorem above) still sees the logical `List Value` body;
   only code generation is swapped. -/
attribute [implemented_by compileModelFast] compileModel

/-- A model belongs to the direct LeanFzn.Solver fragment exactly when compilation
    succeeds. -/
def SupportedModel (model : Model) : Prop :=
  ∃ problem : CompiledProblem DomConstraint, compileModel model = .ok problem

end LeanFzn.Compiler

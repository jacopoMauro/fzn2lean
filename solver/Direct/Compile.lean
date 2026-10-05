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
  | _ => none

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
  | .andFalse _ _ => some (.bool false)
  | .orTrue _ _ => some (.bool true)
  | .andTrue _ _ => none
  | .orFalse _ _ => none

/-- The SECOND aux slot's pinned value (`some v` only for the
    two-literal times shapes, whose second literal `k'` needs its own
    pinned slot). -/
def AuxShape.pin2 : AuxShape → Option Value
  | .timesRKK _ _ k' => some (.int k')
  | .timesKRR _ _ k' => some (.int k')
  | .timesKKR _ _ k' => some (.int k')
  | _ => none

/-- The successor aux identifier: the second aux slot's name is the
    first's name with one more `$` (its dollar-run is one longer, so
    it encodes the next position). -/
def nextAuxIdent (aux : Ident) : Ident :=
  Ident.mk (aux.name.push '$')

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

/-- The expansion pre-pass: walks the constraint list with an
    accumulator of already-emitted aux slots, classifying each
    constraint. Non-pinning constraints pass through unchanged; a
    pinning shape consumes ONE fresh aux slot (appended to the
    accumulator, so the slot's counter — the accumulator's length —
    is its final position in the aux slot list) and contributes its
    rewritten constraints; a TWO-literal times shape consumes TWO
    (the second's name is the first's with one more `$`, so it
    occupies the next counter position). The result is (aux slots,
    expanded constraints). -/
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
              let (auxs', cs') := expandPlan taken auxs rest
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

/-- A model belongs to the direct solver fragment exactly when compilation
    succeeds. -/
def SupportedModel (model : Model) : Prop :=
  ∃ problem : CompiledProblem DomConstraint, compileModel model = .ok problem

end LeanFzn.Solver.Direct

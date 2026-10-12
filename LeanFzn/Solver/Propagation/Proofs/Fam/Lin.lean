/-
File: LeanFzn/Solver/Propagation/Proofs/Fam/Lin.lean

Purpose:
  The corrected linear propagator packages: a FIXED `propLinLe2`
  (the `int_lin_le` family with a sound cause discipline — this
  module kills the machine-checked linLe obstruction preserved in
  `LeanFzn/Solver/UIP/Proofs/Obstructions.lean`) and a NEW `propLinEq2` (the
  `int_lin_eq` family), each with its complete proof package:
  the fit-based safe triple, the state-free conflict entitlement,
  the state-free reason validity (Reason.Valid + normalization),
  the standalone registration `propagatorOfProvedBLin`, and the
  obstruction regression.

The fixed cause discipline (the obstruction's cure):
  `propLinLe`'s `causeOfMin`/`causeOfMax` emitted cause literals
  only for ±1 coefficients, so a |c|≠1 term contributing to the
  min-sum `loRest` carried NO pin and the emitted clause was NOT
  integer-valid under `Σ cₜxₜ ≤ b` alone (the witness
  `x + 2t ≤ 0` emitted the unit `[x ≤ 0]`, falsified at the
  solution `x = 3, t = −2`). The fixed discipline pins EVERY
  rest term at the extremum its contribution is taken at, via the
  negation of the witnessing domain bound:

  * min-contribution of term (t, ct) — `causeOfMin`:
      ct > 0 → `posLe t (mnₜ − 1)`   (¬ xₜ ≥ mnₜ), mnₜ = min;
      ct < 0 → `negLe t mxₜ`         (¬ xₜ ≤ mxₜ), mxₜ = max;
      ct = 0 → none (0-contribution needs no pin: 0·xₜ = 0).
  * max-contribution — `causeOfMax`, dually:
      ct > 0 → `negLe t mxₜ`;
      ct < 0 → `posLe t (mnₜ − 1)`;
      ct = 0 → none.

  With every rest term pinned, a point falsifying all literals of
  an emitted clause violates the constraint by pure arithmetic —
  the clause is integer-valid with NO domain, coherence, or trail
  premises (the two-case disjunctions below).

The completeness guard (the second hole, found by the same
discipline): propLinLe's `terms` filterMap silently DROPS a rest
pair whose state domain lacks integer extrema, so the dropped
term contributes to the constraint but is pinned by NO literal —
at a state-free solution its read is still an integer (the
constraint's own dot product forces it), unboundedly below its
"assumed" 0. Witness: `x + y + z ≤ 0` at a state whose slot-`z`
domain is `[]`: the +1 arm on `x` sums only `y`'s min-contribution
and emits `[x ≤ −minY, y ≥ minY]`, falsified by the solution
`x = −minY+1, y = minY, z = −100`. The cure: the deduction arms
fire only when EVERY rest pair has both extrema
(`rest.all (minContrib st ·.isSome)`) — then every contribution
summed into `loRest`/`hiRest` is pinned by a cause, and the
clauses are valid.

  The linEq family (`Σ cₜxₜ = b`): for slot m with coefficient
  cₘ ∈ {1, −1}, BOTH bounds are deduced:

  * cₘ = 1: x_m ≤ b − minΣ_{t≠m}  (min-causes) and
            x_m ≥ b − maxΣ_{t≠m}  (max-causes);
  * cₘ = −1: x_m ≥ minΣ_{t≠m} − b (min-causes) and
             x_m ≤ maxΣ_{t≠m} − b (max-causes).

The GENERAL-COEFFICIENT arms (the |c| ≠ 1 gap, closed): a sweep
position with c ∉ {1, −1} now ALSO narrows via the divided bound —
the FLOOR for the upper bounds and the negated floor (the CEILING)
for the lower ones, both by a POSITIVE divisor (c or −c), where
Lean's Euclidean `Int.div` coincides with floor division:

  * c > 0 (le and eq, the upper bound): x_m ≤ ⌊(b − minΣ)/c⌋
    (the arm `linGenArmHiMin`, min-causes);
  * c < 0 (le and eq, the lower bound):
    x_m ≥ ⌈(minΣ − b)/(−c)⌉ = −⌊(b − minΣ)/(−c)⌋
    (the arm `linGenArmLoMin`, min-causes);
  * c > 0 (eq, the lower bound):
    x_m ≥ ⌈(b − maxΣ)/c⌉ = −⌊(maxΣ − b)/c⌋
    (the arm `linGenArmLoMax`, max-causes);
  * c < 0 (eq, the upper bound): x_m ≤ ⌊(maxΣ − b)/(−c)⌋
    (the arm `linGenArmHiMax`, max-causes).

ROUTE (2) — the STRONG floor bound — was taken (no guarded
weakening): Lean 4.33 core carries the full Euclidean spec
(`Int.ediv_mul_le`, `Int.ediv_mul_add_emod`, `Int.emod_nonneg`,
`Int.emod_lt_of_pos`), from which the floor/ceiling two-case facts
`hi·c ≤ a < hi·c + c` and `(lo − 1)·k < −s` follow (the
division-spec lemmas `lin2_fl_hi_lt`/`lin2_cl_neg_lo_gt` below,
closed by omega); each emitted clause stays integer-valid under the
constraint alone (the four general-c absurd kernels
`lin2_absurd_gen_*`): a falsified head puts `x_m` strictly past the
divided bound, and the floor/ceiling spec turns that into
`Σ > b` (le) or `Σ < b` (eq) against the pinned rest contributions.

Structure of the copies: `propLinLe2` is propLinLe with (1) the
fixed causes, (2) the completeness guard, and (3) the deduce and
sweep kernels hoisted to top-level definitions
(`linDeduceLe`/`linSweep`) so the emission inversions are plain
case analyses; the terms/loRest filterMap-folds are the SAME
functions the six-family module already proves about
(`minContrib`/`sumMin` — propLinLe's `terms` fold verbatim) plus
the dual `maxContrib`/`sumMax`. `propLinEq2` mirrors the sweep
with both bounds per ±1 slot (firstEvent over the two arms).

Verification: `timeout 700 env LEAN_NUM_THREADS=4 lake env lean
LeanFzn/Solver/UIP/Proofs/Fam/Lin.lean` — zero errors.

Dependencies:
  - LeanFzn.Solver.Propagation.Proofs.Propagators: the lin arithmetic
    infrastructure (dotOver, minContrib/sumMin, the zipIdx and
    read bridges, linLe_reads_int/linLe_dot) and everything it
    re-exports (ConstFamilies' narrow inversions, Theory,
    Propagate, Encoding, Fam.Arith's shared reason-validity
    kernels). This module needs the linLe-specific dot/sum
    lemmas that only live there, so it imports that module
    directly (its own additions are otherwise self-contained).

DAG:
  LeanFzn.Solver.UIP.Proofs.Propagators -> LeanFzn.Solver.UIP.Proofs.Fam.Lin (this module)
    -> (future) the registration extension and front-door wiring
       that retire the linLe-free gates.
-/


import LeanFzn.Solver.Propagation.Proofs.ConstFamilies
import LeanFzn.Solver.Propagation.Proofs.Theory
import LeanFzn.Solver.Propagation.Propagate
import LeanFzn.Solver.Propagation.Encoding
import LeanFzn.Compiler.Domain
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Reference


open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Reference

/-! ## The min/max-contribution sums (local twins of the
Propagators.lean kernels — kept structurally identical so the
transfer lemmas apply verbatim) -/

/-- The MIN-contribution of a pair: `ct·mn` for positive
    coefficients, `ct·mx` for negative ones (ct < 0: smallest at
    max). -/
def minContrib (st : State) (p : Int × Nat) : Option (Nat × Int × Int) :=
  match domMinI (st.domains.getD p.2 []), domMaxI (st.domains.getD p.2 []) with
  | some mn, some mx =>
      if p.1 ≥ 0 then some (p.2, p.1, p.1 * mn) else some (p.2, p.1, p.1 * mx)
  | _, _ => none

/-- The folded sum of the min-contributions. -/
def sumMin (st : State) : List (Int × Nat) → Option Int
  | [] => none
  | p :: rest =>
      match minContrib st p with
      | none => sumMin st rest
      | some t =>
          match sumMin st rest with
          | none => some t.2.2
          | some s => some (s + t.2.2)

/-! ## The max-contribution sum (the dual of `sumMin`) -/

/-- The MAX-contribution of a pair: `ct·mx` for positive
    coefficients, `ct·mn` for negative ones (ct < 0: largest at
    min). The exact dual of Propagators.lean's `minContrib`. -/
def maxContrib (st : State) (p : Int × Nat) : Option (Nat × Int × Int) :=
  match domMinI (st.domains.getD p.2 []), domMaxI (st.domains.getD p.2 []) with
  | some mn, some mx =>
      if p.1 ≥ 0 then some (p.2, p.1, p.1 * mx) else some (p.2, p.1, p.1 * mn)
  | _, _ => none

/-- The folded max-contribution sum of a pair list (the dual of
    `sumMin`; same fold shape). -/
def sumMax (st : State) : List (Int × Nat) → Option Int
  | [] => none
  | p :: rest =>
      match maxContrib st p with
      | none => sumMax st rest
      | some t =>
          match sumMax st rest with
          | none => some t.2.2
          | some s => some (s + t.2.2)

/-! ## The fixed cause discipline -/

/-- The min-contribution cause of a term: the negation of the
    domain bound witnessing the term's minimal contribution.
    `ct > 0` contributes `ct·mn` at `x ≥ mn` (cause `x ≤ mn−1`);
    `ct < 0` contributes `ct·mx` at `x ≤ mx` (cause `x > mx`);
    `ct = 0` contributes 0 (no pin needed). -/
def linCauseMinPair (st : State) (p : Int × Nat) : Option Literal :=
  if p.1 > 0 then
    (domMinI (st.domains.getD p.2 [])).map fun mn => posLe p.2 (mn - 1)
  else if p.1 < 0 then
    (domMaxI (st.domains.getD p.2 [])).map fun mx => negLe p.2 mx
  else none

/-- The max-contribution cause of a term: the dual discipline.
    `ct > 0` contributes `ct·mx` at `x ≤ mx` (cause `x > mx`);
    `ct < 0` contributes `ct·mn` at `x ≥ mn` (cause `x ≤ mn−1`);
    `ct = 0` contributes 0 (no pin needed). -/
def linCauseMaxPair (st : State) (p : Int × Nat) : Option Literal :=
  if p.1 > 0 then
    (domMaxI (st.domains.getD p.2 [])).map fun mx => negLe p.2 mx
  else if p.1 < 0 then
    (domMinI (st.domains.getD p.2 [])).map fun mn => posLe p.2 (mn - 1)
  else none

/-- The min-contribution cause list of a rest list (the tail of
    every min-nogood emitted by the ±1 arms). -/
def linCausesMin (st : State) (rest : List (Int × Nat)) : Clause :=
  rest.filterMap (linCauseMinPair st)

/-- The max-contribution cause list of a rest list. -/
def linCausesMax (st : State) (rest : List (Int × Nat)) : Clause :=
  rest.filterMap (linCauseMaxPair st)

/-! ## The general-coefficient arms (route (2): the divided bound) -/

/-- The general-c arm for c > 0: `x_m ≤ ⌊(b − lr)/c⌋` with the
    min-causes (the upper bound of both the le and eq families). -/
def linGenArmHiMin (st : State) (m : Nat) (b c : Int)
    (rest : List (Int × Nat)) : Option Int → PropagationResult
  | some lr => narrowHi st m ((b - lr) / c)
      ([posLe m ((b - lr) / c)] ++ linCausesMin st rest)
  | none => .stable

/-- The general-c arm for c < 0: `x_m ≥ ⌈(lr − b)/(−c)⌉` (the
    negated floor) with the min-causes (the lower bound of both
    families). -/
def linGenArmLoMin (st : State) (m : Nat) (b c : Int)
    (rest : List (Int × Nat)) : Option Int → PropagationResult
  | some lr => narrowLo st m (-((b - lr) / (-c)))
      ([negLe m (-((b - lr) / (-c)) - 1)] ++ linCausesMin st rest)
  | none => .stable

/-- The general-c arm for c > 0, eq family: `x_m ≥ ⌈(b − hr)/c⌉`
    (the negated floor) with the max-causes. -/
def linGenArmLoMax (st : State) (m : Nat) (b c : Int)
    (rest : List (Int × Nat)) : Option Int → PropagationResult
  | some hr => narrowLo st m (-((hr - b) / c))
      ([negLe m (-((hr - b) / c) - 1)] ++ linCausesMax st rest)
  | none => .stable

/-- The general-c arm for c < 0, eq family: `x_m ≤ ⌊(hr − b)/(−c)⌋`
    with the max-causes. -/
def linGenArmHiMax (st : State) (m : Nat) (b c : Int)
    (rest : List (Int × Nat)) : Option Int → PropagationResult
  | some hr => narrowHi st m ((hr - b) / (-c))
      ([posLe m ((hr - b) / (-c))] ++ linCausesMax st rest)
  | none => .stable

/-! ## The linLe deduction kernel (propLinLe's `deduce`, fixed) -/

/-- The ±1-slot deduction for `Σ cₜxₜ ≤ b` over slot `m` with the
    rest pairs `rest`: propLinLe's `deduce` with the FIXED cause
    discipline and the completeness guard, EXTENDED with the
    general-coefficient arms (route (2), the STRONG floor/ceiling
    bound by a positive divisor).

    * `cₘ = 1`: `x_m ≤ b − loRest` where `loRest` is the rest's
      min-contribution sum — the nogood
      `[x_m ≤ b − loRest] ++ min-causes`;
    * `cₘ = −1`: `x_m ≥ loRest − b` — the nogood
      `[x_m > loRest − b − 1] ++ min-causes`;
    * `cₘ > 0` (general): `x_m ≤ ⌊(b − loRest)/cₘ⌋` — the nogood
      `[x_m ≤ (b − loRest)/cₘ] ++ min-causes`;
    * `cₘ < 0` (general): `x_m ≥ ⌈(loRest − b)/(−cₘ)⌉` (the
      negated floor) — the nogood
      `[x_m > −(b − loRest)/(−cₘ) − 1] ++ min-causes`.

    Each clause is integer-valid under `Σ cₜxₜ ≤ b` alone: a
    point falsifying every literal has every rest term at its
    pinned extreme (so `Σ_{t≠m} cₜxₜ ≥ loRest`) and the head
    beyond its bound, whence `Σ cₜxₜ > b`. -/
def linDeduceLe (st : State) (b : Int) (m : Nat) (c : Int)
    (rest : List (Int × Nat)) : PropagationResult :=
  -- the completeness guard: a rest pair without extrema would be
  -- dropped from the sums but pinned by no literal
  if rest.all (fun p => (minContrib st p).isSome) then
    if c = 1 then
      match sumMin st rest with
      | some lr =>
          narrowHi st m (b - lr) ([posLe m (b - lr)] ++ linCausesMin st rest)
      | none => .stable
    else if c = -1 then
      match sumMin st rest with
      | some lr =>
          narrowLo st m (lr - b) ([negLe m (lr - b - 1)] ++ linCausesMin st rest)
      | none => .stable
    else if c > 0 then
      -- the general positive arm: the FLOOR upper bound over the
      -- min-sum
      match sumMin st rest with
      | some lr => linGenArmHiMin st m b c rest lr
      | none => .stable
    else if c < 0 then
      -- the general negative arm: the negated-floor (ceiling) lower
      -- bound over the min-sum
      match sumMin st rest with
      | some lr => linGenArmLoMin st m b c rest lr
      | none => .stable
    else .stable
  else .stable

/-- The propagator sweep (propLinLe's `let rec sweep`, hoisted):
    over each zipped position, deduce over ALL other entries —
    dropping exactly the CURRENT pair by position (a duplicated
    slot's other coefficients belong to "the rest"). -/
def linSweep (coeffs : List Int) (is : List Nat)
    (f : Nat → Int → List (Int × Nat) → PropagationResult) :
    List ((Int × Nat) × Nat) → Nat → PropagationResult
  | [], _ => .stable
  | ((c, m), i) :: rest, idx =>
      let others := ((coeffs.zip is).zipIdx.filter (fun p => p.2 != i)).map (·.1)
      match f m c others with
      | .stable => linSweep coeffs is f rest (idx + 1)
      | r => r

/-- The corrected `int_lin_le` propagator: propLinLe's sweep over
    the zipped (coefficient, slot) pairs with the fixed deduce
    kernel. The `[]` arm mirrors the original's (a length mismatch
    would silently truncate the pairing; the compiled shape always
    has equal lengths — the packages carry `hlen`). -/
def propLinLe2 (st : State) (coeffs : List Int) (is : List Nat) (b : Int) :
    PropagationResult :=
  match coeffs.zip is with
  | [] => .stable
  | ps => linSweep coeffs is (linDeduceLe st b) (ps.zipIdx) 0

/-! ## The linEq deduction kernel (the new family) -/

/-- The `x_m ≤ b − loRest` arm of linEq (cₘ = 1, min-causes). -/
def linEqArmHiMin (st : State) (m : Nat) (b : Int) (rest : List (Int × Nat)) :
    Option Int → PropagationResult
  | some lr => narrowHi st m (b - lr) ([posLe m (b - lr)] ++ linCausesMin st rest)
  | none => .stable

/-- The `x_m ≥ b − hiRest` arm of linEq (cₘ = 1, max-causes). -/
def linEqArmLoMax (st : State) (m : Nat) (b : Int) (rest : List (Int × Nat)) :
    Option Int → PropagationResult
  | some hr => narrowLo st m (b - hr) ([negLe m (b - hr - 1)] ++ linCausesMax st rest)
  | none => .stable

/-- The `x_m ≥ loRest − b` arm of linEq (cₘ = −1, min-causes). -/
def linEqArmLoMin (st : State) (m : Nat) (b : Int) (rest : List (Int × Nat)) :
    Option Int → PropagationResult
  | some lr => narrowLo st m (lr - b) ([negLe m (lr - b - 1)] ++ linCausesMin st rest)
  | none => .stable

/-- The `x_m ≤ hiRest − b` arm of linEq (cₘ = −1, max-causes). -/
def linEqArmHiMax (st : State) (m : Nat) (b : Int) (rest : List (Int × Nat)) :
    Option Int → PropagationResult
  | some hr => narrowHi st m (hr - b) ([posLe m (hr - b)] ++ linCausesMax st rest)
  | none => .stable

/-- The ±1-slot deduction for `Σ cₜxₜ = b` over slot `m`: BOTH
    bounds per slot (firstEvent over the two arms; up to four
    narrow calls across the two slot polarities), other
    coefficients stable (sound, merely incomplete).

    Validity (both directions of the equality): from
    `cₘ·x_m = b − Σ_{t≠m}` and the rest pinned in
    `[loRest, hiRest]`:
    * cₘ = 1: `x_m ≤ b − loRest` and `x_m ≥ b − hiRest`;
    * cₘ = −1: `x_m ≥ loRest − b` and `x_m ≤ hiRest − b`. -/
def linDeduceEq (st : State) (b : Int) (m : Nat) (c : Int)
    (rest : List (Int × Nat)) : PropagationResult :=
  if rest.all (fun p => (minContrib st p).isSome) then
    if c = 1 then
      firstEvent
        [ linEqArmHiMin st m b rest (sumMin st rest)
        , linEqArmLoMax st m b rest (sumMax st rest) ]
    else if c = -1 then
      firstEvent
        [ linEqArmLoMin st m b rest (sumMin st rest)
        , linEqArmHiMax st m b rest (sumMax st rest) ]
    else if c > 0 then
      firstEvent
        [ linGenArmHiMin st m b c rest (sumMin st rest)
        , linGenArmLoMax st m b c rest (sumMax st rest) ]
    else if c < 0 then
      firstEvent
        [ linGenArmLoMin st m b c rest (sumMin st rest)
        , linGenArmHiMax st m b c rest (sumMax st rest) ]
    else .stable
  else .stable

/-- The new `int_lin_eq` propagator: the same sweep with the
    equality deduction kernel. -/
def propLinEq2 (st : State) (coeffs : List Int) (is : List Nat) (b : Int) :
    PropagationResult :=
  match coeffs.zip is with
  | [] => .stable
  | ps => linSweep coeffs is (linDeduceEq st b) (ps.zipIdx) 0

/-! ## The standalone registration -/

/-- The propagators of this module's two families: `linLe` (the
    corrected propagator) and `linEq` (the new family). -/
def propagatorOfProvedBLin : DomConstraint → Option Propagator
  | .linLe coeffs is b =>
      some { watches := [], run := fun st => propLinLe2 st coeffs is b }
  | .linEq coeffs is b =>
      some { watches := [], run := fun st => propLinEq2 st coeffs is b }
  | _ => none

/-! ## The obstruction regression (the witness now works) -/

/-- The witness problem of the linLe obstruction: `x + 2t ≤ 0`
    over two int slots with generous problem domains. -/
def linLe2_probI : Problem DomConstraint Unit where
  names := ["x", "t"]
  domains := [[Value.int (-2), Value.int 3, Value.int 5],
    [Value.int (-2), Value.int 10]]
  constraints := [DomConstraint.linLe [1, 2] [0, 1] 0]
  objective := ()
  clauses := []

/-- The witness state (the obstruction's `stI`): slot-`x`'s domain
    read `{0,5}` (min 0), slot-`t`'s domain read `{0,10}`. -/
def linLe2_stI : State where
  domains := [[Value.int 0, Value.int 5], [Value.int 0, Value.int 10]]
  trail := []
  decisionLevel := 0
  clauses := []
  learned := []
  queue := []
  conflict := none

/-- The OLD propagator at the witness state emits the UNIT clause
    `[x ≤ 0]` — the obstruction's falsified emission (the |2|≠1
    term `2t` contributed its min `0` to the bound but carried no
    pin). -/
theorem linLe2_old_emission : propLinLe linLe2_stI [1, 2] [0, 1] 0
    = .implied (posLe 0 0) { clause := [posLe 0 0] } := rfl

/-- **The fix, computationally**: the corrected propagator at the
    SAME state emits the same implied literal with the clause that
    now carries the second cause `t ≥ 0` (as `t ≤ −1` negated:
    `posLe 1 (−1)`) — the |2|≠1 term's pin. -/
theorem linLe2_obstruction_fixed : propLinLe2 linLe2_stI [1, 2] [0, 1] 0
    = .implied (posLe 0 0)
        { clause := [posLe 0 0, posLe 1 (-1)] } := rfl

/-! ### The general-coefficient regression

`2x + y ≤ 4` over `x ∈ {0,5}`, `y ∈ {1,3}`: the OLD propagator
skipped the |2|-coefficient slot of `x` entirely (no ±1 arm fires
for it); the new general arm derives `x ≤ ⌊(4 − minY)/2⌋ = ⌊3/2⌋
= 1` — the divided bound — with the min-cause `y ≥ 1` (as `y ≤ 0`
negated). -/

/-- The general-c witness state: slot-`x`'s domain `{0,5}`,
    slot-`y`'s domain `{1,3}` (min 1, max 3). -/
def linLe2_gen_stI : State where
  domains := [[Value.int 0, Value.int 5], [Value.int 1, Value.int 3]]
  trail := []
  decisionLevel := 0
  clauses := []
  learned := []
  queue := []
  conflict := none

/-- **The general-coefficient arm fires**: at the |2|-coefficient
    slot the corrected propagator now emits the implied literal
    `x ≤ 1` (the floor of `(4 − 1)/2`) with the divided-bound
    nogood `[x ≤ 1, y ≥ 1]` — where the pre-general propagator
    was `.stable` at this slot. -/
theorem linLe2_general_emission : propLinLe2 linLe2_gen_stI [2, 1] [0, 1] 4
    = .implied (posLe 0 1)
        { clause := [posLe 0 1, posLe 1 0] } := rfl

/-- The linEq general-c twin: `2x + y = 5` over the same state
    derives BOTH bounds of the |2| slot: the sweep's first event is
    `x ≤ ⌊(5 − 1)/2⌋ = 2`. -/
theorem linEq2_general_emission : propLinEq2 linLe2_gen_stI [2, 1] [0, 1] 5
    = .implied (posLe 0 2)
        { clause := [posLe 0 2, posLe 1 0] } := rfl

/-- The witness assignment `x = 3, t = −2` (a solution of the
    witness problem: `3 + 2·(−2) = −1 ≤ 0`). -/
def linLe2_aI : Assignment := [Value.int 3, Value.int (-2)]

/-- The witness is a ProblemSolution of the witness problem. -/
theorem linLe2_aI_solution :
    ProblemSolution linLe2_probI DomConstraint.SatisfiedBy linLe2_aI := by
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · intro slot value hv
    have hlt : slot < 2 := (List.getElem?_eq_some_iff.mp hv).1
    cases slot with
    | zero =>
        have hv2 : linLe2_aI[0]? = some value := hv
        rw [show linLe2_aI[0]? = some (Value.int 3) from rfl] at hv2
        injection hv2 with hv3
        rw [← hv3]
        have hdom : linLe2_probI.domains.getD 0 []
            = [Value.int (-2), Value.int 3, Value.int 5] := rfl
        rw [hdom]
        exact List.mem_cons_of_mem _ (List.mem_cons_self)
    | succ n =>
        have hn : n = 0 := by omega
        subst hn
        have hv2 : linLe2_aI[1]? = some value := hv
        rw [show linLe2_aI[1]? = some (Value.int (-2)) from rfl] at hv2
        injection hv2 with hv3
        rw [← hv3]
        have hdom : linLe2_probI.domains.getD 1 []
            = [Value.int (-2), Value.int 10] := rfl
        rw [hdom]
        exact List.mem_cons_self
  · intro dc hdc
    have hdc2 : dc = DomConstraint.linLe [1, 2] [0, 1] 0 :=
      List.mem_singleton.mp hdc
    subst hdc2
    -- 1·3 + 2·(−2) = −1 ≤ 0
    have hd : dotProduct (intVals [1, 2])
        (List.map (fun i => linLe2_aI[i]!) [0, 1]) = some (-1) := rfl
    show dotLe (intVals [1, 2])
        (List.map (fun i => linLe2_aI[i]!) [0, 1]) 0 = true
    unfold dotLe
    rw [hd]
    exact of_decide_eq_true rfl

/-- The witness falsifies the head `x ≤ 0` (`3 > 0`) — exactly as
    in the obstruction. -/
theorem linLe2_aI_head_false : (posLe 0 0).eval linLe2_aI = some false := rfl

/-- ...but the NEW second cause `t ≤ −1` is TRUE at the witness
    (`t = −2 ≤ −1`), so the emitted clause is satisfied where the
    obstruction's unit clause was falsified. -/
theorem linLe2_aI_cause_true : (posLe 1 (-1)).eval linLe2_aI = some true := rfl

/-! ## The minContrib/maxContrib inversions -/

/-- A some min-contribution forces both extrema and the recorded
    triple shape. -/
theorem minContrib_inv {st : State} {p : Int × Nat} {t : Nat × Int × Int}
    (ht : minContrib st p = some t) :
    ∃ mn mx, domMinI (st.domains.getD p.2 []) = some mn ∧
      domMaxI (st.domains.getD p.2 []) = some mx ∧
      t = (p.2, p.1, if p.1 ≥ 0 then p.1 * mn else p.1 * mx) := by
  unfold minContrib at ht
  split at ht
  · rename_i mn mx hmn hmx
    by_cases hp : p.1 ≥ 0
    · rw [if_pos hp] at ht
      injection ht with ht2
      subst ht2
      exact ⟨mn, mx, hmn, hmx, by rw [if_pos hp]⟩
    · rw [if_neg hp] at ht
      injection ht with ht2
      subst ht2
      exact ⟨mn, mx, hmn, hmx, by rw [if_neg hp]⟩
  · cases ht

/-- A some max-contribution forces both extrema and the recorded
    triple shape (the dual selection). -/
theorem maxContrib_inv {st : State} {p : Int × Nat} {t : Nat × Int × Int}
    (ht : maxContrib st p = some t) :
    ∃ mn mx, domMinI (st.domains.getD p.2 []) = some mn ∧
      domMaxI (st.domains.getD p.2 []) = some mx ∧
      t = (p.2, p.1, if p.1 ≥ 0 then p.1 * mx else p.1 * mn) := by
  unfold maxContrib at ht
  split at ht
  · rename_i mn mx hmn hmx
    by_cases hp : p.1 ≥ 0
    · rw [if_pos hp] at ht
      injection ht with ht2
      subst ht2
      exact ⟨mn, mx, hmn, hmx, by rw [if_pos hp]⟩
    · rw [if_neg hp] at ht
      injection ht with ht2
      subst ht2
      exact ⟨mn, mx, hmn, hmx, by rw [if_neg hp]⟩
  · cases ht

/-- The two contribution selectors exist together: a pair with a
    min-contribution also has a max-contribution. -/
theorem maxContrib_isSome_of_minContrib {st : State} {p : Int × Nat}
    (h : (minContrib st p).isSome = true) :
    (maxContrib st p).isSome = true := by
  cases hc : minContrib st p with
  | none => rw [hc] at h; simp at h
  | some t =>
      obtain ⟨mn, mx, hmn, hmx, _⟩ := minContrib_inv hc
      show (maxContrib st p).isSome = true
      rw [maxContrib, hmn, hmx]
      by_cases hp : p.1 ≥ 0
      · show (if p.1 ≥ 0 then
            some (p.2, p.1, p.1 * mx) else
            some (p.2, p.1, p.1 * mn)).isSome = true
        rw [if_pos hp]; rfl
      · show (if p.1 ≥ 0 then
            some (p.2, p.1, p.1 * mx) else
            some (p.2, p.1, p.1 * mn)).isSome = true
        rw [if_neg hp]; rfl

/-! ## Constraint semantics at integer views -/

/-- The linLe constraint's semantics at a solution: the dot
    product over the zipped pairs exists and is at most `b`
    (`linLe_dot` restated at the zip). -/
theorem linLe2_views {a : Assignment} {coeffs : List Int} {is : List Nat}
    {b : Int}
    (hcons : (DomConstraint.linLe coeffs is b).SatisfiedBy a)
    (hlen : coeffs.length = is.length) :
    ∃ d, dotOver (coeffs.zip is) a 0 = some d ∧ d ≤ b :=
  linLe_dot hcons hlen

/-- The linEq constraint's semantics at a solution: the dot
    product over the zipped pairs exists and equals `b`. -/
theorem linEq2_views {a : Assignment} {coeffs : List Int} {is : List Nat}
    {b : Int}
    (hcons : (DomConstraint.linEq coeffs is b).SatisfiedBy a)
    (hlen : coeffs.length = is.length) :
    ∃ d, dotOver (coeffs.zip is) a 0 = some d ∧ d = b := by
  rw [show DomConstraint.SatisfiedBy (DomConstraint.linEq coeffs is b) a =
    (dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) = some b) from rfl]
    at hcons
  rw [dotProduct_eq_dotOver hlen] at hcons
  exact ⟨_, hcons, rfl⟩

/-- linLe's reads-int bridge at the zip (the six-family module's
    `linLe_reads_int`). -/
theorem linLe2_reads_int {coeffs : List Int} {is : List Nat} {b : Int}
    {a : Assignment}
    (hcons : (DomConstraint.linLe coeffs is b).SatisfiedBy a)
    (hlen : coeffs.length = is.length) :
    ∀ p, p ∈ coeffs.zip is → ∃ i, slotInt a p.2 = some i :=
  linLe_reads_int hcons hlen

/-- linEq's reads-int bridge at the zip: an existing dot product
    forces every zipped slot's read to be an integer. -/
theorem linEq2_reads_int {coeffs : List Int} {is : List Nat} {b : Int}
    {a : Assignment}
    (hcons : (DomConstraint.linEq coeffs is b).SatisfiedBy a)
    (hlen : coeffs.length = is.length) :
    ∀ p, p ∈ coeffs.zip is → ∃ i, slotInt a p.2 = some i := by
  rw [show DomConstraint.SatisfiedBy (DomConstraint.linEq coeffs is b) a =
    (dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) = some b) from rfl]
    at hcons
  intro p hp
  have hmem : p.2 ∈ is := mem_zip_snd hp
  obtain ⟨x, hx⟩ := dotProduct_reads_int hcons p.2 hmem
  refine ⟨x, ?_⟩
  show a[p.2]?.bind Value.intView = some x
  have hrng : p.2 < a.length := by
    cases hlt : Nat.lt_or_ge p.2 a.length with
    | inl h => exact h
    | inr hge =>
        exfalso
        have hdef : a[p.2]! = (default : Value) := by
          rw [List.getElem!_eq_getElem?_getD]
          rw [List.getElem?_eq_none_iff.mpr hge]
          rfl
        rw [hdef] at hx
        cases hx
  have hread : a[p.2]? = some (.int x) := by
    rw [List.getElem?_eq_getElem hrng]
    have h1 : a[p.2]! = a[p.2] := by
      rw [List.getElem!_eq_getElem?_getD (l := a) (i := p.2)]
      · rw [List.getElem?_eq_getElem hrng]
        rfl
    rw [← h1]
    exact congrArg some hx
  rw [hread]
  show (some (Value.int x)).bind Value.intView = some x
  rfl

/-- linEq's dot at the zip (the `linLe_dot` dual). -/
theorem linEq2_dot {coeffs : List Int} {is : List Nat} {b : Int}
    {a : Assignment}
    (hcons : (DomConstraint.linEq coeffs is b).SatisfiedBy a)
    (hlen : coeffs.length = is.length) :
    ∃ d, dotOver (coeffs.zip is) a 0 = some d ∧ d = b := by
  rw [show DomConstraint.SatisfiedBy (DomConstraint.linEq coeffs is b) a =
    (dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) = some b) from rfl]
    at hcons
  rw [dotProduct_eq_dotOver hlen] at hcons
  exact ⟨_, hcons, rfl⟩

/-! ## The emission shape lemma -/

/-- The `others` list of a sweep position: dropping the current
    pair by position leaves exactly the other zipped pairs. -/
theorem linOthers_eq {coeffs : List Int} {is : List Nat} {i : Nat}
    (hi : i < (coeffs.zip is).length) :
    (((coeffs.zip is).zipIdx.filter (fun p => p.2 != i)).map (·.1)) =
      (coeffs.zip is).take i ++ (coeffs.zip is).drop (i+1) :=
  zipIdx_filter_remove _ i hi

/-! ## lin2 list infrastructure -/

/-- A zipIdx entry's first component is a member of the underlying
    list. -/
theorem lin2_mem_zip_of_zipIdx {α : Type} : ∀ (l : List α) (k : Nat)
    (p : α × Nat), p ∈ l.zipIdx k → p.1 ∈ l := by
  intro l
  induction l with
  | nil => intro k p h; cases h
  | cons x xs ih =>
      intro k p h
      rcases List.mem_cons.mp h with hc | hc
      · rw [hc]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih (k+1) p hc)

/-- Every pair of a sweep position's `others` list is a zipped
    pair. -/
theorem lin2_others_mem_zip {coeffs : List Int} {is : List Nat} {i : Nat}
    {p : Int × Nat}
    (hp : p ∈ (((coeffs.zip is).zipIdx.filter
        (fun q => q.2 != i)).map (·.1))) :
    p ∈ coeffs.zip is := by
  rw [List.mem_map] at hp
  obtain ⟨q, hqfilter, hqp⟩ := hp
  have hqzip : q ∈ (coeffs.zip is).zipIdx :=
    (List.mem_filter.mp hqfilter).1
  have hqmem : q.1 ∈ coeffs.zip is :=
    lin2_mem_zip_of_zipIdx _ 0 q hqzip
  rw [← hqp]
  exact hqmem

/-- The reads-int transfer to a sweep position's others list. -/
theorem lin2_reads_of_others {coeffs : List Int} {is : List Nat} {i : Nat}
    {a : Assignment}
    (hreads : ∀ p, p ∈ coeffs.zip is → ∃ x, slotInt a p.2 = some x) :
    ∀ p, p ∈ (((coeffs.zip is).zipIdx.filter
        (fun q => q.2 != i)).map (·.1)) → ∃ x, slotInt a p.2 = some x :=
  fun p hp => hreads p (lin2_others_mem_zip hp)

/-! ## The state-free contribution sums under falsified causes -/

/-- Under the completeness guard, a `none` sum forces the empty
    list (a cons would contribute and make the sum some). -/
theorem lin2_sumMin_none_eq_nil {st : State} {rest : List (Int × Nat)}
    (hguard : ∀ p ∈ rest, (minContrib st p).isSome = true)
    (h : sumMin st rest = none) : rest = [] := by
  cases rest with
  | nil => rfl
  | cons p ls =>
      exfalso
      obtain ⟨t, ht⟩ : ∃ t, minContrib st p = some t := by
        cases hc : minContrib st p with
        | none =>
            exfalso
            have hg : (minContrib st p).isSome = false := by
              rw [hc]; rfl
            have := hguard p List.mem_cons_self
            rw [hg] at this
            exact absurd this (by simp)
        | some t => exact ⟨t, rfl⟩
      rw [sumMin, ht] at h
      cases hs : sumMin st ls with
      | none => rw [hs] at h; cases h
      | some s => rw [hs] at h; cases h

/-- The dual for the max sum. -/
theorem lin2_sumMax_none_eq_nil {st : State} {rest : List (Int × Nat)}
    (hguard : ∀ p ∈ rest, (maxContrib st p).isSome = true)
    (h : sumMax st rest = none) : rest = [] := by
  cases rest with
  | nil => rfl
  | cons p ls =>
      exfalso
      obtain ⟨t, ht⟩ : ∃ t, maxContrib st p = some t := by
        cases hc : maxContrib st p with
        | none =>
            exfalso
            have hg : (maxContrib st p).isSome = false := by
              rw [hc]; rfl
            have := hguard p List.mem_cons_self
            rw [hg] at this
            exact absurd this (by simp)
        | some t => exact ⟨t, rfl⟩
      rw [sumMax, ht] at h
      cases hs : sumMax st ls with
      | none => rw [hs] at h; cases h
      | some s => rw [hs] at h; cases h

/-- **The state-free min-sum bound** (the heart of the fix): when
    every min-cause literal is false at `a`, every rest term sits
    at or above its recorded min-contribution, so the total is at
    least `loRest`. The fit-based premise of the six-family
    `sumMin_le_dotOver` is replaced by cause falsity — no state
    coherence needed. -/
theorem lin2_sumMin_le {a : Assignment} {st : State} {rest : List (Int × Nat)}
    (hreads : ∀ p, p ∈ rest → ∃ i, slotInt a p.2 = some i)
    (hguard : ∀ p ∈ rest, (minContrib st p).isSome = true)
    (hcauses : ∀ q ∈ linCausesMin st rest, q.eval a = some false) :
    ∀ (l : List (Int × Nat)), (∀ p, p ∈ l → p ∈ rest) →
    ∀ loRest, sumMin st l = some loRest →
    ∀ acc d, dotOver l a acc = some d → loRest + acc ≤ d := by
  intro l hsub
  induction l with
  | nil => intro loRest hlo; cases hlo
  | cons p ls ih =>
      intro loRest hsum acc d hd
      -- p's read and integer view
      obtain ⟨xt, hxt⟩ := hreads p (hsub p List.mem_cons_self)
      obtain ⟨v, hv, hvi⟩ := read_of_slotInt hxt
      have hrng : p.2 < a.length := by
        cases hr : Nat.lt_or_ge p.2 a.length with
        | inl h => exact h
        | inr hge =>
            exfalso
            have hnone : a[p.2]? = none :=
              List.getElem?_eq_none_iff.mpr (by omega)
            rw [hnone] at hv
            cases hv
      have hread : a[p.2]! = v := getElem_bang_of_read hv hrng
      -- p's min-contribution record (the guard gives some)
      obtain ⟨t, ht⟩ : ∃ t, minContrib st p = some t := by
        cases hc : minContrib st p with
        | none =>
            exfalso
            have hg : (minContrib st p).isSome = false := by
              rw [hc]; rfl
            have := hguard p (hsub p List.mem_cons_self)
            rw [hg] at this
            exact absurd this (by simp)
        | some t => exact ⟨t, rfl⟩
      obtain ⟨mn, mx, hmn, hmx, htshape⟩ := minContrib_inv ht
      -- the recorded contribution is a lower bound on p.1 * xt
      have hcontrib : t.2.2 ≤ p.1 * xt := by
        by_cases hpos : p.1 > 0
        · -- cause posLe p.2 (mn − 1), false → mn ≤ xt
          have hcause : linCauseMinPair st p = some (posLe p.2 (mn - 1)) := by
            show (if p.1 > 0 then
                (domMinI (st.domains.getD p.2 [])).map
                  fun m => posLe p.2 (m - 1)
              else if p.1 < 0 then
                (domMaxI (st.domains.getD p.2 [])).map fun m => negLe p.2 m
              else none) = _
            rw [if_pos hpos, hmn, Option.map_some]
          have hmem : posLe p.2 (mn - 1) ∈ linCausesMin st rest := by
            rw [linCausesMin, List.mem_filterMap]
            exact ⟨p, hsub p List.mem_cons_self, hcause⟩
          obtain ⟨xt2, hsx2, hlt⟩ := eval_posLe_false a p.2 (mn - 1)
            (hcauses _ hmem)
          rw [hxt] at hsx2
          have hxt2 : xt2 = xt := Option.some.inj hsx2.symm
          rw [hxt2] at hlt
          rw [htshape, if_pos (by omega : p.1 ≥ 0)]
          exact Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
        · by_cases hneg : p.1 < 0
          · -- cause negLe p.2 mx, false → xt ≤ mx
            have hcause : linCauseMinPair st p = some (negLe p.2 mx) := by
              show (if p.1 > 0 then
                  (domMinI (st.domains.getD p.2 [])).map
                    fun m => posLe p.2 (m - 1)
                else if p.1 < 0 then
                  (domMaxI (st.domains.getD p.2 [])).map fun m => negLe p.2 m
                else none) = _
              rw [if_neg (by omega : ¬ p.1 > 0), if_pos hneg, hmx,
                Option.map_some]
            have hmem : negLe p.2 mx ∈ linCausesMin st rest := by
              rw [linCausesMin, List.mem_filterMap]
              exact ⟨p, hsub p List.mem_cons_self, hcause⟩
            obtain ⟨xt2, hsx2, hle⟩ := eval_negLe_false a p.2 mx
              (hcauses _ hmem)
            rw [hxt] at hsx2
            have hxt2 : xt2 = xt := Option.some.inj hsx2.symm
            rw [hxt2] at hle
            rw [htshape, if_neg (by omega : ¬ p.1 ≥ 0)]
            exact Int.mul_comm p.1 xt ▸ Int.mul_comm p.1 mx ▸
              Int.mul_le_mul_of_nonpos_right hle (by omega)
          · -- p.1 = 0: the recorded contribution is 0
            have hp0 : p.1 = 0 := by omega
            rw [htshape, if_pos (by omega : p.1 ≥ 0)]
            rw [hp0]
            simp
      -- the dot's cons step at the int read
      have hdotcase : (match a[p.2]! with
        | .int x => dotOver ls a (acc + p.1 * x)
        | _ => (none : Option Int)) = some d := hd
      cases v with
      | int x =>
          have hxeq : x = xt := by
            rw [Value.intView] at hvi
            exact Option.some.inj hvi
          rw [hread, hxeq] at hdotcase
          -- the sum's cons step
          rw [sumMin, ht] at hsum
          cases hs : sumMin st ls with
          | none =>
              have hlsnil : ls = [] :=
                lin2_sumMin_none_eq_nil
                  (fun q hq => hguard q (hsub q (List.mem_cons_of_mem _ hq))) hs
              subst hlsnil
              have hlo : loRest = t.2.2 := by
                have h2 := hsum
                rw [hs] at h2
                exact (Option.some.inj h2).symm
              have hd2 : d = acc + p.1 * xt := by
                have h3 : (match (Value.int xt : Value) with
                  | .int x => dotOver ([] : List (Int × Nat)) a (acc + p.1 * x)
                  | _ => (none : Option Int)) =
                  some (acc + p.1 * xt) := rfl
                rw [h3] at hdotcase
                exact (Option.some.inj hdotcase).symm
              rw [hlo, hd2]
              omega
          | some s =>
              have hlo : loRest = s + t.2.2 := by
                have h2 := hsum
                rw [hs] at h2
                exact (Option.some.inj h2).symm
              have hih := ih
                (fun q hq => hsub q (List.mem_cons_of_mem _ hq))
                s hs (acc + p.1 * xt) d hdotcase
              rw [hlo]
              omega
      | bool b =>
          rw [hread] at hdotcase
          cases hdotcase
      | setOfInt s =>
          rw [hread] at hdotcase
          cases hdotcase
      | array xs =>
          rw [hread] at hdotcase
          cases hdotcase

/-- **The state-free max-sum bound** (the dual): when every
    max-cause literal is false at `a`, every rest term sits at or
    below its recorded max-contribution, so the total is at most
    `hiRest`. -/
theorem lin2_sumMax_ge {a : Assignment} {st : State} {rest : List (Int × Nat)}
    (hreads : ∀ p, p ∈ rest → ∃ i, slotInt a p.2 = some i)
    (hguard : ∀ p ∈ rest, (maxContrib st p).isSome = true)
    (hcauses : ∀ q ∈ linCausesMax st rest, q.eval a = some false) :
    ∀ (l : List (Int × Nat)), (∀ p, p ∈ l → p ∈ rest) →
    ∀ hiRest, sumMax st l = some hiRest →
    ∀ acc d, dotOver l a acc = some d → d ≤ hiRest + acc := by
  intro l hsub
  induction l with
  | nil => intro hiRest hhi; cases hhi
  | cons p ls ih =>
      intro hiRest hsum acc d hd
      -- p's read and integer view
      obtain ⟨xt, hxt⟩ := hreads p (hsub p List.mem_cons_self)
      obtain ⟨v, hv, hvi⟩ := read_of_slotInt hxt
      have hrng : p.2 < a.length := by
        cases hr : Nat.lt_or_ge p.2 a.length with
        | inl h => exact h
        | inr hge =>
            exfalso
            have hnone : a[p.2]? = none :=
              List.getElem?_eq_none_iff.mpr (by omega)
            rw [hnone] at hv
            cases hv
      have hread : a[p.2]! = v := getElem_bang_of_read hv hrng
      -- p's max-contribution record (the guard gives some)
      obtain ⟨t, ht⟩ : ∃ t, maxContrib st p = some t := by
        cases hc : maxContrib st p with
        | none =>
            exfalso
            have hg : (maxContrib st p).isSome = false := by
              rw [hc]; rfl
            have := hguard p (hsub p List.mem_cons_self)
            rw [hg] at this
            exact absurd this (by simp)
        | some t => exact ⟨t, rfl⟩
      obtain ⟨mn, mx, hmn, hmx, htshape⟩ := maxContrib_inv ht
      -- the recorded contribution is an upper bound on p.1 * xt
      have hcontrib : p.1 * xt ≤ t.2.2 := by
        by_cases hpos : p.1 > 0
        · -- cause negLe p.2 mx, false → xt ≤ mx
          have hcause : linCauseMaxPair st p = some (negLe p.2 mx) := by
            show (if p.1 > 0 then
                (domMaxI (st.domains.getD p.2 [])).map fun m => negLe p.2 m
              else if p.1 < 0 then
                (domMinI (st.domains.getD p.2 [])).map
                  fun m => posLe p.2 (m - 1)
              else none) = _
            rw [if_pos hpos, hmx, Option.map_some]
          have hmem : negLe p.2 mx ∈ linCausesMax st rest := by
            rw [linCausesMax, List.mem_filterMap]
            exact ⟨p, hsub p List.mem_cons_self, hcause⟩
          obtain ⟨xt2, hsx2, hle⟩ := eval_negLe_false a p.2 mx
            (hcauses _ hmem)
          rw [hxt] at hsx2
          have hxt2 : xt2 = xt := Option.some.inj hsx2.symm
          rw [hxt2] at hle
          rw [htshape, if_pos (by omega : p.1 ≥ 0)]
          exact Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
        · by_cases hneg : p.1 < 0
          · -- cause posLe p.2 (mn − 1), false → mn ≤ xt
            have hcause : linCauseMaxPair st p = some (posLe p.2 (mn - 1)) := by
              show (if p.1 > 0 then
                  (domMaxI (st.domains.getD p.2 [])).map fun m => negLe p.2 m
                else if p.1 < 0 then
                  (domMinI (st.domains.getD p.2 [])).map
                    fun m => posLe p.2 (m - 1)
                else none) = _
              rw [if_neg (by omega : ¬ p.1 > 0), if_pos hneg, hmn,
                Option.map_some]
            have hmem : posLe p.2 (mn - 1) ∈ linCausesMax st rest := by
              rw [linCausesMax, List.mem_filterMap]
              exact ⟨p, hsub p List.mem_cons_self, hcause⟩
            obtain ⟨xt2, hsx2, hlt⟩ := eval_posLe_false a p.2 (mn - 1)
              (hcauses _ hmem)
            rw [hxt] at hsx2
            have hxt2 : xt2 = xt := Option.some.inj hsx2.symm
            rw [hxt2] at hlt
            have hmnle : mn ≤ xt := by omega
            rw [htshape, if_neg (by omega : ¬ p.1 ≥ 0)]
            exact Int.mul_comm p.1 xt ▸ Int.mul_comm p.1 mn ▸
              Int.mul_le_mul_of_nonpos_right hmnle (by omega)
          · -- p.1 = 0: the recorded contribution is 0
            have hp0 : p.1 = 0 := by omega
            rw [htshape, if_pos (by omega : p.1 ≥ 0)]
            rw [hp0]
            simp
      -- the dot's cons step at the int read
      have hdotcase : (match a[p.2]! with
        | .int x => dotOver ls a (acc + p.1 * x)
        | _ => (none : Option Int)) = some d := hd
      cases v with
      | int x =>
          have hxeq : x = xt := by
            rw [Value.intView] at hvi
            exact Option.some.inj hvi
          rw [hread, hxeq] at hdotcase
          -- the sum's cons step
          rw [sumMax, ht] at hsum
          cases hs : sumMax st ls with
          | none =>
              have hlsnil : ls = [] :=
                lin2_sumMax_none_eq_nil
                  (fun q hq => hguard q (hsub q (List.mem_cons_of_mem _ hq))) hs
              subst hlsnil
              have hhi : hiRest = t.2.2 := by
                have h2 := hsum
                rw [hs] at h2
                exact (Option.some.inj h2).symm
              have hd2 : d = acc + p.1 * xt := by
                have h3 : (match (Value.int xt : Value) with
                  | .int x => dotOver ([] : List (Int × Nat)) a (acc + p.1 * x)
                  | _ => (none : Option Int)) =
                  some (acc + p.1 * xt) := rfl
                rw [h3] at hdotcase
                exact (Option.some.inj hdotcase).symm
              rw [hhi, hd2]
              omega
          | some s =>
              have hhi : hiRest = s + t.2.2 := by
                have h2 := hsum
                rw [hs] at h2
                exact (Option.some.inj h2).symm
              have hih := ih
                (fun q hq => hsub q (List.mem_cons_of_mem _ hq))
                s hs (acc + p.1 * xt) d hdotcase
              rw [hhi]
              omega
      | bool b =>
          rw [hread] at hdotcase
          cases hdotcase
      | setOfInt s =>
          rw [hread] at hdotcase
          cases hdotcase
      | array xs =>
          rw [hread] at hdotcase
          cases hdotcase

/-! ## The state-free entry split -/

/-- The dot-product split at a zipped entry (state-free): the
    constraint's dot over the full zip is the rest's dot plus the
    entry's contribution `c·xt`, where `xt` is slot `m`'s integer
    view at `a` and the rest is exactly the sweep position's
    others list. -/
theorem lin2_entry_dot {a : Assignment} {coeffs : List Int} {is : List Nat}
    {m : Nat} {c : Int} {i : Nat} {d : Int}
    (hmem : ((c, m), i) ∈ (coeffs.zip is).zipIdx)
    (hreads : ∀ p, p ∈ coeffs.zip is → ∃ x, slotInt a p.2 = some x)
    (hdot : dotOver (coeffs.zip is) a 0 = some d) :
    ∃ xt, slotInt a m = some xt ∧
      dotOver ((((coeffs.zip is).zipIdx.filter
          (fun q => q.2 != i)).map (·.1))) a 0 = some (d - c * xt) := by
  have hlen2 : i - 0 < (coeffs.zip is).length :=
    zipIdx_mem_length _ 0 i (c, m) hmem
  have hi : i < (coeffs.zip is).length := by omega
  have hentry : (coeffs.zip is).getD i (c, m) = (c, m) :=
    zipIdx_getD (coeffs.zip is) i (c, m) hmem
  obtain ⟨c2, m2, xt2, rest2, hcm2, hxt2, hrest2, hdotrest⟩ :=
    dotOver_split_mid (coeffs := coeffs) (is := is) hi hreads hdot
  -- reconcile the entry components (getD at an in-range index
  -- ignores the default)
  have hget : ∀ df : Int × Nat, (coeffs.zip is).getD i df =
      (coeffs.zip is).getD i (0, 0) := by
    intro df
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi]
    rfl
  obtain ⟨hc, hm⟩ : c2 = c ∧ m2 = m := by
    have h1 : (coeffs.zip is).getD i (0, 0) = (c, m) := by
      rw [show (coeffs.zip is).getD i (0, 0) =
        (coeffs.zip is).getD i (c, m) from (hget (c, m)).symm]
      rw [hentry]
    have h2 : (c2, m2) = (c, m) := hcm2.symm.trans h1
    exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩
  subst hc
  subst hm
  refine ⟨xt2, hxt2, ?_⟩
  rw [hrest2] at hdotrest
  rw [zipIdx_filter_remove _ i hi]
  exact hdotrest

/-! ## Cause hygiene: shape, decidedness, normalization -/

/-- A min-cause is a `posLe` below a positive coefficient and a
    `negLe` below a negative one. -/
theorem lin2_causeMin_inv {st : State} {p : Int × Nat} {q : Literal}
    (h : linCauseMinPair st p = some q) :
    (∃ mn, domMinI (st.domains.getD p.2 []) = some mn ∧
        q = posLe p.2 (mn - 1) ∧ p.1 > 0) ∨
    (∃ mx, domMaxI (st.domains.getD p.2 []) = some mx ∧
        q = negLe p.2 mx ∧ p.1 < 0) := by
  unfold linCauseMinPair at h
  by_cases hpos : p.1 > 0
  · rw [if_pos hpos] at h
    cases hmn : domMinI (st.domains.getD p.2 []) with
    | none =>
        rw [hmn] at h
        exact absurd h (by intro hc; cases hc)
    | some mn =>
        rw [hmn, Option.map_some] at h
        injection h with hq2
        exact Or.inl ⟨mn, rfl, hq2.symm, hpos⟩
  · by_cases hneg : p.1 < 0
    · rw [if_neg (by omega : ¬ p.1 > 0), if_pos hneg] at h
      cases hmx : domMaxI (st.domains.getD p.2 []) with
      | none =>
          rw [hmx] at h
          exact absurd h (by intro hc; cases hc)
      | some mx =>
          rw [hmx, Option.map_some] at h
          injection h with hq2
          exact Or.inr ⟨mx, rfl, hq2.symm, hneg⟩
    · rw [if_neg (by omega : ¬ p.1 > 0), if_neg hneg] at h
      cases h

/-- A max-cause is a `negLe` below a positive coefficient and a
    `posLe` below a negative one. -/
theorem lin2_causeMax_inv {st : State} {p : Int × Nat} {q : Literal}
    (h : linCauseMaxPair st p = some q) :
    (∃ mx, domMaxI (st.domains.getD p.2 []) = some mx ∧
        q = negLe p.2 mx ∧ p.1 > 0) ∨
    (∃ mn, domMinI (st.domains.getD p.2 []) = some mn ∧
        q = posLe p.2 (mn - 1) ∧ p.1 < 0) := by
  unfold linCauseMaxPair at h
  by_cases hpos : p.1 > 0
  · rw [if_pos hpos] at h
    cases hmx : domMaxI (st.domains.getD p.2 []) with
    | none =>
        rw [hmx] at h
        exact absurd h (by intro hc; cases hc)
    | some mx =>
        rw [hmx, Option.map_some] at h
        injection h with hq2
        exact Or.inl ⟨mx, rfl, hq2.symm, hpos⟩
  · by_cases hneg : p.1 < 0
    · rw [if_neg (by omega : ¬ p.1 > 0), if_pos hneg] at h
      cases hmn : domMinI (st.domains.getD p.2 []) with
      | none =>
          rw [hmn] at h
          exact absurd h (by intro hc; cases hc)
      | some mn =>
          rw [hmn, Option.map_some] at h
          injection h with hq2
          exact Or.inr ⟨mn, rfl, hq2.symm, hneg⟩
    · rw [if_neg (by omega : ¬ p.1 > 0), if_neg hneg] at h
      cases h

/-- Every min-cause literal is decided at an assignment reading
    all the rest slots. -/
theorem lin2_causesMin_eval_some {a : Assignment} {st : State}
    {rest : List (Int × Nat)}
    (hreads : ∀ p, p ∈ rest → ∃ i, slotInt a p.2 = some i)
    {q : Literal} (hq : q ∈ linCausesMin st rest) :
    ∃ bv, q.eval a = some bv := by
  rw [linCausesMin, List.mem_filterMap] at hq
  obtain ⟨p, hpmem, hpq⟩ := hq
  obtain ⟨i, hi⟩ := hreads p hpmem
  rcases lin2_causeMin_inv hpq with ⟨mn, _, hq2, _⟩ | ⟨mx, _, hq2, _⟩
  · subst hq2
    rw [eval_posLe, hi]
    exact ⟨_, rfl⟩
  · subst hq2
    rw [eval_negLe, hi]
    exact ⟨_, rfl⟩

/-- Every max-cause literal is decided at an assignment reading
    all the rest slots. -/
theorem lin2_causesMax_eval_some {a : Assignment} {st : State}
    {rest : List (Int × Nat)}
    (hreads : ∀ p, p ∈ rest → ∃ i, slotInt a p.2 = some i)
    {q : Literal} (hq : q ∈ linCausesMax st rest) :
    ∃ bv, q.eval a = some bv := by
  rw [linCausesMax, List.mem_filterMap] at hq
  obtain ⟨p, hpmem, hpq⟩ := hq
  obtain ⟨i, hi⟩ := hreads p hpmem
  rcases lin2_causeMax_inv hpq with ⟨mx, _, hq2, _⟩ | ⟨mn, _, hq2, _⟩
  · subst hq2
    rw [eval_negLe, hi]
    exact ⟨_, rfl⟩
  · subst hq2
    rw [eval_posLe, hi]
    exact ⟨_, rfl⟩

/-- Min-cause lists are normalized (order literals only). -/
theorem lin2_causesMin_norm {st : State} {rest : List (Int × Nat)} :
    ∀ q ∈ linCausesMin st rest, q = q.norm := by
  intro q hq
  rw [linCausesMin, List.mem_filterMap] at hq
  obtain ⟨p, _, hpq⟩ := hq
  rcases lin2_causeMin_inv hpq with ⟨_, _, hq2, _⟩ | ⟨_, _, hq2, _⟩
  · subst hq2; rfl
  · subst hq2; rfl

/-- Max-cause lists are normalized. -/
theorem lin2_causesMax_norm {st : State} {rest : List (Int × Nat)} :
    ∀ q ∈ linCausesMax st rest, q = q.norm := by
  intro q hq
  rw [linCausesMax, List.mem_filterMap] at hq
  obtain ⟨p, _, hpq⟩ := hq
  rcases lin2_causeMax_inv hpq with ⟨_, _, hq2, _⟩ | ⟨_, _, hq2, _⟩
  · subst hq2; rfl
  · subst hq2; rfl

/-! ## The master absurd lemmas

Each emitted clause, checked by hand: a solution falsifying
every literal violates the constraint. The two le-directions
and the two eq-max-directions; the eq-min-directions reuse the
le lemmas (`d = b` implies `d ≤ b`). -/

/-- The +1-slot nogood `[x_m ≤ b − loRest] ++ minCauses` of
    `Σ cₜxₜ ≤ b` (and of `Σ cₜxₜ = b`): falsifying the head puts
    `x_m` above `b − loRest`, falsifying every cause pins every
    rest term at or above its min-contribution, so
    `Σ = x_m + Σ_rest > b`. -/
theorem lin2_absurd_le_hi {a : Assignment} {st : State} {m : Nat}
    {coeffs : List Int} {is : List Nat} {b lr d : Int} {i : Nat}
    {rest : List (Int × Nat)}
    (hmem : ((1, m), i) ∈ (coeffs.zip is).zipIdx)
    (hrest : rest = (((coeffs.zip is).zipIdx.filter
        (fun q => q.2 != i)).map (·.1)))
    (hguard : ∀ p ∈ rest, (minContrib st p).isSome = true)
    (hcauses : ∀ q ∈ linCausesMin st rest, q.eval a = some false)
    (hsum : sumMin st rest = some lr)
    (hreads : ∀ p, p ∈ coeffs.zip is → ∃ x, slotInt a p.2 = some x)
    (hdot : dotOver (coeffs.zip is) a 0 = some d)
    (hdle : d ≤ b)
    (hhead : (posLe m (b - lr)).eval a = some false) : False := by
  rw [hrest] at hsum hcauses hguard
  obtain ⟨xt, hxtm, hdotrest⟩ :=
    lin2_entry_dot hmem hreads hdot
  -- the min-sum bound at the rest
  have hbound : lr + 0 ≤ (d - 1 * xt) :=
    lin2_sumMin_le (lin2_reads_of_others hreads)
      hguard hcauses _ (fun p hp => hp) lr hsum 0 (d - 1 * xt) hdotrest
  -- the falsified head: b − lr < xt
  obtain ⟨xt2, hsx2, hlt⟩ := eval_posLe_false a m (b - lr) hhead
  rw [hxtm] at hsx2
  have hxt2 : xt2 = xt := Option.some.inj hsx2.symm
  rw [hxt2] at hlt
  omega

/-- The −1-slot nogood `[x_m > loRest − b − 1] ++ minCauses` of
    `Σ cₜxₜ ≤ b` (and of `Σ cₜxₜ = b`): falsifying the head puts
    `x_m ≤ loRest − b − 1`, so `−x_m ≥ b − loRest + 1`; with the
    rest pinned at or above `loRest`,
    `Σ = −x_m + Σ_rest > b`. -/
theorem lin2_absurd_le_lo {a : Assignment} {st : State} {m : Nat}
    {coeffs : List Int} {is : List Nat} {b lr d : Int} {i : Nat}
    {rest : List (Int × Nat)}
    (hmem : ((-1, m), i) ∈ (coeffs.zip is).zipIdx)
    (hrest : rest = (((coeffs.zip is).zipIdx.filter
        (fun q => q.2 != i)).map (·.1)))
    (hguard : ∀ p ∈ rest, (minContrib st p).isSome = true)
    (hcauses : ∀ q ∈ linCausesMin st rest, q.eval a = some false)
    (hsum : sumMin st rest = some lr)
    (hreads : ∀ p, p ∈ coeffs.zip is → ∃ x, slotInt a p.2 = some x)
    (hdot : dotOver (coeffs.zip is) a 0 = some d)
    (hdle : d ≤ b)
    (hhead : (negLe m (lr - b - 1)).eval a = some false) : False := by
  rw [hrest] at hsum hcauses hguard
  obtain ⟨xt, hxtm, hdotrest⟩ :=
    lin2_entry_dot hmem hreads hdot
  -- the min-sum bound at the rest
  have hbound : lr + 0 ≤ (d - (-1) * xt) :=
    lin2_sumMin_le (lin2_reads_of_others hreads)
      hguard hcauses _ (fun p hp => hp) lr hsum 0 (d - (-1) * xt) hdotrest
  -- the falsified head: xt ≤ lr − b − 1
  obtain ⟨xt2, hsx2, hle⟩ := eval_negLe_false a m (lr - b - 1) hhead
  rw [hxtm] at hsx2
  have hxt2 : xt2 = xt := Option.some.inj hsx2.symm
  rw [hxt2] at hle
  omega

/-- The +1-slot max nogood `[x_m > b − hiRest − 1] ++ maxCauses`
    of `Σ cₜxₜ = b`: falsifying the head puts
    `x_m ≤ b − hiRest − 1`; with the rest pinned at or below
    `hiRest`, `Σ = x_m + Σ_rest ≤ b − 1 < b`. -/
theorem lin2_absurd_eq_lo_max {a : Assignment} {st : State} {m : Nat}
    {coeffs : List Int} {is : List Nat} {b hr d : Int} {i : Nat}
    {rest : List (Int × Nat)}
    (hmem : ((1, m), i) ∈ (coeffs.zip is).zipIdx)
    (hrest : rest = (((coeffs.zip is).zipIdx.filter
        (fun q => q.2 != i)).map (·.1)))
    (hguard : ∀ p ∈ rest, (maxContrib st p).isSome = true)
    (hcauses : ∀ q ∈ linCausesMax st rest, q.eval a = some false)
    (hsum : sumMax st rest = some hr)
    (hreads : ∀ p, p ∈ coeffs.zip is → ∃ x, slotInt a p.2 = some x)
    (hdot : dotOver (coeffs.zip is) a 0 = some d)
    (hdeq : d = b)
    (hhead : (negLe m (b - hr - 1)).eval a = some false) : False := by
  rw [hrest] at hsum hcauses hguard
  obtain ⟨xt, hxtm, hdotrest⟩ :=
    lin2_entry_dot hmem hreads hdot
  -- the max-sum bound at the rest
  have hbound : (d - 1 * xt) ≤ hr + 0 :=
    lin2_sumMax_ge (lin2_reads_of_others hreads)
      hguard hcauses _ (fun p hp => hp) hr hsum 0 (d - 1 * xt) hdotrest
  -- the falsified head: xt ≤ b − hr − 1
  obtain ⟨xt2, hsx2, hle⟩ := eval_negLe_false a m (b - hr - 1) hhead
  rw [hxtm] at hsx2
  have hxt2 : xt2 = xt := Option.some.inj hsx2.symm
  rw [hxt2] at hle
  omega

/-- The −1-slot max nogood `[x_m ≤ hiRest − b] ++ maxCauses` of
    `Σ cₜxₜ = b`: falsifying the head puts `x_m > hiRest − b`;
    with the rest pinned at or below `hiRest`,
    `Σ = −x_m + Σ_rest < b`. -/
theorem lin2_absurd_eq_hi_max {a : Assignment} {st : State} {m : Nat}
    {coeffs : List Int} {is : List Nat} {b hr d : Int} {i : Nat}
    {rest : List (Int × Nat)}
    (hmem : ((-1, m), i) ∈ (coeffs.zip is).zipIdx)
    (hrest : rest = (((coeffs.zip is).zipIdx.filter
        (fun q => q.2 != i)).map (·.1)))
    (hguard : ∀ p ∈ rest, (maxContrib st p).isSome = true)
    (hcauses : ∀ q ∈ linCausesMax st rest, q.eval a = some false)
    (hsum : sumMax st rest = some hr)
    (hreads : ∀ p, p ∈ coeffs.zip is → ∃ x, slotInt a p.2 = some x)
    (hdot : dotOver (coeffs.zip is) a 0 = some d)
    (hdeq : d = b)
    (hhead : (posLe m (hr - b)).eval a = some false) : False := by
  rw [hrest] at hsum hcauses hguard
  obtain ⟨xt, hxtm, hdotrest⟩ :=
    lin2_entry_dot hmem hreads hdot
  -- the max-sum bound at the rest
  have hbound : (d - (-1) * xt) ≤ hr + 0 :=
    lin2_sumMax_ge (lin2_reads_of_others hreads)
      hguard hcauses _ (fun p hp => hp) hr hsum 0 (d - (-1) * xt) hdotrest
  -- the falsified head: hr − b < xt
  obtain ⟨xt2, hsx2, hlt⟩ := eval_posLe_false a m (hr - b) hhead
  rw [hxtm] at hsx2
  have hxt2 : xt2 = xt := Option.some.inj hsx2.symm
  rw [hxt2] at hlt
  omega

/-! ## The division spec (the general-coefficient bound arithmetic)

ROUTE (2) (the STRONG floor bound): Lean 4.33 core's Euclidean
`Int.div` satisfies, for a POSITIVE divisor c, the floor spec
`hi·c ≤ a < hi·c + c` with `hi = a / c` (the core lemmas
`Int.ediv_mul_le`, `Int.ediv_mul_add_emod`, `Int.emod_nonneg`,
`Int.emod_lt_of_pos`); the negated floor `-((s / k))` is the
CEILING of `s / k`, whose one-below multiple is strictly below
`-s`. These two facts are the head-true halves of the four
general-coefficient nogoods below. -/

/-- The floor's upper-neighbour fact: `a < (a/c)·c + c` for a
    positive divisor (the spec's strict half, closed by omega over
    the Euclidean division identity). -/
theorem lin2_fl_hi_lt {a c : Int} (hc : 0 < c) :
    a < (a / c) * c + c := by
  have h2 : a % c < c := Int.emod_lt_of_pos a hc
  have h2' : 0 ≤ a % c := Int.emod_nonneg a (by omega)
  have h3 := Int.ediv_mul_add_emod a c
  have key : a / c * c ≤ a ∧ a - (a / c * c) < c := by omega
  omega

/-- The CEILING's one-below fact: for a positive `k`, the multiple
    `(-⌊s/k⌋ - 1)·k` lies strictly below `-s` — the strict half of
    the negated-floor spec, from the floor spec at `-s`. -/
theorem lin2_cl_neg_lo_gt {s k : Int} (hk : 0 < k) :
    (-((s / k)) - 1) * k < -s := by
  have hqk : (s / k) * k ≤ s := Int.ediv_mul_le s (by omega)
  have hfl : s < (s / k) * k + k := lin2_fl_hi_lt hk
  have hexp : (-((s / k)) - 1) * k = -((s / k) * k) - k := by
    rw [Int.sub_mul, Int.neg_mul, Int.one_mul]
  omega

/-- The `firstEvent` pair inversion: a two-element list's result is
    either the first element or (when the first is stable) the
    second — the emission shape of the general-coefficient eq
    arms. -/
theorem firstEvent_two {r1 r2 res : PropagationResult}
    (h : firstEvent [r1, r2] = res) :
    res = r1 ∨ (r1 = .stable ∧ res = r2) := by
  cases r1 with
  | stable =>
      right
      cases r2 with
      | stable => exact ⟨rfl, h.symm⟩
      | implied l r => exact ⟨rfl, h.symm⟩
      | conflict c => exact ⟨rfl, h.symm⟩
  | implied l r => left; exact h.symm
  | conflict c => left; exact h.symm

/-! ## The general-coefficient absurd kernels

Each general-c emitted clause, checked by hand: a solution
falsifying every literal violates the constraint. The two le-shaped
arms (c > 0 upper, c < 0 lower — both also serve the eq family
via `d = b ⟹ d ≤ b`); the two eq-max-shaped arms. -/

/-- The general-c nogood `[x_m ≤ ⌊(b − lr)/c⌋] ++ minCauses` of
    `Σ cₜxₜ ≤ b` (and of `Σ cₜxₜ = b`) for c > 0: falsifying the
    head puts `x_m` above the floor, so
    `c·x_m ≥ (⌊(b−lr)/c⌋+1)·c > b − lr`; with the rest pinned at
    or above `lr`, `Σ > b`. -/
theorem lin2_absurd_gen_le_hi {a : Assignment} {st : State} {m : Nat}
    {coeffs : List Int} {is : List Nat} {b lr d c : Int} {i : Nat}
    {rest : List (Int × Nat)}
    (hmem : ((c, m), i) ∈ (coeffs.zip is).zipIdx)
    (hc : 0 < c)
    (hrest : rest = (((coeffs.zip is).zipIdx.filter
        (fun q => q.2 != i)).map (·.1)))
    (hguard : ∀ p ∈ rest, (minContrib st p).isSome = true)
    (hcauses : ∀ q ∈ linCausesMin st rest, q.eval a = some false)
    (hsum : sumMin st rest = some lr)
    (hreads : ∀ p, p ∈ coeffs.zip is → ∃ x, slotInt a p.2 = some x)
    (hdot : dotOver (coeffs.zip is) a 0 = some d)
    (hdle : d ≤ b)
    (hhead : (posLe m ((b - lr) / c)).eval a = some false) : False := by
  rw [hrest] at hsum hcauses hguard
  obtain ⟨xt, hxtm, hdotrest⟩ :=
    lin2_entry_dot hmem hreads hdot
  -- the min-sum bound at the rest
  have hbound : lr + 0 ≤ (d - c * xt) :=
    lin2_sumMin_le (lin2_reads_of_others hreads)
      hguard hcauses _ (fun p hp => hp) lr hsum 0 (d - c * xt) hdotrest
  -- the falsified head: (b − lr)/c < xt
  obtain ⟨xt2, hsx2, hlt⟩ := eval_posLe_false a m ((b - lr) / c) hhead
  rw [hxtm] at hsx2
  have hxt2 : xt2 = xt := Option.some.inj hsx2.symm
  rw [hxt2] at hlt
  -- the floor spec and the monotone transfer through c > 0
  have hs1 : ((b - lr) / c) * c ≤ b - lr :=
    Int.ediv_mul_le _ (by omega)
  have hs2 : b - lr < ((b - lr) / c) * c + c := lin2_fl_hi_lt hc
  have hmono : ((b - lr) / c) * c + c ≤ c * xt := by
    have h1 : c * (((b - lr) / c) + 1)
        = ((b - lr) / c) * c + c := by
      rw [Int.mul_add, Int.mul_one, Int.mul_comm c ((b - lr) / c)]
    have h2 : c * (((b - lr) / c) + 1) ≤ c * xt :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    rw [h1] at h2
    exact h2
  omega

/-- The general-c nogood `[x_m > −⌊(b − lr)/(−c)⌋ − 1] ++ minCauses`
    of `Σ cₜxₜ ≤ b` (and of `Σ cₜxₜ = b`) for c < 0: falsifying
    the head puts `x_m` at or below the ceiling-less-one multiple,
    so `c·x_m ≥ (lo−1)·(−c) > b − lr` (the negative-coefficient
    monotonicity flips the order); with the rest pinned at or
    above `lr`, `Σ > b`. -/
theorem lin2_absurd_gen_le_lo {a : Assignment} {st : State} {m : Nat}
    {coeffs : List Int} {is : List Nat} {b lr d c : Int} {i : Nat}
    {rest : List (Int × Nat)}
    (hmem : ((c, m), i) ∈ (coeffs.zip is).zipIdx)
    (hc : c < 0)
    (hrest : rest = (((coeffs.zip is).zipIdx.filter
        (fun q => q.2 != i)).map (·.1)))
    (hguard : ∀ p ∈ rest, (minContrib st p).isSome = true)
    (hcauses : ∀ q ∈ linCausesMin st rest, q.eval a = some false)
    (hsum : sumMin st rest = some lr)
    (hreads : ∀ p, p ∈ coeffs.zip is → ∃ x, slotInt a p.2 = some x)
    (hdot : dotOver (coeffs.zip is) a 0 = some d)
    (hdle : d ≤ b)
    (hhead : (negLe m (-((b - lr) / (-c)) - 1)).eval a = some false) :
    False := by
  rw [hrest] at hsum hcauses hguard
  obtain ⟨xt, hxtm, hdotrest⟩ :=
    lin2_entry_dot hmem hreads hdot
  have hbound : lr + 0 ≤ (d - c * xt) :=
    lin2_sumMin_le (lin2_reads_of_others hreads)
      hguard hcauses _ (fun p hp => hp) lr hsum 0 (d - c * xt) hdotrest
  -- the falsified head: xt ≤ −⌊(b − lr)/(−c)⌋ − 1
  obtain ⟨xt2, hsx2, hle⟩ := eval_negLe_false a m
    (-((b - lr) / (-c)) - 1) hhead
  rw [hxtm] at hsx2
  have hxt2 : xt2 = xt := Option.some.inj hsx2.symm
  rw [hxt2] at hle
  -- the ceiling spec at s := b − lr, k := −c:
  -- (lo − 1)·k < −s = lr − b
  have hspec := lin2_cl_neg_lo_gt (s := b - lr) (k := -c) (by omega)
  -- the negative-coefficient monotone transfer
  have hmono : c * (-((b - lr) / (-c)) - 1) ≤ c * xt :=
    Int.mul_le_mul_of_nonpos_left (by omega) (by omega)
  have hneg : c * (-((b - lr) / (-c)) - 1)
      = -((-((b - lr) / (-c)) - 1) * (-c)) := by
    rw [Int.mul_comm, Int.mul_neg, Int.neg_neg]
  omega

/-- The general-c nogood `[x_m > −⌊(hr − b)/c⌋ − 1] ++ maxCauses`
    of `Σ cₜxₜ = b` for c > 0: falsifying the head puts `x_m` at
    or below the ceiling-less-one multiple, so
    `c·x_m ≤ (lo−1)·c < b − hr`; with the rest pinned at or below
    `hr`, `Σ < b`. -/
theorem lin2_absurd_gen_eq_lo_max {a : Assignment} {st : State} {m : Nat}
    {coeffs : List Int} {is : List Nat} {b hr d c : Int} {i : Nat}
    {rest : List (Int × Nat)}
    (hmem : ((c, m), i) ∈ (coeffs.zip is).zipIdx)
    (hc : 0 < c)
    (hrest : rest = (((coeffs.zip is).zipIdx.filter
        (fun q => q.2 != i)).map (·.1)))
    (hguard : ∀ p ∈ rest, (maxContrib st p).isSome = true)
    (hcauses : ∀ q ∈ linCausesMax st rest, q.eval a = some false)
    (hsum : sumMax st rest = some hr)
    (hreads : ∀ p, p ∈ coeffs.zip is → ∃ x, slotInt a p.2 = some x)
    (hdot : dotOver (coeffs.zip is) a 0 = some d)
    (hdeq : d = b)
    (hhead : (negLe m (-((hr - b) / c) - 1)).eval a = some false) :
    False := by
  rw [hrest] at hsum hcauses hguard
  obtain ⟨xt, hxtm, hdotrest⟩ :=
    lin2_entry_dot hmem hreads hdot
  have hbound : (d - c * xt) ≤ hr + 0 :=
    lin2_sumMax_ge (lin2_reads_of_others hreads)
      hguard hcauses _ (fun p hp => hp) hr hsum 0 (d - c * xt) hdotrest
  obtain ⟨xt2, hsx2, hle⟩ := eval_negLe_false a m (-((hr - b) / c) - 1)
    hhead
  rw [hxtm] at hsx2
  have hxt2 : xt2 = xt := Option.some.inj hsx2.symm
  rw [hxt2] at hle
  -- the ceiling spec at s := hr − b, k := c: (lo − 1)·k < −s
  have hspec := lin2_cl_neg_lo_gt (s := hr - b) (k := c) (by omega)
  have hmono : c * xt ≤ c * (-((hr - b) / c) - 1) :=
    Int.mul_le_mul_of_nonneg_left hle (by omega)
  have hcomm : c * (-((hr - b) / c) - 1)
      = (-((hr - b) / c) - 1) * c := Int.mul_comm _ _
  omega

/-- The general-c nogood `[x_m ≤ ⌊(hr − b)/(−c)⌋] ++ maxCauses` of
    `Σ cₜxₜ = b` for c < 0: falsifying the head puts `x_m` above
    the floor, so `c·x_m ≤ c·(hi+1) = −(hi+1)·(−c) < b − hr`
    (the negative coefficient flips the order); with the rest
    pinned at or below `hr`, `Σ < b`. -/
theorem lin2_absurd_gen_eq_hi_max {a : Assignment} {st : State} {m : Nat}
    {coeffs : List Int} {is : List Nat} {b hr d c : Int} {i : Nat}
    {rest : List (Int × Nat)}
    (hmem : ((c, m), i) ∈ (coeffs.zip is).zipIdx)
    (hc : c < 0)
    (hrest : rest = (((coeffs.zip is).zipIdx.filter
        (fun q => q.2 != i)).map (·.1)))
    (hguard : ∀ p ∈ rest, (maxContrib st p).isSome = true)
    (hcauses : ∀ q ∈ linCausesMax st rest, q.eval a = some false)
    (hsum : sumMax st rest = some hr)
    (hreads : ∀ p, p ∈ coeffs.zip is → ∃ x, slotInt a p.2 = some x)
    (hdot : dotOver (coeffs.zip is) a 0 = some d)
    (hdeq : d = b)
    (hhead : (posLe m ((hr - b) / (-c))).eval a = some false) : False := by
  rw [hrest] at hsum hcauses hguard
  obtain ⟨xt, hxtm, hdotrest⟩ :=
    lin2_entry_dot hmem hreads hdot
  have hbound : (d - c * xt) ≤ hr + 0 :=
    lin2_sumMax_ge (lin2_reads_of_others hreads)
      hguard hcauses _ (fun p hp => hp) hr hsum 0 (d - c * xt) hdotrest
  obtain ⟨xt2, hsx2, hlt⟩ := eval_posLe_false a m ((hr - b) / (-c)) hhead
  rw [hxtm] at hsx2
  have hxt2 : xt2 = xt := Option.some.inj hsx2.symm
  rw [hxt2] at hlt
  -- the floor spec at a := hr − b, divisor −c > 0
  have hs1 : ((hr - b) / (-c)) * (-c) ≤ hr - b :=
    Int.ediv_mul_le _ (by omega)
  have hs2 : hr - b < ((hr - b) / (-c)) * (-c) + (-c) :=
    lin2_fl_hi_lt (by omega : (0 : Int) < -c)
  -- the negative-coefficient monotone transfer: xt ≥ hi+1, c < 0
  have hmono : c * xt ≤ c * (((hr - b) / (-c)) + 1) :=
    Int.mul_le_mul_of_nonpos_left (by omega) (by omega)
  have hexp : c * (((hr - b) / (-c)) + 1)
      = c * ((hr - b) / (-c)) + c := by
    rw [Int.mul_add, Int.mul_one]
  have hneg : c * ((hr - b) / (-c))
      = -(((hr - b) / (-c)) * (-c)) := by
    rw [Int.mul_comm, Int.mul_neg, Int.neg_neg]
  omega

/-! ## The sweep and emission inversions

The propagator's result, inverted to ONE narrow call with all its
ingredients: which slot, which rest list, which sum, which clause.
Both the safe triple (at a fitting solution) and the state-free
packages (at an arbitrary internal solution) consume this single
case analysis. -/

/-- The sweep inversion: a non-stable sweep result is one sweep
    position's deduction over the others list of that position. -/
theorem lin2_sweep_inv {f : Nat → Int → List (Int × Nat) → PropagationResult}
    {coeffs : List Int} {is : List Nat}
    {ps : List ((Int × Nat) × Nat)} {idx : Nat} {res : PropagationResult}
    (h : linSweep coeffs is f ps idx = res) :
    res = .stable ∨ ∃ m c i,
      ((c, m), i) ∈ ps ∧
      res = f m c ((((coeffs.zip is).zipIdx).filter
        (fun p => p.2 != i)).map (·.1)) := by
  induction ps generalizing idx with
  | nil =>
      have h2 : linSweep coeffs is f [] idx = .stable := rfl
      rw [h2] at h
      left
      exact h.symm
  | cons entry ps' ih =>
      obtain ⟨p, i⟩ := entry
      obtain ⟨c, m⟩ := p
      have hrw : linSweep coeffs is f (((c, m), i) :: ps') idx =
        (match f m c ((((coeffs.zip is).zipIdx).filter
          (fun p => p.2 != i)).map (·.1)) with
         | .stable => linSweep coeffs is f ps' (idx + 1)
         | r => r) := rfl
      rw [hrw] at h
      cases hf : f m c ((((coeffs.zip is).zipIdx).filter
        (fun p => p.2 != i)).map (·.1)) with
      | stable =>
          rw [hf] at h
          simp only [] at h
          rcases ih (idx := idx + 1) h with h1 | ⟨m2, c2, i2, hmem, hres⟩
          · exact Or.inl h1
          · exact Or.inr ⟨m2, c2, i2, List.mem_cons_of_mem _ hmem, hres⟩
      | implied l r =>
          rw [hf] at h
          exact Or.inr ⟨m, c, i, List.mem_cons_self, by
            rw [hf]; exact h.symm⟩
      | conflict c2 =>
          rw [hf] at h
          exact Or.inr ⟨m, c, i, List.mem_cons_self, by
            rw [hf]; exact h.symm⟩

/-- The master emission inversion for `propLinLe2`: a non-stable
    result is one of the two ±1-slot narrows, with the position's
    membership, the rest list, the completeness guard, and the
    min-sum. -/
theorem propLinLe2_emission_inv {st : State} {coeffs : List Int}
    {is : List Nat} {b : Int} {res : PropagationResult}
    (hrun : propLinLe2 st coeffs is b = res) :
    res = .stable ∨
    (∃ m i rest lr,
      ((1, m), i) ∈ (coeffs.zip is).zipIdx ∧
      rest = (((coeffs.zip is).zipIdx.filter
          (fun q => q.2 != i)).map (·.1)) ∧
      (∀ p ∈ rest, (minContrib st p).isSome = true) ∧
      sumMin st rest = some lr ∧
      res = narrowHi st m (b - lr)
        ([posLe m (b - lr)] ++ linCausesMin st rest)) ∨
    (∃ m i rest lr,
      ((-1, m), i) ∈ (coeffs.zip is).zipIdx ∧
      rest = (((coeffs.zip is).zipIdx.filter
          (fun q => q.2 != i)).map (·.1)) ∧
      (∀ p ∈ rest, (minContrib st p).isSome = true) ∧
      sumMin st rest = some lr ∧
      res = narrowLo st m (lr - b)
        ([negLe m (lr - b - 1)] ++ linCausesMin st rest)) ∨
    (∃ m i rest lr c,
      ((c, m), i) ∈ (coeffs.zip is).zipIdx ∧ 0 < c ∧
      rest = (((coeffs.zip is).zipIdx.filter
          (fun q => q.2 != i)).map (·.1)) ∧
      (∀ p ∈ rest, (minContrib st p).isSome = true) ∧
      sumMin st rest = some lr ∧
      res = narrowHi st m ((b - lr) / c)
        ([posLe m ((b - lr) / c)] ++ linCausesMin st rest)) ∨
    (∃ m i rest lr c,
      ((c, m), i) ∈ (coeffs.zip is).zipIdx ∧ c < 0 ∧
      rest = (((coeffs.zip is).zipIdx.filter
          (fun q => q.2 != i)).map (·.1)) ∧
      (∀ p ∈ rest, (minContrib st p).isSome = true) ∧
      sumMin st rest = some lr ∧
      res = narrowLo st m (-((b - lr) / (-c)))
        ([negLe m (-((b - lr) / (-c)) - 1)] ++ linCausesMin st rest)) := by
  unfold propLinLe2 at hrun
  split at hrun
  · left; exact hrun.symm
  · rcases lin2_sweep_inv hrun with hstable | ⟨m, c, i, hmem, hdet⟩
    · left; exact hstable
    · by_cases hguard : List.all
          ((((coeffs.zip is).zipIdx.filter
            (fun q => q.2 != i)).map (·.1)))
            (fun p => (minContrib st p).isSome) = true
      · have hguard' : ∀ p ∈ (((coeffs.zip is).zipIdx.filter
            (fun q => q.2 != i)).map (·.1)),
            (minContrib st p).isSome = true :=
          fun p hp => (List.all_eq_true.mp hguard) p hp
        have hc3 : c = 1 ∨ c = -1 ∨ (c ≠ 1 ∧ c ≠ -1) := by omega
        rcases hc3 with hc | hc | hc
        · subst hc
          cases hlr : sumMin st
              (((coeffs.zip is).zipIdx.filter
                (fun q => q.2 != i)).map (·.1)) with
          | none =>
              left
              exact hdet.trans
                (by
                  unfold linDeduceLe
                  rw [if_pos hguard, if_pos rfl, hlr])
          | some lr =>
              right
              left
              refine ⟨m, i, _, lr, hmem, rfl, hguard', hlr, ?_⟩
              rw [hdet]
              unfold linDeduceLe
              rw [if_pos hguard, if_pos rfl, hlr]
        · subst hc
          cases hlr : sumMin st
              (((coeffs.zip is).zipIdx.filter
                (fun q => q.2 != i)).map (·.1)) with
          | none =>
              left
              exact hdet.trans
                (by
                  unfold linDeduceLe
                  rw [if_pos hguard,
                    if_neg (by omega : ¬ (-1 : Int) = 1),
                    if_pos rfl, hlr])
          | some lr =>
              right
              right
              left
              refine ⟨m, i, _, lr, hmem, rfl, hguard', hlr, ?_⟩
              rw [hdet]
              unfold linDeduceLe
              rw [if_pos hguard, if_neg (by omega : ¬ (-1 : Int) = 1),
                if_pos rfl, hlr]
        · -- the general-coefficient arms: c ≠ 1, c ≠ −1
          have hgp : (0 : Int) < c ∨ c < 0 ∨ c = 0 := by omega
          cases hlr : sumMin st
              (((coeffs.zip is).zipIdx.filter
                (fun q => q.2 != i)).map (·.1)) with
          | none =>
              left
              rcases hgp with hpos | hneg | hzero
              · exact hdet.trans
                  (by
                    unfold linDeduceLe
                    rw [if_pos hguard, if_neg hc.1, if_neg hc.2,
                      if_pos hpos, hlr])
              · exact hdet.trans
                  (by
                    unfold linDeduceLe
                    rw [if_pos hguard, if_neg hc.1, if_neg hc.2,
                      if_neg (by omega : ¬ (0 : Int) < c),
                      if_pos hneg, hlr])
              · exact hdet.trans
                  (by
                    unfold linDeduceLe
                    rw [if_pos hguard, if_neg hc.1, if_neg hc.2,
                      if_neg (by omega : ¬ (0 : Int) < c),
                      if_neg (by omega : ¬ c < (0 : Int))])
          | some lr =>
              rcases hgp with hpos | hneg | hzero
              · right
                right
                right
                left
                refine ⟨m, i, _, lr, c, hmem, hpos, rfl, hguard',
                  hlr, ?_⟩
                rw [hdet]
                unfold linDeduceLe
                rw [if_pos hguard, if_neg hc.1, if_neg hc.2,
                  if_pos hpos, hlr]
                rfl
              · right
                right
                right
                right
                refine ⟨m, i, _, lr, c, hmem, hneg, rfl, hguard',
                  hlr, ?_⟩
                rw [hdet]
                unfold linDeduceLe
                rw [if_pos hguard, if_neg hc.1, if_neg hc.2,
                  if_neg (by omega : ¬ (0 : Int) < c),
                  if_pos hneg, hlr]
                rfl
              · left
                exact hdet.trans
                  (by
                    unfold linDeduceLe
                    rw [if_pos hguard, if_neg hc.1, if_neg hc.2,
                      if_neg (by omega : ¬ (0 : Int) < c),
                      if_neg (by omega : ¬ c < (0 : Int))])
      · left
        exact hdet.trans
          (by
            unfold linDeduceLe
            rw [if_neg (by
              intro hcon
              rw [hcon] at hguard
              exact absurd hguard (by simp))])

/-- A false `List.all` carries a failing element. -/
theorem lin2_all_false_mem {α : Type} (p : α → Bool) :
    ∀ (l : List α), l.all p = false → ∃ x ∈ l, p x = false := by
  intro l
  induction l with
  | nil => intro h; simp [List.all] at h
  | cons x xs ih =>
      intro h
      by_cases hx : p x = true
      · rw [List.all_cons, hx] at h
        have hnot : (xs.all p) = false := by
          cases hxs : xs.all p with
          | true => rw [hxs] at h; simp at h
          | false => rfl
        obtain ⟨y, hy, hy2⟩ := ih hnot
        exact ⟨y, List.mem_cons_of_mem _ hy, hy2⟩
      · have hx2 : p x = false := by
          cases hpx : p x with
          | true => exact absurd hpx hx
          | false => rfl
        exact ⟨x, List.mem_cons_self, hx2⟩

/-- The master emission inversion for `propLinEq2`: a non-stable
    result is one of the FOUR ±1-slot narrows (the two bounds per
    slot polarity) or one of the FOUR general-coefficient narrows
    (the two divided bounds per slot polarity). -/
theorem propLinEq2_emission_inv {st : State} {coeffs : List Int}
    {is : List Nat} {b : Int} {res : PropagationResult}
    (hrun : propLinEq2 st coeffs is b = res) :
    res = .stable ∨
    (∃ m i rest lr,
      ((1, m), i) ∈ (coeffs.zip is).zipIdx ∧
      rest = (((coeffs.zip is).zipIdx.filter
          (fun q => q.2 != i)).map (·.1)) ∧
      (∀ p ∈ rest, (minContrib st p).isSome = true) ∧
      sumMin st rest = some lr ∧
      res = narrowHi st m (b - lr)
        ([posLe m (b - lr)] ++ linCausesMin st rest)) ∨
    (∃ m i rest hr,
      ((1, m), i) ∈ (coeffs.zip is).zipIdx ∧
      rest = (((coeffs.zip is).zipIdx.filter
          (fun q => q.2 != i)).map (·.1)) ∧
      (∀ p ∈ rest, (maxContrib st p).isSome = true) ∧
      sumMax st rest = some hr ∧
      res = narrowLo st m (b - hr)
        ([negLe m (b - hr - 1)] ++ linCausesMax st rest)) ∨
    (∃ m i rest lr,
      ((-1, m), i) ∈ (coeffs.zip is).zipIdx ∧
      rest = (((coeffs.zip is).zipIdx.filter
          (fun q => q.2 != i)).map (·.1)) ∧
      (∀ p ∈ rest, (minContrib st p).isSome = true) ∧
      sumMin st rest = some lr ∧
      res = narrowLo st m (lr - b)
        ([negLe m (lr - b - 1)] ++ linCausesMin st rest)) ∨
    (∃ m i rest hr,
      ((-1, m), i) ∈ (coeffs.zip is).zipIdx ∧
      rest = (((coeffs.zip is).zipIdx.filter
          (fun q => q.2 != i)).map (·.1)) ∧
      (∀ p ∈ rest, (maxContrib st p).isSome = true) ∧
      sumMax st rest = some hr ∧
      res = narrowHi st m (hr - b)
        ([posLe m (hr - b)] ++ linCausesMax st rest)) ∨
    (∃ m i rest lr c,
      ((c, m), i) ∈ (coeffs.zip is).zipIdx ∧ 0 < c ∧
      rest = (((coeffs.zip is).zipIdx.filter
          (fun q => q.2 != i)).map (·.1)) ∧
      (∀ p ∈ rest, (minContrib st p).isSome = true) ∧
      sumMin st rest = some lr ∧
      res = narrowHi st m ((b - lr) / c)
        ([posLe m ((b - lr) / c)] ++ linCausesMin st rest)) ∨
    (∃ m i rest hr c,
      ((c, m), i) ∈ (coeffs.zip is).zipIdx ∧ 0 < c ∧
      rest = (((coeffs.zip is).zipIdx.filter
          (fun q => q.2 != i)).map (·.1)) ∧
      (∀ p ∈ rest, (maxContrib st p).isSome = true) ∧
      sumMax st rest = some hr ∧
      res = narrowLo st m (-((hr - b) / c))
        ([negLe m (-((hr - b) / c) - 1)] ++ linCausesMax st rest)) ∨
    (∃ m i rest lr c,
      ((c, m), i) ∈ (coeffs.zip is).zipIdx ∧ c < 0 ∧
      rest = (((coeffs.zip is).zipIdx.filter
          (fun q => q.2 != i)).map (·.1)) ∧
      (∀ p ∈ rest, (minContrib st p).isSome = true) ∧
      sumMin st rest = some lr ∧
      res = narrowLo st m (-((b - lr) / (-c)))
        ([negLe m (-((b - lr) / (-c)) - 1)] ++ linCausesMin st rest)) ∨
    (∃ m i rest hr c,
      ((c, m), i) ∈ (coeffs.zip is).zipIdx ∧ c < 0 ∧
      rest = (((coeffs.zip is).zipIdx.filter
          (fun q => q.2 != i)).map (·.1)) ∧
      (∀ p ∈ rest, (maxContrib st p).isSome = true) ∧
      sumMax st rest = some hr ∧
      res = narrowHi st m ((hr - b) / (-c))
        ([posLe m ((hr - b) / (-c))] ++ linCausesMax st rest)) := by
  unfold propLinEq2 at hrun
  split at hrun
  · left; exact hrun.symm
  · rcases lin2_sweep_inv hrun with hstable | ⟨m, c, i, hmem, hdet⟩
    · left; exact hstable
    · by_cases hguardMin : List.all
          ((((coeffs.zip is).zipIdx.filter
            (fun q => q.2 != i)).map (·.1)))
            (fun p => (minContrib st p).isSome) = true
      · have hguardMin' : ∀ p ∈ (((coeffs.zip is).zipIdx.filter
            (fun q => q.2 != i)).map (·.1)),
            (minContrib st p).isSome = true :=
          fun p hp => (List.all_eq_true.mp hguardMin) p hp
        by_cases hguardMax : List.all
            ((((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1)))
            (fun p => (maxContrib st p).isSome) = true
        · have hguardMax' : ∀ p ∈ (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1)),
              (maxContrib st p).isSome = true :=
            fun p hp => (List.all_eq_true.mp hguardMax) p hp
          have hc3 : c = 1 ∨ c = -1 ∨ (c ≠ 1 ∧ c ≠ -1) := by omega
          rcases hc3 with hc | hc | hc
          · subst hc
            -- c = 1: firstEvent [HiMin (sumMin), LoMax (sumMax)]
            cases hlr : sumMin st
                (((coeffs.zip is).zipIdx.filter
                  (fun q => q.2 != i)).map (·.1)) with
            | none =>
                -- the HiMin arm is stable
                cases hhr : sumMax st
                    (((coeffs.zip is).zipIdx.filter
                      (fun q => q.2 != i)).map (·.1)) with
                | none =>
                    left
                    refine hdet.trans ?_
                    unfold linDeduceEq
                    rw [if_pos hguardMin, if_pos rfl]
                    have h1 : linEqArmHiMin st m b
                        (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                        (sumMin st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) = .stable := by
                      unfold linEqArmHiMin
                      rw [hlr]
                    have h2 : linEqArmLoMax st m b
                        (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                        (sumMax st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) = .stable := by
                      unfold linEqArmLoMax
                      rw [hhr]
                    rw [h1, h2]
                    rfl
                | some hr =>
                    -- res = firstEvent [stable, narrowLo Y] = narrowLo Y
                    right
                    right
                    left
                    refine ⟨m, i, _, hr, hmem, rfl, hguardMax', hhr, ?_⟩
                    rw [hdet]
                    unfold linDeduceEq
                    rw [if_pos hguardMin, if_pos rfl]
                    have h1 : linEqArmHiMin st m b
                        (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                        (sumMin st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) = .stable := by
                      unfold linEqArmHiMin
                      rw [hlr]
                    have h2 : linEqArmLoMax st m b
                        (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                        (sumMax st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) =
                        narrowLo st m (b - hr)
                          ([negLe m (b - hr - 1)] ++
                            linCausesMax st (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) := by
                      unfold linEqArmLoMax
                      rw [hhr]
                    rw [h1, h2]
                    cases hy : narrowLo st m (b - hr)
                          ([negLe m (b - hr - 1)] ++
                            linCausesMax st (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) with
                    | stable => rfl
                    | implied l r => rfl
                    | conflict c2 => rfl
            | some lr =>
                -- the HiMin arm is narrowHi X
                cases hhr : sumMax st
                    (((coeffs.zip is).zipIdx.filter
                      (fun q => q.2 != i)).map (·.1)) with
                | none =>
                    -- res = firstEvent [narrowHi X, stable]: case on X
                    cases hx : narrowHi st m (b - lr)
                          ([posLe m (b - lr)] ++ linCausesMin st
                            (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) with
                    | stable =>
                        left
                        refine hdet.trans ?_
                        unfold linDeduceEq
                        rw [if_pos hguardMin, if_pos rfl]
                        have h1 : linEqArmHiMin st m b
                            (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                            (sumMin st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) =
                            narrowHi st m (b - lr)
                              ([posLe m (b - lr)] ++ linCausesMin st
                                (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) := by
                          unfold linEqArmHiMin
                          rw [hlr]
                        have h2 : linEqArmLoMax st m b
                            (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                            (sumMax st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) = .stable := by
                          unfold linEqArmLoMax
                          rw [hhr]
                        rw [h1, h2, hx]
                        rfl
                    | implied l r =>
                        right
                        left
                        refine ⟨m, i, _, lr, hmem, rfl, hguardMin', hlr, ?_⟩
                        rw [hdet]
                        unfold linDeduceEq
                        rw [if_pos hguardMin, if_pos rfl]
                        have h1 : linEqArmHiMin st m b
                            (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                            (sumMin st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) =
                            narrowHi st m (b - lr)
                              ([posLe m (b - lr)] ++ linCausesMin st
                                (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) := by
                          unfold linEqArmHiMin
                          rw [hlr]
                        have h2 : linEqArmLoMax st m b
                            (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                            (sumMax st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) = .stable := by
                          unfold linEqArmLoMax
                          rw [hhr]
                        rw [h1, h2, hx]
                        rfl
                    | conflict c2 =>
                        right
                        left
                        refine ⟨m, i, _, lr, hmem, rfl, hguardMin', hlr, ?_⟩
                        rw [hdet]
                        unfold linDeduceEq
                        rw [if_pos hguardMin, if_pos rfl]
                        have h1 : linEqArmHiMin st m b
                            (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                            (sumMin st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) =
                            narrowHi st m (b - lr)
                              ([posLe m (b - lr)] ++ linCausesMin st
                                (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) := by
                          unfold linEqArmHiMin
                          rw [hlr]
                        have h2 : linEqArmLoMax st m b
                            (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                            (sumMax st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) = .stable := by
                          unfold linEqArmLoMax
                          rw [hhr]
                        rw [h1, h2, hx]
                        rfl
                | some hr =>
                    -- res = firstEvent [narrowHi X, narrowLo Y]
                    cases hx : narrowHi st m (b - lr)
                          ([posLe m (b - lr)] ++ linCausesMin st
                            (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) with
                    | stable =>
                        cases hy : narrowLo st m (b - hr)
                              ([negLe m (b - hr - 1)] ++
                                linCausesMax st (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) with
                        | stable =>
                            left
                            refine hdet.trans ?_
                            unfold linDeduceEq
                            rw [if_pos hguardMin, if_pos rfl]
                            have h1 : linEqArmHiMin st m b
                                (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                                (sumMin st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) =
                                narrowHi st m (b - lr)
                                  ([posLe m (b - lr)] ++ linCausesMin st
                                    (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) := by
                              unfold linEqArmHiMin
                              rw [hlr]
                            have h2 : linEqArmLoMax st m b
                                (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                                (sumMax st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) =
                                narrowLo st m (b - hr)
                                  ([negLe m (b - hr - 1)] ++
                                    linCausesMax st (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) := by
                              unfold linEqArmLoMax
                              rw [hhr]
                            rw [h1, h2, hx, hy]
                            rfl
                        | implied l r =>
                            right
                            right
                            left
                            refine ⟨m, i, _, hr, hmem, rfl, hguardMax',
                              hhr, ?_⟩
                            rw [hdet]
                            unfold linDeduceEq
                            rw [if_pos hguardMin, if_pos rfl]
                            have h1 : linEqArmHiMin st m b
                                (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                                (sumMin st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) =
                                narrowHi st m (b - lr)
                                  ([posLe m (b - lr)] ++ linCausesMin st
                                    (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) := by
                              unfold linEqArmHiMin
                              rw [hlr]
                            have h2 : linEqArmLoMax st m b
                                (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                                (sumMax st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) =
                                narrowLo st m (b - hr)
                                  ([negLe m (b - hr - 1)] ++
                                    linCausesMax st (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) := by
                              unfold linEqArmLoMax
                              rw [hhr]
                            rw [h1, h2, hx, hy]
                            rfl
                        | conflict c2 =>
                            right
                            right
                            left
                            refine ⟨m, i, _, hr, hmem, rfl, hguardMax',
                              hhr, ?_⟩
                            rw [hdet]
                            unfold linDeduceEq
                            rw [if_pos hguardMin, if_pos rfl]
                            have h1 : linEqArmHiMin st m b
                                (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                                (sumMin st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) =
                                narrowHi st m (b - lr)
                                  ([posLe m (b - lr)] ++ linCausesMin st
                                    (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) := by
                              unfold linEqArmHiMin
                              rw [hlr]
                            have h2 : linEqArmLoMax st m b
                                (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                                (sumMax st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) =
                                narrowLo st m (b - hr)
                                  ([negLe m (b - hr - 1)] ++
                                    linCausesMax st (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) := by
                              unfold linEqArmLoMax
                              rw [hhr]
                            rw [h1, h2, hx, hy]
                            rfl
                    | implied l r =>
                        right
                        left
                        refine ⟨m, i, _, lr, hmem, rfl, hguardMin',
                          hlr, ?_⟩
                        rw [hdet]
                        unfold linDeduceEq
                        rw [if_pos hguardMin, if_pos rfl]
                        have h1 : linEqArmHiMin st m b
                            (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                            (sumMin st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) =
                            narrowHi st m (b - lr)
                              ([posLe m (b - lr)] ++ linCausesMin st
                                (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) := by
                          unfold linEqArmHiMin
                          rw [hlr]
                        have h2 : linEqArmLoMax st m b
                            (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                            (sumMax st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) =
                            narrowLo st m (b - hr)
                              ([negLe m (b - hr - 1)] ++
                                linCausesMax st (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) := by
                          unfold linEqArmLoMax
                          rw [hhr]
                        rw [h1, h2, hx]
                        rfl
                    | conflict c2 =>
                        right
                        left
                        refine ⟨m, i, _, lr, hmem, rfl, hguardMin',
                          hlr, ?_⟩
                        rw [hdet]
                        unfold linDeduceEq
                        rw [if_pos hguardMin, if_pos rfl]
                        have h1 : linEqArmHiMin st m b
                            (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                            (sumMin st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) =
                            narrowHi st m (b - lr)
                              ([posLe m (b - lr)] ++ linCausesMin st
                                (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) := by
                          unfold linEqArmHiMin
                          rw [hlr]
                        have h2 : linEqArmLoMax st m b
                            (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                            (sumMax st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) =
                            narrowLo st m (b - hr)
                              ([negLe m (b - hr - 1)] ++
                                linCausesMax st (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) := by
                          unfold linEqArmLoMax
                          rw [hhr]
                        rw [h1, h2, hx]
                        rfl
          · subst hc
            -- c = -1: firstEvent [LoMin (sumMin), HiMax (sumMax)]
            cases hlr : sumMin st
                (((coeffs.zip is).zipIdx.filter
                  (fun q => q.2 != i)).map (·.1)) with
            | none =>
                -- the LoMin arm is stable
                cases hhr : sumMax st
                    (((coeffs.zip is).zipIdx.filter
                      (fun q => q.2 != i)).map (·.1)) with
                | none =>
                    left
                    refine hdet.trans ?_
                    unfold linDeduceEq
                    rw [if_pos hguardMin,
                      if_neg (by omega : ¬ (-1 : Int) = 1), if_pos rfl]
                    have h1 : linEqArmLoMin st m b
                        (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                        (sumMin st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) = .stable := by
                      unfold linEqArmLoMin
                      rw [hlr]
                    have h2 : linEqArmHiMax st m b
                        (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                        (sumMax st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) = .stable := by
                      unfold linEqArmHiMax
                      rw [hhr]
                    rw [h1, h2]
                    rfl
                | some hr =>
                    -- res = firstEvent [stable, narrowHi Y] = narrowHi Y
                    right
                    right
                    right
                    right
                    left
                    refine ⟨m, i, _, hr, hmem, rfl, hguardMax', hhr, ?_⟩
                    rw [hdet]
                    unfold linDeduceEq
                    rw [if_pos hguardMin,
                      if_neg (by omega : ¬ (-1 : Int) = 1), if_pos rfl]
                    have h1 : linEqArmLoMin st m b
                        (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                        (sumMin st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) = .stable := by
                      unfold linEqArmLoMin
                      rw [hlr]
                    have h2 : linEqArmHiMax st m b
                        (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                        (sumMax st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) =
                        narrowHi st m (hr - b)
                          ([posLe m (hr - b)] ++ linCausesMax st
                            (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) := by
                      unfold linEqArmHiMax
                      rw [hhr]
                    rw [h1, h2]
                    cases hy : narrowHi st m (hr - b)
                          ([posLe m (hr - b)] ++ linCausesMax st
                            (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) with
                    | stable => rfl
                    | implied l r => rfl
                    | conflict c2 => rfl
            | some lr =>
                -- the LoMin arm is narrowLo X
                cases hhr : sumMax st
                    (((coeffs.zip is).zipIdx.filter
                      (fun q => q.2 != i)).map (·.1)) with
                | none =>
                    -- res = firstEvent [narrowLo X, stable]: case on X
                    cases hx : narrowLo st m (lr - b)
                          ([negLe m (lr - b - 1)] ++ linCausesMin st
                            (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) with
                    | stable =>
                        left
                        refine hdet.trans ?_
                        unfold linDeduceEq
                        rw [if_pos hguardMin,
                          if_neg (by omega : ¬ (-1 : Int) = 1),
                          if_pos rfl]
                        have h1 : linEqArmLoMin st m b
                            (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                            (sumMin st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) =
                            narrowLo st m (lr - b)
                              ([negLe m (lr - b - 1)] ++
                                linCausesMin st (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) := by
                          unfold linEqArmLoMin
                          rw [hlr]
                        have h2 : linEqArmHiMax st m b
                            (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                            (sumMax st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) = .stable := by
                          unfold linEqArmHiMax
                          rw [hhr]
                        rw [h1, h2, hx]
                        rfl
                    | implied l r =>
                        right
                        right
                        right
                        left
                        refine ⟨m, i, _, lr, hmem, rfl, hguardMin',
                          hlr, ?_⟩
                        rw [hdet]
                        unfold linDeduceEq
                        rw [if_pos hguardMin,
                          if_neg (by omega : ¬ (-1 : Int) = 1),
                          if_pos rfl]
                        have h1 : linEqArmLoMin st m b
                            (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                            (sumMin st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) =
                            narrowLo st m (lr - b)
                              ([negLe m (lr - b - 1)] ++
                                linCausesMin st (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) := by
                          unfold linEqArmLoMin
                          rw [hlr]
                        have h2 : linEqArmHiMax st m b
                            (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                            (sumMax st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) = .stable := by
                          unfold linEqArmHiMax
                          rw [hhr]
                        rw [h1, h2, hx]
                        rfl
                    | conflict c2 =>
                        right
                        right
                        right
                        left
                        refine ⟨m, i, _, lr, hmem, rfl, hguardMin',
                          hlr, ?_⟩
                        rw [hdet]
                        unfold linDeduceEq
                        rw [if_pos hguardMin,
                          if_neg (by omega : ¬ (-1 : Int) = 1),
                          if_pos rfl]
                        have h1 : linEqArmLoMin st m b
                            (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                            (sumMin st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) =
                            narrowLo st m (lr - b)
                              ([negLe m (lr - b - 1)] ++
                                linCausesMin st (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) := by
                          unfold linEqArmLoMin
                          rw [hlr]
                        have h2 : linEqArmHiMax st m b
                            (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                            (sumMax st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) = .stable := by
                          unfold linEqArmHiMax
                          rw [hhr]
                        rw [h1, h2, hx]
                        rfl
                | some hr =>
                    -- res = firstEvent [narrowLo X, narrowHi Y]
                    cases hx : narrowLo st m (lr - b)
                          ([negLe m (lr - b - 1)] ++ linCausesMin st
                            (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) with
                    | stable =>
                        cases hy : narrowHi st m (hr - b)
                              ([posLe m (hr - b)] ++ linCausesMax st
                                (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) with
                        | stable =>
                            left
                            refine hdet.trans ?_
                            unfold linDeduceEq
                            rw [if_pos hguardMin,
                              if_neg (by omega : ¬ (-1 : Int) = 1),
                              if_pos rfl]
                            have h1 : linEqArmLoMin st m b
                                (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                                (sumMin st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) =
                                narrowLo st m (lr - b)
                                  ([negLe m (lr - b - 1)] ++
                                    linCausesMin st (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) := by
                              unfold linEqArmLoMin
                              rw [hlr]
                            have h2 : linEqArmHiMax st m b
                                (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                                (sumMax st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) =
                                narrowHi st m (hr - b)
                                  ([posLe m (hr - b)] ++
                                    linCausesMax st (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) := by
                              unfold linEqArmHiMax
                              rw [hhr]
                            rw [h1, h2, hx, hy]
                            rfl
                        | implied l r =>
                            right
                            right
                            right
                            right
                            left
                            refine ⟨m, i, _, hr, hmem, rfl, hguardMax',
                              hhr, ?_⟩
                            rw [hdet]
                            unfold linDeduceEq
                            rw [if_pos hguardMin,
                              if_neg (by omega : ¬ (-1 : Int) = 1),
                              if_pos rfl]
                            have h1 : linEqArmLoMin st m b
                                (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                                (sumMin st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) =
                                narrowLo st m (lr - b)
                                  ([negLe m (lr - b - 1)] ++
                                    linCausesMin st (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) := by
                              unfold linEqArmLoMin
                              rw [hlr]
                            have h2 : linEqArmHiMax st m b
                                (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                                (sumMax st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) =
                                narrowHi st m (hr - b)
                                  ([posLe m (hr - b)] ++
                                    linCausesMax st (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) := by
                              unfold linEqArmHiMax
                              rw [hhr]
                            rw [h1, h2, hx, hy]
                            rfl
                        | conflict c2 =>
                            right
                            right
                            right
                            right
                            left
                            refine ⟨m, i, _, hr, hmem, rfl, hguardMax',
                              hhr, ?_⟩
                            rw [hdet]
                            unfold linDeduceEq
                            rw [if_pos hguardMin,
                              if_neg (by omega : ¬ (-1 : Int) = 1),
                              if_pos rfl]
                            have h1 : linEqArmLoMin st m b
                                (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                                (sumMin st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) =
                                narrowLo st m (lr - b)
                                  ([negLe m (lr - b - 1)] ++
                                    linCausesMin st (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) := by
                              unfold linEqArmLoMin
                              rw [hlr]
                            have h2 : linEqArmHiMax st m b
                                (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                                (sumMax st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) =
                                narrowHi st m (hr - b)
                                  ([posLe m (hr - b)] ++
                                    linCausesMax st (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) := by
                              unfold linEqArmHiMax
                              rw [hhr]
                            rw [h1, h2, hx, hy]
                            rfl
                    | implied l r =>
                        right
                        right
                        right
                        left
                        refine ⟨m, i, _, lr, hmem, rfl, hguardMin',
                          hlr, ?_⟩
                        rw [hdet]
                        unfold linDeduceEq
                        rw [if_pos hguardMin,
                          if_neg (by omega : ¬ (-1 : Int) = 1),
                          if_pos rfl]
                        have h1 : linEqArmLoMin st m b
                            (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                            (sumMin st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) =
                            narrowLo st m (lr - b)
                              ([negLe m (lr - b - 1)] ++
                                linCausesMin st (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) := by
                          unfold linEqArmLoMin
                          rw [hlr]
                        have h2 : linEqArmHiMax st m b
                            (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                            (sumMax st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) =
                            narrowHi st m (hr - b)
                              ([posLe m (hr - b)] ++
                                linCausesMax st (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) := by
                          unfold linEqArmHiMax
                          rw [hhr]
                        rw [h1, h2, hx]
                        rfl
                    | conflict c2 =>
                        right
                        right
                        right
                        left
                        refine ⟨m, i, _, lr, hmem, rfl, hguardMin',
                          hlr, ?_⟩
                        rw [hdet]
                        unfold linDeduceEq
                        rw [if_pos hguardMin,
                          if_neg (by omega : ¬ (-1 : Int) = 1),
                          if_pos rfl]
                        have h1 : linEqArmLoMin st m b
                            (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                            (sumMin st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) =
                            narrowLo st m (lr - b)
                              ([negLe m (lr - b - 1)] ++
                                linCausesMin st (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) := by
                          unfold linEqArmLoMin
                          rw [hlr]
                        have h2 : linEqArmHiMax st m b
                            (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
                            (sumMax st (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))) =
                            narrowHi st m (hr - b)
                              ([posLe m (hr - b)] ++
                                linCausesMax st (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1))) := by
                          unfold linEqArmHiMax
                          rw [hhr]
                        rw [h1, h2, hx]
                        rfl
          · -- the general-coefficient arms: firstEvent over the two
            -- divided bounds (the pair inversion gives the case
            -- analysis; each arm is one narrow call to unfold)
            have hgp : (0 : Int) < c ∨ c < 0 ∨ c = 0 := by omega
            rcases hgp with hpos | hneg | hzero
            · -- c > 0: firstEvent [genHiMin (sumMin), genLoMax (sumMax)]
              have hdet2 : res = firstEvent
                  [ linGenArmHiMin st m b c
                      ((((coeffs.zip is).zipIdx.filter
                        (fun q => q.2 != i)).map (·.1)))
                      (sumMin st (((coeffs.zip is).zipIdx.filter
                        (fun q => q.2 != i)).map (·.1)))
                  , linGenArmLoMax st m b c
                      ((((coeffs.zip is).zipIdx.filter
                        (fun q => q.2 != i)).map (·.1)))
                      (sumMax st (((coeffs.zip is).zipIdx.filter
                        (fun q => q.2 != i)).map (·.1))) ] := by
                rw [hdet]
                unfold linDeduceEq
                rw [if_pos hguardMin, if_neg hc.1, if_neg hc.2,
                  if_pos hpos]
              rcases firstEvent_two hdet2.symm with hfirst |
                ⟨hstable, hsecond⟩
              · -- the HiMin arm fired: it is a narrowHi (or stable)
                cases hlr : sumMin st
                    (((coeffs.zip is).zipIdx.filter
                      (fun q => q.2 != i)).map (·.1)) with
                | none =>
                    left
                    rw [hfirst]
                    unfold linGenArmHiMin
                    rw [hlr]
                | some lr =>
                    have hshape : res = narrowHi st m ((b - lr) / c)
                        ([posLe m ((b - lr) / c)] ++
                          linCausesMin st (((coeffs.zip is).zipIdx.filter
                            (fun q => q.2 != i)).map (·.1))) := by
                      rw [hfirst, hlr]
                      rfl
                    right
                    right
                    right
                    right
                    right
                    left
                    exact ⟨m, i, _, lr, c, hmem, hpos, rfl,
                      hguardMin', hlr, hshape⟩
              · -- the LoMax arm fired (the HiMin arm was stable)
                cases hhr : sumMax st
                    (((coeffs.zip is).zipIdx.filter
                      (fun q => q.2 != i)).map (·.1)) with
                | none =>
                    left
                    rw [hsecond, hhr]
                    rfl
                | some hr =>
                    have hshape : res = narrowLo st m (-((hr - b) / c))
                        ([negLe m (-((hr - b) / c) - 1)] ++
                          linCausesMax st (((coeffs.zip is).zipIdx.filter
                            (fun q => q.2 != i)).map (·.1))) := by
                      rw [hsecond, hhr]
                      rfl
                    right
                    right
                    right
                    right
                    right
                    right
                    left
                    exact ⟨m, i, _, hr, c, hmem, hpos, rfl,
                      hguardMax', hhr, hshape⟩
            · -- c < 0: firstEvent [genLoMin (sumMin), genHiMax (sumMax)]
              have hdet2 : res = firstEvent
                  [ linGenArmLoMin st m b c
                      ((((coeffs.zip is).zipIdx.filter
                        (fun q => q.2 != i)).map (·.1)))
                      (sumMin st (((coeffs.zip is).zipIdx.filter
                        (fun q => q.2 != i)).map (·.1)))
                  , linGenArmHiMax st m b c
                      ((((coeffs.zip is).zipIdx.filter
                        (fun q => q.2 != i)).map (·.1)))
                      (sumMax st (((coeffs.zip is).zipIdx.filter
                        (fun q => q.2 != i)).map (·.1))) ] := by
                rw [hdet]
                unfold linDeduceEq
                rw [if_pos hguardMin, if_neg hc.1, if_neg hc.2,
                  if_neg (by omega : ¬ (0 : Int) < c), if_pos hneg]
              rcases firstEvent_two hdet2.symm with hfirst |
                ⟨hstable, hsecond⟩
              · -- the LoMin arm fired: a narrowLo (or stable)
                cases hlr : sumMin st
                    (((coeffs.zip is).zipIdx.filter
                      (fun q => q.2 != i)).map (·.1)) with
                | none =>
                    left
                    rw [hfirst]
                    unfold linGenArmLoMin
                    rw [hlr]
                | some lr =>
                    have hshape : res = narrowLo st m (-((b - lr) / (-c)))
                        ([negLe m (-((b - lr) / (-c)) - 1)] ++
                          linCausesMin st (((coeffs.zip is).zipIdx.filter
                            (fun q => q.2 != i)).map (·.1))) := by
                      rw [hfirst, hlr]
                      rfl
                    right
                    right
                    right
                    right
                    right
                    right
                    right
                    left
                    exact ⟨m, i, _, lr, c, hmem, hneg, rfl,
                      hguardMin', hlr, hshape⟩
              · -- the HiMax arm fired (the LoMin arm was stable)
                cases hhr : sumMax st
                    (((coeffs.zip is).zipIdx.filter
                      (fun q => q.2 != i)).map (·.1)) with
                | none =>
                    left
                    rw [hsecond, hhr]
                    rfl
                | some hr =>
                    have hshape : res = narrowHi st m ((hr - b) / (-c))
                        ([posLe m ((hr - b) / (-c))] ++
                          linCausesMax st (((coeffs.zip is).zipIdx.filter
                            (fun q => q.2 != i)).map (·.1))) := by
                      rw [hsecond, hhr]
                      rfl
                    right
                    right
                    right
                    right
                    right
                    right
                    right
                    right
                    exact ⟨m, i, _, hr, c, hmem, hneg, rfl,
                      hguardMax', hhr, hshape⟩
            · left
              refine hdet.trans ?_
              unfold linDeduceEq
              rw [if_pos hguardMin, if_neg hc.1, if_neg hc.2,
                if_neg (by omega : ¬ (0 : Int) < c),
                if_neg (by omega : ¬ c < (0 : Int))]
        · exfalso
          -- min-guard true but max-guard false: impossible (a pair
          -- with a min-contribution also has a max-contribution)
          have hcontra : ∃ p, p ∈ (((coeffs.zip is).zipIdx.filter
              (fun q => q.2 != i)).map (·.1)) ∧
              (maxContrib st p).isSome = false := by
            have hall : (((coeffs.zip is).zipIdx.filter
                (fun q => q.2 != i)).map (·.1)).all
                (fun p => (maxContrib st p).isSome) = false := by
              cases hall2 : (((coeffs.zip is).zipIdx.filter
                  (fun q => q.2 != i)).map (·.1)).all
                  (fun p => (maxContrib st p).isSome) with
              | true => exact absurd hall2 hguardMax
              | false => rfl
            exact lin2_all_false_mem
              (fun p => (maxContrib st p).isSome)
              (((coeffs.zip is).zipIdx.filter
                (fun q => q.2 != i)).map (·.1)) hall
          obtain ⟨p, hpmem, hfalse⟩ := hcontra
          have hmin := hguardMin' p hpmem
          rw [maxContrib_isSome_of_minContrib hmin] at hfalse
          cases hfalse
      · left
        refine hdet.trans ?_
        unfold linDeduceEq
        rw [if_neg (by
          intro hcon
          rw [hcon] at hguardMin
          exact absurd hguardMin (by simp))]

/-! ## The two-case clause truth

Every emitted clause consists solely of order literals on slots the
constraint reads as integers, so each literal is DECIDED at every
solution; the clause then either carries a true literal or ALL its
literals are false — the latter is exactly the kernels' premise
bundle, which contradicts the constraint. -/

/-- A list of decided literals either carries a true one or has all
    of them false (plain induction, no choice). -/
theorem lin2_clause_decided_cases {a : Assignment} : ∀ {qs : Clause},
    (∀ q ∈ qs, ∃ b, q.eval a = some b) →
    (∃ q ∈ qs, q.eval a = some true) ∨
      (∀ q ∈ qs, q.eval a = some false) := by
  intro qs
  induction qs with
  | nil => intro _; exact Or.inr (fun q hq => absurd hq (by cases hq))
  | cons q qs ih =>
      intro hdec
      obtain ⟨b, hb⟩ := hdec q List.mem_cons_self
      cases b with
      | true => exact Or.inl ⟨q, List.mem_cons_self, hb⟩
      | false =>
          rcases ih (fun q2 hq2 =>
            hdec q2 (List.mem_cons_of_mem _ hq2)) with
            ⟨q2, hq2mem, hq2t⟩ | hallfalse
          · exact Or.inl ⟨q2, List.mem_cons_of_mem _ hq2mem, hq2t⟩
          · refine Or.inr ?_
            intro q2 hq2
            rcases List.mem_cons.mp hq2 with rfl | hq2'
            · exact hb
            · exact hallfalse q2 hq2'

/-! ## The four nogood-truth kernels at an arbitrary solution

Each emitted clause carries a true literal at every solution of the
constraint — the single place the two-case disjunctions live; the
safe triple's implied half, the conflict entitlement, and the reason
validity all consume them. -/

/-- The +1-slot min nogood `[x_m ≤ b − lr] ++ minCauses` is true at
    every solution of `Σ cₜxₜ ≤ b` (and of `Σ cₜxₜ = b`). -/
theorem lin2_nogood_le_hi_true {a : Assignment} {st : State} {m : Nat}
    {coeffs : List Int} {is : List Nat} {b lr : Int} {i : Nat}
    {rest : List (Int × Nat)}
    (hmem : ((1, m), i) ∈ (coeffs.zip is).zipIdx)
    (hrest : rest = (((coeffs.zip is).zipIdx.filter
        (fun q => q.2 != i)).map (·.1)))
    (hguard : ∀ p ∈ rest, (minContrib st p).isSome = true)
    (hsum : sumMin st rest = some lr)
    (hreads : ∀ p, p ∈ coeffs.zip is → ∃ x, slotInt a p.2 = some x)
    (hcons : (DomConstraint.linLe coeffs is b).SatisfiedBy a)
    (hlen : coeffs.length = is.length) :
    ∃ q ∈ [posLe m (b - lr)] ++ linCausesMin st rest,
      q.eval a = some true := by
  have hdec : ∀ q ∈ [posLe m (b - lr)] ++ linCausesMin st rest,
      ∃ bv, q.eval a = some bv := by
    intro q hq
    rcases List.mem_append.mp hq with hq' | hq'
    · rw [List.mem_singleton.mp hq']
      have hmem' : (1, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((1, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (1, m) hmem'
      rw [eval_posLe, hxt]
      exact ⟨_, rfl⟩
    · exact lin2_causesMin_eval_some
        (fun p hp => hreads p (by
          rw [hrest] at hp
          exact lin2_others_mem_zip hp)) hq'
  rcases lin2_clause_decided_cases hdec with ⟨q, hqmem, hqtrue⟩ | hallfalse
  · exact ⟨q, hqmem, hqtrue⟩
  · exfalso
    obtain ⟨d, hdot, hdle⟩ := linLe2_views hcons hlen
    exact lin2_absurd_le_hi hmem hrest hguard
      (fun q hq => hallfalse q (List.mem_append.mpr (Or.inr hq)))
      hsum hreads hdot hdle
      (hallfalse _ (List.mem_append.mpr (Or.inl List.mem_cons_self)))

/-- The −1-slot min nogood `[x_m > lr − b − 1] ++ minCauses` is true
    at every solution of `Σ cₜxₜ ≤ b` (and of `Σ cₜxₜ = b`). -/
theorem lin2_nogood_le_lo_true {a : Assignment} {st : State} {m : Nat}
    {coeffs : List Int} {is : List Nat} {b lr : Int} {i : Nat}
    {rest : List (Int × Nat)}
    (hmem : ((-1, m), i) ∈ (coeffs.zip is).zipIdx)
    (hrest : rest = (((coeffs.zip is).zipIdx.filter
        (fun q => q.2 != i)).map (·.1)))
    (hguard : ∀ p ∈ rest, (minContrib st p).isSome = true)
    (hsum : sumMin st rest = some lr)
    (hreads : ∀ p, p ∈ coeffs.zip is → ∃ x, slotInt a p.2 = some x)
    (hcons : (DomConstraint.linLe coeffs is b).SatisfiedBy a)
    (hlen : coeffs.length = is.length) :
    ∃ q ∈ [negLe m (lr - b - 1)] ++ linCausesMin st rest,
      q.eval a = some true := by
  have hdec : ∀ q ∈ [negLe m (lr - b - 1)] ++ linCausesMin st rest,
      ∃ bv, q.eval a = some bv := by
    intro q hq
    rcases List.mem_append.mp hq with hq' | hq'
    · rw [List.mem_singleton.mp hq']
      have hmem' : (-1, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((-1, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (-1, m) hmem'
      rw [eval_negLe, hxt]
      exact ⟨_, rfl⟩
    · exact lin2_causesMin_eval_some
        (fun p hp => hreads p (by
          rw [hrest] at hp
          exact lin2_others_mem_zip hp)) hq'
  rcases lin2_clause_decided_cases hdec with ⟨q, hqmem, hqtrue⟩ | hallfalse
  · exact ⟨q, hqmem, hqtrue⟩
  · exfalso
    obtain ⟨d, hdot, hdle⟩ := linLe2_views hcons hlen
    exact lin2_absurd_le_lo hmem hrest hguard
      (fun q hq => hallfalse q (List.mem_append.mpr (Or.inr hq)))
      hsum hreads hdot hdle
      (hallfalse _ (List.mem_append.mpr (Or.inl List.mem_cons_self)))

/-- The +1-slot max nogood `[x_m > b − hr − 1] ++ maxCauses` is true
    at every solution of `Σ cₜxₜ = b`. -/
theorem lin2_nogood_eq_lo_max_true {a : Assignment} {st : State} {m : Nat}
    {coeffs : List Int} {is : List Nat} {b hr : Int} {i : Nat}
    {rest : List (Int × Nat)}
    (hmem : ((1, m), i) ∈ (coeffs.zip is).zipIdx)
    (hrest : rest = (((coeffs.zip is).zipIdx.filter
        (fun q => q.2 != i)).map (·.1)))
    (hguard : ∀ p ∈ rest, (maxContrib st p).isSome = true)
    (hsum : sumMax st rest = some hr)
    (hreads : ∀ p, p ∈ coeffs.zip is → ∃ x, slotInt a p.2 = some x)
    (hcons : (DomConstraint.linEq coeffs is b).SatisfiedBy a)
    (hlen : coeffs.length = is.length) :
    ∃ q ∈ [negLe m (b - hr - 1)] ++ linCausesMax st rest,
      q.eval a = some true := by
  have hdec : ∀ q ∈ [negLe m (b - hr - 1)] ++ linCausesMax st rest,
      ∃ bv, q.eval a = some bv := by
    intro q hq
    rcases List.mem_append.mp hq with hq' | hq'
    · rw [List.mem_singleton.mp hq']
      have hmem' : (1, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((1, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (1, m) hmem'
      rw [eval_negLe, hxt]
      exact ⟨_, rfl⟩
    · exact lin2_causesMax_eval_some
        (fun p hp => hreads p (by
          rw [hrest] at hp
          exact lin2_others_mem_zip hp)) hq'
  rcases lin2_clause_decided_cases hdec with ⟨q, hqmem, hqtrue⟩ | hallfalse
  · exact ⟨q, hqmem, hqtrue⟩
  · exfalso
    obtain ⟨d, hdot, hdeq⟩ := linEq2_dot hcons hlen
    exact lin2_absurd_eq_lo_max hmem hrest hguard
      (fun q hq => hallfalse q (List.mem_append.mpr (Or.inr hq)))
      hsum hreads hdot hdeq
      (hallfalse _ (List.mem_append.mpr (Or.inl List.mem_cons_self)))

/-- The −1-slot max nogood `[x_m ≤ hr − b] ++ maxCauses` is true at
    every solution of `Σ cₜxₜ = b`. -/
theorem lin2_nogood_eq_hi_max_true {a : Assignment} {st : State} {m : Nat}
    {coeffs : List Int} {is : List Nat} {b hr : Int} {i : Nat}
    {rest : List (Int × Nat)}
    (hmem : ((-1, m), i) ∈ (coeffs.zip is).zipIdx)
    (hrest : rest = (((coeffs.zip is).zipIdx.filter
        (fun q => q.2 != i)).map (·.1)))
    (hguard : ∀ p ∈ rest, (maxContrib st p).isSome = true)
    (hsum : sumMax st rest = some hr)
    (hreads : ∀ p, p ∈ coeffs.zip is → ∃ x, slotInt a p.2 = some x)
    (hcons : (DomConstraint.linEq coeffs is b).SatisfiedBy a)
    (hlen : coeffs.length = is.length) :
    ∃ q ∈ [posLe m (hr - b)] ++ linCausesMax st rest,
      q.eval a = some true := by
  have hdec : ∀ q ∈ [posLe m (hr - b)] ++ linCausesMax st rest,
      ∃ bv, q.eval a = some bv := by
    intro q hq
    rcases List.mem_append.mp hq with hq' | hq'
    · rw [List.mem_singleton.mp hq']
      have hmem' : (-1, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((-1, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (-1, m) hmem'
      rw [eval_posLe, hxt]
      exact ⟨_, rfl⟩
    · exact lin2_causesMax_eval_some
        (fun p hp => hreads p (by
          rw [hrest] at hp
          exact lin2_others_mem_zip hp)) hq'
  rcases lin2_clause_decided_cases hdec with ⟨q, hqmem, hqtrue⟩ | hallfalse
  · exact ⟨q, hqmem, hqtrue⟩
  · exfalso
    obtain ⟨d, hdot, hdeq⟩ := linEq2_dot hcons hlen
    exact lin2_absurd_eq_hi_max hmem hrest hguard
      (fun q hq => hallfalse q (List.mem_append.mpr (Or.inr hq)))
      hsum hreads hdot hdeq
      (hallfalse _ (List.mem_append.mpr (Or.inl List.mem_cons_self)))

/-! ### The four general-coefficient nogood-truth kernels -/

/-- The general-c nogood `[x_m ≤ (b − lr)/c] ++ minCauses` is true at
    every solution of `Σ cₜxₜ ≤ b` (and of `Σ cₜxₜ = b`) for
    c > 0. -/
theorem lin2_nogood_gen_le_hi_true {a : Assignment} {st : State} {m : Nat}
    {coeffs : List Int} {is : List Nat} {b lr c : Int} {i : Nat}
    {rest : List (Int × Nat)}
    (hmem : ((c, m), i) ∈ (coeffs.zip is).zipIdx)
    (hc : 0 < c)
    (hrest : rest = (((coeffs.zip is).zipIdx.filter
        (fun q => q.2 != i)).map (·.1)))
    (hguard : ∀ p ∈ rest, (minContrib st p).isSome = true)
    (hsum : sumMin st rest = some lr)
    (hreads : ∀ p, p ∈ coeffs.zip is → ∃ x, slotInt a p.2 = some x)
    (hcons : (DomConstraint.linLe coeffs is b).SatisfiedBy a)
    (hlen : coeffs.length = is.length) :
    ∃ q ∈ [posLe m ((b - lr) / c)] ++ linCausesMin st rest,
      q.eval a = some true := by
  have hdec : ∀ q ∈ [posLe m ((b - lr) / c)] ++ linCausesMin st rest,
      ∃ bv, q.eval a = some bv := by
    intro q hq
    rcases List.mem_append.mp hq with hq' | hq'
    · rw [List.mem_singleton.mp hq']
      have hmem' : (c, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((c, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (c, m) hmem'
      rw [eval_posLe, hxt]
      exact ⟨_, rfl⟩
    · exact lin2_causesMin_eval_some
        (fun p hp => hreads p (by
          rw [hrest] at hp
          exact lin2_others_mem_zip hp)) hq'
  rcases lin2_clause_decided_cases hdec with ⟨q, hqmem, hqtrue⟩ | hallfalse
  · exact ⟨q, hqmem, hqtrue⟩
  · exfalso
    obtain ⟨d, hdot, hdle⟩ := linLe2_views hcons hlen
    exact lin2_absurd_gen_le_hi hmem hc hrest hguard
      (fun q hq => hallfalse q (List.mem_append.mpr (Or.inr hq)))
      hsum hreads hdot hdle
      (hallfalse _ (List.mem_append.mpr (Or.inl List.mem_cons_self)))

/-- The general-c nogood `[x_m > −(b − lr)/(−c) − 1] ++ minCauses`
    is true at every solution of `Σ cₜxₜ ≤ b` (and of
    `Σ cₜxₜ = b`) for c < 0. -/
theorem lin2_nogood_gen_le_lo_true {a : Assignment} {st : State} {m : Nat}
    {coeffs : List Int} {is : List Nat} {b lr c : Int} {i : Nat}
    {rest : List (Int × Nat)}
    (hmem : ((c, m), i) ∈ (coeffs.zip is).zipIdx)
    (hc : c < 0)
    (hrest : rest = (((coeffs.zip is).zipIdx.filter
        (fun q => q.2 != i)).map (·.1)))
    (hguard : ∀ p ∈ rest, (minContrib st p).isSome = true)
    (hsum : sumMin st rest = some lr)
    (hreads : ∀ p, p ∈ coeffs.zip is → ∃ x, slotInt a p.2 = some x)
    (hcons : (DomConstraint.linLe coeffs is b).SatisfiedBy a)
    (hlen : coeffs.length = is.length) :
    ∃ q ∈ [negLe m (-((b - lr) / (-c)) - 1)] ++ linCausesMin st rest,
      q.eval a = some true := by
  have hdec : ∀ q ∈ [negLe m (-((b - lr) / (-c)) - 1)] ++
      linCausesMin st rest,
      ∃ bv, q.eval a = some bv := by
    intro q hq
    rcases List.mem_append.mp hq with hq' | hq'
    · rw [List.mem_singleton.mp hq']
      have hmem' : (c, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((c, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (c, m) hmem'
      rw [eval_negLe, hxt]
      exact ⟨_, rfl⟩
    · exact lin2_causesMin_eval_some
        (fun p hp => hreads p (by
          rw [hrest] at hp
          exact lin2_others_mem_zip hp)) hq'
  rcases lin2_clause_decided_cases hdec with ⟨q, hqmem, hqtrue⟩ | hallfalse
  · exact ⟨q, hqmem, hqtrue⟩
  · exfalso
    obtain ⟨d, hdot, hdle⟩ := linLe2_views hcons hlen
    exact lin2_absurd_gen_le_lo hmem hc hrest hguard
      (fun q hq => hallfalse q (List.mem_append.mpr (Or.inr hq)))
      hsum hreads hdot hdle
      (hallfalse _ (List.mem_append.mpr (Or.inl List.mem_cons_self)))

/-- The general-c nogood `[x_m > −(hr − b)/c − 1] ++ maxCauses` is
    true at every solution of `Σ cₜxₜ = b` for c > 0. -/
theorem lin2_nogood_gen_eq_lo_max_true {a : Assignment} {st : State}
    {m : Nat}
    {coeffs : List Int} {is : List Nat} {b hr c : Int} {i : Nat}
    {rest : List (Int × Nat)}
    (hmem : ((c, m), i) ∈ (coeffs.zip is).zipIdx)
    (hc : 0 < c)
    (hrest : rest = (((coeffs.zip is).zipIdx.filter
        (fun q => q.2 != i)).map (·.1)))
    (hguard : ∀ p ∈ rest, (maxContrib st p).isSome = true)
    (hsum : sumMax st rest = some hr)
    (hreads : ∀ p, p ∈ coeffs.zip is → ∃ x, slotInt a p.2 = some x)
    (hcons : (DomConstraint.linEq coeffs is b).SatisfiedBy a)
    (hlen : coeffs.length = is.length) :
    ∃ q ∈ [negLe m (-((hr - b) / c) - 1)] ++ linCausesMax st rest,
      q.eval a = some true := by
  have hdec : ∀ q ∈ [negLe m (-((hr - b) / c) - 1)] ++
      linCausesMax st rest,
      ∃ bv, q.eval a = some bv := by
    intro q hq
    rcases List.mem_append.mp hq with hq' | hq'
    · rw [List.mem_singleton.mp hq']
      have hmem' : (c, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((c, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (c, m) hmem'
      rw [eval_negLe, hxt]
      exact ⟨_, rfl⟩
    · exact lin2_causesMax_eval_some
        (fun p hp => hreads p (by
          rw [hrest] at hp
          exact lin2_others_mem_zip hp)) hq'
  rcases lin2_clause_decided_cases hdec with ⟨q, hqmem, hqtrue⟩ | hallfalse
  · exact ⟨q, hqmem, hqtrue⟩
  · exfalso
    obtain ⟨d, hdot, hdeq⟩ := linEq2_dot hcons hlen
    exact lin2_absurd_gen_eq_lo_max hmem hc hrest hguard
      (fun q hq => hallfalse q (List.mem_append.mpr (Or.inr hq)))
      hsum hreads hdot hdeq
      (hallfalse _ (List.mem_append.mpr (Or.inl List.mem_cons_self)))

/-- The general-c nogood `[x_m ≤ (hr − b)/(−c)] ++ maxCauses` is true
    at every solution of `Σ cₜxₜ = b` for c < 0. -/
theorem lin2_nogood_gen_eq_hi_max_true {a : Assignment} {st : State}
    {m : Nat}
    {coeffs : List Int} {is : List Nat} {b hr c : Int} {i : Nat}
    {rest : List (Int × Nat)}
    (hmem : ((c, m), i) ∈ (coeffs.zip is).zipIdx)
    (hc : c < 0)
    (hrest : rest = (((coeffs.zip is).zipIdx.filter
        (fun q => q.2 != i)).map (·.1)))
    (hguard : ∀ p ∈ rest, (maxContrib st p).isSome = true)
    (hsum : sumMax st rest = some hr)
    (hreads : ∀ p, p ∈ coeffs.zip is → ∃ x, slotInt a p.2 = some x)
    (hcons : (DomConstraint.linEq coeffs is b).SatisfiedBy a)
    (hlen : coeffs.length = is.length) :
    ∃ q ∈ [posLe m ((hr - b) / (-c))] ++ linCausesMax st rest,
      q.eval a = some true := by
  have hdec : ∀ q ∈ [posLe m ((hr - b) / (-c))] ++ linCausesMax st rest,
      ∃ bv, q.eval a = some bv := by
    intro q hq
    rcases List.mem_append.mp hq with hq' | hq'
    · rw [List.mem_singleton.mp hq']
      have hmem' : (c, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((c, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (c, m) hmem'
      rw [eval_posLe, hxt]
      exact ⟨_, rfl⟩
    · exact lin2_causesMax_eval_some
        (fun p hp => hreads p (by
          rw [hrest] at hp
          exact lin2_others_mem_zip hp)) hq'
  rcases lin2_clause_decided_cases hdec with ⟨q, hqmem, hqtrue⟩ | hallfalse
  · exact ⟨q, hqmem, hqtrue⟩
  · exfalso
    obtain ⟨d, hdot, hdeq⟩ := linEq2_dot hcons hlen
    exact lin2_absurd_gen_eq_hi_max hmem hc hrest hguard
      (fun q hq => hallfalse q (List.mem_append.mpr (Or.inr hq)))
      hsum hreads hdot hdeq
      (hallfalse _ (List.mem_append.mpr (Or.inl List.mem_cons_self)))

/-! ## Fit-based cause falsity

At a FITTING solution every cause literal is FALSE: each cause is the
negation of a domain bound, and a fitting assignment's slot views lie
within the domain extrema the bound came from. This is what promotes
the nogood-truth disjunction to HEAD-truth for the implied half of
the safe triple, and to full falsity for the conflict half. -/

/-- Every min-cause is false at a fitting assignment that reads all
    the rest slots. -/
theorem lin2_causesMin_false_of_fits {st : State} {a : Assignment}
    {rest : List (Int × Nat)}
    (hfit : Core.Assignment.Fits st.domains a)
    (hreads : ∀ p ∈ rest, ∃ x, slotInt a p.2 = some x) :
    ∀ q ∈ linCausesMin st rest, q.eval a = some false := by
  intro q hq
  rw [linCausesMin, List.mem_filterMap] at hq
  obtain ⟨p, hpmem, hpq⟩ := hq
  obtain ⟨xt, hxt⟩ := hreads p hpmem
  rcases lin2_causeMin_inv hpq with ⟨mn, hmn, hq2, _⟩ | ⟨mx, hmx, hq2, _⟩
  · subst hq2
    have hbound : mn ≤ xt := fits_min_bound hfit hmn hxt
    rw [eval_posLe, hxt]
    have hdec : decide (xt ≤ mn - 1) = false :=
      decide_eq_false (by omega)
    show Option.map (fun i => decide (i ≤ mn - 1)) (some xt) =
      some false
    rw [show Option.map (fun i => decide (i ≤ mn - 1)) (some xt) =
      some (decide (xt ≤ mn - 1)) from rfl, hdec]
  · subst hq2
    have hbound : xt ≤ mx := fits_max_bound hfit hmx hxt
    rw [eval_negLe, hxt]
    have hdec : (!decide (xt ≤ mx)) = false := by
      have htrue : decide (xt ≤ mx) = true := decide_eq_true (by omega)
      rw [htrue]
      rfl
    show Option.map (fun i => !(decide (i ≤ mx))) (some xt) =
      some false
    rw [show Option.map (fun i => !(decide (i ≤ mx))) (some xt) =
      some (!(decide (xt ≤ mx))) from rfl, hdec]

/-- Every max-cause is false at a fitting assignment that reads all
    the rest slots. -/
theorem lin2_causesMax_false_of_fits {st : State} {a : Assignment}
    {rest : List (Int × Nat)}
    (hfit : Core.Assignment.Fits st.domains a)
    (hreads : ∀ p ∈ rest, ∃ x, slotInt a p.2 = some x) :
    ∀ q ∈ linCausesMax st rest, q.eval a = some false := by
  intro q hq
  rw [linCausesMax, List.mem_filterMap] at hq
  obtain ⟨p, hpmem, hpq⟩ := hq
  obtain ⟨xt, hxt⟩ := hreads p hpmem
  rcases lin2_causeMax_inv hpq with ⟨mx, hmx, hq2, _⟩ | ⟨mn, hmn, hq2, _⟩
  · subst hq2
    have hbound : xt ≤ mx := fits_max_bound hfit hmx hxt
    rw [eval_negLe, hxt]
    have hdec : (!decide (xt ≤ mx)) = false := by
      have htrue : decide (xt ≤ mx) = true := decide_eq_true (by omega)
      rw [htrue]
      rfl
    show Option.map (fun i => !(decide (i ≤ mx))) (some xt) =
      some false
    rw [show Option.map (fun i => !(decide (i ≤ mx))) (some xt) =
      some (!(decide (xt ≤ mx))) from rfl, hdec]
  · subst hq2
    have hbound : mn ≤ xt := fits_min_bound hfit hmn hxt
    rw [eval_posLe, hxt]
    have hdec : decide (xt ≤ mn - 1) = false :=
      decide_eq_false (by omega)
    show Option.map (fun i => decide (i ≤ mn - 1)) (some xt) =
      some false
    rw [show Option.map (fun i => decide (i ≤ mn - 1)) (some xt) =
      some (decide (xt ≤ mn - 1)) from rfl, hdec]

/-! ## propLinLe2 soundness: the safe triple at fitting solutions -/

/-- The propagator of a `linLe coeffs is b` constraint (the corrected
    propagator): implied-literal soundness, conflict soundness, and
    conflict entitlement, at every state. -/
theorem propLinLe2_safe (st : State) (coeffs : List Int) (is : List Nat)
    (b : Int) (hlen : coeffs.length = is.length) :
    (∀ l r, propLinLe2 st coeffs is b = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.linLe coeffs is b).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ c, propLinLe2 st coeffs is b = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.linLe coeffs is b).SatisfiedBy a → False) ∧
    (∀ c, propLinLe2 st coeffs is b = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.linLe coeffs is b).SatisfiedBy a →
        ∃ l ∈ c, l.eval a = some true) := by
  refine ⟨?_, ?_, ?_⟩
  · -- implied-literal soundness: the head is true at every fitting
    -- solution (the causes are the domain-bound negations, false at
    -- every fitting solution; the kernel then forces the head)
    intro l r hrun a hfit hcons
    rcases propLinLe2_emission_inv hrun with hstable |
      ⟨m, i, rest, lr, hmem, hrest, hguard, hsum, hnarrow⟩ |
      ⟨m, i, rest, lr, hmem, hrest, hguard, hsum, hnarrow⟩ |
      ⟨m, i, rest, lr, c, hmem, hpos, hrest, hguard, hsum, hnarrow⟩ |
      ⟨m, i, rest, lr, c, hmem, hneg, hrest, hguard, hsum, hnarrow⟩
    · exact absurd hstable (by intro hc; cases hc)
    · -- the +1 slot: the implied head is posLe m (b − lr)
      obtain ⟨hl, hcl⟩ := narrowHi_implied_inv hnarrow.symm
      subst hl
      have hreads := linLe2_reads_int hcons hlen
      have hreadsRest : ∀ p ∈ rest, ∃ x, slotInt a p.2 = some x := by
        intro p hp
        rw [hrest] at hp
        exact hreads p (lin2_others_mem_zip hp)
      have hcauses := lin2_causesMin_false_of_fits hfit hreadsRest
      have hmem' : (1, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((1, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (1, m) hmem'
      rw [eval_posLe, hxt]
      cases hbv : decide (xt ≤ b - lr) with
      | true =>
          show Option.map (fun i => decide (i ≤ b - lr)) (some xt) =
            some true
          rw [show Option.map (fun i => decide (i ≤ b - lr)) (some xt) =
            some (decide (xt ≤ b - lr)) from rfl, hbv]
      | false =>
          exfalso
          have hhead : (posLe m (b - lr)).eval a = some false := by
            rw [eval_posLe, hxt]
            show Option.map (fun i => decide (i ≤ b - lr)) (some xt) =
              some false
            rw [show Option.map (fun i => decide (i ≤ b - lr))
                (some xt) = some (decide (xt ≤ b - lr)) from rfl, hbv]
          obtain ⟨d, hdot, hdle⟩ := linLe2_views hcons hlen
          exact lin2_absurd_le_hi hmem hrest hguard hcauses hsum
            hreads hdot hdle hhead
    · -- the −1 slot: the implied head is negLe m (lr − b − 1)
      obtain ⟨hl, hcl⟩ := narrowLo_implied_inv hnarrow.symm
      subst hl
      have hreads := linLe2_reads_int hcons hlen
      have hreadsRest : ∀ p ∈ rest, ∃ x, slotInt a p.2 = some x := by
        intro p hp
        rw [hrest] at hp
        exact hreads p (lin2_others_mem_zip hp)
      have hcauses := lin2_causesMin_false_of_fits hfit hreadsRest
      have hmem' : (-1, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((-1, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (-1, m) hmem'
      rw [eval_negLe, hxt]
      cases hbv : (!(decide (xt ≤ lr - b - 1))) with
      | true =>
          show Option.map (fun i => !(decide (i ≤ lr - b - 1)))
              (some xt) = some true
          rw [show Option.map (fun i => !(decide (i ≤ lr - b - 1)))
              (some xt) = some (!(decide (xt ≤ lr - b - 1))) from rfl,
            hbv]
      | false =>
          exfalso
          have hhead : (negLe m (lr - b - 1)).eval a = some false := by
            rw [eval_negLe, hxt]
            show Option.map (fun i => !(decide (i ≤ lr - b - 1)))
                (some xt) = some false
            rw [show Option.map (fun i => !(decide (i ≤ lr - b - 1)))
                (some xt) = some (!(decide (xt ≤ lr - b - 1))) from rfl,
              hbv]
          obtain ⟨d, hdot, hdle⟩ := linLe2_views hcons hlen
          exact lin2_absurd_le_lo hmem hrest hguard hcauses hsum
            hreads hdot hdle hhead
    · -- the general c > 0 slot: the implied head is
      -- posLe m ((b − lr)/c)
      obtain ⟨hl, hcl⟩ := narrowHi_implied_inv hnarrow.symm
      subst hl
      have hreads := linLe2_reads_int hcons hlen
      have hreadsRest : ∀ p ∈ rest, ∃ x, slotInt a p.2 = some x := by
        intro p hp
        rw [hrest] at hp
        exact hreads p (lin2_others_mem_zip hp)
      have hcauses := lin2_causesMin_false_of_fits hfit hreadsRest
      have hmem' : (c, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((c, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (c, m) hmem'
      rw [eval_posLe, hxt]
      cases hbv : decide (xt ≤ (b - lr) / c) with
      | true =>
          show Option.map (fun i => decide (i ≤ (b - lr) / c))
              (some xt) = some true
          rw [show Option.map (fun i => decide (i ≤ (b - lr) / c))
              (some xt) = some (decide (xt ≤ (b - lr) / c)) from rfl,
            hbv]
      | false =>
          exfalso
          have hhead : (posLe m ((b - lr) / c)).eval a = some false := by
            rw [eval_posLe, hxt]
            show Option.map (fun i => decide (i ≤ (b - lr) / c))
                (some xt) = some false
            rw [show Option.map (fun i => decide (i ≤ (b - lr) / c))
                (some xt) = some (decide (xt ≤ (b - lr) / c)) from rfl,
              hbv]
          obtain ⟨d, hdot, hdle⟩ := linLe2_views hcons hlen
          exact lin2_absurd_gen_le_hi hmem hpos hrest hguard hcauses
            hsum hreads hdot hdle hhead
    · -- the general c < 0 slot: the implied head is
      -- negLe m (−(b − lr)/(−c) − 1)
      obtain ⟨hl, hcl⟩ := narrowLo_implied_inv hnarrow.symm
      subst hl
      have hreads := linLe2_reads_int hcons hlen
      have hreadsRest : ∀ p ∈ rest, ∃ x, slotInt a p.2 = some x := by
        intro p hp
        rw [hrest] at hp
        exact hreads p (lin2_others_mem_zip hp)
      have hcauses := lin2_causesMin_false_of_fits hfit hreadsRest
      have hmem' : (c, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((c, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (c, m) hmem'
      rw [eval_negLe, hxt]
      cases hbv : (!(decide (xt ≤ -((b - lr) / (-c)) - 1))) with
      | true =>
          show Option.map (fun i =>
              !(decide (i ≤ -((b - lr) / (-c)) - 1)))
              (some xt) = some true
          rw [show Option.map (fun i =>
              !(decide (i ≤ -((b - lr) / (-c)) - 1)))
              (some xt) =
              some (!(decide (xt ≤ -((b - lr) / (-c)) - 1))) from rfl,
            hbv]
      | false =>
          exfalso
          have hhead : (negLe m (-((b - lr) / (-c)) - 1)).eval a
              = some false := by
            rw [eval_negLe, hxt]
            show Option.map (fun i =>
                !(decide (i ≤ -((b - lr) / (-c)) - 1)))
                (some xt) = some false
            rw [show Option.map (fun i =>
                !(decide (i ≤ -((b - lr) / (-c)) - 1)))
                (some xt) =
                some (!(decide (xt ≤ -((b - lr) / (-c)) - 1))) from rfl,
              hbv]
          obtain ⟨d, hdot, hdle⟩ := linLe2_views hcons hlen
          exact lin2_absurd_gen_le_lo hmem hneg hrest hguard hcauses
            hsum hreads hdot hdle hhead
  · -- conflict exclusion: the conflict clause is a nogood; its
    -- head is falsified by the conflict inversion's domain bound and
    -- its causes by the fit — the kernel then contradicts the
    -- constraint at the fitting solution
    intro c hrun a hfit hcons
    rcases propLinLe2_emission_inv hrun with hstable |
      ⟨m, i, rest, lr, hmem, hrest, hguard, hsum, hnarrow⟩ |
      ⟨m, i, rest, lr, hmem, hrest, hguard, hsum, hnarrow⟩ |
      ⟨m, i, rest, lr, c, hmem, hpos, hrest, hguard, hsum, hnarrow⟩ |
      ⟨m, i, rest, lr, c, hmem, hneg, hrest, hguard, hsum, hnarrow⟩
    · exact absurd hstable (by intro hc; cases hc)
    · -- the +1 slot's narrowHi conflict arm
      obtain ⟨mn, mx, hmn, hmx, hgt, hcc⟩ :=
        narrowHi_conflict_inv hnarrow.symm
      have hreads := linLe2_reads_int hcons hlen
      have hmem' : (1, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((1, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (1, m) hmem'
      have hmnt : mn ≤ xt := fits_min_bound hfit hmn hxt
      have hhead : (posLe m (b - lr)).eval a = some false := by
        rw [eval_posLe, hxt]
        show Option.map (fun i => decide (i ≤ b - lr)) (some xt) =
          some false
        rw [show Option.map (fun i => decide (i ≤ b - lr))
            (some xt) = some (decide (xt ≤ b - lr)) from rfl]
        have hdec : decide (xt ≤ b - lr) = false :=
          decide_eq_false (by omega)
        rw [hdec]
      have hreadsRest : ∀ p ∈ rest, ∃ x, slotInt a p.2 = some x := by
        intro p hp
        rw [hrest] at hp
        exact hreads p (lin2_others_mem_zip hp)
      have hcauses := lin2_causesMin_false_of_fits hfit hreadsRest
      obtain ⟨d, hdot, hdle⟩ := linLe2_views hcons hlen
      exact lin2_absurd_le_hi hmem hrest hguard hcauses hsum
        hreads hdot hdle hhead
    · -- the −1 slot's narrowLo conflict arm
      obtain ⟨mn, mx, hmn, hmx, hlt, hcc⟩ :=
        narrowLo_conflict_inv hnarrow.symm
      have hreads := linLe2_reads_int hcons hlen
      have hmem' : (-1, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((-1, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (-1, m) hmem'
      have hmxt : xt ≤ mx := fits_max_bound hfit hmx hxt
      have hhead : (negLe m (lr - b - 1)).eval a = some false := by
        rw [eval_negLe, hxt]
        show Option.map (fun i => !(decide (i ≤ lr - b - 1)))
            (some xt) = some false
        rw [show Option.map (fun i => !(decide (i ≤ lr - b - 1)))
            (some xt) = some (!(decide (xt ≤ lr - b - 1))) from rfl]
        have hdec : (!(decide (xt ≤ lr - b - 1))) = false := by
          have htrue : decide (xt ≤ lr - b - 1) = true :=
            decide_eq_true (by omega)
          rw [htrue]
          rfl
        rw [hdec]
      have hreadsRest : ∀ p ∈ rest, ∃ x, slotInt a p.2 = some x := by
        intro p hp
        rw [hrest] at hp
        exact hreads p (lin2_others_mem_zip hp)
      have hcauses := lin2_causesMin_false_of_fits hfit hreadsRest
      obtain ⟨d, hdot, hdle⟩ := linLe2_views hcons hlen
      exact lin2_absurd_le_lo hmem hrest hguard hcauses hsum
        hreads hdot hdle hhead
    · -- the general c > 0 slot's narrowHi conflict arm
      obtain ⟨mn, mx, hmn, hmx, hgt, hcc⟩ :=
        narrowHi_conflict_inv hnarrow.symm
      have hreads := linLe2_reads_int hcons hlen
      have hmem' : (c, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((c, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (c, m) hmem'
      have hmnt : mn ≤ xt := fits_min_bound hfit hmn hxt
      have hhead : (posLe m ((b - lr) / c)).eval a = some false := by
        rw [eval_posLe, hxt]
        show Option.map (fun i => decide (i ≤ (b - lr) / c))
            (some xt) = some false
        rw [show Option.map (fun i => decide (i ≤ (b - lr) / c))
            (some xt) = some (decide (xt ≤ (b - lr) / c)) from rfl]
        have hdec : decide (xt ≤ (b - lr) / c) = false :=
          decide_eq_false (by omega)
        rw [hdec]
      have hreadsRest : ∀ p ∈ rest, ∃ x, slotInt a p.2 = some x := by
        intro p hp
        rw [hrest] at hp
        exact hreads p (lin2_others_mem_zip hp)
      have hcauses := lin2_causesMin_false_of_fits hfit hreadsRest
      obtain ⟨d, hdot, hdle⟩ := linLe2_views hcons hlen
      exact lin2_absurd_gen_le_hi hmem hpos hrest hguard hcauses hsum
        hreads hdot hdle hhead
    · -- the general c < 0 slot's narrowLo conflict arm
      obtain ⟨mn, mx, hmn, hmx, hlt, hcc⟩ :=
        narrowLo_conflict_inv hnarrow.symm
      have hreads := linLe2_reads_int hcons hlen
      have hmem' : (c, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((c, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (c, m) hmem'
      have hmxt : xt ≤ mx := fits_max_bound hfit hmx hxt
      have hhead : (negLe m (-((b - lr) / (-c)) - 1)).eval a
          = some false := by
        rw [eval_negLe, hxt]
        show Option.map (fun i =>
            !(decide (i ≤ -((b - lr) / (-c)) - 1)))
            (some xt) = some false
        rw [show Option.map (fun i =>
            !(decide (i ≤ -((b - lr) / (-c)) - 1)))
            (some xt) =
            some (!(decide (xt ≤ -((b - lr) / (-c)) - 1))) from rfl]
        have hdec : (!(decide (xt ≤ -((b - lr) / (-c)) - 1))) = false := by
          have htrue : decide (xt ≤ -((b - lr) / (-c)) - 1) = true :=
            decide_eq_true (by omega)
          rw [htrue]
          rfl
        rw [hdec]
      have hreadsRest : ∀ p ∈ rest, ∃ x, slotInt a p.2 = some x := by
        intro p hp
        rw [hrest] at hp
        exact hreads p (lin2_others_mem_zip hp)
      have hcauses := lin2_causesMin_false_of_fits hfit hreadsRest
      obtain ⟨d, hdot, hdle⟩ := linLe2_views hcons hlen
      exact lin2_absurd_gen_le_lo hmem hneg hrest hguard hcauses hsum
        hreads hdot hdle hhead
  · -- conflict entitlement: VACUOUS — the second conjunct's
    -- exclusion makes the fitting+satisfied hypotheses contradictory
    intro c hrun a hfit hcons
    have hexcl : False := by
      rcases propLinLe2_emission_inv hrun with hstable |
        ⟨m, i, rest, lr, hmem, hrest, hguard, hsum, hnarrow⟩ |
        ⟨m, i, rest, lr, hmem, hrest, hguard, hsum, hnarrow⟩ |
        ⟨m, i, rest, lr, c, hmem, hpos, hrest, hguard, hsum, hnarrow⟩ |
        ⟨m, i, rest, lr, c, hmem, hneg, hrest, hguard, hsum, hnarrow⟩
      · exact absurd hstable (by intro hc; cases hc)
      · -- the conflict's exclusion at this arm (same argument as the
        -- second conjunct)
        obtain ⟨mn, mx, hmn, hmx, hgt, hcc⟩ :=
          narrowHi_conflict_inv hnarrow.symm
        have hreads := linLe2_reads_int hcons hlen
        have hmem' : (1, m) ∈ coeffs.zip is :=
          lin2_mem_zip_of_zipIdx _ 0 ((1, m), i) hmem
        obtain ⟨xt, hxt⟩ := hreads (1, m) hmem'
        have hmnt : mn ≤ xt := fits_min_bound hfit hmn hxt
        have hhead : (posLe m (b - lr)).eval a = some false := by
          rw [eval_posLe, hxt]
          show Option.map (fun i => decide (i ≤ b - lr)) (some xt) =
            some false
          rw [show Option.map (fun i => decide (i ≤ b - lr))
              (some xt) = some (decide (xt ≤ b - lr)) from rfl]
          have hdec : decide (xt ≤ b - lr) = false :=
            decide_eq_false (by omega)
          rw [hdec]
        have hreadsRest : ∀ p ∈ rest, ∃ x, slotInt a p.2 = some x := by
          intro p hp
          rw [hrest] at hp
          exact hreads p (lin2_others_mem_zip hp)
        have hcauses := lin2_causesMin_false_of_fits hfit hreadsRest
        obtain ⟨d, hdot, hdle⟩ := linLe2_views hcons hlen
        exact lin2_absurd_le_hi hmem hrest hguard hcauses hsum
          hreads hdot hdle hhead
      · obtain ⟨mn, mx, hmn, hmx, hlt, hcc⟩ :=
          narrowLo_conflict_inv hnarrow.symm
        have hreads := linLe2_reads_int hcons hlen
        have hmem' : (-1, m) ∈ coeffs.zip is :=
          lin2_mem_zip_of_zipIdx _ 0 ((-1, m), i) hmem
        obtain ⟨xt, hxt⟩ := hreads (-1, m) hmem'
        have hmxt : xt ≤ mx := fits_max_bound hfit hmx hxt
        have hhead : (negLe m (lr - b - 1)).eval a = some false := by
          rw [eval_negLe, hxt]
          show Option.map (fun i => !(decide (i ≤ lr - b - 1)))
              (some xt) = some false
          rw [show Option.map (fun i => !(decide (i ≤ lr - b - 1)))
              (some xt) = some (!(decide (xt ≤ lr - b - 1))) from rfl]
          have hdec : (!(decide (xt ≤ lr - b - 1))) = false := by
            have htrue : decide (xt ≤ lr - b - 1) = true :=
              decide_eq_true (by omega)
            rw [htrue]
            rfl
          rw [hdec]
        have hreadsRest : ∀ p ∈ rest, ∃ x, slotInt a p.2 = some x := by
          intro p hp
          rw [hrest] at hp
          exact hreads p (lin2_others_mem_zip hp)
        have hcauses := lin2_causesMin_false_of_fits hfit hreadsRest
        obtain ⟨d, hdot, hdle⟩ := linLe2_views hcons hlen
        exact lin2_absurd_le_lo hmem hrest hguard hcauses hsum
          hreads hdot hdle hhead
      · -- the general c > 0 arm's conflict exclusion
        obtain ⟨mn, mx, hmn, hmx, hgt, hcc⟩ :=
          narrowHi_conflict_inv hnarrow.symm
        have hreads := linLe2_reads_int hcons hlen
        have hmem' : (c, m) ∈ coeffs.zip is :=
          lin2_mem_zip_of_zipIdx _ 0 ((c, m), i) hmem
        obtain ⟨xt, hxt⟩ := hreads (c, m) hmem'
        have hmnt : mn ≤ xt := fits_min_bound hfit hmn hxt
        have hhead : (posLe m ((b - lr) / c)).eval a = some false := by
          rw [eval_posLe, hxt]
          show Option.map (fun i => decide (i ≤ (b - lr) / c))
              (some xt) = some false
          rw [show Option.map (fun i => decide (i ≤ (b - lr) / c))
              (some xt) = some (decide (xt ≤ (b - lr) / c)) from rfl]
          have hdec : decide (xt ≤ (b - lr) / c) = false :=
            decide_eq_false (by omega)
          rw [hdec]
        have hreadsRest : ∀ p ∈ rest, ∃ x, slotInt a p.2 = some x := by
          intro p hp
          rw [hrest] at hp
          exact hreads p (lin2_others_mem_zip hp)
        have hcauses := lin2_causesMin_false_of_fits hfit hreadsRest
        obtain ⟨d, hdot, hdle⟩ := linLe2_views hcons hlen
        exact lin2_absurd_gen_le_hi hmem hpos hrest hguard hcauses hsum
          hreads hdot hdle hhead
      · -- the general c < 0 arm's conflict exclusion
        obtain ⟨mn, mx, hmn, hmx, hlt, hcc⟩ :=
          narrowLo_conflict_inv hnarrow.symm
        have hreads := linLe2_reads_int hcons hlen
        have hmem' : (c, m) ∈ coeffs.zip is :=
          lin2_mem_zip_of_zipIdx _ 0 ((c, m), i) hmem
        obtain ⟨xt, hxt⟩ := hreads (c, m) hmem'
        have hmxt : xt ≤ mx := fits_max_bound hfit hmx hxt
        have hhead : (negLe m (-((b - lr) / (-c)) - 1)).eval a
            = some false := by
          rw [eval_negLe, hxt]
          show Option.map (fun i =>
              !(decide (i ≤ -((b - lr) / (-c)) - 1)))
              (some xt) = some false
          rw [show Option.map (fun i =>
              !(decide (i ≤ -((b - lr) / (-c)) - 1)))
              (some xt) =
              some (!(decide (xt ≤ -((b - lr) / (-c)) - 1))) from rfl]
          have hdec : (!(decide (xt ≤ -((b - lr) / (-c)) - 1))) = false := by
            have htrue : decide (xt ≤ -((b - lr) / (-c)) - 1) = true :=
              decide_eq_true (by omega)
            rw [htrue]
            rfl
          rw [hdec]
        have hreadsRest : ∀ p ∈ rest, ∃ x, slotInt a p.2 = some x := by
          intro p hp
          rw [hrest] at hp
          exact hreads p (lin2_others_mem_zip hp)
        have hcauses := lin2_causesMin_false_of_fits hfit hreadsRest
        obtain ⟨d, hdot, hdle⟩ := linLe2_views hcons hlen
        exact lin2_absurd_gen_le_lo hmem hneg hrest hguard hcauses hsum
          hreads hdot hdle hhead
    exact absurd hexcl (fun h => h)

/-! ## The linEq-to-linLe satisfaction bridge

The two ≤-shaped eq arms (eqHiMin over a +1 slot, eqLoMin over a −1
slot) emit exactly the nogoods the le propagator emits, and the le
nogood-truth kernels apply: `d = b` implies `d ≤ b`. -/

/-- A satisfying assignment of `Σ cₜxₜ = b` also satisfies
    `Σ cₜxₜ ≤ b`. -/
theorem linEq_sat_le {coeffs : List Int} {is : List Nat} {b : Int}
    {a : Assignment}
    (hcons : (DomConstraint.linEq coeffs is b).SatisfiedBy a) :
    (DomConstraint.linLe coeffs is b).SatisfiedBy a := by
  rw [show DomConstraint.SatisfiedBy (DomConstraint.linLe coeffs is b) a =
    (dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b = true) from rfl]
  rw [show DomConstraint.SatisfiedBy (DomConstraint.linEq coeffs is b) a =
    (dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) = some b) from rfl] at hcons
  rw [dotLe_eq]
  exact ⟨b, hcons, by omega⟩

/-! ## Reason-validity shared kernels

Local copies of Fam/Arith.lean's shared kernels (which are
themselves local copies of Reason.lean's — this module sits upstream
of Reason, so the standalone packaging stays self-contained). -/

/-- Reason validity from clause truth: when some member of the
    reason clause is true at every internal solution, the reason's
    clause is entailed; with pivot membership the reason is valid. -/
theorem lin2_reason_valid_of_clause_true
    {problem : Problem DomConstraint Unit}
    {l : Literal} {r : Reason}
    (hmem : l ∈ r.clause)
    (htrue : ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
      ∃ l' ∈ r.clause, l'.eval a = some true) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l :=
  ⟨fun a ha => htrue a ha, decide_eq_true hmem⟩

/-- Normalization transfer from the raw emitted clause. -/
theorem lin2_reason_clause_norm_sf {r : Reason} {ng : Clause}
    (hcl : r = { clause := ng })
    (hnorm : ∀ q ∈ ng, q = q.norm) :
    ∀ q ∈ r.clause, q = q.norm := by
  intro q hq
  rw [hcl] at hq
  exact hnorm q hq

/-- A head-then-causes nogood is normalized when the head and the
    causes are (the emitted clause shape of both families). -/
theorem lin2_nogood_norm {head : Literal} {causes : Clause}
    (hhead : head = head.norm)
    (hcauses : ∀ q ∈ causes, q = q.norm) :
    ∀ q ∈ [head] ++ causes, q = q.norm := by
  intro q hq
  rcases List.mem_append.mp hq with hq' | hq'
  · rw [List.mem_singleton.mp hq']
    exact hhead
  · exact hcauses q hq'

/-! ## propLinLe2: the state-free conflict entitlement -/

/-- Every conflict clause of the corrected linLe propagator carries
    a true literal at every internal solution of any problem
    containing the constraint: the conflict clause IS the emitted
    nogood (`narrowHi`/`narrowLo`'s conflict arms carry it
    verbatim), and the nogood-truth kernels make it true under the
    constraint alone — no fit, no state coherence. -/
theorem propLinLe2_entitled {problem : Problem DomConstraint Unit}
    {st : State} {coeffs : List Int} {is : List Nat} {b : Int}
    {cc : Clause}
    (hprob : DomConstraint.linLe coeffs is b ∈ problem.constraints)
    (hlen : coeffs.length = is.length)
    (hrun : propLinLe2 st coeffs is b = .conflict cc)
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ cc, l.eval a = some true := by
  rcases propLinLe2_emission_inv hrun with hstable |
    ⟨m, i, rest, lr, hmem, hrest, hguard, hsum, hnarrow⟩ |
    ⟨m, i, rest, lr, hmem, hrest, hguard, hsum, hnarrow⟩ |
    ⟨m, i, rest, lr, c, hmem, hpos, hrest, hguard, hsum, hnarrow⟩ |
    ⟨m, i, rest, lr, c, hmem, hneg, hrest, hguard, hsum, hnarrow⟩
  · exact absurd hstable (by intro hc; cases hc)
  · -- the +1 slot's narrowHi conflict arm: cc is the emitted nogood
    obtain ⟨_, _, _, _, _, hcc⟩ := narrowHi_conflict_inv hnarrow.symm
    have hcons := ha.2 _ hprob
    have hreads := linLe2_reads_int hcons hlen
    rw [hcc]
    exact lin2_nogood_le_hi_true hmem hrest hguard hsum hreads
      hcons hlen
  · -- the −1 slot's narrowLo conflict arm
    obtain ⟨_, _, _, _, _, hcc⟩ := narrowLo_conflict_inv hnarrow.symm
    have hcons := ha.2 _ hprob
    have hreads := linLe2_reads_int hcons hlen
    rw [hcc]
    exact lin2_nogood_le_lo_true hmem hrest hguard hsum hreads
      hcons hlen
  · -- the general c > 0 slot's narrowHi conflict arm
    obtain ⟨_, _, _, _, _, hcc⟩ := narrowHi_conflict_inv hnarrow.symm
    have hcons := ha.2 _ hprob
    have hreads := linLe2_reads_int hcons hlen
    rw [hcc]
    exact lin2_nogood_gen_le_hi_true hmem hpos hrest hguard hsum
      hreads hcons hlen
  · -- the general c < 0 slot's narrowLo conflict arm
    obtain ⟨_, _, _, _, _, hcc⟩ := narrowLo_conflict_inv hnarrow.symm
    have hcons := ha.2 _ hprob
    have hreads := linLe2_reads_int hcons hlen
    rw [hcc]
    exact lin2_nogood_gen_le_lo_true hmem hneg hrest hguard hsum
      hreads hcons hlen

/-! ## propLinLe2: the state-free reason validity -/

/-- THE key theorem: every implied literal's reason is valid at
    every state — the reason clause is the emitted nogood (entailed
    at every internal solution by the nogood-truth kernels, no fit
    needed), the pivot is the head (the first element), and every
    clause literal is normalized. -/
theorem propLinLe2_reason_valid {problem : Problem DomConstraint Unit}
    {st : State} {coeffs : List Int} {is : List Nat} {b : Int}
    {l : Literal} {r : Reason}
    (hprob : DomConstraint.linLe coeffs is b ∈ problem.constraints)
    (hlen : coeffs.length = is.length)
    (hrun : propLinLe2 st coeffs is b = .implied l r) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  rcases propLinLe2_emission_inv hrun with hstable |
    ⟨m, i, rest, lr, hmem, hrest, hguard, hsum, hnarrow⟩ |
    ⟨m, i, rest, lr, hmem, hrest, hguard, hsum, hnarrow⟩ |
    ⟨m, i, rest, lr, c, hmem, hpos, hrest, hguard, hsum, hnarrow⟩ |
    ⟨m, i, rest, lr, c, hmem, hneg, hrest, hguard, hsum, hnarrow⟩
  · exact absurd hstable (by intro hc; cases hc)
  · -- the +1 slot: implied posLe m (b − lr), nogood
    -- [posLe m (b − lr)] ++ min-causes
    obtain ⟨hl, hcl⟩ := narrowHi_implied_inv hnarrow.symm
    have hpivmem : l ∈ r.clause := by
      subst hl; rw [hcl]; exact List.mem_cons_self
    refine ⟨lin2_reason_valid_of_clause_true hpivmem ?_,
      lin2_reason_clause_norm_sf hcl
        (lin2_nogood_norm (posLe_norm m (b - lr)).symm
          (lin2_causesMin_norm (st := st) (rest := rest)))⟩
    intro a ha
    have hcons := ha.2 _ hprob
    have hreads := linLe2_reads_int hcons hlen
    have hcl2 : r.clause = [posLe m (b - lr)] ++ linCausesMin st rest := by
      rw [hcl]
    rw [hcl2]
    exact lin2_nogood_le_hi_true hmem hrest hguard hsum hreads
      hcons hlen
  · -- the −1 slot: implied negLe m (lr − b − 1), nogood
    -- [negLe m (lr − b − 1)] ++ min-causes
    obtain ⟨hl, hcl⟩ := narrowLo_implied_inv hnarrow.symm
    have hpivmem : l ∈ r.clause := by
      subst hl; rw [hcl]; exact List.mem_cons_self
    refine ⟨lin2_reason_valid_of_clause_true hpivmem ?_,
      lin2_reason_clause_norm_sf hcl
        (lin2_nogood_norm (negLe_norm m (lr - b - 1)).symm
          (lin2_causesMin_norm (st := st) (rest := rest)))⟩
    intro a ha
    have hcons := ha.2 _ hprob
    have hreads := linLe2_reads_int hcons hlen
    have hcl2 : r.clause =
        [negLe m (lr - b - 1)] ++ linCausesMin st rest := by
      rw [hcl]
    rw [hcl2]
    exact lin2_nogood_le_lo_true hmem hrest hguard hsum hreads
      hcons hlen
  · -- the general c > 0 slot: implied posLe m ((b − lr)/c), nogood
    -- [posLe m ((b − lr)/c)] ++ min-causes
    obtain ⟨hl, hcl⟩ := narrowHi_implied_inv hnarrow.symm
    have hpivmem : l ∈ r.clause := by
      subst hl; rw [hcl]; exact List.mem_cons_self
    refine ⟨lin2_reason_valid_of_clause_true hpivmem ?_,
      lin2_reason_clause_norm_sf hcl
        (lin2_nogood_norm (posLe_norm m ((b - lr) / c)).symm
          (lin2_causesMin_norm (st := st) (rest := rest)))⟩
    intro a ha
    have hcons := ha.2 _ hprob
    have hreads := linLe2_reads_int hcons hlen
    have hcl2 : r.clause =
        [posLe m ((b - lr) / c)] ++ linCausesMin st rest := by
      rw [hcl]
    rw [hcl2]
    exact lin2_nogood_gen_le_hi_true hmem hpos hrest hguard hsum
      hreads hcons hlen
  · -- the general c < 0 slot: implied
    -- negLe m (−(b − lr)/(−c) − 1), nogood
    -- [negLe m (−(b − lr)/(−c) − 1)] ++ min-causes
    obtain ⟨hl, hcl⟩ := narrowLo_implied_inv hnarrow.symm
    have hpivmem : l ∈ r.clause := by
      subst hl; rw [hcl]; exact List.mem_cons_self
    refine ⟨lin2_reason_valid_of_clause_true hpivmem ?_,
      lin2_reason_clause_norm_sf hcl
        (lin2_nogood_norm
          (negLe_norm m (-((b - lr) / (-c)) - 1)).symm
          (lin2_causesMin_norm (st := st) (rest := rest)))⟩
    intro a ha
    have hcons := ha.2 _ hprob
    have hreads := linLe2_reads_int hcons hlen
    have hcl2 : r.clause =
        [negLe m (-((b - lr) / (-c)) - 1)] ++ linCausesMin st rest := by
      rw [hcl]
    rw [hcl2]
    exact lin2_nogood_gen_le_lo_true hmem hneg hrest hguard hsum
      hreads hcons hlen

/-! ## propLinEq2 soundness: the safe triple at fitting solutions -/

/-- The propagator of a `linEq coeffs is b` constraint: implied
    literal soundness, conflict soundness, and conflict entitlement,
    at every state. The two ≤-shaped arms (eqHiMin, eqLoMin) reuse
    the le absurd kernels (`d = b` implies `d ≤ b`); the two
    max-shaped arms (eqLoMax, eqHiMax) use the eq-max kernels. -/
theorem propLinEq2_safe (st : State) (coeffs : List Int) (is : List Nat)
    (b : Int) (hlen : coeffs.length = is.length) :
    (∀ l r, propLinEq2 st coeffs is b = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.linEq coeffs is b).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ c, propLinEq2 st coeffs is b = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.linEq coeffs is b).SatisfiedBy a → False) ∧
    (∀ c, propLinEq2 st coeffs is b = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.linEq coeffs is b).SatisfiedBy a →
        ∃ l ∈ c, l.eval a = some true) := by
  -- the conflict exclusion (the second conjunct, hoisted so the
  -- third can consume it vacuously)
  have hexcl : ∀ c, propLinEq2 st coeffs is b = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.linEq coeffs is b).SatisfiedBy a → False := by
    intro c hrun a hfit hcons
    rcases propLinEq2_emission_inv hrun with hstable |
      ⟨m, i, rest, lr, hmem, hrest, hguard, hsum, hnarrow⟩ |
      ⟨m, i, rest, hr, hmem, hrest, hguard, hsum, hnarrow⟩ |
      ⟨m, i, rest, lr, hmem, hrest, hguard, hsum, hnarrow⟩ |
      ⟨m, i, rest, hr, hmem, hrest, hguard, hsum, hnarrow⟩ |
      ⟨m, i, rest, lr, c, hmem, hpos, hrest, hguard, hsum, hnarrow⟩ |
      ⟨m, i, rest, hr, c, hmem, hpos, hrest, hguard, hsum, hnarrow⟩ |
      ⟨m, i, rest, lr, c, hmem, hneg, hrest, hguard, hsum, hnarrow⟩ |
      ⟨m, i, rest, hr, c, hmem, hneg, hrest, hguard, hsum, hnarrow⟩
    · exact absurd hstable (by intro hc; cases hc)
    · -- eqHiMin's narrowHi conflict arm (the le_hi shape)
      obtain ⟨mn, mx, hmn, hmx, hgt, hcc⟩ :=
        narrowHi_conflict_inv hnarrow.symm
      have hreads := linEq2_reads_int hcons hlen
      have hmem' : (1, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((1, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (1, m) hmem'
      have hmnt : mn ≤ xt := fits_min_bound hfit hmn hxt
      have hhead : (posLe m (b - lr)).eval a = some false := by
        rw [eval_posLe, hxt]
        show Option.map (fun i => decide (i ≤ b - lr)) (some xt) =
          some false
        rw [show Option.map (fun i => decide (i ≤ b - lr))
            (some xt) = some (decide (xt ≤ b - lr)) from rfl]
        have hdec : decide (xt ≤ b - lr) = false :=
          decide_eq_false (by omega)
        rw [hdec]
      have hreadsRest : ∀ p ∈ rest, ∃ x, slotInt a p.2 = some x := by
        intro p hp
        rw [hrest] at hp
        exact hreads p (lin2_others_mem_zip hp)
      have hcauses := lin2_causesMin_false_of_fits hfit hreadsRest
      obtain ⟨d, hdot, hdeq⟩ := linEq2_dot hcons hlen
      exact lin2_absurd_le_hi hmem hrest hguard hcauses hsum
        hreads hdot (by omega) hhead
    · -- eqLoMax's narrowLo conflict arm
      obtain ⟨mn, mx, hmn, hmx, hlt, hcc⟩ :=
        narrowLo_conflict_inv hnarrow.symm
      have hreads := linEq2_reads_int hcons hlen
      have hmem' : (1, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((1, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (1, m) hmem'
      have hmxt : xt ≤ mx := fits_max_bound hfit hmx hxt
      have hhead : (negLe m (b - hr - 1)).eval a = some false := by
        rw [eval_negLe, hxt]
        show Option.map (fun i => !(decide (i ≤ b - hr - 1)))
            (some xt) = some false
        rw [show Option.map (fun i => !(decide (i ≤ b - hr - 1)))
            (some xt) = some (!(decide (xt ≤ b - hr - 1))) from rfl]
        have hdec : (!(decide (xt ≤ b - hr - 1))) = false := by
          have htrue : decide (xt ≤ b - hr - 1) = true :=
            decide_eq_true (by omega)
          rw [htrue]
          rfl
        rw [hdec]
      have hreadsRest : ∀ p ∈ rest, ∃ x, slotInt a p.2 = some x := by
        intro p hp
        rw [hrest] at hp
        exact hreads p (lin2_others_mem_zip hp)
      have hcauses := lin2_causesMax_false_of_fits hfit hreadsRest
      obtain ⟨d, hdot, hdeq⟩ := linEq2_dot hcons hlen
      exact lin2_absurd_eq_lo_max hmem hrest hguard hcauses hsum
        hreads hdot hdeq hhead
    · -- eqLoMin's narrowLo conflict arm (the le_lo shape)
      obtain ⟨mn, mx, hmn, hmx, hlt, hcc⟩ :=
        narrowLo_conflict_inv hnarrow.symm
      have hreads := linEq2_reads_int hcons hlen
      have hmem' : (-1, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((-1, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (-1, m) hmem'
      have hmxt : xt ≤ mx := fits_max_bound hfit hmx hxt
      have hhead : (negLe m (lr - b - 1)).eval a = some false := by
        rw [eval_negLe, hxt]
        show Option.map (fun i => !(decide (i ≤ lr - b - 1)))
            (some xt) = some false
        rw [show Option.map (fun i => !(decide (i ≤ lr - b - 1)))
            (some xt) = some (!(decide (xt ≤ lr - b - 1))) from rfl]
        have hdec : (!(decide (xt ≤ lr - b - 1))) = false := by
          have htrue : decide (xt ≤ lr - b - 1) = true :=
            decide_eq_true (by omega)
          rw [htrue]
          rfl
        rw [hdec]
      have hreadsRest : ∀ p ∈ rest, ∃ x, slotInt a p.2 = some x := by
        intro p hp
        rw [hrest] at hp
        exact hreads p (lin2_others_mem_zip hp)
      have hcauses := lin2_causesMin_false_of_fits hfit hreadsRest
      obtain ⟨d, hdot, hdeq⟩ := linEq2_dot hcons hlen
      exact lin2_absurd_le_lo hmem hrest hguard hcauses hsum
        hreads hdot (by omega) hhead
    · -- eqHiMax's narrowHi conflict arm
      obtain ⟨mn, mx, hmn, hmx, hgt, hcc⟩ :=
        narrowHi_conflict_inv hnarrow.symm
      have hreads := linEq2_reads_int hcons hlen
      have hmem' : (-1, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((-1, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (-1, m) hmem'
      have hmnt : mn ≤ xt := fits_min_bound hfit hmn hxt
      have hhead : (posLe m (hr - b)).eval a = some false := by
        rw [eval_posLe, hxt]
        show Option.map (fun i => decide (i ≤ hr - b)) (some xt) =
          some false
        rw [show Option.map (fun i => decide (i ≤ hr - b))
            (some xt) = some (decide (xt ≤ hr - b)) from rfl]
        have hdec : decide (xt ≤ hr - b) = false :=
          decide_eq_false (by omega)
        rw [hdec]
      have hreadsRest : ∀ p ∈ rest, ∃ x, slotInt a p.2 = some x := by
        intro p hp
        rw [hrest] at hp
        exact hreads p (lin2_others_mem_zip hp)
      have hcauses := lin2_causesMax_false_of_fits hfit hreadsRest
      obtain ⟨d, hdot, hdeq⟩ := linEq2_dot hcons hlen
      exact lin2_absurd_eq_hi_max hmem hrest hguard hcauses hsum
        hreads hdot hdeq hhead
    · -- the general c > 0 HiMin arm's conflict exclusion
      obtain ⟨mn, mx, hmn, hmx, hgt, hcc⟩ :=
        narrowHi_conflict_inv hnarrow.symm
      have hreads := linEq2_reads_int hcons hlen
      have hmem' : (c, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((c, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (c, m) hmem'
      have hmnt : mn ≤ xt := fits_min_bound hfit hmn hxt
      have hhead : (posLe m ((b - lr) / c)).eval a = some false := by
        rw [eval_posLe, hxt]
        show Option.map (fun i => decide (i ≤ (b - lr) / c))
            (some xt) = some false
        rw [show Option.map (fun i => decide (i ≤ (b - lr) / c))
            (some xt) = some (decide (xt ≤ (b - lr) / c)) from rfl]
        have hdec : decide (xt ≤ (b - lr) / c) = false :=
          decide_eq_false (by omega)
        rw [hdec]
      have hreadsRest : ∀ p ∈ rest, ∃ x, slotInt a p.2 = some x := by
        intro p hp
        rw [hrest] at hp
        exact hreads p (lin2_others_mem_zip hp)
      have hcauses := lin2_causesMin_false_of_fits hfit hreadsRest
      obtain ⟨d, hdot, hdeq⟩ := linEq2_dot hcons hlen
      exact lin2_absurd_gen_le_hi hmem hpos hrest hguard hcauses hsum
        hreads hdot (by omega) hhead
    · -- the general c > 0 LoMax arm's conflict exclusion
      obtain ⟨mn, mx, hmn, hmx, hlt, hcc⟩ :=
        narrowLo_conflict_inv hnarrow.symm
      have hreads := linEq2_reads_int hcons hlen
      have hmem' : (c, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((c, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (c, m) hmem'
      have hmxt : xt ≤ mx := fits_max_bound hfit hmx hxt
      have hhead : (negLe m (-((hr - b) / c) - 1)).eval a
          = some false := by
        rw [eval_negLe, hxt]
        show Option.map (fun i =>
            !(decide (i ≤ -((hr - b) / c) - 1)))
            (some xt) = some false
        rw [show Option.map (fun i =>
            !(decide (i ≤ -((hr - b) / c) - 1)))
            (some xt) =
            some (!(decide (xt ≤ -((hr - b) / c) - 1))) from rfl]
        have hdec : (!(decide (xt ≤ -((hr - b) / c) - 1))) = false := by
          have htrue : decide (xt ≤ -((hr - b) / c) - 1) = true :=
            decide_eq_true (by omega)
          rw [htrue]
          rfl
        rw [hdec]
      have hreadsRest : ∀ p ∈ rest, ∃ x, slotInt a p.2 = some x := by
        intro p hp
        rw [hrest] at hp
        exact hreads p (lin2_others_mem_zip hp)
      have hcauses := lin2_causesMax_false_of_fits hfit hreadsRest
      obtain ⟨d, hdot, hdeq⟩ := linEq2_dot hcons hlen
      exact lin2_absurd_gen_eq_lo_max hmem hpos hrest hguard hcauses
        hsum hreads hdot hdeq hhead
    · -- the general c < 0 LoMin arm's conflict exclusion
      obtain ⟨mn, mx, hmn, hmx, hlt, hcc⟩ :=
        narrowLo_conflict_inv hnarrow.symm
      have hreads := linEq2_reads_int hcons hlen
      have hmem' : (c, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((c, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (c, m) hmem'
      have hmxt : xt ≤ mx := fits_max_bound hfit hmx hxt
      have hhead : (negLe m (-((b - lr) / (-c)) - 1)).eval a
          = some false := by
        rw [eval_negLe, hxt]
        show Option.map (fun i =>
            !(decide (i ≤ -((b - lr) / (-c)) - 1)))
            (some xt) = some false
        rw [show Option.map (fun i =>
            !(decide (i ≤ -((b - lr) / (-c)) - 1)))
            (some xt) =
            some (!(decide (xt ≤ -((b - lr) / (-c)) - 1))) from rfl]
        have hdec : (!(decide (xt ≤ -((b - lr) / (-c)) - 1))) = false := by
          have htrue : decide (xt ≤ -((b - lr) / (-c)) - 1) = true :=
            decide_eq_true (by omega)
          rw [htrue]
          rfl
        rw [hdec]
      have hreadsRest : ∀ p ∈ rest, ∃ x, slotInt a p.2 = some x := by
        intro p hp
        rw [hrest] at hp
        exact hreads p (lin2_others_mem_zip hp)
      have hcauses := lin2_causesMin_false_of_fits hfit hreadsRest
      obtain ⟨d, hdot, hdeq⟩ := linEq2_dot hcons hlen
      exact lin2_absurd_gen_le_lo hmem hneg hrest hguard hcauses hsum
        hreads hdot (by omega) hhead
    · -- the general c < 0 HiMax arm's conflict exclusion
      obtain ⟨mn, mx, hmn, hmx, hgt, hcc⟩ :=
        narrowHi_conflict_inv hnarrow.symm
      have hreads := linEq2_reads_int hcons hlen
      have hmem' : (c, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((c, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (c, m) hmem'
      have hmnt : mn ≤ xt := fits_min_bound hfit hmn hxt
      have hhead : (posLe m ((hr - b) / (-c))).eval a = some false := by
        rw [eval_posLe, hxt]
        show Option.map (fun i => decide (i ≤ (hr - b) / (-c)))
            (some xt) = some false
        rw [show Option.map (fun i => decide (i ≤ (hr - b) / (-c)))
            (some xt) = some (decide (xt ≤ (hr - b) / (-c))) from rfl]
        have hdec : decide (xt ≤ (hr - b) / (-c)) = false :=
          decide_eq_false (by omega)
        rw [hdec]
      have hreadsRest : ∀ p ∈ rest, ∃ x, slotInt a p.2 = some x := by
        intro p hp
        rw [hrest] at hp
        exact hreads p (lin2_others_mem_zip hp)
      have hcauses := lin2_causesMax_false_of_fits hfit hreadsRest
      obtain ⟨d, hdot, hdeq⟩ := linEq2_dot hcons hlen
      exact lin2_absurd_gen_eq_hi_max hmem hneg hrest hguard hcauses
        hsum hreads hdot hdeq hhead
  refine ⟨?_, hexcl, ?_⟩
  · -- implied-literal soundness: the head is true at every fitting
    -- solution (the causes are the domain-bound negations, false at
    -- every fitting solution; the kernels then force the head)
    intro l r hrun a hfit hcons
    rcases propLinEq2_emission_inv hrun with hstable |
      ⟨m, i, rest, lr, hmem, hrest, hguard, hsum, hnarrow⟩ |
      ⟨m, i, rest, hr, hmem, hrest, hguard, hsum, hnarrow⟩ |
      ⟨m, i, rest, lr, hmem, hrest, hguard, hsum, hnarrow⟩ |
      ⟨m, i, rest, hr, hmem, hrest, hguard, hsum, hnarrow⟩ |
      ⟨m, i, rest, lr, c, hmem, hpos, hrest, hguard, hsum, hnarrow⟩ |
      ⟨m, i, rest, hr, c, hmem, hpos, hrest, hguard, hsum, hnarrow⟩ |
      ⟨m, i, rest, lr, c, hmem, hneg, hrest, hguard, hsum, hnarrow⟩ |
      ⟨m, i, rest, hr, c, hmem, hneg, hrest, hguard, hsum, hnarrow⟩
    · exact absurd hstable (by intro hc; cases hc)
    · -- eqHiMin: the implied head is posLe m (b − lr)
      obtain ⟨hl, hcl⟩ := narrowHi_implied_inv hnarrow.symm
      subst hl
      have hreads := linEq2_reads_int hcons hlen
      have hreadsRest : ∀ p ∈ rest, ∃ x, slotInt a p.2 = some x := by
        intro p hp
        rw [hrest] at hp
        exact hreads p (lin2_others_mem_zip hp)
      have hcauses := lin2_causesMin_false_of_fits hfit hreadsRest
      have hmem' : (1, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((1, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (1, m) hmem'
      rw [eval_posLe, hxt]
      cases hbv : decide (xt ≤ b - lr) with
      | true =>
          show Option.map (fun i => decide (i ≤ b - lr)) (some xt) =
            some true
          rw [show Option.map (fun i => decide (i ≤ b - lr))
              (some xt) = some (decide (xt ≤ b - lr)) from rfl, hbv]
      | false =>
          exfalso
          have hhead : (posLe m (b - lr)).eval a = some false := by
            rw [eval_posLe, hxt]
            show Option.map (fun i => decide (i ≤ b - lr))
                (some xt) = some false
            rw [show Option.map (fun i => decide (i ≤ b - lr))
                (some xt) = some (decide (xt ≤ b - lr)) from rfl, hbv]
          obtain ⟨d, hdot, hdeq⟩ := linEq2_dot hcons hlen
          exact lin2_absurd_le_hi hmem hrest hguard hcauses hsum
            hreads hdot (by omega) hhead
    · -- eqLoMax: the implied head is negLe m (b − hr − 1)
      obtain ⟨hl, hcl⟩ := narrowLo_implied_inv hnarrow.symm
      subst hl
      have hreads := linEq2_reads_int hcons hlen
      have hreadsRest : ∀ p ∈ rest, ∃ x, slotInt a p.2 = some x := by
        intro p hp
        rw [hrest] at hp
        exact hreads p (lin2_others_mem_zip hp)
      have hcauses := lin2_causesMax_false_of_fits hfit hreadsRest
      have hmem' : (1, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((1, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (1, m) hmem'
      rw [eval_negLe, hxt]
      cases hbv : (!(decide (xt ≤ b - hr - 1))) with
      | true =>
          show Option.map (fun i => !(decide (i ≤ b - hr - 1)))
              (some xt) = some true
          rw [show Option.map (fun i => !(decide (i ≤ b - hr - 1)))
              (some xt) = some (!(decide (xt ≤ b - hr - 1))) from rfl,
            hbv]
      | false =>
          exfalso
          have hhead : (negLe m (b - hr - 1)).eval a = some false := by
            rw [eval_negLe, hxt]
            show Option.map (fun i => !(decide (i ≤ b - hr - 1)))
                (some xt) = some false
            rw [show Option.map (fun i => !(decide (i ≤ b - hr - 1)))
                (some xt) = some (!(decide (xt ≤ b - hr - 1))) from rfl,
              hbv]
          obtain ⟨d, hdot, hdeq⟩ := linEq2_dot hcons hlen
          exact lin2_absurd_eq_lo_max hmem hrest hguard hcauses hsum
            hreads hdot hdeq hhead
    · -- eqLoMin: the implied head is negLe m (lr − b − 1)
      obtain ⟨hl, hcl⟩ := narrowLo_implied_inv hnarrow.symm
      subst hl
      have hreads := linEq2_reads_int hcons hlen
      have hreadsRest : ∀ p ∈ rest, ∃ x, slotInt a p.2 = some x := by
        intro p hp
        rw [hrest] at hp
        exact hreads p (lin2_others_mem_zip hp)
      have hcauses := lin2_causesMin_false_of_fits hfit hreadsRest
      have hmem' : (-1, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((-1, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (-1, m) hmem'
      rw [eval_negLe, hxt]
      cases hbv : (!(decide (xt ≤ lr - b - 1))) with
      | true =>
          show Option.map (fun i => !(decide (i ≤ lr - b - 1)))
              (some xt) = some true
          rw [show Option.map (fun i => !(decide (i ≤ lr - b - 1)))
              (some xt) = some (!(decide (xt ≤ lr - b - 1))) from rfl,
            hbv]
      | false =>
          exfalso
          have hhead : (negLe m (lr - b - 1)).eval a = some false := by
            rw [eval_negLe, hxt]
            show Option.map (fun i => !(decide (i ≤ lr - b - 1)))
                (some xt) = some false
            rw [show Option.map (fun i => !(decide (i ≤ lr - b - 1)))
                (some xt) = some (!(decide (xt ≤ lr - b - 1))) from rfl,
              hbv]
          obtain ⟨d, hdot, hdeq⟩ := linEq2_dot hcons hlen
          exact lin2_absurd_le_lo hmem hrest hguard hcauses hsum
            hreads hdot (by omega) hhead
    · -- eqHiMax: the implied head is posLe m (hr − b)
      obtain ⟨hl, hcl⟩ := narrowHi_implied_inv hnarrow.symm
      subst hl
      have hreads := linEq2_reads_int hcons hlen
      have hreadsRest : ∀ p ∈ rest, ∃ x, slotInt a p.2 = some x := by
        intro p hp
        rw [hrest] at hp
        exact hreads p (lin2_others_mem_zip hp)
      have hcauses := lin2_causesMax_false_of_fits hfit hreadsRest
      have hmem' : (-1, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((-1, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (-1, m) hmem'
      rw [eval_posLe, hxt]
      cases hbv : decide (xt ≤ hr - b) with
      | true =>
          show Option.map (fun i => decide (i ≤ hr - b)) (some xt) =
            some true
          rw [show Option.map (fun i => decide (i ≤ hr - b))
              (some xt) = some (decide (xt ≤ hr - b)) from rfl, hbv]
      | false =>
          exfalso
          have hhead : (posLe m (hr - b)).eval a = some false := by
            rw [eval_posLe, hxt]
            show Option.map (fun i => decide (i ≤ hr - b))
                (some xt) = some false
            rw [show Option.map (fun i => decide (i ≤ hr - b))
                (some xt) = some (decide (xt ≤ hr - b)) from rfl, hbv]
          obtain ⟨d, hdot, hdeq⟩ := linEq2_dot hcons hlen
          exact lin2_absurd_eq_hi_max hmem hrest hguard hcauses hsum
            hreads hdot hdeq hhead
    · -- the general c > 0 HiMin arm: the implied head is
      -- posLe m ((b − lr)/c)
      obtain ⟨hl, hcl⟩ := narrowHi_implied_inv hnarrow.symm
      subst hl
      have hreads := linEq2_reads_int hcons hlen
      have hreadsRest : ∀ p ∈ rest, ∃ x, slotInt a p.2 = some x := by
        intro p hp
        rw [hrest] at hp
        exact hreads p (lin2_others_mem_zip hp)
      have hcauses := lin2_causesMin_false_of_fits hfit hreadsRest
      have hmem' : (c, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((c, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (c, m) hmem'
      rw [eval_posLe, hxt]
      cases hbv : decide (xt ≤ (b - lr) / c) with
      | true =>
          show Option.map (fun i => decide (i ≤ (b - lr) / c))
              (some xt) = some true
          rw [show Option.map (fun i => decide (i ≤ (b - lr) / c))
              (some xt) = some (decide (xt ≤ (b - lr) / c)) from rfl,
            hbv]
      | false =>
          exfalso
          have hhead : (posLe m ((b - lr) / c)).eval a = some false := by
            rw [eval_posLe, hxt]
            show Option.map (fun i => decide (i ≤ (b - lr) / c))
                (some xt) = some false
            rw [show Option.map (fun i => decide (i ≤ (b - lr) / c))
                (some xt) = some (decide (xt ≤ (b - lr) / c)) from rfl,
              hbv]
          obtain ⟨d, hdot, hdeq⟩ := linEq2_dot hcons hlen
          exact lin2_absurd_gen_le_hi hmem hpos hrest hguard hcauses
            hsum hreads hdot (by omega) hhead
    · -- the general c > 0 LoMax arm: the implied head is
      -- negLe m (−(hr − b)/c − 1)
      obtain ⟨hl, hcl⟩ := narrowLo_implied_inv hnarrow.symm
      subst hl
      have hreads := linEq2_reads_int hcons hlen
      have hreadsRest : ∀ p ∈ rest, ∃ x, slotInt a p.2 = some x := by
        intro p hp
        rw [hrest] at hp
        exact hreads p (lin2_others_mem_zip hp)
      have hcauses := lin2_causesMax_false_of_fits hfit hreadsRest
      have hmem' : (c, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((c, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (c, m) hmem'
      rw [eval_negLe, hxt]
      cases hbv : (!(decide (xt ≤ -((hr - b) / c) - 1))) with
      | true =>
          show Option.map (fun i =>
              !(decide (i ≤ -((hr - b) / c) - 1)))
              (some xt) = some true
          rw [show Option.map (fun i =>
              !(decide (i ≤ -((hr - b) / c) - 1)))
              (some xt) =
              some (!(decide (xt ≤ -((hr - b) / c) - 1))) from rfl,
            hbv]
      | false =>
          exfalso
          have hhead : (negLe m (-((hr - b) / c) - 1)).eval a
              = some false := by
            rw [eval_negLe, hxt]
            show Option.map (fun i =>
                !(decide (i ≤ -((hr - b) / c) - 1)))
                (some xt) = some false
            rw [show Option.map (fun i =>
                !(decide (i ≤ -((hr - b) / c) - 1)))
                (some xt) =
                some (!(decide (xt ≤ -((hr - b) / c) - 1))) from rfl,
              hbv]
          obtain ⟨d, hdot, hdeq⟩ := linEq2_dot hcons hlen
          exact lin2_absurd_gen_eq_lo_max hmem hpos hrest hguard
            hcauses hsum hreads hdot hdeq hhead
    · -- the general c < 0 LoMin arm: the implied head is
      -- negLe m (−(b − lr)/(−c) − 1)
      obtain ⟨hl, hcl⟩ := narrowLo_implied_inv hnarrow.symm
      subst hl
      have hreads := linEq2_reads_int hcons hlen
      have hreadsRest : ∀ p ∈ rest, ∃ x, slotInt a p.2 = some x := by
        intro p hp
        rw [hrest] at hp
        exact hreads p (lin2_others_mem_zip hp)
      have hcauses := lin2_causesMin_false_of_fits hfit hreadsRest
      have hmem' : (c, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((c, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (c, m) hmem'
      rw [eval_negLe, hxt]
      cases hbv : (!(decide (xt ≤ -((b - lr) / (-c)) - 1))) with
      | true =>
          show Option.map (fun i =>
              !(decide (i ≤ -((b - lr) / (-c)) - 1)))
              (some xt) = some true
          rw [show Option.map (fun i =>
              !(decide (i ≤ -((b - lr) / (-c)) - 1)))
              (some xt) =
              some (!(decide (xt ≤ -((b - lr) / (-c)) - 1))) from rfl,
            hbv]
      | false =>
          exfalso
          have hhead : (negLe m (-((b - lr) / (-c)) - 1)).eval a
              = some false := by
            rw [eval_negLe, hxt]
            show Option.map (fun i =>
                !(decide (i ≤ -((b - lr) / (-c)) - 1)))
                (some xt) = some false
            rw [show Option.map (fun i =>
                !(decide (i ≤ -((b - lr) / (-c)) - 1)))
                (some xt) =
                some (!(decide (xt ≤ -((b - lr) / (-c)) - 1))) from rfl,
              hbv]
          obtain ⟨d, hdot, hdeq⟩ := linEq2_dot hcons hlen
          exact lin2_absurd_gen_le_lo hmem hneg hrest hguard hcauses
            hsum hreads hdot (by omega) hhead
    · -- the general c < 0 HiMax arm: the implied head is
      -- posLe m ((hr − b)/(−c))
      obtain ⟨hl, hcl⟩ := narrowHi_implied_inv hnarrow.symm
      subst hl
      have hreads := linEq2_reads_int hcons hlen
      have hreadsRest : ∀ p ∈ rest, ∃ x, slotInt a p.2 = some x := by
        intro p hp
        rw [hrest] at hp
        exact hreads p (lin2_others_mem_zip hp)
      have hcauses := lin2_causesMax_false_of_fits hfit hreadsRest
      have hmem' : (c, m) ∈ coeffs.zip is :=
        lin2_mem_zip_of_zipIdx _ 0 ((c, m), i) hmem
      obtain ⟨xt, hxt⟩ := hreads (c, m) hmem'
      rw [eval_posLe, hxt]
      cases hbv : decide (xt ≤ (hr - b) / (-c)) with
      | true =>
          show Option.map (fun i => decide (i ≤ (hr - b) / (-c)))
              (some xt) = some true
          rw [show Option.map (fun i => decide (i ≤ (hr - b) / (-c)))
              (some xt) = some (decide (xt ≤ (hr - b) / (-c))) from
              rfl, hbv]
      | false =>
          exfalso
          have hhead : (posLe m ((hr - b) / (-c))).eval a
              = some false := by
            rw [eval_posLe, hxt]
            show Option.map (fun i => decide (i ≤ (hr - b) / (-c)))
                (some xt) = some false
            rw [show Option.map (fun i => decide (i ≤ (hr - b) / (-c)))
                (some xt) = some (decide (xt ≤ (hr - b) / (-c))) from
              rfl, hbv]
          obtain ⟨d, hdot, hdeq⟩ := linEq2_dot hcons hlen
          exact lin2_absurd_gen_eq_hi_max hmem hneg hrest hguard
            hcauses hsum hreads hdot hdeq hhead
  · -- conflict entitlement: VACUOUS — the exclusion above makes the
    -- fitting+satisfied hypotheses contradictory
    intro c hrun a hfit hcons
    exact absurd (hexcl c hrun a hfit hcons) (fun h => h)

/-! ## propLinEq2: the state-free conflict entitlement -/

/-- Every conflict clause of the linEq propagator carries a true
    literal at every internal solution: the clause is one of the four
    emitted nogoods, each integer-valid under the equality alone. -/
theorem propLinEq2_entitled {problem : Problem DomConstraint Unit}
    {st : State} {coeffs : List Int} {is : List Nat} {b : Int}
    {cc : Clause}
    (hprob : DomConstraint.linEq coeffs is b ∈ problem.constraints)
    (hlen : coeffs.length = is.length)
    (hrun : propLinEq2 st coeffs is b = .conflict cc)
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ cc, l.eval a = some true := by
  rcases propLinEq2_emission_inv hrun with hstable |
    ⟨m, i, rest, lr, hmem, hrest, hguard, hsum, hnarrow⟩ |
    ⟨m, i, rest, hr, hmem, hrest, hguard, hsum, hnarrow⟩ |
    ⟨m, i, rest, lr, hmem, hrest, hguard, hsum, hnarrow⟩ |
    ⟨m, i, rest, hr, hmem, hrest, hguard, hsum, hnarrow⟩ |
    ⟨m, i, rest, lr, c, hmem, hpos, hrest, hguard, hsum, hnarrow⟩ |
    ⟨m, i, rest, hr, c, hmem, hpos, hrest, hguard, hsum, hnarrow⟩ |
    ⟨m, i, rest, lr, c, hmem, hneg, hrest, hguard, hsum, hnarrow⟩ |
    ⟨m, i, rest, hr, c, hmem, hneg, hrest, hguard, hsum, hnarrow⟩
  · exact absurd hstable (by intro hc; cases hc)
  · -- eqHiMin's nogood (the le_hi shape; the equality implies the
    -- ≤ bound)
    obtain ⟨_, _, _, _, _, hcc⟩ := narrowHi_conflict_inv hnarrow.symm
    have hcons := ha.2 _ hprob
    have hreads := linEq2_reads_int hcons hlen
    rw [hcc]
    exact lin2_nogood_le_hi_true hmem hrest hguard hsum hreads
      (linEq_sat_le hcons) hlen
  · -- eqLoMax's nogood
    obtain ⟨_, _, _, _, _, hcc⟩ := narrowLo_conflict_inv hnarrow.symm
    have hcons := ha.2 _ hprob
    have hreads := linEq2_reads_int hcons hlen
    rw [hcc]
    exact lin2_nogood_eq_lo_max_true hmem hrest hguard hsum hreads
      hcons hlen
  · -- eqLoMin's nogood (the le_lo shape)
    obtain ⟨_, _, _, _, _, hcc⟩ := narrowLo_conflict_inv hnarrow.symm
    have hcons := ha.2 _ hprob
    have hreads := linEq2_reads_int hcons hlen
    rw [hcc]
    exact lin2_nogood_le_lo_true hmem hrest hguard hsum hreads
      (linEq_sat_le hcons) hlen
  · -- eqHiMax's nogood
    obtain ⟨_, _, _, _, _, hcc⟩ := narrowHi_conflict_inv hnarrow.symm
    have hcons := ha.2 _ hprob
    have hreads := linEq2_reads_int hcons hlen
    rw [hcc]
    exact lin2_nogood_eq_hi_max_true hmem hrest hguard hsum hreads
      hcons hlen
  · -- the general c > 0 HiMin nogood (the le_hi shape)
    obtain ⟨_, _, _, _, _, hcc⟩ := narrowHi_conflict_inv hnarrow.symm
    have hcons := ha.2 _ hprob
    have hreads := linEq2_reads_int hcons hlen
    rw [hcc]
    exact lin2_nogood_gen_le_hi_true hmem hpos hrest hguard hsum
      hreads (linEq_sat_le hcons) hlen
  · -- the general c > 0 LoMax nogood
    obtain ⟨_, _, _, _, _, hcc⟩ := narrowLo_conflict_inv hnarrow.symm
    have hcons := ha.2 _ hprob
    have hreads := linEq2_reads_int hcons hlen
    rw [hcc]
    exact lin2_nogood_gen_eq_lo_max_true hmem hpos hrest hguard hsum
      hreads hcons hlen
  · -- the general c < 0 LoMin nogood (the le_lo shape)
    obtain ⟨_, _, _, _, _, hcc⟩ := narrowLo_conflict_inv hnarrow.symm
    have hcons := ha.2 _ hprob
    have hreads := linEq2_reads_int hcons hlen
    rw [hcc]
    exact lin2_nogood_gen_le_lo_true hmem hneg hrest hguard hsum
      hreads (linEq_sat_le hcons) hlen
  · -- the general c < 0 HiMax nogood
    obtain ⟨_, _, _, _, _, hcc⟩ := narrowHi_conflict_inv hnarrow.symm
    have hcons := ha.2 _ hprob
    have hreads := linEq2_reads_int hcons hlen
    rw [hcc]
    exact lin2_nogood_gen_eq_hi_max_true hmem hneg hrest hguard hsum
      hreads hcons hlen

/-! ## propLinEq2: the state-free reason validity -/

/-- The state-free reason-validity lemma for the linEq family: all
    four nogood shapes are integer-valid under the equality alone,
    the pivot is each nogood's head, and every literal is
    normalized. -/
theorem propLinEq2_reason_valid {problem : Problem DomConstraint Unit}
    {st : State} {coeffs : List Int} {is : List Nat} {b : Int}
    {l : Literal} {r : Reason}
    (hprob : DomConstraint.linEq coeffs is b ∈ problem.constraints)
    (hlen : coeffs.length = is.length)
    (hrun : propLinEq2 st coeffs is b = .implied l r) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  rcases propLinEq2_emission_inv hrun with hstable |
    ⟨m, i, rest, lr, hmem, hrest, hguard, hsum, hnarrow⟩ |
    ⟨m, i, rest, hr, hmem, hrest, hguard, hsum, hnarrow⟩ |
    ⟨m, i, rest, lr, hmem, hrest, hguard, hsum, hnarrow⟩ |
    ⟨m, i, rest, hr, hmem, hrest, hguard, hsum, hnarrow⟩ |
    ⟨m, i, rest, lr, c, hmem, hpos, hrest, hguard, hsum, hnarrow⟩ |
    ⟨m, i, rest, hr, c, hmem, hpos, hrest, hguard, hsum, hnarrow⟩ |
    ⟨m, i, rest, lr, c, hmem, hneg, hrest, hguard, hsum, hnarrow⟩ |
    ⟨m, i, rest, hr, c, hmem, hneg, hrest, hguard, hsum, hnarrow⟩
  · exact absurd hstable (by intro hc; cases hc)
  · -- eqHiMin: implied posLe m (b − lr), nogood
    -- [posLe m (b − lr)] ++ min-causes
    obtain ⟨hl, hcl⟩ := narrowHi_implied_inv hnarrow.symm
    have hpivmem : l ∈ r.clause := by
      subst hl; rw [hcl]; exact List.mem_cons_self
    refine ⟨lin2_reason_valid_of_clause_true hpivmem ?_,
      lin2_reason_clause_norm_sf hcl
        (lin2_nogood_norm (posLe_norm m (b - lr)).symm
          (lin2_causesMin_norm (st := st) (rest := rest)))⟩
    intro a ha
    have hcons := ha.2 _ hprob
    have hreads := linEq2_reads_int hcons hlen
    have hcl2 : r.clause = [posLe m (b - lr)] ++ linCausesMin st rest := by
      rw [hcl]
    rw [hcl2]
    exact lin2_nogood_le_hi_true hmem hrest hguard hsum hreads
      (linEq_sat_le hcons) hlen
  · -- eqLoMax: implied negLe m (b − hr − 1), nogood
    -- [negLe m (b − hr − 1)] ++ max-causes
    obtain ⟨hl, hcl⟩ := narrowLo_implied_inv hnarrow.symm
    have hpivmem : l ∈ r.clause := by
      subst hl; rw [hcl]; exact List.mem_cons_self
    refine ⟨lin2_reason_valid_of_clause_true hpivmem ?_,
      lin2_reason_clause_norm_sf hcl
        (lin2_nogood_norm (negLe_norm m (b - hr - 1)).symm
          (lin2_causesMax_norm (st := st) (rest := rest)))⟩
    intro a ha
    have hcons := ha.2 _ hprob
    have hreads := linEq2_reads_int hcons hlen
    have hcl2 : r.clause =
        [negLe m (b - hr - 1)] ++ linCausesMax st rest := by
      rw [hcl]
    rw [hcl2]
    exact lin2_nogood_eq_lo_max_true hmem hrest hguard hsum hreads
      hcons hlen
  · -- eqLoMin: implied negLe m (lr − b − 1), nogood
    -- [negLe m (lr − b − 1)] ++ min-causes
    obtain ⟨hl, hcl⟩ := narrowLo_implied_inv hnarrow.symm
    have hpivmem : l ∈ r.clause := by
      subst hl; rw [hcl]; exact List.mem_cons_self
    refine ⟨lin2_reason_valid_of_clause_true hpivmem ?_,
      lin2_reason_clause_norm_sf hcl
        (lin2_nogood_norm (negLe_norm m (lr - b - 1)).symm
          (lin2_causesMin_norm (st := st) (rest := rest)))⟩
    intro a ha
    have hcons := ha.2 _ hprob
    have hreads := linEq2_reads_int hcons hlen
    have hcl2 : r.clause =
        [negLe m (lr - b - 1)] ++ linCausesMin st rest := by
      rw [hcl]
    rw [hcl2]
    exact lin2_nogood_le_lo_true hmem hrest hguard hsum hreads
      (linEq_sat_le hcons) hlen
  · -- eqHiMax: implied posLe m (hr − b), nogood
    -- [posLe m (hr − b)] ++ max-causes
    obtain ⟨hl, hcl⟩ := narrowHi_implied_inv hnarrow.symm
    have hpivmem : l ∈ r.clause := by
      subst hl; rw [hcl]; exact List.mem_cons_self
    refine ⟨lin2_reason_valid_of_clause_true hpivmem ?_,
      lin2_reason_clause_norm_sf hcl
        (lin2_nogood_norm (posLe_norm m (hr - b)).symm
          (lin2_causesMax_norm (st := st) (rest := rest)))⟩
    intro a ha
    have hcons := ha.2 _ hprob
    have hreads := linEq2_reads_int hcons hlen
    have hcl2 : r.clause =
        [posLe m (hr - b)] ++ linCausesMax st rest := by
      rw [hcl]
    rw [hcl2]
    exact lin2_nogood_eq_hi_max_true hmem hrest hguard hsum hreads
      hcons hlen
  · -- the general c > 0 HiMin arm: implied
    -- posLe m ((b − lr)/c), nogood
    -- [posLe m ((b − lr)/c)] ++ min-causes
    obtain ⟨hl, hcl⟩ := narrowHi_implied_inv hnarrow.symm
    have hpivmem : l ∈ r.clause := by
      subst hl; rw [hcl]; exact List.mem_cons_self
    refine ⟨lin2_reason_valid_of_clause_true hpivmem ?_,
      lin2_reason_clause_norm_sf hcl
        (lin2_nogood_norm (posLe_norm m ((b - lr) / c)).symm
          (lin2_causesMin_norm (st := st) (rest := rest)))⟩
    intro a ha
    have hcons := ha.2 _ hprob
    have hreads := linEq2_reads_int hcons hlen
    have hcl2 : r.clause =
        [posLe m ((b - lr) / c)] ++ linCausesMin st rest := by
      rw [hcl]
    rw [hcl2]
    exact lin2_nogood_gen_le_hi_true hmem hpos hrest hguard hsum
      hreads (linEq_sat_le hcons) hlen
  · -- the general c > 0 LoMax arm: implied
    -- negLe m (−(hr − b)/c − 1), nogood
    -- [negLe m (−(hr − b)/c − 1)] ++ max-causes
    obtain ⟨hl, hcl⟩ := narrowLo_implied_inv hnarrow.symm
    have hpivmem : l ∈ r.clause := by
      subst hl; rw [hcl]; exact List.mem_cons_self
    refine ⟨lin2_reason_valid_of_clause_true hpivmem ?_,
      lin2_reason_clause_norm_sf hcl
        (lin2_nogood_norm
          (negLe_norm m (-((hr - b) / c) - 1)).symm
          (lin2_causesMax_norm (st := st) (rest := rest)))⟩
    intro a ha
    have hcons := ha.2 _ hprob
    have hreads := linEq2_reads_int hcons hlen
    have hcl2 : r.clause =
        [negLe m (-((hr - b) / c) - 1)] ++ linCausesMax st rest := by
      rw [hcl]
    rw [hcl2]
    exact lin2_nogood_gen_eq_lo_max_true hmem hpos hrest hguard hsum
      hreads hcons hlen
  · -- the general c < 0 LoMin arm: implied
    -- negLe m (−(b − lr)/(−c) − 1), nogood
    -- [negLe m (−(b − lr)/(−c) − 1)] ++ min-causes
    obtain ⟨hl, hcl⟩ := narrowLo_implied_inv hnarrow.symm
    have hpivmem : l ∈ r.clause := by
      subst hl; rw [hcl]; exact List.mem_cons_self
    refine ⟨lin2_reason_valid_of_clause_true hpivmem ?_,
      lin2_reason_clause_norm_sf hcl
        (lin2_nogood_norm
          (negLe_norm m (-((b - lr) / (-c)) - 1)).symm
          (lin2_causesMin_norm (st := st) (rest := rest)))⟩
    intro a ha
    have hcons := ha.2 _ hprob
    have hreads := linEq2_reads_int hcons hlen
    have hcl2 : r.clause =
        [negLe m (-((b - lr) / (-c)) - 1)] ++ linCausesMin st rest := by
      rw [hcl]
    rw [hcl2]
    exact lin2_nogood_gen_le_lo_true hmem hneg hrest hguard hsum
      hreads (linEq_sat_le hcons) hlen
  · -- the general c < 0 HiMax arm: implied
    -- posLe m ((hr − b)/(−c)), nogood
    -- [posLe m ((hr − b)/(−c))] ++ max-causes
    obtain ⟨hl, hcl⟩ := narrowHi_implied_inv hnarrow.symm
    have hpivmem : l ∈ r.clause := by
      subst hl; rw [hcl]; exact List.mem_cons_self
    refine ⟨lin2_reason_valid_of_clause_true hpivmem ?_,
      lin2_reason_clause_norm_sf hcl
        (lin2_nogood_norm (posLe_norm m ((hr - b) / (-c))).symm
          (lin2_causesMax_norm (st := st) (rest := rest)))⟩
    intro a ha
    have hcons := ha.2 _ hprob
    have hreads := linEq2_reads_int hcons hlen
    have hcl2 : r.clause =
        [posLe m ((hr - b) / (-c))] ++ linCausesMax st rest := by
      rw [hcl]
    rw [hcl2]
    exact lin2_nogood_gen_eq_hi_max_true hmem hneg hrest hguard hsum
      hreads hcons hlen

/-! ## The registration packages -/

/-- Membership inversion for the standalone registration. -/
theorem propagatorOfProvedBLin_mem {dcs : List DomConstraint}
    {p : Propagator} (hp : p ∈ dcs.filterMap propagatorOfProvedBLin) :
    ∃ dc ∈ dcs, propagatorOfProvedBLin dc = some p := by
  induction dcs with
  | nil => cases hp
  | cons dc rest ih =>
      cases hpdc : propagatorOfProvedBLin dc with
      | none =>
          simp only [List.filterMap_cons, hpdc] at hp
          obtain ⟨dc2, hdc2mem, hdc2⟩ := ih hp
          exact ⟨dc2, List.mem_cons_of_mem _ hdc2mem, hdc2⟩
      | some p0 =>
          simp only [List.filterMap_cons, hpdc] at hp
          rcases List.mem_cons.mp hp with hp2 | hp2
          · rw [hp2]
            exact ⟨dc, List.mem_cons_self, hpdc⟩
          · obtain ⟨dc2, hdc2mem, hdc2⟩ := ih hp2
            exact ⟨dc2, List.mem_cons_of_mem _ hdc2mem, hdc2⟩

/-- Emission inversion for the registration: a registered
    propagator's run is one of the two families' propagators. -/
theorem propagatorOfProvedBLin_run {dc : DomConstraint} {p : Propagator}
    {st : State} {res : PropagationResult}
    (hprop : propagatorOfProvedBLin dc = some p)
    (hrun : p.run st = res) :
    (∃ coeffs is b, dc = .linLe coeffs is b ∧
      propLinLe2 st coeffs is b = res) ∨
    (∃ coeffs is b, dc = .linEq coeffs is b ∧
      propLinEq2 st coeffs is b = res) := by
  match hdc : dc with
  | .linLe coeffs is b =>
      simp only [propagatorOfProvedBLin] at hprop
      refine Or.inl ⟨coeffs, is, b, rfl, ?_⟩
      have hp2 : p = { watches := [], run := fun st => propLinLe2 st coeffs is b } :=
        (Option.some.inj hprop).symm
      rw [hp2] at hrun
      exact hrun
  | .linEq coeffs is b =>
      simp only [propagatorOfProvedBLin] at hprop
      refine Or.inr ⟨coeffs, is, b, rfl, ?_⟩
      have hp2 : p = { watches := [], run := fun st => propLinEq2 st coeffs is b } :=
        (Option.some.inj hprop).symm
      rw [hp2] at hrun
      exact hrun
  | .eqSlot i j =>
      simp only [propagatorOfProvedBLin] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .neSlot i j =>
      simp only [propagatorOfProvedBLin] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .leSlot i j =>
      simp only [propagatorOfProvedBLin] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .constEq i v =>
      simp only [propagatorOfProvedBLin] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .plusSlot i j k =>
      simp only [propagatorOfProvedBLin] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .leConstHi i c =>
      simp only [propagatorOfProvedBLin] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .leConstLo i c =>
      simp only [propagatorOfProvedBLin] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .allDiff is =>
      simp only [propagatorOfProvedBLin] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .timesSlot i j k =>
      simp only [propagatorOfProvedBLin] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .minSlot i j k =>
      simp only [propagatorOfProvedBLin] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .maxSlot i j k =>
      simp only [propagatorOfProvedBLin] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .absSlot i k =>
      simp only [propagatorOfProvedBLin] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .ltSlot i j =>
      simp only [propagatorOfProvedBLin] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .ltConstHi i c =>
      simp only [propagatorOfProvedBLin] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .ltConstLo i c =>
      simp only [propagatorOfProvedBLin] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .boolNotSlot i j =>
      simp only [propagatorOfProvedBLin] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .boolAndSlot i j k =>
      simp only [propagatorOfProvedBLin] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .boolOrSlot i j k =>
      simp only [propagatorOfProvedBLin] at hprop
      exact absurd hprop (by intro hc; cases hc)

/-! ## Axiom checks

Every theorem above uses only the standard axioms. -/

#print axioms linEq_sat_le
#print axioms lin2_reason_valid_of_clause_true
#print axioms lin2_reason_clause_norm_sf
#print axioms lin2_nogood_norm
#print axioms propLinLe2_entitled
#print axioms propLinLe2_reason_valid
#print axioms propLinEq2_safe
#print axioms propLinEq2_entitled
#print axioms propLinEq2_reason_valid
#print axioms propagatorOfProvedBLin_mem
#print axioms propagatorOfProvedBLin_run
-- the pre-existing key theorems this package consumes
#print axioms propLinLe2_safe
#print axioms propLinLe2_emission_inv
#print axioms propLinEq2_emission_inv
#print axioms lin2_nogood_le_hi_true
#print axioms lin2_nogood_le_lo_true
#print axioms lin2_nogood_eq_lo_max_true
#print axioms lin2_nogood_eq_hi_max_true
-- the general-coefficient package
#print axioms lin2_fl_hi_lt
#print axioms lin2_cl_neg_lo_gt
#print axioms lin2_absurd_gen_le_hi
#print axioms lin2_absurd_gen_le_lo
#print axioms lin2_absurd_gen_eq_lo_max
#print axioms lin2_absurd_gen_eq_hi_max
#print axioms lin2_nogood_gen_le_hi_true
#print axioms lin2_nogood_gen_le_lo_true
#print axioms lin2_nogood_gen_eq_lo_max_true
#print axioms lin2_nogood_gen_eq_hi_max_true
#print axioms lin2_causesMin_false_of_fits
#print axioms lin2_causesMax_false_of_fits
#print axioms propagatorOfProvedBLin

end LeanFzn.Solver.Propagation

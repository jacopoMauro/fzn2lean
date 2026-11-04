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
import LeanFzn.Solver.Propagation.Proofs.Fam.Bool
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
  match domMinI (st.domains.getD p.2 Dom.empty), domMaxI (st.domains.getD p.2 Dom.empty) with
  | some mn, some mx =>
      if p.1 ≥ 0 then some (p.2, p.1, p.1 * mn) else some (p.2, p.1, p.1 * mx)
  | _, _ => none

/-- Structural twin of `minContrib`: the compact bounds read the stored
    endpoints instead of enumerating a wide hole interval on every sweep
    step. -/
def minContribFast (st : State) (p : Int × Nat) : Option (Nat × Int × Int) :=
  match Dom.minInt? (st.domains.getD p.2 Dom.empty),
      Dom.maxInt? (st.domains.getD p.2 Dom.empty) with
  | some mn, some mx =>
      if p.1 ≥ 0 then some (p.2, p.1, p.1 * mn) else some (p.2, p.1, p.1 * mx)
  | _, _ => none

theorem minContribFast_eq (st : State) (p : Int × Nat) :
    minContribFast st p = minContrib st p := by
  unfold minContribFast minContrib
  rw [minInt?_eq_domMinI, maxInt?_eq_domMaxI]

attribute [implemented_by minContribFast] minContrib

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
  match domMinI (st.domains.getD p.2 Dom.empty), domMaxI (st.domains.getD p.2 Dom.empty) with
  | some mn, some mx =>
      if p.1 ≥ 0 then some (p.2, p.1, p.1 * mx) else some (p.2, p.1, p.1 * mn)
  | _, _ => none

/-- Structural twin of `maxContrib`. -/
def maxContribFast (st : State) (p : Int × Nat) : Option (Nat × Int × Int) :=
  match Dom.minInt? (st.domains.getD p.2 Dom.empty),
      Dom.maxInt? (st.domains.getD p.2 Dom.empty) with
  | some mn, some mx =>
      if p.1 ≥ 0 then some (p.2, p.1, p.1 * mx) else some (p.2, p.1, p.1 * mn)
  | _, _ => none

theorem maxContribFast_eq (st : State) (p : Int × Nat) :
    maxContribFast st p = maxContrib st p := by
  unfold maxContribFast maxContrib
  rw [minInt?_eq_domMinI, maxInt?_eq_domMaxI]

attribute [implemented_by maxContribFast] maxContrib

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
    (domMinI (st.domains.getD p.2 Dom.empty)).map fun mn => posLe p.2 (mn - 1)
  else if p.1 < 0 then
    (domMaxI (st.domains.getD p.2 Dom.empty)).map fun mx => negLe p.2 mx
  else none

/-- Structural twin of `linCauseMinPair`. -/
def linCauseMinPairFast (st : State) (p : Int × Nat) : Option Literal :=
  if p.1 > 0 then
    (Dom.minInt? (st.domains.getD p.2 Dom.empty)).map fun mn => posLe p.2 (mn - 1)
  else if p.1 < 0 then
    (Dom.maxInt? (st.domains.getD p.2 Dom.empty)).map fun mx => negLe p.2 mx
  else none

theorem linCauseMinPairFast_eq (st : State) (p : Int × Nat) :
    linCauseMinPairFast st p = linCauseMinPair st p := by
  unfold linCauseMinPairFast linCauseMinPair
  rw [minInt?_eq_domMinI, maxInt?_eq_domMaxI]

attribute [implemented_by linCauseMinPairFast] linCauseMinPair

/-- The max-contribution cause of a term: the dual discipline.
    `ct > 0` contributes `ct·mx` at `x ≤ mx` (cause `x > mx`);
    `ct < 0` contributes `ct·mn` at `x ≥ mn` (cause `x ≤ mn−1`);
    `ct = 0` contributes 0 (no pin needed). -/
def linCauseMaxPair (st : State) (p : Int × Nat) : Option Literal :=
  if p.1 > 0 then
    (domMaxI (st.domains.getD p.2 Dom.empty)).map fun mx => negLe p.2 mx
  else if p.1 < 0 then
    (domMinI (st.domains.getD p.2 Dom.empty)).map fun mn => posLe p.2 (mn - 1)
  else none

/-- Structural twin of `linCauseMaxPair`. -/
def linCauseMaxPairFast (st : State) (p : Int × Nat) : Option Literal :=
  if p.1 > 0 then
    (Dom.maxInt? (st.domains.getD p.2 Dom.empty)).map fun mx => negLe p.2 mx
  else if p.1 < 0 then
    (Dom.minInt? (st.domains.getD p.2 Dom.empty)).map fun mn => posLe p.2 (mn - 1)
  else none

theorem linCauseMaxPairFast_eq (st : State) (p : Int × Nat) :
    linCauseMaxPairFast st p = linCauseMaxPair st p := by
  unfold linCauseMaxPairFast linCauseMaxPair
  rw [minInt?_eq_domMinI, maxInt?_eq_domMaxI]

attribute [implemented_by linCauseMaxPairFast] linCauseMaxPair

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

/-
Cached-bounds fast twin of `propLinEq2`.

`propLinEq2`'s per-sweep-step work is bound by `List.getD` on the frame
spine: one `linDeduceEq` call performs several hundred `st.domains.getD`
lookups (one per rest term, repeated in the guard, the min-sum, the
max-sum and the cause lists).  The logical code re-reads every slot from
the whole frame list on every visit.

The twin reads the (at most `is.length`) distinct slot bounds ONCE per
propagator call into a tiny association list, then serves every later
lookup from that cache, falling back to the frame for slots outside
`is` (so the correctness statement needs no membership side
conditions).  Every definition below is a literal transcription of its
logical counterpart with `st.domains.getD · Dom.empty` replaced by a
bounds function; the equality theorem bottoms out in
`minInt?_eq_domMinI`/`maxInt?_eq_domMaxI`.
-/

/-- The cached integer bounds of a domain (the two extrema the deduction
    kernel reads). -/
def linBounds (d : Domain) : Option Int × Option Int :=
  (d.minInt?, d.maxInt?)

/-- Bounds of the slots `is`, read once from the frame. -/
def linCache (st : State) (is : List Nat) : List (Nat × Option Int × Option Int) :=
  is.map fun s =>
    let d := st.domains.getD s Dom.empty
    (s, linBounds d)

/-- Bounds lookup with frame fallback. -/
def linLookupB (st : State) (cache : List (Nat × Option Int × Option Int)) (s : Nat) :
    Option Int × Option Int :=
  match cache.find? (fun p => p.1 == s) with
  | some p => p.2
  | none => linBounds (st.domains.getD s Dom.empty)

/-- Every element of a cache produced by `linCache` stores the bounds of
    its own slot. -/
theorem linLookupB_aux (st : State) (l : List (Nat × Option Int × Option Int))
    (s : Nat) (h : ∀ q ∈ l, q.2 = linBounds (st.domains.getD q.1 Dom.empty)) :
    linLookupB st l s = linBounds (st.domains.getD s Dom.empty) := by
  unfold linLookupB
  induction l with
  | nil => rfl
  | cons q qs ih =>
      by_cases hq : (q.1 == s) = true
      · rw [List.find?_cons_of_pos (p := fun p : Nat × Option Int × Option Int => p.1 == s)
          (a := q) (l := qs) hq]
        dsimp only
        rw [← beq_iff_eq.mp hq]
        exact h q List.mem_cons_self
      · rw [List.find?_cons_of_neg (p := fun p : Nat × Option Int × Option Int => p.1 == s)
          (a := q) (l := qs) hq]
        exact ih fun p hp => h p (List.mem_cons_of_mem q hp)

/-- The cache lookup agrees with the frame on every slot. -/
theorem linLookupB_eq (st : State) (is : List Nat) (s : Nat) :
    linLookupB st (linCache st is) s = linBounds (st.domains.getD s Dom.empty) := by
  refine linLookupB_aux st (linCache st is) s ?_
  intro q hq
  obtain ⟨t, _, ht⟩ := List.mem_map.mp hq
  rw [← ht]

/-- Cached twin of `minContrib`. -/
def minContribB (f : Nat → Option Int × Option Int) (p : Int × Nat) :
    Option (Nat × Int × Int) :=
  let q := f p.2
  match q.1, q.2 with
  | some mn, some mx =>
      if p.1 ≥ 0 then some (p.2, p.1, p.1 * mn) else some (p.2, p.1, p.1 * mx)
  | _, _ => none

theorem minContribB_eq (st : State) (f : Nat → Option Int × Option Int)
    (h : ∀ s, f s = linBounds (st.domains.getD s Dom.empty)) (p : Int × Nat) :
    minContribB f p = minContrib st p := by
  simp only [minContribB, minContrib, linBounds, h p.2,
    minInt?_eq_domMinI, maxInt?_eq_domMaxI]

/-- Cached twin of `maxContrib`. -/
def maxContribB (f : Nat → Option Int × Option Int) (p : Int × Nat) :
    Option (Nat × Int × Int) :=
  let q := f p.2
  match q.1, q.2 with
  | some mn, some mx =>
      if p.1 ≥ 0 then some (p.2, p.1, p.1 * mx) else some (p.2, p.1, p.1 * mn)
  | _, _ => none

theorem maxContribB_eq (st : State) (f : Nat → Option Int × Option Int)
    (h : ∀ s, f s = linBounds (st.domains.getD s Dom.empty)) (p : Int × Nat) :
    maxContribB f p = maxContrib st p := by
  simp only [maxContribB, maxContrib, linBounds, h p.2,
    minInt?_eq_domMinI, maxInt?_eq_domMaxI]

/-- Cached twin of `sumMin`. -/
def sumMinB (f : Nat → Option Int × Option Int) : List (Int × Nat) → Option Int
  | [] => none
  | p :: rest =>
      match minContribB f p with
      | none => sumMinB f rest
      | some t =>
          match sumMinB f rest with
          | none => some t.2.2
          | some s => some (s + t.2.2)

theorem sumMinB_eq (st : State) (f : Nat → Option Int × Option Int)
    (h : ∀ s, f s = linBounds (st.domains.getD s Dom.empty)) :
    ∀ rest, sumMinB f rest = sumMin st rest
  | [] => rfl
  | p :: rest => by
      simp only [sumMinB, sumMin, minContribB_eq st f h p,
        sumMinB_eq st f h rest]

/-- Cached twin of `sumMax`. -/
def sumMaxB (f : Nat → Option Int × Option Int) : List (Int × Nat) → Option Int
  | [] => none
  | p :: rest =>
      match maxContribB f p with
      | none => sumMaxB f rest
      | some t =>
          match sumMaxB f rest with
          | none => some t.2.2
          | some s => some (s + t.2.2)

theorem sumMaxB_eq (st : State) (f : Nat → Option Int × Option Int)
    (h : ∀ s, f s = linBounds (st.domains.getD s Dom.empty)) :
    ∀ rest, sumMaxB f rest = sumMax st rest
  | [] => rfl
  | p :: rest => by
      simp only [sumMaxB, sumMax, maxContribB_eq st f h p,
        sumMaxB_eq st f h rest]

/-- Cached twin of `linCauseMinPair`. -/
def linCauseMinPairB (f : Nat → Option Int × Option Int) (p : Int × Nat) :
    Option Literal :=
  let q := f p.2
  if p.1 > 0 then
    q.1.map fun mn => posLe p.2 (mn - 1)
  else if p.1 < 0 then
    q.2.map fun mx => negLe p.2 mx
  else none

theorem linCauseMinPairB_eq (st : State) (f : Nat → Option Int × Option Int)
    (h : ∀ s, f s = linBounds (st.domains.getD s Dom.empty)) (p : Int × Nat) :
    linCauseMinPairB f p = linCauseMinPair st p := by
  simp only [linCauseMinPairB, linCauseMinPair, linBounds, h p.2,
    minInt?_eq_domMinI, maxInt?_eq_domMaxI]

/-- Cached twin of `linCauseMaxPair`. -/
def linCauseMaxPairB (f : Nat → Option Int × Option Int) (p : Int × Nat) :
    Option Literal :=
  let q := f p.2
  if p.1 > 0 then
    q.2.map fun mx => negLe p.2 mx
  else if p.1 < 0 then
    q.1.map fun mn => posLe p.2 (mn - 1)
  else none

theorem linCauseMaxPairB_eq (st : State) (f : Nat → Option Int × Option Int)
    (h : ∀ s, f s = linBounds (st.domains.getD s Dom.empty)) (p : Int × Nat) :
    linCauseMaxPairB f p = linCauseMaxPair st p := by
  simp only [linCauseMaxPairB, linCauseMaxPair, linBounds, h p.2,
    minInt?_eq_domMinI, maxInt?_eq_domMaxI]

/-- Cached twin of `linCausesMin`. -/
def linCausesMinB (f : Nat → Option Int × Option Int) (rest : List (Int × Nat)) :
    Clause :=
  rest.filterMap (linCauseMinPairB f)

theorem linCausesMinB_eq (st : State) (f : Nat → Option Int × Option Int)
    (h : ∀ s, f s = linBounds (st.domains.getD s Dom.empty))
    (rest : List (Int × Nat)) :
    linCausesMinB f rest = linCausesMin st rest := by
  unfold linCausesMinB linCausesMin
  induction rest with
  | nil => rfl
  | cons p ps ih =>
      rw [List.filterMap_cons, List.filterMap_cons,
        linCauseMinPairB_eq st f h p, ih]

/-- Cached twin of `linCausesMax`. -/
def linCausesMaxB (f : Nat → Option Int × Option Int) (rest : List (Int × Nat)) :
    Clause :=
  rest.filterMap (linCauseMaxPairB f)

theorem linCausesMaxB_eq (st : State) (f : Nat → Option Int × Option Int)
    (h : ∀ s, f s = linBounds (st.domains.getD s Dom.empty))
    (rest : List (Int × Nat)) :
    linCausesMaxB f rest = linCausesMax st rest := by
  unfold linCausesMaxB linCausesMax
  induction rest with
  | nil => rfl
  | cons p ps ih =>
      rw [List.filterMap_cons, List.filterMap_cons,
        linCauseMaxPairB_eq st f h p, ih]

/-- Cached twin of `narrowHi`. -/
def narrowHiB (f : Nat → Option Int × Option Int) (s : Nat) (hi : Int)
    (ng : Clause) : PropagationResult :=
  let q := f s
  match q.1, q.2 with
  | some mn, some mx =>
      if mn > hi then .conflict ng
      else if decide (hi < mx) then
        .implied (posLe s hi) { clause := ng }
      else .stable
  | _, _ => .stable

theorem narrowHiB_eq (st : State) (f : Nat → Option Int × Option Int)
    (h : ∀ s, f s = linBounds (st.domains.getD s Dom.empty)) (s : Nat)
    (hi : Int) (ng : Clause) :
    narrowHiB f s hi ng = narrowHi st s hi ng := by
  simp only [narrowHiB, narrowHi, linBounds, h s,
    minInt?_eq_domMinI, maxInt?_eq_domMaxI]
  rfl

/-- Cached twin of `narrowLo`. -/
def narrowLoB (f : Nat → Option Int × Option Int) (s : Nat) (lo : Int)
    (ng : Clause) : PropagationResult :=
  let q := f s
  match q.1, q.2 with
  | some mn, some mx =>
      if mx < lo then .conflict ng
      else if decide (mn < lo) then
        .implied (negLe s (lo - 1)) { clause := ng }
      else .stable
  | _, _ => .stable

theorem narrowLoB_eq (st : State) (f : Nat → Option Int × Option Int)
    (h : ∀ s, f s = linBounds (st.domains.getD s Dom.empty)) (s : Nat)
    (lo : Int) (ng : Clause) :
    narrowLoB f s lo ng = narrowLo st s lo ng := by
  simp only [narrowLoB, narrowLo, linBounds, h s,
    minInt?_eq_domMinI, maxInt?_eq_domMaxI]
  rfl

/-- Cached twin of `linEqArmHiMin`. -/
def linEqArmHiMinB (f : Nat → Option Int × Option Int) (m : Nat) (b : Int)
    (rest : List (Int × Nat)) : Option Int → PropagationResult
  | some lr => narrowHiB f m (b - lr) ([posLe m (b - lr)] ++ linCausesMinB f rest)
  | none => .stable

theorem linEqArmHiMinB_eq (st : State) (f : Nat → Option Int × Option Int)
    (h : ∀ s, f s = linBounds (st.domains.getD s Dom.empty)) (m : Nat) (b : Int)
    (rest : List (Int × Nat)) (o : Option Int) :
    linEqArmHiMinB f m b rest o = linEqArmHiMin st m b rest o := by
  cases o with
  | none => rfl
  | some lr =>
      simp only [linEqArmHiMinB, linEqArmHiMin, narrowHiB_eq st f h,
        linCausesMinB_eq st f h]

/-- Cached twin of `linEqArmLoMax`. -/
def linEqArmLoMaxB (f : Nat → Option Int × Option Int) (m : Nat) (b : Int)
    (rest : List (Int × Nat)) : Option Int → PropagationResult
  | some hr => narrowLoB f m (b - hr) ([negLe m (b - hr - 1)] ++ linCausesMaxB f rest)
  | none => .stable

theorem linEqArmLoMaxB_eq (st : State) (f : Nat → Option Int × Option Int)
    (h : ∀ s, f s = linBounds (st.domains.getD s Dom.empty)) (m : Nat) (b : Int)
    (rest : List (Int × Nat)) (o : Option Int) :
    linEqArmLoMaxB f m b rest o = linEqArmLoMax st m b rest o := by
  cases o with
  | none => rfl
  | some hr =>
      simp only [linEqArmLoMaxB, linEqArmLoMax, narrowLoB_eq st f h,
        linCausesMaxB_eq st f h]

/-- Cached twin of `linEqArmLoMin`. -/
def linEqArmLoMinB (f : Nat → Option Int × Option Int) (m : Nat) (b : Int)
    (rest : List (Int × Nat)) : Option Int → PropagationResult
  | some lr => narrowLoB f m (lr - b) ([negLe m (lr - b - 1)] ++ linCausesMinB f rest)
  | none => .stable

theorem linEqArmLoMinB_eq (st : State) (f : Nat → Option Int × Option Int)
    (h : ∀ s, f s = linBounds (st.domains.getD s Dom.empty)) (m : Nat) (b : Int)
    (rest : List (Int × Nat)) (o : Option Int) :
    linEqArmLoMinB f m b rest o = linEqArmLoMin st m b rest o := by
  cases o with
  | none => rfl
  | some lr =>
      simp only [linEqArmLoMinB, linEqArmLoMin, narrowLoB_eq st f h,
        linCausesMinB_eq st f h]

/-- Cached twin of `linEqArmHiMax`. -/
def linEqArmHiMaxB (f : Nat → Option Int × Option Int) (m : Nat) (b : Int)
    (rest : List (Int × Nat)) : Option Int → PropagationResult
  | some hr => narrowHiB f m (hr - b) ([posLe m (hr - b)] ++ linCausesMaxB f rest)
  | none => .stable

theorem linEqArmHiMaxB_eq (st : State) (f : Nat → Option Int × Option Int)
    (h : ∀ s, f s = linBounds (st.domains.getD s Dom.empty)) (m : Nat) (b : Int)
    (rest : List (Int × Nat)) (o : Option Int) :
    linEqArmHiMaxB f m b rest o = linEqArmHiMax st m b rest o := by
  cases o with
  | none => rfl
  | some hr =>
      simp only [linEqArmHiMaxB, linEqArmHiMax, narrowHiB_eq st f h,
        linCausesMaxB_eq st f h]

/-- Cached twin of `linGenArmHiMin`. -/
def linGenArmHiMinB (f : Nat → Option Int × Option Int) (m : Nat) (b c : Int)
    (rest : List (Int × Nat)) : Option Int → PropagationResult
  | some lr => narrowHiB f m ((b - lr) / c)
      ([posLe m ((b - lr) / c)] ++ linCausesMinB f rest)
  | none => .stable

theorem linGenArmHiMinB_eq (st : State) (f : Nat → Option Int × Option Int)
    (h : ∀ s, f s = linBounds (st.domains.getD s Dom.empty)) (m : Nat) (b c : Int)
    (rest : List (Int × Nat)) (o : Option Int) :
    linGenArmHiMinB f m b c rest o = linGenArmHiMin st m b c rest o := by
  cases o with
  | none => rfl
  | some lr =>
      simp only [linGenArmHiMinB, linGenArmHiMin, narrowHiB_eq st f h,
        linCausesMinB_eq st f h]

/-- Cached twin of `linGenArmLoMin`. -/
def linGenArmLoMinB (f : Nat → Option Int × Option Int) (m : Nat) (b c : Int)
    (rest : List (Int × Nat)) : Option Int → PropagationResult
  | some lr => narrowLoB f m (-((b - lr) / (-c)))
      ([negLe m (-((b - lr) / (-c)) - 1)] ++ linCausesMinB f rest)
  | none => .stable

theorem linGenArmLoMinB_eq (st : State) (f : Nat → Option Int × Option Int)
    (h : ∀ s, f s = linBounds (st.domains.getD s Dom.empty)) (m : Nat) (b c : Int)
    (rest : List (Int × Nat)) (o : Option Int) :
    linGenArmLoMinB f m b c rest o = linGenArmLoMin st m b c rest o := by
  cases o with
  | none => rfl
  | some lr =>
      simp only [linGenArmLoMinB, linGenArmLoMin, narrowLoB_eq st f h,
        linCausesMinB_eq st f h]

/-- Cached twin of `linGenArmLoMax`. -/
def linGenArmLoMaxB (f : Nat → Option Int × Option Int) (m : Nat) (b c : Int)
    (rest : List (Int × Nat)) : Option Int → PropagationResult
  | some hr => narrowLoB f m (-((hr - b) / c))
      ([negLe m (-((hr - b) / c) - 1)] ++ linCausesMaxB f rest)
  | none => .stable

theorem linGenArmLoMaxB_eq (st : State) (f : Nat → Option Int × Option Int)
    (h : ∀ s, f s = linBounds (st.domains.getD s Dom.empty)) (m : Nat) (b c : Int)
    (rest : List (Int × Nat)) (o : Option Int) :
    linGenArmLoMaxB f m b c rest o = linGenArmLoMax st m b c rest o := by
  cases o with
  | none => rfl
  | some hr =>
      simp only [linGenArmLoMaxB, linGenArmLoMax, narrowLoB_eq st f h,
        linCausesMaxB_eq st f h]

/-- Cached twin of `linGenArmHiMax`. -/
def linGenArmHiMaxB (f : Nat → Option Int × Option Int) (m : Nat) (b c : Int)
    (rest : List (Int × Nat)) : Option Int → PropagationResult
  | some hr => narrowHiB f m ((hr - b) / (-c))
      ([posLe m ((hr - b) / (-c))] ++ linCausesMaxB f rest)
  | none => .stable

theorem linGenArmHiMaxB_eq (st : State) (f : Nat → Option Int × Option Int)
    (h : ∀ s, f s = linBounds (st.domains.getD s Dom.empty)) (m : Nat) (b c : Int)
    (rest : List (Int × Nat)) (o : Option Int) :
    linGenArmHiMaxB f m b c rest o = linGenArmHiMax st m b c rest o := by
  cases o with
  | none => rfl
  | some hr =>
      simp only [linGenArmHiMaxB, linGenArmHiMax, narrowHiB_eq st f h,
        linCausesMaxB_eq st f h]

/-- Cached twin of `linDeduceEq`. -/
def linDeduceEqB (f : Nat → Option Int × Option Int) (b : Int) (m : Nat) (c : Int)
    (rest : List (Int × Nat)) : PropagationResult :=
  if rest.all (fun p => (minContribB f p).isSome) then
    if c = 1 then
      firstEvent
        [ linEqArmHiMinB f m b rest (sumMinB f rest)
        , linEqArmLoMaxB f m b rest (sumMaxB f rest) ]
    else if c = -1 then
      firstEvent
        [ linEqArmLoMinB f m b rest (sumMinB f rest)
        , linEqArmHiMaxB f m b rest (sumMaxB f rest) ]
    else if c > 0 then
      firstEvent
        [ linGenArmHiMinB f m b c rest (sumMinB f rest)
        , linGenArmLoMaxB f m b c rest (sumMaxB f rest) ]
    else if c < 0 then
      firstEvent
        [ linGenArmLoMinB f m b c rest (sumMinB f rest)
        , linGenArmHiMaxB f m b c rest (sumMaxB f rest) ]
    else .stable
  else .stable

theorem linDeduceEqB_eq (st : State) (f : Nat → Option Int × Option Int)
    (h : ∀ s, f s = linBounds (st.domains.getD s Dom.empty)) (b : Int) (m : Nat)
    (c : Int) (rest : List (Int × Nat)) :
    linDeduceEqB f b m c rest = linDeduceEq st b m c rest := by
  unfold linDeduceEqB linDeduceEq
  rw [List.all_congr rfl (fun p => by rw [minContribB_eq st f h p])]
  by_cases h1 : c = 1
  · rw [if_pos h1, if_pos h1, sumMinB_eq st f h, sumMaxB_eq st f h,
      linEqArmHiMinB_eq st f h, linEqArmLoMaxB_eq st f h]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : c = -1
    · rw [if_pos h2, if_pos h2, sumMinB_eq st f h, sumMaxB_eq st f h,
        linEqArmLoMinB_eq st f h, linEqArmHiMaxB_eq st f h]
    · rw [if_neg h2, if_neg h2]
      by_cases h3 : c > 0
      · rw [if_pos h3, if_pos h3, sumMinB_eq st f h, sumMaxB_eq st f h,
          linGenArmHiMinB_eq st f h, linGenArmLoMaxB_eq st f h]
      · rw [if_neg h3, if_neg h3]
        by_cases h4 : c < 0
        · rw [if_pos h4, if_pos h4, sumMinB_eq st f h, sumMaxB_eq st f h,
            linGenArmLoMinB_eq st f h, linGenArmHiMaxB_eq st f h]
        · rw [if_neg h4, if_neg h4]

/-- Congruence of the sweep in the deduction kernel. -/
theorem linSweep_congr (coeffs : List Int) (is : List Nat)
    (f g : Nat → Int → List (Int × Nat) → PropagationResult)
    (h : ∀ m c rest, f m c rest = g m c rest) :
    ∀ ps idx, linSweep coeffs is f ps idx = linSweep coeffs is g ps idx
  | [], _ => rfl
  | ((c, m), i) :: rest, idx => by
      simp only [linSweep]
      rw [h m c]
      split
      · exact linSweep_congr coeffs is f g h rest (idx + 1)
      · rfl

/-- Cached-bounds twin of `propLinEq2`: read each involved slot's bounds
    once, then sweep with the bound-parameterised kernel. -/
def propLinEq2Fast (st : State) (coeffs : List Int) (is : List Nat) (b : Int) :
    PropagationResult :=
  match coeffs.zip is with
  | [] => .stable
  | ps =>
      let cache := linCache st is
      linSweep coeffs is (linDeduceEqB (linLookupB st cache) b) ps.zipIdx 0

theorem propLinEq2Fast_eq (st : State) (coeffs : List Int) (is : List Nat)
    (b : Int) :
    propLinEq2Fast st coeffs is b = propLinEq2 st coeffs is b := by
  unfold propLinEq2Fast propLinEq2
  cases hz : coeffs.zip is with
  | nil => rfl
  | cons p ps =>
      dsimp only
      exact linSweep_congr coeffs is _ _
        (fun m c rest => linDeduceEqB_eq st _ (linLookupB_eq st is) b m c rest) _ 0

attribute [implemented_by propLinEq2Fast] propLinEq2

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
  domains := [Dom.ofList [Value.int (-2), Value.int 3, Value.int 5],
    Dom.ofList [Value.int (-2), Value.int 10]]
  constraints := [DomConstraint.linLe [1, 2] [0, 1] 0]
  objective := ()
  clauses := []

/-- The witness state (the obstruction's `stI`): slot-`x`'s domain
    read `{0,5}` (min 0), slot-`t`'s domain read `{0,10}`. -/
def linLe2_stI : State where
  domains := [Dom.ofList [Value.int 0, Value.int 5],
    Dom.ofList [Value.int 0, Value.int 10]]
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
  domains := [Dom.ofList [Value.int 0, Value.int 5],
    Dom.ofList [Value.int 1, Value.int 3]]
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
        have hdom : Dom.enum (linLe2_probI.domains.getD 0 Dom.empty)
            = [Value.int (-2), Value.int 3, Value.int 5] := rfl
        have hmem : Value.int 3 ∈ Dom.enum (linLe2_probI.domains.getD 0 Dom.empty) := by
          rw [hdom]
          exact List.mem_cons_of_mem _ (List.mem_cons_self)
        exact (DomainLike.mem_iff _ _).mpr hmem
    | succ n =>
        have hn : n = 0 := by omega
        subst hn
        have hv2 : linLe2_aI[1]? = some value := hv
        rw [show linLe2_aI[1]? = some (Value.int (-2)) from rfl] at hv2
        injection hv2 with hv3
        rw [← hv3]
        have hdom : Dom.enum (linLe2_probI.domains.getD 1 Dom.empty)
            = [Value.int (-2), Value.int 10] := rfl
        have hmem : Value.int (-2) ∈ Dom.enum (linLe2_probI.domains.getD 1 Dom.empty) := by
          rw [hdom]
          exact List.mem_cons_self
        exact (DomainLike.mem_iff _ _).mpr hmem
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
    ∃ mn mx, domMinI (st.domains.getD p.2 Dom.empty) = some mn ∧
      domMaxI (st.domains.getD p.2 Dom.empty) = some mx ∧
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
    ∃ mn mx, domMinI (st.domains.getD p.2 Dom.empty) = some mn ∧
      domMaxI (st.domains.getD p.2 Dom.empty) = some mx ∧
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

/-! ## Locality of the linear-family kernels (PLAN P1 scheduled scan)

Every read of the kernels below goes through `st.domains.getD s Dom.empty` for a
slot `s` drawn from the constraint's slot list: the contribution sums and
cause lists read only the pairs' slots, the deduction arms read the passed
rest list's slots plus the narrowed slot `m`, and the sweeps draw their
slots from `coeffs.zip is`. These lemmas record that pointwise-equal
domains on the read slots yield equal runs — the `PropLocalOne` premiss
of the scheduled scan's equivalence theorems, instantiated for the
concrete registrations in `ScheduledFamilies.lean`. -/

/-- `filterMap` respects a pointwise-equal function on a list. -/
theorem lin2_filterMap_local {α β : Type} {f g : α → Option β} {l : List α}
    (h : ∀ a ∈ l, f a = g a) :
    l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      have ha := h a (List.mem_cons_self ..)
      have hl := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
      simp only [List.filterMap_cons, ha, hl]

/-- `narrowHi` reads only its slot's domain. -/
theorem linNarrowHi_local {s : Nat} {hi : Int} {ng : Clause} {st1 st2 : State}
    (h : st1.domains.getD s Dom.empty = st2.domains.getD s Dom.empty) :
    narrowHi st1 s hi ng = narrowHi st2 s hi ng := by
  simp only [narrowHi, h]

/-- `narrowLo` reads only its slot's domain. -/
theorem linNarrowLo_local {s : Nat} {lo : Int} {ng : Clause} {st1 st2 : State}
    (h : st1.domains.getD s Dom.empty = st2.domains.getD s Dom.empty) :
    narrowLo st1 s lo ng = narrowLo st2 s lo ng := by
  simp only [narrowLo, h]

/-- `minContrib` reads only the pair's slot. -/
theorem minContrib_local {st1 st2 : State} {p : Int × Nat}
    (h : st1.domains.getD p.2 Dom.empty = st2.domains.getD p.2 Dom.empty) :
    minContrib st1 p = minContrib st2 p := by
  simp only [minContrib, h]

/-- `maxContrib` reads only the pair's slot. -/
theorem maxContrib_local {st1 st2 : State} {p : Int × Nat}
    (h : st1.domains.getD p.2 Dom.empty = st2.domains.getD p.2 Dom.empty) :
    maxContrib st1 p = maxContrib st2 p := by
  simp only [maxContrib, h]

/-- The min-contribution sum depends only on the pairs' slots. -/
theorem sumMin_local {st1 st2 : State} {ps : List (Int × Nat)}
    (h : ∀ p ∈ ps, st1.domains.getD p.2 Dom.empty = st2.domains.getD p.2 Dom.empty) :
    sumMin st1 ps = sumMin st2 ps := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
      have hp := minContrib_local (h p (List.mem_cons_self ..))
      have hr := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
      rw [sumMin, sumMin, hp, hr]

/-- The max-contribution sum depends only on the pairs' slots. -/
theorem sumMax_local {st1 st2 : State} {ps : List (Int × Nat)}
    (h : ∀ p ∈ ps, st1.domains.getD p.2 Dom.empty = st2.domains.getD p.2 Dom.empty) :
    sumMax st1 ps = sumMax st2 ps := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
      have hp := maxContrib_local (h p (List.mem_cons_self ..))
      have hr := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
      rw [sumMax, sumMax, hp, hr]

/-- The min-contribution cause reads only the pair's slot. -/
theorem linCauseMinPair_local {st1 st2 : State} {p : Int × Nat}
    (h : st1.domains.getD p.2 Dom.empty = st2.domains.getD p.2 Dom.empty) :
    linCauseMinPair st1 p = linCauseMinPair st2 p := by
  simp only [linCauseMinPair, h]

/-- The max-contribution cause reads only the pair's slot. -/
theorem linCauseMaxPair_local {st1 st2 : State} {p : Int × Nat}
    (h : st1.domains.getD p.2 Dom.empty = st2.domains.getD p.2 Dom.empty) :
    linCauseMaxPair st1 p = linCauseMaxPair st2 p := by
  simp only [linCauseMaxPair, h]

/-- The min-cause list depends only on the pairs' slots. -/
theorem linCausesMin_local {st1 st2 : State} {rest : List (Int × Nat)}
    (h : ∀ p ∈ rest, st1.domains.getD p.2 Dom.empty = st2.domains.getD p.2 Dom.empty) :
    linCausesMin st1 rest = linCausesMin st2 rest :=
  lin2_filterMap_local (fun p hp => linCauseMinPair_local (h p hp))

/-- The max-cause list depends only on the pairs' slots. -/
theorem linCausesMax_local {st1 st2 : State} {rest : List (Int × Nat)}
    (h : ∀ p ∈ rest, st1.domains.getD p.2 Dom.empty = st2.domains.getD p.2 Dom.empty) :
    linCausesMax st1 rest = linCausesMax st2 rest :=
  lin2_filterMap_local (fun p hp => linCauseMaxPair_local (h p hp))

/-- The `c > 0` upper-bound arm reads only the narrowed slot and the
    rest list's slots. -/
theorem linGenArmHiMin_local {st1 st2 : State} {m : Nat} {b c : Int}
    {rest : List (Int × Nat)} (o : Option Int)
    (hm : st1.domains.getD m Dom.empty = st2.domains.getD m Dom.empty)
    (hc : linCausesMin st1 rest = linCausesMin st2 rest) :
    linGenArmHiMin st1 m b c rest o = linGenArmHiMin st2 m b c rest o := by
  cases o with
  | none => rfl
  | some lr =>
      unfold linGenArmHiMin
      rw [hc]
      exact linNarrowHi_local hm

/-- The `c < 0` lower-bound arm reads only the narrowed slot and the
    rest list's slots. -/
theorem linGenArmLoMin_local {st1 st2 : State} {m : Nat} {b c : Int}
    {rest : List (Int × Nat)} (o : Option Int)
    (hm : st1.domains.getD m Dom.empty = st2.domains.getD m Dom.empty)
    (hc : linCausesMin st1 rest = linCausesMin st2 rest) :
    linGenArmLoMin st1 m b c rest o = linGenArmLoMin st2 m b c rest o := by
  cases o with
  | none => rfl
  | some lr =>
      unfold linGenArmLoMin
      rw [hc]
      exact linNarrowLo_local hm

/-- The `c > 0` equality lower-bound arm reads only the narrowed slot and
    the rest list's slots. -/
theorem linGenArmLoMax_local {st1 st2 : State} {m : Nat} {b c : Int}
    {rest : List (Int × Nat)} (o : Option Int)
    (hm : st1.domains.getD m Dom.empty = st2.domains.getD m Dom.empty)
    (hc : linCausesMax st1 rest = linCausesMax st2 rest) :
    linGenArmLoMax st1 m b c rest o = linGenArmLoMax st2 m b c rest o := by
  cases o with
  | none => rfl
  | some hr =>
      unfold linGenArmLoMax
      rw [hc]
      exact linNarrowLo_local hm

/-- The `c < 0` equality upper-bound arm reads only the narrowed slot and
    the rest list's slots. -/
theorem linGenArmHiMax_local {st1 st2 : State} {m : Nat} {b c : Int}
    {rest : List (Int × Nat)} (o : Option Int)
    (hm : st1.domains.getD m Dom.empty = st2.domains.getD m Dom.empty)
    (hc : linCausesMax st1 rest = linCausesMax st2 rest) :
    linGenArmHiMax st1 m b c rest o = linGenArmHiMax st2 m b c rest o := by
  cases o with
  | none => rfl
  | some hr =>
      unfold linGenArmHiMax
      rw [hc]
      exact linNarrowHi_local hm

/-- The `x_m ≤ b − loRest` eq arm reads only the narrowed slot and the
    rest list's slots. -/
theorem linEqArmHiMin_local {st1 st2 : State} {m : Nat} {b : Int}
    {rest : List (Int × Nat)} (o : Option Int)
    (hm : st1.domains.getD m Dom.empty = st2.domains.getD m Dom.empty)
    (hc : linCausesMin st1 rest = linCausesMin st2 rest) :
    linEqArmHiMin st1 m b rest o = linEqArmHiMin st2 m b rest o := by
  cases o with
  | none => rfl
  | some lr =>
      unfold linEqArmHiMin
      rw [hc]
      exact linNarrowHi_local hm

/-- The `x_m ≥ b − hiRest` eq arm reads only the narrowed slot and the
    rest list's slots. -/
theorem linEqArmLoMax_local {st1 st2 : State} {m : Nat} {b : Int}
    {rest : List (Int × Nat)} (o : Option Int)
    (hm : st1.domains.getD m Dom.empty = st2.domains.getD m Dom.empty)
    (hc : linCausesMax st1 rest = linCausesMax st2 rest) :
    linEqArmLoMax st1 m b rest o = linEqArmLoMax st2 m b rest o := by
  cases o with
  | none => rfl
  | some hr =>
      unfold linEqArmLoMax
      rw [hc]
      exact linNarrowLo_local hm

/-- The `x_m ≥ loRest − b` eq arm reads only the narrowed slot and the
    rest list's slots. -/
theorem linEqArmLoMin_local {st1 st2 : State} {m : Nat} {b : Int}
    {rest : List (Int × Nat)} (o : Option Int)
    (hm : st1.domains.getD m Dom.empty = st2.domains.getD m Dom.empty)
    (hc : linCausesMin st1 rest = linCausesMin st2 rest) :
    linEqArmLoMin st1 m b rest o = linEqArmLoMin st2 m b rest o := by
  cases o with
  | none => rfl
  | some lr =>
      unfold linEqArmLoMin
      rw [hc]
      exact linNarrowLo_local hm

/-- The `x_m ≤ hiRest − b` eq arm reads only the narrowed slot and the
    rest list's slots. -/
theorem linEqArmHiMax_local {st1 st2 : State} {m : Nat} {b : Int}
    {rest : List (Int × Nat)} (o : Option Int)
    (hm : st1.domains.getD m Dom.empty = st2.domains.getD m Dom.empty)
    (hc : linCausesMax st1 rest = linCausesMax st2 rest) :
    linEqArmHiMax st1 m b rest o = linEqArmHiMax st2 m b rest o := by
  cases o with
  | none => rfl
  | some hr =>
      unfold linEqArmHiMax
      rw [hc]
      exact linNarrowHi_local hm

/-- The completeness guard depends only on the rest list's slots. -/
theorem all_minContrib_isSome_local {st1 st2 : State} {rest : List (Int × Nat)}
    (h : ∀ p ∈ rest, st1.domains.getD p.2 Dom.empty = st2.domains.getD p.2 Dom.empty) :
    rest.all (fun p => (minContrib st1 p).isSome) =
      rest.all (fun p => (minContrib st2 p).isSome) := by
  induction rest with
  | nil => rfl
  | cons p rest ih =>
      have hp := minContrib_local (h p (List.mem_cons_self ..))
      have hr := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
      simp only [List.all_cons, hp, hr]

/-- `linDeduceLe` reads only the narrowed slot `m` and the rest list's
    slots. -/
theorem linDeduceLe_local {st1 st2 : State} {b : Int} {m : Nat} {c : Int}
    {rest : List (Int × Nat)}
    (hm : st1.domains.getD m Dom.empty = st2.domains.getD m Dom.empty)
    (hrest : ∀ p ∈ rest, st1.domains.getD p.2 Dom.empty = st2.domains.getD p.2 Dom.empty) :
    linDeduceLe st1 b m c rest = linDeduceLe st2 b m c rest := by
  have hall := all_minContrib_isSome_local hrest
  have hsum := sumMin_local hrest
  have hcm := linCausesMin_local hrest
  have hhi : ∀ o, linGenArmHiMin st1 m b c rest o = linGenArmHiMin st2 m b c rest o :=
    fun o => linGenArmHiMin_local o hm hcm
  have hlo : ∀ o, linGenArmLoMin st1 m b c rest o = linGenArmLoMin st2 m b c rest o :=
    fun o => linGenArmLoMin_local o hm hcm
  unfold linDeduceLe
  rw [hall, hsum, hcm]
  simp only [linNarrowHi_local hm, linNarrowLo_local hm, hhi, hlo]

/-- `linDeduceEq` reads only the narrowed slot `m` and the rest list's
    slots. -/
theorem linDeduceEq_local {st1 st2 : State} {b : Int} {m : Nat} {c : Int}
    {rest : List (Int × Nat)}
    (hm : st1.domains.getD m Dom.empty = st2.domains.getD m Dom.empty)
    (hrest : ∀ p ∈ rest, st1.domains.getD p.2 Dom.empty = st2.domains.getD p.2 Dom.empty) :
    linDeduceEq st1 b m c rest = linDeduceEq st2 b m c rest := by
  have hall := all_minContrib_isSome_local hrest
  have hsum := sumMin_local hrest
  have hmax := sumMax_local hrest
  have hcm := linCausesMin_local hrest
  have hcx := linCausesMax_local hrest
  have h1 : ∀ o, linEqArmHiMin st1 m b rest o = linEqArmHiMin st2 m b rest o :=
    fun o => linEqArmHiMin_local o hm hcm
  have h2 : ∀ o, linEqArmLoMax st1 m b rest o = linEqArmLoMax st2 m b rest o :=
    fun o => linEqArmLoMax_local o hm hcx
  have h3 : ∀ o, linEqArmLoMin st1 m b rest o = linEqArmLoMin st2 m b rest o :=
    fun o => linEqArmLoMin_local o hm hcm
  have h4 : ∀ o, linEqArmHiMax st1 m b rest o = linEqArmHiMax st2 m b rest o :=
    fun o => linEqArmHiMax_local o hm hcx
  have g1 : ∀ o, linGenArmHiMin st1 m b c rest o = linGenArmHiMin st2 m b c rest o :=
    fun o => linGenArmHiMin_local o hm hcm
  have g2 : ∀ o, linGenArmLoMax st1 m b c rest o = linGenArmLoMax st2 m b c rest o :=
    fun o => linGenArmLoMax_local o hm hcx
  have g3 : ∀ o, linGenArmLoMin st1 m b c rest o = linGenArmLoMin st2 m b c rest o :=
    fun o => linGenArmLoMin_local o hm hcm
  have g4 : ∀ o, linGenArmHiMax st1 m b c rest o = linGenArmHiMax st2 m b c rest o :=
    fun o => linGenArmHiMax_local o hm hcx
  unfold linDeduceEq
  rw [hall, hsum, hmax]
  simp only [h1, h2, h3, h4, g1, g2, g3, g4]

/-- The sweep depends only on the positions' slots and the `rest` lists
    drawn from `coeffs.zip is`. -/
theorem linSweep_local {coeffs : List Int} {is : List Nat}
    {f1 f2 : Nat → Int → List (Int × Nat) → PropagationResult} :
    ∀ (ps : List ((Int × Nat) × Nat)) (idx : Nat),
      (∀ p ∈ ps, ∀ rest, (∀ q ∈ rest, q ∈ coeffs.zip is) →
        f1 p.1.2 p.1.1 rest = f2 p.1.2 p.1.1 rest) →
      linSweep coeffs is f1 ps idx = linSweep coeffs is f2 ps idx := by
  intro ps
  induction ps with
  | nil => intro idx _; rfl
  | cons p rest ih =>
      intro idx hf
      obtain ⟨⟨c, m⟩, i⟩ := p
      have hp := hf ((c, m), i) (List.mem_cons_self ..)
      have hr : ∀ q ∈ rest, ∀ r, (∀ z ∈ r, z ∈ coeffs.zip is) →
          f1 q.1.2 q.1.1 r = f2 q.1.2 q.1.1 r :=
        fun q hq => hf q (List.mem_cons_of_mem _ hq)
      rw [linSweep, linSweep]
      rw [hp (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1))
            (fun r hr => lin2_others_mem_zip hr)]
      cases hc : f2 m c (((coeffs.zip is).zipIdx.filter (fun q => q.2 != i)).map (·.1)) with
      | stable => exact ih (idx + 1) hr
      | implied _ _ => rfl
      | conflict _ => rfl

/-- `propLinLe2` reads only the slots of `is`: pointwise-equal domains
    on `is` yield equal runs. -/
theorem propLinLe2_local {st1 st2 : State} {coeffs : List Int} {is : List Nat}
    {b : Int}
    (h : ∀ i ∈ is, st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty) :
    propLinLe2 st1 coeffs is b = propLinLe2 st2 coeffs is b := by
  unfold propLinLe2
  cases hz : coeffs.zip is with
  | nil => rfl
  | cons p ps =>
      show linSweep coeffs is (linDeduceLe st1 b) ((p :: ps).zipIdx) 0 =
           linSweep coeffs is (linDeduceLe st2 b) ((p :: ps).zipIdx) 0
      refine linSweep_local ((p :: ps).zipIdx) 0 ?_
      intro q hq rest hrest
      exact linDeduceLe_local
        (h q.1.2 (mem_zip_snd (hz.symm ▸ lin2_mem_zip_of_zipIdx _ 0 q hq)))
        (fun r hr => h r.2 (mem_zip_snd (hrest r hr)))

/-- `propLinEq2` reads only the slots of `is`: pointwise-equal domains
    on `is` yield equal runs. -/
theorem propLinEq2_local {st1 st2 : State} {coeffs : List Int} {is : List Nat}
    {b : Int}
    (h : ∀ i ∈ is, st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty) :
    propLinEq2 st1 coeffs is b = propLinEq2 st2 coeffs is b := by
  unfold propLinEq2
  cases hz : coeffs.zip is with
  | nil => rfl
  | cons p ps =>
      show linSweep coeffs is (linDeduceEq st1 b) ((p :: ps).zipIdx) 0 =
           linSweep coeffs is (linDeduceEq st2 b) ((p :: ps).zipIdx) 0
      refine linSweep_local ((p :: ps).zipIdx) 0 ?_
      intro q hq rest hrest
      exact linDeduceEq_local
        (h q.1.2 (mem_zip_snd (hz.symm ▸ lin2_mem_zip_of_zipIdx _ 0 q hq)))
        (fun r hr => h r.2 (mem_zip_snd (hrest r hr)))

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
                (domMinI (st.domains.getD p.2 Dom.empty)).map
                  fun m => posLe p.2 (m - 1)
              else if p.1 < 0 then
                (domMaxI (st.domains.getD p.2 Dom.empty)).map fun m => negLe p.2 m
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
                  (domMinI (st.domains.getD p.2 Dom.empty)).map
                    fun m => posLe p.2 (m - 1)
                else if p.1 < 0 then
                  (domMaxI (st.domains.getD p.2 Dom.empty)).map fun m => negLe p.2 m
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
                (domMaxI (st.domains.getD p.2 Dom.empty)).map fun m => negLe p.2 m
              else if p.1 < 0 then
                (domMinI (st.domains.getD p.2 Dom.empty)).map
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
                  (domMaxI (st.domains.getD p.2 Dom.empty)).map fun m => negLe p.2 m
                else if p.1 < 0 then
                  (domMinI (st.domains.getD p.2 Dom.empty)).map
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
    (∃ mn, domMinI (st.domains.getD p.2 Dom.empty) = some mn ∧
        q = posLe p.2 (mn - 1) ∧ p.1 > 0) ∨
    (∃ mx, domMaxI (st.domains.getD p.2 Dom.empty) = some mx ∧
        q = negLe p.2 mx ∧ p.1 < 0) := by
  unfold linCauseMinPair at h
  by_cases hpos : p.1 > 0
  · rw [if_pos hpos] at h
    cases hmn : domMinI (st.domains.getD p.2 Dom.empty) with
    | none =>
        rw [hmn] at h
        exact absurd h (by intro hc; cases hc)
    | some mn =>
        rw [hmn, Option.map_some] at h
        injection h with hq2
        exact Or.inl ⟨mn, rfl, hq2.symm, hpos⟩
  · by_cases hneg : p.1 < 0
    · rw [if_neg (by omega : ¬ p.1 > 0), if_pos hneg] at h
      cases hmx : domMaxI (st.domains.getD p.2 Dom.empty) with
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
    (∃ mx, domMaxI (st.domains.getD p.2 Dom.empty) = some mx ∧
        q = negLe p.2 mx ∧ p.1 > 0) ∨
    (∃ mn, domMinI (st.domains.getD p.2 Dom.empty) = some mn ∧
        q = posLe p.2 (mn - 1) ∧ p.1 < 0) := by
  unfold linCauseMaxPair at h
  by_cases hpos : p.1 > 0
  · rw [if_pos hpos] at h
    cases hmx : domMaxI (st.domains.getD p.2 Dom.empty) with
    | none =>
        rw [hmx] at h
        exact absurd h (by intro hc; cases hc)
    | some mx =>
        rw [hmx, Option.map_some] at h
        injection h with hq2
        exact Or.inl ⟨mx, rfl, hq2.symm, hpos⟩
  · by_cases hneg : p.1 < 0
    · rw [if_neg (by omega : ¬ p.1 > 0), if_pos hneg] at h
      cases hmn : domMinI (st.domains.getD p.2 Dom.empty) with
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


/-! ## L1a: the pinned `int_lin_le_reif` delegation -/

/-- An integer-only domain guard: no Boolean value can be read. -/
def domIntOnlyB (d : List Value) : Bool :=
  d.all (fun v => match v with | .int _ => true | _ => false)

/-- The integer-only operand guard of a linear constraint: every operand
    slot is in range, has a nonempty domain, and its domain holds only
    integers. -/
def domsIntOnlyB (doms : List Domain) (is : List Nat) : Bool :=
  is.all (fun i => decide (i < doms.length) && decide (0 < (doms.getD i Dom.empty).length)
    && domIntOnlyB (Dom.enum (doms.getD i Dom.empty)))

/-- The enumerated integer-kind scan is the structural compact test. -/
theorem domIntOnlyB_enum_eq (d : Dom) :
    domIntOnlyB (Dom.enum d) = Dom.allIntBStruct d :=
  (Dom.allIntBStruct_eq d).symm

/-- Structural twin of the integer-only operand guard: the compact
    constructor tag answers the kind test without materialising any
    operand domain.  The range test is the lookup itself: each operand is
    fetched once and the domain list length is never recomputed. -/
def domsIntOnlyBFast (doms : List Domain) (is : List Nat) : Bool :=
  is.all (fun i =>
    match doms[i]? with
    | some d => decide (0 < d.length) && Dom.allIntBStruct d
    | none => false)

theorem domsIntOnlyBFast_eq (doms : List Domain) (is : List Nat) :
    domsIntOnlyBFast doms is = domsIntOnlyB doms is := by
  unfold domsIntOnlyBFast domsIntOnlyB
  apply List.all_congr rfl
  intro i
  rw [domIntOnlyB_enum_eq]
  by_cases hi : i < doms.length
  · rw [List.getElem?_eq_getElem hi, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi]
    simp [hi]
  · rw [List.getElem?_eq_none (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by omega)]
    simp [hi]

attribute [implemented_by domsIntOnlyBFast] domsIntOnlyB

/-- The delegation escape of the `r = true` direction: the reified fact is
    true only when the slot reads `true`, so `r = false` refutes the whole
    delegated nogood. -/
def linLeReifEscTrue (r : Nat) : Clause := [posBool r false]

/-- The delegation escapes of the `r = false` direction: `r = true`, plus,
    for every operand slot, the two Boolean-value literals — one of which is
    true exactly when the slot reads a Boolean. -/
def linLeReifEscFalse (is : List Nat) (r : Nat) : Clause :=
  posBool r true :: is.flatMap (fun i => [posBool i false, posBool i true])

/-- Insert `extras` after the head of a clause (the head is the pivot of the
    emission and stays first; an empty clause holds the extras alone). -/
def insertAfterHead (extras : Clause) : Clause → Clause
  | [] => extras
  | h :: t => h :: (extras ++ t)

/-- Augment every emitted clause of a result with `extras` (after its
    head). -/
def augmentRes (extras : Clause) : PropagationResult → PropagationResult
  | .stable => .stable
  | .implied l rs => .implied l { clause := insertAfterHead extras rs.clause }
  | .conflict c => .conflict (insertAfterHead extras c)

/-- Drop implied emissions, keep conflicts. The `r = false` direction emits
    conflicts only: its bound implications need a reason contract that
    relates the state box's slot count to the problem box's (see PLAN L1a);
    its conflicts are entitled at faithful solutions alone. -/
def conflictsOnly : PropagationResult → PropagationResult
  | .stable => .stable
  | .implied _ _ => .stable
  | .conflict c => .conflict c

/-! ## L1b: the unpinned bounds-decide-`b` arm (machinery) -/

def domBoolOnlyB (d : List Value) : Bool :=
  decide (0 < d.length) && d.all (fun v => match v with | .bool _ => true | _ => false)

theorem domBoolOnlyB_eq {d : List Value} (h : domBoolOnlyB d = true) :
    0 < d.length ∧ ∀ v ∈ d, ∃ b : Bool, v = .bool b := by
  rw [domBoolOnlyB, Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1, by
    intro v hv
    have hv' := List.all_eq_true.mp h.2 v hv
    cases v with
    | bool b => exact ⟨b, rfl⟩
    | int k => exact absurd hv' (by simp)
    | setOfInt s => exact absurd hv' (by simp)
    | array a => exact absurd hv' (by simp)⟩

/-- The operand Boolean-value escapes of the bounds-decide-`b` arm. -/
def linLeReifEscB (is : List Nat) : Clause :=
  is.flatMap (fun i => [posBool i false, posBool i true])

/-- The dual (PLAN G1d) emission of the bounds-decide-`b` arm: when the
    reif slot is unpinned (and Boolean-valued) and the operand domains are
    integer-only with complete extrema, a minimum-contribution sum exceeding
    `b` pins the reif slot to `false` (the inequality can hold for no
    operand instantiation). -/
def propLinLeReifBDual (st : State) (coeffs : List Int) (is : List Nat)
    (b : Int) (r : Nat) : PropagationResult :=
  match sumMin st (coeffs.zip is) with
  | some lo => if b < lo then
      .implied (posBool r false)
        { clause := posBool r false
            :: (linLeReifEscB is ++ linCausesMin st (coeffs.zip is)) }
    else .stable
  | none => .stable

/-- The dual arm's complete emission shape. -/
theorem propLinLeReifBDual_emission_inv {st : State} {coeffs : List Int}
    {is : List Nat} {b : Int} {r : Nat} {res : PropagationResult}
    (h : propLinLeReifBDual st coeffs is b r = res) :
    res = .stable ∨
    ∃ lo, sumMin st (coeffs.zip is) = some lo ∧ b < lo ∧
      res = .implied (posBool r false)
        { clause := posBool r false
            :: (linLeReifEscB is ++ linCausesMin st (coeffs.zip is)) } := by
  unfold propLinLeReifBDual at h
  cases hs : sumMin st (coeffs.zip is) with
  | none => simp only [hs] at h; exact Or.inl h.symm
  | some lo =>
      simp only [hs] at h
      by_cases hlt : b < lo
      · rw [if_pos hlt] at h
        exact Or.inr ⟨lo, rfl, hlt, h.symm⟩
      · rw [if_neg hlt] at h
        exact Or.inl h.symm

/-- The bounds-decide-`b` arm: when the reif slot is unpinned (and
    Boolean-valued) and the operand domains are integer-only with complete
    extrema, an exceeding max-contribution sum pins the reif slot to `true`
    (PLAN L1b), and the dual: a minimum-contribution sum exceeding `b` pins
    it to `false` (PLAN G1d). -/
def propLinLeReifB (st : State) (coeffs : List Int) (is : List Nat) (b : Int)
    (r : Nat) : PropagationResult :=
  if (domBoolPin st.domains r true || domBoolPin st.domains r false) = true then .stable
  else if (domBoolOnlyB (Dom.enum (st.domains.getD r Dom.empty)) && is.all (fun i => decide (i ≠ r))
      && domsIntOnlyB st.domains is) = true then
    if ((coeffs.zip is).all (fun p => (minContrib st p).isSome)) = true then
      match sumMax st (coeffs.zip is) with
      | some hr => if hr ≤ b then
          .implied (posBool r true)
            { clause := posBool r true
                :: (linLeReifEscB is ++ linCausesMax st (coeffs.zip is)) }
        else propLinLeReifBDual st coeffs is b r
      | none => propLinLeReifBDual st coeffs is b r
    else .stable
  else .stable

theorem propLinLeReifB_emission_inv {st : State} {coeffs : List Int}
    {is : List Nat} {b : Int} {r : Nat} {res : PropagationResult}
    (h : propLinLeReifB st coeffs is b r = res) :
    res = .stable ∨
    ((domBoolPin st.domains r true || domBoolPin st.domains r false) = false ∧
     domBoolOnlyB (Dom.enum (st.domains.getD r Dom.empty)) = true ∧
     (is.all (fun i => decide (i ≠ r))) = true ∧
     domsIntOnlyB st.domains is = true ∧
     (∀ p ∈ coeffs.zip is, (minContrib st p).isSome = true) ∧
     ∃ hr, sumMax st (coeffs.zip is) = some hr ∧ hr ≤ b ∧
       res = .implied (posBool r true)
         { clause := posBool r true
             :: (linLeReifEscB is ++ linCausesMax st (coeffs.zip is)) }) ∨
    ((domBoolPin st.domains r true || domBoolPin st.domains r false) = false ∧
     domBoolOnlyB (Dom.enum (st.domains.getD r Dom.empty)) = true ∧
     (is.all (fun i => decide (i ≠ r))) = true ∧
     domsIntOnlyB st.domains is = true ∧
     (∀ p ∈ coeffs.zip is, (minContrib st p).isSome = true) ∧
     ∃ lo, sumMin st (coeffs.zip is) = some lo ∧ b < lo ∧
       res = .implied (posBool r false)
         { clause := posBool r false
             :: (linLeReifEscB is ++ linCausesMin st (coeffs.zip is)) }) := by
  unfold propLinLeReifB at h
  by_cases h1 : (domBoolPin st.domains r true || domBoolPin st.domains r false) = true
  · rw [if_pos h1] at h
    exact Or.inl h.symm
  · rw [if_neg h1] at h
    by_cases h2 : (domBoolOnlyB (Dom.enum (st.domains.getD r Dom.empty))
        && is.all (fun i => decide (i ≠ r))
        && domsIntOnlyB st.domains is) = true
    · rw [if_pos h2] at h
      have h2' := h2
      simp only [Bool.and_eq_true] at h2'
      obtain ⟨⟨hb, hne⟩, hi⟩ := h2'
      by_cases h3 : ((coeffs.zip is).all (fun p => (minContrib st p).isSome)) = true
      · rw [if_pos h3] at h
        cases hsm : sumMax st (coeffs.zip is) with
        | none =>
            simp only [hsm] at h
            rcases propLinLeReifBDual_emission_inv h with
              hstable | ⟨lo, hs, hlt, hres⟩
            · exact Or.inl hstable
            · exact Or.inr (Or.inr ⟨Bool.eq_false_iff.mpr h1, hb, hne, hi,
                fun p hp => List.all_eq_true.mp h3 p hp, lo, hs, hlt, hres⟩)
        | some hr =>
            simp only [hsm] at h
            by_cases h4 : hr ≤ b
            · rw [if_pos h4] at h
              exact Or.inr (Or.inl ⟨Bool.eq_false_iff.mpr h1, hb, hne, hi,
                fun p hp => List.all_eq_true.mp h3 p hp, hr, rfl, h4, h.symm⟩)
            · rw [if_neg h4] at h
              rcases propLinLeReifBDual_emission_inv h with
                hstable | ⟨lo, hs, hlt, hres⟩
              · exact Or.inl hstable
              · exact Or.inr (Or.inr ⟨Bool.eq_false_iff.mpr h1, hb, hne, hi,
                  fun p hp => List.all_eq_true.mp h3 p hp, lo, hs, hlt, hres⟩)
      · rw [if_neg h3] at h
        exact Or.inl h.symm
    · rw [if_neg h2] at h
      exact Or.inl h.symm

/-- The bounds arm never reports a conflict (its emissions are `.stable` or
    an implied pin). -/
theorem propLinLeReifB_ne_conflict {st : State} {coeffs : List Int}
    {is : List Nat} {b : Int} {r : Nat} {c : Clause}
    (h : propLinLeReifB st coeffs is b r = .conflict c) : False := by
  rcases propLinLeReifB_emission_inv h with
    hst | ⟨-, -, -, -, -, hr, hsum, hle, hres⟩ |
    ⟨-, -, -, -, -, lo, hsum, hle, hres⟩
  · cases hst
  · cases hres
  · cases hres

/-! ## The max-contribution sum bounds a fitting assignment's dot -/

theorem slotInt_of_getElem_int {a : Assignment} {i : Nat} {x : Int}
    (h : a[i]! = .int x) : slotInt a i = some x := by
  show a[i]?.bind Value.intView = some x
  by_cases hlt : i < a.length
  · have hread : a[i]? = some a[i] := List.getElem?_eq_getElem hlt
    have hget : a[i]! = a[i] := by
      rw [List.getElem!_eq_getElem?_getD, hread]; rfl
    rw [hget] at h
    rw [hread, h]
    rfl
  · have hnone : a[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    have hdef : a[i]! = (default : Value) := by
      rw [List.getElem!_eq_getElem?_getD, hnone]; rfl
    rw [hdef] at h
    rw [show (default : Value) = Value.bool false from rfl] at h
    cases h

theorem sumMax_exists_of_all {st : State} :
    ∀ {pairs : List (Int × Nat)}, pairs ≠ [] →
    (∀ p ∈ pairs, (minContrib st p).isSome = true) →
      ∃ s, sumMax st pairs = some s
  | [], hne, _ => absurd rfl hne
  | (c, i) :: rest, _, hall => by
      have hc : (maxContrib st (c, i)).isSome = true :=
        maxContrib_isSome_of_minContrib (hall (c, i) (List.mem_cons_self))
      have hrest : ∀ q ∈ rest, (minContrib st q).isSome = true :=
        fun q hq => hall q (List.mem_cons_of_mem _ hq)
      cases hmax : maxContrib st (c, i) with
      | none => rw [hmax] at hc; exact absurd hc (by simp)
      | some t =>
          by_cases hne : rest = []
          · subst hne
            exact ⟨t.2.2, by simp only [sumMax, hmax]⟩
          · obtain ⟨s', hs'⟩ := sumMax_exists_of_all hne hrest
            exact ⟨s' + t.2.2, by simp only [sumMax, hmax, hs']⟩

/-- The max-contribution sum bounds a fitting assignment's dot (with the
    assignment's reads known to be integers). -/
theorem dotOver_le_sumMax {st : State} {a : Assignment}
    {pairs : List (Int × Nat)}
    (hne : pairs ≠ [])
    (hfit : Assignment.Fits st.domains a)
    (hall : ∀ p ∈ pairs, (minContrib st p).isSome = true)
    (hreads : ∀ p ∈ pairs, ∃ x : Int, a[p.2]! = .int x) :
    ∃ s, sumMax st pairs = some s ∧
      ∀ d, dotOver pairs a 0 = some d → d ≤ s := by
  induction pairs with
  | nil => exact absurd rfl hne
  | cons p rest ih =>
      obtain ⟨c, i⟩ := p
      have hc : (minContrib st (c, i)).isSome = true :=
        hall (c, i) (List.mem_cons_self)
      have hrest : ∀ q ∈ rest, (minContrib st q).isSome = true :=
        fun q hq => hall q (List.mem_cons_of_mem _ hq)
      have hrreads : ∀ q ∈ rest, ∃ x : Int, a[q.2]! = .int x :=
        fun q hq => hreads q (List.mem_cons_of_mem _ hq)
      have hmaxsome : (maxContrib st (c, i)).isSome = true :=
        maxContrib_isSome_of_minContrib hc
      cases hmax : maxContrib st (c, i) with
      | none => rw [hmax] at hmaxsome; exact absurd hmaxsome (by simp)
      | some t =>
          obtain ⟨mn, mx, hmn, hmx, ht⟩ := maxContrib_inv hmax
          obtain ⟨x, hx⟩ := hreads (c, i) (List.mem_cons_self)
          have hslot : slotInt a i = some x := slotInt_of_getElem_int hx
          have hxb : x ≤ mx := fits_max_bound hfit hmx hslot
          have hxb2 : mn ≤ x := fits_min_bound hfit hmn hslot
          have hterm : c * x ≤ t.2.2 := by
            rw [ht]
            by_cases hcpos : c ≥ 0
            · rw [if_pos hcpos]
              exact Int.mul_le_mul_of_nonneg_left hxb hcpos
            · rw [if_neg hcpos]
              exact Int.mul_le_mul_of_nonpos_left (by omega) hxb2
          by_cases hne : rest = []
          · subst hne
            refine ⟨t.2.2, by simp only [sumMax, hmax], ?_⟩
            intro d hd
            simp only [dotOver, hx] at hd
            injection hd with hd
            have hd' : d = 0 + c * x := hd.symm
            omega
          · obtain ⟨s', hs', hle'⟩ := ih hne hrest hrreads
            refine ⟨s' + t.2.2, by simp only [sumMax, hmax, hs'], ?_⟩
            intro d hd
            simp only [dotOver, hx] at hd
            rw [dotOver_shift] at hd
            cases hd2 : dotOver rest a 0 with
            | none => rw [hd2] at hd; cases hd
            | some d' =>
                rw [hd2] at hd
                injection hd with hd
                have hd' : d = d' + c * x := by simpa using hd.symm
                have hrestle : d' ≤ s' := hle' d' hd2
                omega

/-! ## The cause-false max-contribution bound (PLAN L1b)

The bounds arm's reason obligation needs the max-contribution sum to
bound the dot at a solution where every emitted max-cause literal is
FALSE (the state box need not contain the solution: the cause literals
are exactly its bound facts). -/

/-- A pair's term is bounded by its max-contribution when its max-cause is
    false at the assignment and the pair's read is the recorded integer. -/
theorem mul_le_maxContrib_of_cause_false {st : State} {p : Int × Nat}
    {a : Assignment} {x : Int} {t : Nat × Int × Int}
    (hslot : slotInt a p.2 = some x)
    (hmin : (minContrib st p).isSome = true)
    (hmax : maxContrib st p = some t)
    (hfalse : ∀ q, linCauseMaxPair st p = some q → q.eval a = some false) :
    p.1 * x ≤ t.2.2 := by
  obtain ⟨mn, mx, hmn, hmx⟩ : ∃ mn mx,
      domMinI (st.domains.getD p.2 Dom.empty) = some mn ∧
      domMaxI (st.domains.getD p.2 Dom.empty) = some mx := by
    cases hc : minContrib st p with
    | none => rw [hc] at hmin; exact absurd hmin (by simp)
    | some t0 =>
        obtain ⟨mn, mx, hmn, hmx, -⟩ := minContrib_inv hc
        exact ⟨mn, mx, hmn, hmx⟩
  obtain ⟨mn', mx', hmn', hmx', ht⟩ := maxContrib_inv hmax
  have hmn2 : mn' = mn := Option.some.inj (hmn'.symm.trans hmn)
  have hmx2 : mx' = mx := Option.some.inj (hmx'.symm.trans hmx)
  rw [ht]
  show p.1 * x ≤ if p.1 ≥ 0 then p.1 * mx' else p.1 * mn'
  by_cases hpos : p.1 > 0
  · rw [if_pos (by omega : p.1 ≥ 0)]
    have hcause : linCauseMaxPair st p = some (negLe p.2 mx') := by
      unfold linCauseMaxPair
      rw [if_pos hpos, hmx']
      rfl
    have hq := hfalse _ hcause
    have hx : x ≤ mx' := by
      by_cases hle : x ≤ mx'
      · exact hle
      · have htrue : (negLe p.2 mx').eval a = some true := by
          rw [eval_negLe, hslot]
          show Option.map (fun i => !(decide (i ≤ mx'))) (some x) = some true
          rw [show Option.map (fun i => !(decide (i ≤ mx'))) (some x)
                = some (!(decide (x ≤ mx'))) from rfl, decide_eq_false hle]
          rfl
        rw [htrue] at hq
        exact absurd hq (by simp)
    exact Int.mul_le_mul_of_nonneg_left hx (by omega)
  · by_cases hzero : p.1 = 0
    · rw [if_pos (by omega : p.1 ≥ 0), hzero]
      show (0 : Int) * x ≤ 0 * mx'
      omega
    · have hneg : p.1 < 0 := by omega
      rw [if_neg (by omega : ¬ p.1 ≥ 0)]
      have hcause : linCauseMaxPair st p = some (posLe p.2 (mn' - 1)) := by
        unfold linCauseMaxPair
        rw [if_neg (by omega : ¬ p.1 > 0), if_pos hneg, hmn']
        rfl
      have hq := hfalse _ hcause
      have hx : x ≥ mn' := by
        by_cases hle : x ≤ mn' - 1
        · have htrue : (posLe p.2 (mn' - 1)).eval a = some true := by
            rw [eval_posLe, hslot]
            show Option.map (fun i => decide (i ≤ mn' - 1)) (some x) = some true
            rw [show Option.map (fun i => decide (i ≤ mn' - 1)) (some x)
                  = some (decide (x ≤ mn' - 1)) from rfl, decide_eq_true hle]
          rw [htrue] at hq
          exact absurd hq (by simp)
        · omega
      exact Int.mul_le_mul_of_nonpos_left (by omega : p.1 ≤ 0) hx

/-- The max-contribution sum bounds a dot whose reads are integers and whose
    max-causes are all false at the assignment (the cause-false twin of
    `dotOver_le_sumMax`). -/
theorem dotOver_le_sumMax_of_causes_false {st : State} {a : Assignment}
    {pairs : List (Int × Nat)}
    (hne : pairs ≠ [])
    (hall : ∀ p ∈ pairs, (minContrib st p).isSome = true)
    (hreads : ∀ p ∈ pairs, ∃ x : Int, a[p.2]! = .int x)
    (hcauses : ∀ q ∈ linCausesMax st pairs, q.eval a = some false) :
    ∃ s, sumMax st pairs = some s ∧
      ∀ d, dotOver pairs a 0 = some d → d ≤ s := by
  induction pairs with
  | nil => exact absurd rfl hne
  | cons p rest ih =>
      obtain ⟨c, i⟩ := p
      have hc : (minContrib st (c, i)).isSome = true :=
        hall (c, i) (List.mem_cons_self)
      have hrest : ∀ q ∈ rest, (minContrib st q).isSome = true :=
        fun q hq => hall q (List.mem_cons_of_mem _ hq)
      have hrreads : ∀ q ∈ rest, ∃ x : Int, a[q.2]! = .int x :=
        fun q hq => hreads q (List.mem_cons_of_mem _ hq)
      have hmaxsome : (maxContrib st (c, i)).isSome = true :=
        maxContrib_isSome_of_minContrib hc
      cases hmax : maxContrib st (c, i) with
      | none => rw [hmax] at hmaxsome; exact absurd hmaxsome (by simp)
      | some t =>
          obtain ⟨x, hx⟩ := hreads (c, i) (List.mem_cons_self)
          have hslot : slotInt a i = some x := slotInt_of_getElem_int hx
          have hhead : ∀ q, linCauseMaxPair st (c, i) = some q →
              q.eval a = some false :=
            fun q hq =>
              hcauses q (List.mem_filterMap.mpr
                ⟨(c, i), List.mem_cons_self, hq⟩)
          have hterm : c * x ≤ t.2.2 :=
            mul_le_maxContrib_of_cause_false hslot hc hmax hhead
          have hrestcauses : ∀ q ∈ linCausesMax st rest,
              q.eval a = some false := by
            intro q hq
            obtain ⟨p', hp'mem, hp'q⟩ := List.mem_filterMap.mp hq
            exact hcauses q (List.mem_filterMap.mpr
              ⟨p', List.mem_cons_of_mem _ hp'mem, hp'q⟩)
          by_cases hne : rest = []
          · subst hne
            refine ⟨t.2.2, by simp only [sumMax, hmax], ?_⟩
            intro d hd
            simp only [dotOver, hx] at hd
            injection hd with hd
            have hd' : d = 0 + c * x := hd.symm
            omega
          · obtain ⟨s', hs', hle'⟩ := ih hne hrest hrreads hrestcauses
            refine ⟨s' + t.2.2, by simp only [sumMax, hmax, hs'], ?_⟩
            intro d hd
            simp only [dotOver, hx] at hd
            rw [dotOver_shift] at hd
            cases hd2 : dotOver rest a 0 with
            | none => rw [hd2] at hd; cases hd
            | some d' =>
                rw [hd2] at hd
                injection hd with hd
                have hd' : d = d' + c * x := by simpa using hd.symm
                have hrestle : d' ≤ s' := hle' d' hd2
                omega

/-- The pinned-direction delegation propagator for
    `int_lin_le_reif coeffs is b r`:
    * the reif slot pinned `true`: propagate the underlying `Σ ≤ b` with the
      escape `r = false` woven into every clause;
    * the reif slot pinned `false` over integer-only operand domains:
      propagate the underlying `Σ ≥ b+1` (the delegated `propLinLe2` on the
      negated coefficients) — both its conflicts and its bound implications
      (PLAN G1d), with the escapes `r = true` and the operand Boolean-value
      literals woven into every clause;
    * the reif slot unpinned: the bounds arm `propLinLeReifB` (PLAN L1b,
      both directions since PLAN G1d). -/
def propLinLeReif (st : State) (coeffs : List Int) (is : List Nat) (b : Int)
    (r : Nat) : PropagationResult :=
  if coeffs.length == is.length then
    if domBoolPin st.domains r true then
      augmentRes (linLeReifEscTrue r) (propLinLe2 st coeffs is b)
    else if domBoolPin st.domains r false && domsIntOnlyB st.domains is then
      augmentRes (linLeReifEscFalse is r)
        (propLinLe2 st (coeffs.map (fun c => -c)) is (-(b + 1)))
    else propLinLeReifB st coeffs is b r
  else .stable

/-! ## Run equations -/

theorem propLinLeReif_run_true {st : State} {coeffs : List Int} {is : List Nat}
    {b : Int} {r : Nat} (hlenB : (coeffs.length == is.length) = true)
    (h : domBoolPin st.domains r true = true) :
    propLinLeReif st coeffs is b r
      = augmentRes (linLeReifEscTrue r) (propLinLe2 st coeffs is b) := by
  simp [propLinLeReif, hlenB, h]

theorem propLinLeReif_run_false {st : State} {coeffs : List Int}
    {is : List Nat} {b : Int} {r : Nat}
    (hlenB : (coeffs.length == is.length) = true)
    (h1 : ¬ (domBoolPin st.domains r true = true))
    (h2 : (domBoolPin st.domains r false && domsIntOnlyB st.domains is) = true) :
    propLinLeReif st coeffs is b r
      = augmentRes (linLeReifEscFalse is r)
          (propLinLe2 st (coeffs.map (fun c => -c)) is (-(b + 1))) := by
  simp [propLinLeReif, hlenB, h2, if_neg h1]

/-- The unpinned arm's run equation: the delegation falls through to the
    bounds arm `propLinLeReifB` (PLAN L1b). -/
theorem propLinLeReif_run_b {st : State} {coeffs : List Int}
    {is : List Nat} {b : Int} {r : Nat}
    (hlenB : (coeffs.length == is.length) = true)
    (h1 : ¬ (domBoolPin st.domains r true = true))
    (h2 : ¬ ((domBoolPin st.domains r false && domsIntOnlyB st.domains is) = true)) :
    propLinLeReif st coeffs is b r = propLinLeReifB st coeffs is b r := by
  show (if (coeffs.length == is.length) = true then
      (if (domBoolPin st.domains r true) = true then
        augmentRes (linLeReifEscTrue r) (propLinLe2 st coeffs is b)
      else if (domBoolPin st.domains r false
          && domsIntOnlyB st.domains is) = true then
        augmentRes (linLeReifEscFalse is r)
          (propLinLe2 st (coeffs.map (fun c => -c)) is (-(b + 1)))
      else propLinLeReifB st coeffs is b r)
    else .stable) = propLinLeReifB st coeffs is b r
  rw [if_pos hlenB, if_neg h1, if_neg h2]

theorem propLinLeReif_run_arity {st : State} {coeffs : List Int}
    {is : List Nat} {b : Int} {r : Nat}
    (hlenB : (coeffs.length == is.length) = false) :
    propLinLeReif st coeffs is b r = .stable := by
  simp [propLinLeReif, hlenB]

/-- The two pin tests are exclusive. -/
theorem domBoolPin_excl {doms : List Domain} {s : Nat} {b b' : Bool}
    (h : domBoolPin doms s b = true) (hne : b' ≠ b) :
    domBoolPin doms s b' = false := by
  have hd := domBoolPin_eq h
  unfold domBoolPin
  rw [hd]
  cases b <;> cases b' <;> simp_all [valueMemB, Value.eqB]

/-! ## Membership algebra -/

theorem mem_insertAfterHead {extras cl : Clause} {q : Literal}
    (h : q ∈ insertAfterHead extras cl) : q ∈ cl ∨ q ∈ extras := by
  cases cl with
  | nil => exact Or.inr h
  | cons hd tl =>
      rw [insertAfterHead] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl List.mem_cons_self
      · rcases List.mem_append.mp h with h | h
        · exact Or.inr h
        · exact Or.inl (List.mem_cons_of_mem _ h)

theorem mem_insertAfterHead_of_mem {extras cl : Clause} {q : Literal}
    (h : q ∈ cl) : q ∈ insertAfterHead extras cl := by
  cases cl with
  | nil => exact absurd h (by simp)
  | cons hd tl =>
      rw [insertAfterHead]
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ h)

theorem mem_insertAfterHead_of_mem_extras {extras cl : Clause} {q : Literal}
    (h : q ∈ extras) : q ∈ insertAfterHead extras cl := by
  cases cl with
  | nil => exact h
  | cons hd tl =>
      rw [insertAfterHead]
      exact List.mem_cons_of_mem _ (List.mem_append_left _ h)

/-! ## Emission inversions -/

theorem augmentRes_implied_inv {extras : Clause} {res : PropagationResult}
    {l : Literal} {rs : Reason} (h : augmentRes extras res = .implied l rs) :
    ∃ rs0 : Reason, res = .implied l rs0
      ∧ rs.clause = insertAfterHead extras rs0.clause := by
  cases res with
  | stable => cases h
  | implied l0 rs0 =>
      injection h with h1 h2
      subst h1
      exact ⟨rs0, rfl, by rw [← h2]⟩
  | conflict c => cases h

theorem augmentRes_conflict_inv {extras : Clause} {res : PropagationResult}
    {c : Clause} (h : augmentRes extras res = .conflict c) :
    ∃ c0 : Clause, res = .conflict c0 ∧ c = insertAfterHead extras c0 := by
  cases res with
  | stable => cases h
  | implied l rs => cases h
  | conflict c0 =>
      injection h with h1
      subst h1
      exact ⟨c0, rfl, rfl⟩

theorem conflictsOnly_implied_elim {res : PropagationResult} {l : Literal}
    {rs : Reason} (h : conflictsOnly res = .implied l rs) : False := by
  cases res with
  | stable => cases h
  | implied l0 rs0 => cases h
  | conflict c => cases h

theorem conflictsOnly_conflict_inv {res : PropagationResult} {c : Clause}
    (h : conflictsOnly res = .conflict c) : res = .conflict c := by
  cases res with
  | stable => cases h
  | implied l rs => cases h
  | conflict c0 => injection h with h1; subst h1; rfl

/-! ## The guard's semantics -/

theorem domIntOnlyB_eq {d : List Value} (h : domIntOnlyB d = true) :
    ∀ v ∈ d, ∃ k : Int, v = .int k := by
  intro v hv
  have hv' := List.all_eq_true.mp h v hv
  cases v with
  | int k => exact ⟨k, rfl⟩
  | bool b => exact absurd hv' (by simp)
  | setOfInt s => exact absurd hv' (by simp)
  | array a => exact absurd hv' (by simp)

theorem domsIntOnlyB_eq {doms : List Domain} {is : List Nat}
    (h : domsIntOnlyB doms is = true) :
    ∀ i ∈ is, i < doms.length ∧ 0 < (doms.getD i Dom.empty).length
      ∧ ∀ v ∈ Dom.enum (doms.getD i Dom.empty), ∃ k : Int, v = .int k := by
  intro i hi
  have h1 := List.all_eq_true.mp h i hi
  rw [Bool.and_eq_true, Bool.and_eq_true] at h1
  exact ⟨of_decide_eq_true h1.1.1, of_decide_eq_true h1.1.2, domIntOnlyB_eq h1.2⟩

/-- The guard's per-slot read: at a fitting assignment every operand slot
    reads an integer. -/
theorem domsIntOnlyB_fits_read {doms : List Domain} {is : List Nat}
    {a : Assignment} (hg : domsIntOnlyB doms is = true)
    (hfit : Assignment.Fits doms a) :
    ∀ i ∈ is, ∃ k : Int, a[i]! = .int k := by
  intro i hi
  obtain ⟨hrange, -, hint⟩ := domsIntOnlyB_eq hg i hi
  have hlen : i < a.length := by rw [hfit.1]; exact hrange
  have hread : a[i]? = some a[i] := List.getElem?_eq_getElem hlen
  have hmem : a[i] ∈ doms.getD i Dom.empty := hfit.2 i (a[i]) hread
  have hmemE : a[i] ∈ Dom.enum (doms.getD i Dom.empty) :=
    (DomainLike.mem_iff _ _).mp hmem
  obtain ⟨k, hk⟩ := hint (a[i]) hmemE
  exact ⟨k, by rw [List.getElem!_eq_getElem?_getD, hread]; exact hk⟩

/-- The guard's per-slot read at a faithful assignment. -/
theorem domsIntOnlyB_faithful_read {doms : List Domain} {is : List Nat}
    {a : Assignment} (hg : domsIntOnlyB doms is = true)
    (hfaith : FrameFaithful doms a) :
    ∀ i ∈ is, ∃ k : Int, a[i]! = .int k := by
  intro i hi
  obtain ⟨hrange, hne, hint⟩ := domsIntOnlyB_eq hg i hi
  have hneE : Dom.enum (doms.getD i Dom.empty) ≠ [] := by
    intro h0
    have hlen0 : (doms.getD i Dom.empty).length = 0 := by
      rw [Dom.length_eq_enum, h0]
      rfl
    omega
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ hneE
  obtain ⟨y, hy, -, hsort⟩ := hfaith i hrange
  have hyint : ∃ k : Int, y = .int k := by
    rcases hsort v ((DomainLike.mem_iff _ _).mpr hv) with ⟨hintv, hyi⟩ | ⟨hbv, hyb⟩
    · exact hyi
    · obtain ⟨k, hk⟩ := hint v hv
      rcases hbv with ⟨b, hb⟩
      rw [hb] at hk
      exact absurd hk (by simp)
  obtain ⟨k, hk⟩ := hyint
  exact ⟨k, by rw [List.getElem!_eq_getElem?_getD, hy, hk]; rfl⟩

/-- At a faithful assignment every in-range slot has an integer view. -/
theorem frameFaithful_slotInt {doms : List Domain} {a : Assignment}
    (hfaith : FrameFaithful doms a) {i : Nat} (hi : i < doms.length) :
    ∃ x, slotInt a i = some x := by
  obtain ⟨y, hy, hyv, -⟩ := hfaith i hi
  cases hv : y.intView with
  | none => exact absurd hv hyv
  | some x =>
      refine ⟨x, ?_⟩
      show a[i]?.bind Value.intView = some x
      rw [hy]
      show (some y).bind Value.intView = some x
      rw [Option.bind_some]
      exact hv

/-! ## Dot-product algebra -/

theorem intVals_length (cs : List Int) : (intVals cs).length = cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [intVals, ih]

/-- The value-level negation map of `intVals`. -/
def negIntVal : Value → Value
  | .int k => .int (-k)
  | v => v

theorem intVals_map_neg (cs : List Int) :
    intVals (cs.map (fun c => -c)) = (intVals cs).map negIntVal := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons, intVals, negIntVal, ih]

/-- Negation moves out of a left product. -/
theorem neg_mul_eq (c x : Int) : (-c) * x = -(x * c) := by
  rw [Int.neg_mul, Int.mul_comm]

/-- Dot products with negated values negate. -/
theorem dotProduct_negIntVal : ∀ (as xs : List Value),
    dotProduct (as.map negIntVal) xs = (dotProduct as xs).map (fun d => -d)
  | [], [] => rfl
  | [], _ :: _ => rfl
  | .int c :: as, [] => rfl
  | .int c :: as, .int x :: xs => by
      simp only [List.map_cons, negIntVal, dotProduct]
      rw [dotProduct_negIntVal as xs]
      cases hd : dotProduct as xs with
      | none => rfl
      | some d =>
          simp only [Option.map_some]
          congr 1
          rw [neg_mul_eq, Int.mul_comm]
          omega
  | .int c :: as, .bool _ :: _ => rfl
  | .int c :: as, .setOfInt _ :: _ => rfl
  | .int c :: as, .array _ :: _ => rfl
  | .bool _ :: _, _ => rfl
  | .setOfInt _ :: _, _ => rfl
  | .array _ :: _, _ => rfl

theorem dotProduct_intVals_neg (cs : List Int) (xs : List Value) :
    dotProduct (intVals (cs.map (fun c => -c))) xs
      = (dotProduct (intVals cs) xs).map (fun d => -d) := by
  rw [intVals_map_neg]
  exact dotProduct_negIntVal (intVals cs) xs

/-- An all-integer read list of matching length yields a dot product. -/
theorem dotProduct_intVals_exists_of_length {cs : List Int} {xs : List Value}
    (hlen : xs.length = (intVals cs).length)
    (h : ∀ x ∈ xs, ∃ k : Int, x = .int k) :
    ∃ d, dotProduct (intVals cs) xs = some d := by
  induction cs generalizing xs with
  | nil =>
      cases xs with
      | nil => exact ⟨0, rfl⟩
      | cons x xs => simp [intVals] at hlen
  | cons c cs ih =>
      cases xs with
      | nil => simp [intVals] at hlen
      | cons x xs =>
          obtain ⟨k, rfl⟩ := h x (List.mem_cons_self)
          have hlen' : xs.length = (intVals cs).length := by
            simp only [List.length_cons, intVals, intVals_length] at hlen
            rw [intVals_length]
            omega
          have h' : ∀ y ∈ xs, ∃ k : Int, y = .int k :=
            fun y hy => h y (List.mem_cons_of_mem _ hy)
          obtain ⟨d, hd⟩ := ih hlen' h'
          exact ⟨k * c + d, by simp only [intVals, dotProduct, hd, Int.mul_comm]⟩

/-! ## Constraint-semantics bridges -/

theorem linLeReif_satisfied_inv {coeffs : List Int} {is : List Nat} {b : Int}
    {r : Nat} {a : Assignment}
    (h : (DomConstraint.linLeReif coeffs is b r).SatisfiedBy a) :
    ∃ rb : Bool, a[r]? = some (.bool rb)
      ∧ (rb = true ↔ dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b = true) :=
  h

/-- The `r`-pinned-true bridge: the reified `Σ ≤ b` holds. -/
theorem linLeReif_true_dot {coeffs : List Int} {is : List Nat} {b : Int}
    {r : Nat} {a : Assignment}
    (h : (DomConstraint.linLeReif coeffs is b r).SatisfiedBy a)
    (hpin : a[r]? = some (.bool true)) :
    (DomConstraint.linLe coeffs is b).SatisfiedBy a := by
  obtain ⟨rb, hread, hiff⟩ := linLeReif_satisfied_inv h
  rw [hpin] at hread
  have hrb : rb = true := by simpa using hread.symm
  show dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b = true
  exact hiff.mp hrb

/-- The `r`-pinned-false bridge: with integer operand reads, the negated
    `-Σ ≤ -(b+1)` holds. -/
theorem linLeReif_false_dot {coeffs : List Int} {is : List Nat} {b : Int}
    {r : Nat} {a : Assignment}
    (h : (DomConstraint.linLeReif coeffs is b r).SatisfiedBy a)
    (hpin : a[r]? = some (.bool false))
    (hreads : ∀ i ∈ is, ∃ k : Int, a[i]! = .int k)
    (hlen : coeffs.length = is.length) :
    (DomConstraint.linLe (coeffs.map (fun c => -c)) is (-(b + 1))).SatisfiedBy a := by
  obtain ⟨rb, hread, hiff⟩ := linLeReif_satisfied_inv h
  have hrbfalse : rb = false := by
    rw [hpin] at hread
    simpa using hread.symm
  have hdot : dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b = false := by
    have h1 : ¬ (dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b = true) := by
      intro hc
      have : rb = true := hiff.mpr hc
      rw [hrbfalse] at this
      exact Bool.noConfusion this
    cases hd : dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b with
    | false => rfl
    | true => exact absurd hd h1
  have hreadsAll : ∀ x ∈ is.map (fun i => a[i]!), ∃ k : Int, x = .int k := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact hreads i hi
  have hlen2 : (is.map (fun i => a[i]!)).length = (intVals coeffs).length := by
    rw [List.length_map, intVals_length]
    omega
  obtain ⟨d, hd⟩ := dotProduct_intVals_exists_of_length hlen2 hreadsAll
  have hdle : b < d := by
    have h1 : dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b
        = decide (d ≤ b) := by
      rw [dotLe, hd]
    rw [h1] at hdot
    by_cases hle : d ≤ b
    · rw [decide_eq_true hle] at hdot
      exact Bool.noConfusion hdot
    · omega
  show dotLe (intVals (coeffs.map (fun c => -c))) (is.map (fun i => a[i]!))
    (-(b + 1)) = true
  rw [dotLe, dotProduct_intVals_neg, hd]
  show decide (-d ≤ -(b + 1)) = true
  exact decide_eq_true (by omega)

/-! ## Boolean literal evaluation helpers -/

/-- A positive Boolean literal is true at a reading of its value. -/
theorem posBool_eval_true {a : Assignment} {s : Nat} {b : Bool}
    (h : a[s]? = some (.bool b)) : (posBool s b).eval a = some true := by
  simp [posBool, Literal.eval, Atom.eval, h]

/-- A Boolean reading DECIDES a positive Boolean literal (an undefined or
    wrongly-typed read leaves it undecided). -/
theorem posBool_eval_bool {a : Assignment} {s : Nat} {b b' : Bool}
    (h : a[s]? = some (.bool b')) :
    ∃ t, (posBool s b).eval a = some t :=
  ⟨b' == b, by simp [posBool, Literal.eval, Atom.eval, h]⟩

/-! ## The B arm's implied literal is true at fitting solutions -/

/-- The bounds arm's implied pin is true at every fitting solution of the
    reified constraint (the B-arm implied arm of the safe triple). -/
theorem propLinLeReifB_implied_true {st : State} {coeffs : List Int}
    {is : List Nat} {b : Int} {r : Nat} {l : Literal} {rs : Reason}
    (hlen : coeffs.length = is.length)
    (hrun : propLinLeReifB st coeffs is b r = .implied l rs) :
    ∀ a, Assignment.Fits st.domains a →
      (DomConstraint.linLeReif coeffs is b r).SatisfiedBy a →
      l.eval a = some true := by
  intro a hfit hcons
  rcases propLinLeReifB_emission_inv hrun with hstable |
    ⟨-, -, -, hint, hcomp, hr, hsum, hle, hres⟩ |
    ⟨-, hb, -, hint, hcomp, lo, hsum, hlt, hres⟩
  · exact absurd hstable (by intro hc; cases hc)
  · have hl : l = posBool r true := by
      injection hres
    rw [hl]
    obtain ⟨rb, hread, hiff⟩ := linLeReif_satisfied_inv hcons
    have hreads : ∀ p ∈ coeffs.zip is, ∃ x : Int, a[p.2]! = .int x :=
      fun p hp => domsIntOnlyB_fits_read hint hfit p.2 (mem_zip_snd hp)
    have hne : coeffs.zip is ≠ [] := by
      intro h0
      rw [h0] at hsum
      exact absurd hsum (by simp [sumMax])
    obtain ⟨s, hs, hleS⟩ := dotOver_le_sumMax hne hfit hcomp hreads
    have hs' : s = hr := by
      rw [hsum] at hs
      injection hs with hs2
      exact hs2.symm
    have hlen2 : (is.map (fun i => a[i]!)).length = (intVals coeffs).length := by
      rw [List.length_map, intVals_length]; omega
    obtain ⟨d, hd⟩ := dotProduct_intVals_exists_of_length hlen2
      (by intro x hx
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
          exact domsIntOnlyB_fits_read hint hfit i hi)
    have hd' : dotOver (coeffs.zip is) a 0 = some d := by
      rw [← dotProduct_eq_dotOver hlen]; exact hd
    have hdle : d ≤ hr := by
      rw [← hs']
      exact hleS d hd'
    have hdot : dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b = true := by
      rw [dotLe, hd]
      exact decide_eq_true (by omega)
    have hrb : rb = true := hiff.mpr hdot
    rw [hrb] at hread
    exact posBool_eval_true hread
  · -- PLAN G1d: the dual pin is `r = false`; a fitting solution reads a
    -- Boolean at `r`, and `r = true` would make the dot at most `b` while
    -- the minimum-contribution sum already exceeds it
    have hl : l = posBool r false := by
      injection hres
    rw [hl]
    obtain ⟨rb, hread, hiff⟩ := linLeReif_satisfied_inv hcons
    obtain ⟨hlenR, hallR⟩ := domBoolOnlyB_eq hb
    have hneR : st.domains.getD r Dom.empty ≠ Dom.empty := by
      intro h0
      rw [h0, Dom.enum_empty] at hlenR
      simp at hlenR
    have hltR : r < st.domains.length := by
      by_cases hr : r < st.domains.length
      · exact hr
      · exact absurd (getD_nil_of_length_le hr) hneR
    have hltA : r < a.length := by
      rw [hfit.1]
      exact hltR
    have hreadA : a[r]? = some a[r] := List.getElem?_eq_getElem hltA
    have hmemA : a[r] ∈ Dom.enum (st.domains.getD r Dom.empty) :=
      (DomainLike.mem_iff _ _).mp (hfit.2 r a[r] hreadA)
    obtain ⟨rb2, hrb2⟩ := hallR a[r] hmemA
    have hread2 : a[r]? = some (.bool rb2) := by rw [hreadA, hrb2]
    have hrb2eq : rb2 = rb := bool_read_eq hread2 hread
    have hreads : ∀ p ∈ coeffs.zip is, ∃ x : Int, a[p.2]! = .int x :=
      fun p hp => domsIntOnlyB_fits_read hint hfit p.2 (mem_zip_snd hp)
    have hreadsZ : ∀ p ∈ coeffs.zip is, ∃ i : Int, slotInt a p.2 = some i :=
      fun p hp => by
        obtain ⟨x, hx⟩ := hreads p hp
        exact ⟨x, slotInt_of_getElem_int hx⟩
    have hcf : ∀ q ∈ linCausesMin st (coeffs.zip is), q.eval a = some false :=
      lin2_causesMin_false_of_fits hfit hreadsZ
    have hlen2 : (is.map (fun i => a[i]!)).length = (intVals coeffs).length := by
      rw [List.length_map, intVals_length]; omega
    obtain ⟨d, hd⟩ := dotProduct_intVals_exists_of_length hlen2
      (by intro x hx
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
          exact domsIntOnlyB_fits_read hint hfit i hi)
    have hd' : dotOver (coeffs.zip is) a 0 = some d := by
      rw [← dotProduct_eq_dotOver hlen]; exact hd
    have hdle : lo ≤ d := by
      have hleZ := lin2_sumMin_le hreadsZ hcomp hcf (coeffs.zip is)
        (fun _ hp => hp) lo hsum 0 d hd'
      omega
    have hdot : dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b = false := by
      rw [dotLe, hd]
      exact decide_eq_false (by omega)
    have hrbf : rb = false := by
      cases rb with
      | false => rfl
      | true =>
          exfalso
          have hdotT : dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b = true :=
            hiff.mp rfl
          rw [hdotT] at hdot
          exact Bool.noConfusion hdot
    have hrbf2 : rb2 = false := hrb2eq.trans hrbf
    rw [hrbf2] at hread2
    exact posBool_eval_true hread2

/-! ## The safe triple at fitting solutions -/

/-- The pinned-delegation propagator's safe triple w.r.t. the reified
    family: implied-literal soundness, conflict exclusion, and conflict
    entitlement, at every fitting solution of the reified constraint. -/
theorem propLinLeReif_safe (st : State) (coeffs : List Int) (is : List Nat)
    (b : Int) (r : Nat) :
    (∀ l rs, propLinLeReif st coeffs is b r = .implied l rs →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.linLeReif coeffs is b r).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ c, propLinLeReif st coeffs is b r = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.linLeReif coeffs is b r).SatisfiedBy a → False) ∧
    (∀ c, propLinLeReif st coeffs is b r = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.linLeReif coeffs is b r).SatisfiedBy a →
        ∃ l ∈ c, l.eval a = some true) := by
  by_cases hlenB : (coeffs.length == is.length) = true
  · have hlen : coeffs.length = is.length := beq_iff_eq.mp hlenB
    refine ⟨?_, ?_, ?_⟩
    · intro l rs hrun a hfit hcons
      by_cases h1 : domBoolPin st.domains r true = true
      · rw [propLinLeReif_run_true hlenB h1] at hrun
        obtain ⟨rs0, hres, -⟩ := augmentRes_implied_inv hrun
        have hle := linLeReif_true_dot hcons (fits_of_domBoolPin hfit h1)
        exact (propLinLe2_safe st coeffs is b hlen).1 l rs0 hres a hfit hle
      · by_cases h2 : (domBoolPin st.domains r false
            && domsIntOnlyB st.domains is) = true
        · rw [propLinLeReif_run_false hlenB h1 h2] at hrun
          obtain ⟨rs0, hres, -⟩ := augmentRes_implied_inv hrun
          have h2' := h2
          rw [Bool.and_eq_true] at h2'
          obtain ⟨hpf, hg⟩ := h2'
          have hreads := domsIntOnlyB_fits_read hg hfit
          have hcons' := linLeReif_false_dot hcons (fits_of_domBoolPin hfit hpf)
            hreads hlen
          exact (propLinLe2_safe st (coeffs.map (fun c => -c)) is (-(b + 1))
            (by simp [hlen])).1 l rs0 hres a hfit hcons'
        · rw [propLinLeReif_run_b hlenB h1 h2] at hrun
          exact propLinLeReifB_implied_true hlen hrun a hfit hcons
    · intro c hrun a hfit hcons
      by_cases h1 : domBoolPin st.domains r true = true
      · rw [propLinLeReif_run_true hlenB h1] at hrun
        obtain ⟨c0, hres, -⟩ := augmentRes_conflict_inv hrun
        have hle := linLeReif_true_dot hcons (fits_of_domBoolPin hfit h1)
        exact (propLinLe2_safe st coeffs is b hlen).2.1 c0 hres a hfit hle
      · by_cases h2 : (domBoolPin st.domains r false
            && domsIntOnlyB st.domains is) = true
        · rw [propLinLeReif_run_false hlenB h1 h2] at hrun
          obtain ⟨c0, hres, -⟩ := augmentRes_conflict_inv hrun
          have h2' := h2
          rw [Bool.and_eq_true] at h2'
          obtain ⟨hpf, hg⟩ := h2'
          have hreads := domsIntOnlyB_fits_read hg hfit
          have hcons' := linLeReif_false_dot hcons (fits_of_domBoolPin hfit hpf)
            hreads hlen
          exact (propLinLe2_safe st (coeffs.map (fun c => -c)) is (-(b + 1))
            (by simp [hlen])).2.1 c0 hres a hfit hcons'
        · rw [propLinLeReif_run_b hlenB h1 h2] at hrun
          exact (propLinLeReifB_ne_conflict hrun).elim
    · intro c hrun a hfit hcons
      by_cases h1 : domBoolPin st.domains r true = true
      · rw [propLinLeReif_run_true hlenB h1] at hrun
        obtain ⟨c0, hres, hcl⟩ := augmentRes_conflict_inv hrun
        have hle := linLeReif_true_dot hcons (fits_of_domBoolPin hfit h1)
        obtain ⟨l, hl, hlt⟩ := (propLinLe2_safe st coeffs is b hlen).2.2 c0 hres
          a hfit hle
        exact ⟨l, by rw [hcl]; exact mem_insertAfterHead_of_mem hl, hlt⟩
      · by_cases h2 : (domBoolPin st.domains r false
            && domsIntOnlyB st.domains is) = true
        · rw [propLinLeReif_run_false hlenB h1 h2] at hrun
          obtain ⟨c0, hres, hcl⟩ := augmentRes_conflict_inv hrun
          have h2' := h2
          rw [Bool.and_eq_true] at h2'
          obtain ⟨hpf, hg⟩ := h2'
          have hreads := domsIntOnlyB_fits_read hg hfit
          have hcons' := linLeReif_false_dot hcons (fits_of_domBoolPin hfit hpf)
            hreads hlen
          obtain ⟨l, hl, hlt⟩ := (propLinLe2_safe st (coeffs.map (fun c => -c))
            is (-(b + 1)) (by simp [hlen])).2.2 c0 hres a hfit hcons'
          exact ⟨l, by rw [hcl]; exact mem_insertAfterHead_of_mem hl, hlt⟩
        · rw [propLinLeReif_run_b hlenB h1 h2] at hrun
          exact (propLinLeReifB_ne_conflict hrun).elim
  · have hlenF : (coeffs.length == is.length) = false :=
      Bool.eq_false_iff.mpr hlenB
    refine ⟨?_, ?_, ?_⟩
    · intro l rs hrun
      rw [propLinLeReif_run_arity hlenF] at hrun
      cases hrun
    · intro c hrun
      rw [propLinLeReif_run_arity hlenF] at hrun
      cases hrun
    · intro c hrun
      rw [propLinLeReif_run_arity hlenF] at hrun
      cases hrun

/-! ## The conflict entitlement at faithful solutions -/

/-- The delegated kernels at a solution of the underlying `linLe`: every
    conflict clause of `propLinLe2` carries a true literal (the state-free
    conflict entitlement, keyed on the dot rather than the constraint
    membership). -/
theorem propLinLe2_entitled_dot {st : State} {coeffs : List Int}
    {is : List Nat} {b : Int} {cc : Clause} {a : Assignment}
    (hlen : coeffs.length = is.length)
    (hrun : propLinLe2 st coeffs is b = .conflict cc)
    (hcons : (DomConstraint.linLe coeffs is b).SatisfiedBy a) :
    ∃ l ∈ cc, l.eval a = some true := by
  rcases propLinLe2_emission_inv hrun with hstable |
    ⟨m, i, rest, lr, hmem, hrest, hguard, hsum, hnarrow⟩ |
    ⟨m, i, rest, lr, hmem, hrest, hguard, hsum, hnarrow⟩ |
    ⟨m, i, rest, lr, c, hmem, hpos, hrest, hguard, hsum, hnarrow⟩ |
    ⟨m, i, rest, lr, c, hmem, hneg, hrest, hguard, hsum, hnarrow⟩
  · exact absurd hstable (by intro hc; cases hc)
  · obtain ⟨_, _, _, _, _, hcc⟩ := narrowHi_conflict_inv hnarrow.symm
    have hreads := linLe2_reads_int hcons hlen
    rw [hcc]
    exact lin2_nogood_le_hi_true hmem hrest hguard hsum hreads hcons hlen
  · obtain ⟨_, _, _, _, _, hcc⟩ := narrowLo_conflict_inv hnarrow.symm
    have hreads := linLe2_reads_int hcons hlen
    rw [hcc]
    exact lin2_nogood_le_lo_true hmem hrest hguard hsum hreads hcons hlen
  · obtain ⟨_, _, _, _, _, hcc⟩ := narrowHi_conflict_inv hnarrow.symm
    have hreads := linLe2_reads_int hcons hlen
    rw [hcc]
    exact lin2_nogood_gen_le_hi_true hmem hpos hrest hguard hsum hreads
      hcons hlen
  · obtain ⟨_, _, _, _, _, hcc⟩ := narrowLo_conflict_inv hnarrow.symm
    have hreads := linLe2_reads_int hcons hlen
    rw [hcc]
    exact lin2_nogood_gen_le_lo_true hmem hneg hrest hguard hsum hreads
      hcons hlen

/-- A Boolean reading of an operand makes one of the bounds-arm operand
    escapes true (the PROVABLE cover of the Boolean-read case in the
    fallback reason obligation). -/
theorem linLeReifEscB_true_of_bool_read {is : List Nat} {a : Assignment}
    {i : Nat} {b' : Bool} (hi : i ∈ is) (hread : a[i]? = some (.bool b')) :
    ∃ q ∈ linLeReifEscB is, q.eval a = some true := by
  refine ⟨posBool i b', ?_, posBool_eval_true hread⟩
  rw [linLeReifEscB, List.mem_flatMap]
  refine ⟨i, hi, ?_⟩
  cases b' <;> simp

/-- Every conflict clause of the pinned delegation carries a true literal
    at every faithful solution of the reified constraint. -/
theorem propLinLeReif_entitled {st : State} {coeffs : List Int}
    {is : List Nat} {b : Int} {r : Nat} {cc : Clause}
    {a : Assignment}
    (hrun : propLinLeReif st coeffs is b r = .conflict cc)
    (hfaith : FrameFaithful st.domains a)
    (ha : (DomConstraint.linLeReif coeffs is b r).SatisfiedBy a) :
    ∃ l ∈ cc, l.eval a = some true := by
  obtain ⟨rb, hread, hiff⟩ := linLeReif_satisfied_inv ha
  by_cases hlenB : (coeffs.length == is.length) = true
  · have hlen : coeffs.length = is.length := beq_iff_eq.mp hlenB
    by_cases h1 : domBoolPin st.domains r true = true
    · -- the escape `r = false` is true at `rb = false`; `rb = true` runs
      -- the delegated kernel off the reified dot
      rw [propLinLeReif_run_true hlenB h1] at hrun
      obtain ⟨c0, hres, hcl⟩ := augmentRes_conflict_inv hrun
      cases rb with
      | false =>
          refine ⟨posBool r false, ?_, posBool_eval_true hread⟩
          rw [hcl]
          exact mem_insertAfterHead_of_mem_extras (by simp [linLeReifEscTrue])
      | true =>
          have hle : (DomConstraint.linLe coeffs is b).SatisfiedBy a := by
            show dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b = true
            exact hiff.mp rfl
          obtain ⟨l, hl, hlt⟩ := propLinLe2_entitled_dot (cc := c0) hlen hres hle
          exact ⟨l, by rw [hcl]; exact mem_insertAfterHead_of_mem hl, hlt⟩
    · by_cases h2 : (domBoolPin st.domains r false
          && domsIntOnlyB st.domains is) = true
      · rw [propLinLeReif_run_false hlenB h1 h2] at hrun
        obtain ⟨c0, hres, hcl⟩ := augmentRes_conflict_inv hrun
        have h2' := h2
        rw [Bool.and_eq_true] at h2'
        obtain ⟨hpf, hg⟩ := h2'
        cases rb with
        | true =>
            refine ⟨posBool r true, ?_, posBool_eval_true hread⟩
            rw [hcl]
            exact mem_insertAfterHead_of_mem_extras (by simp [linLeReifEscFalse])
        | false =>
            have hreads := domsIntOnlyB_faithful_read hg hfaith
            have hcons' := linLeReif_false_dot ha hread hreads hlen
            obtain ⟨l, hl, hlt⟩ := propLinLe2_entitled_dot
              (coeffs := coeffs.map (fun c => -c)) (is := is) (b := -(b + 1))
              (st := st) (cc := c0) (by simp [hlen]) hres hcons'
            exact ⟨l, by rw [hcl]; exact mem_insertAfterHead_of_mem hl, hlt⟩
      · rw [propLinLeReif_run_b hlenB h1 h2] at hrun
        exact (propLinLeReifB_ne_conflict hrun).elim
  · have hlenF : (coeffs.length == is.length) = false :=
      Bool.eq_false_iff.mpr hlenB
    rw [propLinLeReif_run_arity hlenF] at hrun
    cases hrun

  /-! ## The delegated clause bundle: pivot, normalization, truth -/

  /-- One arm analysis for the delegated implied emission: the pivot is in
      the clause, every clause literal is normalized, and the clause is true
      at every solution of the underlying `linLe`. -/
  theorem propLinLe2_implied_clause_all {st : State} {coeffs : List Int}
      {is : List Nat} {b : Int} {l : Literal} {rs : Reason}
      (hlen : coeffs.length = is.length)
      (hrun : propLinLe2 st coeffs is b = .implied l rs) :
      l ∈ rs.clause ∧ (∀ q ∈ rs.clause, q = q.norm) ∧
      (∀ a, (DomConstraint.linLe coeffs is b).SatisfiedBy a →
        ∃ q ∈ rs.clause, q.eval a = some true) := by
    rcases propLinLe2_emission_inv hrun with hstable |
      ⟨m, i, rest, lr, hmem, hrest, hguard, hsum, hnarrow⟩ |
      ⟨m, i, rest, lr, hmem, hrest, hguard, hsum, hnarrow⟩ |
      ⟨m, i, rest, lr, c, hmem, hpos, hrest, hguard, hsum, hnarrow⟩ |
      ⟨m, i, rest, lr, c, hmem, hneg, hrest, hguard, hsum, hnarrow⟩
    · exact absurd hstable (by intro hc; cases hc)
    · obtain ⟨hl, hcl⟩ := narrowHi_implied_inv hnarrow.symm
      subst hl
      refine ⟨by rw [hcl]; exact List.mem_cons_self,
        lin2_reason_clause_norm_sf hcl
          (lin2_nogood_norm (posLe_norm m (b - lr)).symm
            (lin2_causesMin_norm (st := st) (rest := rest))), ?_⟩
      intro a hcons
      have hreads := linLe2_reads_int hcons hlen
      have hcl2 : rs.clause = [posLe m (b - lr)] ++ linCausesMin st rest := by
        rw [hcl]
      rw [hcl2]
      exact lin2_nogood_le_hi_true hmem hrest hguard hsum hreads hcons hlen
    · obtain ⟨hl, hcl⟩ := narrowLo_implied_inv hnarrow.symm
      subst hl
      refine ⟨by rw [hcl]; exact List.mem_cons_self,
        lin2_reason_clause_norm_sf hcl
          (lin2_nogood_norm (negLe_norm m (lr - b - 1)).symm
            (lin2_causesMin_norm (st := st) (rest := rest))), ?_⟩
      intro a hcons
      have hreads := linLe2_reads_int hcons hlen
      have hcl2 : rs.clause = [negLe m (lr - b - 1)] ++ linCausesMin st rest := by
        rw [hcl]
      rw [hcl2]
      exact lin2_nogood_le_lo_true hmem hrest hguard hsum hreads hcons hlen
    · obtain ⟨hl, hcl⟩ := narrowHi_implied_inv hnarrow.symm
      subst hl
      refine ⟨by rw [hcl]; exact List.mem_cons_self,
        lin2_reason_clause_norm_sf hcl
          (lin2_nogood_norm (posLe_norm m ((b - lr) / c)).symm
            (lin2_causesMin_norm (st := st) (rest := rest))), ?_⟩
      intro a hcons
      have hreads := linLe2_reads_int hcons hlen
      have hcl2 : rs.clause = [posLe m ((b - lr) / c)] ++ linCausesMin st rest := by
        rw [hcl]
      rw [hcl2]
      exact lin2_nogood_gen_le_hi_true hmem hpos hrest hguard hsum hreads
        hcons hlen
    · obtain ⟨hl, hcl⟩ := narrowLo_implied_inv hnarrow.symm
      subst hl
      refine ⟨by rw [hcl]; exact List.mem_cons_self,
        lin2_reason_clause_norm_sf hcl
          (lin2_nogood_norm (negLe_norm m (-((b - lr) / (-c)) - 1)).symm
            (lin2_causesMin_norm (st := st) (rest := rest))), ?_⟩
      intro a hcons
      have hreads := linLe2_reads_int hcons hlen
      have hcl2 : rs.clause
          = [negLe m (-((b - lr) / (-c)) - 1)] ++ linCausesMin st rest := by
        rw [hcl]
      rw [hcl2]
      exact lin2_nogood_gen_le_lo_true hmem hneg hrest hguard hsum hreads
        hcons hlen

/-! ## The state-free reason validity -/

/-- The bounds arm's implied literals carry valid, normalized reasons at
    every internal solution of any problem containing the reified
    constraint, provided the problem's operand slots are in range (the
    problem-level gate `hlreif`): the pivot pins `r = true`; at
    `r = false` the reif fact falsifies the dot, and the operand escapes
    (Boolean reads) or the max-causes (integer reads: all-false would
    force `Σ ≤ sumMax ≤ b`) supply a true clause literal. -/
theorem propLinLeReifB_reason_valid {problem : Problem DomConstraint Unit}
    {st : State} {coeffs : List Int} {is : List Nat} {b : Int} {r : Nat}
    {l : Literal} {rs : Reason}
    (hview : IntViewedDoms problem.domains)
    (hprob : DomConstraint.linLeReif coeffs is b r ∈ problem.constraints)
    (hlreif : ∀ i ∈ is, i < problem.domains.length)
    (hlen : coeffs.length = is.length)
    (hrun : propLinLeReifB st coeffs is b r = .implied l rs) :
    Reason.Valid problem DomConstraint.SatisfiedBy rs l ∧
      (∀ q ∈ rs.clause, q = q.norm) := by
  rcases propLinLeReifB_emission_inv hrun with hstable |
    ⟨-, -, -, -, hcomp, hr, hsum, hle, hres⟩ |
    ⟨-, hb, -, -, hcomp, lo, hsum, hlt, hres⟩
  · exact absurd hstable (by intro hc; cases hc)
  · have hl : l = posBool r true := by
      injection hres
    have hcl : rs.clause = posBool r true ::
        (linLeReifEscB is ++ linCausesMax st (coeffs.zip is)) := by
      injection hres with h1 h3
      rw [h3]
    refine ⟨lin2_reason_valid_of_clause_true ?_ ?_, ?_⟩
    · rw [hl, hcl]
      exact List.mem_cons_self
    · intro a ha
      obtain ⟨rb, hread, hiff⟩ := linLeReif_satisfied_inv (ha.2 _ hprob)
      rw [hcl]
      cases rb with
      | true =>
          exact ⟨posBool r true, List.mem_cons_self, posBool_eval_true hread⟩
      | false =>
          have hdotnot : ¬ (dotLe (intVals coeffs)
              (is.map (fun i => a[i]!)) b = true) := by
            intro hc
            have h1 : false = true := hiff.mpr hc
            exact Bool.noConfusion h1
          have hdot : dotLe (intVals coeffs)
              (is.map (fun i => a[i]!)) b = false := by
            cases hd2 : dotLe (intVals coeffs)
                (is.map (fun i => a[i]!)) b with
            | false => rfl
            | true => exact absurd hd2 hdotnot
          by_cases hbools : ∃ i ∈ is, ∃ bb : Bool, a[i]? = some (.bool bb)
          · obtain ⟨i, hi, bb, hbi⟩ := hbools
            obtain ⟨q, hq, hqt⟩ := linLeReifEscB_true_of_bool_read hi hbi
            exact ⟨q, List.mem_cons_of_mem _
              (List.mem_append_left _ hq), hqt⟩
          · have hallint : ∀ i ∈ is, ∃ k : Int, a[i]! = .int k := by
              intro i hi
              have hlt : i < problem.domains.length := hlreif i hi
              have hia : i < a.length := by rw [ha.1.1]; exact hlt
              have hread' : a[i]? = some a[i] := List.getElem?_eq_getElem hia
              have hmem : a[i] ∈ problem.domains.getD i Dom.empty :=
                ha.1.2 i (a[i]) hread'
              have hv := hview _ (getD_mem_of_lt hlt) _ hmem
              cases hv' : a[i] with
              | int k =>
                  exact ⟨k, by
                    rw [List.getElem!_eq_getElem?_getD, hread', hv']
                    rfl⟩
              | bool bb =>
                  exact absurd ⟨i, hi, bb, by rw [hread', hv']⟩ hbools
              | setOfInt s =>
                  rw [hv'] at hv
                  exact absurd rfl hv
              | array s =>
                  rw [hv'] at hv
                  exact absurd rfl hv
            have hneZip : coeffs.zip is ≠ [] := by
              intro h0
              rw [h0] at hsum
              exact absurd hsum (by simp [sumMax])
            have hreadsZip : ∀ p ∈ coeffs.zip is,
                ∃ x : Int, a[p.2]! = .int x :=
              fun p hp => hallint p.2 (mem_zip_snd hp)
            by_cases hcause : ∃ q ∈ linCausesMax st (coeffs.zip is),
                q.eval a = some true
            · obtain ⟨q, hq, hqt⟩ := hcause
              exact ⟨q, List.mem_cons_of_mem _
                (List.mem_append_right _ hq), hqt⟩
            · have hcf : ∀ q ∈ linCausesMax st (coeffs.zip is),
                  q.eval a = some false := by
                intro q hq
                obtain ⟨bv, hbval⟩ := lin2_causesMax_eval_some
                  (fun p hp => by
                    obtain ⟨k, hk⟩ := hallint p.2 (mem_zip_snd hp)
                    exact ⟨k, slotInt_of_getElem_int hk⟩) hq
                cases bv with
                | true => exact absurd ⟨q, hq, hbval⟩ hcause
                | false => exact hbval
              obtain ⟨s, hs, hles⟩ :=
                dotOver_le_sumMax_of_causes_false hneZip hcomp hreadsZip hcf
              have hs2 : s = hr := by
                rw [hsum] at hs
                injection hs with hs3
                exact hs3.symm
              have hlen2 : (is.map (fun i => a[i]!)).length
                  = (intVals coeffs).length := by
                rw [List.length_map, intVals_length]
                omega
              obtain ⟨d, hd⟩ := dotProduct_intVals_exists_of_length hlen2
                (by intro x hx
                    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
                    exact hallint i hi)
              have hd' : dotOver (coeffs.zip is) a 0 = some d := by
                rw [← dotProduct_eq_dotOver hlen]
                exact hd
              have hdle : d ≤ hr := by
                rw [← hs2]
                exact hles d hd'
              have hdotT : dotLe (intVals coeffs)
                  (is.map (fun i => a[i]!)) b = true := by
                rw [dotLe, hd]
                exact decide_eq_true (by omega)
              rw [hdotT] at hdot
              exact Bool.noConfusion hdot
    · intro q hq
      rw [hcl] at hq
      rcases List.mem_cons.mp hq with rfl | hq
      · rfl
      · rcases List.mem_append.mp hq with hq | hq
        · rw [linLeReifEscB] at hq
          obtain ⟨i, -, hq2⟩ := List.mem_flatMap.mp hq
          rcases List.mem_cons.mp hq2 with rfl | hq2
          · rfl
          · rw [List.mem_singleton.mp hq2]
            rfl
        · exact lin2_causesMax_norm q hq
  · -- PLAN G1d: the dual pin is `r = false`; at `r = false` the pivot is
    -- true, and at `r = true` the operand escapes, a true min-cause, or
    -- `r = false`'s own falsity (the minimum-contribution sum exceeds `b`)
    -- supply a true clause literal
    have hl : l = posBool r false := by
      injection hres
    have hcl : rs.clause = posBool r false ::
        (linLeReifEscB is ++ linCausesMin st (coeffs.zip is)) := by
      injection hres with h1 h3
      rw [h3]
    refine ⟨lin2_reason_valid_of_clause_true ?_ ?_, ?_⟩
    · rw [hl, hcl]
      exact List.mem_cons_self
    · intro a ha
      obtain ⟨rb, hread, hiff⟩ := linLeReif_satisfied_inv (ha.2 _ hprob)
      rw [hcl]
      cases rb with
      | false =>
          exact ⟨posBool r false, List.mem_cons_self, posBool_eval_true hread⟩
      | true =>
          by_cases hbools : ∃ i ∈ is, ∃ bb : Bool, a[i]? = some (.bool bb)
          · obtain ⟨i, hi, bb, hbi⟩ := hbools
            obtain ⟨q, hq, hqt⟩ := linLeReifEscB_true_of_bool_read hi hbi
            exact ⟨q, List.mem_cons_of_mem _
              (List.mem_append_left _ hq), hqt⟩
          · have hallint : ∀ i ∈ is, ∃ k : Int, a[i]! = .int k := by
              intro i hi
              have hlt : i < problem.domains.length := hlreif i hi
              have hia : i < a.length := by rw [ha.1.1]; exact hlt
              have hread' : a[i]? = some a[i] := List.getElem?_eq_getElem hia
              have hmem : a[i] ∈ problem.domains.getD i Dom.empty :=
                ha.1.2 i (a[i]) hread'
              have hv := hview _ (getD_mem_of_lt hlt) _ hmem
              cases hv' : a[i] with
              | int k =>
                  exact ⟨k, by
                    rw [List.getElem!_eq_getElem?_getD, hread', hv']
                    rfl⟩
              | bool bb =>
                  exact absurd ⟨i, hi, bb, by rw [hread', hv']⟩ hbools
              | setOfInt s =>
                  rw [hv'] at hv
                  exact absurd rfl hv
              | array s =>
                  rw [hv'] at hv
                  exact absurd rfl hv
            have hneZip : coeffs.zip is ≠ [] := by
              intro h0
              rw [h0] at hsum
              exact absurd hsum (by simp [sumMin])
            have hreadsZip : ∀ p ∈ coeffs.zip is,
                ∃ x : Int, a[p.2]! = .int x :=
              fun p hp => hallint p.2 (mem_zip_snd hp)
            have hreadsZ : ∀ p ∈ coeffs.zip is,
                ∃ i : Int, slotInt a p.2 = some i :=
              fun p hp => by
                obtain ⟨x, hx⟩ := hreadsZip p hp
                exact ⟨x, slotInt_of_getElem_int hx⟩
            by_cases hcause : ∃ q ∈ linCausesMin st (coeffs.zip is),
                q.eval a = some true
            · obtain ⟨q, hq, hqt⟩ := hcause
              exact ⟨q, List.mem_cons_of_mem _
                (List.mem_append_right _ hq), hqt⟩
            · have hcf : ∀ q ∈ linCausesMin st (coeffs.zip is),
                  q.eval a = some false := by
                intro q hq
                obtain ⟨bv, hbval⟩ := lin2_causesMin_eval_some
                  (fun p hp => by
                    obtain ⟨k, hk⟩ := hallint p.2 (mem_zip_snd hp)
                    exact ⟨k, slotInt_of_getElem_int hk⟩) hq
                cases bv with
                | true => exact absurd ⟨q, hq, hbval⟩ hcause
                | false => exact hbval
              have hlen2 : (is.map (fun i => a[i]!)).length
                  = (intVals coeffs).length := by
                rw [List.length_map, intVals_length]
                omega
              obtain ⟨d, hd⟩ := dotProduct_intVals_exists_of_length hlen2
                (by intro x hx
                    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
                    exact hallint i hi)
              have hd' : dotOver (coeffs.zip is) a 0 = some d := by
                rw [← dotProduct_eq_dotOver hlen]
                exact hd
              have hdle : lo ≤ d := by
                have hleZ := lin2_sumMin_le hreadsZ hcomp hcf (coeffs.zip is)
                  (fun _ hp => hp) lo hsum 0 d hd'
                omega
              have hdot : dotLe (intVals coeffs)
                  (is.map (fun i => a[i]!)) b = false := by
                rw [dotLe, hd]
                exact decide_eq_false (by omega)
              have hdotT : dotLe (intVals coeffs)
                  (is.map (fun i => a[i]!)) b = true := hiff.mp rfl
              rw [hdotT] at hdot
              exact Bool.noConfusion hdot
    · intro q hq
      rw [hcl] at hq
      rcases List.mem_cons.mp hq with rfl | hq
      · rfl
      · rcases List.mem_append.mp hq with hq | hq
        · rw [linLeReifEscB] at hq
          obtain ⟨i, -, hq2⟩ := List.mem_flatMap.mp hq
          rcases List.mem_cons.mp hq2 with rfl | hq2
          · rfl
          · rw [List.mem_singleton.mp hq2]
            rfl
        · exact lin2_causesMin_norm q hq

/-- The delegation's implied literals carry valid, normalized reasons at
    every internal solution of any problem containing the reified
    constraint (the pinned arms are state-free; the bounds arm needs the
    problem-level operand-range gate `hlreif`). -/
theorem propLinLeReif_reason_valid {problem : Problem DomConstraint Unit}
    {st : State} {coeffs : List Int} {is : List Nat} {b : Int} {r : Nat}
    {l : Literal} {rs : Reason}
    (hview : IntViewedDoms problem.domains)
    (hprob : DomConstraint.linLeReif coeffs is b r ∈ problem.constraints)
    (hlreif : ∀ dc ∈ problem.constraints, ∀ coeffs is b r,
      dc = .linLeReif coeffs is b r → ∀ i ∈ is, i < problem.domains.length)
    (hrun : propLinLeReif st coeffs is b r = .implied l rs) :
    Reason.Valid problem DomConstraint.SatisfiedBy rs l ∧
      (∀ q ∈ rs.clause, q = q.norm) := by
  by_cases hlenB : (coeffs.length == is.length) = true
  · have hlen : coeffs.length = is.length := beq_iff_eq.mp hlenB
    by_cases h1 : domBoolPin st.domains r true = true
    · rw [propLinLeReif_run_true hlenB h1] at hrun
      obtain ⟨rs0, hres, hcl⟩ := augmentRes_implied_inv hrun
      obtain ⟨hpiv, hnorm0, htrue0⟩ := propLinLe2_implied_clause_all hlen hres
      refine ⟨lin2_reason_valid_of_clause_true ?hmem ?htrue, ?hnorm⟩
      · rw [hcl]
        exact mem_insertAfterHead_of_mem hpiv
      · intro a ha
        obtain ⟨rb, hread, hiff⟩ := linLeReif_satisfied_inv (ha.2 _ hprob)
        rw [hcl]
        cases rb with
        | false =>
            exact ⟨posBool r false,
              mem_insertAfterHead_of_mem_extras (by simp [linLeReifEscTrue]),
              posBool_eval_true hread⟩
        | true =>
            have hle : (DomConstraint.linLe coeffs is b).SatisfiedBy a := by
              show dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b = true
              exact hiff.mp rfl
            obtain ⟨q, hq, hqt⟩ := htrue0 a hle
            exact ⟨q, mem_insertAfterHead_of_mem hq, hqt⟩
      · intro q hq
        rw [hcl] at hq
        rcases mem_insertAfterHead hq with hq | hq
        · exact hnorm0 q hq
        · simp only [linLeReifEscTrue, List.mem_singleton] at hq
          rw [hq]
          simp [posBool, Literal.norm]
    · by_cases h2 : (domBoolPin st.domains r false
          && domsIntOnlyB st.domains is) = true
      · -- PLAN G1d: the retained delegated bound implication at `r = false`
        rw [propLinLeReif_run_false hlenB h1 h2] at hrun
        obtain ⟨rs0, hres, hcl⟩ := augmentRes_implied_inv hrun
        obtain ⟨hpiv, hnorm0, htrue0⟩ :=
          propLinLe2_implied_clause_all (by simp [hlen]) hres
        have h2' := h2
        rw [Bool.and_eq_true] at h2'
        obtain ⟨hpf, hg⟩ := h2'
        refine ⟨lin2_reason_valid_of_clause_true ?_ ?_, ?_⟩
        · rw [hcl]
          exact mem_insertAfterHead_of_mem hpiv
        · intro a ha
          obtain ⟨rb, hread, hiff⟩ := linLeReif_satisfied_inv (ha.2 _ hprob)
          rw [hcl]
          cases rb with
          | true =>
              exact ⟨posBool r true,
                mem_insertAfterHead_of_mem_extras (by simp [linLeReifEscFalse]),
                posBool_eval_true hread⟩
          | false =>
              by_cases hbools : ∃ i ∈ is, ∃ bb : Bool, a[i]? = some (.bool bb)
              · obtain ⟨i, hi, bb, hbi⟩ := hbools
                obtain ⟨q, hq, hqt⟩ := linLeReifEscB_true_of_bool_read hi hbi
                have hqf : q ∈ linLeReifEscFalse is r := by
                  rw [linLeReifEscFalse]
                  exact List.mem_cons_of_mem _ hq
                exact ⟨q, mem_insertAfterHead_of_mem_extras hqf, hqt⟩
              · have hallint : ∀ i ∈ is, ∃ k : Int, a[i]! = .int k := by
                  intro i hi
                  have hlt : i < problem.domains.length :=
                    hlreif _ hprob coeffs is b r rfl i hi
                  have hia : i < a.length := by rw [ha.1.1]; exact hlt
                  have hread' : a[i]? = some a[i] :=
                    List.getElem?_eq_getElem hia
                  have hmem : a[i] ∈ problem.domains.getD i Dom.empty :=
                    ha.1.2 i (a[i]) hread'
                  have hv := hview _ (getD_mem_of_lt hlt) _ hmem
                  cases hv' : a[i] with
                  | int k =>
                      exact ⟨k, by
                        rw [List.getElem!_eq_getElem?_getD, hread', hv']
                        rfl⟩
                  | bool bb =>
                      exact absurd ⟨i, hi, bb, by rw [hread', hv']⟩ hbools
                  | setOfInt s =>
                      rw [hv'] at hv
                      exact absurd rfl hv
                  | array s =>
                      rw [hv'] at hv
                      exact absurd rfl hv
                have hcons' := linLeReif_false_dot (ha.2 _ hprob) hread
                  hallint hlen
                obtain ⟨q, hq, hqt⟩ := htrue0 a hcons'
                exact ⟨q, mem_insertAfterHead_of_mem hq, hqt⟩
        · intro q hq
          rw [hcl] at hq
          rcases mem_insertAfterHead hq with hq | hq
          · exact hnorm0 q hq
          · rw [linLeReifEscFalse] at hq
            rcases List.mem_cons.mp hq with rfl | hq
            · rfl
            · obtain ⟨i, -, hq2⟩ := List.mem_flatMap.mp hq
              rcases List.mem_cons.mp hq2 with rfl | hq2
              · rfl
              · rw [List.mem_singleton.mp hq2]
                rfl
      · rw [propLinLeReif_run_b hlenB h1 h2] at hrun
        exact propLinLeReifB_reason_valid hview hprob
          (hlreif _ hprob coeffs is b r rfl) hlen hrun
  · have hlenF : (coeffs.length == is.length) = false :=
      Bool.eq_false_iff.mpr hlenB
    rw [propLinLeReif_run_arity hlenF] at hrun
    cases hrun


/-! ## L2: the explained `int_lin_ne` propagator -/

/-- The integer a slot is pinned to by its (singleton integer) domain. -/
def pinInt (doms : List Domain) (s : Nat) : Option Int :=
  match Dom.enum (doms.getD s Dom.empty) with
  | [.int v] => some v
  | _ => none

/-- Fast twin of `pinInt`: inspect the compact representation directly
    instead of materialising `Dom.enum`. -/
def pinIntFast (doms : List Domain) (s : Nat) : Option Int :=
  (doms.getD s Dom.empty).intSingleton?

theorem pinIntFast_eq (doms : List Domain) (s : Nat) :
    pinIntFast doms s = pinInt doms s := by
  unfold pinIntFast pinInt
  exact Dom.intSingleton?_eq _

attribute [implemented_by pinIntFast] pinInt

/-- Sum of the pinned operands' contributions. -/
def linNeSum (doms : List Domain) : List (Int × Nat) → Int
  | [] => 0
  | (c, s) :: rest =>
      match pinInt doms s with
      | some v => c * v + linNeSum doms rest
      | none => linNeSum doms rest

/-- The fix literals `x_s ≠ v_s` of the pinned operands. -/
def linNeCauses (doms : List Domain) : List (Int × Nat) → Clause
  | [] => []
  | (c, s) :: rest =>
      match pinInt doms s with
      | some v => posNe s v :: linNeCauses doms rest
      | none => linNeCauses doms rest

/-- The unpinned operands. -/
def linNeFree (doms : List Domain) : List (Int × Nat) → List (Int × Nat)
  | [] => []
  | (c, s) :: rest =>
      match pinInt doms s with
      | some _ => linNeFree doms rest
      | none => (c, s) :: linNeFree doms rest

/-- The explained `int_lin_ne` propagator. -/
def propLinNe (st : State) (coeffs : List Int) (is : List Nat) (b : Int) :
    PropagationResult :=
  if coeffs.length == is.length then
    match linNeFree st.domains (coeffs.zip is) with
    | [] =>
        if linNeSum st.domains (coeffs.zip is) == b then
          .conflict (linNeCauses st.domains (coeffs.zip is))
        else .stable
    | [(c, m)] =>
        let s := b - linNeSum st.domains (coeffs.zip is)
        if c != 0 && s % c == 0
            && Dom.memBool (st.domains.getD m Dom.empty) (.int (s / c)) then
          .implied (posNe m (s / c))
            { clause := posNe m (s / c) :: linNeCauses st.domains (coeffs.zip is) }
        else .stable
    | _ => .stable
  else .stable

theorem eq_of_pinInt {doms : List Domain} {s : Nat} {v : Int}
    (h : pinInt doms s = some v) :
    Dom.enum (doms.getD s Dom.empty) = [.int v] := by
  unfold pinInt at h
  split at h
  · rename_i v' heq
    have := Option.some.inj h
    subst this
    exact heq
  · cases h

theorem pinInt_of_eq {doms : List Domain} {s : Nat} {v : Int}
    (h : Dom.enum (doms.getD s Dom.empty) = [.int v]) : pinInt doms s = some v := by
  unfold pinInt
  rw [h]

theorem linNeCauses_mem {doms : List Domain} {ps : List (Int × Nat)} {q : Literal} :
    q ∈ linNeCauses doms ps ↔
      ∃ c s v, (c, s) ∈ ps ∧ pinInt doms s = some v ∧ q = posNe s v := by
  induction ps with
  | nil => simp [linNeCauses]
  | cons p rest ih =>
      obtain ⟨c0, s0⟩ := p
      unfold linNeCauses
      cases hp : pinInt doms s0 with
      | none =>
          simp only []
          rw [ih]
          constructor
          · rintro ⟨c, s, v, hm, hv, hq⟩
            exact ⟨c, s, v, List.mem_cons_of_mem _ hm, hv, hq⟩
          · rintro ⟨c, s, v, hm, hv, hq⟩
            rcases List.mem_cons.mp hm with hm | hm
            · injection hm with h1 h2
              subst h2
              rw [hp] at hv
              cases hv
            · exact ⟨c, s, v, hm, hv, hq⟩
      | some v0 =>
          simp only []
          rw [List.mem_cons, ih]
          constructor
          · rintro (hq | ⟨c, s, v, hm, hv, hq⟩)
            · exact ⟨c0, s0, v0, List.mem_cons_self, hp, hq⟩
            · exact ⟨c, s, v, List.mem_cons_of_mem _ hm, hv, hq⟩
          · rintro ⟨c, s, v, hm, hv, hq⟩
            rcases List.mem_cons.mp hm with hm | hm
            · injection hm with h1 h2
              subst h2
              rw [hp] at hv
              cases hv
              exact Or.inl hq
            · exact Or.inr ⟨c, s, v, hm, hv, hq⟩

theorem linNeFree_mem {doms : List Domain} {ps : List (Int × Nat)} {p : Int × Nat}
    (h : p ∈ linNeFree doms ps) : p ∈ ps ∧ pinInt doms p.2 = none := by
  induction ps with
  | nil => simp [linNeFree] at h
  | cons q rest ih =>
      obtain ⟨c0, s0⟩ := q
      unfold linNeFree at h
      cases hp : pinInt doms s0 with
      | some v0 =>
          rw [hp] at h
          obtain ⟨h1, h2⟩ := ih h
          exact ⟨List.mem_cons_of_mem _ h1, h2⟩
      | none =>
          rw [hp] at h
          rcases List.mem_cons.mp h with h | h
          · subst h
            exact ⟨List.mem_cons_self, hp⟩
          · obtain ⟨h1, h2⟩ := ih h
            exact ⟨List.mem_cons_of_mem _ h1, h2⟩

/-! ## Locality of the `int_lin_ne` kernel (PLAN P1 scheduled scan)

Every read of the `int_lin_ne` kernel goes through `st.domains.getD s Dom.empty`
for a slot `s` drawn from the constraint's slot list (`pinInt` on the
`coeffs.zip is` pairs); these lemmas record that pointwise-equal domains
on the read slots yield equal runs. -/

/-- `pinInt` reads only its slot's domain. -/
theorem pinInt_local {doms1 doms2 : List Domain} {s : Nat}
    (h : doms1.getD s Dom.empty = doms2.getD s Dom.empty) :
    pinInt doms1 s = pinInt doms2 s := by
  unfold pinInt
  rw [h]

/-- `linNeSum` depends only on the pairs' slots. -/
theorem linNeSum_local {doms1 doms2 : List Domain} {ps : List (Int × Nat)}
    (h : ∀ p ∈ ps, doms1.getD p.2 Dom.empty = doms2.getD p.2 Dom.empty) :
    linNeSum doms1 ps = linNeSum doms2 ps := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨c, s⟩ := p
      have hp := pinInt_local (h (c, s) (List.mem_cons_self ..))
      have hr := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
      rw [linNeSum, linNeSum, hp, hr]

/-- `linNeCauses` depends only on the pairs' slots. -/
theorem linNeCauses_local {doms1 doms2 : List Domain} {ps : List (Int × Nat)}
    (h : ∀ p ∈ ps, doms1.getD p.2 Dom.empty = doms2.getD p.2 Dom.empty) :
    linNeCauses doms1 ps = linNeCauses doms2 ps := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨c, s⟩ := p
      have hp := pinInt_local (h (c, s) (List.mem_cons_self ..))
      have hr := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
      rw [linNeCauses, linNeCauses, hp, hr]

/-- `linNeFree` depends only on the pairs' slots. -/
theorem linNeFree_local {doms1 doms2 : List Domain} {ps : List (Int × Nat)}
    (h : ∀ p ∈ ps, doms1.getD p.2 Dom.empty = doms2.getD p.2 Dom.empty) :
    linNeFree doms1 ps = linNeFree doms2 ps := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨c, s⟩ := p
      have hp := pinInt_local (h (c, s) (List.mem_cons_self ..))
      have hr := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
      rw [linNeFree, linNeFree, hp, hr]

/-- `propLinNe` reads only the slots of `is`: pointwise-equal domains on
    `is` yield equal runs. -/
theorem propLinNe_local {st1 st2 : State} {coeffs : List Int} {is : List Nat}
    {b : Int}
    (h : ∀ i ∈ is, st1.domains.getD i Dom.empty = st2.domains.getD i Dom.empty) :
    propLinNe st1 coeffs is b = propLinNe st2 coeffs is b := by
  have hzip : ∀ p ∈ coeffs.zip is,
      st1.domains.getD p.2 Dom.empty = st2.domains.getD p.2 Dom.empty :=
    fun p hp => h p.2 (mem_zip_snd hp)
  have hfree := linNeFree_local hzip
  have hsum := linNeSum_local hzip
  have hcauses := linNeCauses_local hzip
  unfold propLinNe
  rw [hfree, hsum, hcauses]
  by_cases hlen : (coeffs.length == is.length) = true
  · simp only [if_pos hlen]
    cases hfl : linNeFree st2.domains (coeffs.zip is) with
    | nil => rfl
    | cons q qs =>
        cases qs with
        | nil =>
            obtain ⟨c, m⟩ := q
            have hm : m ∈ is :=
              mem_zip_snd (linNeFree_mem (hfl ▸ List.mem_singleton_self (c, m))).1
            simp only [h m hm]
        | cons q' qs' => rfl
  · simp only [if_neg hlen]

/-- Pinned operands read their pins, so the dot product factors through the
    unpinned operands. -/
theorem dotOver_scan {doms : List Domain} {a : Assignment}
    {ps : List (Int × Nat)}
    (H : ∀ c s v, (c, s) ∈ ps → pinInt doms s = some v → a[s]! = .int v)
    (acc : Int) :
    dotOver ps a acc =
      dotOver (linNeFree doms ps) a (acc + linNeSum doms ps) := by
  induction ps generalizing acc with
  | nil => simp [linNeFree, linNeSum, dotOver]
  | cons p rest ih =>
      obtain ⟨c0, s0⟩ := p
      have ih' := ih (fun c s v hm hv => H c s v (List.mem_cons_of_mem _ hm) hv)
      unfold linNeFree linNeSum
      cases hp : pinInt doms s0 with
      | some v0 =>
          simp only []
          have hread := H c0 s0 v0 List.mem_cons_self hp
          rw [dotOver, hread]
          simp only []
          rw [ih' (acc + c0 * v0)]
          congr 1
          omega
      | none =>
          simp only []
          rw [dotOver, dotOver]
          cases hr : a[s0]! with
          | int x =>
              simp only []
              rw [ih' (acc + c0 * x)]
              congr 1
              omega
          | bool x => rfl
          | setOfInt x => rfl
          | array x => rfl

theorem linNe_sat_dot {coeffs : List Int} {is : List Nat} {b : Int}
    {a : Assignment} (hlen : coeffs.length = is.length)
    (h : (DomConstraint.linNe coeffs is b).SatisfiedBy a) :
    (∃ d, dotOver (coeffs.zip is) a 0 = some d ∧ d ≠ b) ∧
      ∀ t ∈ is, ∃ x, a[t]! = .int x := by
  have h' : dotNe (intVals coeffs) (is.map (fun i => a[i]!)) b = true := h
  obtain ⟨d, hd, hne⟩ := (dotNe_eq _ _ _).mp h'
  refine ⟨⟨d, ?_, hne⟩, dotProduct_reads_int hd⟩
  rw [← dotProduct_eq_dotOver hlen]
  exact hd

/-- Fitting assignments read the pins. -/
theorem pinInt_read_of_fits {doms : List Domain} {a : Assignment}
    (hfit : Assignment.Fits doms a) {s : Nat} {v : Int}
    (h : pinInt doms s = some v) : a[s]! = .int v := by
  have hg := eq_of_pinInt h
  have hlt : s < doms.length := by
    by_cases hlt : s < doms.length
    · exact hlt
    · rw [getD_nil_of_length_le hlt] at hg
      cases hg
  have hlen : s < a.length := by rw [hfit.1]; exact hlt
  have hread : a[s]? = some a[s] := List.getElem?_eq_getElem hlen
  have hmem : a[s] ∈ doms.getD s Dom.empty := hfit.2 s (a[s]) hread
  have hmemE : a[s] ∈ Dom.enum (doms.getD s Dom.empty) :=
    (DomainLike.mem_iff _ _).mp hmem
  rw [hg] at hmemE
  have : a[s] = .int v := List.mem_singleton.mp hmemE
  rw [List.getElem!_eq_getElem?_getD, hread]
  exact this

theorem slotBang_int' {a : List Value} {i : Nat} {p : Int}
    (h : a[i]! = .int p) : a[i]? = some (.int p) := by
  by_cases hi : i < a.length
  · rw [getElem!_pos a i hi] at h
    rw [List.getElem?_eq_getElem hi]; exact congrArg some h
  · rw [getElem!_neg a i hi] at h
    exact absurd h (by intro hc; cases hc)

theorem posNe_true_of_read {a : Assignment} {s : Nat} {x v : Int}
    (hx : a[s]! = .int x) (hne : x ≠ v) : (posNe s v).eval a = some true := by
  rw [eval_posNe_iff]
  exact ⟨x, by simp [slotInt, slotBang_int' hx, Value.intView], hne⟩

theorem eq_of_posNe_not_true {a : Assignment} {s : Nat} {x v : Int}
    (hx : a[s]! = .int x) (h : ¬ (posNe s v).eval a = some true) : x = v := by
  by_cases hxv : x = v
  · exact hxv
  · exact absurd (posNe_true_of_read hx hxv) h


theorem propLinNe_conflict_inv {st : State} {coeffs : List Int} {is : List Nat}
    {b : Int} {cc : Clause}
    (h : propLinNe st coeffs is b = .conflict cc) :
    coeffs.length = is.length ∧
      linNeFree st.domains (coeffs.zip is) = [] ∧
      linNeSum st.domains (coeffs.zip is) = b ∧
      cc = linNeCauses st.domains (coeffs.zip is) := by
  unfold propLinNe at h
  by_cases hl : (coeffs.length == is.length) = true
  · rw [if_pos hl] at h
    dsimp only at h
    refine ⟨beq_iff_eq.mp hl, ?_⟩
    split at h
    · rename_i hfree
      split at h
      · rename_i hs
        injection h with h
        exact ⟨hfree, beq_iff_eq.mp hs, h.symm⟩
      · cases h
    · split at h
      · cases h
      · cases h
    · cases h
  · rw [if_neg hl] at h
    cases h

theorem propLinNe_implied_inv {st : State} {coeffs : List Int} {is : List Nat}
    {b : Int} {l : Literal} {rs : Reason}
    (h : propLinNe st coeffs is b = .implied l rs) :
    coeffs.length = is.length ∧ ∃ c m,
      linNeFree st.domains (coeffs.zip is) = [(c, m)] ∧ c ≠ 0 ∧
      (b - linNeSum st.domains (coeffs.zip is)) % c = 0 ∧
      Value.int ((b - linNeSum st.domains (coeffs.zip is)) / c) ∈
        st.domains.getD m Dom.empty ∧
      l = posNe m ((b - linNeSum st.domains (coeffs.zip is)) / c) ∧
      rs = { clause := posNe m ((b - linNeSum st.domains (coeffs.zip is)) / c)
              :: linNeCauses st.domains (coeffs.zip is) } := by
  unfold propLinNe at h
  by_cases hl : (coeffs.length == is.length) = true
  · rw [if_pos hl] at h
    dsimp only at h
    refine ⟨beq_iff_eq.mp hl, ?_⟩
    split at h
    · split at h <;> cases h
    · rename_i c m hfree
      split at h
      · rename_i hc
        injection h with h1 h2
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hc
        obtain ⟨⟨hc0, hmod⟩, hmem⟩ := hc
        exact ⟨c, m, hfree, hc0, hmod,
          (DomainLike.mem_iff _ _).mpr ((Dom.memBool_iff _ _).mp hmem), h1.symm, h2.symm⟩
      · cases h
    · cases h
  · rw [if_neg hl] at h
    cases h

/-- All operands read their pins and nothing is free: the sum is `b`, so the
    constraint fails. -/
theorem linNe_conflict_false {st : State} {coeffs : List Int} {is : List Nat}
    {b : Int} {a : Assignment} (hlen : coeffs.length = is.length)
    (hsat : (DomConstraint.linNe coeffs is b).SatisfiedBy a)
    (hfree : linNeFree st.domains (coeffs.zip is) = [])
    (hsum : linNeSum st.domains (coeffs.zip is) = b)
    (H : ∀ c s v, (c, s) ∈ coeffs.zip is → pinInt st.domains s = some v →
      a[s]! = .int v) : False := by
  obtain ⟨⟨d, hd, hne⟩, -⟩ := linNe_sat_dot hlen hsat
  rw [dotOver_scan H, hfree] at hd
  simp only [dotOver, Int.zero_add] at hd
  exact hne (by rw [← Option.some.inj hd]; exact hsum)

/-- All pinned operands read their pins and one operand is free: the free
    slot avoids the forbidden value. -/
theorem linNe_free_true {st : State} {coeffs : List Int} {is : List Nat}
    {b : Int} {a : Assignment} (hlen : coeffs.length = is.length)
    (hsat : (DomConstraint.linNe coeffs is b).SatisfiedBy a)
    {c : Int} {m : Nat}
    (hfree : linNeFree st.domains (coeffs.zip is) = [(c, m)])
    (hmod : (b - linNeSum st.domains (coeffs.zip is)) % c = 0)
    (H : ∀ c s v, (c, s) ∈ coeffs.zip is → pinInt st.domains s = some v →
      a[s]! = .int v) :
    (posNe m ((b - linNeSum st.domains (coeffs.zip is)) / c)).eval a = some true := by
  obtain ⟨⟨d, hd, hne⟩, hreads⟩ := linNe_sat_dot hlen hsat
  rw [dotOver_scan H, hfree] at hd
  have hm : m ∈ is := by
    have := (linNeFree_mem (by rw [hfree]; exact List.mem_singleton_self (c, m))).1
    exact (List.of_mem_zip this).2
  obtain ⟨x, hx⟩ := hreads m hm
  simp only [dotOver, hx, Int.zero_add] at hd
  apply posNe_true_of_read hx
  intro hxv
  apply hne
  have hdiv : c * ((b - linNeSum st.domains (coeffs.zip is)) / c)
      = b - linNeSum st.domains (coeffs.zip is) :=
    Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hmod)
  rw [← Option.some.inj hd, hxv]
  omega

theorem propLinNe_safe (st : State) (coeffs : List Int) (is : List Nat) (b : Int) :
    (∀ l rs, propLinNe st coeffs is b = .implied l rs →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.linNe coeffs is b).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ c, propLinNe st coeffs is b = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.linNe coeffs is b).SatisfiedBy a → False) ∧
    (∀ c, propLinNe st coeffs is b = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.linNe coeffs is b).SatisfiedBy a →
        ∃ l ∈ c, l.eval a = some true) := by
  have hexcl : ∀ c, propLinNe st coeffs is b = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.linNe coeffs is b).SatisfiedBy a → False := by
    intro c hrun a hfit hsat
    obtain ⟨hlen, hfree, hsum, -⟩ := propLinNe_conflict_inv hrun
    exact linNe_conflict_false hlen hsat hfree hsum
      (fun c s v _ hv => pinInt_read_of_fits hfit hv)
  refine ⟨?_, hexcl, fun c hrun a hfit hsat => (hexcl c hrun a hfit hsat).elim⟩
  intro l rs hrun a hfit hsat
  obtain ⟨hlen, c, m, hfree, hc0, hmod, hmem, hl, -⟩ := propLinNe_implied_inv hrun
  rw [hl]
  exact linNe_free_true hlen hsat hfree hmod
    (fun c s v _ hv => pinInt_read_of_fits hfit hv)

/-- If no cause literal is true at a satisfying assignment, every pinned
    operand reads its pin. -/
theorem linNe_causes_read {st : State} {coeffs : List Int} {is : List Nat}
    {b : Int} {a : Assignment} (hlen : coeffs.length = is.length)
    (hsat : (DomConstraint.linNe coeffs is b).SatisfiedBy a)
    (hnone : ∀ q ∈ linNeCauses st.domains (coeffs.zip is), ¬ q.eval a = some true) :
    ∀ c s v, (c, s) ∈ coeffs.zip is → pinInt st.domains s = some v →
      a[s]! = .int v := by
  intro c s v hm hv
  obtain ⟨-, hreads⟩ := linNe_sat_dot hlen hsat
  obtain ⟨x, hx⟩ := hreads s (List.of_mem_zip hm).2
  have hq : posNe s v ∈ linNeCauses st.domains (coeffs.zip is) :=
    linNeCauses_mem.mpr ⟨c, s, v, hm, hv, rfl⟩
  have := eq_of_posNe_not_true hx (hnone _ hq)
  rw [hx, this]

/-- The conflict clause is entitled at every satisfying assignment (state-free:
    no fit or faithfulness needed). -/
theorem propLinNe_entitled {st : State} {coeffs : List Int} {is : List Nat}
    {b : Int} {cc : Clause} {a : Assignment}
    (hrun : propLinNe st coeffs is b = .conflict cc)
    (ha : (DomConstraint.linNe coeffs is b).SatisfiedBy a) :
    ∃ l ∈ cc, l.eval a = some true := by
  obtain ⟨hlen, hfree, hsum, hcl⟩ := propLinNe_conflict_inv hrun
  refine Classical.byContradiction fun hno => ?_
  have hno' : ∀ q ∈ linNeCauses st.domains (coeffs.zip is), ¬ q.eval a = some true :=
    fun q hq hqt => hno ⟨q, by rw [hcl]; exact hq, hqt⟩
  exact linNe_conflict_false hlen ha hfree hsum (linNe_causes_read hlen ha hno')

/-- State-free reason validity of the implied literal. -/
theorem propLinNe_reason_valid {problem : Problem DomConstraint Unit}
    {st : State} {coeffs : List Int} {is : List Nat} {b : Int}
    {l : Literal} {rs : Reason}
    (hprob : DomConstraint.linNe coeffs is b ∈ problem.constraints)
    (hrun : propLinNe st coeffs is b = .implied l rs) :
    Reason.Valid problem DomConstraint.SatisfiedBy rs l ∧
      (∀ q ∈ rs.clause, q = q.norm) := by
  obtain ⟨hlen, c, m, hfree, hc0, hmod, hmem, hl, hrs⟩ := propLinNe_implied_inv hrun
  have hmemc : l ∈ rs.clause := by rw [hrs, hl]; exact List.mem_cons_self
  refine ⟨lin2_reason_valid_of_clause_true hmemc ?_, ?_⟩
  · intro a ha
    have hsat := ha.2 _ hprob
    by_cases ht : (posNe m ((b - linNeSum st.domains (coeffs.zip is)) / c)).eval a
        = some true
    · exact ⟨l, hmemc, by rw [hl]; exact ht⟩
    · by_cases hex : ∃ q ∈ linNeCauses st.domains (coeffs.zip is),
          q.eval a = some true
      · obtain ⟨q, hq, hqt⟩ := hex
        exact ⟨q, by rw [hrs]; exact List.mem_cons_of_mem _ hq, hqt⟩
      · have H := linNe_causes_read hlen hsat (fun q hq hqt => hex ⟨q, hq, hqt⟩)
        exact absurd (linNe_free_true hlen hsat hfree hmod H) ht
  · intro q hq
    rw [hrs] at hq
    rcases List.mem_cons.mp hq with rfl | hq
    · simp [posNe, Literal.norm]
    · obtain ⟨c', s, v, -, -, rfl⟩ := linNeCauses_mem.mp hq
      simp [posNe, Literal.norm]


/-- The implied literal is decided at every solution of a problem containing
    the constraint: the satisfied dot product forces an integer read of the
    free operand. -/
theorem propLinNe_implied_decided {problem : Problem DomConstraint Unit}
    {st : State} {coeffs : List Int} {is : List Nat} {b : Int}
    {l : Literal} {rs : Reason} {a : Assignment}
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a)
    (hprob : DomConstraint.linNe coeffs is b ∈ problem.constraints)
    (hrun : propLinNe st coeffs is b = .implied l rs) :
    ∃ t, l.eval a = some t := by
  obtain ⟨hlen, c, m, hfree, -, -, -, hl, -⟩ := propLinNe_implied_inv hrun
  obtain ⟨-, hreads⟩ := linNe_sat_dot hlen (ha.2 _ hprob)
  have hm : m ∈ is := by
    have := (linNeFree_mem (by rw [hfree]; exact List.mem_singleton_self (c, m))).1
    exact (List.of_mem_zip this).2
  obtain ⟨x, hx⟩ := hreads m hm
  rw [hl, eval_posNe]
  refine ⟨decide (x ≠ (b - linNeSum st.domains (coeffs.zip is)) / c), ?_⟩
  simp [slotInt, slotBang_int' hx, Value.intView]


/-! ## L5 local helper twins

The three bound-extrema helpers of the "L1a consumers' helpers" section
sit in the file's NESTED `namespace LeanFzn.Solver.Propagation` region
(they are only used by the L1a obligations there); the L5 section below
sits in the flat namespace, so it carries local, structurally identical
twins (the module's usual "local copies of shared kernels" discipline). -/

theorem linReifNarrowHi_bounds_of_implied {st : State} {s : Nat} {hi : Int}
    {ng : Clause} {l : Literal} {rs : Reason}
    (h : narrowHi st s hi ng = .implied l rs) :
    ∃ mn mx, domMinI (st.domains.getD s Dom.empty) = some mn ∧
      domMaxI (st.domains.getD s Dom.empty) = some mx := by
  unfold narrowHi at h
  split at h
  · rename_i mn mx hmn hmx
    exact ⟨mn, mx, hmn, hmx⟩
  · cases h

theorem linReifNarrowLo_bounds_of_implied {st : State} {s : Nat} {lo : Int}
    {ng : Clause} {l : Literal} {rs : Reason}
    (h : narrowLo st s lo ng = .implied l rs) :
    ∃ mn mx, domMinI (st.domains.getD s Dom.empty) = some mn ∧
      domMaxI (st.domains.getD s Dom.empty) = some mx := by
  unfold narrowLo at h
  split at h
  · rename_i mn mx hmn hmx
    exact ⟨mn, mx, hmn, hmx⟩
  · cases h

theorem linReif_getD_ne_nil_of_domMinI {d' : List Domain} {s : Nat}
    {mn : Int} (h : domMinI (d'.getD s Dom.empty) = some mn) :
    d'.getD s Dom.empty ≠ Dom.empty := by
  intro h0
  rw [h0] at h
  have h0' : domMinI (Dom.empty : Domain) = none := by
    unfold domMinI domInts
    rw [domElems_eq_enum, Dom.enum_empty]
    rfl
  rw [h0'] at h
  exact absurd h (by simp)

/-! ## L5: the pinned reified linear equalities/disequalities

`int_lin_eq_reif coeffs is b r` and `int_lin_ne_reif coeffs is b r`
are the `linEq`/`linNe` twins of L1a's `linLeReif`: their
`SatisfiedBy` reads the reif slot as a Boolean and reifies the
underlying DOT predicate, with the same three-valued dot (`dotProduct`
refuses Boolean operands; the clause literals read Booleans as 0/1).
The pinned-direction delegation therefore mirrors L1a exactly:

* r pinned `true`: delegate to the explained inner propagator
  (`propLinEq2` resp. `propLinNe`), each emitted clause augmented
  with the escape `posBool r false` (the reified fact holds only
  when `r` reads `true`);
* r pinned `false` over integer-only operand domains: the reif fact
  FALSIFIES the inner predicate, whose complement is
  `.linNe`/`.linEq` only when the dot exists; the delegation goes to
  the complemented inner propagator with the escapes `posBool r true`
  and the per-slot Boolean-read literals, and (as in L1a) reports
  CONFLICTS ONLY — its bound implications would need the state-box /
  problem-box slot-count premise that `PropagationContract.reason`
  does not carry. -/

/-- The pinned-direction delegation for `int_lin_eq_reif`. -/
def propLinEqReif (st : State) (coeffs : List Int) (is : List Nat)
    (b : Int) (r : Nat) : PropagationResult :=
  if coeffs.length == is.length then
    if domBoolPin st.domains r true then
      augmentRes (linLeReifEscTrue r) (propLinEq2 st coeffs is b)
    else if domBoolPin st.domains r false && domsIntOnlyB st.domains is then
      conflictsOnly (augmentRes (linLeReifEscFalse is r)
        (propLinNe st coeffs is b))
    else .stable
  else .stable

/-- The pinned-direction delegation for `int_lin_ne_reif`. -/
def propLinNeReif (st : State) (coeffs : List Int) (is : List Nat)
    (b : Int) (r : Nat) : PropagationResult :=
  if coeffs.length == is.length then
    if domBoolPin st.domains r true then
      augmentRes (linLeReifEscTrue r) (propLinNe st coeffs is b)
    else if domBoolPin st.domains r false && domsIntOnlyB st.domains is then
      conflictsOnly (augmentRes (linLeReifEscFalse is r)
        (propLinEq2 st coeffs is b))
    else .stable
  else .stable

/-! ## Run equations -/

theorem propLinEqReif_run_true {st : State} {coeffs : List Int}
    {is : List Nat} {b : Int} {r : Nat}
    (hlenB : (coeffs.length == is.length) = true)
    (h : domBoolPin st.domains r true = true) :
    propLinEqReif st coeffs is b r
      = augmentRes (linLeReifEscTrue r) (propLinEq2 st coeffs is b) := by
  show (if (coeffs.length == is.length) = true then
      (if (domBoolPin st.domains r true) = true then
        augmentRes (linLeReifEscTrue r) (propLinEq2 st coeffs is b)
      else if (domBoolPin st.domains r false
          && domsIntOnlyB st.domains is) = true then
        conflictsOnly (augmentRes (linLeReifEscFalse is r)
          (propLinNe st coeffs is b))
      else .stable)
    else .stable) = augmentRes (linLeReifEscTrue r) (propLinEq2 st coeffs is b)
  rw [if_pos hlenB, if_pos h]

theorem propLinEqReif_run_false {st : State} {coeffs : List Int}
    {is : List Nat} {b : Int} {r : Nat}
    (hlenB : (coeffs.length == is.length) = true)
    (h1 : ¬ (domBoolPin st.domains r true = true))
    (h2 : (domBoolPin st.domains r false && domsIntOnlyB st.domains is) = true) :
    propLinEqReif st coeffs is b r
      = conflictsOnly (augmentRes (linLeReifEscFalse is r)
          (propLinNe st coeffs is b)) := by
  show (if (coeffs.length == is.length) = true then
      (if (domBoolPin st.domains r true) = true then
        augmentRes (linLeReifEscTrue r) (propLinEq2 st coeffs is b)
      else if (domBoolPin st.domains r false
          && domsIntOnlyB st.domains is) = true then
        conflictsOnly (augmentRes (linLeReifEscFalse is r)
          (propLinNe st coeffs is b))
      else .stable)
    else .stable) = conflictsOnly (augmentRes (linLeReifEscFalse is r)
      (propLinNe st coeffs is b))
  rw [if_pos hlenB, if_neg h1, if_pos h2]

theorem propLinEqReif_run_stable {st : State} {coeffs : List Int}
    {is : List Nat} {b : Int} {r : Nat}
    (hlenB : (coeffs.length == is.length) = true)
    (h1 : ¬ (domBoolPin st.domains r true = true))
    (h2 : ¬ ((domBoolPin st.domains r false && domsIntOnlyB st.domains is) = true)) :
    propLinEqReif st coeffs is b r = .stable := by
  show (if (coeffs.length == is.length) = true then
      (if (domBoolPin st.domains r true) = true then
        augmentRes (linLeReifEscTrue r) (propLinEq2 st coeffs is b)
      else if (domBoolPin st.domains r false
          && domsIntOnlyB st.domains is) = true then
        conflictsOnly (augmentRes (linLeReifEscFalse is r)
          (propLinNe st coeffs is b))
      else .stable)
    else .stable) = .stable
  rw [if_pos hlenB, if_neg h1, if_neg h2]

theorem propLinEqReif_run_arity {st : State} {coeffs : List Int}
    {is : List Nat} {b : Int} {r : Nat}
    (hlenB : (coeffs.length == is.length) = false) :
    propLinEqReif st coeffs is b r = .stable := by
  simp [propLinEqReif, hlenB]

theorem propLinNeReif_run_true {st : State} {coeffs : List Int}
    {is : List Nat} {b : Int} {r : Nat}
    (hlenB : (coeffs.length == is.length) = true)
    (h : domBoolPin st.domains r true = true) :
    propLinNeReif st coeffs is b r
      = augmentRes (linLeReifEscTrue r) (propLinNe st coeffs is b) := by
  show (if (coeffs.length == is.length) = true then
      (if (domBoolPin st.domains r true) = true then
        augmentRes (linLeReifEscTrue r) (propLinNe st coeffs is b)
      else if (domBoolPin st.domains r false
          && domsIntOnlyB st.domains is) = true then
        conflictsOnly (augmentRes (linLeReifEscFalse is r)
          (propLinEq2 st coeffs is b))
      else .stable)
    else .stable) = augmentRes (linLeReifEscTrue r) (propLinNe st coeffs is b)
  rw [if_pos hlenB, if_pos h]

theorem propLinNeReif_run_false {st : State} {coeffs : List Int}
    {is : List Nat} {b : Int} {r : Nat}
    (hlenB : (coeffs.length == is.length) = true)
    (h1 : ¬ (domBoolPin st.domains r true = true))
    (h2 : (domBoolPin st.domains r false && domsIntOnlyB st.domains is) = true) :
    propLinNeReif st coeffs is b r
      = conflictsOnly (augmentRes (linLeReifEscFalse is r)
          (propLinEq2 st coeffs is b)) := by
  show (if (coeffs.length == is.length) = true then
      (if (domBoolPin st.domains r true) = true then
        augmentRes (linLeReifEscTrue r) (propLinNe st coeffs is b)
      else if (domBoolPin st.domains r false
          && domsIntOnlyB st.domains is) = true then
        conflictsOnly (augmentRes (linLeReifEscFalse is r)
          (propLinEq2 st coeffs is b))
      else .stable)
    else .stable) = conflictsOnly (augmentRes (linLeReifEscFalse is r)
      (propLinEq2 st coeffs is b))
  rw [if_pos hlenB, if_neg h1, if_pos h2]

theorem propLinNeReif_run_stable {st : State} {coeffs : List Int}
    {is : List Nat} {b : Int} {r : Nat}
    (hlenB : (coeffs.length == is.length) = true)
    (h1 : ¬ (domBoolPin st.domains r true = true))
    (h2 : ¬ ((domBoolPin st.domains r false && domsIntOnlyB st.domains is) = true)) :
    propLinNeReif st coeffs is b r = .stable := by
  show (if (coeffs.length == is.length) = true then
      (if (domBoolPin st.domains r true) = true then
        augmentRes (linLeReifEscTrue r) (propLinNe st coeffs is b)
      else if (domBoolPin st.domains r false
          && domsIntOnlyB st.domains is) = true then
        conflictsOnly (augmentRes (linLeReifEscFalse is r)
          (propLinEq2 st coeffs is b))
      else .stable)
    else .stable) = .stable
  rw [if_pos hlenB, if_neg h1, if_neg h2]

theorem propLinNeReif_run_arity {st : State} {coeffs : List Int}
    {is : List Nat} {b : Int} {r : Nat}
    (hlenB : (coeffs.length == is.length) = false) :
    propLinNeReif st coeffs is b r = .stable := by
  simp [propLinNeReif, hlenB]

/-! ## Constraint-semantics bridges -/

theorem linEqReif_satisfied_inv {coeffs : List Int} {is : List Nat}
    {b : Int} {r : Nat} {a : Assignment}
    (h : (DomConstraint.linEqReif coeffs is b r).SatisfiedBy a) :
    ∃ rb : Bool, a[r]? = some (.bool rb)
      ∧ (rb = true ↔
          dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) = some b) :=
  h

theorem linNeReif_satisfied_inv {coeffs : List Int} {is : List Nat}
    {b : Int} {r : Nat} {a : Assignment}
    (h : (DomConstraint.linNeReif coeffs is b r).SatisfiedBy a) :
    ∃ rb : Bool, a[r]? = some (.bool rb)
      ∧ (rb = true ↔
          dotNe (intVals coeffs) (is.map (fun i => a[i]!)) b = true) :=
  h

/-- The `r`-pinned-true bridge: the reified `Σ = b` holds. -/
theorem linEqReif_true_dot {coeffs : List Int} {is : List Nat} {b : Int}
    {r : Nat} {a : Assignment}
    (h : (DomConstraint.linEqReif coeffs is b r).SatisfiedBy a)
    (hpin : a[r]? = some (.bool true)) :
    (DomConstraint.linEq coeffs is b).SatisfiedBy a := by
  obtain ⟨rb, hread, hiff⟩ := linEqReif_satisfied_inv h
  rw [hpin] at hread
  have hrb : rb = true := by simpa using hread.symm
  show dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) = some b
  exact hiff.mp hrb

/-- The `r`-pinned-true bridge: the reified `Σ ≠ b` holds. -/
theorem linNeReif_true_dot {coeffs : List Int} {is : List Nat} {b : Int}
    {r : Nat} {a : Assignment}
    (h : (DomConstraint.linNeReif coeffs is b r).SatisfiedBy a)
    (hpin : a[r]? = some (.bool true)) :
    (DomConstraint.linNe coeffs is b).SatisfiedBy a := by
  obtain ⟨rb, hread, hiff⟩ := linNeReif_satisfied_inv h
  rw [hpin] at hread
  have hrb : rb = true := by simpa using hread.symm
  show dotNe (intVals coeffs) (is.map (fun i => a[i]!)) b = true
  exact hiff.mp hrb

/-- Integer operand reads of matching arity yield a dot product. -/
theorem dotProduct_exists_of_reads {coeffs : List Int} {is : List Nat}
    {a : Assignment} (hlen : coeffs.length = is.length)
    (hreads : ∀ i ∈ is, ∃ k : Int, a[i]! = .int k) :
    ∃ d, dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) = some d := by
  apply dotProduct_intVals_exists_of_length
  · rw [List.length_map, intVals_length]
    omega
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact hreads i hi

/-- The `r`-pinned-false bridge for `linEqReif`: with integer operand
    reads the dot product exists and differs from `b`, so the
    disequality holds. -/
theorem linEqReif_false_dot {coeffs : List Int} {is : List Nat} {b : Int}
    {r : Nat} {a : Assignment}
    (h : (DomConstraint.linEqReif coeffs is b r).SatisfiedBy a)
    (hpin : a[r]? = some (.bool false))
    (hreads : ∀ i ∈ is, ∃ k : Int, a[i]! = .int k)
    (hlen : coeffs.length = is.length) :
    (DomConstraint.linNe coeffs is b).SatisfiedBy a := by
  obtain ⟨rb, hread, hiff⟩ := linEqReif_satisfied_inv h
  have hrbfalse : rb = false := by
    rw [hpin] at hread
    simpa using hread.symm
  show dotNe (intVals coeffs) (is.map (fun i => a[i]!)) b = true
  obtain ⟨d, hd⟩ := dotProduct_exists_of_reads hlen hreads
  rw [dotNe, hd]
  have hne : d ≠ b := by
    intro hdb
    have h1 : rb = true := hiff.mpr (by rw [hd, hdb])
    rw [hrbfalse] at h1
    exact Bool.noConfusion h1
  exact decide_eq_true hne

/-- The `r`-pinned-false bridge for `linNeReif`: with integer operand
    reads the dot product exists and equals `b`, so the equality
    holds. -/
theorem linNeReif_false_dot {coeffs : List Int} {is : List Nat} {b : Int}
    {r : Nat} {a : Assignment}
    (h : (DomConstraint.linNeReif coeffs is b r).SatisfiedBy a)
    (hpin : a[r]? = some (.bool false))
    (hreads : ∀ i ∈ is, ∃ k : Int, a[i]! = .int k)
    (hlen : coeffs.length = is.length) :
    (DomConstraint.linEq coeffs is b).SatisfiedBy a := by
  obtain ⟨rb, hread, hiff⟩ := linNeReif_satisfied_inv h
  have hrbfalse : rb = false := by
    rw [hpin] at hread
    simpa using hread.symm
  show dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) = some b
  obtain ⟨d, hd⟩ := dotProduct_exists_of_reads hlen hreads
  have hdb : d = b := by
    by_cases hdne : d = b
    · exact hdne
    · have h1 : rb = true := hiff.mpr (by rw [dotNe, hd]; exact decide_eq_true hdne)
      rw [hrbfalse] at h1
      exact absurd h1 (by simp)
  rw [hd, hdb]



/-! ## The safe triples at fitting solutions -/

/-- The pinned-delegation propagator's safe triple w.r.t. the reified
    family: implied-literal soundness, conflict exclusion, and conflict
    entitlement, at every fitting solution of the reified constraint. -/
theorem propLinEqReif_safe (st : State) (coeffs : List Int) (is : List Nat)
    (b : Int) (r : Nat) :
    (∀ l rs, propLinEqReif st coeffs is b r = .implied l rs →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.linEqReif coeffs is b r).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ c, propLinEqReif st coeffs is b r = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.linEqReif coeffs is b r).SatisfiedBy a → False) ∧
    (∀ c, propLinEqReif st coeffs is b r = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.linEqReif coeffs is b r).SatisfiedBy a →
        ∃ l ∈ c, l.eval a = some true) := by
  by_cases hlenB : (coeffs.length == is.length) = true
  · have hlen : coeffs.length = is.length := beq_iff_eq.mp hlenB
    refine ⟨?_, ?_, ?_⟩
    · intro l rs hrun a hfit hcons
      by_cases h1 : domBoolPin st.domains r true = true
      · rw [propLinEqReif_run_true hlenB h1] at hrun
        obtain ⟨rs0, hres, -⟩ := augmentRes_implied_inv hrun
        have hle := linEqReif_true_dot hcons (fits_of_domBoolPin hfit h1)
        exact (propLinEq2_safe st coeffs is b hlen).1 l rs0 hres a hfit hle
      · by_cases h2 : (domBoolPin st.domains r false
            && domsIntOnlyB st.domains is) = true
        · rw [propLinEqReif_run_false hlenB h1 h2] at hrun
          exact (conflictsOnly_implied_elim hrun).elim
        · rw [propLinEqReif_run_stable hlenB h1 h2] at hrun
          cases hrun
    · intro c hrun a hfit hcons
      by_cases h1 : domBoolPin st.domains r true = true
      · rw [propLinEqReif_run_true hlenB h1] at hrun
        obtain ⟨c0, hres, -⟩ := augmentRes_conflict_inv hrun
        have hle := linEqReif_true_dot hcons (fits_of_domBoolPin hfit h1)
        exact (propLinEq2_safe st coeffs is b hlen).2.1 c0 hres a hfit hle
      · by_cases h2 : (domBoolPin st.domains r false
            && domsIntOnlyB st.domains is) = true
        · rw [propLinEqReif_run_false hlenB h1 h2] at hrun
          have hrun2 := conflictsOnly_conflict_inv hrun
          obtain ⟨c0, hres, -⟩ := augmentRes_conflict_inv hrun2
          have h2' := h2
          rw [Bool.and_eq_true] at h2'
          obtain ⟨hpf, hg⟩ := h2'
          have hreads := domsIntOnlyB_fits_read hg hfit
          have hcons' := linEqReif_false_dot hcons
            (fits_of_domBoolPin hfit hpf) hreads hlen
          exact (propLinNe_safe st coeffs is b).2.1 c0 hres a hfit hcons'
        · rw [propLinEqReif_run_stable hlenB h1 h2] at hrun
          cases hrun
    · intro c hrun a hfit hcons
      by_cases h1 : domBoolPin st.domains r true = true
      · rw [propLinEqReif_run_true hlenB h1] at hrun
        obtain ⟨c0, hres, hcl⟩ := augmentRes_conflict_inv hrun
        have hle := linEqReif_true_dot hcons (fits_of_domBoolPin hfit h1)
        obtain ⟨l, hl, hlt⟩ := (propLinEq2_safe st coeffs is b hlen).2.2 c0 hres
          a hfit hle
        exact ⟨l, by rw [hcl]; exact mem_insertAfterHead_of_mem hl, hlt⟩
      · by_cases h2 : (domBoolPin st.domains r false
            && domsIntOnlyB st.domains is) = true
        · rw [propLinEqReif_run_false hlenB h1 h2] at hrun
          have hrun2 := conflictsOnly_conflict_inv hrun
          obtain ⟨c0, hres, hcl⟩ := augmentRes_conflict_inv hrun2
          have h2' := h2
          rw [Bool.and_eq_true] at h2'
          obtain ⟨hpf, hg⟩ := h2'
          have hreads := domsIntOnlyB_fits_read hg hfit
          have hcons' := linEqReif_false_dot hcons
            (fits_of_domBoolPin hfit hpf) hreads hlen
          obtain ⟨l, hl, hlt⟩ := (propLinNe_safe st coeffs is b).2.2 c0 hres
            a hfit hcons'
          exact ⟨l, by rw [hcl]; exact mem_insertAfterHead_of_mem hl, hlt⟩
        · rw [propLinEqReif_run_stable hlenB h1 h2] at hrun
          cases hrun
  · have hlenF : (coeffs.length == is.length) = false :=
      Bool.eq_false_iff.mpr hlenB
    refine ⟨?_, ?_, ?_⟩
    · intro l rs hrun
      rw [propLinEqReif_run_arity hlenF] at hrun
      cases hrun
    · intro c hrun
      rw [propLinEqReif_run_arity hlenF] at hrun
      cases hrun
    · intro c hrun
      rw [propLinEqReif_run_arity hlenF] at hrun
      cases hrun

/-- The `int_lin_ne_reif` twin of `propLinEqReif_safe`. -/
theorem propLinNeReif_safe (st : State) (coeffs : List Int) (is : List Nat)
    (b : Int) (r : Nat) :
    (∀ l rs, propLinNeReif st coeffs is b r = .implied l rs →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.linNeReif coeffs is b r).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ c, propLinNeReif st coeffs is b r = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.linNeReif coeffs is b r).SatisfiedBy a → False) ∧
    (∀ c, propLinNeReif st coeffs is b r = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.linNeReif coeffs is b r).SatisfiedBy a →
        ∃ l ∈ c, l.eval a = some true) := by
  by_cases hlenB : (coeffs.length == is.length) = true
  · have hlen : coeffs.length = is.length := beq_iff_eq.mp hlenB
    refine ⟨?_, ?_, ?_⟩
    · intro l rs hrun a hfit hcons
      by_cases h1 : domBoolPin st.domains r true = true
      · rw [propLinNeReif_run_true hlenB h1] at hrun
        obtain ⟨rs0, hres, -⟩ := augmentRes_implied_inv hrun
        have hne := linNeReif_true_dot hcons (fits_of_domBoolPin hfit h1)
        exact (propLinNe_safe st coeffs is b).1 l rs0 hres a hfit hne
      · by_cases h2 : (domBoolPin st.domains r false
            && domsIntOnlyB st.domains is) = true
        · rw [propLinNeReif_run_false hlenB h1 h2] at hrun
          exact (conflictsOnly_implied_elim hrun).elim
        · rw [propLinNeReif_run_stable hlenB h1 h2] at hrun
          cases hrun
    · intro c hrun a hfit hcons
      by_cases h1 : domBoolPin st.domains r true = true
      · rw [propLinNeReif_run_true hlenB h1] at hrun
        obtain ⟨c0, hres, -⟩ := augmentRes_conflict_inv hrun
        have hne := linNeReif_true_dot hcons (fits_of_domBoolPin hfit h1)
        exact (propLinNe_safe st coeffs is b).2.1 c0 hres a hfit hne
      · by_cases h2 : (domBoolPin st.domains r false
            && domsIntOnlyB st.domains is) = true
        · rw [propLinNeReif_run_false hlenB h1 h2] at hrun
          have hrun2 := conflictsOnly_conflict_inv hrun
          obtain ⟨c0, hres, -⟩ := augmentRes_conflict_inv hrun2
          have h2' := h2
          rw [Bool.and_eq_true] at h2'
          obtain ⟨hpf, hg⟩ := h2'
          have hreads := domsIntOnlyB_fits_read hg hfit
          have hle := linNeReif_false_dot hcons
            (fits_of_domBoolPin hfit hpf) hreads hlen
          exact (propLinEq2_safe st coeffs is b hlen).2.1 c0 hres a hfit hle
        · rw [propLinNeReif_run_stable hlenB h1 h2] at hrun
          cases hrun
    · intro c hrun a hfit hcons
      by_cases h1 : domBoolPin st.domains r true = true
      · rw [propLinNeReif_run_true hlenB h1] at hrun
        obtain ⟨c0, hres, hcl⟩ := augmentRes_conflict_inv hrun
        have hne := linNeReif_true_dot hcons (fits_of_domBoolPin hfit h1)
        obtain ⟨l, hl, hlt⟩ := (propLinNe_safe st coeffs is b).2.2 c0 hres
          a hfit hne
        exact ⟨l, by rw [hcl]; exact mem_insertAfterHead_of_mem hl, hlt⟩
      · by_cases h2 : (domBoolPin st.domains r false
            && domsIntOnlyB st.domains is) = true
        · rw [propLinNeReif_run_false hlenB h1 h2] at hrun
          have hrun2 := conflictsOnly_conflict_inv hrun
          obtain ⟨c0, hres, hcl⟩ := augmentRes_conflict_inv hrun2
          have h2' := h2
          rw [Bool.and_eq_true] at h2'
          obtain ⟨hpf, hg⟩ := h2'
          have hreads := domsIntOnlyB_fits_read hg hfit
          have hle := linNeReif_false_dot hcons
            (fits_of_domBoolPin hfit hpf) hreads hlen
          obtain ⟨l, hl, hlt⟩ := (propLinEq2_safe st coeffs is b hlen).2.2 c0
            hres a hfit hle
          exact ⟨l, by rw [hcl]; exact mem_insertAfterHead_of_mem hl, hlt⟩
        · rw [propLinNeReif_run_stable hlenB h1 h2] at hrun
          cases hrun
  · have hlenF : (coeffs.length == is.length) = false :=
      Bool.eq_false_iff.mpr hlenB
    refine ⟨?_, ?_, ?_⟩
    · intro l rs hrun
      rw [propLinNeReif_run_arity hlenF] at hrun
      cases hrun
    · intro c hrun
      rw [propLinNeReif_run_arity hlenF] at hrun
      cases hrun
    · intro c hrun
      rw [propLinNeReif_run_arity hlenF] at hrun
      cases hrun


/-! ## The conflict entitlement at faithful solutions -/

/-- The delegated `propLinEq2` kernel at a solution of the underlying
    `.linEq` (keyed on the equality rather than constraint membership):
    every conflict clause carries a true literal. -/
theorem propLinEq2_entitled_dot {st : State} {coeffs : List Int}
    {is : List Nat} {b : Int} {cc : Clause} {a : Assignment}
    (hlen : coeffs.length = is.length)
    (hrun : propLinEq2 st coeffs is b = .conflict cc)
    (hcons : (DomConstraint.linEq coeffs is b).SatisfiedBy a) :
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
  · obtain ⟨_, _, _, _, _, hcc⟩ := narrowHi_conflict_inv hnarrow.symm
    have hreads := linEq2_reads_int hcons hlen
    rw [hcc]
    exact lin2_nogood_le_hi_true hmem hrest hguard hsum hreads
      (linEq_sat_le hcons) hlen
  · obtain ⟨_, _, _, _, _, hcc⟩ := narrowLo_conflict_inv hnarrow.symm
    have hreads := linEq2_reads_int hcons hlen
    rw [hcc]
    exact lin2_nogood_eq_lo_max_true hmem hrest hguard hsum hreads
      hcons hlen
  · obtain ⟨_, _, _, _, _, hcc⟩ := narrowLo_conflict_inv hnarrow.symm
    have hreads := linEq2_reads_int hcons hlen
    rw [hcc]
    exact lin2_nogood_le_lo_true hmem hrest hguard hsum hreads
      (linEq_sat_le hcons) hlen
  · obtain ⟨_, _, _, _, _, hcc⟩ := narrowHi_conflict_inv hnarrow.symm
    have hreads := linEq2_reads_int hcons hlen
    rw [hcc]
    exact lin2_nogood_eq_hi_max_true hmem hrest hguard hsum hreads
      hcons hlen
  · obtain ⟨_, _, _, _, _, hcc⟩ := narrowHi_conflict_inv hnarrow.symm
    have hreads := linEq2_reads_int hcons hlen
    rw [hcc]
    exact lin2_nogood_gen_le_hi_true hmem hpos hrest hguard hsum
      hreads (linEq_sat_le hcons) hlen
  · obtain ⟨_, _, _, _, _, hcc⟩ := narrowLo_conflict_inv hnarrow.symm
    have hreads := linEq2_reads_int hcons hlen
    rw [hcc]
    exact lin2_nogood_gen_eq_lo_max_true hmem hpos hrest hguard hsum
      hreads hcons hlen
  · obtain ⟨_, _, _, _, _, hcc⟩ := narrowLo_conflict_inv hnarrow.symm
    have hreads := linEq2_reads_int hcons hlen
    rw [hcc]
    exact lin2_nogood_gen_le_lo_true hmem hneg hrest hguard hsum
      hreads (linEq_sat_le hcons) hlen
  · obtain ⟨_, _, _, _, _, hcc⟩ := narrowHi_conflict_inv hnarrow.symm
    have hreads := linEq2_reads_int hcons hlen
    rw [hcc]
    exact lin2_nogood_gen_eq_hi_max_true hmem hneg hrest hguard hsum
      hreads hcons hlen

/-- Every conflict clause of the pinned `linEqReif` delegation carries a
    true literal at every faithful solution of the reified constraint. -/
theorem propLinEqReif_entitled {st : State} {coeffs : List Int}
    {is : List Nat} {b : Int} {r : Nat} {cc : Clause}
    {a : Assignment}
    (hrun : propLinEqReif st coeffs is b r = .conflict cc)
    (hfaith : FrameFaithful st.domains a)
    (ha : (DomConstraint.linEqReif coeffs is b r).SatisfiedBy a) :
    ∃ l ∈ cc, l.eval a = some true := by
  obtain ⟨rb, hread, hiff⟩ := linEqReif_satisfied_inv ha
  by_cases hlenB : (coeffs.length == is.length) = true
  · have hlen : coeffs.length = is.length := beq_iff_eq.mp hlenB
    by_cases h1 : domBoolPin st.domains r true = true
    · rw [propLinEqReif_run_true hlenB h1] at hrun
      obtain ⟨c0, hres, hcl⟩ := augmentRes_conflict_inv hrun
      cases rb with
      | false =>
          refine ⟨posBool r false, ?_, posBool_eval_true hread⟩
          rw [hcl]
          exact mem_insertAfterHead_of_mem_extras (by simp [linLeReifEscTrue])
      | true =>
          have hle : (DomConstraint.linEq coeffs is b).SatisfiedBy a := by
            show dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) = some b
            exact hiff.mp rfl
          obtain ⟨l, hl, hlt⟩ := propLinEq2_entitled_dot hlen hres hle
          exact ⟨l, by rw [hcl]; exact mem_insertAfterHead_of_mem hl, hlt⟩
    · by_cases h2 : (domBoolPin st.domains r false
          && domsIntOnlyB st.domains is) = true
      · rw [propLinEqReif_run_false hlenB h1 h2] at hrun
        have hrun2 := conflictsOnly_conflict_inv hrun
        obtain ⟨c0, hres, hcl⟩ := augmentRes_conflict_inv hrun2
        have h2' := h2
        rw [Bool.and_eq_true] at h2'
        obtain ⟨hpf, hg⟩ := h2'
        cases rb with
        | true =>
            refine ⟨posBool r true, ?_, posBool_eval_true hread⟩
            rw [hcl]
            exact mem_insertAfterHead_of_mem_extras
              (by simp [linLeReifEscFalse])
        | false =>
            have hreads := domsIntOnlyB_faithful_read hg hfaith
            have hcons' := linEqReif_false_dot ha hread hreads hlen
            obtain ⟨l, hl, hlt⟩ := propLinNe_entitled hres hcons'
            exact ⟨l, by rw [hcl]; exact mem_insertAfterHead_of_mem hl, hlt⟩
      · rw [propLinEqReif_run_stable hlenB h1 h2] at hrun
        cases hrun
  · have hlenF : (coeffs.length == is.length) = false :=
      Bool.eq_false_iff.mpr hlenB
    rw [propLinEqReif_run_arity hlenF] at hrun
    cases hrun

/-- Every conflict clause of the pinned `linNeReif` delegation carries a
    true literal at every faithful solution of the reified constraint. -/
theorem propLinNeReif_entitled {st : State} {coeffs : List Int}
    {is : List Nat} {b : Int} {r : Nat} {cc : Clause}
    {a : Assignment}
    (hrun : propLinNeReif st coeffs is b r = .conflict cc)
    (hfaith : FrameFaithful st.domains a)
    (ha : (DomConstraint.linNeReif coeffs is b r).SatisfiedBy a) :
    ∃ l ∈ cc, l.eval a = some true := by
  obtain ⟨rb, hread, hiff⟩ := linNeReif_satisfied_inv ha
  by_cases hlenB : (coeffs.length == is.length) = true
  · have hlen : coeffs.length = is.length := beq_iff_eq.mp hlenB
    by_cases h1 : domBoolPin st.domains r true = true
    · rw [propLinNeReif_run_true hlenB h1] at hrun
      obtain ⟨c0, hres, hcl⟩ := augmentRes_conflict_inv hrun
      cases rb with
      | false =>
          refine ⟨posBool r false, ?_, posBool_eval_true hread⟩
          rw [hcl]
          exact mem_insertAfterHead_of_mem_extras (by simp [linLeReifEscTrue])
      | true =>
          have hne : (DomConstraint.linNe coeffs is b).SatisfiedBy a := by
            show dotNe (intVals coeffs) (is.map (fun i => a[i]!)) b = true
            exact hiff.mp rfl
          obtain ⟨l, hl, hlt⟩ := propLinNe_entitled hres hne
          exact ⟨l, by rw [hcl]; exact mem_insertAfterHead_of_mem hl, hlt⟩
    · by_cases h2 : (domBoolPin st.domains r false
          && domsIntOnlyB st.domains is) = true
      · rw [propLinNeReif_run_false hlenB h1 h2] at hrun
        have hrun2 := conflictsOnly_conflict_inv hrun
        obtain ⟨c0, hres, hcl⟩ := augmentRes_conflict_inv hrun2
        have h2' := h2
        rw [Bool.and_eq_true] at h2'
        obtain ⟨hpf, hg⟩ := h2'
        cases rb with
        | true =>
            refine ⟨posBool r true, ?_, posBool_eval_true hread⟩
            rw [hcl]
            exact mem_insertAfterHead_of_mem_extras
              (by simp [linLeReifEscFalse])
        | false =>
            have hreads := domsIntOnlyB_faithful_read hg hfaith
            have hle' := linNeReif_false_dot ha hread hreads hlen
            obtain ⟨l, hl, hlt⟩ := propLinEq2_entitled_dot hlen hres hle'
            exact ⟨l, by rw [hcl]; exact mem_insertAfterHead_of_mem hl, hlt⟩
      · rw [propLinNeReif_run_stable hlenB h1 h2] at hrun
        cases hrun
  · have hlenF : (coeffs.length == is.length) = false :=
      Bool.eq_false_iff.mpr hlenB
    rw [propLinNeReif_run_arity hlenF] at hrun
    cases hrun

/-! ## The implied literals: order shape and decidedness -/

/-- The implied literal of the `linEqReif` delegation is either an order
    literal on a slot whose state domain has both extrema (hence is
    nonempty and in range), or a value-removal literal whose removed
    value is a member of the slot's state domain. -/
theorem propLinEqReif_implied_order {st : State} {coeffs : List Int}
    {is : List Nat} {b : Int} {r : Nat} {l : Literal} {rs : Reason}
    (hrun : propLinEqReif st coeffs is b r = .implied l rs) :
    (∃ m k mn mx, (l = posLe m k ∨ l = negLe m k) ∧
      domMinI (st.domains.getD m Dom.empty) = some mn ∧
      domMaxI (st.domains.getD m Dom.empty) = some mx) ∨
    (∃ m v, l = posNe m v ∧ Value.int v ∈ st.domains.getD m Dom.empty) := by
  by_cases hlenB : (coeffs.length == is.length) = true
  · by_cases h1 : domBoolPin st.domains r true = true
    · rw [propLinEqReif_run_true hlenB h1] at hrun
      obtain ⟨rs0, hres, -⟩ := augmentRes_implied_inv hrun
      rcases propLinEq2_emission_inv hres with hstable |
        ⟨m, i, rest, lr, hmem, hrest, hguard, hsum, hnarrow⟩ |
        ⟨m, i, rest, hr, hmem, hrest, hguard, hsum, hnarrow⟩ |
        ⟨m, i, rest, lr, hmem, hrest, hguard, hsum, hnarrow⟩ |
        ⟨m, i, rest, hr, hmem, hrest, hguard, hsum, hnarrow⟩ |
        ⟨m, i, rest, lr, c, hmem, hpos, hrest, hguard, hsum, hnarrow⟩ |
        ⟨m, i, rest, hr, c, hmem, hpos, hrest, hguard, hsum, hnarrow⟩ |
        ⟨m, i, rest, lr, c, hmem, hneg, hrest, hguard, hsum, hnarrow⟩ |
        ⟨m, i, rest, hr, c, hmem, hneg, hrest, hguard, hsum, hnarrow⟩
      · exact absurd hstable (by intro hc; cases hc)
      · obtain ⟨hl, -⟩ := narrowHi_implied_inv hnarrow.symm
        obtain ⟨mn, mx, hmn, hmx⟩ := linReifNarrowHi_bounds_of_implied hnarrow.symm
        exact Or.inl ⟨m, b - lr, mn, mx, Or.inl hl, hmn, hmx⟩
      · obtain ⟨hl, -⟩ := narrowLo_implied_inv hnarrow.symm
        obtain ⟨mn, mx, hmn, hmx⟩ := linReifNarrowLo_bounds_of_implied hnarrow.symm
        exact Or.inl ⟨m, b - hr - 1, mn, mx, Or.inr hl, hmn, hmx⟩
      · obtain ⟨hl, -⟩ := narrowLo_implied_inv hnarrow.symm
        obtain ⟨mn, mx, hmn, hmx⟩ := linReifNarrowLo_bounds_of_implied hnarrow.symm
        exact Or.inl ⟨m, lr - b - 1, mn, mx, Or.inr hl, hmn, hmx⟩
      · obtain ⟨hl, -⟩ := narrowHi_implied_inv hnarrow.symm
        obtain ⟨mn, mx, hmn, hmx⟩ := linReifNarrowHi_bounds_of_implied hnarrow.symm
        exact Or.inl ⟨m, hr - b, mn, mx, Or.inl hl, hmn, hmx⟩
      · obtain ⟨hl, -⟩ := narrowHi_implied_inv hnarrow.symm
        obtain ⟨mn, mx, hmn, hmx⟩ := linReifNarrowHi_bounds_of_implied hnarrow.symm
        exact Or.inl ⟨m, (b - lr) / c, mn, mx, Or.inl hl, hmn, hmx⟩
      · obtain ⟨hl, -⟩ := narrowLo_implied_inv hnarrow.symm
        obtain ⟨mn, mx, hmn, hmx⟩ := linReifNarrowLo_bounds_of_implied hnarrow.symm
        exact Or.inl ⟨m, -((hr - b) / c) - 1, mn, mx, Or.inr hl, hmn, hmx⟩
      · obtain ⟨hl, -⟩ := narrowLo_implied_inv hnarrow.symm
        obtain ⟨mn, mx, hmn, hmx⟩ := linReifNarrowLo_bounds_of_implied hnarrow.symm
        exact Or.inl ⟨m, -((b - lr) / (-c)) - 1, mn, mx, Or.inr hl, hmn, hmx⟩
      · obtain ⟨hl, -⟩ := narrowHi_implied_inv hnarrow.symm
        obtain ⟨mn, mx, hmn, hmx⟩ := linReifNarrowHi_bounds_of_implied hnarrow.symm
        exact Or.inl ⟨m, (hr - b) / (-c), mn, mx, Or.inl hl, hmn, hmx⟩
    · by_cases h2 : (domBoolPin st.domains r false
          && domsIntOnlyB st.domains is) = true
      · rw [propLinEqReif_run_false hlenB h1 h2] at hrun
        exact (conflictsOnly_implied_elim hrun).elim
      · rw [propLinEqReif_run_stable hlenB h1 h2] at hrun
        cases hrun
  · rw [propLinEqReif_run_arity (Bool.eq_false_iff.mpr hlenB)] at hrun
    cases hrun

/-- The `linNeReif` twin of `propLinEqReif_implied_order`: the delegated
    `propLinNe` implied is a value-removal literal whose removed value
    is a member of the slot's state domain. -/
theorem propLinNeReif_implied_order {st : State} {coeffs : List Int}
    {is : List Nat} {b : Int} {r : Nat} {l : Literal} {rs : Reason}
    (hrun : propLinNeReif st coeffs is b r = .implied l rs) :
    (∃ m k mn mx, (l = posLe m k ∨ l = negLe m k) ∧
      domMinI (st.domains.getD m Dom.empty) = some mn ∧
      domMaxI (st.domains.getD m Dom.empty) = some mx) ∨
    (∃ m v, l = posNe m v ∧ Value.int v ∈ st.domains.getD m Dom.empty) := by
  by_cases hlenB : (coeffs.length == is.length) = true
  · by_cases h1 : domBoolPin st.domains r true = true
    · rw [propLinNeReif_run_true hlenB h1] at hrun
      obtain ⟨rs0, hres, -⟩ := augmentRes_implied_inv hrun
      obtain ⟨-, c, m, -, -, -, hmem, hl, -⟩ := propLinNe_implied_inv hres
      exact Or.inr ⟨m, (b - linNeSum st.domains (coeffs.zip is)) / c, hl, hmem⟩
    · by_cases h2 : (domBoolPin st.domains r false
          && domsIntOnlyB st.domains is) = true
      · rw [propLinNeReif_run_false hlenB h1 h2] at hrun
        exact (conflictsOnly_implied_elim hrun).elim
      · rw [propLinNeReif_run_stable hlenB h1 h2] at hrun
        cases hrun
  · rw [propLinNeReif_run_arity (Bool.eq_false_iff.mpr hlenB)] at hrun
    cases hrun



/-- A nonempty state slot is in range at the problem box (of equal
    length), and the value the solution reads there has an integer view:
    the slot's integer read exists. -/
theorem slotInt_exists_of_state_ne_nil {problem : Problem DomConstraint Unit}
    {st : State} {a : Assignment} {m : Nat}
    (hview : IntViewedDoms problem.domains)
    (hsub : DomSub st.domains problem.domains)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a)
    (hne : st.domains.getD m Dom.empty ≠ Dom.empty) :
    ∃ x, slotInt a m = some x := by
  have hlt1 : m < st.domains.length := by
    by_cases hlt : m < st.domains.length
    · exact hlt
    · exact absurd (getD_nil_of_length_le hlt) hne
  have hlt2 : m < problem.domains.length := by rw [← hsub.1]; exact hlt1
  have hlt3 : m < a.length := by rw [ha.1.1]; exact hlt2
  have hread : a[m]? = some a[m] := List.getElem?_eq_getElem hlt3
  have hmem : a[m] ∈ problem.domains.getD m Dom.empty := ha.1.2 m (a[m]) hread
  have hx : Value.intView (a[m]) ≠ none :=
    hview _ (getD_mem_of_lt hlt2) _ hmem
  obtain ⟨x, hx2⟩ : ∃ x, Value.intView (a[m]) = some x := by
    cases hv : Value.intView (a[m]) with
    | none => exact absurd hv hx
    | some x => exact ⟨x, rfl⟩
  refine ⟨x, ?_⟩
  show a[m]?.bind Value.intView = some x
  rw [hread]
  show (some a[m]).bind Value.intView = some x
  rw [Option.bind_some]
  exact hx2

/-- The delegated implied literal is DECIDED at every solution of a
    problem whose box has the state's slots in range and int-viewed: the
    emission's own guard provides a nonempty state domain for the
    literal's slot. -/
theorem propLinEqReif_implied_decided {problem : Problem DomConstraint Unit}
    {st : State} {coeffs : List Int} {is : List Nat} {b : Int} {r : Nat}
    {l : Literal} {rs : Reason} {a : Assignment}
    (hview : IntViewedDoms problem.domains)
    (hsub : DomSub st.domains problem.domains)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a)
    (hrun : propLinEqReif st coeffs is b r = .implied l rs) :
    ∃ t, l.eval a = some t := by
  rcases propLinEqReif_implied_order hrun with
    ⟨m, k, mn, mx, hord, hmn, hmx⟩ | ⟨m, v, hpos, hmem⟩
  · obtain ⟨x, hslot⟩ := slotInt_exists_of_state_ne_nil hview hsub ha
      (linReif_getD_ne_nil_of_domMinI hmn)
    rcases hord with rfl | rfl
    · exact ⟨decide (x ≤ k), by
        simp [posLe, Literal.eval, Atom.eval, hslot]⟩
    · exact ⟨!(decide (x ≤ k)), by
        simp [negLe, Literal.eval, Atom.eval, hslot]⟩
  · obtain ⟨x, hslot⟩ := slotInt_exists_of_state_ne_nil hview hsub ha
      (by intro h0; rw [h0] at hmem; exact absurd hmem (by simp))
    rw [hpos, eval_posNe, hslot]
    exact ⟨decide (x ≠ v), rfl⟩

/-- The `linNeReif` twin of `propLinEqReif_implied_decided`. -/
theorem propLinNeReif_implied_decided {problem : Problem DomConstraint Unit}
    {st : State} {coeffs : List Int} {is : List Nat} {b : Int} {r : Nat}
    {l : Literal} {rs : Reason} {a : Assignment}
    (hview : IntViewedDoms problem.domains)
    (hsub : DomSub st.domains problem.domains)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a)
    (hrun : propLinNeReif st coeffs is b r = .implied l rs) :
    ∃ t, l.eval a = some t := by
  rcases propLinNeReif_implied_order hrun with
    ⟨m, k, mn, mx, hord, hmn, hmx⟩ | ⟨m, v, hpos, hmem⟩
  · obtain ⟨x, hslot⟩ := slotInt_exists_of_state_ne_nil hview hsub ha
      (linReif_getD_ne_nil_of_domMinI hmn)
    rcases hord with rfl | rfl
    · exact ⟨decide (x ≤ k), by
        simp [posLe, Literal.eval, Atom.eval, hslot]⟩
    · exact ⟨!(decide (x ≤ k)), by
        simp [negLe, Literal.eval, Atom.eval, hslot]⟩
  · obtain ⟨x, hslot⟩ := slotInt_exists_of_state_ne_nil hview hsub ha
      (by intro h0; rw [h0] at hmem; exact absurd hmem (by simp))
    rw [hpos, eval_posNe, hslot]
    exact ⟨decide (x ≠ v), rfl⟩

/-! ## L1a consumers' helpers (order shape + decidedness) -/

namespace LeanFzn.Solver.Propagation

theorem narrowHi_bounds_of_implied {st : State} {s : Nat} {hi : Int}
    {ng : Clause} {l : Literal} {rs : Reason}
    (h : narrowHi st s hi ng = .implied l rs) :
    ∃ mn mx, domMinI (st.domains.getD s Dom.empty) = some mn ∧
      domMaxI (st.domains.getD s Dom.empty) = some mx := by
  unfold narrowHi at h
  split at h
  · rename_i mn mx hmn hmx
    exact ⟨mn, mx, hmn, hmx⟩
  · cases h

theorem narrowLo_bounds_of_implied {st : State} {s : Nat} {lo : Int}
    {ng : Clause} {l : Literal} {rs : Reason}
    (h : narrowLo st s lo ng = .implied l rs) :
    ∃ mn mx, domMinI (st.domains.getD s Dom.empty) = some mn ∧
      domMaxI (st.domains.getD s Dom.empty) = some mx := by
  unfold narrowLo at h
  split at h
  · rename_i mn mx hmn hmx
    exact ⟨mn, mx, hmn, hmx⟩
  · cases h

theorem domMinI_ne_none_of_some {d : List Value} {mn : Int}
    (h : domMinI d = some mn) : domMinI d ≠ none := by
  intro hc
  rw [h] at hc
  exact absurd hc (by simp)

theorem getD_ne_nil_of_domMinI {d' : List Domain} {s : Nat}
    {mn : Int} (h : domMinI (d'.getD s Dom.empty) = some mn) :
    d'.getD s Dom.empty ≠ Dom.empty := by
  intro h0
  rw [h0] at h
  have h0' : domMinI (Dom.empty : Domain) = none := by
    unfold domMinI domInts
    rw [domElems_eq_enum, Dom.enum_empty]
    rfl
  rw [h0'] at h
  exact absurd h (by simp)

/-- The order-literal shape of a delegated `propLinLe2` implied pivot. -/
theorem propLinLe2_implied_order {st : State} {coeffs : List Int}
    {is : List Nat} {b : Int} {l : Literal} {rs : Reason}
    (hrun : propLinLe2 st coeffs is b = .implied l rs) :
    ∃ m k mn mx, (l = posLe m k ∨ l = negLe m k) ∧
      domMinI (st.domains.getD m Dom.empty) = some mn ∧
      domMaxI (st.domains.getD m Dom.empty) = some mx := by
  rcases propLinLe2_emission_inv hrun with hstable |
    ⟨m, i, rest, lr, hmem, hrest, hguard, hsum, hnarrow⟩ |
    ⟨m, i, rest, lr, hmem, hrest, hguard, hsum, hnarrow⟩ |
    ⟨m, i, rest, lr, c, hmem, hpos, hrest, hguard, hsum, hnarrow⟩ |
    ⟨m, i, rest, lr, c, hmem, hneg, hrest, hguard, hsum, hnarrow⟩
  · exact absurd hstable (by intro hc; cases hc)
  · obtain ⟨hl, -⟩ := narrowHi_implied_inv hnarrow.symm
    obtain ⟨mn, mx, hmn, hmx⟩ := narrowHi_bounds_of_implied hnarrow.symm
    exact ⟨m, b - lr, mn, mx, Or.inl hl, hmn, hmx⟩
  · obtain ⟨hl, -⟩ := narrowLo_implied_inv hnarrow.symm
    obtain ⟨mn, mx, hmn, hmx⟩ := narrowLo_bounds_of_implied hnarrow.symm
    exact ⟨m, lr - b - 1, mn, mx, Or.inr hl, hmn, hmx⟩
  · obtain ⟨hl, -⟩ := narrowHi_implied_inv hnarrow.symm
    obtain ⟨mn, mx, hmn, hmx⟩ := narrowHi_bounds_of_implied hnarrow.symm
    exact ⟨m, (b - lr) / c, mn, mx, Or.inl hl, hmn, hmx⟩
  · obtain ⟨hl, -⟩ := narrowLo_implied_inv hnarrow.symm
    obtain ⟨mn, mx, hmn, hmx⟩ := narrowLo_bounds_of_implied hnarrow.symm
    exact ⟨m, -((b - lr) / (-c)) - 1, mn, mx, Or.inr hl, hmn, hmx⟩

/-- The implied literal of the delegation is either an order literal on a
    slot whose state domain has both extrema (hence is nonempty and in
    range) — a delegated emission, either in a pinned direction or in the
    retained `r = false` direction (PLAN G1d) — or one of the bounds arm's
    plain pins `posBool r b` (with the Boolean-only state domain guard that
    justified it). -/
theorem propLinLeReif_implied_order {st : State} {coeffs : List Int}
    {is : List Nat} {b : Int} {r : Nat} {l : Literal} {rs : Reason}
    (hrun : propLinLeReif st coeffs is b r = .implied l rs) :
    (∃ m k mn mx, (l = posLe m k ∨ l = negLe m k) ∧
      domMinI (st.domains.getD m Dom.empty) = some mn ∧
      domMaxI (st.domains.getD m Dom.empty) = some mx) ∨
    ((l = posBool r true ∨ l = posBool r false) ∧
      domBoolOnlyB (Dom.enum (st.domains.getD r Dom.empty)) = true) := by
  by_cases hlenB : (coeffs.length == is.length) = true
  · have hlen : coeffs.length = is.length := beq_iff_eq.mp hlenB
    by_cases h1 : domBoolPin st.domains r true = true
    · rw [propLinLeReif_run_true hlenB h1] at hrun
      obtain ⟨rs0, hres, -⟩ := augmentRes_implied_inv hrun
      exact Or.inl (propLinLe2_implied_order hres)
    · by_cases h2 : (domBoolPin st.domains r false
          && domsIntOnlyB st.domains is) = true
      · -- PLAN G1d: the retained delegated implied emission
        rw [propLinLeReif_run_false hlenB h1 h2] at hrun
        obtain ⟨rs0, hres, -⟩ := augmentRes_implied_inv hrun
        exact Or.inl (propLinLe2_implied_order hres)
      · rw [propLinLeReif_run_b hlenB h1 h2] at hrun
        rcases propLinLeReifB_emission_inv hrun with hstable |
          ⟨-, hb, -, -, -, -, -, -, hres⟩ |
          ⟨-, hb, -, -, -, -, -, -, hres⟩
        · exact absurd hstable (by intro hc; cases hc)
        · refine Or.inr ⟨Or.inl ?_, hb⟩
          injection hres
        · refine Or.inr ⟨Or.inr ?_, hb⟩
          injection hres
  · rw [propLinLeReif_run_arity (Bool.eq_false_iff.mpr hlenB)] at hrun
    cases hrun

/-- The implied literal of the delegation is DECIDED at every solution
    of a problem containing the reified constraint, provided the state box
    is a sub-box of the problem box (the engine's `DomSub` invariant): an
    order literal is read through the state slot's extrema, and the bounds
    arm's pin reads the reif slot, which the constraint's satisfaction
    types as a Boolean. -/
theorem propLinLeReif_implied_decided {problem : Problem DomConstraint Unit}
    {st : State} {coeffs : List Int} {is : List Nat} {b : Int} {r : Nat}
    {l : Literal} {rs : Reason} {a : Assignment}
    (hview : IntViewedDoms problem.domains)
    (hsub : DomSub st.domains problem.domains)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a)
    (hcons : (DomConstraint.linLeReif coeffs is b r).SatisfiedBy a)
    (hrun : propLinLeReif st coeffs is b r = .implied l rs) :
    ∃ t, l.eval a = some t := by
  rcases propLinLeReif_implied_order hrun with
    ⟨m, k, mn, mx, hord, hmn, hmx⟩ | ⟨hbool, -⟩
  · have hgetD : st.domains.getD m Dom.empty ≠ Dom.empty := getD_ne_nil_of_domMinI hmn
    have hlt1 : m < st.domains.length := by
      by_cases hlt : m < st.domains.length
      · exact hlt
      · exact absurd (getD_nil_of_length_le hlt) hgetD
    have hlt2 : m < problem.domains.length := by rw [← hsub.1]; exact hlt1
    have hlt3 : m < a.length := by rw [ha.1.1]; exact hlt2
    have hread : a[m]? = some a[m] := List.getElem?_eq_getElem hlt3
    have hmem : a[m] ∈ problem.domains.getD m Dom.empty := ha.1.2 m (a[m]) hread
    have hx : Value.intView (a[m]) ≠ none :=
      hview _ (getD_mem_of_lt hlt2) _ hmem
    obtain ⟨x, hx2⟩ : ∃ x, Value.intView (a[m]) = some x := by
      cases hv : Value.intView (a[m]) with
      | none => exact absurd hv hx
      | some x => exact ⟨x, rfl⟩
    have hslot : slotInt a m = some x := by
      show a[m]?.bind Value.intView = some x
      rw [hread]
      show (some a[m]).bind Value.intView = some x
      rw [Option.bind_some]
      exact hx2
    rcases hord with rfl | rfl
    · exact ⟨decide (x ≤ k), by simp [posLe, Literal.eval, Atom.eval, hslot]⟩
    · exact ⟨!(decide (x ≤ k)), by simp [negLe, Literal.eval, Atom.eval, hslot]⟩
  · rcases hbool with hbool | hbool <;> subst hbool <;>
      obtain ⟨rb, hread, -⟩ := linLeReif_satisfied_inv hcons <;>
      exact posBool_eval_bool hread


end LeanFzn.Solver.Propagation

end LeanFzn.Solver.Propagation

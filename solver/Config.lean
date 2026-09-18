import solver.Solve
import solver.Heuristic
import solver.Fixpoint
import solver.Extract
import solver.Learning
import solver.Restarts

/-!
# The composed front door (PLAN.md item 6, final integration)

The solver stack behind this module is built in layers, each with its
own master theorems:

* the reference solver `solveModel` (`solver/Solve.lean`), whose leaf
  is the verified checker itself;
* the propagating solver `solveModelProp` (`solver/Fixpoint.lean`
  through `solver/Solve.lean`);
* the MRV solver `solveModelHeur` (`solver/Heuristic.lean` through
  `solver/Solve.lean`);
* the learning solver `learnSearch` (`solver/Learning.lean`);
* the resource-bounded solver `solveModelBounded`
  (`solver/Restarts.lean`).

This module is the *composed front door*: `SolveConfig` names the
stack features, and `solveModelWith cfg m` runs the composed
combination.  Every supported combination routes through one of the
already-proven entry points (or a small composition of them proved
here), so each carries the SAT soundness of its component — and the
budget path carries the `unknown`-not-`unsat` safety theorem of
PLAN 6.6.

## The configuration space

| `useProp` | `useMrv` | `budget`   | `nogoods` | runs                                     |
|-----------|----------|------------|-----------|------------------------------------------|
| false     | false    | none       | false     | `solveModel` (reference)                 |
| true      | false    | none       | false     | `solveModelProp` (propagation)          |
| false     | true     | none       | false     | `solveModelHeur` (MRV)                   |
| true      | true     | none       | false     | `solveModelPropMrv` (propagation + MRV) |
| false     | false    | none       | true      | `solveModelLearn` (NoGood learning)     |
| false     | false    | `some b`   | false     | `solveModelBounded` (restarts, default  |
|           |          |            |           | schedule `[b/8, b/4, b/2, b]`)           |

Every other combination — propagation, MRV, or learning *combined
with* a budget, or NoGood learning combined with propagation or MRV —
is *documented-unsupported*: `solveModelWith` returns
`.unsupported` with a reason naming the configuration.  This is the
honest scope restriction: composing two search-stack features into
one verified engine requires either a new combined master theorem or
a leaf-composition argument per pair; the pairwise compositions with
budgets/learning would need the restart loop and the learning loop to
share a search spine, which is future work (see PLAN 6.6's restart
+ learning retention discussion).  What IS composed here is the
strongest pruning pair, propagation + MRV, by the leaf-composition
architecture: the MRV permutation (`solver/Heuristic.lean`) reorders
the slots *and* the extracted constraints are re-indexed along the
permutation (`permConstraint`), so the pruning search of
`solver/Fixpoint.lean` runs unchanged on the reordered problem while
the leaf checks the assignment in original slot order
(`mrvLeaf`).

## The result type

`ConfigResult` refines `SolveResult` with PLAN 6.1's third verdict:
`unknown` (no claim — the budget ran out or the model was statically
refused) is no longer folded into `unsupported`.  The two adapters
`liftSR`/`liftBR` map the existing entry points' results into it,
with inversion lemmas proving that a lifted `.sat`/`.unsat` came from
a real `.sat`/`.unsat` of the underlying entry point.

## The theorems

* `solveModelWith_sat_sound` — **SAT soundness for the full config
  space** (unconditional): a text returned by any supported
  configuration is accepted by the verified front door.  Each path
  routes through the corresponding component theorem:
  `solveModel_sat_sound`, `solveModelProp_sat_sound`,
  `solveModelHeur_sat_sound`, `solveModelPropMrv_sat_sound`,
  `solveModelLearn_sat_sound`, or `solveModelBounded_sat_sound`.

* `solveModelWith_unsat_sound` — UNSAT soundness: an `unsat`
  verdict from a supported configuration excludes every complete
  assignment of the slot domains (the propagation paths carry the
  documented pruning licence of `solveModelProp_unsat_sound`, whose
  store-level content is `extractConstraints_holds`; the budget path
  carries `solveModelBounded_unsat_sound`'s complete-exhaustion
  guarantee).

* `solveModelWith_budget_never_falseUnsat` — **the safety theorem
  of PLAN 6.6, config-level**: for a *budgeted* configuration, a
  model with an accepted slot assignment is never reported `unsat` —
  the worst a bounded run can do is `unknown`.
-/

namespace LeanFzn.Solver

open LeanFzn LeanFzn.Solution LeanFzn.Check LeanFzn.Globals

/-! ## The configuration and the composed result type -/

/-- **The solver configuration.**  Selects the features of the
    composed front door:

    * `useProp` — fixpoint propagation with branch pruning over the
      constraints extracted from the model (`solver/Propagators.lean`,
      `solver/Fixpoint.lean`, `solver/Extract.lean`);
    * `useMrv` — minimum-remaining-values branch ordering
      (`solver/Heuristic.lean`);
    * `budget` — `none` for an unbounded run; `some b` for restarts
      over the default schedule `[b/8, b/4, b/2, b]`
      (`solver/Restarts.lean`);
    * `nogoods` — decision-trail NoGood learning
      (`solver/Learning.lean`).

    The supported combinations are: each switch alone, and
    `useProp` + `useMrv` together.  Every other combination is
    returned as `.unsupported` with a reason (see the module
    docstring's table). -/
structure SolveConfig where
  /-- Propagation on/off. -/
  useProp : Bool
  /-- MRV branch ordering on/off. -/
  useMrv : Bool
  /-- `none` = unbounded; `some b` = restarts with the default
      schedule `[b/8, b/4, b/2, b]`. -/
  budget : Option Nat
  /-- NoGood learning on/off. -/
  nogoods : Bool
  deriving Repr, Inhabited

/-- The result of the composed front door: PLAN 6.1's three-way
    discipline made explicit — `unknown` (no claim: interrupted or
    statically refused) is distinct from `unsupported` (the
    configuration or model is outside the supported fragment). -/
inductive ConfigResult where
  /-- A solution was found; the carried text is accepted by the
      verified checker (`solveModelWith_sat_sound`). -/
  | sat (text : String)
  /-- Exhaustive (or certified) search found no accepted
      assignment. -/
  | unsat
  /-- No verdict: the budget ran out or the model was statically
      refused; **no claim is made** (PLAN 6.6's safety split). -/
  | unknown (reason : String)
  /-- The configuration is unsupported, or the model is outside the
      searched fragment. -/
  | unsupported (reason : String)
  deriving Repr, Inhabited, BEq

/-- The adapter from the unbounded solvers' `SolveResult`: `unknown`
    never arises there, so it is the identity on the three
    constructors. -/
def liftSR : SolveResult → ConfigResult
  | .sat t => .sat t
  | .unsat => .unsat
  | .unsupported r => .unsupported r

/-- The adapter from the bounded solver's `BoundedResult`: `unknown`
    (no verdict) becomes the config-level `unknown`. -/
def liftBR : BoundedResult String → ConfigResult
  | .sat t => .sat t
  | .unsat => .unsat
  | .unknown =>
      .unknown
        "no verdict: the budget schedule was exhausted or the model was statically refused"

/-- A lifted `.sat` comes from a real `.sat`. -/
theorem liftSR_sat {r : SolveResult} {t : String}
    (h : liftSR r = ConfigResult.sat t) : r = SolveResult.sat t := by
  cases r with
  | sat t' =>
      simp only [liftSR] at h
      have ht : t' = t := ConfigResult.sat.inj h
      subst ht
      rfl
  | unsat => simp only [liftSR] at h; exact absurd h (by simp)
  | unsupported r' => simp only [liftSR] at h; exact absurd h (by simp)

/-- A lifted `.unsat` comes from a real `.unsat`. -/
theorem liftSR_unsat {r : SolveResult}
    (h : liftSR r = ConfigResult.unsat) : r = SolveResult.unsat := by
  cases r with
  | sat t' => simp only [liftSR] at h; exact absurd h (by simp)
  | unsat => simp only [liftSR] at h; rfl
  | unsupported r' => simp only [liftSR] at h; exact absurd h (by simp)

/-- A bounded-lifted `.sat` comes from a real `.sat`. -/
theorem liftBR_sat {r : BoundedResult String} {t : String}
    (h : liftBR r = ConfigResult.sat t) : r = BoundedResult.sat t := by
  cases r with
  | sat t' =>
      simp only [liftBR] at h
      have ht : t' = t := ConfigResult.sat.inj h
      subst ht
      rfl
  | unsat => simp only [liftBR] at h; exact absurd h (by simp)
  | unknown => simp only [liftBR] at h; exact absurd h (by simp)

/-- A bounded-lifted `.unsat` comes from a real `.unsat`. -/
theorem liftBR_unsat {r : BoundedResult String}
    (h : liftBR r = ConfigResult.unsat) : r = BoundedResult.unsat := by
  cases r with
  | sat t' => simp only [liftBR] at h; exact absurd h (by simp)
  | unsat => simp only [liftBR] at h; rfl
  | unknown => simp only [liftBR] at h; exact absurd h (by simp)

/-! ## Defaults -/

/-- The default propagation fuel (branching levels before the
    fallback to exhaustive search; sound for every value, only the
    pruning strength changes). -/
def propFuelDefault : Nat := 50

/-- The default learning fuel (number of learning steps; fuel 0 is
    the plain reference search, `learnSearch_zero`). -/
def learnFuelDefault : Nat := 100

/-- The default budget schedule derived from a total budget `b`:
    four growing restart budgets (geometric ramp with ratio 2,
    starting at an eighth and ending at the full budget). -/
def budgetSchedule (b : Nat) : List Nat := [b / 8, b / 4, b / 2, b]

/-! ## The prop+mrv composition (permutation of the pruning search)

The MRV permutation composes with the pruning search by re-indexing:
`selectSlots order doms` reorders the domains, and
`permConstraint order` re-indexes every extracted `DomConstraint`
along the same order, so the pruning search of
`solver/Fixpoint.lean` runs on the reordered problem while its leaf
(`mrvLeaf`) unpermutes and consults the original
`solveLeaf`-checker.  The composition theorem
`permConstraint_satisfiedBy_iff` is the bridge: a reordered
assignment satisfies the re-indexed constraints exactly when the
unpermuted assignment satisfies the original ones. -/

/-- Re-index a slot constraint along an `order`: slot `i` of the
    original problem is slot `order.idxOf i` of the reordered one. -/
def permConstraint (order : List Nat) : DomConstraint → DomConstraint
  | .eqSlot i j => .eqSlot (order.idxOf i) (order.idxOf j)
  | .neSlot i j => .neSlot (order.idxOf i) (order.idxOf j)
  | .leSlot i j => .leSlot (order.idxOf i) (order.idxOf j)
  | .constEq i v => .constEq (order.idxOf i) v
  | .plusSlot i j k =>
      .plusSlot (order.idxOf i) (order.idxOf j) (order.idxOf k)
  | .leConstHi i c => .leConstHi (order.idxOf i) c
  | .leConstLo i c => .leConstLo (order.idxOf i) c
  | .allDiff is => .allDiff (is.map (order.idxOf ·))
  | .timesSlot i j k =>
      .timesSlot (order.idxOf i) (order.idxOf j) (order.idxOf k)
  | .minSlot i j k =>
      .minSlot (order.idxOf i) (order.idxOf j) (order.idxOf k)
  | .maxSlot i j k =>
      .maxSlot (order.idxOf i) (order.idxOf j) (order.idxOf k)
  | .absSlot i k => .absSlot (order.idxOf i) (order.idxOf k)
  | .linEq coeffs is b => .linEq coeffs (is.map (order.idxOf ·)) b
  | .linLe coeffs is b => .linLe coeffs (is.map (order.idxOf ·)) b
  | .ltSlot i j => .ltSlot (order.idxOf i) (order.idxOf j)
  | .ltConstHi i c => .ltConstHi (order.idxOf i) c
  | .ltConstLo i c => .ltConstLo (order.idxOf i) c
  | .boolNotSlot i j => .boolNotSlot (order.idxOf i) (order.idxOf j)
  | .boolAndSlot i j k =>
      .boolAndSlot (order.idxOf i) (order.idxOf j) (order.idxOf k)
  | .boolOrSlot i j k =>
      .boolOrSlot (order.idxOf i) (order.idxOf j) (order.idxOf k)

/-- Position bridge: reading the unpermuted assignment at slot `i`
    is reading the reordered assignment at the position `order` gives
    slot `i`.  For assignments of the right length and admissible
    orders both sides agree; the length hypothesis keeps the
    out-of-range case honest (both sides are `none` past the
    ends). -/
theorem unpermute_getElem?_eq_idxOf {order : List Nat} {n : Nat} {b : List Value}
    (hperm : IsPerm order n) (hb : b.length = n) (i : Nat) :
    (unpermute order b)[i]? = b[order.idxOf i]? := by
  have holen : order.length = n := isPerm_length hperm
  by_cases hi : i < order.length
  · have hmap : (unpermute order b)[i]? =
        Option.map (fun j => b.getD (order.idxOf j) default)
          ((List.range order.length)[i]?) := by
      rw [show unpermute order b =
        (List.range order.length).map (fun j => b.getD (order.idxOf j) default) from rfl,
        List.getElem?_map]
    rw [hmap, List.getElem?_range hi, Option.map_some]
    have hidx : order.idxOf i < order.length :=
      isPerm_idxOf_lt hperm (by omega)
    have hblen : b.length = order.length := by rw [hb]; exact holen.symm
    have hblt : order.idxOf i < b.length := by omega
    have hd : b.getD (order.idxOf i) default = b[order.idxOf i]'hblt := by
      show (b[order.idxOf i]?.getD default) = b[order.idxOf i]'hblt
      rw [List.getElem?_eq_some_iff.mpr ⟨hblt, rfl⟩, Option.getD_some]
    rw [hd, List.getElem?_eq_some_iff.mpr ⟨hblt, rfl⟩]
  · have hulen : (unpermute order b).length = order.length := by
      simp only [unpermute, List.length_map, List.length_range]
    have hnone : (unpermute order b)[i]? = none :=
      List.getElem?_eq_none_iff.mpr (by rw [hulen]; omega)
    rw [hnone]
    have hnotmem : i ∉ order := by
      intro hmem
      have hilt : i < n := isPerm_lt_length hperm hmem
      have : i < order.length := by omega
      omega
    have hidx : order.idxOf i = order.length := by
      have hfind : order.findIdx (fun x => x == i) = order.length :=
        List.findIdx_eq_length.mpr
          (fun x hx => by
            have hxlt : x < n := isPerm_lt_length hperm hx
            have hne : x ≠ i := fun heq => by omega
            cases hxb : (x == i) with
            | false => rfl
            | true => exact absurd (beq_iff_eq.mp hxb) hne)
      rw [show order.idxOf i = order.findIdx (fun x => x == i) from rfl, hfind]
    rw [hidx]
    have hblen2 : b.length = order.length := by rw [hb]; exact holen.symm
    have hnone2 : b[order.length]? = none :=
      List.getElem?_eq_none_iff.mpr (by omega)
    rw [hnone2]

/-- Position bridge for the default read: reading the unpermuted
    assignment at slot `i` is reading the reordered assignment at the
    position `order` gives slot `i` (the `getElem!` form of
    `unpermute_getElem?_eq_idxOf`, needed by constraints whose
    semantics read slot values as a list, such as `allDiff`). -/
theorem unpermute_getElem!_eq_idxOf {order : List Nat} {n : Nat} {b : List Value}
    (hperm : IsPerm order n) (hb : b.length = n) (i : Nat) :
    (unpermute order b)[i]! = b[order.idxOf i]! := by
  have hget : ∀ (l : List Value) (j : Nat),
      l[j]! = (l[j]?).getD (default : Value) := by
    intro l j
    by_cases hj : j < l.length
    · rw [getElem!_pos l j hj, List.getElem?_eq_getElem hj]
      rfl
    · rw [getElem!_neg l j hj, getElem?_neg l j hj]
      rfl
  rw [hget, unpermute_getElem?_eq_idxOf hperm hb, ← hget]


/-- **The composition bridge**: a reordered assignment satisfies the
    re-indexed constraint exactly when the unpermuted assignment
    satisfies the original one — so pruning with re-indexed
    constraints prunes exactly the assignments whose unpermuted
    originals violate the original constraints. -/
theorem permConstraint_satisfiedBy_iff {order : List Nat} {n : Nat} {b : List Value}
    (hperm : IsPerm order n) (hb : b.length = n) (c : DomConstraint) :
    (permConstraint order c).SatisfiedBy b ↔ c.SatisfiedBy (unpermute order b) := by
  cases c with
  | eqSlot i j =>
      simp only [permConstraint, DomConstraint.SatisfiedBy,
        unpermute_getElem?_eq_idxOf hperm hb]
  | neSlot i j =>
      simp only [permConstraint, DomConstraint.SatisfiedBy,
        unpermute_getElem?_eq_idxOf hperm hb]
  | leSlot i j =>
      simp only [permConstraint, DomConstraint.SatisfiedBy,
        unpermute_getElem?_eq_idxOf hperm hb]
  | constEq i v =>
      simp only [permConstraint, DomConstraint.SatisfiedBy,
        unpermute_getElem?_eq_idxOf hperm hb]
  | plusSlot i j k =>
      simp only [permConstraint, DomConstraint.SatisfiedBy,
        unpermute_getElem?_eq_idxOf hperm hb]
  | leConstHi i c =>
      simp only [permConstraint, DomConstraint.SatisfiedBy,
        unpermute_getElem?_eq_idxOf hperm hb]
  | leConstLo i c =>
      simp only [permConstraint, DomConstraint.SatisfiedBy,
        unpermute_getElem?_eq_idxOf hperm hb]
  | allDiff is =>
      simp only [permConstraint, DomConstraint.SatisfiedBy, List.map_map,
        Function.comp_def]
      have hfun : (fun i => (unpermute order b)[i]!) =
          (fun x => b[order.idxOf x]!) := by
        funext i
        exact unpermute_getElem!_eq_idxOf hperm hb i
      rw [hfun]
  | timesSlot i j k =>
      simp only [permConstraint, DomConstraint.SatisfiedBy,
        unpermute_getElem?_eq_idxOf hperm hb]
  | minSlot i j k =>
      simp only [permConstraint, DomConstraint.SatisfiedBy,
        unpermute_getElem?_eq_idxOf hperm hb]
  | maxSlot i j k =>
      simp only [permConstraint, DomConstraint.SatisfiedBy,
        unpermute_getElem?_eq_idxOf hperm hb]
  | absSlot i k =>
      simp only [permConstraint, DomConstraint.SatisfiedBy,
        unpermute_getElem?_eq_idxOf hperm hb]
  | linEq coeffs is b =>
      simp only [permConstraint, DomConstraint.SatisfiedBy,
        unpermute_getElem!_eq_idxOf hperm hb, List.map_map,
        Function.comp_def]
  | linLe coeffs is b =>
      simp only [permConstraint, DomConstraint.SatisfiedBy,
        unpermute_getElem!_eq_idxOf hperm hb, List.map_map,
        Function.comp_def]
  | ltSlot i j =>
      simp only [permConstraint, DomConstraint.SatisfiedBy,
        unpermute_getElem?_eq_idxOf hperm hb]
  | ltConstHi i c =>
      simp only [permConstraint, DomConstraint.SatisfiedBy,
        unpermute_getElem?_eq_idxOf hperm hb]
  | ltConstLo i c =>
      simp only [permConstraint, DomConstraint.SatisfiedBy,
        unpermute_getElem?_eq_idxOf hperm hb]
  | boolNotSlot i j =>
      simp only [permConstraint, DomConstraint.SatisfiedBy,
        unpermute_getElem?_eq_idxOf hperm hb]
  | boolAndSlot i j k =>
      simp only [permConstraint, DomConstraint.SatisfiedBy,
        unpermute_getElem?_eq_idxOf hperm hb]
  | boolOrSlot i j k =>
      simp only [permConstraint, DomConstraint.SatisfiedBy,
        unpermute_getElem?_eq_idxOf hperm hb]

/-- The leaf of the composed prop+mrv search: judge a reordered
    assignment by unpermuting it (into original slot order) and
    consulting the checker leaf (its prepared twin, over the
    `PreparedModel` the caller binds once per solve — `solveLeaf`
    pointwise by `solveLeafP_eq`; the length guard keeps the
    unpermuted lookup total on short lists; it is exactly the slot
    count on every assignment the reordered search produces). -/
def mrvLeaf (p : PreparedModel) (names : List String) (order : List Nat) (n : Nat)
    (b : List Value) : Bool :=
  b.length == n && solveLeafP p names (unpermute order b)

/-- The prop+mrv search core: the pruning search of
    `solver/Fixpoint.lean` on the MRV-reordered domains with the
    re-indexed extracted constraints and the `mrvLeaf` leaf.  The
    result is in *reordered* slot order; callers unpermute it. -/
def propMrvCore (m : Model) (names : List String) (doms : List (List Value))
    (cs : List DomConstraint) (fuel : Nat) : Option (List Value) :=
  prunedSearch (mrvLeaf (prepareModel m) names (mrvOrder doms) doms.length)
    (domPropagators (cs.map (permConstraint (mrvOrder doms)))) fuel
    (selectSlots (mrvOrder doms) doms) []

/-- **SAT soundness of the prop+mrv core**: a returned (reordered)
    assignment unpermutes to a complete assignment of the original
    domains that passes the checker leaf. -/
theorem propMrvCore_some {m : Model} {names : List String} {doms : List (List Value)}
    {cs : List DomConstraint} {fuel : Nat} {r : List Value}
    (h : propMrvCore m names doms cs fuel = some r) :
    unpermute (mrvOrder doms) r ∈ allAssigns doms ∧
      solveLeaf m names (unpermute (mrvOrder doms) r) = true := by
  have hperm : IsPerm (mrvOrder doms) doms.length := mrvOrder_isPerm doms
  unfold propMrvCore at h
  obtain ⟨a, ha, hrfl, hleaf⟩ :=
    prunedSearch_some (mrvLeaf (prepareModel m) names (mrvOrder doms) doms.length)
      (domPropagators (cs.map (permConstraint (mrvOrder doms))))
      (cs.map (permConstraint (mrvOrder doms)))
      (domPropagators_preserve (cs.map (permConstraint (mrvOrder doms))))
      fuel (selectSlots (mrvOrder doms) doms) [] r h
  rw [List.nil_append] at hrfl hleaf
  unfold mrvLeaf at hleaf
  rw [Bool.and_eq_true] at hleaf
  obtain ⟨_hlen, hleaf'⟩ := hleaf
  rw [solveLeafP_eq] at hleaf'
  subst hrfl
  exact ⟨unpermute_mem_allAssigns (mrvOrder doms) doms hperm ha, hleaf'⟩

/-- **UNSAT soundness of the prop+mrv core** (under the same pruning
    licence `prunedSearch_none` needs, transported along the
    permutation): if every leaf-passing assignment satisfies every
    original constraint of `cs`, then a `none` verdict excludes every
    complete assignment of the original domains. -/
theorem propMrvCore_none {m : Model} {names : List String} {doms : List (List Value)}
    {cs : List DomConstraint} {fuel : Nat}
    (h : propMrvCore m names doms cs fuel = none)
    (hleaf : ∀ a, solveLeaf m names a = true → AllSat cs a) :
    ∀ asg ∈ allAssigns doms, solveLeaf m names asg = false := by
  have hperm : IsPerm (mrvOrder doms) doms.length := mrvOrder_isPerm doms
  have hlicence : ∀ b, mrvLeaf (prepareModel m) names (mrvOrder doms) doms.length
        ([] ++ b) = true →
      AllSat (cs.map (permConstraint (mrvOrder doms))) b := by
    intro b hb
    rw [List.nil_append] at hb
    unfold mrvLeaf at hb
    rw [Bool.and_eq_true] at hb
    obtain ⟨hblen, hleafb⟩ := hb
    have hbl : b.length = doms.length := beq_iff_eq.mp hblen
    rw [solveLeafP_eq] at hleafb
    have hall := hleaf (unpermute (mrvOrder doms) b) hleafb
    intro c' hc'
    obtain ⟨c, hc, hc'⟩ := List.mem_map.mp hc'
    rw [← hc']
    exact (permConstraint_satisfiedBy_iff hperm hbl c).mpr (hall c hc)
  unfold propMrvCore at h
  have hnone := prunedSearch_none
    (mrvLeaf (prepareModel m) names (mrvOrder doms) doms.length)
    (domPropagators (cs.map (permConstraint (mrvOrder doms))))
    (cs.map (permConstraint (mrvOrder doms)))
    (domPropagators_preserve (cs.map (permConstraint (mrvOrder doms))))
    [] hlicence fuel (selectSlots (mrvOrder doms) doms) h
  intro asg hasg
  have hb : permMap (mrvOrder doms) asg ∈ allAssigns (selectSlots (mrvOrder doms) doms) :=
    permMap_mem_allAssigns (mrvOrder doms) doms hperm hasg
  have hf := hnone (permMap (mrvOrder doms) asg) hb
  rw [List.nil_append] at hf
  unfold mrvLeaf at hf
  have hplen : ((permMap (mrvOrder doms) asg).length == doms.length) = true := by
    rw [beq_iff_eq]
    have h1 : (permMap (mrvOrder doms) asg).length = (mrvOrder doms).length := by
      simp only [permMap, List.length_map]
    rw [h1]
    exact isPerm_length hperm
  rw [hplen, Bool.true_and, unpermute_permMap (mrvOrder doms) doms hperm hasg,
    solveLeafP_eq] at hf
  exact hf

/-! ## The glue entry points -/

/-- **The prop+mrv solver**: `solveModel`'s gates and leaf-check
    architecture with the composed propagation + MRV search
    (`propMrvCore`).  The returned assignment is unpermuted into
    original slot order before emission, so the emitted text assigns
    the slot names in declaration order, exactly like every other
    entry point. -/
def solveModelPropMrv (fuel : Nat) (m : Model) : SolveResult :=
  match firstUnsupportedFast m with
  | some n => .unsupported s!"unsupported predicate: {n}"
  | none =>
      if wellFormedFastB m then
        match slotsChecked m with
        | .error e => .unsupported e
        | .ok slots =>
            match propMrvCore m (slots.map Prod.fst) (slots.map Prod.snd)
                (match extractConstraints m with
                  | .ok cs => cs
                  | .error _ => []) fuel with
            | some r => .sat (emitAssignment (slots.map Prod.fst)
                (unpermute (mrvOrder (slots.map Prod.snd)) r))
            | none => .unsat
      else
        .unsupported "model is not well-formed"

/-- **SAT soundness of `solveModelPropMrv`** (unconditional): a
    solution text returned by the composed propagation + MRV solver
    is accepted by the verified front door. -/
theorem solveModelPropMrv_sat_sound {m : Model} {fuel : Nat} {text : String}
    (h : solveModelPropMrv fuel m = .sat text) :
    checkModelSolution m text = .accepted := by
  rw [← checkModelSolutionFast_eq]
  simp only [solveModelPropMrv] at h
  cases huns : firstUnsupportedFast m with
  | some n => rw [huns] at h; exact absurd h (by simp)
  | none =>
      rw [huns] at h
      simp only at h
      cases hwf : wellFormedFastB m with
      | false =>
          rw [if_neg (by simp [hwf])] at h
          exact absurd h (by simp)
      | true =>
          rw [if_pos (by simp [hwf])] at h
          cases hslots : slotsChecked m with
          | error e => rw [hslots] at h; exact absurd h (by simp)
          | ok slots =>
              rw [hslots] at h
              simp only at h
              cases hsearch : propMrvCore m (slots.map Prod.fst) (slots.map Prod.snd)
                  (match extractConstraints m with
                    | .ok cs => cs
                    | .error _ => []) fuel with
              | none => rw [hsearch] at h; exact absurd h (by simp)
              | some r =>
                  rw [hsearch] at h
                  have htext : text = emitAssignment (slots.map Prod.fst)
                      (unpermute (mrvOrder (slots.map Prod.snd)) r) :=
                    (SolveResult.sat.inj h).symm
                  subst htext
                  obtain ⟨_hmem, hleaf⟩ :=
                    propMrvCore_some (m := m) (names := slots.map Prod.fst)
                      (doms := slots.map Prod.snd)
                      (cs := match extractConstraints m with
                        | .ok cs => cs
                        | .error _ => [])
                      (fuel := fuel) (r := r) hsearch
                  simp only [solveLeaf, emitAssignment, beq_iff_eq] at hleaf
                  exact hleaf

/-- **UNSAT soundness of `solveModelPropMrv`**, under the same
    pruning licence as `solveModelProp_unsat_sound` (every
    leaf-passing assignment satisfies every extracted `DomConstraint`;
    the store-level content is `extractConstraints_holds`,
    `solver/Extract.lean`). -/
theorem solveModelPropMrv_unsat_sound {m : Model} {fuel : Nat}
    (h : solveModelPropMrv fuel m = .unsat)
    (hleaf : ∀ a, solveLeaf m (slotNames m) a = true →
      AllSat (extractDomConstraints m) a)
    {asg : List Value} (hmem : asg ∈ allAssigns (slotDomains m)) :
    checkModelSolution m (emitAssignment (slotNames m) asg) ≠ .accepted := by
  intro hacc
  rw [← checkModelSolutionFast_eq] at hacc
  simp only [solveModelPropMrv] at h
  cases huns : firstUnsupportedFast m with
  | some n => rw [huns] at h; exact absurd h (by simp)
  | none =>
      rw [huns] at h
      simp only at h
      cases hwf : wellFormedFastB m with
      | false =>
          rw [if_neg (by simp [hwf])] at h
          exact absurd h (by simp)
      | true =>
          rw [if_pos (by simp [hwf])] at h
          cases hslots : slotsChecked m with
          | error e => rw [hslots] at h; exact absurd h (by simp)
          | ok slots =>
              rw [hslots] at h
              simp only at h
              cases hsearch : propMrvCore m (slots.map Prod.fst) (slots.map Prod.snd)
                  (match extractConstraints m with
                    | .ok cs => cs
                    | .error _ => []) fuel with
              | some r => rw [hsearch] at h; exact absurd h (by simp)
              | none =>
                  have hslots' : modelSlots m = some slots :=
                    (modelSlots_eq.mpr hslots)
                  obtain ⟨hnames, hdoms⟩ :=
                    slotNames_domains_of_modelSlots hslots'
                  have hlicence : ∀ a, solveLeaf m (slots.map Prod.fst) a = true →
                      AllSat (match extractConstraints m with
                        | .ok cs => cs
                        | .error _ => []) a := by
                    intro a hleafa
                    have hleafa' : solveLeaf m (slotNames m) a = true := by
                      rw [hnames]; exact hleafa
                    have hsame : (match extractConstraints m with
                        | .ok cs => cs
                        | .error _ => []) = extractDomConstraints m := by
                      unfold extractDomConstraints
                      cases extractConstraints m with
                      | error _ => rfl
                      | ok cs => rfl
                    rw [hsame]
                    exact hleaf a hleafa'
                  have hnone := propMrvCore_none (m := m)
                    (names := slots.map Prod.fst) (doms := slots.map Prod.snd)
                    (cs := match extractConstraints m with
                      | .ok cs => cs
                      | .error _ => [])
                    (fuel := fuel) hsearch hlicence
                  rw [hdoms] at hmem
                  have hleaf := hnone asg hmem
                  have hleafacc : solveLeaf m (slots.map Prod.fst) asg = true := by
                    simp only [solveLeaf, beq_iff_eq]
                    rw [← hnames]
                    exact hacc
                  rw [hleafacc] at hleaf
                  exact Bool.noConfusion hleaf

/-- **The learning solver**: `solveModel`'s gates and leaf-check
    architecture with the NoGood-learning search `learnSearch` of
    `solver/Learning.lean` (fuel `learnFuelDefault`; the checker leaf
    is the prepared twin over a `PreparedModel` bound once per solve —
    `solveLeaf` pointwise by `solveLeafP_eq`). -/
def solveModelLearn (fuel : Nat) (m : Model) : SolveResult :=
  match firstUnsupportedFast m with
  | some n => .unsupported s!"unsupported predicate: {n}"
  | none =>
      if wellFormedFastB m then
        match slotsChecked m with
        | .error e => .unsupported e
        | .ok slots =>
            let p := prepareModel m
            match learnSearch fuel (solveLeafP p (slots.map Prod.fst))
                (slots.map Prod.snd) with
            | some asg => .sat (emitAssignment (slots.map Prod.fst) asg)
            | none => .unsat
      else
        .unsupported "model is not well-formed"

/-- **SAT soundness of `solveModelLearn`** (unconditional): a
    solution text returned by the learning solver is accepted by the
    verified front door — the composed leaf only tightens the plain
    checker leaf (`learnSearch_some`). -/
theorem solveModelLearn_sat_sound {m : Model} {fuel : Nat} {text : String}
    (h : solveModelLearn fuel m = .sat text) :
    checkModelSolution m text = .accepted := by
  rw [← checkModelSolutionFast_eq]
  simp only [solveModelLearn] at h
  cases huns : firstUnsupportedFast m with
  | some n => rw [huns] at h; exact absurd h (by simp)
  | none =>
      rw [huns] at h
      simp only at h
      cases hwf : wellFormedFastB m with
      | false =>
          rw [if_neg (by simp [hwf])] at h
          exact absurd h (by simp)
      | true =>
          rw [if_pos (by simp [hwf])] at h
          cases hslots : slotsChecked m with
          | error e => rw [hslots] at h; exact absurd h (by simp)
          | ok slots =>
              rw [hslots] at h
              simp only at h
              rw [solveLeafP_eq' m (slots.map Prod.fst)] at h
              cases hsearch : learnSearch fuel (solveLeaf m (slots.map Prod.fst))
                  (slots.map Prod.snd) with
              | none => rw [hsearch] at h; exact absurd h (by simp)
              | some asg =>
                  rw [hsearch] at h
                  have htext : text = emitAssignment (slots.map Prod.fst) asg :=
                    (SolveResult.sat.inj h).symm
                  subst htext
                  have hleaf := learnSearch_some fuel (solveLeaf m (slots.map Prod.fst))
                    (slots.map Prod.snd) asg hsearch
                  simp only [solveLeaf, emitAssignment, beq_iff_eq] at hleaf
                  exact hleaf

/-- **UNSAT soundness of `solveModelLearn`** (unconditional): an
    `unsat` verdict excludes every complete assignment of the slot
    domains — every learned NoGood is entailed by construction
    (`learnSearch_none`). -/
theorem solveModelLearn_unsat_sound {m : Model} {fuel : Nat}
    (h : solveModelLearn fuel m = .unsat)
    {asg : List Value} (hmem : asg ∈ allAssigns (slotDomains m)) :
    checkModelSolution m (emitAssignment (slotNames m) asg) ≠ .accepted := by
  intro hacc
  rw [← checkModelSolutionFast_eq] at hacc
  simp only [solveModelLearn] at h
  cases huns : firstUnsupportedFast m with
  | some n => rw [huns] at h; exact absurd h (by simp)
  | none =>
      rw [huns] at h
      simp only at h
      cases hwf : wellFormedFastB m with
      | false =>
          rw [if_neg (by simp [hwf])] at h
          exact absurd h (by simp)
      | true =>
          rw [if_pos (by simp [hwf])] at h
          cases hslots : slotsChecked m with
          | error e => rw [hslots] at h; exact absurd h (by simp)
          | ok slots =>
              rw [hslots] at h
              simp only at h
              rw [solveLeafP_eq' m (slots.map Prod.fst)] at h
              cases hsearch : learnSearch fuel (solveLeaf m (slots.map Prod.fst))
                  (slots.map Prod.snd) with
              | some a => rw [hsearch] at h; exact absurd h (by simp)
              | none =>
                  have hnone := learnSearch_none fuel (solveLeaf m (slots.map Prod.fst))
                    (slots.map Prod.snd) hsearch
                  have hslots' : modelSlots m = some slots :=
                    (modelSlots_eq.mpr hslots)
                  obtain ⟨hnames, hdoms⟩ :=
                    slotNames_domains_of_modelSlots hslots'
                  rw [hdoms] at hmem
                  have hleaf := hnone asg hmem
                  have hleafacc : solveLeaf m (slots.map Prod.fst) asg = true := by
                    simp only [solveLeaf, beq_iff_eq]
                    rw [← hnames]
                    exact hacc
                  rw [hleafacc] at hleaf
                  exact Bool.noConfusion hleaf

/-! ## The composed front door -/

/-- The refusal reason for an unsupported configuration: names the
    configuration and the supported combinations. -/
def unsupportedMsg (cfg : SolveConfig) : String :=
  s!"configuration not supported: useProp = {cfg.useProp}, useMrv = {cfg.useMrv}, budget = {cfg.budget}, nogoods = {cfg.nogoods} (supported: each switch alone, and propagation with MRV together)"

/-- **The composed front door.**  Runs the configured combination on
    the model, with `solveModel`'s gates and the leaf-check
    architecture in every supported path.  Unsupported combinations
    return `.unsupported` with a reason; a budgeted run may return
    `.unknown` (never a false `.unsat`,
    `solveModelWith_budget_never_falseUnsat`). -/
def solveModelWith (cfg : SolveConfig) (m : Model) : ConfigResult :=
  match cfg with
  | ⟨false, false, none, false⟩ => liftSR (solveModel m)
  | ⟨true, false, none, false⟩ => liftSR (solveModelProp propFuelDefault m)
  | ⟨false, true, none, false⟩ => liftSR (solveModelHeur m)
  | ⟨true, true, none, false⟩ => liftSR (solveModelPropMrv propFuelDefault m)
  | ⟨false, false, none, true⟩ => liftSR (solveModelLearn learnFuelDefault m)
  | ⟨false, false, some b, false⟩ => liftBR (solveModelBounded m (budgetSchedule b))
  | ⟨_, _, _, _⟩ => .unsupported (unsupportedMsg cfg)

/-- **SAT soundness of the composed front door** (the full supported
    config space, unconditional): a solution text returned by
    `solveModelWith` under any configuration is accepted by the
    verified checker — so by `checkModelSolution_correct` the model
    is well formed and the parsed entries' completed store satisfies
    `Satisfies fullSig fullInterp`.  Each path routes through its
    component's theorem. -/
theorem solveModelWith_sat_sound {cfg : SolveConfig} {m : Model} {text : String}
    (h : solveModelWith cfg m = ConfigResult.sat text) :
    checkModelSolution m text = .accepted := by
  rcases cfg with ⟨up, um, bud, ng⟩
  cases up <;> cases um <;> cases bud <;> cases ng
  all_goals simp only [solveModelWith] at h
  all_goals first
    | exact absurd h (by simp)
    | exact solveModel_sat_sound (liftSR_sat h)
    | exact solveModelProp_sat_sound (liftSR_sat h)
    | exact solveModelHeur_sat_sound (liftSR_sat h)
    | exact solveModelPropMrv_sat_sound (liftSR_sat h)
    | exact solveModelLearn_sat_sound (liftSR_sat h)
    | exact solveModelBounded_sat_sound (liftBR_sat h)

/-- **UNSAT soundness of the composed front door**: an `unsat`
    verdict from a supported configuration excludes every complete
    assignment of the slot domains.  The propagation paths carry the
    documented pruning licence (the explicit hypothesis, whose
    store-level content is `extractConstraints_holds`); the other
    paths are unconditional. -/
theorem solveModelWith_unsat_sound {cfg : SolveConfig} {m : Model}
    (h : solveModelWith cfg m = ConfigResult.unsat)
    (hleaf : ∀ a, solveLeaf m (slotNames m) a = true →
      AllSat (extractDomConstraints m) a)
    {asg : List Value} (hmem : asg ∈ allAssigns (slotDomains m)) :
    checkModelSolution m (emitAssignment (slotNames m) asg) ≠ .accepted := by
  intro hacc
  rcases cfg with ⟨up, um, bud, ng⟩
  cases up <;> cases um <;> cases bud <;> cases ng
  all_goals simp only [solveModelWith] at h
  all_goals first
    | exact absurd h (by simp)
    | exact solveModel_unsat_sound (liftSR_unsat h) hmem hacc
    | exact solveModelHeur_unsat_sound (liftSR_unsat h) hmem hacc
    | exact solveModelLearn_unsat_sound (liftSR_unsat h) hmem hacc
    | exact solveModelBounded_unsat_sound (liftBR_unsat h) hmem hacc
    | exact solveModelProp_unsat_sound (liftSR_unsat h) hleaf hmem hacc
    | exact solveModelPropMrv_unsat_sound (liftSR_unsat h) hleaf hmem hacc

/-- **The safety theorem of PLAN 6.6, config-level**: for a
    *budgeted* configuration (`cfg.budget = some b`), a model with
    an accepted slot assignment is never reported `unsat` — the
    worst a bounded run can do is `unknown`. -/
theorem solveModelWith_budget_never_falseUnsat {cfg : SolveConfig} {m : Model}
    (hbud : ∃ b, cfg.budget = some b)
    (hsat : ∃ asg ∈ allAssigns (slotDomains m),
      checkModelSolution m (emitAssignment (slotNames m) asg) = .accepted) :
    solveModelWith cfg m ≠ ConfigResult.unsat := by
  obtain ⟨b, hb⟩ := hbud
  rcases cfg with ⟨up, um, bud, ng⟩
  have hbud : bud = some b := hb
  subst hbud
  cases up <;> cases um <;> cases ng
  all_goals simp only [solveModelWith]
  all_goals
    first
    | simp
    | intro hcontra
    | exact True.intro
  case false.false.false =>
    intro hcontra
    exact solveModelBounded_never_falseUnsat hsat (liftBR_unsat hcontra)

end LeanFzn.Solver

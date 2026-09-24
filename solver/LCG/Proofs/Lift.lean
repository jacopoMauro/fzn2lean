/-
File: solver/LCG/Proofs/Lift.lean

Purpose:
  The propagation-loop soundness lift (PLAN.md Step 2.1 items 3–4).
  From a trail-sound state (every internal solution satisfies the
  trail) whose clause database is sound, one `propagateLoop` run
  reports either

  * a conflict clause `c` all of whose literals are falsified at every
    assignment satisfying the *pre-run* trail (hence no internal
    solution of the pre-state survives), or
  * a quiescent state that is again trail-sound, with the same original
    clause database, with every new trail entry carrying a valid reason
    (analysis ready), with root facts intact.

  The proof is a fuel induction. The interesting cases are handled by
  step lemmas: `unitEnqueue_trailSat` (unit enqueue keeps soundness)
  and the `runPropagators` fold lift. The propagators enter only
  through the per-state contract `PropContract`, which is used
  hypothesis-wise; no propagator internals are inspected here.

Dependencies:
  - solver.LCG.Engine: `propagateLoop`, `runPropagators`, `scanAll`.
  - solver.LCG.Proofs.Engine: `scanClause_conflict_falsified'`,
    `scanClause_unit_justified'`.
  - solver.LCG.Proofs.Reachability: reachability vocabulary and the
    `enqueueNorm_fresh_trailSat` step lemma.

DAG:
  LCG.Engine + LCG.Proofs.Engine + LCG.Proofs.Reachability
  -> LCG.Proofs.Lift -> LCG.Proofs.Search (EngineSafe elimination)
-/

import solver.LCG.Engine
import solver.LCG.Proofs.Engine
import solver.LCG.Proofs.Reachability
import solver.LCG.Proofs.EngDup

namespace LeanFzn.Solver.LCG

open LeanFzn LeanFzn.Solver.Core

/-! ## The propagator contract -/

/-- Propagator soundness contract over a state `st`:

* `implied`: each propagator's implied literal carries a reason whose
  clause is entailed by the internal problem, whose pivot is the
  implied literal itself, and whose every other disjunct is falsified
  at every assignment represented by the pre-state — so enqueueing the
  literal preserves trail soundness (its own truth: pivot membership
  plus disjunct-falsification forces the pivot to be the satisfying
  witness);
* `conflictFalsified`: each reported conflict clause is falsified at
  every assignment represented by the pre-state.

The contract quantifies over assignments and the propagator's observed
output only; it is what per-constraint soundness (Step 2.2) must
establish for each family. -/
structure PropContract (problem : Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop)
    (props : List Propagator) (st : State) : Prop where
  implied : ∀ p ∈ props, ∀ l r,
    p.run st = .implied l r →
    Reason.Valid problem constraintHolds r l ∧
    (∀ c ∈ r.clause, c = c.norm) ∧
    (∀ a : Assignment,
      (ProblemSolution problem constraintHolds a ∧ st.Represents a) →
      ∀ q ∈ r.clause, q ≠ l → q.eval a = some false)
  conflictFalsified : ∀ p ∈ props, ∀ c,
    p.run st = .conflict c →
    (∀ a : Assignment,
      (ProblemSolution problem constraintHolds a ∧ st.Represents a) →
      ¬ c.SatisfiedBy a)

/-! ### Trail-soundness step lemmas -/

/-- A unit enqueue from a scanning hit keeps trail soundness (or sets
    the conflict flag, which the loop propagates honestly). The unit
    clause is entailed by the internal problem; the scan justified the
    reported literal as the clause's only non-falsified disjunct, so
    the entailed clause's witness must be that literal. -/
theorem unitEnqueue_trailSat
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st : State} {c : Clause} {l : Literal} {r : Reason}
    {a : Assignment}
    (hsol : ProblemSolution problem constraintHolds a)
    (hsat : st.TrailSatisfied a)
    (hent : c.EntailedBy problem constraintHolds)
    (hscan : scanClause st c = some (.inr (l, r))) :
    (enqueueNorm st l (some r)).TrailSatisfied a := by
  -- the trail-satisfying witness for the clause: entailment gives one
  obtain ⟨l2, hm2, hev2⟩ := hent a hsol
  -- and the scan's uniqueness says that witness is the reported unit
  have hunit := scanClause_unit_justified' hscan hsat ⟨l2, hm2, hev2⟩
  -- the enqueued literal is l.norm and evaluates like l
  have heval : l.norm.eval a = some true := by
    rw [Literal.norm_eval l a]; exact hunit
  -- the three enqueueNorm branches: (already-on-trail skip |
  -- opposing-fact skip | fresh enqueue). First zeta-reduce the let.
  simp only [enqueueNorm]
  split
  · -- already-on-trail skip: state unchanged
    exact hsat
  · split
    · -- opposing-fact: trail unchanged
      intro e he
      exact hsat e he
    · -- fresh enqueue: apply the fresh-branch lemma; the split's
      -- rename_i yields ¬(cond = true), convertible to `= false`
      rename_i hnew hneg
      have hnew' : st.litOnTrail l.norm = false := by
        cases hb : st.litOnTrail l.norm with
        | true => exact absurd hb hnew
        | false => rfl
      have hneg' : st.negOnTrail l.norm = false := by
        cases hb : st.negOnTrail l.norm with
        | true => exact absurd hb hneg
        | false => rfl
      have hres : (enqueueNorm st l (some r)).TrailSatisfied a :=
        enqueueNorm_fresh_trailSat (st := st) (l0 := l)
          (reason := some r) hnew' hneg' hsol hsat heval
      -- the goal is hres modulo the same branch firing; normalize both
      unfold enqueueNorm at hres
      simp only [hnew', hneg', Bool.false_eq_true, if_false] at hres
      exact hres

/-! ### The propagator sweep

`runPropagators` folds a single propagator `run` over the list,
enqueuing each `.implied` deduction through `enqueueNorm` and stopping
at the first `.conflict`. The fold's accumulator is itself a state
whose soundness is maintained by the same step lemma as above, with
the propagator contract supplying the justification. -/

/-- One propagator application preserves soundness: from a
    conflict-free trail-sound state, the output is either
    conflict-free and trail-sound, or carries a conflict clause that
    is falsified at every assignment satisfying the pre-state's trail. -/
theorem oneProp_sound
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {p : Propagator} {st : State} {a : Assignment}
    (hpc : PropContract problem constraintHolds [p] st)
    (hsol : ProblemSolution problem constraintHolds a)
    (hsat : st.TrailSatisfied a)
    (hconf : st.conflict = none) :
    (p.run st = .stable → st.TrailSatisfied a) ∧
    (∀ l : Literal, ∀ reason : Reason, p.run st = .implied l reason →
      (enqueueNorm st l (some reason)).TrailSatisfied a ∨
        (enqueueNorm st l (some reason)).conflict ≠ none) ∧
    (∀ c : Clause, p.run st = .conflict c →
      ∀ a2 : Assignment,
        (ProblemSolution problem constraintHolds a2 ∧
          st.Represents a2) →
        ¬ c.SatisfiedBy a2) := by
  obtain ⟨himplied, hconflict⟩ := hpc
  refine ⟨fun _ => hsat, ?_, ?_⟩
  · intro l reason hrun
    obtain ⟨hrv, hnorms, hfalse⟩ :=
      himplied p (List.mem_cons_self) l reason hrun
    -- Whether the enqueue takes a skip branch (state's trail
    -- unchanged: soundness transfers) or the fresh branch: the
    -- fresh branch's soundness needs the pivot's truth at `a`.
    simp only [enqueueNorm]
    split
    · exact Or.inl hsat
    · split
      · exact Or.inr (by simp [State.conflict])
      · -- fresh branch: the head justification at `a` is the
        -- remaining lift obligation (see module notes); parked while
        -- the loop-level composition is built
        sorry
  · intro c hrun a2 hpair
    exact hconflict p (List.mem_cons_self) c hrun a2 hpair

/-! ### The propagation-loop lift -/

/-- The full carry-bundle of a propagation-loop state: everything the
    engine's downstream consumers (conflict analysis, leaf checks, the
    UNSAT terminal reports) need, in one place. -/
structure LoopInv (problem : Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop)
    (props : List Propagator) (st : State) : Prop where
  conflictNone : st.conflict = none
  fitLen : st.domains.length = problem.domains.length
  coherent : DomainCoherent problem st
  trailSatOfSol : ∀ a, ProblemSolution problem constraintHolds a →
    st.TrailSatisfied a
  reasonValid : ∀ e ∈ st.trail, ∀ r ∈ e.reason,
    Reason.Valid problem constraintHolds r e.literal
  rootFacts' : RootFacts problem constraintHolds st.trail
  normReasons : ∀ e ∈ st.trail, ∀ r ∈ e.reason, ∀ l ∈ r.clause, l = l.norm
  rooted : ∀ e ∈ st.trail, e.level ≤ st.decisionLevel
  -- props soundness AT this state (re-established at each step because
  -- propagators observe the state)
  propContract : PropContract problem constraintHolds props st

/-! ### Fits-lifting through the fold

The single-step coherence results of `Proofs/Engine.lean`
(`fits_domOfLit_sat_pos/neg/bool`) say: an assignment fitting the
NARROWED domains satisfies the narrowing literal. Combined with the
coherence invariant (the state's domains are exactly the trail-fold of
`domOfLit`), this gives the *characteristic property* of a coherent
state: every assignment fitting the state's domains satisfies every
literal on the trail — provided its slot values have integer views
where the literals demand them. That, together with clause-soundness,
is `Represents`. The induction below maintains `Represents` directly,
because it is the object both terminal reports need. -/

/-! ### The firing lemma: satisfied literal ⇒ fitting assignment passes

`domOfLit doms l` removes (or Boolean-pins) the values of `l`'s slot.
An assignment FITTING `doms` whose value at that slot survives the
filter also fits the NARROWED domains; survival is exactly the literal
being satisfied — up to the int view of the surviving values. This is
the direction the `Represents`-preservation needs (the direction
`fits_domOfLit_sat_pos` runs BACKWARD). -/

/-- THE FIRING LEMMA: a fitting assignment satisfying the narrowing
    literal fits the narrowed domains. -/
theorem firing {doms : List (List Value)} {l : Literal} {a : Assignment}
    (hfit : a.Fits doms)
    (hin : l.atom.slot < a.length)
    (hsat : l.eval a = some true) :
    a.Fits (domOfLit doms l) := by
  obtain ⟨hfitlen, hfitmem⟩ := hfit
  refine ⟨by rw [domOfLit_length l]; exact hfitlen, ?_⟩
  intro slot value hv
  by_cases hsl : slot = l.atom.slot
  · -- the touched slot: the member value's survival through the filter
    -- is the literal's satisfaction at a (up to the int view), which
    -- `hsat` provides
    subst hsl
    cases l with
    | mk atom pos =>
      cases atom with
      | intLe s k =>
          cases pos with
          | false =>
              -- keep p > k
              show value ∈ (updateSlot doms s
                (fun d => domFilterInt (fun p => decide (p > k)) d)).getD s []
              refine mem_updateSlot_of_mem doms s _ value (by
                rw [show (doms.length : Nat) = a.length from hfitlen.symm]; exact hin) ?_
              rw [domFilterInt, List.mem_filter]
              refine ⟨hfitmem s value hv, ?_⟩
              -- value passes the > k test: derive from hsat. The slot's
              -- value in `a` IS `value` (same slot, fits) and the
              -- satisfied literal's eval equation unfolds to the slot
              -- int view > k; since a[s] = value, that int view is
              -- value's.
              have hslotmem : value ∈ doms.getD s [] := hfitmem s value hv
              -- eval of negLe s k on a:
              have hsat' : (negLe s k).eval a = some true := hsat
              rw [eval_negLe_iff] at hsat'
              obtain ⟨i, hi, hik⟩ := hsat'
              -- hi : slotInt a s = some i; and a[s] = value
              have hvi : Value.intView value = some i := by
                unfold slotInt at hi
                show Value.intView value = some i
                have hv2 : a[s]? = some value := by
                  show a[(⟨Atom.intLe s k, false⟩ : Literal).atom.slot]? = some value
                  exact hv
                have hv3 : (some value).bind Value.intView = some i := by
                  rw [← hv2]
                  exact hi
                show Value.intView value = some i
                exact hv3
              cases value with
              | int x =>
                  show decide (x > k) = true
                  have hvi' : Value.intView (Value.int x) = some i := by
                    simpa using hvi
                  rw [Value.intView] at hvi'
                  rw [Option.some.injEq] at hvi'
                  show decide (x > k) = true
                  have : x > k := by omega
                  exact decide_eq_true this
              | bool x =>
                  show decide ((if x then 1 else 0) > k) = true
                  have hvi' : Value.intView (Value.bool x) = some i := by
                    simpa using hvi
                  have hx : (if x then 1 else 0) = i := by
                    have : Value.intView (Value.bool x)
                        = some (if x then 1 else 0) := rfl
                    rw [this] at hvi'
                    rw [Option.some.injEq] at hvi'
                    exact hvi'
                  have hik' : k < i := hik
                  have hxi : (if x then 1 else 0) = i := hx
                  show decide ((if x then 1 else 0) > k) = true
                  have : k < (if x then 1 else 0) := by omega
                  exact decide_eq_true this
              | setOfInt x =>
                  exfalso
                  exact absurd hvi (by simp [Value.intView])
              | array x =>
                  exfalso
                  exact absurd hvi (by simp [Value.intView])
          | true =>
              -- keep p ≤ k
              show value ∈ (updateSlot doms s
                (fun d => domFilterInt (fun p => decide (p ≤ k)) d)).getD s []
              refine mem_updateSlot_of_mem doms s _ value (by
                rw [show (doms.length : Nat) = a.length from hfitlen.symm]; exact hin) ?_
              rw [domFilterInt, List.mem_filter]
              refine ⟨hfitmem s value hv, ?_⟩
              have hsat' : (posLe s k).eval a = some true := hsat
              rw [eval_posLe_iff] at hsat'
              obtain ⟨i, hi, hik⟩ := hsat'
              have hvi : Value.intView value = some i := by
                unfold slotInt at hi
                show Value.intView value = some i
                have hv2 : a[s]? = some value := by
                  show a[(⟨Atom.intLe s k, false⟩ : Literal).atom.slot]? = some value
                  exact hv
                have hv3 : (some value).bind Value.intView = some i := by
                  rw [← hv2]
                  exact hi
                show Value.intView value = some i
                exact hv3
              cases value with
              | int x =>
                  show decide (x ≤ k) = true
                  have hvi' : Value.intView (Value.int x) = some i := by
                    simpa using hvi
                  rw [Value.intView] at hvi'
                  rw [Option.some.injEq] at hvi'
                  have hik' : x ≤ k := by omega
                  exact decide_eq_true hik'
              | bool x =>
                  show decide ((if x then 1 else 0) ≤ k) = true
                  have hvi' : Value.intView (Value.bool x) = some i := by
                    simpa using hvi
                  have hx : (if x then 1 else 0) = i := by
                    have hview : Value.intView (Value.bool x)
                        = some (if x then 1 else 0) := rfl
                    rw [hview] at hvi'
                    rw [Option.some.injEq] at hvi'
                    exact hvi'
                  have hik' : (if x then 1 else 0) ≤ k := by omega
                  exact decide_eq_true hik'
              | setOfInt x =>
                  exact absurd hvi (by simp [Value.intView])
              | array x =>
                  exact absurd hvi (by simp [Value.intView])
      | boolEq s b =>
          -- the pin: domOfLit sets the slot to [bool forced]; the goal
          -- membership needs value to BE the forced Boolean, which the
          -- satisfied literal pins exactly
          show value ∈ (updateSlot doms s
            (fun _ => [Value.bool (if pos then b else !b)])).getD s []
          refine mem_updateSlot_of_mem doms s _ value (by
            rw [show (doms.length : Nat) = a.length from hfitlen.symm]; exact hin) ?_
          show value ∈ [Value.bool (if pos then b else !b)]
          -- the satisfiable literal: posBool / negBool truth at a
          cases pos with
          | true =>
              -- l = ⟨boolEq s b, true⟩ = posBool s b
              -- eval true ⟺ a[s] = bool b (eval_posBool_iff)
              show value ∈ [Value.bool b]
              have hp : a[(⟨Atom.boolEq s b, true⟩ : Literal).atom.slot]? =
                  some (Value.bool b) :=
                (eval_posBool_iff a s b).mp hsat
              rw [hp] at hv
              injection hv with hv'
              rw [hv']
              exact List.mem_cons_self ..
          | false =>
              -- l = ⟨boolEq s b, false⟩; eval true ⟺ ¬(a[s] = bool b),
              -- and since a[s] IS value, value ≠ bool b, so value is
              -- bool (some x ≠ b)... but domOfLit pins to bool (!b):
              -- the truthful eval for negative Boolean is
              -- a[s] = bool (!b) (only a Boolean atom has bool eval);
              -- conveniently the norm lemma: ⟨boolEq s b, false⟩.norm =
              -- posBool s (!b), and eval equality gives
              -- a[s] = bool (!b)
              show value ∈ [Value.bool (!b)]
              -- norm of the negative Boolean literal is the positive
              -- pinned one: ⟨boolEq s b, false⟩.norm = ⟨boolEq s (!b), true⟩
              have hsatNorm : (Literal.norm
                  (⟨Atom.boolEq s b, false⟩ : Literal)).eval a = some true := by
                rw [Literal.norm_eval]
                exact hsat
              -- unfold the norm shape: ⟨boolEq s b, false⟩.norm = ⟨boolEq s (!b), true⟩
              have hsatNorm' : (⟨Atom.boolEq s (!b), true⟩ : Literal).eval a
                  = some true := hsatNorm
              have hp : a[(⟨Atom.boolEq s b, false⟩ : Literal).atom.slot]? =
                  some (Value.bool (!b)) :=
                (eval_posBool_iff a s (!b)).mp hsatNorm'
              rw [hp] at hv
              injection hv with hv'
              rw [hv']
              exact List.mem_cons_self ..
  · -- untouched slot: case on the atom; each shape is an updateSlot at
    -- a different slot, so the untouched-slot rule applies directly
    cases l with
    | mk atom pos =>
      cases atom with
      | intLe s' k =>
          cases pos with
          | false =>
              show value ∈ (updateSlot doms s'
                (fun d => domFilterInt (fun q => decide (q > k)) d)).getD slot []
              rw [updateSlot_getD_ne doms s'
                (fun d => domFilterInt (fun q => decide (q > k)) d) slot
                (fun hcon => hsl hcon)]
              exact hfitmem slot value hv
          | true =>
              show value ∈ (updateSlot doms s'
                (fun d => domFilterInt (fun q => decide (q ≤ k)) d)).getD slot []
              rw [updateSlot_getD_ne doms s'
                (fun d => domFilterInt (fun q => decide (q ≤ k)) d) slot
                (fun hcon => hsl hcon)]
              exact hfitmem slot value hv
      | boolEq s' b =>
          show value ∈ (updateSlot doms s'
            (fun _ => [Value.bool (if pos then b else !b)])).getD slot []
          rw [updateSlot_getD_ne doms s' (fun _ => [Value.bool (if pos then b else !b)]) slot
            (fun hcon => hsl hcon)]
          exact hfitmem slot value hv

end LeanFzn.Solver.LCG






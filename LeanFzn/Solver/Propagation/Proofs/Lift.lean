/-
File: LeanFzn/Solver/Propagation/Proofs/Lift.lean

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
  - LeanFzn.Solver.Reference.Engine: `propagateLoop`, `runPropagators`, `scanAll`.
  - LeanFzn.Solver.Propagation.Proofs.Engine: `scanClause_conflict_falsified'`,
    `scanClause_unit_justified'`.
  - LeanFzn.Solver.Propagation.Proofs.Reachability: reachability vocabulary and the
    `enqueueNorm_fresh_trailSat` step lemma.

DAG:
  LeanFzn.Solver.UIP.Engine + LeanFzn.Solver.UIP.Proofs.Engine + LeanFzn.Solver.UIP.Proofs.Reachability
  -> LeanFzn.Solver.UIP.Proofs.Lift -> LeanFzn.Solver.UIP.Proofs.Search (EngineSafe elimination)
-/

import LeanFzn.Solver.Reference.Engine
import LeanFzn.Solver.Propagation.Proofs.Engine
import LeanFzn.Solver.Propagation.Proofs.Reachability
import LeanFzn.Solver.Propagation.Proofs.EngDup


namespace LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Reference
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
structure PropContract (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop)
    (props : List Propagator) (st : State) : Prop where
  implied : ∀ p ∈ props, ∀ l r,
    p.run st = .implied l r →
    Reason.Valid problem constraintHolds r l ∧
    (∀ c ∈ r.clause, c = c.norm) ∧
    (∀ a : Assignment,
      ProblemSolution problem constraintHolds a →
      l.eval a = some true)
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
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
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
      | intNe s k =>
          cases pos with
          | true =>
              -- keep p ≠ k: the surviving values' views differ from k
              show value ∈ (updateSlot doms s
                (fun d => domFilterInt (fun p => decide (p ≠ k)) d)).getD s []
              refine mem_updateSlot_of_mem doms s _ value (by
                rw [show (doms.length : Nat) = a.length from hfitlen.symm]; exact hin) ?_
              rw [domFilterInt, List.mem_filter]
              refine ⟨hfitmem s value hv, ?_⟩
              have hsat' : (posNe s k).eval a = some true := hsat
              rw [eval_posNe_iff] at hsat'
              obtain ⟨i, hi, hik⟩ := hsat'
              have hvi : Value.intView value = some i := by
                unfold slotInt at hi
                show Value.intView value = some i
                have hv2 : a[s]? = some value := by
                  show a[(⟨Atom.intNe s k, true⟩ : Literal).atom.slot]? = some value
                  exact hv
                have hv3 : (some value).bind Value.intView = some i := by
                  rw [← hv2]
                  exact hi
                show Value.intView value = some i
                exact hv3
              cases value with
              | int x =>
                  show decide (x ≠ k) = true
                  have hvi' : Value.intView (Value.int x) = some i := by
                    simpa using hvi
                  rw [Value.intView] at hvi'
                  rw [Option.some.injEq] at hvi'
                  exact decide_eq_true (by omega)
              | bool x =>
                  show decide ((if x then 1 else 0) ≠ k) = true
                  have hvi' : Value.intView (Value.bool x) = some i := by
                    simpa using hvi
                  have hx : (if x then 1 else 0) = i := by
                    have hview : Value.intView (Value.bool x)
                        = some (if x then 1 else 0) := rfl
                    rw [hview] at hvi'
                    rw [Option.some.injEq] at hvi'
                    exact hvi'
                  exact decide_eq_true (by omega)
              | setOfInt x =>
                  exact absurd hvi (by simp [Value.intView])
              | array x =>
                  exact absurd hvi (by simp [Value.intView])
          | false =>
              -- keep p = k: the slot's view IS k (negNe true)
              show value ∈ (updateSlot doms s
                (fun d => domFilterInt (fun p => decide (p = k)) d)).getD s []
              refine mem_updateSlot_of_mem doms s _ value (by
                rw [show (doms.length : Nat) = a.length from hfitlen.symm]; exact hin) ?_
              rw [domFilterInt, List.mem_filter]
              refine ⟨hfitmem s value hv, ?_⟩
              have hsat' : (negNe s k).eval a = some true := hsat
              rw [eval_negNe_iff] at hsat'
              obtain ⟨i, hi, hik⟩ := hsat'
              have hvi : Value.intView value = some i := by
                unfold slotInt at hi
                show Value.intView value = some i
                have hv2 : a[s]? = some value := by
                  show a[(⟨Atom.intNe s k, false⟩ : Literal).atom.slot]? = some value
                  exact hv
                have hv3 : (some value).bind Value.intView = some i := by
                  rw [← hv2]
                  exact hi
                show Value.intView value = some i
                exact hv3
              cases value with
              | int x =>
                  show decide (x = k) = true
                  have hvi' : Value.intView (Value.int x) = some i := by
                    simpa using hvi
                  rw [Value.intView] at hvi'
                  rw [Option.some.injEq] at hvi'
                  have : x = k := by omega
                  exact decide_eq_true this
              | bool x =>
                  show decide ((if x then 1 else 0) = k) = true
                  have hvi' : Value.intView (Value.bool x) = some i := by
                    simpa using hvi
                  have hx : (if x then 1 else 0) = i := by
                    have hview : Value.intView (Value.bool x)
                        = some (if x then 1 else 0) := rfl
                    rw [hview] at hvi'
                    rw [Option.some.injEq] at hvi'
                    exact hvi'
                  have : (if x then 1 else 0) = k := by omega
                  exact decide_eq_true this
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
      | intNe s' k =>
          cases pos with
          | false =>
              show value ∈ (updateSlot doms s'
                (fun d => domFilterInt (fun q => decide (q = k)) d)).getD slot []
              rw [updateSlot_getD_ne doms s'
                (fun d => domFilterInt (fun q => decide (q = k)) d) slot
                (fun hcon => hsl hcon)]
              exact hfitmem slot value hv
          | true =>
              show value ∈ (updateSlot doms s'
                (fun d => domFilterInt (fun q => decide (q ≠ k)) d)).getD slot []
              rw [updateSlot_getD_ne doms s'
                (fun d => domFilterInt (fun q => decide (q ≠ k)) d) slot
                (fun hcon => hsl hcon)]
              exact hfitmem slot value hv
      | boolEq s' b =>
          show value ∈ (updateSlot doms s'
            (fun _ => [Value.bool (if pos then b else !b)])).getD slot []
          rw [updateSlot_getD_ne doms s' (fun _ => [Value.bool (if pos then b else !b)]) slot
            (fun hcon => hsl hcon)]
          exact hfitmem slot value hv

/-! ### The guard: represented solutions survive a firing enqueue

An enqueue of a justified literal narrows the domains (fresh branch) or
leaves the state untouched (both skip branches). For an internal
solution REPRESENTED by the pre-state (fits the narrowed domains, and
the pre-trail covers every clause of the trail), the satisfied literal
condones the domain refinement precisely because:

* firing value filter: the slot value of the represented assignment is
  an interval-view value whose truth at the narrowed domain's determined
  way holds — correlates the domain fold's MOST narrowing prefix with
  the original;
* the witnessing literal fits through `firing`.

So the post-enqueue state again REPRESENTS the same solution. Note the
premises: unit justification is specialization of the *reason-valid*
argument (the scan's only non-falsified disjunct). -/

/-- An atom evaluating to `some` at `a` has its slot in range (the
    lookup must have succeeded). -/
theorem eval_some_slot_lt {atom : Atom} {a : Assignment} {behind : Bool}
    (h : atom.eval a = some behind) : atom.slot < a.length := by
  cases atom with
  | boolEq s b =>
      show s < a.length
      unfold Atom.eval at h
      simp only [Option.map_eq_some_iff] at h
      -- h : (match a[s]? with ...) = some true
      cases hh : a[s]? with
      | none => rw [hh] at h; simp at h
      | some v =>
          cases hv2 : v with
          | bool bv => exact (List.getElem?_eq_some_iff.mp hh).1
          | int x => rw [hh, hv2] at h; simp at h
          | setOfInt x => rw [hh, hv2] at h; simp at h
          | array x => rw [hh, hv2] at h; simp at h
  | intLe s k =>
      show s < a.length
      unfold Atom.eval slotInt at h
      simp only [Option.map_eq_some_iff] at h
      -- h : slotInt a s = some true → the bind's inner value: obtain ⟨x, hx, _⟩
      obtain ⟨w, hw, _⟩ := h
      -- hw : a[s]?.bind Value.intView = some w
      rw [Option.bind_eq_some_iff] at hw
      obtain ⟨v, hv, hvw⟩ := hw
      exact (List.getElem?_eq_some_iff.mp hv).1
  | intNe s k =>
      show s < a.length
      unfold Atom.eval slotInt at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨w, hw, _⟩ := h
      rw [Option.bind_eq_some_iff] at hw
      obtain ⟨v, hv, hvw⟩ := hw
      exact (List.getElem?_eq_some_iff.mp hv).1

/-- A literal evaluating to `some` at `a` has its slot in range: its
    atom's evaluation (up to the sign flip that keeps `some`ness) was
    `some`. -/
theorem eval_lit_some_slot_lt {l : Literal} {a : Assignment}
    (h : l.eval a = some true) : l.atom.slot < a.length := by
  unfold Literal.eval at h
  cases hatomic : l.atom.eval a with
  | none => rw [hatomic] at h; simp at h
  | some bb =>
      -- the sign map maps some → some
      rw [hatomic] at h
      simp only [Option.map_eq_some_iff] at h
      exact eval_some_slot_lt (atom := l.atom) hatomic

/-- The unit-scan step keeps the represented solution. -/
theorem unitEnqueue_represents
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st : State} {c : Clause} {l : Literal} {r : Reason}
    {a : Assignment}
    (hsol : ProblemSolution problem constraintHolds a)
    (hrep : st.Represents a)
    (hent : c.EntailedBy problem constraintHolds)
    (hscan : scanClause st c = some (.inr (l, r))) :
    (enqueueNorm st l (some r)).Represents a := by
  obtain ⟨hfit, htrail, hclauses, hlearned⟩ := hrep
  -- the unit justification: the reported literal satisfied by a
  have heval := unitEnqueue_trailSat (problem := problem)
    (constraintHolds := constraintHolds) (st := st) (c := c)
    (l := l) (r := r) (a := a) hsol
      (fun e he => htrail e he) hent hscan
  -- the same three branch analysis as in trailSat transfer
  simp only [enqueueNorm]
  split
  · refine ⟨hfit, htrail, hclauses, hlearned⟩
  · split
    · refine ⟨hfit, htrail, hclauses, hlearned⟩
    · -- fresh: the trail grows with the justified literal; the domains
      -- narrow by domOfLit, and `a` fits by the firing lemma
      refine ⟨?_, ?_, hclauses, hlearned⟩
      · -- fits: `firing` applies with the pre-state fit, the claimed
        -- slot in range (from `heval`'s some-shape: the atom's eval
        -- cannot be `some` at an out-of-range slot), and `heval`
        -- itself.
        -- Step 1: the normalized literal's truth — the scan-uniqueness
        -- argument: the clause's entailed witness at `a` must be the
        -- reported unit l
        obtain ⟨l2, hm2, hev2⟩ := hent a hsol
        have hunit := scanClause_unit_justified' (st := st) (c := c)
          (l := l) (r := r) (a := a) hscan (fun e he => htrail e he)
          ⟨l2, hm2, hev2⟩
        have hevaln : l.norm.eval a = some true := by
          rw [Literal.norm_eval l a]; exact hunit
        -- Step 2: slot range — evaluation being `some` forces the slot
          -- lookup to succeed (lemma: an atom evaluating to `some` has
          -- its slot in range)
        have hinrange : l.norm.atom.slot < a.length := by
          apply eval_lit_some_slot_lt (l := l.norm) hevaln        -- Step 3: firing
        exact firing (doms := st.domains) (l := l.norm) (a := a)
          hfit hinrange hevaln
      · -- the trail satisfaction transfers via the fresh-branch lemma's
        -- branch firing; goal is enqueueNorm-output modulo branches
        rename_i hnew hneg
        have hnew' : st.litOnTrail l.norm = false := by
          cases hb : st.litOnTrail l.norm with
          | true => exact absurd hb hnew
          | false => rfl
        have hneg' : st.negOnTrail l.norm = false := by
          cases hb : st.negOnTrail l.norm with
          | true => exact absurd hb hneg
          | false => rfl
        have hres : (enqueueNorm st l (some r)).TrailSatisfied a := heval
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
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
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
    obtain ⟨hrv, hnorms, hhead⟩ :=
      himplied p (List.mem_cons_self) l reason hrun
    -- Whether the enqueue takes a skip branch (state's trail
    -- unchanged: soundness transfers) or the fresh branch: the
    -- fresh branch's soundness needs the pivot's truth at `a`.
    simp only [enqueueNorm]
    split
    · exact Or.inl hsat
    · split
      · exact Or.inr (by simp [State.conflict])
      · -- fresh branch: the head justification (the second conjunct
        -- of `implied`) gives the enqueued literal's truth; the fresh-
        -- branch step lemma closes the trail transfer
        rename_i hnew hneg
        have hnew' : st.litOnTrail l.norm = false := by
          cases hb : st.litOnTrail l.norm with
          | true => exact absurd hb hnew
          | false => rfl
        have hneg' : st.negOnTrail l.norm = false := by
          cases hb : st.negOnTrail l.norm with
          | true => exact absurd hb hneg
          | false => rfl
        have hin' : l.eval a = some true := hhead a hsol
        have hres : (enqueueNorm st l (some reason)).TrailSatisfied a :=
          enqueueNorm_fresh_trailSat (st := st) (l0 := l)
            (reason := some reason) hnew' hneg' hsol hsat
            (by rw [Literal.norm_eval l a]; exact hin')
        unfold enqueueNorm at hres
        simp only [hnew', hneg', Bool.false_eq_true, if_false] at hres
        exact Or.inl hres
  · intro c hrun a2 hpair
    exact hconflict p (List.mem_cons_self) c hrun a2 hpair

/-! ### The propagation-loop lift -/

/-- The full carry-bundle of a propagation-loop state: everything the
    engine's downstream consumers (conflict analysis, leaf checks, the
    UNSAT terminal reports) need, in one place. -/
structure LoopInv (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
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

/-! ### The scanAll inversion -/

/-- Inversion on scanAll: a `.inl` verdict comes from a scanClause call
    on a clause of the scanned state's database. -/
theorem scanAll_inl_inv {st : State} {c : Clause}
    (h : scanAll st = some (Sum.inl c)) :
    ∃ d, scanClause st d = some (Sum.inl c) := by
  unfold scanAll at h
  have walkFun : ∀ (cs : List Clause) (v : Clause ⊕ (Literal × Reason)),
      scanAll.go st cs = some v →
      ∃ d, scanClause st d = some v := by
        intro cs
        induction cs with
        | nil => intro v hv; cases hv
        | cons d rest ih =>
            intro v hv
            simp only [scanAll.go] at hv
            match hm2 : scanClause st d, hv with
            | none, hv' =>
                exact ih v (by simpa [scanAll.go, hm2] using hv')
            | some r0, hv' =>
                exact ⟨d, by
                  cases hv'
                  exact hm2⟩
  obtain ⟨d, hd⟩ := walkFun _ _ h
  exact ⟨d, hd⟩

/-! ### The runPropagators conflict-guard -/

/-- Once a state's conflict is set, the sweep fold is a pass-through of
    the conflict value. -/
theorem runPropagators_go_conflict_fixed (props : List Propagator) :
    ∀ (ps : List Propagator) (s : State) (d : Clause),
      s.conflict = some d → (runPropagators.go ps s).conflict = some d := by
  intro ps
  induction ps with
  | nil => intro s d h; exact h
  | cons p rest ih =>
      intro s d h
      simp only [runPropagators.go]
      rw [if_pos (show s.conflict.isSome = true from by rw [h]; simp)]
      exact h

/-- Inversion for `runPropagators`: if the swept state reports a conflict
    clause `c` where the starting state had none, then the report's
    origin is either some propagator's own `.conflict` report at some
    state, or the opposing-fact pair of some literal (set inside
    `enqueueNorm` when a propagator's implied literal contradicts the
    trail). -/
theorem runPropagators_conflict_inv (props : List Propagator)
    (st : State) (c : Clause)
    (hnone : st.conflict = none)
    (hsome : (runPropagators props st).conflict = some c) :
    (∃ p, p ∈ props ∧ ∃ st2 : State, p.run st2 = .conflict c)
      ∨ (∃ w : Literal, c = [w, w.negate]) := by
  have goInv : ∀ (ps : List Propagator) (acc : State),
      acc.conflict = none →
      ∀ d, (runPropagators.go ps acc).conflict = some d →
        (∃ p, p ∈ ps ∧ ∃ st2 : State, p.run st2 = .conflict d)
          ∨ (∃ w : Literal, d = [w, w.negate]) := by
    intro ps
    induction ps with
    | nil =>
        intro acc hacnone d hgo
        have h1 : (runPropagators.go [] acc).conflict = acc.conflict := rfl
        rw [h1, hacnone] at hgo
        exact absurd hgo (by simp)
    | cons p rest ih =>
        intro acc hacnone d hgo
        simp only [runPropagators.go] at hgo
        split at hgo
        · -- guard-true: acc.conflict.isSome, contradicting hacnone
          rename_i his
          rw [hacnone] at his
          exact absurd his (by simp)
        · split at hgo
          · -- stable: recurse with acc
            obtain hres := ih acc hacnone d hgo
            rcases hres with ⟨q, hqm, st2, hrun⟩ | hpair
            · exact Or.inl ⟨q, List.mem_cons_of_mem _ hqm, st2,
                hrun⟩
            · exact Or.inr hpair
          · -- conflict: p's own report wrote it
            rename_i c2 heq
            have hc2c : c2 = d := by injection hgo
            refine Or.inl ⟨p, List.mem_cons_self, acc, ?_⟩
            rw [← hc2c]
            exact heq
          · -- implied: the fold continues at the enqueued state
            rename_i lig rsn heq
            cases hb1 : acc.litOnTrail lig.norm with
            | true =>
                -- skip arm: enqueued state is acc itself
                have hstate : enqueueNorm acc lig (some rsn) = acc := by
                  simp only [enqueueNorm, hb1, if_true]
                have hgo2 : (runPropagators.go rest acc).conflict = some d := by
                  rw [← hstate]; exact hgo
                obtain hres := ih acc hacnone d hgo2
                rcases hres with ⟨q, hqm, st2, hrun⟩ | hpair
                · exact Or.inl ⟨q, List.mem_cons_of_mem _ hqm, st2,
                    hrun⟩
                · exact Or.inr hpair
            | false =>
                cases hb2 : acc.negOnTrail lig.norm with
                | true =>
                    -- opposing-fact arm: the pair state's conflict is
                    -- the pair, and the next sweep guard passes it
                    -- through unchanged
                    have hstate : (enqueueNorm acc lig (some rsn)).conflict
                        = some [lig.norm, lig.norm.negate] := by
                      simp only [enqueueNorm, hb1, Bool.false_eq_true,
                        if_false, hb2, if_true]
                    have hpass : (runPropagators.go rest (enqueueNorm
                        acc lig (some rsn))).conflict
                        = some [lig.norm, lig.norm.negate] :=
                      runPropagators_go_conflict_fixed props rest
                        (enqueueNorm acc lig (some rsn))
                        [lig.norm, lig.norm.negate] hstate
                    rw [hpass] at hgo
                    injection hgo with hgo4
                    exact Or.inr ⟨lig.norm, hgo4.symm⟩
                | false =>
                    -- fresh enqueue: keeps acc's none conflict
                    -- the fresh enqueue never writes the conflict slot
                    have hstate2 : (enqueueNorm acc lig (some rsn)).conflict
                        = none := by
                      simp only [enqueueNorm, hb1, hb2,
                        Bool.false_eq_true, if_false]
                      exact hacnone
                    obtain hres := ih (enqueueNorm acc lig (some rsn))
                      hstate2 d hgo
                    rcases hres with ⟨q, hqm, s2, hrun2⟩ | hpair
                    · exact Or.inl ⟨q, List.mem_cons_of_mem _ hqm, s2,
                        hrun2⟩
                    · exact Or.inr hpair
  exact goInv props st hnone c hsome

/-! ### The propagation-loop bumped-up lift -/

/-- THE LOOP-LEVEL ORIGIN LIFT: if a conflict-free propagation run from
    `st` reports a conflict, then the reported clause's origin is one of
    the engine's three structural sources:

    (a) a scan verdict at some state reached by the run,
    (b) the opposing-fact pair of some literal,
    (c) some propagator's own conflict report at some state.

    The fuel induction unfolds `propagateLoop` one step and transports
    the origin through the recursion via `scanAll_inl_inv` (scan arm),
    `enqueueNorm`'s three-branch analysis (unit-enqueue arm), and the
    sweep's pass-through guard (quiesce/extend arms). -/
theorem propagateLoop_lift :
    ∀ (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
      (constraintHolds : Constraint → Assignment → Prop)
      (props : List Propagator) (fuel : Nat) (st : State),
      st.conflict = none →
      (propagateLoop fuel props st).conflict.isSome = true →
      ∃ cc, (propagateLoop fuel props st).conflict = some cc ∧
        ((∃ st1 : State, ∃ d, scanClause st1 d = some (.inl cc))
          ∨ (∃ w : Literal, cc = [w, w.negate])
            ∨ ∃ p ∈ props, ∃ d : Clause, ∃ st2 : State,
              p.run st2 = .conflict d) := by
  intro problem constraintHolds props fuel
  induction fuel with
  | zero =>
      intro st hc hisSome
      simp only [propagateLoop] at hisSome
      rw [hc] at hisSome
      exact absurd hisSome (by simp)
  | succ fuel ih =>
      intro st hc hisSome
      cases hscan : scanAll st with
      | none =>
          -- the sweep branch: the driver runs the propagators and
          -- either quiesces (returns the sweep result) or recurses at
          -- the swept state
          have hstep : propagateLoop (fuel + 1) props st
              = propagateLoop fuel props (runPropagators props st) ∨
                propagateLoop (fuel + 1) props st
                  = runPropagators props st := by
            simp only [propagateLoop, hc, Bool.false_eq_true, if_false,
              hscan, Option.isSome_none]
            split
            · exact Or.inr rfl
            · exact Or.inl rfl
          rcases hstep with hext | hquiesce
          · -- extend: recursion at the swept state
            cases hcp : (runPropagators props st).conflict with
            | none =>
                have hstepEq : propagateLoop (fuel + 1) props st
                    = propagateLoop fuel props (runPropagators props st) := hext
                rw [hstepEq]
                exact ih (runPropagators props st) (by rw [hcp])
                  (by rw [hstepEq] at hisSome; exact hisSome)
            | some c =>
                -- swept state's conflict locks the report (guard);
                -- origin pinned by the sweep inversion
                have hfix : (propagateLoop fuel props
                    (runPropagators props st)).conflict
                  = some c := by
                  cases fuel with
                  | zero => exact hcp
                  | succ k =>
                      show ((if (runPropagators props st).conflict.isSome
                        = true then (runPropagators props st)
                        else _) : State).conflict = _
                      rw [show (runPropagators props st).conflict.isSome
                        = true from by rw [hcp]; simp, if_pos rfl]
                      exact hcp
                have hstate : propagateLoop (fuel + 1) props st
                    = propagateLoop fuel props (runPropagators props st) := hext
                rw [hstate]
                rcases runPropagators_conflict_inv props st c hc hcp
                  with ⟨p, hp, st2, hrun⟩ | hpair
                · exact Exists.intro c (And.intro hfix
                    (Or.inr (Or.inr (Exists.intro p (And.intro hp
                      (Exists.intro c (Exists.intro st2 hrun)))))))
                · exact Exists.intro c (And.intro hfix
                    (Or.inr (Or.inl hpair)))
          · -- quiesce: the run IS `runPropagators props st`
            rw [hquiesce] at hisSome
            cases hcp : (runPropagators props st).conflict with
            | none =>
                rw [hcp] at hisSome
                exact absurd hisSome (by simp)
            | some c =>
                refine Exists.intro c (And.intro ?_ ?_)

                · rw [hquiesce]; exact hcp

                · rcases runPropagators_conflict_inv props st c hc hcp
                    with ⟨p, hp, st2, hrun⟩ | hpair
                  · exact Or.inr (Or.inr (Exists.intro p (And.intro hp
                      (Exists.intro c (Exists.intro st2 hrun)))))
                  · exact Or.inr (Or.inl hpair)
      | some verdict =>
          cases verdict with
          | inl c =>
              -- the scan reported the conflict directly
              refine Exists.intro c (And.intro ?_ ?_)
              · have hstate : propagateLoop (Nat.succ fuel) props st
                    = { st with conflict := some c } := by
                  simp only [propagateLoop, hc, Bool.false_eq_true, if_false,
                    hscan, Option.isSome_none]
                rw [hstate]
              · exact Or.inl (Exists.intro st
                  (scanAll_inl_inv hscan))
          | inr w =>
              -- the loop enqueued and recursed: w = (l, r)
              obtain ⟨l, r⟩ := w
              cases hnt : st.litOnTrail l.norm with
              | true =>
                  -- skip-on-trail: the enqueued state is st itself
                  have h1 : propagateLoop (fuel + 1) props st
                      = propagateLoop fuel props (enqueueNorm st l
                        (some r)) := by
                    simp only [propagateLoop, hc, Bool.false_eq_true,
                      if_false, hscan, Option.isSome_none]
                  have h2 : enqueueNorm st l (some r) = st := by
                    simp only [enqueueNorm, hnt, if_true]
                  have hstep : (propagateLoop fuel props st).conflict.isSome
                      = true := by
                    rw [h1, h2] at hisSome
                    exact hisSome
                  obtain ⟨cc, hcc, horg⟩ := ih st hc hstep
                  refine Exists.intro cc (And.intro ?_ horg)
                  show (propagateLoop (fuel + 1) props st).conflict = some cc
                  rw [h1, h2]
                  exact hcc
              | false =>
                  cases hneg : st.negOnTrail l.norm with
                  | true =>
                      -- opposing-fact: the enqueued state's conflict is
                      -- the pair; the driver's next guard passes it
                      -- through unchanged, so the reported clause IS
                      -- the pair
                      have h2 : (enqueueNorm st l (some r)).conflict
                          = some [l.norm, l.norm.negate] := by
                        simp only [enqueueNorm, hnt, Bool.false_eq_true,
                          if_false, hneg]
                        rfl
                      have hstep : propagateLoop (fuel + 1) props st
                          = propagateLoop fuel props (enqueueNorm st l
                            (some r)) := by
                        simp only [propagateLoop, hc, Bool.false_eq_true,
                          if_false, hscan, Option.isSome_none]
                      have hguard : (propagateLoop fuel props
                          (enqueueNorm st l (some r))).conflict
                        = some [l.norm, l.norm.negate] := by
                        cases fuel with
                        | zero => exact h2
                        | succ k =>
                            show ((if (enqueueNorm st l (some r)).conflict.isSome
                              = true then (enqueueNorm st l (some r))
                              else _) : State).conflict = _
                            rw [show (enqueueNorm st l (some r)).conflict.isSome
                              = true from by rw [h2]; simp, if_pos rfl]
                            exact h2
                      rw [hstep]
                      refine Exists.intro [l.norm, l.norm.negate]
                        (And.intro hguard ?_)
                      exact Or.inr (Or.inl (Exists.intro l.norm rfl))
                  | false =>
                      -- fresh enqueue: never writes the conflict slot
                      have hst2none : (enqueueNorm st l (some r)).conflict
                          = none := by
                        simp only [enqueueNorm, hnt, Bool.false_eq_true,
                          if_false, hneg, Bool.false_eq_true, if_false,
                          enqueue]
                        exact hc
                      have hstep : propagateLoop (fuel + 1) props st
                          = propagateLoop fuel props (enqueueNorm st l
                            (some r)) := by
                        simp only [propagateLoop, hc, Bool.false_eq_true,
                          if_false, hscan, Option.isSome_none]
                      obtain ⟨cc, hcc, horg⟩ := ih (enqueueNorm st l
                        (some r)) hst2none (by rw [← hstep] at *; exact hisSome)
                      refine Exists.intro cc (And.intro ?_ horg)
                      have hcongr :
                          (propagateLoop (fuel + 1) props st).conflict
                            = (propagateLoop fuel props (enqueueNorm st l
                              (some r))).conflict := by
                        rw [hstep]
                      rw [hcongr]
                      exact hcc

end LeanFzn.Solver.Propagation

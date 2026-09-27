/- s27 (v2): the ≤1-length per-slot discipline, getD form.

    domOfLt_getD_le_one: if every slot of doms has length ≤ 1, then
    every slot of domOfLit doms l has length ≤ 1 — read through getD,
    which is both how allSingleton's fold sees domains and how
    mem_getD_updateSlot_eq/ne speak.
-/

import solver.LCG.Proofs.Theory

namespace LeanFzn.Solver.LCG

open LeanFzn LeanFzn.Solver.Core

/-- Filtering a ≤1-element list keeps ≤ 1 elements. -/
theorem filter_le_one {α : Type} (p : α → Bool) (l : List α)
    (h : l.length ≤ 1) : (l.filter p).length ≤ 1 := by
  match l with
  | [] => simp
  | [v] =>
      by_cases hp : p v
      · simp [hp]
      · simp [hp]
  | v1 :: v2 :: rest =>
      exfalso
      simp only [List.length_cons] at h
      omega

/-- domFilterInt keeps the ≤ 1 length discipline. -/
theorem domFilterInt_le_one {d : List Value} {keep : Int → Bool}
    (h : d.length ≤ 1) : (domFilterInt keep d).length ≤ 1 := by
  unfold domFilterInt
  exact filter_le_one _ _ h

/-! ## The per-slot discipline through getD -/

/-- Length at the SAME in-range index after updateSlot is the image's
    length: updateSlot reads the old slot and replaces it by f of it.
    (Out of range, getD is [] on both sides and f's value on the
    DEFAULT is irrelevant — the discipline only needs in-range.) -/
theorem length_getD_updateSlot_eq : ∀ (doms : List (List Value)) (s : Nat)
    (f : List Value → List Value),
    s < doms.length →
    ((updateSlot doms s f).getD s []).length = (f (doms.getD s [])).length := by
  intro doms
  induction doms with
  | nil => intro s f hlt; simp only [List.length_nil] at hlt; exact absurd hlt (by omega)
  | cons d ds ih =>
      intro s f hlt
      cases s with
      | zero => rfl
      | succ s' =>
          simp only [updateSlot, List.getD_cons_succ,
            List.length_cons] at hlt ⊢
          exact ih s' f (by omega)

/-- Length at a DIFFERENT index after updateSlot is unchanged. -/
theorem length_getD_updateSlot_ne : ∀ (doms : List (List Value))
    (s s0 : Nat) (f : List Value → List Value),
    s0 ≠ s →
    ((updateSlot doms s f).getD s0 []).length = (doms.getD s0 []).length := by
  intro doms
  induction doms with
  | nil =>
      intro s s0 f _
      cases s <;> cases s0 <;>
        simp [updateSlot, setSlot, getSlot, List.getD, List.length_nil]
  | cons d ds ih =>
      intro s s0 f hne
      cases s with
      | zero =>
          cases s0 with
          | zero => exact absurd rfl hne
          | succ s0' => rfl
      | succ s' =>
          cases s0 with
          | zero => rfl
          | succ s0' =>
              simp only [updateSlot, List.getD_cons_succ]
              exact ih s' s0' f (by omega)

/-! ## The per-slot discipline -/

/-- THE PER-SLOT DISCIPLINE: if every slot of doms has ≤ 1 value, so
    does every slot of domOfLit doms l — for ANY literal (both
    polarities, both atom kinds). -/
theorem domOfLt_getD_le_one : ∀ (doms : List (List Value)) (l : Literal),
    (∀ s : Nat, (doms.getD s []).length ≤ 1) →
    (∀ s : Nat, ((domOfLit doms l).getD s []).length ≤ 1) := by
  intro doms l hall
  cases l with
  | mk atom pos =>
    cases pos with
    | false =>
      cases atom with
      | intLe sl k =>
          -- NEGATIVE int literal: filter p > k at slot sl
          intro s
          show ((domOfLit doms ⟨.intLe sl k, false⟩).getD s []).length ≤ 1
          unfold domOfLit
          simp only [Bool.false_eq_true, if_false]
          by_cases hs : s = sl
          · rw [hs]
            by_cases hrange : sl < doms.length
            · rw [length_getD_updateSlot_eq doms sl _ hrange]
              exact domFilterInt_le_one
                (d := doms.getD sl [])
                (keep := fun p => decide (p > k))
                (hall sl)
            · have hge : doms.length ≤ sl := Nat.le_of_not_lt hrange
              unfold updateSlot
              rw [setSlot_eq_self_of_le doms (domFilterInt
                (fun p => decide (p > k)) (doms.getD sl [])) sl hge]
              exact hall sl
          · rw [length_getD_updateSlot_ne doms sl s _ (fun h => hs h)]
            exact hall s
      | boolEq sl b =>
          -- NEGATIVE bool literal: pin to !b at slot sl
          intro s
          show ((domOfLit doms ⟨.boolEq sl b, false⟩).getD s []).length ≤ 1
          unfold domOfLit
          simp only [Bool.false_eq_true, if_false]
          by_cases hs : s = sl
          · rw [hs]
            by_cases hrange : sl < doms.length
            · rw [length_getD_updateSlot_eq doms sl _ hrange]
              exact Nat.le_refl _
            · have hge : doms.length ≤ sl := Nat.le_of_not_lt hrange
              unfold updateSlot
              rw [setSlot_eq_self_of_le doms [.bool (!b)] sl hge]
              exact hall sl
          · rw [length_getD_updateSlot_ne doms sl s _ (fun h => hs h)]
            exact hall s
    | true =>
      cases atom with
      | intLe sl k =>
          -- POSITIVE int literal: filter p ≤ k at slot sl
          intro s
          show ((domOfLit doms ⟨.intLe sl k, true⟩).getD s []).length ≤ 1
          unfold domOfLit
          simp only [if_true]
          by_cases hs : s = sl
          · rw [hs]
            by_cases hrange : sl < doms.length
            · rw [length_getD_updateSlot_eq doms sl _ hrange]
              exact domFilterInt_le_one
                (d := doms.getD sl [])
                (keep := fun p => decide (p ≤ k))
                (hall sl)
            · have hge : doms.length ≤ sl := Nat.le_of_not_lt hrange
              unfold updateSlot
              rw [setSlot_eq_self_of_le doms (domFilterInt
                (fun p => decide (p ≤ k)) (doms.getD sl [])) sl hge]
              exact hall sl
          · rw [length_getD_updateSlot_ne doms sl s _ (fun h => hs h)]
            exact hall s
      | boolEq sl b =>
          -- POSITIVE bool literal: pin to b at slot sl
          intro s
          show ((domOfLit doms ⟨.boolEq sl b, true⟩).getD s []).length ≤ 1
          unfold domOfLit
          simp only [if_true]
          by_cases hs : s = sl
          · rw [hs]
            by_cases hrange : sl < doms.length
            · rw [length_getD_updateSlot_eq doms sl _ hrange]
              exact Nat.le_refl _
            · have hge : doms.length ≤ sl := Nat.le_of_not_lt hrange
              unfold updateSlot
              rw [setSlot_eq_self_of_le doms [.bool b] sl hge]
              exact hall sl
          · rw [length_getD_updateSlot_ne doms sl s _ (fun h => hs h)]
            exact hall s



/-- decideLiteral is none at ANY state with the ≤ 1-per-slot
    discipline: no bisection anywhere. -/
theorem decideLiteral_none_of_le_one (st : State)
    (hall : ∀ s : Nat, (st.domains.getD s []).length ≤ 1) :
    decideLiteral st = none := by
  unfold decideLiteral
  have hgo : ∀ (s : Nat) (ds : List (List Value)),
      (∀ s2 : Nat, (ds.getD s2 []).length ≤ 1) →
      decideLiteral.go s ds = none := by
    intro s ds
    induction ds generalizing s with
    | nil => intro _; rfl
    | cons d rest ih =>
        intro hall
        -- the head slot's length ≤ 1 means at most 1 int value
        have hd1 : (d.length ≤ 1) := by
          have := hall 0
          simp only [List.getD_cons_zero] at this
          exact this
        have hdi : (domInts d).length ≤ 1 := by
          match hd : d with
          | [] => simp [domInts]
          | [v] =>
              unfold domInts
              cases v <;> simp
          | v1 :: v2 :: rest2 =>
              exfalso
              simp only [List.length_cons] at hd1
              omega
        have hrest : ∀ s2 : Nat, (rest.getD s2 []).length ≤ 1 := by
          intro s2
          have := hall (s2 + 1)
          simp only [List.getD_cons_succ] at this
          exact this
        simp only [decideLiteral.go]
        match hdi2 : domInts d with
        | [] =>
            have hmn : domMinI d = none := domMinI_of_nil hdi2
            have hmx : domMaxI d = none := domMaxI_of_nil hdi2
            rw [hmn, hmx]
            exact ih (s + 1) hrest
        | [v] =>
            have hmn : domMinI d = some v := domMinI_of_single hdi2
            have hmx : domMaxI d = some v := domMaxI_of_single hdi2
            rw [hmn, hmx]
            simp only []
            rw [if_neg (by omega)]
            exact ih (s + 1) hrest
        | v1 :: v2 :: vs =>
            exfalso
            have : (domInts d).length ≥ 2 := by rw [hdi2]; simp
            omega
  exact hgo 0 st.domains hall

/-! ## The go-level fragment discipline -/

/-- The enqueued state's domains after enqueueNorm are either the
    fresh-arm narrowing or the original's. -/
theorem enqueueNorm_domains_cases {st : State} {l : Literal}
    {reason : Option Reason} :
    (enqueueNorm st l reason).domains = domOfLit st.domains l.norm ∨
    (enqueueNorm st l reason).domains = st.domains := by
  unfold enqueueNorm
  cases hb : st.litOnTrail l.norm with
  | true =>
    simp only [hb, if_true]
    exact Or.inr (by simp)
  | false =>
    simp only [hb, Bool.false_eq_true, if_false]
    cases hb2 : st.negOnTrail l.norm with
    | true =>
      simp only [if_true]
      exact Or.inr (by simp)
    | false =>
      simp only [Bool.false_eq_true, if_false]
      exact Or.inl rfl

/-- propagateLoop preserves the ≤1-per-slot discipline: every domain
    change is a domOfLit step (enqueueNorm's fresh arm) or none. -/
theorem propagateLoop_le_one {props : List Propagator} :
    ∀ (fuel : Nat) (st : State),
      (∀ s : Nat, (st.domains.getD s []).length ≤ 1) →
      (∀ s : Nat, ((propagateLoop fuel props st).domains.getD s []).length ≤ 1) := by
  intro fuel
  induction fuel with
  | zero => intro st hall; exact hall
  | succ k ih =>
      intro st hall
      cases hc : st.conflict with
      | some c =>
          -- a conflicting state is the fixpoint: domains unchanged
          rw [propagateLoop_conflict_fix props (k + 1) st c hc]
          exact hall
      | none =>
          cases hscan : scanAll st with
          | none =>
              have hUnf : propagateLoop (k + 1) props st =
                  (if ((runPropagators props st).trail.length == st.trail.length)
                    = true then runPropagators props st
                  else propagateLoop k props (runPropagators props st)) := by
                simp [propagateLoop, hc, hscan, Option.isSome_none]
              rw [hUnf]
              -- the sweep's own discipline (runPropagators lemma):
              have hgo : ∀ (ps : List Propagator) (acc : State),
                  (∀ s : Nat, (List.getD acc.domains s []).length ≤ 1) →
                  (∀ s : Nat, (List.getD
                    (runPropagators.go ps acc).domains
                    s []).length ≤ 1) := by
                intro ps
                induction ps with
                | nil => intro acc hall; exact hall
                | cons p rest ihp =>
                    intro acc hall
                    have hstep : ∀ (acc2 : State) (s : Nat),
                        (∀ s : Nat, (List.getD acc2.domains s []).length ≤ 1) →
                      (List.getD (runPropagators.go (p :: rest) acc2).domains
                        s []).length ≤ 1 := by
                      intro acc2 s hall2
                      simp only [runPropagators.go]
                      split
                      · -- guard-true: acc unchanged
                        exact hall2 s
                      · -- guard-false: three match arms
                        next hgt =>
                        split
                        · -- stable
                          exact ihp acc2 hall2 s
                        · -- conflict: only the conflict field is set
                          next c hconf =>
                            exact hall2 s
                        · -- implied
                          next lig rsn hr =>
                            have hdom : ∀ s2 : Nat, (List.getD
                                (enqueueNorm acc2 lig (some rsn)).domains
                                s2 []).length ≤ 1 := by
                              intro s2
                              rcases enqueueNorm_domains_cases (st := acc2)
                                (l := lig) (reason := some rsn) with hd | hd
                              · rw [hd]
                                exact domOfLt_getD_le_one acc2.domains
                                  lig.norm hall2 s2
                              · rw [hd]
                                exact hall2 s2
                            exact ihp (enqueueNorm acc2 lig (some rsn)) hdom s
                    intro s
                    exact hstep acc s hall
              by_cases hlen : ((runPropagators props st).trail.length ==
                  st.trail.length) = true
              · rw [if_pos hlen]
                exact hgo props st hall
              · rw [if_neg hlen]
                exact ih (runPropagators props st) (hgo props st hall)
          | some verdict =>
              cases verdict with
              | inl c =>
                  -- scan conflict: only the conflict field is set
                  show ∀ s : Nat, (List.getD
                    (propagateLoop (k+1) props st).domains
                    s []).length ≤ 1
                  rw [show propagateLoop (k+1) props st
                    = { st with conflict := some c } by
                    simp [propagateLoop, hc, hscan, Option.isSome_none]]
                  exact hall
              | inr w =>
                  match w with
                  | (l, r) =>
                      have hUnf : propagateLoop (k + 1) props st
                          = propagateLoop k props (enqueueNorm st l (some r)) := by
                        simp [propagateLoop, hc, hscan, Option.isSome_none]
                      rw [hUnf]
                      -- the enqueued state's discipline (three arms)
                      have hdom : ∀ s : Nat, (List.getD
                          (enqueueNorm st l (some r)).domains
                          s []).length ≤ 1 := by
                        intro s
                        rcases enqueueNorm_domains_cases (st := st)
                          (l := l) (reason := some r) with hd | hd
                        · rw [hd]
                          exact domOfLt_getD_le_one st.domains l.norm hall s
                        · rw [hd]
                          exact hall s
                      exact ih (enqueueNorm st l (some r)) hdom


/-! ## The fragment's no-decision go lemma -/

/-- For the all-singleton fragment, `go` NEVER produces a decision:
    at any iterate reached from the initial state (whose domains are
    the problem's — the initial plus domOfLit-folds), every slot has
    ≤ 1 value, so decideLiteral is none. The proof is by induction
    over fuel, carrying the ≤1 discipline (propagateLoop_le_one +
    repairs rebuilding from the problem's domains via fold). -/
theorem go_fragment_no_decide
    {problem : Problem Constraint Objective}
    {constraintHoldsB : Constraint → Assignment → Bool}
    {props : List Propagator}
    (hfrag : ∀ s : Nat, (List.getD problem.domains s []).length ≤ 1) :
    ∀ (fuel : Nat) (st : State),
      st.domains = (st.trail.foldl (fun acc e => domOfLit acc e.literal)
        problem.domains) →
      (lcgSearch.go problem constraintHoldsB props fuel st = .unsat) →
        st.decisionLevel = 0 ∧
        ((propagateLoop (32 + 8 * st.domains.length + 4 * st.trail.length)
            props st).conflict.isSome = true
          ∨
          ((propagateLoop (32 + 8 * st.domains.length + 4 * st.trail.length)
              props st).conflict = none ∧
            allSingleton (propagateLoop
              (32 + 8 * st.domains.length + 4 * st.trail.length)
              props st) = true ∧
            ∃ a, singletonAssignment (propagateLoop
              (32 + 8 * st.domains.length + 4 * st.trail.length)
              props st) = some a ∧
            ¬ (fitsB problem a &&
                problem.constraints.all (fun c => constraintHoldsB c a))))
  := by
  sorry

end LeanFzn.Solver.LCG

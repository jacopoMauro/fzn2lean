/-
File: LeanFzn/Solver/Propagation/Proofs/FallbackFit.lean

Purpose:
  The `hnoFit` discharge for the chronological-fallback nogood
  (PLAN.md §5 items 4–5): the remaining front-door obligation left
  open by LeanFzn/Solver/UIP/Proofs/Fallback.lean — at a conflict-free
  run-invariant entry whose propagation ends conflict-carrying with
  an unresolvable analysis, no assignment fitting the propagated
  domains is an internal problem solution.

  THE HONEST GATE. The propagated conflict has three structural
  origins (the `propagateLoop_lift` trichotomy, Proofs/Lift.lean):

  * (a) PROPAGATOR reports — some propagator returns `.conflict c`
    at an intermediate sweep accumulator. The sweep's conflict arm
    returns `{acc with conflict := some c}` (domains unchanged,
    Engine.lean's `runPropagators.go`), and the loop passes
    conflict-carrying states through unchanged
    (`propagateLoop_conflict_fix`), so the FINAL state's domains ARE
    the reporting accumulator's — which the sweep keeps
    domain-coherent (`runPropagators_go_coherent`). The per-family
    fits-exclusion (each `propX_safe`'s conflict bullet: a conflict
    excludes every FITTING constraint-satisfier, stated with NO trail
    dependence) applies AT THAT ACCUMULATOR and transfers to the
    final state unchanged. This arm needs no emptiness.

  * (b) SCAN reports — every literal of an active (original or
    learned) clause is trail-false. A fitting assignment need not
    satisfy the trail, so trail-falsification alone excludes
    nothing; for NONEMPTY clauses this arm genuinely fails (the
    counterexample sketch below). For the EMPTY clause, however,
    the reported clause is an entitled database clause, and an
    empty entitled clause refutes every internal solution — the
    exclusion holds VACUOUSLY. No database-emptiness premise is
    needed: an empty ORIGINAL clause is refuted by the clause
    entitlement premise `hdb`, an empty LEARNED clause by the
    threaded learned entitlement.

  * (c) OPPOSING-PAIR — `enqueueNorm` sets `[l, l.negate]` when a
    propagator's implied literal opposes a trail fact. The pair is
    a two-literal clause, NEVER empty — under the empty-conflict
    gate this origin is impossible. (Without the gate the
    pair-origin exclusion is again false in general: the opposing
    trail fact can be an overridden Boolean pin, resurrecting the
    implied literal's negation at a fitting solution.)

  So the theorem proved here is the EMPTY-CONFLICT version
  (`propagateLoop_conflict_nofit_empty`): when the propagated
  conflict clause is `[]` — exactly the `neSlot`/propNe shape of
  the ph3/ph4 pigeonhole use case (propNe reports `.conflict []` on
  equal raw singletons) — the fits-exclusion holds for all three
  origins.

  Why the master theorem's own premises do not give emptiness:
  `analyzeConflict = none` HOLDS for empty conflicts
  (`analyzeConflict_empty_none`), but nonempty conflicts can also
  fail to analyze (all falsifiers below the current level make the
  mark set empty and `nextPivot` none; a decision-pivot with
  remaining marks makes `analyzeStep` return none). The composed
  front door (`propagatorsOfProved_fallbackng'`) therefore carries
  the empty-conflict observable as its one extra premise
  (`hconfempty`); an engine gate distinguishing propagator-origin
  conflicts — e.g. learning the fallback nogood only when the
  conflict clause is empty — would make the front door
  unconditional for the compiled path.

  THE COUNTEREXAMPLE SHAPE (why the unrestricted `hnoFit` is FALSE
  for the scan origin; no Lean term is built, this documents the
  obstruction): a Boolean slot `s` whose problem domain is all-Bool;
  the trail carries a BELOW-LEVEL order fact `¬(s ≤ 1)` (emptying
  the slot's viewed values through the `domOfLit` fold) and a LATER
  Boolean pin `s = true` (re-filling it); the original clause
  `[(s ≤ 1)]` is entitled (Bool views are ≤ 1) and scan-conflicting
  (its only literal is trail-false, no literal is on-trail); every
  falsifier sits below the current level, so the analysis returns
  `none` and the fallback arm fires. The assignment `[bool true]`
  fits the folded domains (the pin re-filled the emptied slot) and
  satisfies every constraint — a fitting internal solution at a
  scan-origin fallback conflict. Only the empty-conflict gate (this
  file) or a stronger trail-vs-domain premise closes that arm.

Contents:
  * `runPropagators_conflict_nofit_empty` — the sweep-level
    exclusion: an empty swept conflict excludes every fitting
    solution (origin (a) via the per-family fits-exclusion at the
    frozen accumulator; origin (c) refuted by the pair's
    nonemptiness).
  * `propagateLoop_conflict_nofit_empty` — the loop-level theorem:
    at a conflict-free, domain-coherent, database-fixed entry, an
    empty propagated conflict excludes every assignment fitting the
    propagated domains (origin (b) vacuous via entitlement, plus the
    two sweep origins).
  * `propagatorsOfProved_fitexcl` — the ELEVEN-family assembly of
    the per-family fits-exclusion (`hfitexcl`) over the registered
    proved propagators, mirroring `propagatorsOfProved_safeUniv`'s
    dispatch (the conflict bullet of each family's safety triple).
  * `propagatorsOfProved_fitexcl_nolinle` — the same dispatch under
    the front door's no-linLe registration premise.
  * `propagatorsOfProved_fallbackng'` — the composed front door:
    `propagatorsOfProved_fallbackng` (Fallback.lean) with its
    `hnoFit` premise DISCHARGED from the empty-conflict observable.

Dependencies:
  - LeanFzn.Solver.Propagation.Proofs.Fallback (the front door whose `hnoFit`
    premise this file discharges; transitively Reason, Propagators,
    ConstFamilies, Run, Theory, Lift, Engine — the family safety
    triples, the sweep/loop fixpoint and inversion lemmas, the
    run invariant, `RunInv`).

DAG:
  Propagate + Theory + ConstFamilies + Run -> Reason -> Fallback
    -> FallbackFit (a leaf; nothing above it imports it yet)
-/

import LeanFzn.Solver.Propagation.Proofs.Fallback
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Reference


open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Reference

/-! ## The sweep-level fits-exclusion

An EMPTY conflict reported by one full propagator sweep from a
conflict-free, domain-coherent state excludes every assignment
fitting the swept state's domains. The sweep's conflict arm returns
`{acc with conflict := some c}` with the accumulator's domains
unchanged, so the exclusion is established AT the reporting
accumulator — coherent by the sweep's own preservation — where the
per-family fits-exclusion (`hfitexcl`) applies. The opposing-pair
arm of `enqueueNorm` (inside the sweep's implied arm) is refuted by
the pair's nonemptiness against the empty-conflict premise. No
clause database and no trail premises are consumed. -/

/-- THE SWEEP-LEVEL FITS-EXCLUSION: when a conflict-free,
    domain-coherent state's propagator sweep reports the EMPTY
    conflict clause, no assignment fitting the swept state's
    domains is an internal problem solution. The reporting
    accumulator's domains ARE the swept state's (the sweep's
    conflict arm only sets the conflict slot), and the sweep keeps
    every accumulator domain-coherent, so the per-family
    fits-exclusion `hfitexcl` applies at the reporting state. The
    opposing-pair arm cannot produce an empty conflict (the pair
    `[l, l.negate]` has two literals). -/
theorem runPropagators_conflict_nofit_empty
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {props : List Propagator}
    (hfitexcl : ∀ (st : State), DomainCoherent problem st →
      ∀ p ∈ props, ∀ c, p.run st = .conflict c →
        ∀ a, a.Fits st.domains →
          ¬ ProblemSolution problem constraintHolds a) :
    ∀ (st : State), st.conflict = none →
      DomainCoherent problem st →
      (runPropagators props st).conflict = some [] →
      ∀ a, a.Fits (runPropagators props st).domains →
        ¬ ProblemSolution problem constraintHolds a := by
  -- the internal sweep induction: each propagator's conflict report
  -- is witnessed at its own (coherent) accumulator; implied literals
  -- enqueue through enqueueNorm whose three branches are handled
  have goInv : ∀ (ps : List Propagator) (acc : State),
      (∀ q ∈ ps, q ∈ props) →
      acc.conflict = none →
      DomainCoherent problem acc →
      (runPropagators.go ps acc).conflict = some [] →
      ∀ a, a.Fits (runPropagators.go ps acc).domains →
        ¬ ProblemSolution problem constraintHolds a := by
    intro ps
    induction ps with
    | nil =>
        intro acc _ hacnone _ hgo
        have h1 : runPropagators.go [] acc = acc := rfl
        rw [h1] at hgo
        rw [hacnone] at hgo
        exact absurd hgo (by simp)
    | cons p rest ih =>
        intro acc hmem hacnone hcohacc hgo a hfit
        have hp : p ∈ props := hmem p (List.mem_cons_self)
        have hrest : ∀ q ∈ rest, q ∈ props := fun q hq =>
          hmem q (List.mem_cons_of_mem _ hq)
        match hrun : p.run acc with
        | PropagationResult.stable =>
            -- the sweep continues at the same accumulator
            have hEq : runPropagators.go (p :: rest) acc
                = runPropagators.go rest acc := by
              simp only [runPropagators.go, hrun]
              split
              · next his =>
                  rw [hacnone] at his
                  exact absurd his (by simp)
              · rfl
            rw [hEq] at hgo hfit
            exact ih acc hrest hacnone hcohacc hgo a hfit
        | PropagationResult.conflict c =>
            -- p's own report: the sweep returns the accumulator with
            -- only the conflict slot set — the domains ARE acc's, and
            -- acc is domain-coherent, so hfitexcl applies there
            have hEq : runPropagators.go (p :: rest) acc
                = { acc with conflict := some c } := by
              simp only [runPropagators.go, hrun]
              split
              · next his =>
                  rw [hacnone] at his
                  exact absurd his (by simp)
              · rfl
            rw [hEq] at hgo hfit
            exact hfitexcl acc hcohacc p hp c hrun a hfit
        | PropagationResult.implied l r =>
            -- the enqueue's three branches: skip (identity), opposing
            -- (the two-literal pair — nonempty, contradicting the
            -- empty swept conflict), fresh (conflict stays clear)
            have hEq : runPropagators.go (p :: rest) acc
                = runPropagators.go rest (enqueueNorm acc l (some r)) := by
              simp only [runPropagators.go, hrun]
              split
              · next his =>
                  rw [hacnone] at his
                  exact absurd his (by simp)
              · rfl
            rw [hEq] at hgo hfit
            cases hb1 : acc.litOnTrail l.norm with
            | true =>
                have hskip : enqueueNorm acc l (some r) = acc := by
                  simp only [enqueueNorm, hb1, if_true]
                rw [hskip] at hgo hfit
                exact ih acc hrest hacnone hcohacc hgo a hfit
            | false =>
                cases hb2 : acc.negOnTrail l.norm with
                | true =>
                    -- the opposing arm: the pair conflict is final
                    -- (the sweep guard passes it through), and a
                    -- two-literal clause cannot be empty
                    have hpair : (enqueueNorm acc l (some r)).conflict
                        = some [l.norm, l.norm.negate] := by
                      simp only [enqueueNorm, hb1, Bool.false_eq_true,
                        if_false, hb2, if_true]
                    have hpass : (runPropagators.go rest
                        (enqueueNorm acc l (some r))).conflict
                        = some [l.norm, l.norm.negate] :=
                      runPropagators_go_conflict_fixed props rest
                        (enqueueNorm acc l (some r))
                        [l.norm, l.norm.negate] hpair
                    rw [hpass] at hgo
                    exfalso
                    injection hgo with hgo2
                    exact absurd hgo2 (by simp)
                | false =>
                    have hfresh : (enqueueNorm acc l (some r)).conflict
                        = none := by
                      simp only [enqueueNorm, hb1, hb2,
                        Bool.false_eq_true, if_false]
                      exact hacnone
                    exact ih (enqueueNorm acc l (some r)) hrest hfresh
                      (enqueueNorm_coherent hcohacc) hgo a hfit
  intro st hnone hcoh hrep a hfit
  exact goInv props st (fun q hq => hq) hnone hcoh hrep a hfit

/-! ## The loop-level fits-exclusion (the empty-conflict gate)

The propagation loop's three arms assemble the sweep theorem with
the two remaining origins: the SCAN arm's empty reported clause is
an entitled database clause (an empty entitled clause refutes every
solution — the exclusion is vacuous), and the UNIT arm recurses (the
scan-unit enqueue is unconditionally conflict-clear). The sweep arm
quiesces or extends; an extended conflict-carrying swept state is
returned unchanged (the fixpoint lemma), so the sweep theorem
applies at the entry directly. -/

/-- THE LOOP-LEVEL FITS-EXCLUSION (the `hnoFit` discharge under the
    empty-conflict gate): at a conflict-free, domain-coherent,
    database-fixed entry, when the whole propagation loop ends with
    the EMPTY conflict clause, no assignment fitting the propagated
    domains is an internal problem solution.

    Premises: `hfitexcl` (the per-family propagator fits-exclusion —
    see `propagatorsOfProved_fitexcl` for the eleven-family
    assembly), `hdb` (the original clause database's entitlement),
    and the entry's own coherence, clause fixity, and learned
    entitlement (RunInv's `coherent`/`clausesFixed`/
    `learnedEntailed` fields). No `analyzeConflict` premise is
    needed: the empty conflict clause is the operative observable
    (an empty conflict never analyzes, but nonempty conflicts can
    also fail to analyze — see the module header). -/
theorem propagateLoop_conflict_nofit_empty
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {props : List Propagator}
    (hfitexcl : ∀ (st : State), DomainCoherent problem st →
      ∀ p ∈ props, ∀ c, p.run st = .conflict c →
        ∀ a, a.Fits st.domains →
          ¬ ProblemSolution problem constraintHolds a)
    (hdb : ∀ c ∈ problem.clauses, ∀ a,
      ProblemSolution problem constraintHolds a →
        ∃ l ∈ c, l.eval a = some true) :
    ∀ (fuel : Nat) (st : State),
      st.conflict = none →
      DomainCoherent problem st →
      st.clauses = problem.clauses →
      (∀ c ∈ st.learned, ∀ a,
        ProblemSolution problem constraintHolds a →
          ∃ l ∈ c, l.eval a = some true) →
      (propagateLoop fuel props st).conflict = some [] →
      ∀ a, a.Fits (propagateLoop fuel props st).domains →
        ¬ ProblemSolution problem constraintHolds a := by
  intro fuel
  induction fuel with
  | zero =>
      intro st hnone _ _ _ hrep
      simp only [propagateLoop] at hrep
      rw [hnone] at hrep
      exact absurd hrep (by simp)
  | succ fuel ih =>
      intro st hnone hcoh hclfix hlearned hrep
      cases hscan : scanAll st with
      | none =>
          -- the sweep arm: quiesce (the swept state is the answer) or
          -- extend (recurse at the swept state; a swept conflict is
          -- final by the fixpoint lemma)
          have hUnf : propagateLoop (fuel + 1) props st =
              (if ((runPropagators props st).trail.length ==
                  st.trail.length) = true
                then runPropagators props st
              else propagateLoop fuel props (runPropagators props st)) := by
            simp [propagateLoop, hnone, hscan, Option.isSome_none]
          rw [hUnf] at hrep ⊢
          by_cases hlen : ((runPropagators props st).trail.length ==
              st.trail.length) = true
          · -- quiesced: the sweep's own exclusion at the entry
            rw [if_pos hlen] at hrep ⊢
            exact runPropagators_conflict_nofit_empty hfitexcl st hnone
              hcoh hrep
          · -- extended: recurse, or the swept conflict is final
            rw [if_neg hlen] at hrep ⊢
            have hcl2 : (runPropagators props st).clauses = st.clauses := by
              unfold runPropagators
              exact runPropagators_go_clauses props st
            have hln2 : (runPropagators props st).learned = st.learned := by
              unfold runPropagators
              exact runPropagators_go_learned props st
            cases hconf2 : (runPropagators props st).conflict with
            | none =>
                exact ih (runPropagators props st) hconf2
                  (runPropagators_coherent props st hcoh)
                  (by rw [hcl2]; exact hclfix)
                  (by rw [hln2]; exact hlearned) hrep
            | some c2 =>
                have hfix : propagateLoop fuel props (runPropagators props st)
                    = runPropagators props st :=
                  propagateLoop_conflict_fix props fuel
                    (runPropagators props st) c2 hconf2
                rw [hfix] at hrep ⊢
                exact runPropagators_conflict_nofit_empty hfitexcl st hnone
                  hcoh hrep
      | some verdict =>
          cases verdict with
          | inl c =>
              -- the scan arm: the reported clause is an entitled
              -- database clause; c = [] makes the entitlement refute
              -- every solution, so the exclusion is vacuous
              have hUnf : propagateLoop (fuel + 1) props st
                  = { st with conflict := some c } := by
                simp [propagateLoop, hnone, hscan, Option.isSome_none]
              rw [hUnf] at hrep ⊢
              intro a _hfit ha
              have hce : c = [] := by injection hrep
              obtain ⟨d, hdm, hds⟩ := scanAll_inl_full hscan
              have hcd : c = d := scanClause_inl_eq hds
              have hd0 : d = [] := by rw [← hcd]; exact hce
              rcases List.mem_append.mp hdm with hcl | hln
              · have hent := hdb d (hclfix ▸ hcl) a ha
                rw [hd0] at hent
                exact absurd hent (by simp)
              · have hent := hlearned d hln a ha
                rw [hd0] at hent
                exact absurd hent (by simp)
          | inr w =>
              -- the unit arm: the scan-unit enqueue is
              -- unconditionally conflict-clear; recurse
              obtain ⟨l, r⟩ := w
              have hUnf : propagateLoop (fuel + 1) props st
                  = propagateLoop fuel props (enqueueNorm st l (some r)) := by
                simp [propagateLoop, hnone, hscan, Option.isSome_none]
              rw [hUnf] at hrep ⊢
              have hcs : scanClause st r.clause = some (.inr (l, r)) := by
                obtain ⟨c2, _, hcr, hcscan⟩ := scanAll_unit_reason hscan
                rw [hcr] at hcscan
                rw [hcr]
                exact hcscan
              have hnone2 : (enqueueNorm st l (some r)).conflict = none :=
                enqueueNorm_scanUnit_conflict_none hcs hnone
              exact ih (enqueueNorm st l (some r)) hnone2
                (enqueueNorm_coherent hcoh)
                (by rw [enqueueNorm_clauses]; exact hclfix)
                (by rw [enqueueNorm_learned]; exact hlearned) hrep

/-! ## The per-family fits-exclusion assembly

The `hfitexcl` premise of the two theorems above, discharged for the
ELEVEN registered families: each family's safety triple carries, as
its conflict bullet, that a reported conflict excludes every
assignment FITTING the state's domains and satisfying the family's
own constraint (`propX_safe.2.1`; `propLinLe_safe.2` for linLe).
A problem solution satisfies every problem constraint — in
particular the reporting propagator's own family constraint (the
registration premise `hprops`) — so the exclusion transfers. -/

/-- THE ELEVEN-FAMILY FITS-EXCLUSION: at every domain-coherent
    state, every conflict reported by a registered proved
    propagator excludes every assignment fitting the state's
    domains from the internal problem solutions. Mirrors
    `propagatorsOfProved_safeUniv`'s dispatch (the conflict bullet
    of each family's safety triple); the `neSlot` family's EMPTY
    conflict clause is covered by `propNe_safe.2.1` like any other.
    linLe participates under the equal-length gate `hlin` (its
    conflict bullet is fits-only, unlike its reason side). -/
theorem propagatorsOfProved_fitexcl
    {problem : Problem DomConstraint Unit}
    (hview : IntViewedDoms problem.domains)
    {props : List Propagator}
    (hprops : ∀ p ∈ props, ∃ dc ∈ problem.constraints,
      propagatorOfProved dc = some p)
    (hlin : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linLe coeffs is b → coeffs.length = is.length)
    (hlinE : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linEq coeffs is b → coeffs.length = is.length) :
    ∀ (st : State), DomainCoherent problem st →
      ∀ p ∈ props, ∀ c, p.run st = .conflict c →
        ∀ a, a.Fits st.domains →
          ¬ ProblemSolution problem DomConstraint.SatisfiedBy a := by
  intro st hcoh p hp c hrun a hfit ha
  obtain ⟨dc, hdc, hprop⟩ := hprops p hp
  rcases propagatorOfProved_run hprop hrun with
    ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, hdc2, hrun2⟩ |
    ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, k, hdc2, hrun2⟩ |
    ⟨coeffs, is, b2, hdc2, hrun2⟩ | ⟨i, c2, hdc2, hrun2⟩ |
    ⟨i, c2, hdc2, hrun2⟩ | ⟨i, c2, hdc2, hrun2⟩ |
    ⟨i, c2, hdc2, hrun2⟩ | ⟨i, v, hdc2, hrun2⟩ |
    ⟨ia, ja, hdca, hruna⟩ | ⟨ib, jb, kb, hdcb, hrunb⟩ |
    ⟨ic, jc, kc, hdcc, hrunc⟩ | ⟨id, jd, kd, hdcd, hrund⟩ |
    ⟨ie, je, ke, hdce, hrune⟩ | ⟨ig, kg, hdcg, hrung⟩ |
    ⟨lc, li, lb2, hdcl, hrunl⟩ | ⟨ti, tj, tk2, hdct, hrunt⟩ |
    ⟨ais, hdcai, hrunad⟩
  · rw [hdc2] at hdc
    exact (propLe_safe st i j).2.1 c hrun2 a hfit (ha.2 _ hdc)
  · rw [hdc2] at hdc
    exact (propLt_safe st i j).2.1 c hrun2 a hfit (ha.2 _ hdc)
  · rw [hdc2] at hdc
    have hviewst := intViewedDoms_of_coherent hview hcoh
    exact (propEq_safe st i j hviewst).2.1 c hrun2 a hfit (ha.2 _ hdc)
  · rw [hdc2] at hdc
    have hviewst := intViewedDoms_of_coherent hview hcoh
    exact (propNe_safe st i j hviewst).2.1 c hrun2 a hfit (ha.2 _ hdc)
  · rw [hdc2] at hdc
    exact (propPlus_safe st i j k).2.1 c hrun2 a hfit (ha.2 _ hdc)
  · rw [hdc2] at hdc
    have hlen : coeffs.length = is.length :=
      hlin _ hdc coeffs is b2 rfl
    exact (propLinLe2_safe st coeffs is b2 hlen).2.1 c hrun2 a hfit
      (ha.2 _ hdc)
  · rw [hdc2] at hdc
    exact (propLeConstHi_safe st i c2).2.1 c hrun2 a hfit (ha.2 _ hdc)
  · rw [hdc2] at hdc
    exact (propLeConstLo_safe st i c2).2.1 c hrun2 a hfit (ha.2 _ hdc)
  · rw [hdc2] at hdc
    exact (propLtConstHi_safe st i c2).2.1 c hrun2 a hfit (ha.2 _ hdc)
  · rw [hdc2] at hdc
    exact (propLtConstLo_safe st i c2).2.1 c hrun2 a hfit (ha.2 _ hdc)
  · rw [hdc2] at hdc
    exact (propConstEq_safe st i v).2.1 c hrun2 a hfit (ha.2 _ hdc)
  · rw [hdca] at hdc
    exact (propBoolNot_safe st ia ja).2.1 c hruna a hfit (ha.2 _ hdc)
  · rw [hdcb] at hdc
    exact (propBoolAnd_safe st ib jb kb).2.1 c hrunb a hfit (ha.2 _ hdc)
  · rw [hdcc] at hdc
    exact (propBoolOr_safe st ic jc kc).2.1 c hrunc a hfit (ha.2 _ hdc)
  · rw [hdcd] at hdc
    exact (propMin_safe st id jd kd).2.1 c hrund a hfit (ha.2 _ hdc)
  · rw [hdce] at hdc
    exact (propMax_safe st ie je ke).2.1 c hrune a hfit (ha.2 _ hdc)
  · rw [hdcg] at hdc
    exact (propAbs_safe st ig kg).2.1 c hrung a hfit (ha.2 _ hdc)
  · rw [hdcl] at hdc
    have hlenE : lc.length = li.length :=
      hlinE _ hdc lc li lb2 rfl
    exact (propLinEq2_safe st lc li lb2 hlenE).2.1 c hrunl a hfit
      (ha.2 _ hdc)
  · rw [hdct] at hdc
    exact (propTimes_safe st ti tj tk2).2.1 c hrunt a hfit
      (ha.2 _ hdc)
  · rw [hdcai] at hdc
    exact propAllDiffLCG_fitexcl hdc st hrunad a hfit ha

/-- The ten-family specialization under the front door's no-linLe
    registration premise (the shape `propagatorsOfProved_fallbackng`
    and `propagatorsOfProved_conflictEntitled` carry): linLe
    constraints may still be in the problem, but none of them
    registers a propagator in `props`, so the linLe dispatch arm is
    unreachable. This is the `hfitexcl` instance the composed front
    door below consumes. -/
theorem propagatorsOfProved_fitexcl_nolinle
    {problem : Problem DomConstraint Unit}
    (hview : IntViewedDoms problem.domains)
    {props : List Propagator}
    (hprops : ∀ p ∈ props, ∃ dc ∈ problem.constraints,
      propagatorOfProved dc = some p)
    (hlin : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linLe coeffs is b → coeffs.length = is.length)
    (hlinE : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linEq coeffs is b → coeffs.length = is.length) :
    ∀ (st : State), DomainCoherent problem st →
      ∀ p ∈ props, ∀ c, p.run st = .conflict c →
        ∀ a, a.Fits st.domains →
          ¬ ProblemSolution problem DomConstraint.SatisfiedBy a := by
  intro st hcoh p hp c hrun a hfit ha
  obtain ⟨dc, hdc, hprop⟩ := hprops p hp
  rcases propagatorOfProved_run hprop hrun with
    ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, hdc2, hrun2⟩ |
    ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, k, hdc2, hrun2⟩ |
    ⟨coeffs, is, b2, hdc2, hrun2⟩ | ⟨i, c2, hdc2, hrun2⟩ |
    ⟨i, c2, hdc2, hrun2⟩ | ⟨i, c2, hdc2, hrun2⟩ |
    ⟨i, c2, hdc2, hrun2⟩ | ⟨i, v, hdc2, hrun2⟩ |
    ⟨ia, ja, hdca, hruna⟩ | ⟨ib, jb, kb, hdcb, hrunb⟩ |
    ⟨ic, jc, kc, hdcc, hrunc⟩ | ⟨id, jd, kd, hdcd, hrund⟩ |
    ⟨ie, je, ke, hdce, hrune⟩ | ⟨ig, kg, hdcg, hrung⟩ |
    ⟨lc, li, lb2, hdcl, hrunl⟩ | ⟨ti, tj, tk2, hdct, hrunt⟩ |
    ⟨ais, hdcai, hrunad⟩
  · rw [hdc2] at hdc
    exact (propLe_safe st i j).2.1 c hrun2 a hfit (ha.2 _ hdc)
  · rw [hdc2] at hdc
    exact (propLt_safe st i j).2.1 c hrun2 a hfit (ha.2 _ hdc)
  · rw [hdc2] at hdc
    have hviewst := intViewedDoms_of_coherent hview hcoh
    exact (propEq_safe st i j hviewst).2.1 c hrun2 a hfit (ha.2 _ hdc)
  · rw [hdc2] at hdc
    have hviewst := intViewedDoms_of_coherent hview hcoh
    exact (propNe_safe st i j hviewst).2.1 c hrun2 a hfit (ha.2 _ hdc)
  · rw [hdc2] at hdc
    exact (propPlus_safe st i j k).2.1 c hrun2 a hfit (ha.2 _ hdc)
  · rw [hdc2] at hdc
    have hlenL : coeffs.length = is.length :=
      hlin _ hdc coeffs is b2 rfl
    exact (propLinLe2_safe st coeffs is b2 hlenL).2.1 c hrun2 a hfit
      (ha.2 _ hdc)
  · rw [hdc2] at hdc
    exact (propLeConstHi_safe st i c2).2.1 c hrun2 a hfit (ha.2 _ hdc)
  · rw [hdc2] at hdc
    exact (propLeConstLo_safe st i c2).2.1 c hrun2 a hfit (ha.2 _ hdc)
  · rw [hdc2] at hdc
    exact (propLtConstHi_safe st i c2).2.1 c hrun2 a hfit (ha.2 _ hdc)
  · rw [hdc2] at hdc
    exact (propLtConstLo_safe st i c2).2.1 c hrun2 a hfit (ha.2 _ hdc)
  · rw [hdc2] at hdc
    exact (propConstEq_safe st i v).2.1 c hrun2 a hfit (ha.2 _ hdc)
  · rw [hdca] at hdc
    exact (propBoolNot_safe st ia ja).2.1 c hruna a hfit (ha.2 _ hdc)
  · rw [hdcb] at hdc
    exact (propBoolAnd_safe st ib jb kb).2.1 c hrunb a hfit (ha.2 _ hdc)
  · rw [hdcc] at hdc
    exact (propBoolOr_safe st ic jc kc).2.1 c hrunc a hfit (ha.2 _ hdc)
  · rw [hdcd] at hdc
    exact (propMin_safe st id jd kd).2.1 c hrund a hfit (ha.2 _ hdc)
  · rw [hdce] at hdc
    exact (propMax_safe st ie je ke).2.1 c hrune a hfit (ha.2 _ hdc)
  · rw [hdcg] at hdc
    exact (propAbs_safe st ig kg).2.1 c hrung a hfit (ha.2 _ hdc)
  · rw [hdcl] at hdc
    have hlenE : lc.length = li.length :=
      hlinE _ hdc lc li lb2 rfl
    exact (propLinEq2_safe st lc li lb2 hlenE).2.1 c hrunl a hfit
      (ha.2 _ hdc)
  · rw [hdct] at hdc
    exact (propTimes_safe st ti tj tk2).2.1 c hrunt a hfit
      (ha.2 _ hdc)
  · rw [hdcai] at hdc
    exact propAllDiffLCG_fitexcl hdc st hrunad a hfit ha

/-! ## The composed front door

`propagatorsOfProved_fallbackng` (Fallback.lean) with its `hnoFit`
premise discharged: the one extra premise is the EMPTY-CONFLICT
observable `hconfempty` — the propagated conflict clause is `[]`
exactly when the fallback arm's analysis failed on an empty clause
(the propNe/ph3-ph4 shape). Under that observable the fits-exclusion
holds by `propagateLoop_conflict_nofit_empty`, with the per-family
`hfitexcl` from `propagatorsOfProved_fitexcl_nolinle`, the entry's
RunInv supplying coherence, clause fixity, and learned entitlement,
and the clause entitlement premise read through
`Clause.EntailedBy`'s unfolding. -/

/-- THE COMPOSED FRONT DOOR (the `hfallbackng` discharge under the
    empty-conflict gate): the exact premise list and conclusion of
    `propagatorsOfProved_fallbackng` (Fallback.lean), with `hnoFit`
    REPLACED by the observable `hconfempty` — at every entry whose
    propagation ends conflict-carrying with an unresolvable
    analysis, the propagated conflict clause is EMPTY. Under that
    gate the exclusion is `propagateLoop_conflict_nofit_empty`, so
    the fallback trail nogood is entailed at every internal problem
    solution.

    The residual (see the module header): `analyzeConflict = none`
    does NOT imply the empty conflict in general — nonempty clauses
    with all-below-level falsifiers, or with a decision pivot under
    remaining marks, also fail to analyze, and for those the
    fits-exclusion is FALSE (the scan-origin counterexample). An
    engine gate that only learns the fallback nogood when the
    conflict clause is empty — exactly the `neSlot`/propNe use case
    of PLAN §5 items 4–5 — discharges `hconfempty` by inspection. -/
theorem propagatorsOfProved_fallbackng'
    {problem : Problem DomConstraint Unit}
    (hview : IntViewedDoms problem.domains)
    {props : List Propagator}
    (hprops : ∀ p ∈ props, ∃ dc ∈ problem.constraints,
      propagatorOfProved dc = some p)
    (hlin : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linLe coeffs is b → coeffs.length = is.length)
    (hlinE : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linEq coeffs is b → coeffs.length = is.length)
    (hreason : ReasonSafeUniv problem DomConstraint.SatisfiedBy props)
    (hjust : ∀ (acc : State), DomainCoherent problem acc →
      acc.decisionLevel = 0 →
      RootFacts problem DomConstraint.SatisfiedBy acc.trail →
      (∀ e ∈ acc.trail, e.level ≤ acc.decisionLevel) →
      ∀ p ∈ props, ∀ l r, p.run acc = .implied l r →
        ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
          l.norm.eval a = some true)
    (hdb : ∀ c ∈ problem.clauses,
      Clause.EntailedBy problem DomConstraint.SatisfiedBy c)
    (hagrees : ∀ (c : DomConstraint) (a : Assignment),
      DomConstraint.satisfiedB c a = true ↔ c.SatisfiedBy a)
    (hconfempty : ∀ (st : State), st.conflict = none →
      RunInv problem DomConstraint.SatisfiedBy props st →
      TrailDistinct st.trail →
      (propagateLoop (engineFuel st) props st).conflict.isSome = true →
      analyzeConflict (propagateLoop (engineFuel st) props st) = none →
      (propagateLoop (engineFuel st) props st).conflict = some []) :
    ∀ (st : State), st.conflict = none →
      RunInv problem DomConstraint.SatisfiedBy props st →
      TrailDistinct st.trail →
      trailBoolPinsOk problem
        (propagateLoop (engineFuel st) props st).trail = true →
      (propagateLoop (engineFuel st) props st).conflict.isSome = true →
      analyzeConflict (propagateLoop (engineFuel st) props st) = none →
      Clause.EntailedBy problem DomConstraint.SatisfiedBy
        (List.map (fun e => e.literal.negate.norm)
          (List.filter (fun e => decide (e.level > 0))
            (propagateLoop (engineFuel st) props st).trail)) := by
  intro st hnone hinv hdist hgate hconf hanone
  have hempty := hconfempty st hnone hinv hdist hconf hanone
  have hnoFit : ∀ (st2 : State), st2.conflict = none →
      RunInv problem DomConstraint.SatisfiedBy props st2 →
      (propagateLoop (engineFuel st2) props st2).conflict = some [] →
      (∀ a, a.Fits (propagateLoop (engineFuel st2) props st2).domains →
        ¬ ProblemSolution problem DomConstraint.SatisfiedBy a) := by
    intro st2 hnone2 hinv2 hempty2
    exact propagateLoop_conflict_nofit_empty
      (propagatorsOfProved_fitexcl_nolinle hview hprops hlin hlinE) hdb
      (engineFuel st2) st2 hnone2 hinv2.coherent hinv2.clausesFixed
      (fun c hc a ha => hinv2.learnedEntailed c hc a ha) hempty2
  exact propagatorsOfProved_fallbackng hview hprops hreason hjust hdb
    hagrees hnoFit st hnone hinv hdist hgate hempty

/-- **THE DISCHARGED FALLBACK FRONT DOOR** (PLAN §5 items 4–5): the
    master theorem's `hfallbackng` premise over the proved-propagator
    registration, with `hnoFit` derived from the empty-conflict
    exclusion (`propagateLoop_conflict_nofit_empty` + the eleven-→
    ten-family fits-exclusion assembly). This is the exact premise
    shape `go_unsat_entry_invariant` consumes: conflict-free RunInv
    entry + pins gate + the EMPTY conflict clause at the propagated
    state — no `isSome`/`analyzeConflict` observables needed, since
    the engine's match arm itself supplies the emptiness. -/
theorem propagatorsOfProved_fallbackng_discharged
    {problem : Problem DomConstraint Unit}
    (hview : IntViewedDoms problem.domains)
    {props : List Propagator}
    (hprops : ∀ p ∈ props, ∃ dc ∈ problem.constraints,
      propagatorOfProved dc = some p)
    (hlin : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linLe coeffs is b → coeffs.length = is.length)
    (hlinE : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linEq coeffs is b → coeffs.length = is.length)
    (hreason : ReasonSafeUniv problem DomConstraint.SatisfiedBy props)
    (hjust : ∀ (acc : State), DomainCoherent problem acc →
      acc.decisionLevel = 0 →
      RootFacts problem DomConstraint.SatisfiedBy acc.trail →
      (∀ e ∈ acc.trail, e.level ≤ acc.decisionLevel) →
      ∀ p ∈ props, ∀ l r, p.run acc = .implied l r →
        ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
          l.norm.eval a = some true)
    (hdb : ∀ c ∈ problem.clauses,
      Clause.EntailedBy problem DomConstraint.SatisfiedBy c) :
    ∀ (st : State), st.conflict = none →
      RunInv problem DomConstraint.SatisfiedBy props st →
      TrailDistinct st.trail →
      trailBoolPinsOk problem
        (propagateLoop (engineFuel st) props st).trail = true →
      (propagateLoop (engineFuel st) props st).conflict = some [] →
      Clause.EntailedBy problem DomConstraint.SatisfiedBy
        (List.map (fun e => e.literal.negate.norm)
          (List.filter (fun e => decide (e.level > 0))
            (propagateLoop (engineFuel st) props st).trail)) := by
  intro st hnone hinv hdist hgate hempty
  -- the fits-exclusion at the propagated state, from the empty
  -- conflict's origin
  have hnoFit : ∀ a, a.Fits (propagateLoop (engineFuel st)
      props st).domains →
    ¬ ProblemSolution problem DomConstraint.SatisfiedBy a :=
    propagateLoop_conflict_nofit_empty
      (propagatorsOfProved_fitexcl_nolinle hview hprops hlin hlinE) hdb
      (engineFuel st) st hnone hinv.coherent hinv.clausesFixed
      (fun c hc a ha => hinv.learnedEntailed c hc a ha) hempty
  exact propagatorsOfProved_fallbackng hview hprops hreason hjust hdb
    (fun c a => DomConstraint.satisfiedB_iff c a)
    (fun st2 hnone2 hinv2 hempty2 => by
      -- the per-state restatement: hnoFit at the queried state
      exact propagateLoop_conflict_nofit_empty
        (propagatorsOfProved_fitexcl_nolinle hview hprops hlin hlinE) hdb
        (engineFuel st2) st2 hnone2 hinv2.coherent
        hinv2.clausesFixed
        (fun c hc a ha => hinv2.learnedEntailed c hc a ha) hempty2)
    st hnone hinv hdist hgate hempty

#print axioms LeanFzn.Solver.Propagation.propagatorsOfProved_fallbackng_discharged

end LeanFzn.Solver.Propagation

/-
File: LeanFzn/Solver/Propagation/Proofs/Fallback.lean

Purpose:
  The chronological-fallback nogood entitlement (PLAN.md §5 items
  4–5, proof half). When conflict analysis cannot resolve
  (`analyzeConflict st1 = none`), the engine's fallback arm LEARNS
  THE TRAIL NOGOOD before retreating —

    (st1.trail.filter fun e => e.level > 0).map
      fun e => e.literal.negate.norm

  — the negations of the conflicted state's positive-level trail
  literals (LeanFzn/Solver/UIP/Engine.lean, the `| none =>` arm of
  `match analyzeConflict st1`; gated on `trailBoolPinsOk`, the same
  executable gate as the leaf nogood below it in the same match).

  The entitlement mirrors the leaf nogood (`leafNogood_entailed`,
  Proofs/Reason.lean): every internal problem solution either

  * falsifies some POSITIVE-level trail literal — its negated,
    normalized form is IN the learned clause and TRUE there
    (`fold_fits_or_falsifies` walks the trail; `RootFacts` rules out
    the level-0 case); or

  * fits the conflicted state's domains — and the conflict excludes
    exactly that: NO fitting assignment is an internal solution
    (the `hexcl` premise).

  The leaf premises (`hsingle`/`ha`/`hfail` — the failed leaf test)
  are replaced by the conflict-domain exclusion `hexcl`. The
  front-door assembly (`propagatorsOfProved_fallbackng`, mirroring
  `propagatorsOfProved_leafng`) carries `hexcl` as its one new
  premise — `hnoFit`, stated over the same entry shape as the master
  theorem's `hfallbackng` premise (`go_unsat_entry_invariant`,
  Proofs/Run.lean: the conflict-free / RunInv / TrailDistinct /
  pins-gate / conflict-carrying / analysis-none chain) — because the
  exclusion is a property of the conflict's ORIGIN (a propagator's
  fits-only conflict exclusion, a scan clause's trail falsification,
  or the opposing-pair decidedness); see the remaining-obligation
  note at the bottom.

Dependencies:
  - LeanFzn.Solver.Propagation.Proofs.Reason (`fold_fits_or_falsifies`,
    `TrailBoolPins`, `trailBoolPinsOk_iff`, the leaf-nogood mirror
    this file parallels)
  - transitively Run (`RunInv`, `propagateLoop_runInv`,
    `TrailDistinct`), Theory (`engineFuel`), Propagators /
    ConstFamilies (the family assemblies whose premise shapes the
    front door mirrors).

DAG:
  Propagate + Theory + ConstFamilies + Run -> Reason -> Fallback
  (a sibling of Reason's front-door assemblies; imports only Reason)
-/

import LeanFzn.Solver.Propagation.Proofs.Reason
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Reference


open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Reference

/-! ## THE FALLBACK NOGOOD ENTITLEMENT (PLAN §5 items 4–5)

On a domain-coherent state whose conflict excludes every FITTING
assignment from the internal solutions, the clause the engine's
chronological-fallback arm learns is entailed at every internal
problem solution. This is `leafNogood_entailed` (Reason.lean) with
the failed-leaf-test premise replaced by the conflict's
domain-exclusion: the leaf's "a fits the domains, hence EQUALS the
failed assignment `a0`" contradiction becomes "a fits the domains,
contradicting the exclusion". The proof skeleton is unchanged:

  1. `fold_fits_or_falsifies` — walking the state's own trail from
     the problem's domains, any solution either falsifies some trail
     entry or fits the fully folded domains;
  2. a falsified entry at level 0 is impossible (`RootFacts`); at a
     positive level its negated, normalized form is IN the learned
     clause and TRUE there (`Literal.norm_eval` +
     `Literal.eval_negate`);
  3. a fitting assignment contradicts `hexcl`. -/

/-- THE FALLBACK NOGOOD ENTITLEMENT (PLAN §5 items 4–5). At a
    domain-coherent state whose conflict excludes every fitting
    assignment from the internal solutions, the clause the engine's
    chronological-fallback arm learns —

      (st.trail.filter fun e => e.level > 0).map
        fun e => e.literal.negate.norm

    — is entailed at every internal problem solution: every solution
    either falsifies some positive-level trail literal (whose negated,
    normalized form is IN the clause and TRUE there), or fits the
    state's domains — excluded by the conflict.

    Premises (beyond the engine-observed conflict): `hcoh`
    (RunInv.coherent at the propagated state), `hexcl` (the
    conflict's domain-exclusion — the replacement for the leaf
    failure; see the module header), `hroot` (RunInv.rootFacts), and
    `hboolpins` (the documented leaf premise, equally necessary
    here; vacuous when the trail carries no Boolean pins — see
    `LeanFzn/Solver/UIP/Proofs/Obstructions.lean`
    (`boolPins_premise_necessary`) for the machine-checked
    counterexample). `hagrees` is carried for signature symmetry
    with the leaf statements; this proof does not consume it. -/
theorem fallbackNogood_entailed
    {problem : Problem DomConstraint Unit}
    {constraintHoldsB : DomConstraint → Assignment → Bool}
    (hagrees : ∀ (c : DomConstraint) (a : Assignment),
      constraintHoldsB c a = true ↔ c.SatisfiedBy a)
    (st : State)
    (hcoh : DomainCoherent problem st)
    (hexcl : ∀ a, a.Fits st.domains →
      ¬ ProblemSolution problem DomConstraint.SatisfiedBy a)
    (hroot : RootFacts problem DomConstraint.SatisfiedBy st.trail)
    (hboolpins : TrailBoolPins problem.domains st.trail) :
    ∀ (a : Assignment), ProblemSolution problem DomConstraint.SatisfiedBy a →
      ∃ l ∈ (st.trail.filter fun e => e.level > 0).map
        (fun e => e.literal.negate.norm), l.eval a = some true := by
  intro a ha2
  obtain ⟨hafit, hacs⟩ := ha2
  -- (1) the fold divergence over the state's own trail
  have hsol : ProblemSolution problem DomConstraint.SatisfiedBy a :=
    ⟨hafit, hacs⟩
  rcases fold_fits_or_falsifies (D := problem.domains) hafit st.trail
      problem.domains hboolpins hafit with
    ⟨e, hemem, hevfalse⟩ | hfits
  · -- (2) a falsifying entry: level 0 is impossible (RootFacts),
    -- level > 0 gives the fallbackNg witness
    rcases Nat.lt_or_ge e.level 1 with hzero | hpos
    · exfalso
      have hlev0 : e.level = 0 := by omega
      have htrue := hroot e hemem hlev0 a hsol
      rw [hevfalse] at htrue
      simp at htrue
    · refine ⟨e.literal.negate.norm, ?_, ?_⟩
      · exact List.mem_map_of_mem
          (List.mem_filter.mpr ⟨hemem, decide_eq_true hpos⟩)
      · rw [Literal.norm_eval, Literal.eval_negate, hevfalse]
        rfl
  · -- (3) a fits st.domains: the conflict's domain-exclusion
    -- contradicts a's solutionhood
    exfalso
    have hcoheq : st.domains = st.trail.foldl
        (fun acc e => domOfLit acc e.literal) problem.domains := hcoh
    have hfitst : a.Fits st.domains := by
      rw [hcoheq]
      exact hfits
    exact hexcl a hfitst hsol

/-! ## The packaging at the coordinator's insertion shape

The engine's fallback arm observes the POST-PROPAGATION state `st1`
(a conflict-carrying state whose analysis returned `none`); the
entitlement is consumed there with the state's own coherence
(RunInv.coherent at the entry, preserved through `propagateLoop`)
and root facts (RunInv's own field, likewise preserved). This
corollary packages the exact statement the coordinator's insertion
obligation for the fallback nogood needs: the learned clause is
`EntailedBy` (true at every internal solution). -/

/-- The fallback nogood, packaged as clause entailment (the
    `RunInv.learnedEntailed` shape for the coordinator's insertion
    obligation — the mirror of `leafNogood_entailed_by`). -/
theorem fallbackNogood_entailed_by
    {problem : Problem DomConstraint Unit}
    {constraintHoldsB : DomConstraint → Assignment → Bool}
    (hagrees : ∀ (c : DomConstraint) (a : Assignment),
      constraintHoldsB c a = true ↔ c.SatisfiedBy a)
    (st : State)
    (hcoh : DomainCoherent problem st)
    (hexcl : ∀ a, a.Fits st.domains →
      ¬ ProblemSolution problem DomConstraint.SatisfiedBy a)
    (hroot : RootFacts problem DomConstraint.SatisfiedBy st.trail)
    (hboolpins : TrailBoolPins problem.domains st.trail) :
    Clause.EntailedBy problem DomConstraint.SatisfiedBy
      ((st.trail.filter fun e => e.level > 0).map
        (fun e => e.literal.negate.norm)) := by
  intro a hsa
  obtain ⟨l, hl, hev⟩ :=
    fallbackNogood_entailed hagrees st hcoh hexcl hroot hboolpins a hsa
  exact ⟨l, hl, hev⟩

/-! ### The master-theorem `hfallbackng` premise's front-door assembly

Mirrors `propagatorsOfProved_leafng` (Reason.lean): at a
conflict-free run-invariant entry, when the executable pins gate
passes, the chronological fallback's trail nogood is entailed — via
`fallbackNogood_entailed_by` at the propagated state, whose
coherence and root facts come from the run invariant
(`propagateLoop_runInv`). The ONE new premise is `hnoFit` — the
conflict's domain-exclusion, stated at exactly the `hfallbackng`
premise's own entry shape (the same conflict-free / RunInv /
TrailDistinct / pins-gate / conflict-carrying / analysis-none
chain; only the pins-gate conjunct is dropped from the antecedent
since the gate feeds the conclusion, not the exclusion). Its own
discharge is the remaining front-door obligation (see the note
below). -/

/-- THE hfallbackng FRONT-DOOR ASSEMBLY: at a conflict-free
    run-invariant entry with a distinct trail, when the executable
    pins gate passes and the propagation ends conflict-carrying with
    an unresolvable analysis, the fallback trail nogood is entailed
    (via `fallbackNogood_entailed_by` at the propagated state, with
    `hnoFit` supplying the conflict's domain-exclusion there). The
    conclusion is stated exactly as the master theorem's
    `hfallbackng` premise (`go_unsat_entry_invariant`,
    Proofs/Run.lean) so the coordinator can plug it in directly. -/
theorem propagatorsOfProved_fallbackng
    {problem : Problem DomConstraint Unit}
    (hview : IntViewedDoms problem.domains)
    {props : List Propagator}
    (hprops : ∀ p ∈ props, ∃ dc ∈ problem.constraints,
      propagatorOfProved dc = some p)
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
    (hnoFit : ∀ (st : State), st.conflict = none →
      RunInv problem DomConstraint.SatisfiedBy props st →
      (propagateLoop (engineFuel st) props st).conflict = some [] →
      (∀ a, a.Fits (propagateLoop (engineFuel st) props st).domains →
        ¬ ProblemSolution problem DomConstraint.SatisfiedBy a)) :
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
  -- the propagated state's run invariant (coherence + root facts)
  have hinv1 := propagateLoop_runInv hreason hjust hdb
    (engineFuel st) st hnone hinv
  exact fallbackNogood_entailed_by hagrees
    (propagateLoop (engineFuel st) props st) hinv1.coherent
    (hnoFit st hnone hinv hempty) hinv1.rootFacts
    (trailBoolPinsOk_iff hgate)

/-! ### Remaining front-door obligation: the `hnoFit` discharge

`propagateLoop_conflict_nofit` — at a conflict-free RunInv entry
whose propagation ends conflict-carrying with an unresolvable
analysis, no assignment fitting the propagated domains is an
internal solution — is NOT proven here, and `hnoFit` is therefore
an explicit premise of the assembly above (no `sorry`, no
weakening). Honest status of the obstruction:

* The abstract layer does NOT imply it. `CoherentSafeUniv`'s
  `conflictExcludes` is vacuous for the EMPTY conflict clause
  (`¬ [].SatisfiedBy a` is a truth), and the neSlot family reports
  exactly `.conflict []` on disjoint domains; meanwhile
  `propagateLoop_solvedBy_any` keeps every internal solution
  REPRESENTED — hence FITTING the propagated domains — along runs
  from a solved-by entry. An always-`.conflict []` propagator
  satisfies the abstract contract while breaking the exclusion.

* The per-family fits-only conflict exclusions (the
  `propX_safe.2.1` shape: `∀ c, propX = .conflict c → ∀ a,
  a.Fits st.domains a → constraint.SatisfiedBy a → False`) DO give
  the propagator arm — but consuming them needs a new
  conflict-origin lemma (the propagation loop freezes the state at
  the first conflict, so the propagated state's domains ARE the
  conflict-reporting state's) threaded through a loop induction,
  plus the scan-arm slot-exclusion argument (a fitting solution
  cannot resurrect a value a trail entry filtered away — the
  same mixed-domain combinatorics `TrailBoolPins` gates) and the
  opposing-pair arm's decidedness analysis.

That machinery is future work; until it lands, the wide front door
carries `hnoFit` (the master theorem's `hfallbackng` premise is
discharged by `propagatorsOfProved_fallbackng` modulo exactly this
one fact). -/

#print axioms LeanFzn.Solver.Propagation.fallbackNogood_entailed
#print axioms LeanFzn.Solver.Propagation.fallbackNogood_entailed_by
#print axioms LeanFzn.Solver.Propagation.propagatorsOfProved_fallbackng

end LeanFzn.Solver.Propagation

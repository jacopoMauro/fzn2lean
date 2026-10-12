/-
Purpose: assemble the canonical consume invariant from predecessor facts.
Dependencies: PendingRun supplies branch coherence and pending backing;
SchedulerInvariant and SchedulerResume supply the fields and coverage transfer.
Position: independent consume adapter for the supported invariant integration.
No successor invariant is assumed. Log/coverage/deadness producers remain explicit.
-/
import LeanFzn.Solver.UIP.Proofs.PendingRun
import LeanFzn.Solver.UIP.Proofs.SchedulerInvariant
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-- Canonical consume needs only predecessor log/coverage, pending backing,
branch coherence and actual exhausted-frame evidence. -/
theorem stepConsume_invariant_of_components {leaf : Assignment → Bool}
    {cfg next : SchedulerConfig leaf} {f : BranchFrame} {rest : List BranchFrame}
    (hp : cfg.pending = f :: rest) (hs : stepConsume cfg = some next)
    (hbr : ReachableState leaf cfg.orig cfg.branch)
    (hpend : PendingSideInv cfg.orig cfg)
    (hlog : ExhaustionLog.Sound leaf cfg.log)
    (hcov : cfg.coverage)
    (hdead : ∀ a, leaf a = true → FrameCovers cfg.branch.frame a →
      (∃ r ∈ cfg.log.regions, r.mem a = true) ∨
      (∃ c ∈ cfg.branch.learned, ¬ c.SatisfiedBy a)) :
    SchedulerInvariant next := by
  have hr := stepConsume_reachable_of_inv hp hs hbr hpend rfl
  have hi := hpend.stepConsume hp hs
  obtain ⟨hf, hps, hl, hlearn, hstatus⟩ := stepConsume_some_shape hp hs
  have ho : next.orig = cfg.orig := by
    unfold stepConsume at hs
    rw [hp] at hs
    simp only [Option.some.injEq] at hs
    subst next
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [ho] using hr
  · unfold stepConsume at hs
    rw [hp] at hs
    simp only [Option.some.injEq] at hs
    subst next
    simp
  · intro g hg i v hv
    simpa [ho] using (hi.pending g hg).fit i v hv
  · intro i v hv
    simpa [ho] using hr.full_fits i v hv
  · simpa [hl] using hlog
  · intro a ha
    have ha0 : OriginalLeaves leaf cfg.orig a := by simpa [ho] using ha
    rcases hcov a ha0 with hfront | hcl
    · rcases stepConsume_coverage hp hs hdead a ha.1 hfront with hfr | hreg | hcl
      · exact Or.inl hfr
      · obtain ⟨r, hrmem, hrval⟩ := hreg
        exact False.elim (hlog r (by simpa [hl] using hrmem) a ha.1 hrval)
      · exact Or.inr hcl
    · exact Or.inr (by simpa [hlearn] using hcl)
  · intro c hc c' hc' a ha
    have he : c' = c := by simpa using hc'
    subst c'
    exact hr.wf.2.2.2.2 c hc a ha
end LeanFzn.Solver.UIP

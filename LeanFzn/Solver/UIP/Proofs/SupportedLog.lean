/-
Purpose: isolate exhaustion-log registration obligations on one supported run.
Dependencies: SupportedRun fixes initialization and actual transitions;
BackjumpFrontier supplies region soundness. Consumers are consume/invariant
integration. The remaining hypothesis concerns newly inserted regions only,
not log soundness or invariant preservation as a conclusion.
-/
import LeanFzn.Solver.UIP.Proofs.SupportedRun
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-- Per-registration residual. An unchanged log needs no evidence. Producers
must inspect real local-exclusion/fallback/checkpoint-rejection registrations. -/
def SupportedNewRegionsSound (orig : List Domain) (original : List Clause)
    (props : List Propagator) (leaf : Assignment → Bool) : Prop :=
  ∀ {cfg cfg' : SchedulerConfig leaf}, SupportedReach orig original props cfg →
    (schedulerNext cfg).successor = some cfg' →
    ∀ r ∈ cfg'.log.regions, r ∉ cfg.log.regions → DeadRegion.Sound leaf r

/-- The run induction is complete; only newly registered regions remain. -/
theorem supportedLogSound_of_newRegions {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (hnew : SupportedNewRegionsSound orig original props leaf) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ExhaustionLog.Sound leaf cfg.log := by
  intro cfg hreach
  induction hreach with
  | init =>
      intro r hr
      simp [SchedulerConfig.init] at hr
  | @step before after hpre hs ih =>
      intro r hr
      by_cases hold : r ∈ before.log.regions
      · exact ih r hold
      · exact hnew hpre hs r hr hold

/-- Unchanged-region transitions discharge their registration obligation
without a semantic argument (propagate/decide/analyze/jump/consume sites). -/
theorem newRegionsSound_of_regions_eq {leaf : Assignment → Bool}
    {before after : ExhaustionLog} (heq : after.regions = before.regions) :
    ∀ r ∈ after.regions, r ∉ before.regions → DeadRegion.Sound leaf r := by
  intro r hr hn
  exact False.elim (hn (heq ▸ hr))

/-- A single registration reduces exactly to the inserted region's soundness. -/
theorem newRegionsSound_of_register {leaf : Assignment → Bool}
    {before after : ExhaustionLog} {r : DeadRegion}
    (heq : after = before.register r) (hr : DeadRegion.Sound leaf r) :
    ∀ q ∈ after.regions, q ∉ before.regions → DeadRegion.Sound leaf q := by
  subst after
  intro q hq hn
  rcases List.mem_cons.mp hq with hqr | hold
  · subst q
    exact hr
  · exact False.elim (hn hold)

end LeanFzn.Solver.UIP

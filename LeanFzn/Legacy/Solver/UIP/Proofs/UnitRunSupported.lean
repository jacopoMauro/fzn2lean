/-
File: LeanFzn/Solver/UIP/Proofs/UnitRunSupported.lean

Purpose (R1c): the normalized-unit run invariant (N1) along a SUPPORTED run,
under the explicit unit-kit gate that conflict routing makes necessary.

Conflict routing adds three conflict sources to the closure: a falsified
stored clause, a filter-rejected implied literal, and a WIPE-OUT conflict at a
frame with an emptied domain. The first two stay normalized units under the
unit profile and a unit-learned database; the wipe-out clause is the list of
the negated removers of every original value of the emptied slot, which is
in general NOT a unit. Likewise the seeded original clauses are the root
scanned database. The unit-run invariant therefore needs exactly two extra
inputs, bundled here: the original clauses are normalized units, and the run
never reports a wipe-out conflict.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerConflict
import LeanFzn.Legacy.Solver.UIP.Proofs.SupportedRun
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation

/-- THE UNIT-KIT GATE (R1c): the original clauses are normalized units and no
configuration of the supported run reports a wipe-out conflict. -/
structure UnitKitGate {leaf : Assignment → Bool} (orig : List Domain)
    (original : List Clause) (props : List Propagator) : Prop where
  /-- the seeded root database is unit-learned -/
  unit_original : UnitLearned original
  /-- no wipe-out clause is ever buildable along the run -/
  no_wipe : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
    wipeoutClause cfg.orig cfg.branch.trail cfg.branch.frame = none

/-- **N1 ALONG A SUPPORTED RUN**: under the gate every supported
configuration satisfies the unit-run invariant. Replaces the
reachability-indexed `unitRunInvariant_of_reachable` at the supported
consumers (restated by R1c: the extra input is the gate). -/
theorem unitRunInvariant_of_supported {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {dcs : List DomConstraint}
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hgate : UnitKitGate (leaf := leaf) orig original props) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      UnitRunInvariant cfg := by
  intro cfg h
  induction h with
  | init hent =>
      refine ⟨hgate.unit_original, ?_⟩
      intro ev hev
      cases hev
  | @step cfg cfg' hr hs ih =>
      have hpropsOld : cfg.props = dcs.filterMap propagatorOfProved := by
        rw [(SupportedReach.triple_eq hr).2.2, hprops]
      exact unitRunInvariant_step hpropsOld hSupp ih hr.reachable
        (hgate.no_wipe hr) hs

end LeanFzn.Solver.UIP

/-
File: LeanFzn/Solver/UIP/Proofs/LcgRunInvariantGate.lean
U1c: `runSemContract_of_families` / `lcgKit_gate_of_families` WITHOUT the along-run premises
`FrameExplainedFull` and `TrailSnapFixed`, for integer boxes.
-/
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantStep
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantSnap
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP.LcgClamp
open LeanFzn.Solver.UIP.ClampPool LeanFzn.Solver.UIP

namespace LeanFzn.Solver.UIP.LcgRunInv

variable {leaf : Assignment → Bool}

/-- **`RunSemContract` for the clamped family kit on an integer box**: the only premises are
the compiled-problem facts (int box, typed emissions, aligned original clauses) and the branch
reachability `hbr`; the along-run frame/trail premises are theorems. 
VACUOUS on non-unit LCG instances (hbr_refuted); use *_of_kit (LcgKitFinal). -/
theorem runSemContract_intBox {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (hraw : raw = dcs.filterMap propagatorOfProved)
    (hprops : props = clampProps orig raw)
    (hfam : ∀ dc ∈ dcs, lcgFamB dc = true)
    (hint : AllIntBox orig) (hnd : ∀ d ∈ orig, d.Nodup)
    (htyped : ClampPool.EmissionTyped orig raw)
    (horig : DatabaseAligned orig original)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch) :
    RunSemContract orig original props leaf :=
  runSemContract_of_families (dcs := dcs) (by rw [hprops, hraw]) hfam
    (frameExplainedFull_of_supportedRun hint hnd (shape_of_allInt hint) hbr)
    (trailSnapFixed_of_clampedRun hprops htyped horig hbr (shape_of_allInt hint))

/-- The `lcgKit` gate on an integer box without the along-run premises. 
VACUOUS on non-unit LCG instances (hbr_refuted); use *_of_kit (LcgKitFinal). -/
theorem lcgKit_gate_intBox {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (hraw : raw = dcs.filterMap propagatorOfProved)
    (hprops : props = clampProps orig raw)
    (hfam : ∀ dc ∈ dcs, lcgFamB dc = true)
    (hint : AllIntBox orig) (hnd : ∀ d ∈ orig, d.Nodup)
    (htyped : ClampPool.EmissionTyped orig raw)
    (horig : DatabaseAligned orig original)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch) :
    (lcgKit lcgFamB).Gate leaf orig original props :=
  lcgKit_gate_of_families (dcs := dcs) (by rw [hprops, hraw]) hfam
    (frameExplainedFull_of_supportedRun hint hnd (shape_of_allInt hint) hbr)
    (trailSnapFixed_of_clampedRun hprops htyped horig hbr (shape_of_allInt hint))

end LeanFzn.Solver.UIP.LcgRunInv

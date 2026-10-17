import LeanFzn.Solver.UIP.Proofs.ClampPool
import LeanFzn.Solver.UIP.Proofs.ExtendedPoolProducers
import LeanFzn.Solver.UIP.Proofs.SupportedCertifiedRun

/-!
# U1e: pool alignment along clamped runs, and the sorted chain without the alignment premise

With the registered propagators clamped (`clampProps orig raw`), every literal a
propagator emits is pooled (`ClampPool.emissionPoolAt_clampProps`), so the
database alignment `halignDB` is a THEOREM along supported runs
(`halignDB_of_clampedRun`, through the pool-parametric joint invariant
`trailInvWith_of_supportedRun`), and the sorted-progress premise bundle needs no
alignment field (`ClampedPhasePremises`).
-/

namespace LeanFzn.Solver.UIP.ClampedRun
open LeanFzn LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
  LeanFzn.Solver.UIP LeanFzn.Solver.UIP.ClampPool

/-- **`halignDB` ALONG A CLAMPED RUN (theorem, not a premise).** -/
theorem halignDB_of_clampedRun {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {raw props : List Propagator}
    (hprops : props = clampProps orig raw)
    (htyped : EmissionTyped orig raw)
    (horig : DatabaseAligned orig original)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hshape : ShapeTypedDomains orig) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ∀ c ∈ cfg.branch.learned, ∀ q ∈ c, q.norm ∈ litPool orig := by
  intro cfg hreach
  have hv : EmissionPoolAt (litPoolWith [] orig) props := by
    rw [litPoolWith_nil, hprops]; exact emissionPoolAt_clampProps htyped
  have h := (trailInvWith_of_supportedRun (extra := []) hv
    (by rw [litPoolWith_nil]; exact horig) hbr hshape hreach).db
  rwa [litPoolWith_nil] at h

/-- The sorted-progress premise bundle for a clamped run: NO alignment field.
Jump novelty holds by construction (the runtime repeat guard). -/
structure ClampedPhasePremises (orig : List Domain) (original : List Clause)
    (raw : List Propagator) (leaf : Assignment → Bool) : Prop where
  typed : EmissionTyped orig raw
  horig : DatabaseAligned orig original
  hshape : ShapeTypedDomains orig
  hbr : ∀ {cfg : SchedulerConfig leaf},
    SupportedReach orig original (clampProps orig raw) cfg →
    ReachableState leaf orig cfg.branch

/-- Forget to the classical bundle: the alignment field is DERIVED. -/
theorem ClampedPhasePremises.toPremises {orig : List Domain} {original : List Clause}
    {raw : List Propagator} {leaf : Assignment → Bool}
    (P : ClampedPhasePremises orig original raw leaf) :
    SupportedPhasePremises orig original (clampProps orig raw) leaf where
  halignDB := halignDB_of_clampedRun rfl P.typed P.horig P.hbr P.hshape
  hbr := P.hbr

/-- The sorted supported kernel of a clamped run. -/
def clampedPhaseKernelOf {orig : List Domain} {original : List Clause}
    {raw : List Propagator} {leaf : Assignment → Bool}
    (P : ClampedPhasePremises orig original raw leaf) :
    SupportedPhaseKernel orig original (clampProps orig raw) leaf :=
  supportedPhaseKernelOf P.toPremises

end LeanFzn.Solver.UIP.ClampedRun

/-
File: LeanFzn/Integration/Optimization/KernelSeedConfig.lean

Purpose (PLAN F4, seeded branch-and-bound with the F2/F3 policy surface):
the CLI-ready seeded entry.  `lcgSeedSolver` runs the certified LCG kernel
with the previous round's learned database; this module adds the two policy
arguments the F2/F3 linear driver already honours:

  * the slot-selection priority vector (`annotPrioOpts` for `--var=annot`,
    `heurPrio` for the legacy `--var=obj`), and
  * the conflict activity-bump toggle (`--heur-act`, disabled for
    `--var=annot` exactly as in `solveSearchConfigWith`);
  * the static value presentations (`--val=annot|min|max|median`, and
    `--val=act`'s activity order) by running the whole seeded loop on
    `annotDomains p (configOrders p o none)`.  This is a pure re-ordering of
    the box, so `PresentationPerm` transfers the pool alignment and the
    assignment set back to the compiled box.

`--val=incumbent` is the one documented gap: the presentation depends on the
previous round's incumbent, while the seeded driver keeps one fixed box.  The
seeded entry therefore uses the first-round (activity) presentation for it;
see `docs/F4-seeded-adapter.md`.

Claim discipline (PLAN §2.1): every emitted solution comes from a certified
SAT result of the current bounded problem (`optimizeStreamSeedConfig_eq` and
`optimizeSeedConfig_solution_sound`); `run.complete = true` means the strict
improving bound of the last printed solution was certified infeasible
(`optimizeSeedConfig_optimal`); a run with no incumbent proves the model has
no parameter-honest solution (`optimizeSeedConfig_unsat`).  A budget-exhausted
run is the caller's responsibility and makes no completeness claim; this
module's pure and streaming runners have no budget and always return a
complete or explicitly failed run.

DAG: LcgSeed + PresentationPerm + SearchConfig -> this file -> CLI adapter.
NO `sorry`, NO custom axiom.
-/
import LeanFzn.Legacy.Integration.Optimization.KernelSeed
import LeanFzn.Legacy.Integration.Presentation.Perm
import LeanFzn.Legacy.Integration.SearchConfig

namespace LeanFzn.Integration
open LeanFzn.Semantics LeanFzn.Semantics.Globals LeanFzn.Semantics.Evaluation LeanFzn.Compiler LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP


private theorem est_bind_assoc {ε σ α β γ : Type} (x : EST ε σ α)
    (f : α → EST ε σ β) (g : β → EST ε σ γ) :
    (x >>= f) >>= g = x >>= fun y => f y >>= g := by
  funext s
  dsimp only [Bind.bind, EST.bind]
  cases h : x s <;> rfl

private theorem io_bind_assoc {α β γ : Type} (x : IO α) (f : α → IO β)
    (g : β → IO γ) :
    (x >>= f) >>= g = x >>= fun y => f y >>= g :=
  est_bind_assoc x f g

private theorem io_pure_bind {α β : Type} (a : α) (f : α → IO β) :
    (pure a >>= f) = f a := rfl

/-! ## §1 The configured policy -/

/-- The F2/F3 priority vector for the seeded route: annotation groups under
`--var=annot`, the legacy heuristic priority otherwise. -/
def lcgConfigPrio (o : SearchConfig) (p : CompiledProblem DomConstraint) : List Nat :=
  if o.var == .annot then annotPrioOpts p o
  else LcgHeur.heurPrio o.toHeurOpts p

/-- The activity-bump toggle actually used.  `--var=annot` disables it by
design (the exact-halving rescale would destroy the annotation bands). -/
def lcgConfigActBump (o : SearchConfig) : Bool :=
  o.actBump && o.var != .annot

/-- The static value presentation of a configuration.  `configOrders` with no
previous incumbent is the first-round presentation of the linear driver; for
`--val=incumbent` it is the activity order (the documented seeded gap). -/
def lcgConfigDomains (p : CompiledProblem DomConstraint) (o : SearchConfig) :
    List Domain :=
  annotDomains p (configOrders p o none)

/-- The compiled problem on the configured presentation.  Constraints, names,
source model and `toStore` are unchanged; only the per-slot enumeration order
differs. -/
def lcgConfigProblem (p : CompiledProblem DomConstraint) (o : SearchConfig) :
    CompiledProblem DomConstraint :=
  { p with domains := lcgConfigDomains p o }

@[simp] theorem lcgConfigProblem_domains (p : CompiledProblem DomConstraint)
    (o : SearchConfig) :
    (lcgConfigProblem p o).domains = annotDomains p (configOrders p o none) := rfl

@[simp] theorem lcgConfigProblem_constraints (p : CompiledProblem DomConstraint)
    (o : SearchConfig) :
    (lcgConfigProblem p o).constraints = p.constraints := rfl

@[simp] theorem lcgConfigProblem_toStore (p : CompiledProblem DomConstraint)
    (o : SearchConfig) : (lcgConfigProblem p o).toStore = p.toStore := rfl

/-- The presentation does not change the accepted assignments. -/
theorem accepts_lcgConfigProblem (p : CompiledProblem DomConstraint)
    (o : SearchConfig) (a : Assignment) :
    accepts (lcgConfigProblem p o) a = accepts p a := rfl

/-- Adding an objective bound after the presentation is the same acceptance
test as adding it before (the presentation changes domains only). -/
theorem accepts_curP_lcgConfigProblem (p : CompiledProblem DomConstraint)
    (o : SearchConfig) (spec : ObjectiveSpec) (bo : Option Int)
    (a : Assignment) :
    accepts (curP (lcgConfigProblem p o) spec bo) a = accepts (curP p spec bo) a := by
  cases bo <;> rfl

/-- Membership in the presented assignment set is membership in the compiled
assignment set. -/
theorem mem_allAssigns_lcgConfigProblem (p : CompiledProblem DomConstraint)
    (o : SearchConfig) (a : Assignment) :
    a ∈ allAssigns (lcgConfigProblem p o).domains ↔ a ∈ allAssigns p.domains := by
  simpa [lcgConfigProblem, lcgConfigDomains] using
    mem_allAssigns_domListPerm (annotDomains_domListPerm p (configOrders p o none)) a

/-- The configured presentation preserves the executable LCG gate. -/
theorem gateOk_lcgConfigProblem {p : CompiledProblem DomConstraint}
    {o : SearchConfig} (h : gateOk (lcgProblem p) = true) :
    gateOk (lcgProblem (lcgConfigProblem p o)) = true := by
  have hh : gateOk (LcgHeur.heurProblem p) = true := gateOk_heur h
  simpa [lcgConfigProblem, lcgConfigDomains, lcgProblem] using
    gateOk_annot p (configOrders p o none) hh

/-- The configured presentation preserves the full mixed-route gate. -/
theorem lcgRouteGateMixed_lcgConfigProblem {p : CompiledProblem DomConstraint}
    {o : SearchConfig} (h : lcgRouteGateMixed p = true) :
    lcgRouteGateMixed (lcgConfigProblem p o) = true := by
  have hgates := h
  simp only [lcgRouteGateMixed, Bool.and_eq_true,
    LcgMixedCompiledKit.mixedKitGateFastB_eq] at hgates
  simp only [lcgRouteGateMixed, Bool.and_eq_true,
    LcgMixedCompiledKit.mixedKitGateFastB_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa [lcgConfigProblem, lcgConfigDomains, lcgProblem] using
      gateOk_annot p (configOrders p o none) (gateOk_heur hgates.1.1)
  · simpa [lcgConfigProblem, lcgConfigDomains, lcgProblem] using
      domPruningOkB_annot p (configOrders p o none)
        (domPruningOkB_heur hgates.1.2)
  · simpa [lcgConfigProblem, lcgConfigDomains, lcgProblem] using
      mixedKitGateB_annot p (configOrders p o none)
        (mixedKitGateB_heur hgates.2)

/-- The configured seeded solver: the existing certified seeded entry with the
configuration's priority vector and activity-bump toggle.  Value orders are
handled by running the driver on `lcgConfigProblem`; every problem handed to
`solveDb` therefore already has the configured presentation. -/
def lcgSeedSolverConfig (o : SearchConfig) : SeedCertSolver where
  solve := lcgVerdict (o := o)
  gate := fun p => gateOk (lcgProblem p)
  leaf := lcgLeaf
  solveDb := fun orig p hd s =>
    lcgSolveDb orig p hd s (prio := lcgConfigPrio o p) (actBump := lcgConfigActBump o)
  sat_sound := fun _ _ h => lcgVerdict_sat h
  unsat_complete := fun _ h => lcgVerdict_unsat h
  gate_add := fun _ _ => rfl
  total := by
    intro p hg hfail
    unfold lcgVerdict at hfail
    split at hfail
    · cases hfail
    · cases hfail
    · rename_i hs
      exact solveSearchConfig_verdict p o hs
  sat_sound_db := fun _ _ _ _ _ _ h =>
    lcgSolveDb_sat_sound (prio := lcgConfigPrio o _) (actBump := lcgConfigActBump o) h
  unsat_complete_db := fun _ _ _ _ _ h hseed =>
    lcgSolveDb_unsat_complete (prio := lcgConfigPrio o _) (actBump := lcgConfigActBump o)
      h hseed
  db_entailed := fun _ _ _ _ hseed =>
    lcgSolveDb_db_entailed (prio := lcgConfigPrio o _) (actBump := lcgConfigActBump o) hseed
  total_db := fun _ _ _ _ hg =>
    lcgSolveDb_total (prio := lcgConfigPrio o _) (actBump := lcgConfigActBump o) hg
  leaf_add := fun p c a ha => lcgLeaf_addConstraint p c a ha
  leaf_bound := fun _ _ _ _ hwb a ha => lcgLeaf_improveBound hwb a ha

/-- The configured solver's gate at the configured presentation. -/
theorem lcgSeedSolverConfig_gate {o : SearchConfig} {p : CompiledProblem DomConstraint}
    (h : gateOk (lcgProblem p) = true) :
    (lcgSeedSolverConfig o).gate (lcgConfigProblem p o) = true :=
  gateOk_lcgConfigProblem h

/-! ## §2 The pure configured runner -/

/-- The certified seeded optimizer on the configured presentation, starting
from the empty seed.  The summary's `p` is the compiled problem as given (its
`toStore` is the presentation's `toStore`); `run` and `seeds` come from the
seeded loop over `lcgConfigProblem p o`. -/
def optimizeSeedConfig (o : SearchConfig) (m : Model) :
    Except String SeedOptSummary :=
  match compileModelOpt m with
  | .error e => .error e
  | .ok (p, spec) =>
      let p' := lcgConfigProblem p o
      let r := optLoopSeed (lcgSeedSolverConfig o) p' spec none (SeedDb.nil p'.domains)
      .ok ⟨p, r.1, r.2⟩

/-- Unfolding of `optimizeSeedConfig` at a successful compile. -/
theorem optimizeSeedConfig_inv {o : SearchConfig} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun} {seeds : List Nat}
    (h : optimizeSeedConfig o m = .ok ⟨p, run, seeds⟩) :
    ∃ spec, compileModelOpt m = .ok (p, spec) ∧
      (optLoopSeed (lcgSeedSolverConfig o) (lcgConfigProblem p o) spec none
        (SeedDb.nil (lcgConfigProblem p o).domains)).1 = run ∧
      (optLoopSeed (lcgSeedSolverConfig o) (lcgConfigProblem p o) spec none
        (SeedDb.nil (lcgConfigProblem p o).domains)).2 = seeds := by
  unfold optimizeSeedConfig at h
  cases hc : compileModelOpt m with
  | error e => rw [hc] at h; cases h
  | ok r =>
      obtain ⟨p', spec⟩ := r
      rw [hc] at h
      simp only [Except.ok.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨spec, rfl, rfl, rfl⟩

/-- Every emitted solution of a configured seeded run is a store satisfying
the source model, with the reported objective value. -/
theorem optimizeSeedConfig_solution_sound {o : SearchConfig} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun} {seeds : List Nat}
    (h : optimizeSeedConfig o m = .ok ⟨p, run, seeds⟩) (hwf : WellFormed fullSig m)
    {t : List Value × Int} (ht : t ∈ run.sols) :
    Satisfies fullSig fullInterp m (p.toStore t.1) ∧
    LeanFzn.Semantics.ParamHonest m (p.toStore t.1) ∧
    m.solve.objective (p.toStore t.1) = some t.2 := by
  obtain ⟨spec, hc, hr, -⟩ := optimizeSeedConfig_inv h
  let p' := lcgConfigProblem p o
  have hinv := optLoopSeed_inv (lcgSeedSolverConfig o) p' spec _ none
    (SeedDb.nil p'.domains) rfl
    (SeedDb.nil_entailed ((lcgSeedSolverConfig o).leaf (curP p' spec none)) p'.domains)
  rw [← hr] at ht
  obtain ⟨hmem, hacc, hv, -⟩ := hinv.sound t ht
  have hmemP : t.1 ∈ allAssigns p.domains :=
    (mem_allAssigns_lcgConfigProblem p o t.1).mp hmem
  have haccP : accepts p t.1 = true := by
    simpa [p', accepts_lcgConfigProblem] using hacc
  obtain ⟨hsat, hpar, i, hi, hai⟩ := compileOpt_exact hc hwf hmemP haccP
  rw [hv] at hai
  have : t.2 = i := by simpa using hai
  subst this
  exact ⟨⟨hwf, hsat⟩, hpar, hi⟩

/-- The objective strictly improves along a configured seeded run's emitted
sequence. -/
theorem optimizeSeedConfig_improving {o : SearchConfig} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun} {seeds : List Nat}
    (h : optimizeSeedConfig o m = .ok ⟨p, run, seeds⟩) :
    ∃ spec : ObjectiveSpec,
      run.sols.Pairwise (fun t u => betterB spec.dir u.2 t.2 = true) := by
  obtain ⟨spec, -, hr, -⟩ := optimizeSeedConfig_inv h
  let p' := lcgConfigProblem p o
  refine ⟨spec, ?_⟩
  rw [← hr]
  exact (optLoopSeed_inv (lcgSeedSolverConfig o) p' spec _ none (SeedDb.nil p'.domains) rfl
    (SeedDb.nil_entailed ((lcgSeedSolverConfig o).leaf (curP p' spec none)) p'.domains)).pairwise

/-- A completed configured seeded run's last solution is an optimal solution
of the source model. -/
theorem optimizeSeedConfig_optimal {o : SearchConfig} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun} {seeds : List Nat}
    (h : optimizeSeedConfig o m = .ok ⟨p, run, seeds⟩) (hwf : WellFormed fullSig m)
    (hcomp : run.complete = true) {t : List Value × Int}
    (hlast : run.sols.getLast? = some t) :
    IsSolution fullSig fullInterp m (p.toStore t.1) := by
  obtain ⟨spec, hc, hr, -⟩ := optimizeSeedConfig_inv h
  let p' := lcgConfigProblem p o
  have hinv := optLoopSeed_inv (lcgSeedSolverConfig o) p' spec _ none
    (SeedDb.nil p'.domains) rfl
    (SeedDb.nil_entailed ((lcgSeedSolverConfig o).leaf (curP p' spec none)) p'.domains)
  rw [← hr] at hlast hcomp
  have ht : t ∈ (optLoopSeed (lcgSeedSolverConfig o) p' spec none
      (SeedDb.nil p'.domains)).1.sols := List.mem_of_getLast? hlast
  obtain ⟨hmem, hacc, hv, -⟩ := hinv.sound t ht
  have hlb := hinv.last_bound t hlast
  have hopt := hinv.optimal hcomp
  rw [hlb] at hopt
  have hmemP : t.1 ∈ allAssigns p.domains :=
    (mem_allAssigns_lcgConfigProblem p o t.1).mp hmem
  have haccP : accepts p t.1 = true := by
    simpa [p', accepts_lcgConfigProblem] using hacc
  have hoptP : ∀ b ∈ allAssigns p.domains,
      accepts (p.addConstraint (spec.improveBound t.2)) b = false := by
    intro b hb
    have hb' : b ∈ allAssigns p'.domains :=
      (mem_allAssigns_lcgConfigProblem p o b).mpr hb
    have hbnd : accepts (curP (lcgConfigProblem p o) spec (some t.2)) b = false := by
      simpa [p'] using hopt b hb'
    rw [accepts_curP_lcgConfigProblem p o spec (some t.2) b] at hbnd
    simpa [curP] using hbnd
  exact compileOpt_optimal hc hwf hmemP haccP hv hoptP

/-- A completed configured seeded run without solutions proves the source
model has no parameter-honest satisfying store. -/
theorem optimizeSeedConfig_unsat {o : SearchConfig} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun} {seeds : List Nat}
    (h : optimizeSeedConfig o m = .ok ⟨p, run, seeds⟩) (hwf : WellFormed fullSig m)
    (hcomp : run.complete = true) (hnil : run.sols = []) :
    ¬ ∃ store, Satisfies fullSig fullInterp m store ∧
      LeanFzn.Semantics.ParamHonest m store := by
  obtain ⟨spec, hc, hr, -⟩ := optimizeSeedConfig_inv h
  let p' := lcgConfigProblem p o
  have hinv := optLoopSeed_inv (lcgSeedSolverConfig o) p' spec _ none
    (SeedDb.nil p'.domains) rfl
    (SeedDb.nil_entailed ((lcgSeedSolverConfig o).leaf (curP p' spec none)) p'.domains)
  rw [← hr] at hcomp hnil
  have hlb := hinv.nil_bound hnil
  have hopt := hinv.optimal hcomp
  rw [hlb] at hopt
  rintro ⟨store, hs, hph⟩
  obtain ⟨b, hb, hbacc, -⟩ := compileOpt_covers hc hwf hs.2 hph
  have hb' : b ∈ allAssigns p'.domains :=
    (mem_allAssigns_lcgConfigProblem p o b).mpr hb
  have : accepts p b = false := by
    have hbnd : accepts (curP (lcgConfigProblem p o) spec none) b = false := by
      simpa [p'] using hopt b hb'
    rw [accepts_curP_lcgConfigProblem p o spec none b] at hbnd
    simpa [curP] using hbnd
  rw [hbacc] at this
  cases this

/-- Totality: with the compiled gate satisfied a configured seeded run always
completes (never `fail`, never an unreadable objective). -/
theorem optimizeSeedConfig_total {o : SearchConfig} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun} {seeds : List Nat}
    (h : optimizeSeedConfig o m = .ok ⟨p, run, seeds⟩) (hwf : WellFormed fullSig m)
    (hg : gateOk (lcgProblem p) = true) : run.complete = true := by
  obtain ⟨spec, hc, hr, -⟩ := optimizeSeedConfig_inv h
  let p' := lcgConfigProblem p o
  rw [← hr]
  refine optLoopSeed_complete (lcgSeedSolverConfig o) p' spec
    (lcgSeedSolverConfig_gate hg) ?_ _ none (SeedDb.nil p'.domains) rfl
  intro a hmem hacc
  have hmemP : a ∈ allAssigns p.domains :=
    (mem_allAssigns_lcgConfigProblem p o a).mp hmem
  have haccP : accepts p a = true := by
    simpa [p', accepts_lcgConfigProblem] using hacc
  obtain ⟨-, -, i, -, hai⟩ := compileOpt_exact hc hwf hmemP haccP
  exact ⟨i, hai⟩

/-! ## §3 The streaming configured runner -/

/-- Streaming configured seeded branch and bound: `emit` is called on every
certified improving solution before the next round; the returned seed trace is
the per-round learned-database size. -/
def optimizeStreamSeedConfig (o : SearchConfig) (m : Model)
    (emit : Store → IO Unit) : IO (Except String SeedOptSummary) :=
  match compileModelOpt m with
  | .error e => pure (.error e)
  | .ok (p, spec) =>
      let p' := lcgConfigProblem p o
      optimizeStreamSeedLoop (lcgSeedSolverConfig o) p' spec
        (fun a => p.toStore a) emit none (SeedDb.nil p'.domains) >>= fun r =>
        pure (.ok ⟨p, r.1, r.2⟩)

/-- **THE STREAMING CONFIGURED RUNNER'S SPEC**: it emits exactly the source
stores of the seeded run's solutions (in order) and returns that run with its
per-round seed sizes. -/
theorem optimizeStreamSeedConfig_eq {o : SearchConfig} {m : Model}
    (emit : Store → IO Unit) :
    optimizeStreamSeedConfig o m emit =
      (match compileModelOpt m with
       | .error e => pure (.error e)
       | .ok (p, spec) =>
           let p' := lcgConfigProblem p o
           emitAll emit
               ((optLoopSeed (lcgSeedSolverConfig o) p' spec none
                 (SeedDb.nil p'.domains)).1.sols.map (fun t => p.toStore t.1)) >>= fun _ =>
             pure (.ok ⟨p, (optLoopSeed (lcgSeedSolverConfig o) p' spec none
               (SeedDb.nil p'.domains)).1,
               (optLoopSeed (lcgSeedSolverConfig o) p' spec none
               (SeedDb.nil p'.domains)).2⟩)) := by
  unfold optimizeStreamSeedConfig
  cases hc : compileModelOpt m with
  | error e => rfl
  | ok u =>
      obtain ⟨p, spec⟩ := u
      simp only []
      rw [optimizeStreamSeedLoop_emit]
      rw [io_bind_assoc, io_pure_bind]

end LeanFzn.Integration

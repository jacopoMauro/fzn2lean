/-
Purpose: certified compiled-problem solving through the fuel-free LCG kernel
on the executable MIXED kit gates (uniform int/bool domains), with
chronological fallback elsewhere. The integer gate and kit remain for the
integer-only fragment; the public route gates on the mixed kit, which accepts
every integer-gate problem and additionally uniform bool domains.
Dependencies: compiler fit enumeration links connect verdicts to compiled
semantics; LcgCompiledKit/LcgPhaseTerminal (integer fragment) and
LcgMixedCompiledKit/LcgMixedPhaseTerminal (mixed fragment) supply the semantic
LCG proofs; Chronological.Proofs.Search certifies the fallback.
DAG: compiler and solver proof leaves -> Lcg -> source solve and optimization.
-/
import LeanFzn.Compiler.Proofs.CompileCore
import LeanFzn.Compiler.SeedClauses
import LeanFzn.Solver.Chronological.Proofs.Search
import LeanFzn.Solver.UIP.Proofs.LcgCompiledKit
import LeanFzn.Solver.UIP.Proofs.LcgMixedCompiledKit
import LeanFzn.Solver.UIP.Proofs.LcgPhaseTerminal
import LeanFzn.Solver.UIP.Proofs.LcgPhaseKernelSched
import LeanFzn.Solver.UIP.Proofs.LcgMixedPhaseTerminal
import LeanFzn.Solver.UIP.Proofs.LcgSeedClauses

namespace LeanFzn.Integration
open LeanFzn.Semantics LeanFzn.Compiler LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP LeanFzn.Solver.UIP.C3b
open LeanFzn.Solver.UIP.LcgCanonicalClauses LeanFzn.Solver.UIP.LcgSeedClauses

/-- The compiled feasibility problem, with its original clause database
    SEEDED from the compiled constraints: every `bool_clause`
    (`boolClauseSlot`) constraint contributes its original clause
    (`Compiler.seedClauses`), every other family contributes none. -/
def lcgProblem (p : CompiledProblem DomConstraint) :
    LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
  { names := p.names, domains := p.domains, constraints := p.constraints,
    clauses := seedClauses p.constraints, objective := () }

/-- The seeded database is canonical (every seed literal is a positive
    pin, i.e. in normal form). -/
theorem lcgSeedCanonical (p : CompiledProblem DomConstraint) :
    DatabaseCanonical (seedClauses p.constraints) :=
  seedClauses_canonical

def lcgLeaf (p : CompiledProblem DomConstraint) : Assignment → Bool :=
  chronologicalLeaf (lcgProblem p) DomConstraint.satisfiedB

/-- The seeded database is entailed at every leaf solution: every seed
    clause comes from the `bool_clause` semantics of its constraint
    (`Compiler.seedClauses_entailed`), so any leaf-accepted assignment
    satisfies it and the engine may carry it as an original clause. -/
theorem lcgSeedEntailed (p : CompiledProblem DomConstraint) :
    LearnedEntailed (lcgLeaf p) (seedClauses p.constraints) := by
  intro c hc a ha
  have hcons : (p.constraints.all fun dc => dc.satisfiedB a) = true := by
    have h := ha
    simp only [lcgLeaf, chronologicalLeaf, lcgProblem, Bool.and_eq_true] at h
    exact h.2.1
  exact seedClauses_entailed
    (fun dc hdc => List.all_eq_true.mp hcons dc hdc) c hc

/-- All administrative premises of the LCG kit are checked here. -/
def lcgRouteGate (p : CompiledProblem DomConstraint) : Bool :=
  gateOk (lcgProblem p) && domPruningOkB (lcgProblem p) &&
    LcgCompiledKit.kitGateB (lcgProblem p)

theorem lcgInput {p : CompiledProblem DomConstraint} (h : lcgRouteGate p = true) :
    CompiledInput (lcgLeaf p) (lcgProblem p) := by
  simp only [lcgRouteGate, Bool.and_eq_true] at h
  exact ⟨rfl, h.1.1, h.1.2⟩

/-- The integer route gate's slot range makes the seeded database
    pool-aligned. -/
theorem lcgSeedAlignedInt {p : CompiledProblem DomConstraint}
    (h : lcgRouteGate p = true) :
    DatabaseAligned p.domains (seedClauses p.constraints) :=
  seedClauses_aligned_of_slotOK
    (LcgCompiledKit.slots_of_gate (lcgInput h)
      (by simp only [lcgRouteGate, Bool.and_eq_true] at h; exact h.2))

def lcgProps (p : CompiledProblem DomConstraint) : List Propagator :=
  clampProps p.domains (p.constraints.filterMap propagatorOfProved)

theorem lcgKit {p : CompiledProblem DomConstraint} (h : lcgRouteGate p = true) :
    LcgRunGood.LcgKit (lcgLeaf p) p.domains (seedClauses p.constraints) p.constraints
      (p.constraints.filterMap propagatorOfProved) (lcgProps p) :=
  LcgCompiledKit.kit_of_compiled (lcgInput h)
    (by simp only [lcgRouteGate, Bool.and_eq_true] at h; exact h.2)
    (lcgSeedAlignedInt h)

/-- The mixed route gate: administrative premises plus the mixed kit gate
(accepts every problem the integer gate accepts, and additionally uniform
int/bool value domains). PLAN P3b: the kit conjunct is the FAST twin
`mixedKitGateFastB` (sort-based integer-view duplicate check, `O(|d| log |d|)`
instead of the quadratic `decide … .Nodup`);
`LcgMixedCompiledKit.mixedKitGateFastB_eq`
proves it equal to `mixedKitGateB`, so this gate decides the same problems as
before and the gate theorems keep their statements. -/
def lcgRouteGateMixed (p : CompiledProblem DomConstraint) : Bool :=
  gateOk (lcgProblem p) && domPruningOkB (lcgProblem p) &&
    LcgMixedCompiledKit.mixedKitGateFastB (lcgProblem p)

theorem lcgInputMixed {p : CompiledProblem DomConstraint}
    (h : lcgRouteGateMixed p = true) :
    CompiledInput (lcgLeaf p) (lcgProblem p) := by
  simp only [lcgRouteGateMixed, Bool.and_eq_true] at h
  exact ⟨rfl, h.1.1, h.1.2⟩

/-- The mixed route gate's slot range makes the seeded database
    pool-aligned. -/
theorem lcgSeedAlignedMixed {p : CompiledProblem DomConstraint}
    (h : lcgRouteGateMixed p = true) :
    DatabaseAligned p.domains (seedClauses p.constraints) :=
  seedClauses_aligned_of_slotOK
    (LcgMixedCompiledKit.slots_of_mixedGate (lcgInputMixed h)
      (by simp only [lcgRouteGateMixed, Bool.and_eq_true,
        LcgMixedCompiledKit.mixedKitGateFastB_eq] at h; exact h.2))

theorem lcgKitMixed {p : CompiledProblem DomConstraint}
    (h : lcgRouteGateMixed p = true) :
    LcgMixedGood.MixedLcgKit (lcgLeaf p) p.domains (seedClauses p.constraints)
      p.constraints
      (p.constraints.filterMap propagatorOfProved) (lcgProps p) :=
  LcgMixedCompiledKit.kit_of_compiled_mixed (lcgInputMixed h)
    (by simp only [lcgRouteGateMixed, Bool.and_eq_true,
      LcgMixedCompiledKit.mixedKitGateFastB_eq] at h; exact h.2)
    (lcgSeedCanonical p) (lcgSeedAlignedMixed h)

/-- **THE SCHEDULED ROUTE (PLAN P1)**: the same solve through the scheduled
dispatcher `phaseNextSched` (`solve_sched`). The scheduled dispatcher now
evaluates the scheduled scan ONCE per step (`schedulerNextSched` reads its
transition and its table off a single `nextPruningEventSched`; the terminal
continuation re-reads that same event), and the stamp test is a first-order
recursion — so the measured effect on the P1 battery is a WIN: 84% of
propagator runs eliminated and ~1.32x faster than the certified baseline
(`Tests/E1/SchedCounts.lean`, 43 instances, reps=3: 14.8s vs 19.5s). It IS
the public route (`lcgRun`), certified against the baseline kernel by
`lcgRunSched_eq_solve` alone. -/
def lcgRunSched (p : CompiledProblem DomConstraint) : DriverResult (lcgLeaf p) :=
  solve_sched p.domains (seedClauses p.constraints) (lcgProps p)
    (lcgSeedEntailed p) (PropScheduler.init (lcgProps p))
    (clampProps_local p.domains p.constraints)
    (PropSchedulerOK.init (lcgProps p))

/-- **ROUTE EQUALITY (the scheduled route is the certified kernel + the
scheduled dispatch)**: the certification transfers through this equality
alone; no LCG correctness proof is re-done for the scheduled scan. -/
theorem lcgRunSched_eq_solve (p : CompiledProblem DomConstraint) :
    lcgRunSched p = LcgPhaseKernel.solve p.domains (seedClauses p.constraints)
      (lcgProps p) (lcgSeedEntailed p) :=
  solve_sched_eq _ _ _ _ _ _ _

/-- **THE PUBLIC ROUTE IS THE SCHEDULED ROUTE** (wired after the measured
sign flip): the one-scan scheduled dispatch is the faster certified path, so
`lcgRun` — and with it `solveCompiledLcg*` — runs on it. -/
def lcgRun (p : CompiledProblem DomConstraint) : DriverResult (lcgLeaf p) :=
  lcgRunSched p

/-- **ROUTE EQUALITY (public form)**: the public route's verdict is exactly the
certified fuel-free kernel's verdict (the scheduled dispatch is a refinement
of `phaseNext`; the bridge is `lcgRunSched_eq_solve`). -/
theorem lcgRun_eq_solve (p : CompiledProblem DomConstraint) :
    lcgRun p = LcgPhaseKernel.solve p.domains (seedClauses p.constraints)
      (lcgProps p) (lcgSeedEntailed p) := by
  unfold lcgRun
  exact lcgRunSched_eq_solve p

/-- **ROUTE EQUALITY (candidate name)**: the candidate entry `lcgRunSched`
and the public route `lcgRun` are the same certified scheduled route. -/
theorem lcgRunSched_eq_lcgRun (p : CompiledProblem DomConstraint) :
    lcgRunSched p = lcgRun p := by
  unfold lcgRun
  rfl

/-- Uses LCG on the checked mixed kit fragment (uniform int/bool domains) and
certified chronology otherwise. -/
def solveCompiledLcgMixed (p : CompiledProblem DomConstraint) : SearchResult :=
  if lcgRouteGateMixed p then
    match lcgRun p with
    | .sat a => .sat a
    | .unsat => .unsat
  else
    LeanFzn.Solver.Chronological.solve (lcgProblem p) DomConstraint.satisfiedB
      (p.constraints.filterMap propagatorOfProved) (domPruningKit (lcgProblem p))

/-- The public route: LCG on the checked mixed kit fragment, certified
chronology otherwise. Definitionally `solveCompiledLcgMixed`. -/
def solveCompiledLcg (p : CompiledProblem DomConstraint) : SearchResult :=
  solveCompiledLcgMixed p

theorem solveCompiledLcgMixed_sat {p : CompiledProblem DomConstraint} {a : List Value}
    (h : solveCompiledLcgMixed p = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  unfold solveCompiledLcgMixed at h
  split at h
  · rename_i hg
    split at h
    · rename_i a' hr
      rw [lcgRun_eq_solve p] at hr
      cases h
      have hs := LcgMixedPhaseTerminal.solve_sat_solution_of_kit_mixed
        (lcgKitMixed hg) (lcgSeedEntailed p) hr
      have hl := hs.1
      simp only [lcgLeaf, chronologicalLeaf, lcgProblem,
        Bool.and_eq_true] at hl
      exact ⟨fits_mem_allAssigns p.domains a hs.2, hl.2.1⟩
    · cases h
  · have hs := LeanFzn.Solver.Chronological.solve_sat_correct
      (fun c a => DomConstraint.satisfiedB_iff c a) h
    exact ⟨fits_mem_allAssigns p.domains a hs.1,
      List.all_eq_true.mpr (fun c hc => (DomConstraint.satisfiedB_iff c a).mpr (hs.2 c hc))⟩

theorem solveCompiledLcgMixed_unsat {p : CompiledProblem DomConstraint}
    (h : solveCompiledLcgMixed p = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  have hex : ∀ b, b ∈ allAssigns p.domains → accepts p b = true → False := by
    unfold solveCompiledLcgMixed at h
    split at h
    · rename_i hg
      split at h
      · cases h
      · rename_i hr
        rw [lcgRun_eq_solve p] at hr
        intro b hb ha
        have hf : Assignment.Fits p.domains b := ⟨mem_allAssigns_length p.domains b hb,
          fun i v hv => mem_allAssigns_fits p.domains b hb i v hv⟩
        apply LcgMixedPhaseTerminal.solve_unsat_excludes_of_kit_mixed (lcgKitMixed hg)
          (lcgSeedEntailed p) hr b
        refine ⟨?_, hf⟩
        simp only [lcgLeaf, chronologicalLeaf, lcgProblem, Bool.and_eq_true]
        refine ⟨fitsB_iff.mpr hf, ?_, ?_⟩
        · exact ha
        · exact List.all_eq_true.mpr fun c hc =>
            seedClauses_any_satisfiedB
              (fun dc hdc => List.all_eq_true.mp ha dc hdc) c hc
    · have hn := LeanFzn.Solver.Chronological.solve_pruned_unsat_correct
        (fun c a => DomConstraint.satisfiedB_iff c a)
        (fun c hc _ hsol => seedClauses_satisfiedBy
          (fun dc hdc => hsol.2 dc hdc) c hc) h
      intro b hb ha
      apply hn
      refine ⟨b, ⟨mem_allAssigns_length p.domains b hb,
        fun i v hv => mem_allAssigns_fits p.domains b hb i v hv⟩, ?_⟩
      exact fun c hc => (DomConstraint.satisfiedB_iff c b).mp (List.all_eq_true.mp ha c hc)
  intro b hb
  cases ha : accepts p b with
  | false => rfl
  | true => exact False.elim (hex b hb ha)

/-- Both routes terminate without a step budget; the outer source gate is unnecessary. -/
theorem solveCompiledLcgMixed_total (p : CompiledProblem DomConstraint) :
    solveCompiledLcgMixed p ≠ .unknown := by
  unfold solveCompiledLcgMixed
  split
  · cases lcgRun p <;> simp
  · exact LeanFzn.Solver.Chronological.solve_total _ _ _ _

theorem solveCompiledLcg_sat {p : CompiledProblem DomConstraint} {a : List Value}
    (h : solveCompiledLcg p = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  unfold solveCompiledLcg at h
  exact solveCompiledLcgMixed_sat h

theorem solveCompiledLcg_unsat {p : CompiledProblem DomConstraint}
    (h : solveCompiledLcg p = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  unfold solveCompiledLcg at h
  exact solveCompiledLcgMixed_unsat h

/-- Both routes terminate without a step budget; the outer source gate is unnecessary. -/
theorem solveCompiledLcg_total (p : CompiledProblem DomConstraint) :
    solveCompiledLcg p ≠ .unknown := by
  unfold solveCompiledLcg
  exact solveCompiledLcgMixed_total p

end LeanFzn.Integration

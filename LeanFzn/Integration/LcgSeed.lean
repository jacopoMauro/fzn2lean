/-
File: LeanFzn/Integration/LcgSeed.lean

Purpose (PLAN B2): the LCG instance of the seeded branch-and-bound interface
`OptimizeSeed.SeedCertSolver`. §1 proves the leaf monotonicity the driver needs
(the leaf of a compiled problem is antitone under `addConstraint`, and a
strictly better objective bound gives a stronger leaf — the `improveBound`
step). §2 carries a learned clause database into the LCG kernel: the seeded
compiled problem contains the box's own `seedClauses` PLUS the carried clauses,
its mixed kit is produced from the existing kit producer (the carried database
is canonical and pool-aligned by construction), and the DB-producing entry
`LcgPhaseRunDb.solveCfg` decides it. §3 assembles the solver instance and its
per-obligation proofs, so `optLoopSeed lcgSeedSolver` runs the real LCG kernel
on every round with the previous round's learned clauses already in the
database.

DAG: LcgOptimize + OptimizeSeed + UIP LcgPhaseRunDb -> this file -> tests.
NO `sorry`, NO custom axiom.
-/
import LeanFzn.Integration.LcgOptimize
import LeanFzn.Integration.OptimizeSeed
import LeanFzn.Solver.UIP.Proofs.LcgPhaseRunDb

namespace LeanFzn.Integration
open LeanFzn.Semantics LeanFzn.Compiler LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP LeanFzn.Solver.UIP.C3b
open LeanFzn.Solver.UIP.LcgSeedClauses LeanFzn.Solver.UIP.LcgPhaseRunDb
open LeanFzn.Solver.UIP.LcgCanonicalClauses

/-- The solver-level verdict of a driver result (the kernel never fails). -/
def verdictOfDriver {leaf : Assignment → Bool} : DriverResult leaf → CertVerdict
  | .sat a => .sat a
  | .unsat => .unsat

@[simp] theorem verdictOfDriver_sat {leaf : Assignment → Bool} (a : Assignment) :
    verdictOfDriver (leaf := leaf) (.sat a) = .sat a := rfl

@[simp] theorem verdictOfDriver_unsat {leaf : Assignment → Bool} :
    verdictOfDriver (leaf := leaf) (.unsat) = .unsat := rfl

/-! ## §1 Leaf monotonicity (PLAN B2 deliverable 1) -/

/-- **THE LEAF MONOTONICITY CORE.** If `q`'s box is `p`'s, every
`q`-satisfied assignment satisfies `p`'s constraints, and `p`'s clause base is
contained in `q`'s, then every `lcgLeaf q` solution is an `lcgLeaf p` solution:
the chronological leaf of a compiled problem is antitone in the compiled
constraints and clause seeds (the leaf-level reading of `accepts_add`). -/
theorem lcgLeaf_mono {p q : CompiledProblem DomConstraint}
    (hdom : q.domains = p.domains)
    (hc : ∀ a, (q.constraints.all fun c => c.satisfiedB a) = true →
      (p.constraints.all fun c => c.satisfiedB a) = true)
    (hcl : ∀ c ∈ seedClauses p.constraints, c ∈ seedClauses q.constraints) :
    ∀ a, lcgLeaf q a = true → lcgLeaf p a = true := by
  intro a ha
  have hf : fitsB (lcgProblem p) a = fitsB (lcgProblem q) a := by
    simp only [fitsB, lcgProblem, hdom]
  simp only [lcgLeaf, chronologicalLeaf, lcgProblem, Bool.and_eq_true] at ha ⊢
  simp only [lcgProblem] at hf
  refine ⟨?_, hc a ha.2.1, ?_⟩
  · rw [hf]; exact ha.1
  · exact List.all_eq_true.mpr fun c hc' =>
      List.all_eq_true.mp ha.2.2 c (hcl c hc')

/-- **MONOTONICITY, `addConstraint` FORM**: the leaf of `p.addConstraint c` is
stronger than the leaf of `p`. -/
theorem lcgLeaf_addConstraint (p : CompiledProblem DomConstraint)
    (c : DomConstraint) :
    ∀ a, lcgLeaf (p.addConstraint c) a = true → lcgLeaf p a = true := by
  refine lcgLeaf_mono (p := p) (q := p.addConstraint c) rfl ?_ ?_
  · intro a h
    simp only [CompiledProblem.addConstraint, List.all_append, Bool.and_eq_true] at h
    exact h.1
  · intro c' hc'
    have hsplit : seedClauses (p.addConstraint c).constraints
        = seedClauses p.constraints ++ seedClauses [c] := by
      simp only [CompiledProblem.addConstraint, seedClauses, List.filterMap_append]
    rw [hsplit]
    exact List.mem_append_left _ hc'

/-- **DELIVERABLE 1**: a database entailed at `lcgLeaf p` is entailed at
`lcgLeaf (p.addConstraint c')` — the general monotonicity step a branch-and-bound
driver performs at every added bound. -/
theorem learnedEntailed_addConstraint {p : CompiledProblem DomConstraint}
    {c : DomConstraint} {db : List Clause}
    (hent : LearnedEntailed (lcgLeaf p) db) :
    LearnedEntailed (lcgLeaf (p.addConstraint c)) db :=
  learnedEntailed_mono (lcgLeaf_addConstraint p c) hent

/-- The `improveBound` constraint of a strictly better objective value is
stronger than the one of the worse value. -/
theorem improveBound_satisfiedB_mono {spec : ObjectiveSpec} {w b : Int}
    (hwb : betterB spec.dir w b = true) :
    ∀ a, DomConstraint.satisfiedB (spec.improveBound w) a = true →
      DomConstraint.satisfiedB (spec.improveBound b) a = true := by
  intro a h
  rw [DomConstraint.satisfiedB_iff (spec.improveBound w) a] at h
  rw [DomConstraint.satisfiedB_iff (spec.improveBound b) a]
  cases hd : spec.dir <;>
    simp only [ObjectiveSpec.improveBound, hd, DomConstraint.SatisfiedBy, betterB,
      decide_eq_true_eq] at hwb h ⊢
  · obtain ⟨j, hj, hle⟩ := h
    exact ⟨j, hj, by omega⟩
  · obtain ⟨j, hj, hle⟩ := h
    exact ⟨j, hj, by omega⟩

/-- `improveBound` contributes no clause seed (its shape is a constant bound,
never a `bool_clause`). -/
theorem seedClauses_improveBound (dcs : List DomConstraint) (spec : ObjectiveSpec)
    (v : Int) : seedClauses (dcs ++ [spec.improveBound v]) = seedClauses dcs := by
  have hsplit : seedClauses (dcs ++ [spec.improveBound v])
      = seedClauses dcs ++ seedClauses [spec.improveBound v] := by
    simp only [seedClauses, List.filterMap_append]
  have hsingle : seedClauses [spec.improveBound v] = [] := by
    cases hd : spec.dir <;>
      (simp only [ObjectiveSpec.improveBound, hd]; rfl)
  rw [hsplit, hsingle, List.append_nil]

/-- Adding an `improveBound` constraint leaves the clause seed unchanged. -/
theorem seedClauses_add_improveBound (p : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) (v : Int) :
    seedClauses (p.addConstraint (spec.improveBound v)).constraints
      = seedClauses p.constraints :=
  seedClauses_improveBound p.constraints spec v

/-- **MONOTONICITY, `improveBound` FORM**: a strictly better bound gives a
stronger leaf, so a database entailed at the old bound is entailed at the new
one (the `betterB`-driven re-solve step of branch and bound). -/
theorem lcgLeaf_improveBound {p : CompiledProblem DomConstraint} {spec : ObjectiveSpec}
    {w b : Int} (hwb : betterB spec.dir w b = true) :
    ∀ a, lcgLeaf (p.addConstraint (spec.improveBound w)) a = true →
      lcgLeaf (p.addConstraint (spec.improveBound b)) a = true := by
  refine lcgLeaf_mono (p := p.addConstraint (spec.improveBound b))
    (q := p.addConstraint (spec.improveBound w)) rfl ?_ ?_
  · intro a h
    simp only [CompiledProblem.addConstraint, List.all_append, List.all_cons,
      List.all_nil, Bool.and_true, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, improveBound_satisfiedB_mono hwb a h.2⟩
  · intro c' hc'
    rw [seedClauses_add_improveBound p spec b] at hc'
    rwa [seedClauses_add_improveBound p spec w]

/-- **DELIVERABLE 1, bound form**: a database entailed under a bound is
entailed at every strictly better bound. -/
theorem learnedEntailed_improveBound {p : CompiledProblem DomConstraint}
    {spec : ObjectiveSpec} {w b : Int} (hwb : betterB spec.dir w b = true)
    {db : List Clause}
    (hent : LearnedEntailed (lcgLeaf (p.addConstraint (spec.improveBound b))) db) :
    LearnedEntailed (lcgLeaf (p.addConstraint (spec.improveBound w))) db :=
  learnedEntailed_mono (lcgLeaf_improveBound hwb) hent

/-! ## §2 The seeded compiled problem and its mixed kit -/

/-- The seeded compiled problem: the clause base is the problem's own seed
(the C2 `seedClauses`) PLUS the carried learned database, so the carried
clauses are propagated from the very first round of the seeded kernel. -/
def lcgProblemSeed (p : CompiledProblem DomConstraint) (s : SeedDb p.domains) :
    LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
  { lcgProblem p with clauses := seedClauses p.constraints ++ s.clauses }

/-- The leaf of the seeded compiled problem (the chronological leaf of the
seeded clause base). -/
def lcgLeafSeed (p : CompiledProblem DomConstraint) (s : SeedDb p.domains) :
    Assignment → Bool :=
  chronologicalLeaf (lcgProblemSeed p s) DomConstraint.satisfiedB

/-- The executable gates read domains and constraints only, so seeding the
clause base preserves them. -/
theorem gateOk_lcgProblemSeed (p : CompiledProblem DomConstraint) (s : SeedDb p.domains) :
    gateOk (lcgProblemSeed p s) = gateOk (lcgProblem p) := rfl

theorem domPruningOkB_lcgProblemSeed (p : CompiledProblem DomConstraint)
    (s : SeedDb p.domains) :
    domPruningOkB (lcgProblemSeed p s) = domPruningOkB (lcgProblem p) := rfl

theorem mixedKitGateB_lcgProblemSeed (p : CompiledProblem DomConstraint)
    (s : SeedDb p.domains) :
    LcgMixedCompiledKit.mixedKitGateB (lcgProblemSeed p s)
      = LcgMixedCompiledKit.mixedKitGateB (lcgProblem p) := rfl

/-- **THE SEEDED KIT**: the mixed kit of the seeded problem, from the existing
kit producer. The carried database is canonical and pool-aligned by
construction (`SeedDb`), so appending it to the problem's seed preserves both
facts the producer asks for. -/
theorem lcgKitSeed {p : CompiledProblem DomConstraint} {s : SeedDb p.domains}
    (hg : lcgRouteGateMixed p = true) :
    LcgMixedGood.MixedLcgKit (lcgLeafSeed p s) p.domains
      (seedClauses p.constraints ++ s.clauses) p.constraints
      (p.constraints.filterMap propagatorOfProved) (lcgProps p) := by
  have h := hg
  simp only [lcgRouteGateMixed, Bool.and_eq_true,
    LcgMixedCompiledKit.mixedKitGateFastB_eq] at h
  refine LcgMixedCompiledKit.kit_of_compiled_mixed ⟨rfl, ?_, ?_⟩ ?_ ?_ ?_
  · rw [gateOk_lcgProblemSeed]; exact h.1.1
  · rw [domPruningOkB_lcgProblemSeed]; exact h.1.2
  · rw [mixedKitGateB_lcgProblemSeed]; exact h.2
  · exact databaseCanonical_append seedClauses_canonical s.canonical
  · exact databaseAligned_append (lcgSeedAlignedMixed hg) s.aligned

/-- The appended clause base of the seeded problem is entailed at the seeded
leaf — the leaf's own clause conjunct (the derivation of
`CompiledInput.leaf_clauses` at the seeded problem). -/
theorem lcgLeafSeed_entailed (p : CompiledProblem DomConstraint) (s : SeedDb p.domains) :
    LearnedEntailed (lcgLeafSeed p s) (seedClauses p.constraints ++ s.clauses) := by
  intro c hc a ha
  simp only [lcgLeafSeed, chronologicalLeaf, lcgProblemSeed, Bool.and_eq_true] at ha
  obtain ⟨l, hl, hev⟩ := List.any_eq_true.mp (List.all_eq_true.mp ha.2.2 c hc)
  exact ⟨l, hl, of_decide_eq_true hev⟩

/-- **THE RE-ENTRY BRIDGE**: a solution of the problem whose carried database
is entailed is a solution of the SEEDED problem (the appended clauses add
nothing the problem's leaf does not already imply). -/
theorem lcgLeafSeed_of_lcgLeaf {p : CompiledProblem DomConstraint} {s : SeedDb p.domains}
    (hent : LearnedEntailed (lcgLeaf p) s.clauses) :
    ∀ a, lcgLeaf p a = true → lcgLeafSeed p s a = true := by
  intro a ha
  have hcons : (p.constraints.all fun c => c.satisfiedB a) = true := by
    have h := ha
    simp only [lcgLeaf, chronologicalLeaf, lcgProblem, Bool.and_eq_true] at h
    exact h.2.1
  have hclauses : ((seedClauses p.constraints).all
      fun c => c.any (fun l => decide (l.eval a = some true))) = true := by
    have h := ha
    simp only [lcgLeaf, chronologicalLeaf, lcgProblem, Bool.and_eq_true] at h
    exact h.2.2
  have hfits : fitsB (lcgProblemSeed p s) a = true := by
    have h := ha
    simp only [lcgLeaf, chronologicalLeaf, lcgProblem, Bool.and_eq_true] at h
    exact h.1
  simp only [lcgLeafSeed, chronologicalLeaf, lcgProblemSeed, Bool.and_eq_true]
  exact ⟨hfits, hcons, List.all_eq_true.mpr fun c hc => by
    rcases List.mem_append.mp hc with hc | hc
    · exact List.all_eq_true.mp hclauses c hc
    · exact (clause_any_iff c a).mpr (hent c hc a ha)⟩

/-- Every accepted assignment of the box (with the carried database entailed)
is a solution of the seeded problem. -/
theorem lcgLeafSeed_of_accepts {p : CompiledProblem DomConstraint} {s : SeedDb p.domains}
    (hent : LearnedEntailed (lcgLeaf p) s.clauses) {b : List Value}
    (hb : b ∈ allAssigns p.domains) (hacc : accepts p b = true) :
    lcgLeafSeed p s b = true := by
  refine lcgLeafSeed_of_lcgLeaf hent b ?_
  simp only [lcgLeaf, chronologicalLeaf, lcgProblem, Bool.and_eq_true]
  refine ⟨fitsB_iff.mpr ⟨mem_allAssigns_length p.domains b hb,
    fun i v hv => mem_allAssigns_fits p.domains b hb i v hv⟩, hacc, ?_⟩
  exact List.all_eq_true.mpr (seedClauses_any_satisfiedB
    (fun dc hdc => List.all_eq_true.mp hacc dc hdc))
/-- The DB-producing run on the seeded problem: the concrete LCG kernel from
the seeded clause base. -/
def lcgSeedRun (p : CompiledProblem DomConstraint) (s : SeedDb p.domains) :
    DriverResult (lcgLeafSeed p s) × SchedulerConfig (lcgLeafSeed p s) :=
  solveCfg p.domains (seedClauses p.constraints ++ s.clauses) (lcgProps p)
    (lcgLeafSeed_entailed p s)

/-- **THE TERMINAL DATABASE OF THE SEEDED RUN**: canonical, pool-aligned and
entailed at the seeded leaf (`LcgPhaseRunDb.solveDb_spec_mixed` at the seeded
kit). -/
theorem lcgSeedRun_spec {p : CompiledProblem DomConstraint} {s : SeedDb p.domains}
    (hg : lcgRouteGateMixed p = true) :
    DatabaseCanonical (lcgSeedRun p s).2.branch.learned ∧
    DatabaseAligned p.domains (lcgSeedRun p s).2.branch.learned ∧
    LearnedEntailed (lcgLeafSeed p s) (lcgSeedRun p s).2.branch.learned :=
  solveDb_spec_mixed (lcgKitSeed hg) (lcgLeafSeed_entailed p s)

/-- The seeded LCG solve at the compiled-problem level: on the checked mixed
route the concrete LCG kernel runs on the seeded problem and returns its
terminal learned database; otherwise the certified chronological solver
decides and the carried database is passed through unchanged. -/
def lcgSolveDb (orig : List Domain) (p : CompiledProblem DomConstraint)
    (hd : p.domains = orig) (s : SeedDb orig) : CertVerdict × SeedDb orig :=
  if hg : lcgRouteGateMixed p then
    (verdictOfDriver (lcgSeedRun p (SeedDb.cast hd.symm s)).1,
      SeedDb.cast hd ⟨(lcgSeedRun p (SeedDb.cast hd.symm s)).2.branch.learned,
        (lcgSeedRun_spec hg (s := SeedDb.cast hd.symm s)).1,
        (lcgSeedRun_spec hg (s := SeedDb.cast hd.symm s)).2.1⟩)
  else
    (match chronVerdict p with
      | .sat a => .sat a
      | .unsat => .unsat
      | .fail => .fail, s)

/-- **THE SEEDED VERDICT IS SOUND** (SAT): a seeded SAT verdict of the LCG
route is an accepted assignment; on the chronological route it is the existing
`chronVerdict` verdict. -/
theorem lcgSolveDb_sat_sound {orig : List Domain} {p : CompiledProblem DomConstraint}
    {hd : p.domains = orig} {s : SeedDb orig} {a : List Value} {s' : SeedDb orig}
    (hc : lcgSolveDb orig p hd s = (.sat a, s')) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  unfold lcgSolveDb at hc
  split at hc
  · rename_i hg
    cases hr : (lcgSeedRun p (SeedDb.cast hd.symm s)).1 with
    | sat w =>
        simp only [hr, verdictOfDriver_sat, Prod.mk.injEq] at hc
        obtain ⟨hv, -⟩ := hc
        cases hv
        have hsol := solveDb_sat_solution_of_kit_mixed (lcgKitSeed hg)
          (lcgLeafSeed_entailed p (SeedDb.cast hd.symm s)) hr
        have hcons : (p.constraints.all fun c => c.satisfiedB a) = true := by
          have h := hsol.1
          simp only [lcgLeafSeed, chronologicalLeaf, lcgProblemSeed, Bool.and_eq_true] at h
          exact h.2.1
        exact ⟨fits_mem_allAssigns p.domains a hsol.2, hcons⟩
    | unsat =>
        simp only [hr, verdictOfDriver_unsat, Prod.mk.injEq] at hc
        obtain ⟨hv, -⟩ := hc
        cases hv
  · rename_i hng
    cases hv' : chronVerdict p with
    | sat w =>
        simp only [hv', Prod.mk.injEq] at hc
        obtain ⟨hv, -⟩ := hc
        cases hv
        exact chronVerdict_sat hv'
    | unsat =>
        simp only [hv', Prod.mk.injEq] at hc
        obtain ⟨hv, -⟩ := hc
        cases hv
    | fail =>
        simp only [hv', Prod.mk.injEq] at hc
        obtain ⟨hv, -⟩ := hc
        cases hv

/-- **THE SEEDED VERDICT IS COMPLETE** (UNSAT): a seeded UNSAT verdict of the
LCG route excludes every accepted assignment provided the carried database is
entailed at the problem's leaf; on the chronological route it is the existing
`chronVerdict` verdict. -/
theorem lcgSolveDb_unsat_complete {orig : List Domain} {p : CompiledProblem DomConstraint}
    {hd : p.domains = orig} {s : SeedDb orig} {s' : SeedDb orig}
    (hc : lcgSolveDb orig p hd s = (.unsat, s'))
    (hseed : LearnedEntailed (lcgLeaf p) s.clauses) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  intro b hb
  by_cases hacc : accepts p b = true
  · unfold lcgSolveDb at hc
    split at hc
    · rename_i hg
      have hfits : Assignment.Fits p.domains b :=
        ⟨mem_allAssigns_length p.domains b hb,
          fun i v hv' => mem_allAssigns_fits p.domains b hb i v hv'⟩
      cases hr : (lcgSeedRun p (SeedDb.cast hd.symm s)).1 with
      | sat w =>
          simp only [hr, verdictOfDriver_sat, Prod.mk.injEq] at hc
          obtain ⟨hv, -⟩ := hc
          cases hv
      | unsat =>
          simp only [hr, verdictOfDriver_unsat, Prod.mk.injEq] at hc
          obtain ⟨hv, -⟩ := hc
          cases hv
          have hex := solveDb_unsat_excludes_of_kit_mixed (lcgKitSeed hg)
            (lcgLeafSeed_entailed p (SeedDb.cast hd.symm s)) hr
          exact (hex b ⟨lcgLeafSeed_of_accepts hseed hb hacc, hfits⟩).elim
    · rename_i hng
      cases hv' : chronVerdict p with
      | sat w =>
          simp only [hv', Prod.mk.injEq] at hc
          obtain ⟨hv, -⟩ := hc
          cases hv
      | unsat =>
          have hff : accepts p b = false := chronVerdict_unsat hv' b hb
          rw [hff] at hacc
          cases hacc
      | fail =>
          simp only [hv', Prod.mk.injEq] at hc
          obtain ⟨hv, -⟩ := hc
          cases hv
  · cases hh : accepts p b with
    | false => rfl
    | true => exact absurd hh hacc

/-- **THE RETURNED DATABASE IS ENTAILED AND RE-USABLE**: the database returned
by a seeded solve is entailed at the problem's own leaf (given the seed is),
so it may seed the next round (whose leaf is stronger by deliverable 1); on
the chronological route the carried database is passed through unchanged. -/
theorem lcgSolveDb_db_entailed {orig : List Domain} {p : CompiledProblem DomConstraint}
    {hd : p.domains = orig} {s : SeedDb orig}
    (hseed : LearnedEntailed (lcgLeaf p) s.clauses) :
    LearnedEntailed (lcgLeaf p) (lcgSolveDb orig p hd s).2.clauses := by
  unfold lcgSolveDb
  split
  · rename_i hg
    exact learnedEntailed_mono (lcgLeafSeed_of_lcgLeaf hseed)
      (lcgSeedRun_spec hg (s := SeedDb.cast hd.symm s)).2.2
  · exact hseed

/-- **THE SEEDED ENTRY NEVER FAILS UNDER THE GATE**: the LCG route cannot fail
at all, and the chronological route is `chronSolver.total`. -/
theorem lcgSolveDb_total {orig : List Domain} {p : CompiledProblem DomConstraint}
    {hd : p.domains = orig} {s : SeedDb orig}
    (hg : gateOk (lcgProblem p) = true) : (lcgSolveDb orig p hd s).1 ≠ .fail := by
  unfold lcgSolveDb
  split
  · rename_i hroute
    intro hf
    cases hr : (lcgSeedRun p (SeedDb.cast hd.symm s)).1 with
    | sat w => simp only [hr, verdictOfDriver_sat] at hf; cases hf
    | unsat => simp only [hr, verdictOfDriver_unsat] at hf; cases hf
  · rename_i hroute
    intro hf
    cases hv : chronVerdict p with
    | sat w => simp only [hv] at hf; cases hf
    | unsat => simp only [hv] at hf; cases hf
    | fail => exact chronSolver.total p hg hv

/-! ## §3 The seeded LCG solver instance -/

/-- **THE SEEDED LCG SOLVER**: `lcgSolver` plus the seeded entry. Every
problem-level guarantee is the existing LCG one; the leaf is `lcgLeaf` and its
monotonicity is §1. -/
def lcgSeedSolver : SeedCertSolver where
  solve := lcgVerdict
  gate := fun p => gateOk (lcgProblem p)
  leaf := lcgLeaf
  solveDb := lcgSolveDb
  sat_sound := fun _ _ h => lcgVerdict_sat h
  unsat_complete := fun _ h => lcgVerdict_unsat h
  gate_add := fun _ _ => rfl
  total := lcgSolver.total
  sat_sound_db := fun _ _ _ _ _ _ h => lcgSolveDb_sat_sound h
  unsat_complete_db := fun _ _ _ _ _ h hseed => lcgSolveDb_unsat_complete h hseed
  db_entailed := fun _ _ _ _ hseed => lcgSolveDb_db_entailed hseed
  total_db := fun _ _ _ _ hg => lcgSolveDb_total hg
  leaf_add := fun p c a ha => lcgLeaf_addConstraint p c a ha
  leaf_bound := fun _ _ _ _ hwb a ha => lcgLeaf_improveBound hwb a ha

end LeanFzn.Integration

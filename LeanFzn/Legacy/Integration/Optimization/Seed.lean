/-
File: LeanFzn/Integration/Optimization/Seed.lean

Purpose (PLAN B2): the seeded refinement of the certified branch-and-bound
driver `Optimize.optLoop`. `SeedCertSolver` is a certified problem-level
solver whose `solveDb` takes a learned-clause database and returns the
database of the completed run; `optLoopSeed` threads that database from one
round into the next, so the re-solves of branch-and-bound start warmer, and
records the size of every seed handed to a solve (round order).
`optLoopSeed_inv` extends the plain `LoopInv` of `Optimize` with the
per-round SEED-ENTAILMENT invariant (`LearnedEntailed (leaf (curP p0 spec bo))
seed`): the general monotonicity lemma `learnedEntailed_mono` together with
the interface's `leaf_add`/`leaf_bound` steps carries it across each
`improveBound` step, so every existing soundness/optimality conclusion holds
for the seeded run as well.

The plain `CertSolver` interface and all existing theorems over it are
untouched; `SeedCertSolver` is a separate structure carrying the same
problem-level guarantees for the seeded entry.

DAG: Optimize + UIP database facts -> this file -> LcgSeed (LCG instance).
NO `sorry`, NO custom axiom.
-/
import LeanFzn.Integration.Optimization.Basic
import LeanFzn.Legacy.Integration.Optimization.Chronological
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgCanonicalClauses
import LeanFzn.Legacy.Solver.UIP.Proofs.SupportedDatabaseFacts

namespace LeanFzn.Integration
open LeanFzn.Semantics LeanFzn.Semantics.Globals LeanFzn.Semantics.Evaluation
open LeanFzn.Compiler LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgCanonicalClauses

/-! ## §1 The general monotonicity lemma -/

/-- **THE GENERAL MONOTONICITY LEMMA (`accepts_add`/`accepts_improve` at the
leaf level)**: a clause database entailed at every solution of a leaf is
entailed at every solution of any STRONGER leaf, i.e. one whose accepted
assignments are contained in the first's (`p.addConstraint c` is stronger
than `p`). -/
theorem learnedEntailed_mono {leaf₁ leaf₂ : Assignment → Bool} {db : List Clause}
    (h : ∀ a, leaf₂ a = true → leaf₁ a = true)
    (hent : LearnedEntailed leaf₁ db) : LearnedEntailed leaf₂ db :=
  fun c hc a ha => hent c hc a (h a ha)

/-! ## §2 The carried database and the seeded solver interface -/

/-- A learned clause database carried between re-solves: canonical and
pool-aligned with the box `orig`. Entailment at a leaf is deliberately NOT a
field: it is relative to the current problem and is threaded as a driver
invariant (`optLoopSeed_inv.seed_ent`). -/
structure SeedDb (orig : List Domain) where
  /-- the carried learned clauses -/
  clauses : List Clause
  /-- every carried clause is in normal form -/
  canonical : DatabaseCanonical clauses
  /-- every carried literal normalizes into the box's literal pool -/
  aligned : DatabaseAligned orig clauses
  /-- the previous round's incumbent, carried for a future solution-guided
      value presentation (`--val=incumbent`).  The F4 configured seeded entry
      runs one fixed presentation and does not consult it yet (the exact gap
      in `docs/F4-seeded-adapter.md`); it is heuristic metadata and never
      consulted by any soundness or coverage proof. -/
  prev : Option (List Value) := none

/-- The empty carried database (the first round's seed). -/
def SeedDb.nil (orig : List Domain) : SeedDb orig :=
  ⟨[], databaseCanonical_nil, databaseAligned_nil orig, none⟩

/-- Re-index a carried database across equal boxes. The driver threads one
box's bundle across the whole loop, while a solver's seeded entry is stated
over the problem's own `domains`; the cast keeps the two views apart without
changing the carried clauses (`cast_clauses`). -/
def SeedDb.cast {orig orig' : List Domain} (h : orig' = orig) (s : SeedDb orig') :
    SeedDb orig :=
  ⟨s.clauses, s.canonical, h ▸ s.aligned, s.prev⟩

/-- The carried clauses are not changed by the cast. -/
@[simp] theorem SeedDb.cast_clauses {orig orig' : List Domain} (h : orig' = orig)
    (s : SeedDb orig') : (SeedDb.cast h s).clauses = s.clauses := rfl

/-- Record the previous round's incumbent without touching the carried
database. -/
def SeedDb.withPrev (s : SeedDb orig) (a : Option (List Value)) : SeedDb orig :=
  ⟨s.clauses, s.canonical, s.aligned, a⟩

/-- The incumbent annotation never changes the carried clauses. -/
@[simp] theorem SeedDb.withPrev_clauses (s : SeedDb orig) (a : Option (List Value)) :
    (s.withPrev a).clauses = s.clauses := rfl

/-- The empty carried database is entailed at every leaf (vacuously). -/
theorem SeedDb.nil_entailed (leaf : Assignment → Bool) (orig : List Domain) :
    LearnedEntailed leaf (SeedDb.nil orig).clauses :=
  fun _ hc => absurd hc (List.not_mem_nil)

/-- A certified problem-level solver that carries a learned-clause database
between solves (`SeedCertSolver` = the `CertSolver` interface plus a seeded
solve entry). The box `orig` of a seeded solve is an explicit parameter with
the equation `p.domains = orig`, so a driver threading one bundle across a
family of problems that share a box (branch and bound) needs no dependent
casts. `leaf` is the solver's own leaf predicate: the database returned by a
seeded solve is entailed at it (`db_entailed`), and it is monotone under
constraint addition (`leaf_add`) and bound strengthening (`leaf_bound`), which
is what carries the driver's seed invariant across `improveBound` steps. -/
structure SeedCertSolver where
  /-- the unseeded verdict (the `CertSolver` entry) -/
  solve : CompiledProblem DomConstraint → CertVerdict
  /-- the executable gate (extension-stable, as in `CertSolver`) -/
  gate : CompiledProblem DomConstraint → Bool
  /-- the solver's own leaf predicate over the compiled problem -/
  leaf : CompiledProblem DomConstraint → Assignment → Bool
  /-- the seeded verdict: problem + carried database, verdict + carried
      database of the completed run -/
  solveDb : (orig : List Domain) → (p : CompiledProblem DomConstraint) →
    p.domains = orig → SeedDb orig → CertVerdict × SeedDb orig
  sat_sound : ∀ (p : CompiledProblem DomConstraint) (a : List Value),
    solve p = .sat a → a ∈ allAssigns p.domains ∧ accepts p a = true
  unsat_complete : ∀ (p : CompiledProblem DomConstraint), solve p = .unsat →
    ∀ b ∈ allAssigns p.domains, accepts p b = false
  gate_add : ∀ (p : CompiledProblem DomConstraint) (c : DomConstraint),
    gate (p.addConstraint c) = gate p
  total : ∀ (p : CompiledProblem DomConstraint), gate p = true → solve p ≠ .fail
  /-- the seeded SAT verdict is sound (as `CertSolver.sat_sound`) -/
  sat_sound_db : ∀ (orig : List Domain) (p : CompiledProblem DomConstraint)
    (hd : p.domains = orig) (s : SeedDb orig) (a : List Value) (s' : SeedDb orig),
    solveDb orig p hd s = (.sat a, s') →
      a ∈ allAssigns p.domains ∧ accepts p a = true
  /-- the seeded UNSAT verdict excludes every assignment of the box, provided
      the seed is entailed at the solver's leaf -/
  unsat_complete_db : ∀ (orig : List Domain) (p : CompiledProblem DomConstraint)
    (hd : p.domains = orig) (s s' : SeedDb orig),
    solveDb orig p hd s = (.unsat, s') → LearnedEntailed (leaf p) s.clauses →
      ∀ b ∈ allAssigns p.domains, accepts p b = false
  /-- the returned database is entailed at the solver's leaf, provided the
      seed is -/
  db_entailed : ∀ (orig : List Domain) (p : CompiledProblem DomConstraint)
    (hd : p.domains = orig) (s : SeedDb orig),
    LearnedEntailed (leaf p) s.clauses →
      LearnedEntailed (leaf p) (solveDb orig p hd s).2.clauses
  /-- the seeded entry never fails under the gate -/
  total_db : ∀ (orig : List Domain) (p : CompiledProblem DomConstraint)
    (hd : p.domains = orig) (s : SeedDb orig), gate p = true →
    (solveDb orig p hd s).1 ≠ .fail
  /-- the leaf is antitone in the compiled constraint list -/
  leaf_add : ∀ (p : CompiledProblem DomConstraint) (c : DomConstraint)
    (a : List Value), leaf (p.addConstraint c) a = true → leaf p a = true
  /-- a strictly better bound gives a stronger leaf -/
  leaf_bound : ∀ (p : CompiledProblem DomConstraint) (spec : ObjectiveSpec)
    (b w : Int), betterB spec.dir w b = true →
    ∀ a, leaf (p.addConstraint (spec.improveBound w)) a = true →
      leaf (p.addConstraint (spec.improveBound b)) a = true

/-- The gate is extension-stable along the branch-and-bound bounds, exactly as
for `CertSolver` (`gate_curP`). -/
theorem SeedCertSolver.gate_curP (S : SeedCertSolver)
    (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec) (bo : Option Int) :
    S.gate (curP p0 spec bo) = S.gate p0 := by
  cases bo with
  | none => rfl
  | some b => exact S.gate_add _ _

/-! ## §3 The seeded driver -/

/-- Seeded branch and bound: the exact recursion of `optLoop`, with the
carried database returned by each round handed to the next round, and the
size of every seed handed to a solve recorded in order (so the trace of a
finished run is `[|seed of round 0|, |seed of round 1|, …]`). -/
def optLoopSeed (S : SeedCertSolver) (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) (bo : Option Int) (s : SeedDb p0.domains) :
    OptRun × List Nat :=
  match hs : S.solveDb p0.domains (curP p0 spec bo) (curP_domains p0 spec bo) s with
  | (.unsat, _) => (⟨[], true, bo⟩, [s.clauses.length])
  | (.fail, _) => (⟨[], false, bo⟩, [s.clauses.length])
  | (.sat a, s') =>
      match hv : a[spec.slot]? with
      | some (.int v) =>
          let r := optLoopSeed S p0 spec (some v) (s'.withPrev (some a))
          (⟨(a, v) :: r.1.sols, r.1.complete, r.1.lastBound⟩,
            s.clauses.length :: r.2)
      | _ => (⟨[], false, bo⟩, [s.clauses.length])
termination_by meas p0 spec bo
decreasing_by
  have h := S.sat_sound_db p0.domains (curP p0 spec bo) (curP_domains p0 spec bo)
    s a s' hs
  rw [curP_domains] at h
  exact meas_decr h.1 h.2 hv

/-! Unfolding equations for `optLoopSeed`, with the branch matches kept
explicit (same discipline as the `optLoopEmit` equations of `Optimize`):
the match-bound variable of an unfolding step is not nameable, so the
proofs unfold the left-hand side only (`conv => lhs`), rewrite the verdict,
and reduce the verdict match and the objective read with the explicit
hypotheses. -/

private theorem optLoopSeed_unsat_eq {S : SeedCertSolver}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {s : SeedDb p0.domains} {s' : SeedDb p0.domains}
    (hs : S.solveDb p0.domains (curP p0 spec bo) (curP_domains p0 spec bo) s
      = (.unsat, s')) :
    optLoopSeed S p0 spec bo s = (⟨[], true, bo⟩, [s.clauses.length]) := by
  rw [optLoopSeed, hs]

private theorem optLoopSeed_fail_eq {S : SeedCertSolver}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {s : SeedDb p0.domains} {s' : SeedDb p0.domains}
    (hs : S.solveDb p0.domains (curP p0 spec bo) (curP_domains p0 spec bo) s
      = (.fail, s')) :
    optLoopSeed S p0 spec bo s = (⟨[], false, bo⟩, [s.clauses.length]) := by
  rw [optLoopSeed, hs]

private theorem optLoopSeed_sat_int_eq {S : SeedCertSolver}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {s : SeedDb p0.domains} {s' : SeedDb p0.domains}
    {a : List Value} {v : Int}
    (hs : S.solveDb p0.domains (curP p0 spec bo) (curP_domains p0 spec bo) s
      = (.sat a, s'))
    (hv : a[spec.slot]? = some (.int v)) :
    optLoopSeed S p0 spec bo s =
      (⟨(a, v) :: (optLoopSeed S p0 spec (some v) (s'.withPrev (some a))).1.sols,
        (optLoopSeed S p0 spec (some v) (s'.withPrev (some a))).1.complete,
        (optLoopSeed S p0 spec (some v) (s'.withPrev (some a))).1.lastBound⟩,
       s.clauses.length :: (optLoopSeed S p0 spec (some v) (s'.withPrev (some a))).2) := by
  conv => lhs; rw [optLoopSeed]
  rw [hs]
  simp only []
  rw [hv]

private theorem optLoopSeed_sat_none_eq {S : SeedCertSolver}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {s : SeedDb p0.domains} {s' : SeedDb p0.domains}
    {a : List Value}
    (hs : S.solveDb p0.domains (curP p0 spec bo) (curP_domains p0 spec bo) s
      = (.sat a, s'))
    (hn : ∀ i : Int, a[spec.slot]? ≠ some (.int i)) :
    optLoopSeed S p0 spec bo s = (⟨[], false, bo⟩, [s.clauses.length]) := by
  conv => lhs; rw [optLoopSeed]
  rw [hs]
  simp only []

/-! ## §4 The seeded loop invariant -/

/-- Loop invariants of the seeded driver: the plain `LoopInv` fields on the
run, the SEED-ENTAILMENT invariant at the current problem, and the seed TRACE
shape (one entry per solve, headed by the size of the seed actually handed to
this round's solve). -/
structure SeedRunInv (S : SeedCertSolver) (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) (bo : Option Int) (s : SeedDb p0.domains)
    (r : OptRun × List Nat) : Prop where
  sound : ∀ t ∈ r.1.sols, t.1 ∈ allAssigns p0.domains ∧ accepts p0 t.1 = true ∧
    t.1[spec.slot]? = some (.int t.2) ∧
    ∀ b, bo = some b → betterB spec.dir t.2 b = true
  pairwise : r.1.sols.Pairwise (fun t u => betterB spec.dir u.2 t.2 = true)
  optimal : r.1.complete = true →
    ∀ b ∈ allAssigns p0.domains, accepts (curP p0 spec r.1.lastBound) b = false
  nil_bound : r.1.sols = [] → r.1.lastBound = bo
  last_bound : ∀ t, r.1.sols.getLast? = some t → r.1.lastBound = some t.2
  /-- the invariant: the seed of this round is entailed at this round's leaf -/
  seed_ent : LearnedEntailed (S.leaf (curP p0 spec bo)) s.clauses
  /-- one seed size per solve -/
  trace_len : r.2.length = r.1.sols.length + 1
  /-- the first recorded size is this round's seed size -/
  trace_head : r.2.head? = some s.clauses.length

/-- The invariant at a `.sat` verdict whose objective read is NOT an integer:
no round is added and the run stops like `optLoop`. -/
private theorem optLoopSeed_inv_sat_none {S : SeedCertSolver}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {s s' : SeedDb p0.domains} {a : List Value}
    (hc : S.solveDb p0.domains (curP p0 spec bo) (curP_domains p0 spec bo) s
      = (.sat a, s'))
    (hn : ∀ i : Int, a[spec.slot]? ≠ some (.int i))
    (hseed : LearnedEntailed (S.leaf (curP p0 spec bo)) s.clauses) :
    SeedRunInv S p0 spec bo s (optLoopSeed S p0 spec bo s) := by
  rw [optLoopSeed_sat_none_eq hc hn]
  exact ⟨by simp, by simp, by simp, fun _ => rfl, by simp, hseed, by simp, rfl⟩

/-- **THE SEEDED LOOP INVARIANT.** Every emitted solution is accepted, the
sequence strictly improves, a completed run excludes every assignment under
its last bound, and — the B2 content — each round's seed is entailed at that
round's leaf: `learnedEntailed_mono` transfers the round's database to the
next problem's stronger leaf through `leaf_add` (first bound) and `leaf_bound`
(`betterB` re-solves). -/
theorem optLoopSeed_inv (S : SeedCertSolver) (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) :
    ∀ n bo s, meas p0 spec bo = n →
      LearnedEntailed (S.leaf (curP p0 spec bo)) s.clauses →
        SeedRunInv S p0 spec bo s (optLoopSeed S p0 spec bo s) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro bo s hn hseed
    cases hc : S.solveDb p0.domains (curP p0 spec bo) (curP_domains p0 spec bo) s with
    | mk v s' =>
      cases v with
      | unsat =>
          rw [optLoopSeed_unsat_eq hc]
          refine ⟨by simp, by simp, fun _ b hb => ?_, fun _ => rfl, by simp,
            hseed, by simp, rfl⟩
          rw [← curP_domains p0 spec bo] at hb
          exact S.unsat_complete_db p0.domains (curP p0 spec bo)
            (curP_domains p0 spec bo) s s' hc hseed b hb
      | fail =>
          rw [optLoopSeed_fail_eq hc]
          exact ⟨by simp, by simp, by simp, fun _ => rfl, by simp, hseed,
            by simp, rfl⟩
      | sat a =>
          cases hv : a[spec.slot]? with
          | none =>
              exact optLoopSeed_inv_sat_none hc
                (by intro i hi; rw [hv] at hi; cases hi) hseed
          | some w =>
            cases w with
            | int v =>
              rw [optLoopSeed_sat_int_eq hc hv]
              have hsat := S.sat_sound_db p0.domains (curP p0 spec bo)
                (curP_domains p0 spec bo) s a s' hc
              rw [curP_domains] at hsat
              obtain ⟨hmem, hacc⟩ := hsat
              have hlt := meas_decr hmem hacc hv
              have hdb' := S.db_entailed p0.domains (curP p0 spec bo)
                (curP_domains p0 spec bo) s hseed
              rw [hc] at hdb'
              have hseed' : LearnedEntailed (S.leaf (curP p0 spec (some v))) s'.clauses := by
                cases bo with
                | none =>
                    exact learnedEntailed_mono
                      (leaf₁ := S.leaf (curP p0 spec none))
                      (leaf₂ := S.leaf (curP p0 spec (some v)))
                      (fun a ha => S.leaf_add p0 (spec.improveBound v) a ha) hdb'
                | some b =>
                    have hbv : betterB spec.dir v b = true :=
                      (accepts_curP hacc).2 b v rfl hv
                    exact learnedEntailed_mono
                      (leaf₁ := S.leaf (curP p0 spec (some b)))
                      (leaf₂ := S.leaf (curP p0 spec (some v)))
                      (fun a ha =>
                        S.leaf_bound p0 spec b v hbv a ha) hdb'
              have IH := ih _ (hn ▸ hlt) (some v) (s'.withPrev (some a)) rfl hseed'
              obtain ⟨hacc0, hbo⟩ := accepts_curP hacc
              refine ⟨?_, ?_, IH.optimal, ?_, ?_, hseed, ?_, rfl⟩
              · intro t ht
                rcases List.mem_cons.mp ht with rfl | hr
                · exact ⟨hmem, hacc0, hv, fun b hb => hbo b _ hb hv⟩
                · obtain ⟨h1, h2, h3, h4⟩ := IH.sound t hr
                  exact ⟨h1, h2, h3, fun b hb =>
                    betterB_trans (h4 v rfl) (hbo b _ hb hv)⟩
              · refine List.pairwise_cons.mpr ⟨fun t ht => ?_, IH.pairwise⟩
                exact (IH.sound t ht).2.2.2 v rfl
              · intro h; simp at h
              · intro t ht
                dsimp only at ht ⊢
                by_cases hnil : (optLoopSeed S p0 spec (some v) (s'.withPrev (some a))).1.sols = []
                · rw [hnil] at ht
                  simp at ht
                  subst ht
                  exact IH.nil_bound hnil
                · apply IH.last_bound
                  rw [List.getLast?_cons] at ht
                  obtain ⟨x, hx⟩ : ∃ x, (optLoopSeed S p0 spec (some v) (s'.withPrev (some a))).1.sols.getLast? = some x := by
                    cases hl : (optLoopSeed S p0 spec (some v) (s'.withPrev (some a))).1.sols.getLast? with
                    | none => exact absurd (List.getLast?_eq_none_iff.mp hl) hnil
                    | some x => exact ⟨x, rfl⟩
                  rw [hx] at ht ⊢
                  simpa using ht
              · show (s.clauses.length :: (optLoopSeed S p0 spec (some v) (s'.withPrev (some a))).2).length
                  = ((a, v) :: (optLoopSeed S p0 spec (some v) (s'.withPrev (some a))).1.sols).length + 1
                rw [List.length_cons, List.length_cons, IH.trace_len]
            | bool b =>
                exact optLoopSeed_inv_sat_none hc
                  (by intro i hi; rw [hv] at hi; cases hi) hseed
            | setOfInt st =>
                exact optLoopSeed_inv_sat_none hc
                  (by intro i hi; rw [hv] at hi; cases hi) hseed
            | array arr =>
                exact optLoopSeed_inv_sat_none hc
                  (by intro i hi; rw [hv] at hi; cases hi) hseed

/-- Totality of the seeded driver: if the gate holds and every accepted
assignment reads an integer at the objective slot, every seeded run
completes. -/
private theorem optLoopSeed_complete_sat_none {S : SeedCertSolver}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {s s' : SeedDb p0.domains} {a : List Value}
    (hc : S.solveDb p0.domains (curP p0 spec bo) (curP_domains p0 spec bo) s
      = (.sat a, s'))
    (hn : ∀ i : Int, a[spec.slot]? ≠ some (.int i))
    (hread : ∀ a ∈ allAssigns p0.domains, accepts p0 a = true →
      ∃ i, a[spec.slot]? = some (.int i)) :
    (optLoopSeed S p0 spec bo s).1.complete = true := by
  rw [optLoopSeed_sat_none_eq hc hn]
  have hsat := S.sat_sound_db p0.domains (curP p0 spec bo)
    (curP_domains p0 spec bo) s a s' hc
  rw [curP_domains] at hsat
  obtain ⟨i, hi⟩ := hread a hsat.1 (accepts_curP hsat.2).1
  exact absurd hi (hn i)

theorem optLoopSeed_complete (S : SeedCertSolver) (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) (hg : S.gate p0 = true)
    (hread : ∀ a ∈ allAssigns p0.domains, accepts p0 a = true →
      ∃ i, a[spec.slot]? = some (.int i)) :
    ∀ n bo s, meas p0 spec bo = n → (optLoopSeed S p0 spec bo s).1.complete = true := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro bo s hn
    cases hc : S.solveDb p0.domains (curP p0 spec bo) (curP_domains p0 spec bo) s with
    | mk v s' =>
      cases v with
      | unsat => rw [optLoopSeed_unsat_eq hc]
      | fail =>
          rw [optLoopSeed_fail_eq hc]
          exact absurd (congrArg Prod.fst hc)
            (S.total_db p0.domains (curP p0 spec bo) (curP_domains p0 spec bo) s
              (by rw [S.gate_curP]; exact hg))
      | sat a =>
          cases hv : a[spec.slot]? with
          | none =>
              exact optLoopSeed_complete_sat_none hc
                (by intro i hi; rw [hv] at hi; cases hi) hread
          | some w =>
            cases w with
            | int v =>
              rw [optLoopSeed_sat_int_eq hc hv]
              have hsat := S.sat_sound_db p0.domains (curP p0 spec bo)
                (curP_domains p0 spec bo) s a s' hc
              rw [curP_domains] at hsat
              exact ih _ (hn ▸ meas_decr hsat.1 hsat.2 hv) (some v) (s'.withPrev (some a)) rfl
            | bool b =>
                exact optLoopSeed_complete_sat_none hc
                  (by intro i hi; rw [hv] at hi; cases hi) hread
            | setOfInt st =>
                exact optLoopSeed_complete_sat_none hc
                  (by intro i hi; rw [hv] at hi; cases hi) hread
            | array arr =>
                exact optLoopSeed_complete_sat_none hc
                  (by intro i hi; rw [hv] at hi; cases hi) hread

/-! ## §5 Source-level seeded theorems -/

/-- A seeded optimization run: the compiled problem, the run and the seed
sizes handed to each solve, in round order. -/
structure SeedOptSummary where
  p : CompiledProblem DomConstraint
  run : OptRun
  seeds : List Nat

/-- The certified seeded optimizer for a source model: `optimizeCertified`
with a carried learned-clause database, starting from the empty seed. -/
def optimizeSeedCertified (S : SeedCertSolver) (m : Model) :
    Except String SeedOptSummary :=
  match compileModelOpt m with
  | .error e => .error e
  | .ok (p, spec) =>
      let r := optLoopSeed S p spec none (SeedDb.nil p.domains)
      .ok ⟨p, r.1, r.2⟩

theorem optimizeSeedCertified_inv {S : SeedCertSolver} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun} {seeds : List Nat}
    (h : optimizeSeedCertified S m = .ok ⟨p, run, seeds⟩) :
    ∃ spec, compileModelOpt m = .ok (p, spec) ∧
      (optLoopSeed S p spec none (SeedDb.nil p.domains)).1 = run ∧
      (optLoopSeed S p spec none (SeedDb.nil p.domains)).2 = seeds := by
  unfold optimizeSeedCertified at h
  cases hc : compileModelOpt m with
  | error e => rw [hc] at h; cases h
  | ok r =>
      obtain ⟨p', spec⟩ := r
      rw [hc] at h
      simp only [Except.ok.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨spec, rfl, rfl, rfl⟩

/-- Every emitted solution of a seeded run is a store satisfying the source
model, with the reported objective value. -/
theorem optimizeSeedCertified_solution_sound {S : SeedCertSolver} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun} {seeds : List Nat}
    (h : optimizeSeedCertified S m = .ok ⟨p, run, seeds⟩) (hwf : WellFormed fullSig m)
    {t : List Value × Int} (ht : t ∈ run.sols) :
    Satisfies fullSig fullInterp m (p.toStore t.1) ∧
    LeanFzn.Semantics.ParamHonest m (p.toStore t.1) ∧
    m.solve.objective (p.toStore t.1) = some t.2 := by
  obtain ⟨spec, hc, hr, -⟩ := optimizeSeedCertified_inv h
  have hinv := optLoopSeed_inv S p spec _ none (SeedDb.nil p.domains) rfl
    (SeedDb.nil_entailed (S.leaf (curP p spec none)) p.domains)
  rw [← hr] at ht
  obtain ⟨hmem, hacc, hv, -⟩ := hinv.sound t ht
  obtain ⟨hsat, hpar, i, hi, hai⟩ := compileOpt_exact hc hwf hmem hacc
  rw [hv] at hai
  have : t.2 = i := by simpa using hai
  subst this
  exact ⟨⟨hwf, hsat⟩, hpar, hi⟩

/-- The objective strictly improves along a seeded run's emitted sequence. -/
theorem optimizeSeedCertified_improving {S : SeedCertSolver} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun} {seeds : List Nat}
    (h : optimizeSeedCertified S m = .ok ⟨p, run, seeds⟩) :
    ∃ spec : ObjectiveSpec,
      run.sols.Pairwise (fun t u => betterB spec.dir u.2 t.2 = true) := by
  obtain ⟨spec, -, hr, -⟩ := optimizeSeedCertified_inv h
  refine ⟨spec, ?_⟩
  rw [← hr]
  exact (optLoopSeed_inv S p spec _ none (SeedDb.nil p.domains) rfl
    (SeedDb.nil_entailed (S.leaf (curP p spec none)) p.domains)).pairwise

/-- A completed seeded run's last solution is an optimal solution of the
source model (the UNSAT of the improving bound). -/
theorem optimizeSeedCertified_optimal {S : SeedCertSolver} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun} {seeds : List Nat}
    (h : optimizeSeedCertified S m = .ok ⟨p, run, seeds⟩) (hwf : WellFormed fullSig m)
    (hcomp : run.complete = true) {t : List Value × Int}
    (hlast : run.sols.getLast? = some t) :
    IsSolution fullSig fullInterp m (p.toStore t.1) := by
  obtain ⟨spec, hc, hr, -⟩ := optimizeSeedCertified_inv h
  have hinv := optLoopSeed_inv S p spec _ none (SeedDb.nil p.domains) rfl
    (SeedDb.nil_entailed (S.leaf (curP p spec none)) p.domains)
  rw [← hr] at hlast hcomp
  have ht : t ∈ (optLoopSeed S p spec none (SeedDb.nil p.domains)).1.sols :=
    List.mem_of_getLast? hlast
  obtain ⟨hmem, hacc, hv, -⟩ := hinv.sound t ht
  have hlb := hinv.last_bound t hlast
  have hopt := hinv.optimal hcomp
  rw [hlb] at hopt
  exact compileOpt_optimal hc hwf hmem hacc hv hopt

/-- A completed seeded run without solutions proves the source model has no
parameter-honest satisfying store. -/
theorem optimizeSeedCertified_unsat {S : SeedCertSolver} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun} {seeds : List Nat}
    (h : optimizeSeedCertified S m = .ok ⟨p, run, seeds⟩) (hwf : WellFormed fullSig m)
    (hcomp : run.complete = true) (hnil : run.sols = []) :
    ¬ ∃ store, Satisfies fullSig fullInterp m store ∧
      LeanFzn.Semantics.ParamHonest m store := by
  obtain ⟨spec, hc, hr, -⟩ := optimizeSeedCertified_inv h
  have hinv := optLoopSeed_inv S p spec _ none (SeedDb.nil p.domains) rfl
    (SeedDb.nil_entailed (S.leaf (curP p spec none)) p.domains)
  rw [← hr] at hcomp hnil
  have hlb := hinv.nil_bound hnil
  have hopt := hinv.optimal hcomp
  rw [hlb] at hopt
  rintro ⟨store, hs, hph⟩
  obtain ⟨b, hb, hbacc, -⟩ := compileOpt_covers hc hwf hs.2 hph
  have : accepts p b = false := hopt b hb
  rw [hbacc] at this
  cases this

/-- Totality: with the solver gate satisfied a seeded run always completes
(never `fail`, never an unreadable objective). -/
theorem optimizeSeedCertified_total {S : SeedCertSolver} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun} {seeds : List Nat}
    (h : optimizeSeedCertified S m = .ok ⟨p, run, seeds⟩) (hwf : WellFormed fullSig m)
    (hg : S.gate p = true) : run.complete = true := by
  obtain ⟨spec, hc, hr, -⟩ := optimizeSeedCertified_inv h
  rw [← hr]
  refine optLoopSeed_complete S p spec hg ?_ _ none (SeedDb.nil p.domains) rfl
  intro a hmem hacc
  obtain ⟨-, -, i, -, hai⟩ := compileOpt_exact hc hwf hmem hacc
  exact ⟨i, hai⟩

/-! ## §6 The seeded streaming driver -/

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

/-- Seeded streaming branch and bound: the exact recursion of `optLoopSeed`,
calling `emit` once per improving solution before the next solve, and carrying
the returned database into the next round (the `optimizeStream` counterpart of
the seeded driver). -/
def optimizeStreamSeedLoop {α : Type} (S : SeedCertSolver)
    (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec)
    (f : List Value → α) (emit : α → IO Unit) :
    Option Int → SeedDb p0.domains → IO (OptRun × List Nat)
  | bo, s =>
    match hs : S.solveDb p0.domains (curP p0 spec bo) (curP_domains p0 spec bo) s with
    | (.unsat, _) => pure (⟨[], true, bo⟩, [s.clauses.length])
    | (.fail, _) => pure (⟨[], false, bo⟩, [s.clauses.length])
    | (.sat a, s') =>
        match hv : a[spec.slot]? with
        | some (.int v) =>
            emit (f a) >>= fun _ =>
              optimizeStreamSeedLoop S p0 spec f emit (some v) (s'.withPrev (some a)) >>= fun r =>
                pure (⟨(a, v) :: r.1.sols, r.1.complete, r.1.lastBound⟩,
                  s.clauses.length :: r.2)
        | _ => pure (⟨[], false, bo⟩, [s.clauses.length])
termination_by bo s => meas p0 spec bo
decreasing_by
  have h := S.sat_sound_db p0.domains (curP p0 spec bo) (curP_domains p0 spec bo)
    s a s' hs
  rw [curP_domains] at h
  exact meas_decr h.1 h.2 hv

private theorem optimizeStreamSeedLoop_unsat_eq {S : SeedCertSolver}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {s s' : SeedDb p0.domains} {α : Type} {f : List Value → α} {emit : α → IO Unit}
    (hs : S.solveDb p0.domains (curP p0 spec bo) (curP_domains p0 spec bo) s
      = (.unsat, s')) :
    optimizeStreamSeedLoop S p0 spec f emit bo s
      = pure (⟨[], true, bo⟩, [s.clauses.length]) := by
  rw [optimizeStreamSeedLoop, hs]

private theorem optimizeStreamSeedLoop_fail_eq {S : SeedCertSolver}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {s s' : SeedDb p0.domains} {α : Type} {f : List Value → α} {emit : α → IO Unit}
    (hs : S.solveDb p0.domains (curP p0 spec bo) (curP_domains p0 spec bo) s
      = (.fail, s')) :
    optimizeStreamSeedLoop S p0 spec f emit bo s
      = pure (⟨[], false, bo⟩, [s.clauses.length]) := by
  rw [optimizeStreamSeedLoop, hs]

private theorem optimizeStreamSeedLoop_sat_int_eq {S : SeedCertSolver}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {s s' : SeedDb p0.domains} {a : List Value} {v : Int}
    {α : Type} {f : List Value → α} {emit : α → IO Unit}
    (hs : S.solveDb p0.domains (curP p0 spec bo) (curP_domains p0 spec bo) s
      = (.sat a, s'))
    (hv : a[spec.slot]? = some (.int v)) :
    optimizeStreamSeedLoop S p0 spec f emit bo s =
      (emit (f a) >>= fun _ =>
        optimizeStreamSeedLoop S p0 spec f emit (some v) (s'.withPrev (some a)) >>= fun r =>
          pure (⟨(a, v) :: r.1.sols, r.1.complete, r.1.lastBound⟩,
            s.clauses.length :: r.2)) := by
  conv => lhs; rw [optimizeStreamSeedLoop]
  rw [hs]
  simp only []
  rw [hv]

private theorem optimizeStreamSeedLoop_sat_none_eq {S : SeedCertSolver}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {s s' : SeedDb p0.domains} {a : List Value}
    {α : Type} {f : List Value → α} {emit : α → IO Unit}
    (hs : S.solveDb p0.domains (curP p0 spec bo) (curP_domains p0 spec bo) s
      = (.sat a, s'))
    (hn : ∀ i : Int, a[spec.slot]? ≠ some (.int i)) :
    optimizeStreamSeedLoop S p0 spec f emit bo s
      = pure (⟨[], false, bo⟩, [s.clauses.length]) := by
  conv => lhs; rw [optimizeStreamSeedLoop]
  rw [hs]
  simp only []

/-- The streaming spec at a non-integer objective read. -/
private theorem optimizeStreamSeedLoop_spec_none {S : SeedCertSolver}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {s s' : SeedDb p0.domains} {a : List Value}
    {α : Type} {f : List Value → α} {emit : α → IO Unit}
    (hs : S.solveDb p0.domains (curP p0 spec bo) (curP_domains p0 spec bo) s
      = (.sat a, s'))
    (hn : ∀ i : Int, a[spec.slot]? ≠ some (.int i)) :
    optimizeStreamSeedLoop S p0 spec f emit bo s =
      (emitAll emit ((optLoopSeed S p0 spec bo s).1.sols.map (fun u => f u.1)) >>= fun _ =>
        pure (optLoopSeed S p0 spec bo s)) := by
  rw [optimizeStreamSeedLoop_sat_none_eq hs hn, optLoopSeed_sat_none_eq hs hn]
  simp only [emitAll, io_pure_bind, List.map_nil]

/-- **THE SEEDED STREAMING DRIVER'S SPEC**: it emits exactly the `f`-images of
the seeded run's solutions, in order, and returns that seeded run (with its
seed trace) — so every seeded soundness/optimality theorem applies to it
unchanged. -/
theorem optimizeStreamSeedLoop_emit {α : Type} (S : SeedCertSolver)
    (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec) (f : List Value → α)
    (emit : α → IO Unit) (bo : Option Int) (s : SeedDb p0.domains) :
    optimizeStreamSeedLoop S p0 spec f emit bo s =
      (emitAll emit ((optLoopSeed S p0 spec bo s).1.sols.map (fun t => f t.1)) >>= fun _ =>
        pure (optLoopSeed S p0 spec bo s)) := by
  suffices h : ∀ n : Nat, ∀ (b : Option Int) (t : SeedDb p0.domains),
      meas p0 spec b = n →
      optimizeStreamSeedLoop S p0 spec f emit b t =
        (emitAll emit ((optLoopSeed S p0 spec b t).1.sols.map (fun u => f u.1)) >>= fun _ =>
          pure (optLoopSeed S p0 spec b t)) from h _ bo s rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro bo s hn
    cases hc : S.solveDb p0.domains (curP p0 spec bo) (curP_domains p0 spec bo) s with
    | mk v s' =>
      cases v with
      | unsat =>
          rw [optimizeStreamSeedLoop_unsat_eq hc, optLoopSeed_unsat_eq hc]
          simp only [emitAll, io_pure_bind, List.map_nil]
      | fail =>
          rw [optimizeStreamSeedLoop_fail_eq hc, optLoopSeed_fail_eq hc]
          simp only [emitAll, io_pure_bind, List.map_nil]
      | sat a =>
          cases hv : a[spec.slot]? with
          | none =>
              exact optimizeStreamSeedLoop_spec_none hc
                (by intro i hi; rw [hv] at hi; cases hi)
          | some w =>
            cases w with
            | int v =>
              have hsat := S.sat_sound_db p0.domains (curP p0 spec bo)
                (curP_domains p0 spec bo) s a s' hc
              rw [curP_domains] at hsat
              have IH := ih _ (hn ▸ meas_decr hsat.1 hsat.2 hv) (some v) (s'.withPrev (some a)) rfl
              rw [optimizeStreamSeedLoop_sat_int_eq hc hv, optLoopSeed_sat_int_eq hc hv,
                IH]
              simp only [emitAll, io_bind_assoc, io_pure_bind, List.map_cons]
            | bool b =>
                exact optimizeStreamSeedLoop_spec_none hc
                  (by intro i hi; rw [hv] at hi; cases hi)
            | setOfInt st =>
                exact optimizeStreamSeedLoop_spec_none hc
                  (by intro i hi; rw [hv] at hi; cases hi)
            | array arr =>
                exact optimizeStreamSeedLoop_spec_none hc
                  (by intro i hi; rw [hv] at hi; cases hi)

end LeanFzn.Integration

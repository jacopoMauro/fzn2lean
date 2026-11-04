import LeanFzn.Legacy.Integration.Chronological
/-
File: Tests/UIP/OracleFixtures.lean
comparisons)

Purpose (PREPARATION task; this module does NOT activate or claim anything
about the new public path):

  * an INDEPENDENT exhaustive oracle for tiny `DomConstraint` inputs —
    enumerate `allAssigns`, decide SAT/UNSAT and validate witnesses without
    using the LeanFzn.Solver's propagation, clauses, trails, learning or backjumping;
  * small input families covering the P1.5 regression list, each compared
    against the oracle at the PROOF level (the reference driver is
    well-founded-recursive, so the kernel cannot reduce its verdict; the
    comparison is stated as a `Prop` and proved from the certified verdict
    theorems `analyzedSolve_sat_leaf` / `analyzedSolve_unsat_excludes` and
    `solve_total`) and re-checked executably by `main` once T2 registers the
    suite;
  * component fixtures for the machinery that the public driver does not yet
    run: multiple reason resolutions, an irrelevant-level jump, propagation
    after an assertion, a completed long-reason trace, exact and
    order-upgrade reason lookup, redundant/forced decisions, duplicate
    deductions, restored exhaustion, root UNSAT, empty local explanations,
    Boolean/int separation, negative bounds, sparse domains, and the P1.1
    branch-relative deduction counterexample;
  * PENDING D1-activation expectations stated over INTERFACES §2.7's
    `RuntimeEvents`/counter API. The current public driver
    (`analyzedSolve`) never calls `RuntimeEvents.recordResolutions` /
    `recordBackjump` and `SearchStats` still has no `events` field, so there
    is NO runtime producer to observe; the predicates are stated but never
    applied to a value. No counter value is fabricated anywhere in this
    module, and no public backjump is claimed to have occurred.

How the checks run without a registered executable: each executable check is
a `def ... : Bool` accompanied by a kernel-checked `example ... := rfl` or
`by decide` (definitional/kernel evaluation). `native_decide` is NOT used (it
would introduce `Lean.ofReduceBool` and violate the audit boundary); this
module has no `sorry`/`admit`/`axiom`. The reference-driver checks are `Prop`s
proved from the certified theorems; `main` additionally runs them executably.

Registration (owned by T2/V1 — NOT done here, `lakefile.toml` untouched):
  [[lean_exe]]
  name = "tests_lcg_oracle"
  root = "Tests.UIP.OracleFixtures"

Dependencies: LeanFzn.Solver (the umbrella: the reference driver, the analyzer,
the C1 scheduler records, the A2 closure and the certified verdict theorems).
-/

import LeanFzn.Legacy.Solver.Propagation
import LeanFzn.Legacy.Solver.Chronological
import LeanFzn.Legacy.Solver.Reference
import LeanFzn.Legacy.Solver.UIP.SchedulerState
import LeanFzn.Legacy.Solver.UIP.SchedulerStep
import LeanFzn.Legacy.Solver.UIP.AnalysisEvents
import LeanFzn.Legacy.Solver.Propagation.ExplainedPropagation
import LeanFzn.Legacy.Solver.Propagation.BackjumpFrontier
import LeanFzn.Solver.Core.Enumerate
open LeanFzn.Compiler.Domains
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler LeanFzn.Integration


open LeanFzn LeanFzn.Solver LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Integration LeanFzn.Solver.Core

namespace T1Oracle

/-- A plain value-list box as compact domains. -/
def Ds (vss : List (List Value)) : List Domain := vss.map Dom.ofList

/-- Port helper for the pre-M2 `(remaining, chosen)` fixture frames: rebuild the
sparse `BranchFrame` through the positional bridge (chosen prefix becomes
singleton domains, decision order `List.range prefix.length`). -/
def legacyFrame (slots : List (List Value)) (chosen : Assignment) : BranchFrame :=
  SparseFrame.ofPrefixFrame (Ds slots, chosen)

/-! ## 0. Runtime-check vocabulary (same style as the existing suites) -/

/-- Pass/fail counter of the runtime suite (`main`, registered by T2). -/
structure TestState where
  passed : Nat
  failed : Nat

/-- Record one runtime check. -/
def TestState.check (st : TestState) (name : String) (ok : Bool) :
    IO TestState := do
  if ok then
    IO.println s!"ok {name}"
    pure { st with passed := st.passed + 1 }
  else
    IO.eprintln s!"FAIL {name}"
    pure { st with failed := st.failed + 1 }

/-- Integer value helper. -/
def vi (i : Int) : Value := .int i

/-- A reason-less trail entry (a decision). -/
def mkDec (l : Literal) (lvl : Nat) : TrailEntry :=
  { literal := l, level := lvl, reason := none }

/-- A trail entry with a reason clause. -/
def mkImp (l : Literal) (lvl : Nat) (c : Clause) : TrailEntry :=
  { literal := l, level := lvl, reason := some { clause := c } }

/-! ## 1. The independent exhaustive oracle

The oracle shares only the *specification* with the LeanFzn.Solver: the executable
leaf semantics (`DomConstraint.satisfiedB` on complete assignments and the
compiled clauses' `Literal.eval`), exactly the two conjuncts of
`chronologicalLeaf` that concern an enumerated complete assignment — fitting
the original box is guaranteed by `allAssigns` itself. It shares no search
reasoning: no propagator, no watched literal, no trail, no decision level,
no learning, no pruning, no backjumping. Its verdict is consequently a
genuinely independent reference for the tiny families below. -/

/-- The oracle's leaf predicate: every constraint and every original clause,
at the executable specification. -/
def oracleLeaf (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit)
    (a : Assignment) : Bool :=
  problem.constraints.all (fun c => DomConstraint.satisfiedB c a) &&
    problem.clauses.all (fun c => c.any fun l => decide (l.eval a = some true))

/-- Every complete assignment of the original boxes that satisfies the leaf
specification — the exhaustive solution list. -/
def oracleSolutions (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit) :
    List Assignment :=
  (allAssigns problem.domains).filter (oracleLeaf problem)

/-- The oracle's SAT verdict. -/
def oracleSat (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit) : Bool :=
  !(oracleSolutions problem).isEmpty

/-- The oracle's solution count (each family pins its expected count —
an independent numeric fact, derived here by enumeration, not by search). -/
def oracleCount (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit) : Nat :=
  (oracleSolutions problem).length

/-- The oracle's witness check: the claimed assignment is one the oracle
itself enumerated as a solution (hence it fits the boxes, satisfies every
constraint and satisfies every original clause). -/
def oracleWitnessOk (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit)
    (a : Assignment) : Bool :=
  (oracleSolutions problem).any fun b => b == a

/-- A witness accepted by the oracle is an enumerated complete assignment
satisfying the leaf specification. -/
theorem oracleWitnessOk_leaf {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {a : Assignment} (h : oracleWitnessOk problem a = true) :
    a ∈ allAssigns problem.domains ∧ oracleLeaf problem a = true := by
  obtain ⟨b, hb, hba⟩ := List.any_eq_true.mp h
  have hbe : b = a := LawfulBEq.eq_of_beq hba
  rw [hbe] at hb
  exact List.mem_filter.mp hb

/-! ### The reference under comparison

The reference is the CURRENT public driver: `solveDomWithStats` (which calls
`solveWithStats`, i.e. the measured `analyzedSolve` traversal). The scheduler
prepared by C1 is NOT involved. `referenceDriver` names the exact
`analyzedSolve` root call, so the certified verdict theorems can be applied
to it without unfolding the well-founded recursion (which the kernel cannot
reduce — hence the `Prop`-level comparison below). -/

/-- The reference driver's root call, definitionally the `analyzedSolve` call
`solveWithStats` performs for a `DomConstraint` problem. -/
def referenceDriver (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit) :
    FrontierResult × SearchStats :=
  analyzedSolve (chronologicalLeaf problem DomConstraint.satisfiedB)
    (domPruningKit (feasibilityProblem problem)) [(problem.domains, [])]
    problem.clauses {}

/-- The public entry point's first component as a match on the reference
driver's verdict (the only map `solveWithStats` performs). -/
theorem solveDomWithStats_fst_eq (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit) :
    (solveDomWithStats problem).1 =
      (match (referenceDriver problem).1 with
       | .sat a => SearchResult.sat a
       | .unsat => SearchResult.unsat) := by
  unfold solveDomWithStats solveWithStats referenceDriver
  rfl

/-- A driver verdict maps back to a public SAT verdict. -/
theorem solveDomWithStats_sat_of_driver {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {a : Assignment} (h : (referenceDriver problem).1 = .sat a) :
    (solveDomWithStats problem).1 = .sat a := by
  rw [solveDomWithStats_fst_eq, h]

/-- A public SAT verdict comes from a driver SAT verdict. -/
theorem driver_sat_of_solveDomWithStats {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {a : Assignment} (h : (solveDomWithStats problem).1 = .sat a) :
    (referenceDriver problem).1 = .sat a := by
  cases hr : (referenceDriver problem).1 with
  | sat x =>
      rw [solveDomWithStats_fst_eq] at h
      simp only [hr] at h
      cases h
      rfl
  | unsat =>
      rw [solveDomWithStats_fst_eq, hr] at h
      exact absurd h (by simp)

/-- A public UNSAT verdict comes from a driver UNSAT verdict. -/
theorem driver_unsat_of_solveDomWithStats {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (h : (solveDomWithStats problem).1 = .unsat) :
    (referenceDriver problem).1 = .unsat := by
  cases hr : (referenceDriver problem).1 with
  | sat x =>
      rw [solveDomWithStats_fst_eq, hr] at h
      exact absurd h (by simp)
  | unsat => rfl

/-- The reference driver is total: it never reports `unknown` (it is the
fuel-free `analyzedSolve` traversal; this is `solve_total` restated for the
public entry point). Used to pin the verdict of a family from the oracle. -/
theorem solveDomWithStats_ne_unknown (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit) :
    (solveDomWithStats problem).1 ≠ SearchResult.unknown := by
  have h := solve_total problem DomConstraint.satisfiedB
    (problem.constraints.filterMap propagatorOfProved)
    (domPruningKit (feasibilityProblem problem))
  simpa [LeanFzn.Solver.Chronological.solve, solveDomWithStats, solveWithStats] using h

/-- The problem's original clauses are entailed by the compiled leaf. -/
theorem entailedDB_clauses (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit) :
    EntailedDB (chronologicalLeaf problem DomConstraint.satisfiedB)
      problem.clauses := by
  intro c hc a ha
  rw [chronologicalLeaf, Bool.and_eq_true, Bool.and_eq_true] at ha
  obtain ⟨l, hl, hd⟩ := List.any_eq_true.mp (List.all_eq_true.mp ha.2.2 c hc)
  exact ⟨l, hl, of_decide_eq_true hd⟩

/-! ### Oracle comparison, both directions (real proofs, no evaluation)

The comparison is stated as a `Prop` per the T1 instructions: the reference
driver is well-founded-recursive, so `rfl`/`decide` cannot evaluate its
verdict; the certified verdict theorems turn "whatever the driver returns"
into an oracle statement. -/

/-- SAT direction: a SAT verdict of the current reference carries a witness
the exhaustive oracle accepts (so the driver's witness satisfies every
constraint and every clause, and fits the original boxes). -/
theorem reference_sat_oracleWitness {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {a : Assignment} (h : (solveDomWithStats problem).1 = .sat a) :
    oracleWitnessOk problem a = true := by
  have h' := driver_sat_of_solveDomWithStats h
  have hl := analyzedSolve_sat_leaf _ _ _ _ _ a h'
  rw [chronologicalLeaf, Bool.and_eq_true, Bool.and_eq_true] at hl
  obtain ⟨hlen, hget⟩ := fitsB_iff.mp hl.1
  have hmem := mem_allAssigns_of_getElem? problem.domains a hlen hget
  have hlf : oracleLeaf problem a = true := by
    rw [oracleLeaf, Bool.and_eq_true]
    exact ⟨hl.2.1, hl.2.2⟩
  rw [oracleWitnessOk, List.any_eq_true]
  refine ⟨a, ?_, by simp⟩
  rw [oracleSolutions, List.mem_filter]
  exact ⟨hmem, hlf⟩

/-- UNSAT direction: an UNSAT verdict of the current reference means the
exhaustive oracle finds no solution at all. -/
theorem reference_unsat_oracleSat {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (h : (solveDomWithStats problem).1 = .unsat) : oracleSat problem = false := by
  have h' := driver_unsat_of_solveDomWithStats h
  have hex := analyzedSolve_unsat_excludes _ _ _ _ _ (entailedDB_clauses problem) h'
  have hempty : oracleSolutions problem = [] := by
    rw [oracleSolutions, List.filter_eq_nil_iff]
    intro a ha hleaf
    rw [oracleLeaf, Bool.and_eq_true] at hleaf
    have hl : chronologicalLeaf problem DomConstraint.satisfiedB a = true := by
      rw [chronologicalLeaf, Bool.and_eq_true, Bool.and_eq_true]
      exact ⟨fitsB_iff.mpr (allAssigns_fits _ _ ha), hleaf.1, hleaf.2⟩
    have hf := hex a
      ⟨(problem.domains, []), List.mem_singleton_self _, a, ha, by simp⟩
    rw [hl] at hf
    exact absurd hf (by simp)
  simp [oracleSat, hempty]

/-- Verdict pinning, SAT: an oracle-accepted witness proves the reference
verdict is SAT (it cannot be `unsat` by `analyzedSolve_unsat_excludes`, nor
`unknown` by `solve_total`). -/
theorem reference_sat_of_oracle_witness {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {a₀ : Assignment} (h : oracleWitnessOk problem a₀ = true) :
    ∃ a, (solveDomWithStats problem).1 = .sat a := by
  obtain ⟨hmem, hleaf⟩ := oracleWitnessOk_leaf h
  cases hd : (solveDomWithStats problem).1 with
  | sat a => exact ⟨a, rfl⟩
  | unknown => exact absurd hd (solveDomWithStats_ne_unknown problem)
  | unsat =>
      exfalso
      have h' := driver_unsat_of_solveDomWithStats hd
      rw [oracleLeaf, Bool.and_eq_true] at hleaf
      have hl : chronologicalLeaf problem DomConstraint.satisfiedB a₀ = true := by
        rw [chronologicalLeaf, Bool.and_eq_true, Bool.and_eq_true]
        exact ⟨fitsB_iff.mpr (allAssigns_fits _ _ hmem), hleaf.1, hleaf.2⟩
      have hf := (analyzedSolve_unsat_excludes _ _ _ _ _
        (entailedDB_clauses problem) h') a₀
        ⟨(problem.domains, []), List.mem_singleton_self _, a₀, hmem, by simp⟩
      rw [hl] at hf
      exact absurd hf (by simp)

/-- Verdict pinning, UNSAT: an empty oracle solution list proves the
reference verdict is UNSAT (it cannot be `sat` by `analyzedSolve_sat_leaf`,
nor `unknown` by `solve_total`). -/
theorem reference_unsat_of_oracleSat_false {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (h : oracleSat problem = false) : (solveDomWithStats problem).1 = .unsat := by
  have he : oracleSolutions problem = [] := by
    cases hs : oracleSolutions problem with
    | nil => rfl
    | cons b rest => rw [oracleSat, hs] at h; exact absurd h (by simp)
  cases hd : (solveDomWithStats problem).1 with
  | unsat => rfl
  | unknown => exact absurd hd (solveDomWithStats_ne_unknown problem)
  | sat a =>
      exfalso
      have h' := driver_sat_of_solveDomWithStats hd
      have hl := analyzedSolve_sat_leaf _ _ _ _ _ a h'
      rw [chronologicalLeaf, Bool.and_eq_true, Bool.and_eq_true] at hl
      obtain ⟨hlen, hget⟩ := fitsB_iff.mp hl.1
      have hmem := mem_allAssigns_of_getElem? problem.domains a hlen hget
      have hlf : oracleLeaf problem a = true := by
        rw [oracleLeaf, Bool.and_eq_true]
        exact ⟨hl.2.1, hl.2.2⟩
      have hnone : oracleLeaf problem a = false := by
        rw [oracleSolutions, List.filter_eq_nil_iff] at he
        cases hl' : oracleLeaf problem a with
        | false => rfl
        | true => exact absurd hl' (he a hmem)
      rw [hnone] at hlf
      exact absurd hlf (by simp)

/-- The reference-vs-oracle agreement proposition for one input: whatever the
current public reference returns, the exhaustive oracle confirms it. -/
def ReferenceAgrees (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit) : Prop :=
  (∀ a, (solveDomWithStats problem).1 = .sat a →
      oracleWitnessOk problem a = true) ∧
    ((solveDomWithStats problem).1 = .unsat → oracleSat problem = false)

/-- The agreement proposition holds for EVERY `DomConstraint` problem — the
generic content of the per-family checks below. -/
theorem referenceAgrees (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit) :
    ReferenceAgrees problem :=
  ⟨fun _ h => reference_sat_oracleWitness h, fun h => reference_unsat_oracleSat h⟩

/-- Executable (runtime) agreement check used by `main`: compares the actual
verdict against the oracle and validates a SAT witness. The kernel-level
companion is `ReferenceAgrees`; this `Bool` version runs in the suite when
T2 registers it (the kernel cannot reduce the well-founded driver, which is
exactly why the proof-level check is stated as a `Prop`). -/
def referenceAgreesB (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit) : Bool :=
  match (solveDomWithStats problem).1 with
  | .sat a => oracleWitnessOk problem a
  | .unsat => !oracleSat problem
  | .unknown => false

/-! ## 2. Family problems and the kernel-checked oracle comparison -/

/-- Two int slots, `x ≠ y` (SAT; two oracle solutions). -/
def famTwoNeInt : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
  { names := [], domains := Ds [[.int 0, .int 1], [.int 0, .int 1]],
    constraints := [.neSlot 0 1], objective := (), clauses := [] }

/-- Two singleton int slots, `x ≠ y` (UNSAT at the root). -/
def famNeUnsat : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
  { names := [], domains := Ds [[.int 1], [.int 1]],
    constraints := [.neSlot 0 1], objective := (), clauses := [] }

/-- Two Boolean slots, `y = ¬x` (SAT; Boolean values, two oracle solutions). -/
def famBoolNot : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
  { names := [], domains := Ds [[.bool true, .bool false], [.bool true, .bool false]],
    constraints := [.boolNotSlot 0 1], objective := (), clauses := [] }

/-- Negative bounds: `x ≤ y` over `{-3,2} × {-2,1}` (SAT; two solutions). -/
def famNegBounds : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
  { names := [], domains := Ds [[.int (-3), .int 2], [.int (-2), .int 1]],
    constraints := [.leSlot 0 1], objective := (), clauses := [] }

/-- Sparse domains `{0,2,5} × {5}` with `y ≤ x` (SAT; exactly one solution,
`(5,5)`, which only the sparse reading admits). -/
def famSparse : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
  { names := [], domains := Ds [[.int 0, .int 2, .int 5], [.int 5]],
    constraints := [.leSlot 1 0], objective := (), clauses := [] }

/-- Root UNSAT: `x = y` over `{3} × {1}` conflicts at level 0. -/
def famRootUnsat : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
  { names := [], domains := Ds [[.int 3], [.int 1]],
    constraints := [.eqSlot 0 1], objective := (), clauses := [] }

/-- A six-literal clause over two 3-valued slots
(`x > 0 ∨ x > 1 ∨ x > 2 ∨ y > 0 ∨ y > 1 ∨ y > 2`, i.e. `x ≥ 1 ∨ y ≥ 1`):
the long-clause scan case of the executable reference (SAT; 8 solutions). -/
def famLongClause : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
  { names := [], domains := Ds [[.int 0, .int 1, .int 2], [.int 0, .int 1, .int 2]],
    constraints := [], objective := (),
    clauses := [[negLe 0 0, negLe 0 1, negLe 0 2, negLe 1 0, negLe 1 1, negLe 1 2]] }

/-- The runtime family battery: name, problem, expected oracle solution
count. -/
def familyBattery : List (String × LeanFzn.Solver.Propagation.Problem DomConstraint Unit × Nat) :=
  [ ("two-ne-int", famTwoNeInt, 2)
  , ("ne-unsat", famNeUnsat, 0)
  , ("bool-not", famBoolNot, 2)
  , ("neg-bounds", famNegBounds, 2)
  , ("sparse", famSparse, 1)
  , ("root-unsat", famRootUnsat, 0)
  , ("long-clause", famLongClause, 8) ]

-- Independent counts (kernel-checked by enumeration).
example : oracleCount famTwoNeInt = 2 := rfl
example : oracleCount famNeUnsat = 0 := rfl
example : oracleCount famBoolNot = 2 := rfl
example : oracleCount famNegBounds = 2 := rfl
example : oracleCount famSparse = 1 := rfl
example : oracleCount famRootUnsat = 0 := rfl
example : oracleCount famLongClause = 8 := rfl

-- Oracle-accepted witnesses (kernel-checked; the oracle enumerates them).
example : oracleWitnessOk famTwoNeInt [.int 0, .int 1] = true := rfl
example : oracleWitnessOk famBoolNot [.bool true, .bool false] = true := rfl
example : oracleWitnessOk famNegBounds [.int (-3), .int (-2)] = true := rfl
example : oracleWitnessOk famSparse [.int 5, .int 5] = true := rfl
example : oracleWitnessOk famLongClause [.int 0, .int 1] = true := rfl

-- The exhaustive oracle says UNSAT for the two unsatisfiable families.
example : oracleSat famNeUnsat = false := rfl
example : oracleSat famRootUnsat = false := rfl

-- Verdict pins: every family's reference verdict is forced by the oracle
-- (SAT families by an oracle witness, UNSAT families by the empty oracle
-- solution list) — real proofs, no driver evaluation.
example : ∃ a, (solveDomWithStats famTwoNeInt).1 = .sat a :=
  reference_sat_of_oracle_witness (a₀ := [.int 0, .int 1]) (by rfl)
example : ∃ a, (solveDomWithStats famBoolNot).1 = .sat a :=
  reference_sat_of_oracle_witness (a₀ := [.bool true, .bool false]) (by rfl)
example : ∃ a, (solveDomWithStats famNegBounds).1 = .sat a :=
  reference_sat_of_oracle_witness (a₀ := [.int (-3), .int (-2)]) (by rfl)
example : ∃ a, (solveDomWithStats famSparse).1 = .sat a :=
  reference_sat_of_oracle_witness (a₀ := [.int 5, .int 5]) (by rfl)
example : ∃ a, (solveDomWithStats famLongClause).1 = .sat a :=
  reference_sat_of_oracle_witness (a₀ := [.int 0, .int 1]) (by rfl)
example : (solveDomWithStats famNeUnsat).1 = .unsat :=
  reference_unsat_of_oracleSat_false (by rfl)
example : (solveDomWithStats famRootUnsat).1 = .unsat :=
  reference_unsat_of_oracleSat_false (by rfl)

-- And the full two-directional agreement proposition for every family.
example : ReferenceAgrees famTwoNeInt := referenceAgrees _
example : ReferenceAgrees famNeUnsat := referenceAgrees _
example : ReferenceAgrees famBoolNot := referenceAgrees _
example : ReferenceAgrees famNegBounds := referenceAgrees _
example : ReferenceAgrees famSparse := referenceAgrees _
example : ReferenceAgrees famRootUnsat := referenceAgrees _
example : ReferenceAgrees famLongClause := referenceAgrees _

/-! ## 3. Analyzer fixtures: multiple resolutions, irrelevant level, long
reason, exact and order-upgrade lookup -/

/-- THE MULTI-RESOLUTION TRAIL. Chronological entries:

  * level 1: decision `x0 ≤ 5`;
  * level 2: decision `x3 ≠ 1` — an IRRELEVANT level (never jumped onto);
  * level 3: decision `x1 ≤ 7`;
  * level 3: `x2 ≤ 9`, reason `[x2 ≤ 9, ¬(x0 ≤ 5)]`;
  * level 3: `x4 ≤ 2`, reason `[x4 ≤ 2, ¬(x2 ≤ 9)]`.

The conflict `[¬(x1 ≤ 7), ¬(x2 ≤ 9), ¬(x4 ≤ 2)]` is falsified at level 3;
resolving the two latest level-3 marks consumes BOTH reasons (two pivot
expansions), records exactly one below-level falsifier `¬(x0 ≤ 5)` at
level 1, and leaves `x1 ≤ 7` as the first UIP — a 3 → 1 jump over the
irrelevant level 2. -/
def mTrail : List TrailEntry :=
  [ mkDec (posLe 0 5) 1
  , mkDec (posNe 3 1) 2
  , mkDec (posLe 1 7) 3
  , mkImp (posLe 2 9) 3 [posLe 2 9, negLe 0 5]
  , mkImp (posLe 4 2) 3 [posLe 4 2, negLe 2 9] ]

/-- The original box of the analyzer fixtures (R1a: the LCG analyzer reads
it for the root drop): five integer slots with domain `0..12`. -/
def oOrig : List Domain :=
  List.replicate 5 (Dom.ofList ((List.range 13).map fun k => Value.int (Int.ofNat k)))

/-- The multi-resolution conflict clause. -/
def mConflict : Clause := [negLe 1 7, negLe 2 9, negLe 4 2]

/-- The multi-resolution analysis result. -/
def mAnalysis : Option (List (Literal × Nat) × Literal) :=
  analyzeTrail mTrail 3 mConflict

/-- The recorded below-level falsifiers of the multi-resolution fixture. -/
def mBelow : List (Literal × Nat) := mAnalysis.elim [] (fun p => p.1)

/-- The first UIP of the multi-resolution fixture (default for `none`). -/
def mUip : Literal := mAnalysis.elim (posLe 0 5) (fun p => p.2)

/-- The backjump level the scheduler's UIP constructor computes for the
multi-resolution fixture. -/
def mTargetLevel : Nat := (ConflictAnalysis.ofUIP mBelow mUip).backjumpLevel

-- Two reason resolutions: exactly one below-level pair (level 1) and the
-- level-3 decision `x1 ≤ 7` as the first UIP.
example : analyzeTrail mTrail 3 mConflict = some ([(negLe 0 5, 1)], posLe 1 7) := rfl
example : mBelow = [(negLe 0 5, 1)] := rfl
example : mBelow.all (fun p => p.2 < 3) = true := rfl
example : mUip = posLe 1 7 := rfl

-- A COMPLETED trace (13 transitions), not a numeric allowance comparison:
-- the analyzer stops semantically well inside the executable fuel.
example : analyzeTrace oOrig mTrail 3 (analysisFuel mTrail mConflict)
    (initAnalysisState mConflict) = some (13, some ([(negLe 0 5, 1)], posLe 1 7)) := by
  decide

-- The jump skips the irrelevant level 2: target 1 from source level 3.
example : mTargetLevel = 1 := rfl
example : mTargetLevel < 3 := by decide
example : (ConflictAnalysis.ofUIP mBelow mUip).learned = [negLe 1 7, negLe 0 5] := rfl
example : (ConflictAnalysis.ofUIP mBelow mUip).asserting = negLe 1 7 := rfl

/-- THE LONG-REASON TRAIL. Twelve level-1 decisions `x3 ≤ 0 … x3 ≤ 11`,
then a level-2 decision `x1 ≤ 10` and a level-2 implication `x2 ≤ 3` whose
reason is the 13-literal clause `[x2 ≤ 3, ¬(x3 ≤ 0), …, ¬(x3 ≤ 11)]`. The
conflict `[¬(x2 ≤ 3), ¬(x1 ≤ 10)]` resolves the single long reason: all
twelve of its side literals are falsified at level 1 and become the
below-level part of the learned clause. -/
def longTrail : List TrailEntry :=
  (List.range 12).map (fun k => mkDec (posLe 3 (Int.ofNat k)) 1)
  ++ [ mkDec (posLe 1 10) 2
     , mkImp (posLe 2 3) 2
         (posLe 2 3 :: (List.range 12).map (fun k => negLe 3 (Int.ofNat k))) ]

/-- The long-reason conflict clause. -/
def longConflict : Clause := [negLe 2 3, negLe 1 10]

/-- The expected below-level falsifiers of the long-reason fixture (the
resolver records them newest-mark-first, so the twelve pairs are listed in
descending bound order). -/
def longBelow : List (Literal × Nat) :=
  (List.range 12).map (fun k => (negLe 3 (Int.ofNat (11 - k)), 1))

-- The clause has 13 literals and the learned clause is 13 literals wide.
example : (posLe 2 3 :: (List.range 12).map (fun k => negLe 3 (Int.ofNat k))).length = 13 := rfl
example : longBelow.length = 12 := rfl
example : analyzeTrail longTrail 2 longConflict = some (longBelow, posLe 1 10) := rfl

/-- R1a: the LCG analyzer (semantic weakening) learns the twelve side
literals `x3 > k` as the single weakened literal `x3 > 0` — the EARLIEST
entry implying every `x3 ≤ k` is the decision `x3 ≤ 0`. The historical
`analyzeTrail` above still records all twelve. -/
def longBelowLcg : List (Literal × Nat) := [(negLe 3 0, 1)]

-- COMPLETED long-reason trace (19 transitions): the semantic stop, observed,
-- not an allowance-comparison.
example : analyzeTrace oOrig longTrail 2 (analysisFuel longTrail longConflict)
    (initAnalysisState longConflict) = some (19, some (longBelowLcg, posLe 1 10)) := by
  decide
example : (analyzeTrace oOrig longTrail 2 (analysisFuel longTrail longConflict)
    (initAnalysisState longConflict)).isSome = true := by decide

-- EXACT reason lookup: the falsifier `x0 ≤ 5` is found by exact normalized
-- match for the literal `¬(x0 ≤ 5)`.
example : findEntryOf [mkDec (posLe 0 5) 1] (posLe 0 5) = some (mkDec (posLe 0 5) 1) := rfl
example : analyzeTrail [mkDec (posLe 0 5) 1] 1 [negLe 0 5] = some ([], posLe 0 5) := rfl

-- ORDER-UPGRADE lookup: the conflict literal `¬(x0 ≤ 5)` has NO exact
-- negation on the trail (`x0 ≤ 4` is recorded), so the exact lookup fails
-- and the upgrade weakens it to `¬(x0 ≤ 4)`, whose negation IS the trail
-- entry. The analysis still succeeds on that upgraded falsifier.
example : findEntryOf [mkDec (posLe 0 4) 1] (posLe 0 5) = none := rfl
example : orderUpgrade [mkDec (posLe 0 4) 1] (negLe 0 5) = negLe 0 4 := rfl
example : findEntryOf [mkDec (posLe 0 4) 1]
    (orderUpgrade [mkDec (posLe 0 4) 1] (negLe 0 5)).negate
      = some (mkDec (posLe 0 4) 1) := rfl
example : analyzeTrail [mkDec (posLe 0 4) 1] 1 [negLe 0 5] = some ([], posLe 0 4) := rfl

-- Boolean normalization bridge of the same lookup: `¬(b = false)` finds the
-- canonical positive entry `b = true`.
example : (posBool 0 false).negate.norm = posBool 0 true := rfl
example : findEntryOf [mkDec (posBool 0 true) 1] (posBool 0 false).negate
    = some (mkDec (posBool 0 true) 1) := rfl

/-! ## 4. The P1.1 branch-relative deduction counterexample

Under the decision `x = false`, the entailed clause
`¬(x = false) ∨ y = true` is unit on `y = true`: the deduction's pivot is
TRUE at every leaf solution the state represents, but FALSE at the global
solution `x = true, y = false`. Both halves are checked — the second by
evaluating the leaf at that solution, the first by a real proof. -/

/-- The `x ≠ y` problem behind the counterexample. -/
def xyProblem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
  { names := [], domains := Ds [[.bool true, .bool false], [.bool true, .bool false]],
    constraints := [.neSlot 0 1], objective := (), clauses := [] }

/-- The counterexample leaf predicate: the compiled `x ≠ y` leaf the
reference driver uses. -/
def xyLeaf : Assignment → Bool :=
  chronologicalLeaf xyProblem DomConstraint.satisfiedB

/-- The globally entailed reason clause `¬(x = false) ∨ y = true`. -/
def xyClause : Clause := [(posBool 0 false).negate, posBool 1 true]

/-- The decision entry: `x = false` at level 1. -/
def xyDecision : TrailEntry := mkDec (posBool 0 false) 1

/-- The decided child frame: slot 0 pinned to `false`, remaining slots still
full (the decision lives in the prefix, so `fullDomains` reads it). -/
def xyFrame : BranchFrame := legacyFrame [[.bool true, .bool false]] [.bool false]

/-- The branch state: the decision on the trail and the entailed clause in
the global database. -/
def xyState : BranchState xyLeaf :=
  { frame := xyFrame, trail := [xyDecision], level := 1, learned := [xyClause] }

-- The deduction is selected, on the expected pivot, with the expected
-- reason and the expected narrowed frame.
example : (explainedDeduction [] [] xyState).isSome = true := rfl
example : (explainedDeduction [] [] xyState).map (fun d => d.literal)
    = some (posBool 1 true) := rfl
example : (explainedDeduction [] [] xyState).map (fun d => d.reason)
    = some xyClause := rfl
example : (explainedDeduction [] [] xyState).map (fun d => d.frame)
    = some (legacyFrame [[.bool true]] [.bool false]) := rfl

-- GLOBAL FALSITY of the pivot: `x = true, y = false` is an `x ≠ y` solution
-- at which `y = true` is false.
example : xyLeaf [.bool true, .bool false] = true := rfl
example : (posBool 1 true).norm.eval [.bool true, .bool false] = some false := rfl
example : ¬ (∀ a, xyLeaf a = true →
    (posBool 1 true).norm.eval a = some true) := by
  intro h
  have h1 := h [.bool true, .bool false] (by rfl)
  rw [show (posBool 1 true).norm.eval [.bool true, .bool false] = some false
    from rfl] at h1
  exact absurd h1 (by simp)

-- BRANCH-RELATIVE TRUTH of the pivot, proved: the trail pins `x = false`,
-- and the learned clause then forces `y = true` — the exact content of the
-- withdrawn global `literalSound` and its branch-relative replacement.
theorem xy_pivot_branch_relative :
    ∀ a, xyLeaf a = true → xyState.Represents a →
      (posBool 1 true).norm.eval a = some true := by
  intro a _ hrep
  obtain ⟨-, htrail, hlearned⟩ := hrep
  have hdec : (posBool 0 false).eval a = some true := by
    have h := htrail xyDecision (by
      show xyDecision ∈ xyState.trail
      rw [xyState]
      exact List.mem_singleton_self _)
    simpa [xyDecision, mkDec] using h
  have hsat : ∃ l ∈ xyClause, l.eval a = some true :=
    hlearned xyClause (by
      show xyClause ∈ xyState.learned
      rw [xyState]
      exact List.mem_cons_self ..)
  obtain ⟨l, hl, hleval⟩ := hsat
  rw [xyClause] at hl
  rcases List.mem_cons.mp hl with hneg | hpos
  · exfalso
    have hfalse : (posBool 0 false).eval a = some false :=
      (Literal.eval_negate_false_iff (posBool 0 false) a).mp
        (by rw [← hneg]; exact hleval)
    rw [hdec] at hfalse
    exact absurd hfalse (by simp)
  · have hl' : l = posBool 1 true := List.mem_singleton.mp hpos
    rw [hl'] at hleval
    rwa [Literal.norm_eval]

/-! ## 5. Component fixtures for the remaining P1.5 families -/

/-! ### 5.1 Propagation after an assertion -/

/-- The pre-assertion box: two slots, both `{0,1}`. -/
def paFrame : BranchFrame := legacyFrame [[.int 0, .int 1], [.int 0, .int 1]] []

/-- The state after the assertion `x0 = 0` has been enqueued, its reason
recorded, and the assertion narrowing applied — the shape
`learnBackjumpAssert`'s successor has (restored frame, one asserting entry,
narrowed frame, reason clause in the database). The frame is definitionally
the assertion's filter of the pre-assertion box (checked below), and the
database's second clause `[x0 ≠ 0, x1 ≤ 0]` becomes unit only because the
assertion removed `0` from slot 0. -/
def paState : BranchState (fun _ : Assignment => true) :=
  { frame := legacyFrame [[.int 0], [.int 0, .int 1]] [],
    trail := [mkImp (negNe 0 0) 1 [negNe 0 0]], level := 1,
    learned := [[negNe 0 0], [posNe 0 0, posLe 1 0]] }

-- The narrowed frame is exactly the assertion's filter of the pre-box.
example : filterFrame (negNe 0 0) paFrame
    = some (legacyFrame [[.int 0], [.int 0, .int 1]] []) := rfl

-- Propagation resumes: the assertion made `x0 ≠ 0` impossible, so the
-- surviving unit `x1 ≤ 0` is selected and narrows slot 1.
example : (explainedDeduction [] [] paState).isSome = true := rfl
example : (explainedDeduction [] [] paState).map (fun d => d.literal)
    = some (posLe 1 0) := rfl
example : (explainedDeduction [] [] paState).map (fun d => d.reason)
    = some [posNe 0 0, posLe 1 0] := rfl
example : (explainedDeduction [] [] paState).map (fun d => d.frame)
    = some (legacyFrame [[.int 0], [.int 0]] []) := rfl
example : explainedStep [] [] paState
    = .narrow (posLe 1 0) [posNe 0 0, posLe 1 0] [] := rfl

/-! ### 5.2 Duplicate deductions (skip repeated deductions) -/

/-- A database unit `x0 ≠ 0` on the box `{0,1}`. -/
def dupState : BranchState (fun _ : Assignment => true) :=
  { frame := legacyFrame [[.int 0, .int 1]] [], trail := [], level := 0,
    learned := [[posNe 0 0]] }

/-- The successor after the unit was consumed: `0` removed, one entry
recorded. -/
def dupState2 : BranchState (fun _ : Assignment => true) :=
  narrowState dupState (legacyFrame [[.int 1]] []) (posNe 0 0) [posNe 0 0] []

-- The first dispatch is productive; the re-dispatch of the SAME deduction is
-- skipped (non-productive and already recorded), so the closure would stop.
example : (explainedDeduction [] [] dupState).isSome = true := rfl
example : (explainedDeduction [] [] dupState).map (fun d => d.literal)
    = some (posNe 0 0) := rfl
example : (explainedDeduction [] [] dupState).map (fun d => d.frame)
    = some (legacyFrame [[.int 1]] []) := rfl
example : explainedDeduction [] [] dupState2 = none := rfl
example : TrailRedundant dupState2.trail (posNe 0 0) = true := rfl

/-! ### 5.3 Redundant / forced decisions -/

/-- A state whose trail already carries `x0 = 1` while the frame still
admits `{0,1,2}`: the database unit `x0 = 1` is productive (it would remove
two values) but its normalized literal is already recorded, so the
duplicate-safe policy skips it (`.stable`, no entry). -/
def redState : BranchState (fun _ : Assignment => true) :=
  { frame := legacyFrame [[.int 0, .int 1, .int 2]] [], trail := [mkDec (negNe 0 1) 1],
    level := 1, learned := [[negNe 0 1]] }

example : productive (negNe 0 1) redState.frame = true := rfl
example : TrailRedundant redState.trail (negNe 0 1) = true := rfl
example : explainedStep [] [] redState = .stable := rfl
example : explainedDeduction [] [] redState = none := rfl

/-- A root scheduler configuration over a two-value box. -/
def rootCfg : SchedulerConfig (fun _ : Assignment => true) :=
  SchedulerConfig.init (leaf := fun _ => true) (Ds [[.int 0, .int 1]]) [] []

-- FORCED decisions: pinning a singleton head domain is not counted as a
-- decision (`vs.isEmpty` ⇒ 0), while a genuine branch counts one.
example : (stepDecide rootCfg 0 (.int 0) Dom.empty (negNe 0 0)).stats.decisions = 0 := rfl
example : (stepDecide rootCfg 0 (.int 0) (Dom.ofList [.int 1]) (negNe 0 0)).stats.decisions = 1 := rfl
example : (stepDecide rootCfg 0 (.int 0) Dom.empty (negNe 0 0)).branch.level = 1 := rfl

/-! ### 5.4 Restored exhaustion -/

/-- A configuration whose permanent log holds one prefix region. -/
def exCfg : SchedulerConfig (fun _ : Assignment => true) :=
  { orig := Ds [[.int 1, .int 0]], original := [], props := [],
    branch := { frame := legacyFrame [[.int 1, .int 0]] [], trail := [], level := 0,
                learned := [] },
    checkpoints := [], pending := [],
    log := ({} : ExhaustionLog).register
      (DeadRegion.byPrefix ([.int 1, .int 0] : Assignment)) }

/-- The plan's checkpoint state (level 0). -/
def exCpState : BranchState (fun _ : Assignment => true) :=
  { frame := legacyFrame [[.int 1, .int 0]] [], trail := [], level := 0, learned := [] }

/-- A level-0 plan asserting `x0 = 1`. -/
def exPlan : BackjumpPlan (fun _ : Assignment => true) :=
  { target := 0, checkpoint := exCpState, asserting := negNe 0 1,
    learned := [negNe 0 1] }

/-- Recorded conflict evidence for the restored-exhaustion fixture. -/
def exEv : ConflictEvidence :=
  { clause := [negNe 0 1], learned := [], analysis := none }

/-- The restored/narrowed state of the jump. -/
def exRestored : BranchState (fun _ : Assignment => true) :=
  { frame := legacyFrame [[.int 1]] [.int 0], trail := [], level := 0, learned := [] }

-- The jump leaves the permanent log untouched: the registered region still
-- answers, and the §2.7 counters are recorded at the site.
example : (stepLearnBackjumpAssert exCfg exPlan exEv exRestored).log.regions.any
    (fun r => r.mem [.int 1, .int 0]) = true := rfl
example : (stepLearnBackjumpAssert exCfg exPlan exEv exRestored).log.regions.length = 1 := rfl
example : (stepLearnBackjumpAssert exCfg exPlan exEv exRestored).events.backjumps = 1 := rfl
example : (stepLearnBackjumpAssert exCfg exPlan exEv exRestored).events.sourceLevel = 0 := rfl
example : (stepLearnBackjumpAssert exCfg exPlan exEv exRestored).events.targetLevel = 0 := rfl
example : (stepLearnBackjumpAssert exCfg exPlan exEv exRestored).events.assertingEnqueues = 1 := rfl

-- C1's permanence theorem, cited at a concrete log.
example (log : ExhaustionLog) {p : DeadRegion} (h : p ∈ log.regions)
    (extra : List DeadRegion) :
    p ∈ (extra.foldl ExhaustionLog.register log).regions :=
  ExhaustionLog.registered_permanent h extra

-- Region semantics used by the registration sites.
example : (DeadRegion.byPrefix ([.int 1, .int 0] : Assignment)).mem [.int 1, .int 0]
    = true := rfl
example : (DeadRegion.byPrefix ([.int 1, .int 0] : Assignment)).mem [.int 0, .int 1]
    = false := rfl

/-! ### 5.5 Root UNSAT and empty local explanations -/

-- The root-conflict dispatch reports UNSAT only for a NONEMPTY reported
-- clause at level 0; the empty clause list is the LOCAL case.
example : conflictStep rootCfg [[negLe 0 5]] [] = .unsat := rfl
def localExcludeTag : Bool :=
  match conflictStep rootCfg [] [] with
  | .localExclude _ => true
  | _ => false
example : localExcludeTag = true := rfl

/-- A configuration above level 0. -/
def lvlCfg : SchedulerConfig (fun _ : Assignment => true) :=
  { rootCfg with branch := { rootCfg.branch with level := 2 } }

def analyzeTag : Bool :=
  match conflictStep lvlCfg [[negLe 0 5]] [] with
  | .analyzeConflict _ _ => true
  | _ => false
example : analyzeTag = true := rfl

-- Classification: an empty clause is LOCAL at every level and never root.
example : ConflictShape.ofConflict 0 [] = .local := rfl
example : ConflictShape.ofConflict 3 [] = .local := rfl
example : ConflictShape.ofConflict 0 [posLe 0 1] = .root := rfl
example : ConflictShape.ofConflict 3 [posLe 0 1] = .analyzable := rfl

/-- A branch whose learned unit clause is already fully falsified by the
frame. -/
def deadState : BranchState (fun _ : Assignment => true) :=
  { frame := legacyFrame [[.int 5]] [], trail := [], level := 0, learned := [[posLe 0 0]] }

-- The exclusion carries an EMPTY local explanation (`scanDatabase`'s
-- `.conflict []`), never a claim about the whole problem.
example : explainedStep [] [] deadState = .excluded [] := rfl

/-! ### 5.6 Boolean/int separation, negative bounds, sparse domains -/

-- Boolean decisions use the canonical positive pin; integer decisions use
-- the value-equality literal; unsupported value shapes make no decision.
example : valueLiteral 0 (.bool true) = some (posBool 0 true) := rfl
example : valueLiteral 0 (.bool false) = some (posBool 0 false) := rfl
example : valueLiteral 1 (.int 3) = some (negNe 1 3) := rfl
example : valueLiteral 0 (.array []) = none := rfl
example : valueLiteral 0 (.setOfInt (.enumeration [])) = none := rfl
example : Literal.boolOfSlot 0 false = posBool 0 false := rfl

-- The typed 0/1 view Boolean order literals read.
example : Value.intView (.bool true) = some 1 := rfl
example : Value.intView (.bool false) = some 0 := rfl
example : Value.intView (.int (-3)) = some (-3) := rfl

-- Negative bounds evaluate with the usual order meaning.
example : (posLe 0 (-3)).eval [.int (-3)] = some true := rfl
example : (negLe 0 (-3)).eval [.int (-3)] = some false := rfl
example : (negLe 0 (-4)).eval [.int (-3)] = some true := rfl
example : (DeadRegion.below 0 (-2)).mem [.int (-3)] = true := rfl
example : (DeadRegion.below 0 (-2)).mem [.int (-2)] = false := rfl
example : (DeadRegion.above 0 (-1)).mem [.int 0] = true := rfl

/-- Two removal facts for slot 0. -/
def sparseTrail : List TrailEntry :=
  [mkDec (posNe 0 0) 1, mkDec (posNe 0 2) 1]

-- Sparse-domain singleton collapse: `{0,2,5}` minus `0` and `2` justifies
-- the lower bound `5`, while the empty trail justifies no bound at all.
example : removedValues sparseTrail 0 = [0, 2] := rfl
example : derivedLowerWitnesses sparseTrail 0 (Dom.ofList [.int 0, .int 2, .int 5]) 5 = [] := rfl
example : derivedLowerWitnesses sparseTrail 0 (Dom.ofList [.int 0, .int 2, .int 5]) 2 = [] := rfl
example : derivedLowerWitnesses ([] : List TrailEntry) 0
    (Dom.ofList [.int 0, .int 2, .int 5]) 2
    = [0] := rfl

/-! ## 6. PENDING D1-activation expectations (INTERFACES §2.7)

These predicates specify what the NEW public path must observe once D1
activates the scheduler. The current public driver (`analyzedSolve`) never
calls `RuntimeEvents.recordResolutions` / `recordBackjump`, and `SearchStats`
still has no `events` field, so there is no runtime producer whose value
could be read; every predicate below is therefore stated and NEVER applied to
a value in this module. Asserting that one of them holds for a run would be a
fabricated observation. T2/V1 discharge them by reading
`(solveWithStats …).2.events` (or D1's `solveWithEvents` fallback) after the
counter sites are wired. -/

/-- PENDING D1 activation: this must become a runtime observation.
A scheduled run of the multi-resolution family resolves at least two reason
pivots, so `reasonResolutions` — incremented only at the `analyzeConflict`
site (`RuntimeEvents.recordResolutions`) — must be at least 2. No value is
claimed here. -/
def PendingMultipleResolutions (e : RuntimeEvents) : Prop :=
  2 ≤ e.reasonResolutions

/-- PENDING D1 activation: this must become a runtime observation.
A completed learn/backjump/assert records exactly one asserting enqueue
(`RuntimeEvents.recordBackjump` at the `learnBackjumpAssert` site), so a run
that uses the jump path must show `0 < assertingEnqueues`. No value is
claimed here. -/
def PendingAssertingEnqueue (e : RuntimeEvents) : Prop :=
  0 < e.assertingEnqueues

/-- PENDING D1 activation: this must become a runtime observation.
The multi-resolution fixture's analysis target is level 1 from a level-3
conflict (level 2 is the irrelevant level it skips), so a scheduled run of
that family must record exactly one backjump with `sourceLevel = 3` and
`targetLevel = 1`. The numbers are the fixture's own analyzer target — they
are the EXPECTATION, not an observed counter. -/
def PendingIrrelevantLevelJump (e : RuntimeEvents) : Prop :=
  e.backjumps = 1 ∧ e.sourceLevel = 3 ∧ e.targetLevel = 1

/-- PENDING D1 activation: this must become a runtime observation.
A run that falls back chronologically (analysis produced no asserting
result, or no checkpoint at the proved target) completes no backjump, so its
counters must stay silent: no backjump and no asserting enqueue. No value is
claimed here. -/
def PendingFallbackIsJumpSilent (e : RuntimeEvents) : Prop :=
  e.backjumps = 0 ∧ e.assertingEnqueues = 0

/-- PENDING D1 activation: this must become a runtime observation.
Structural consistency of a scheduled run's counters: every completed
backjump records exactly one asserting enqueue, so `backjumps` never
exceeds `assertingEnqueues`; and a run with no completed backjump leaves
both level fields at their initial value. No value is claimed here. -/
def PendingCounterConsistency (e : RuntimeEvents) : Prop :=
  e.backjumps ≤ e.assertingEnqueues ∧
    (e.backjumps = 0 → e.sourceLevel = 0 ∧ e.targetLevel = 0)

/-! ## 7. Executable check definitions (kernel-checked above; run by `main`) -/

/-- All family oracle counts equal their expected values. -/
def checkFamilyOracleCounts : Bool :=
  familyBattery.all fun b => oracleCount b.2.1 == b.2.2

/-- The multi-resolution analysis and its completed trace. -/
def checkMultiResolution : Bool :=
  decide (analyzeTrail mTrail 3 mConflict = some ([(negLe 0 5, 1)], posLe 1 7)) &&
  decide (analyzeTrace oOrig mTrail 3 (analysisFuel mTrail mConflict)
    (initAnalysisState mConflict) = some (13, some ([(negLe 0 5, 1)], posLe 1 7)))

/-- The jump skips the irrelevant level: target 1, strictly below source 3,
with a single below-level falsifier. -/
def checkIrrelevantLevelJump : Bool :=
  (mTargetLevel == 1) && (mTargetLevel < 3) && (mBelow.length == 1)

/-- The long-reason analysis completes (observed trace) with the full
below-level clause. -/
def checkLongReasonTrace : Bool :=
  decide (analyzeTrail longTrail 2 longConflict = some (longBelow, posLe 1 10)) &&
  decide (analyzeTrace oOrig longTrail 2 (analysisFuel longTrail longConflict)
    (initAnalysisState longConflict) = some (19, some (longBelowLcg, posLe 1 10)))

/-- A tag for the root-conflict dispatch (the transition type has no
`DecidableEq`, so the running check matches on the constructor). -/
def rootUnsatTag : Bool :=
  match conflictStep rootCfg [[negLe 0 5]] [] with
  | .unsat => true
  | _ => false

/-- Exact lookup succeeds on the exact falsifier; the order upgrade is
required and succeeds when it is absent. (`TrailEntry` has no `DecidableEq`,
so the entry is pinned by its literal and level.) -/
def checkExactAndUpgradeLookup : Bool :=
  decide ((findEntryOf [mkDec (posLe 0 4) 1] (posLe 0 5)).map
    (fun e => e.literal) = none) &&
  decide (orderUpgrade [mkDec (posLe 0 4) 1] (negLe 0 5) = negLe 0 4) &&
  decide ((findEntryOf [mkDec (posLe 0 4) 1]
    (orderUpgrade [mkDec (posLe 0 4) 1] (negLe 0 5)).negate).map
      (fun e => (e.literal, e.level)) = some (posLe 0 4, 1)) &&
  decide ((findEntryOf [mkDec (posLe 0 5) 1] (posLe 0 5)).map
    (fun e => e.literal) = some (posLe 0 5))

/-- Propagation resumes after the assertion and narrows slot 1. -/
def checkPropagationAfterAssertion : Bool :=
  decide (explainedStep [] [] paState
    = .narrow (posLe 1 0) [posNe 0 0, posLe 1 0] [])

/-- The second dispatch of a consumed deduction is skipped. -/
def checkDuplicateDeduction : Bool :=
  (explainedDeduction [] [] dupState).isSome &&
  (explainedDeduction [] [] dupState2).isNone &&
  TrailRedundant dupState2.trail (posNe 0 0)

/-- A redundant (already recorded) productive deduction is skipped. -/
def checkRedundantDecision : Bool :=
  decide (explainedStep [] [] redState = .stable) &&
  (explainedDeduction [] [] redState).isNone

/-- Forced singleton pins are not counted as decisions. -/
def checkForcedDecisionAccounting : Bool :=
  (stepDecide rootCfg 0 (.int 0) Dom.empty (negNe 0 0)).stats.decisions == 0 &&
  (stepDecide rootCfg 0 (.int 0) (Dom.ofList [.int 1]) (negNe 0 0)).stats.decisions == 1

/-- The jump keeps the permanent exhaustion log and records its counters. -/
def checkRestoredExhaustion : Bool :=
  (stepLearnBackjumpAssert exCfg exPlan exEv exRestored).log.regions.any
      (fun r => r.mem [.int 1, .int 0]) &&
  (stepLearnBackjumpAssert exCfg exPlan exEv exRestored).log.regions.length == 1 &&
  (stepLearnBackjumpAssert exCfg exPlan exEv exRestored).events.backjumps == 1

/-- Root UNSAT goes through the nonempty-clause route; the empty clause list
stays local. -/
def checkRootUnsat : Bool :=
  rootUnsatTag &&
  localExcludeTag &&
  decide (ConflictShape.ofConflict 0 [posLe 0 1] = .root) &&
  decide (ConflictShape.ofConflict 0 [] = .local)

/-- A fully falsified learned clause yields an empty local explanation. -/
def checkEmptyLocalExplanation : Bool :=
  decide (explainedStep [] [] deadState = .excluded [])

/-- Boolean and integer decisions are distinct literal shapes. -/
def checkBooleanIntSeparation : Bool :=
  decide (valueLiteral 0 (.bool true) = some (posBool 0 true)) &&
  decide (valueLiteral 1 (.int 3) = some (negNe 1 3)) &&
  decide (valueLiteral 0 (.array []) = none) &&
  decide (Value.intView (.bool true) = some 1)

/-- Negative bounds read with the usual order semantics. -/
def checkNegativeBounds : Bool :=
  decide ((negLe 0 (-3)).eval [.int (-3)] = some false) &&
  decide ((negLe 0 (-4)).eval [.int (-3)] = some true) &&
  (DeadRegion.below 0 (-2)).mem [.int (-3)]

/-- Sparse domains collapse exactly as the removal facts justify. -/
def checkSparseDomains : Bool :=
  decide (removedValues sparseTrail 0 = [0, 2]) &&
  decide (derivedLowerWitnesses sparseTrail 0 (Dom.ofList [.int 0, .int 2, .int 5]) 5 = []) &&
  decide (derivedLowerWitnesses [] 0 (Dom.ofList [.int 0, .int 2, .int 5]) 2 = [0])

/-- The P1.1 counterexample: the deduction is selected, its pivot is FALSE
at the global solution, and the witness solution is a genuine `x ≠ y`. -/
def checkBranchRelativeCounterexample : Bool :=
  (explainedDeduction [] [] xyState).isSome &&
  decide ((explainedDeduction [] [] xyState).map (fun d => d.literal)
    = some (posBool 1 true)) &&
  xyLeaf [.bool true, .bool false] &&
  decide ((posBool 1 true).norm.eval [.bool true, .bool false] = some false)

-- Kernel-checked companions of the executable checks above.
example : checkFamilyOracleCounts = true := rfl
example : checkMultiResolution = true := rfl
example : checkIrrelevantLevelJump = true := rfl
example : checkLongReasonTrace = true := rfl
example : rootUnsatTag = true := rfl
example : checkExactAndUpgradeLookup = true := rfl
example : checkPropagationAfterAssertion = true := rfl
example : checkDuplicateDeduction = true := rfl
example : checkRedundantDecision = true := rfl
example : checkForcedDecisionAccounting = true := rfl
example : checkRestoredExhaustion = true := rfl
example : checkRootUnsat = true := rfl
example : checkEmptyLocalExplanation = true := rfl
example : checkBooleanIntSeparation = true := rfl
example : checkNegativeBounds = true := rfl
example : checkSparseDomains = true := rfl
example : checkBranchRelativeCounterexample = true := rfl

end T1Oracle

open T1Oracle

/-! ## 8. Runtime suite (`main`)

Registered by T2/V1 as `[[lean_exe]] name = "tests_lcg_oracle", root =
"Tests.UIP.OracleFixtures"`; `lakefile.toml` is deliberately NOT edited by T1.
The PENDING §2.7 predicates are listed but NOT evaluated: there is no
runtime producer yet, so any assertion would be fabricated. -/

namespace T1Oracle

/-- The T1 suite runner. Namespaced (not root-level) so that other
`lean_exe` roots can import these fixtures without a duplicate `main`.
Registration uses the thin wrapper `Tests.UIP.OracleRunner`. -/
def main : IO UInt32 := do
  let mut st : TestState := { passed := 0, failed := 0 }
  IO.println "-- T1 independent oracle and fixture checks --"
  -- Oracle counts and the executable reference agreement per family.
  for b in familyBattery do
    let (name, problem, expected) := b
    st ← st.check s!"{name}: oracle solution count = {expected}"
      (oracleCount problem == expected)
    st ← st.check s!"{name}: reference verdict agrees with the oracle"
      (referenceAgreesB problem)
  -- Component fixtures (kernel-checked above; re-evaluated here).
  st ← st.check "multi-resolution analysis and completed trace"
    checkMultiResolution
  st ← st.check "irrelevant-level jump (3 -> 1, one below-level falsifier)"
    checkIrrelevantLevelJump
  st ← st.check "long-reason analysis completes with the full below clause"
    checkLongReasonTrace
  st ← st.check "exact and order-upgrade reason lookup"
    checkExactAndUpgradeLookup
  st ← st.check "propagation resumes after the assertion"
    checkPropagationAfterAssertion
  st ← st.check "duplicate deduction is skipped after consumption"
    checkDuplicateDeduction
  st ← st.check "redundant (already recorded) deduction is skipped"
    checkRedundantDecision
  st ← st.check "forced singleton pin is not counted as a decision"
    checkForcedDecisionAccounting
  st ← st.check "restored exhaustion survives the jump, counters recorded"
    checkRestoredExhaustion
  st ← st.check "root UNSAT route; empty clause list stays local"
    checkRootUnsat
  st ← st.check "empty local explanation for a falsified learned clause"
    checkEmptyLocalExplanation
  st ← st.check "Boolean/int decision separation"
    checkBooleanIntSeparation
  st ← st.check "negative bounds"
    checkNegativeBounds
  st ← st.check "sparse domains"
    checkSparseDomains
  st ← st.check "P1.1 branch-relative deduction counterexample"
    checkBranchRelativeCounterexample
  IO.println "PENDING D1 activation (no runtime producer yet; NO value asserted):"
  IO.println "  T1Oracle.PendingMultipleResolutions"
  IO.println "  T1Oracle.PendingAssertingEnqueue"
  IO.println "  T1Oracle.PendingIrrelevantLevelJump"
  IO.println "  T1Oracle.PendingFallbackIsJumpSilent"
  IO.println "  T1Oracle.PendingCounterConsistency"
  if st.failed == 0 then
    IO.println s!"ALL {st.passed} ORACLE FIXTURE CHECKS PASSED"
    return 0
  else
    IO.eprintln s!"{st.failed} ORACLE FIXTURE CHECKS FAILED ({st.passed} passed)"
    return 1

end T1Oracle

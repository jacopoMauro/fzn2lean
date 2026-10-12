/-
File: LeanFzn/Solver/UIP/Proofs/ConflictResolution.lean

Purpose:
  Proofs supporting the conflict-analysis contract:

  * conflict falsification and solution exclusion;
  * the branch nogood for empty local explanations and failed leaf
    checks, derived from justified branch assumptions (never promoted
    to global UNSAT);
  * the analyser's asserting/unit property after level restoration;
  * the historical allowance's insufficiency for long clauses, which
    is why the input-dependent `analysisAllowance` replaces it;
  * the bridge that lets the executable analyzer's proved contract
    (from `Proofs/Transitions.lean`) serve as the branch-level
    `AnalysisContract`, with the reachability premises named
    explicitly.

Dependencies:
  - LeanFzn.Solver.Propagation.ConflictResolution
  - LeanFzn.Solver.Propagation.Proofs.Analyze (level lemmas, `analyzeStep_tracked`)
  - LeanFzn.Solver.Propagation.Proofs.Transitions (`analyzeConflict_correct`)
  - LeanFzn.Solver.Propagation.Proofs.BranchState (reachable-state constructions)
  - LeanFzn.Solver.Propagation.AnalysisCompletion (B1: the completed-trace theorems)
  - LeanFzn.Solver.Propagation.BackjumpFrontier (C1: the actual restoration shape)

DAG:
  ConflictResolution + Proofs.Analyze + Proofs.Transitions
  + AnalysisCompletion + BackjumpFrontier
  -> Proofs.ConflictResolution -> BackjumpFrontier (P1.D).
-/

import LeanFzn.Solver.Propagation.ConflictResolution
import LeanFzn.Solver.Propagation.Proofs.Transitions
import LeanFzn.Solver.Propagation.Proofs.BranchState
import LeanFzn.Solver.Propagation.AnalysisCompletion
import LeanFzn.Solver.Propagation.BackjumpFrontier
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## Conflict falsification -/

/-- Every literal of a conflict clause is falsified by the trail: the
clause's literals are (normalized) negations of trail entries. This is
the one-line ALIAS of A1's `FalsifiedByTrail` (INTERFACES §7.3), so no
parallel falsifier invariant exists in the tree. -/
abbrev TrailFalsifies (bs : BranchState leaf) (c : Clause) : Prop :=
  FalsifiedByTrail bs c

/-- A trail-falsified clause is false at every assignment that satisfies
the trail. This is the semantic content of "the conflict is real". -/
theorem trailFalsifies_eval_false {bs : BranchState leaf} {c : Clause}
    {a : Assignment} (h : TrailFalsifies bs c)
    (htrail : ∀ e ∈ bs.trail, e.literal.eval a = some true) :
    ∀ q ∈ c, q.eval a = some false := by
  intro q hq
  obtain ⟨e, he, hlit⟩ := h q hq
  have hev := htrail e he
  rw [hlit] at hev
  exact (Literal.eval_negate_false_iff q a).mp hev

/-- A trail-falsified, entailed conflict clause excludes every
represented leaf solution: this is the exclusion P1.D's scheduler cites
when it retires a branch. -/
theorem conflict_excludes_solution {bs : BranchState leaf} {c : Clause}
    {a : Assignment}
    (hent : LearnedEntailed leaf [c]) (hleaf : leaf a = true)
    (hrep : bs.Represents a) (hfals : TrailFalsifies bs c) : False := by
  obtain ⟨_, htrail, _⟩ := hrep
  obtain ⟨q, hq, hqtrue⟩ := hent c (List.mem_singleton_self _) a hleaf
  have hqfalse := trailFalsifies_eval_false hfals htrail q hq
  rw [hqtrue] at hqfalse
  exact absurd hqfalse (by simp)

/-- At a branch whose trail is exactly-falsified, the conflict clause's
falsity at the conflict state — the `falsifiedAtConflict` field of
`AnalysisContract`, proved from the trail side. -/
theorem conflict_falsified_at_conflict {bs : BranchState leaf} {an : ConflictAnalysis}
    (hfals : TrailFalsifies bs an.learned) :
    ∀ q ∈ an.learned, ∃ e ∈ bs.trail, e.literal = q.negate := hfals

/-! ## Branch nogood for local explanations and failed leaves

An empty local propagator explanation or a failed leaf check excludes
the branch, not the problem. The entailed statement is the *branch
nogood*: the disjunction of the negated trail literals. Its proof needs
two justified branch assumptions:

* `hcovers` — the bridge: an assignment that satisfies every trail
  literal and passes the leaf test is represented by the branch (this
  is the P1.B domain/trail bridge: the trail's literals record exactly
  the frame's narrowing, so satisfying them re-establishes coverage);
* `hdead` — the branch is dead: no leaf-passing represented solution
  exists.

The nogood is entailed at every leaf-passing assignment. -/

/-- The branch nogood: the negations of the trail's literals. -/
def branchNogood (bs : BranchState leaf) : Clause :=
  bs.trail.map fun e => e.literal.negate

/-- The branch nogood is entailed at every leaf-passing assignment, with
the two justified branch assumptions named explicitly (the plan's
"list missing hypotheses" requirement):

* `hbridge` — the P1.B domain/trail bridge: satisfying the trail and
  the learned database re-establishes frame coverage (the trail's
  literals record exactly the frame's narrowing);
* `htotal` — order totality for the typed slots: a trail literal or its
  negation is decided at every leaf-passing assignment (no `none`
  values in the slots the branch speaks about);
* `hlearned` — the learned database is entailed (P1.A's `WellFormed`
  conjunct);
* `hdead` — the branch is dead: no leaf-passing represented solution
  exists.

Conclusion: the branch nogood holds at every leaf-passing assignment,
so it may be learned as a *branch* clause. This is the correct
treatment of empty local explanations and failed leaf checks — the
clause talks only about the branch's own literals. -/
theorem branchNogood_entailed {bs : BranchState leaf}
    (hbridge : ∀ a, leaf a = true →
      (∀ e ∈ bs.trail, e.literal.eval a = some true) →
      (∀ c ∈ bs.learned, c.SatisfiedBy a) →
      FrameCovers bs.frame a)
    (htotal : ∀ a, leaf a = true → ∀ e ∈ bs.trail,
      e.literal.eval a = some true ∨ e.literal.negate.eval a = some true)
    (hlearned : LearnedEntailed leaf bs.learned)
    (hdead : ∀ a, leaf a = true → bs.Represents a → False) :
    LearnedEntailed leaf [branchNogood bs] := by
  intro c hc a hleaf
  rw [List.mem_singleton] at hc
  subst hc
  by_cases hsome : ∃ q ∈ branchNogood bs, q.eval a = some true
  · exact hsome
  · exfalso
    have htrail : ∀ e ∈ bs.trail, e.literal.eval a = some true := by
      intro e he
      rcases htotal a hleaf e he with h | h
      · exact h
      · exact absurd ⟨e.literal.negate, List.mem_map_of_mem he, h⟩ hsome
    have hlearn : ∀ cl ∈ bs.learned, cl.SatisfiedBy a := by
      intro cl hcl
      exact hlearned cl hcl a hleaf
    exact hdead a hleaf ⟨hbridge a hleaf htrail hlearn, htrail, hlearn⟩

/-! ## Analysis fuel: status of the allowance obligation

The historical analyzer ran with the constant `4 * len² + 256`, which
is independent of clause lengths and therefore cannot cover arbitrary
reasons (PLAN P1.C item 4). The new driver uses the input-dependent
`analysisAllowance` = `(reasonBudget + 1) * (len + 1) + 1`, whose
rationale is that each of the `len` trail entries is marked at most
once (`markLit` deduplicates against `marks`) and each mark re-seeds at
most one reason clause, so the worklist's total literal consumption is
at most `len * (reasonBudget + 1)`.

**Status (B1 landed, `AnalysisCompletion.lean`):** the sufficiency is
now PROVED — `analysis_complete_of_reachable` shows that on every
reachable analyzer input the executable fuel cannot be exhausted
(`analyzeTrace` observes a semantic stop), and
`analyzeAtAllowance_stops` identifies `analyzeAtAllowance`'s result with
that completed trace's verdict. The historical constant stays only as
the floor of `analysisFuel` (`analyzeAtAllowance_dominates`), never as
the driver's allowance. The remaining refinement (dropping the `max`
floor) is B1's recorded residual, not a soundness gap: `analysisFuel`
is what the executable runs with and what B2's certificate consumes. -/

/-! ## The analyzer contract bridge

The executable first-UIP analyzer meets the branch-level
`AnalysisContract` once the reachability premises are supplied
explicitly: the state's well-formedness and the `AnalysisReady`
bundle (entailed conflict clause, valid normalized reasons, root
facts). `Proofs/Transitions.lean` proves the entailment and level
halves; `TrailFalsifies` supplies the falsification half. -/

theorem analyzeConflict_contract {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st : State} {an : ConflictAnalysis}
    (hstate : st.WellFormed problem constraintHolds)
    (hready : st.AnalysisReady problem constraintHolds)
    (h : analyzeConflict st = some an) :
    an.learned.EntailedBy problem constraintHolds ∧
      an.backjumpLevel ≤ st.decisionLevel ∧
      (st.decisionLevel = 0 ∨ an.backjumpLevel < st.decisionLevel) :=
  analyzeConflict_correct hstate hready h

/-! ## B2 — the classified results with semantic-stop evidence

`RestorationCertificate.lean` proves the three classified outcomes'
trace-free cores (it is upstream of B1's `analyzeTrace`). This section
composes them with the completed-trace theorems of
`AnalysisCompletion.lean`, so a consumer sees that a `none` result is a
SEMANTIC stop — root contradiction at level 0, or an unsupported local
explanation above it — never a fuel cut-off. -/

/-- SUCCESS IS A SEMANTIC STOP: the success verdict yields the run's own
record AND a completed trace of `k ≤ analysisFuel` transitions. -/
theorem analyzeClassified_success_semanticStop {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf}
    {below : List (Literal × Nat)} {uip : Literal}
    (hin : AnalyzerInput leaf bs) (hreach : ReachableState leaf orig bs)
    (hcl : analyzeClassified bs.trail bs.level hin.conflict
      = .success below uip) :
    analyzeAtAllowance bs.trail bs.level hin.conflict = some (below, uip) ∧
    (∃ k, k ≤ analysisFuel bs.trail hin.conflict ∧
      analyzeTrace bs.trail bs.level (analysisFuel bs.trail hin.conflict)
        (initAnalysisState hin.conflict) = some (k, some (below, uip))) := by
  have hA : analyzeAtAllowance bs.trail bs.level hin.conflict
      = some (below, uip) := analyzeClassified_eq_success_iff_of_allowance.mp hcl
  obtain ⟨k, hk, htr, -⟩ := analyzeAtAllowance_stops hin.conflict hin.nonempty
    (analyzerReachable_of_reachable hreach hin.conflict)
  exact ⟨hA, k, hk, by rw [hA] at htr; exact htr⟩

/-- ROOT CONTRADICTION with semantic-stop evidence: level 0, no analysis
record, the `.root` shape, the trail-conditional and represented
exclusions, and a completed trace that stopped in `none`. -/
theorem analyzeClassified_root_semanticStop {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf}
    (hin : AnalyzerInput leaf bs) (hreach : ReachableState leaf orig bs)
    (hroot : analyzeClassified bs.trail bs.level hin.conflict
      = .rootContradiction) :
    bs.level = 0 ∧
    analyzeAtAllowance bs.trail bs.level hin.conflict = none ∧
    ConflictShape.ofConflict bs.level hin.conflict = .root ∧
    (∀ a, leaf a = true →
      (∀ e ∈ bs.trail, e.literal.eval a = some true) → False) ∧
    (∀ a, leaf a = true → bs.Represents a → False) ∧
    (∃ k, k ≤ analysisFuel bs.trail hin.conflict ∧
      analyzeTrace bs.trail 0 (analysisFuel bs.trail hin.conflict)
        (initAnalysisState hin.conflict) = some (k, none)) := by
  obtain ⟨hlvl0, hA, hshape, hexcl, hrep⟩ :=
    analyzeClassified_root_contradiction hin hreach hroot
  have hr : AnalyzerReachable bs.trail 0 hin.conflict
      (initAnalysisState hin.conflict) := by
    have h := analyzerReachable_of_reachable hreach hin.conflict
    rwa [hlvl0] at h
  have htr := analyzeClassified_root_trace hin.conflict hin.nonempty hr
    (by rwa [hlvl0] at hroot)
  exact ⟨hlvl0, hA, hshape, hexcl, hrep, htr⟩

/-- UNSUPPORTED LOCAL EXPLANATION with semantic-stop evidence: above the
root, no analysis record, the `.analyzable` shape, and a completed trace
that stopped in `none`. NEVER an UNSAT verdict. -/
theorem analyzeClassified_unsupported_semanticStop {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf}
    (hin : AnalyzerInput leaf bs) (hreach : ReachableState leaf orig bs)
    (huns : analyzeClassified bs.trail bs.level hin.conflict
      = .unsupported) :
    bs.level ≠ 0 ∧
    analyzeAtAllowance bs.trail bs.level hin.conflict = none ∧
    bs.analyzeWithAllowance hin.conflict = none ∧
    ConflictShape.ofConflict bs.level hin.conflict = .analyzable ∧
    (∃ k, k ≤ analysisFuel bs.trail hin.conflict ∧
      analyzeTrace bs.trail bs.level (analysisFuel bs.trail hin.conflict)
        (initAnalysisState hin.conflict) = some (k, none)) := by
  obtain ⟨hlvl, hA, hana, hshape⟩ :=
    analyzeClassified_unsupported_local hin hreach huns
  obtain ⟨-, htr⟩ := analyzeClassified_unsupported_trace hin.conflict
    hin.nonempty (analyzerReachable_of_reachable hreach hin.conflict) huns
  exact ⟨hlvl, hA, hana, hshape, htr⟩

/-- THE A-PRIORI ROOT EXCLUSION (INTERFACES §2.3, ledger item 18): with
the root-facts invariant and the leaf-solution bridge (both D1's
problem-level premises), a `.rootContradiction` verdict excludes every
leaf solution a priori — the analyzer's only global UNSAT export. -/
theorem analyzeClassified_root_excludes_all
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {leaf : Assignment → Bool} {orig : List Domain} {bs : BranchState leaf}
    (hin : AnalyzerInput leaf bs) (hreach : ReachableState leaf orig bs)
    (hroot : analyzeClassified bs.trail bs.level hin.conflict
      = .rootContradiction)
    (hrootFacts : RootFacts problem constraintHolds bs.trail)
    (hleafSol : ∀ a, leaf a = true → ProblemSolution problem constraintHolds a) :
    ∀ a, leaf a = true → False := by
  obtain ⟨hlvl0, -, -, hexcl, -⟩ :=
    analyzeClassified_root_contradiction hin hreach hroot
  intro a hleaf
  refine hexcl a hleaf (fun e he => hrootFacts e he ?_ a (hleafSol a hleaf))
  have := hreach.wf.1 e he
  omega

/-- THE SINGLE SCHEDULER-FACING THEOREM OF THE SUCCESS CASE: the
classified success verdict yields BOTH the restoration certificate with
the learned-clause entailment DERIVED from the problem-level lift
(`analyzeStep_tracked` + D1's bridges) AND the completed-trace witness.
No analysis-result premise remains; `hne` is the input's nonempty-clause
discipline (A3's `AnalyzerInput.nonempty`). -/
theorem analyzeClassified_success_certificate_semanticStop
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {leaf : Assignment → Bool} {orig : List Domain} {bs : BranchState leaf}
    {c : Clause} {below : List (Literal × Nat)} {uip : Literal}
    (hreach : ReachableState leaf orig bs)
    (hpos : 0 < bs.level)
    (hne : 1 ≤ c.length)
    (hcl : analyzeClassified bs.trail bs.level c = .success below uip)
    (hconf : Clause.EntailedBy problem constraintHolds c)
    (hleafSol : ∀ a, leaf a = true → ProblemSolution problem constraintHolds a)
    (hreasons : ∀ e ∈ bs.trail, ∀ r ∈ e.reason,
      Reason.Valid problem constraintHolds r e.literal)
    (hrootFacts : RootFacts problem constraintHolds bs.trail)
    (hrnorm : ∀ e ∈ bs.trail, ∀ r ∈ e.reason, ∀ l ∈ r.clause, l = l.norm) :
    RestorationCertificate leaf bs (ConflictAnalysis.ofRun below uip) ∧
    (∃ k, k ≤ analysisFuel bs.trail c ∧
      analyzeTrace bs.trail bs.level (analysisFuel bs.trail c)
        (initAnalysisState c) = some (k, some (below, uip))) := by
  refine ⟨analyzeClassified_success_certificate_of_problem hreach hpos hcl
    hconf hleafSol hreasons hrootFacts hrnorm, ?_⟩
  have hA : analyzeAtAllowance bs.trail bs.level c = some (below, uip) :=
    analyzeClassified_eq_success_iff_of_allowance.mp hcl
  obtain ⟨k, hk, htr, -⟩ := analyzeAtAllowance_stops c hne
    (analyzerReachable_of_reachable hreach c)
  exact ⟨k, hk, by rw [hA] at htr; exact htr⟩

/-! ## B2 — the restoration/enqueue bridge at `BackjumpPlan.execute`

C1's `BackjumpPlan.execute` IS `BranchState.restoreAssert` at the plan's
own fields (definitionally), so the certificate's justified-enqueue
theorems instantiate at the scheduler's ACTUAL restoration shape. This
is where "the enqueue is justified, not asserted" is proved for the
object C2 executes: the reason is entailed (the certificate's), the
pivot is a member, the side literals have earlier falsifiers, and the
trail discipline survives under the enqueue's absence check. -/

/-- `BackjumpPlan.execute` is the certificate's restoration shape: the
checkpoint's frame and trail, the target level, the CURRENT database and
the single asserting entry. Definitional, so every bridge below applies
to C1's object without re-derivation. -/
theorem _root_.LeanFzn.Solver.Propagation.BackjumpPlan.execute_eq_restoreAssert (p : BackjumpPlan leaf)
    (bs : BranchState leaf) :
    p.execute bs = bs.restoreAssert p.checkpoint.frame p.checkpoint.trail
      p.target p.asserting p.learned := rfl

/-- WELL-FORMEDNESS OF THE EXECUTED PLAN, DERIVED: the restored-and-
asserted state is well formed from (i) the checkpoint's own
well-formedness, (ii) the certificate, (iii) the plan's identifying
checkpoint (`Identifies`, so the checkpoint's level IS the target), and
(iv) the two enqueue-site disciplines (the normalized asserting
membership — automatic for the canonical record — and negation-stable
non-asserting literals, J1 round 2: the honest `NegStableAvoiding`
family — the whole-clause `NegStable` is refuted for canonical Boolean
learned literals, `Proofs/HdeadCkpt.lean`). C2's former
`hent`/`hpivot`/`hchron` caller
premises are therefore discharged, not assumed. -/
theorem _root_.LeanFzn.Solver.Propagation.BackjumpPlan.execute_wellFormed_of_certificate
    {leaf : Assignment → Bool} {p : BackjumpPlan leaf} {bs : BranchState leaf}
    {orig : List Domain} {an : ConflictAnalysis}
    (hreach : ReachableState leaf orig bs)
    (hpre : p.checkpoint.WellFormed) (hident : p.Identifies bs)
    (hcert : RestorationCertificate leaf bs an)
    (hstable : an.asserting.norm = an.asserting)
    (hanA : an.asserting = p.asserting) (hanL : an.learned = p.learned)
    (hsurv : ∀ e ∈ bs.trail, e.level ≤ an.backjumpLevel →
      e ∈ p.checkpoint.trail)
    (hneg : NegStableAvoiding an.asserting an.learned) :
    (p.execute bs).WellFormed := by
  have hlev : p.checkpoint.level = p.target := hident.1
  have hpre' : (bs.restoreFrame p.checkpoint.frame p.checkpoint.trail
      p.target).WellFormed := by
    obtain ⟨h1, h2, h3, h4, -⟩ := hpre
    refine ⟨?_, h2, h3, h4, ?_⟩
    · intro e he
      have hle := h1 e he
      rw [hlev] at hle
      exact hle
    · exact hreach.wf.2.2.2.2
  rw [BackjumpPlan.execute_eq_restoreAssert, ← hanA, ← hanL]
  exact restoreAssert_wellFormed_of_certificate hpre' hcert
    (hcert.asserting_norm_mem_of_stable hstable)
    (restore_chronology_of_certificate hcert hstable hsurv hneg)

/-- REPRESENTATION OF THE EXECUTED PLAN, DERIVED: every leaf solution
covered by the checkpoint's frame and satisfying the checkpoint trail,
the retained database and the assertion is represented by the executed
state — the assertion is JUSTIFIED by the certificate's unit property,
never merely posted. -/
theorem _root_.LeanFzn.Solver.Propagation.BackjumpPlan.execute_represents_of_certificate
    {leaf : Assignment → Bool} {p : BackjumpPlan leaf} {bs : BranchState leaf}
    {an : ConflictAnalysis} {a : Assignment}
    (hcert : RestorationCertificate leaf bs an)
    (hanA : an.asserting = p.asserting) (hanL : an.learned = p.learned)
    (hpb : an.backjumpLevel = p.target)
    (hsurv : ∀ e ∈ bs.trail, e.level ≤ an.backjumpLevel →
      e ∈ p.checkpoint.trail)
    (htrail : ∀ e ∈ p.checkpoint.trail, e.literal.eval a = some true)
    (hlearn : ∀ cl ∈ bs.learned, cl.SatisfiedBy a)
    (hframe : FrameCovers p.checkpoint.frame a)
    (hleaf : leaf a = true) :
    (p.execute bs).Represents a := by
  rw [BackjumpPlan.execute_eq_restoreAssert, ← hanA, ← hanL, ← hpb]
  exact restoreAssert_represents_of_certificate hcert hsurv htrail hlearn
    hframe hleaf

/-- THE EXECUTED PLAN'S TRAIL KEEPS THE DISCIPLINE: restoring the
checkpoint trail and appending the normalized asserting entry is
duplicate-safe by A1's `TrailLiteralsDistinct.enqueue`, given the
checkpoint's discipline and the enqueue's absence check. This is the
`TrailLiteralsDistinct` consumer INTERFACES §1 assigns to B2. -/
theorem _root_.LeanFzn.Solver.Propagation.BackjumpPlan.execute_distinct_of_absence
    {leaf : Assignment → Bool} {p : BackjumpPlan leaf} {bs : BranchState leaf}
    (hdist : TrailLiteralsDistinct p.checkpoint.trail)
    (hnorm : ∀ e ∈ p.checkpoint.trail, e.literal = e.literal.norm)
    (hfresh : ∀ e ∈ p.checkpoint.trail, e.literal ≠ p.asserting.norm) :
    TrailLiteralsDistinct (p.execute bs).trail := by
  rw [BackjumpPlan.execute_eq_restoreAssert, BranchState.restoreAssert_trail]
  exact TrailLiteralsDistinct.enqueue hdist hnorm hfresh

/-- TYPED FILTERING AT THE EXECUTED PLAN — REJECTION: if the plan's
assertion rejects the checkpoint frame, no surviving leaf solution is
covered by the checkpoint frame. C1's `restoreNarrow = none` →
local-exclusion path is therefore sound. -/
theorem _root_.LeanFzn.Solver.Propagation.BackjumpPlan.execute_filterFrame_none_excludes
    {leaf : Assignment → Bool} {p : BackjumpPlan leaf} {bs : BranchState leaf}
    {an : ConflictAnalysis}
    (hcert : RestorationCertificate leaf bs an)
    (hanA : an.asserting = p.asserting)
    (hnone : filterFrame p.asserting p.checkpoint.frame = none) :
    ∀ a, leaf a = true →
      (∀ e ∈ bs.trail, e.level ≤ an.backjumpLevel →
        e.literal.eval a = some true) →
      FrameCovers p.checkpoint.frame a → False := by
  intro a hleaf htrail hcov
  have hnone' : filterFrame an.asserting p.checkpoint.frame = none := by
    rw [hanA]
    exact hnone
  exact restoreAssert_filterFrame_none_excludes hcert hnone' a hleaf htrail hcov

end LeanFzn.Solver.UIP

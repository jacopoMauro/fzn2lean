/-
File: solver/LCG/Proofs/Reachability.lean

Purpose:
  The reachability invariant for the LCG engine (PLAN.md Step 2): a
  `Reachable problem holdsB props st` bundle that every state reached by
  `lcgSearch` from `initialStateWithRoots problem` satisfies, and from
  which the two `EngineSafe` obligations follow.

  The bundle is pure reachability: no semantic premise beyond the
  fragment assumption that every value of every int/bool slot has an
  integer view (`IntViewed problem`, the invariant the Step 2 proofs of
  `Proofs/Engine.lean` state as the "int/bool fragment invariant").

  Components and their roles:

  * `coherent` (DomainCoherent): the domains are the `domOfLit` fold of
    the trail — the trail accounts for every domain narrowing, so a
    fitting assignment satisfies every trail-derived bound statement
    (Step 2.1's trail-domain coherence);
  * `fitDomLen`: the domain length matches the problem's (structural);
  * `conflictNone`: the conflict flag is clear between iterations;
  * `learnedEntailed`: every learned clause is entailed by the internal
    problem (Step 1's `analyzeLearned_entailed` threading, L0.4);
  * `trailSatOfSol`: every internal solution satisfies the trail — the
    master soundness invariant, reused at every propagation step;
  * `clausesSatOfSol`: every internal solution satisfies every original
    clause (needed because trail satisfaction alone does not pin the
    original clause database; the engine does not remove clauses);
  * `reasonValid` / `chrono` / `rootFacts` / `normReasons`: the
    `AnalysisReady` conjuncts reachability must supply for conflict
    analysis (reason clauses are trail-derived, hence eval-equal-covered
    by the trail — the chronology component is what makes analysis
    resolution ready).

  `Search`-level proof composes.
-/import solver.LCG.Search
import solver.LCG.Encoding
import solver.LCG.Proofs.Engine
import solver.LCG.Proofs.Analyze
import solver.LCG.Proofs.Transitions

namespace LeanFzn.Solver.LCG

open LeanFzn LeanFzn.Solver.Core

/-! ## The fragment invariant

The order encoding only speaks about int/bool slots: literals over such
slots evaluate against the integer view, and every proof in
`Proofs/Engine.lean` carries the side condition that the slot values
concerned have integer views. The engine never introdroduces set/array
values (domains only shrink or Boolean-pin), so for problems whose
initial domains are all int/bool-typed the invariant is permanent. -/

/-- Every value in any slot domain of `doms` has an integer view. -/
def IntViewedDoms (doms : List (List Value)) : Prop :=
  ∀ d ∈ doms, ∀ v ∈ d, Value.intView v ≠ none

/-- The problem's domains are int/bool-typed throughout. -/
def IntViewed (problem : Problem Constraint Objective) : Prop :=
  IntViewedDoms problem.domains

/-! ## The reachability bundle

`Reachable problem constraintHolds constraintHoldsB props st` collects
everything the UNSAT proof needs about a state the loop actually
produces. Every component is proved separately below to be preserved by
the engine's state transformers. -/

structure Reachable (problem : Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop)
    (props : List Propagator) (st : State) : Prop where
  coherent : DomainCoherent problem st
  fitLen : st.domains.length = problem.domains.length
  conflictNone : st.conflict = none
  learnedEntailed : ∀ c ∈ st.learned,
    c.EntailedBy problem constraintHolds
  trailSatOfSol : ∀ a, ProblemSolution problem constraintHolds a →
    st.TrailSatisfied a
  clausesSatOfSol : ∀ c ∈ st.clauses,
    ∀ a, ProblemSolution problem constraintHolds a →
      ∃ l ∈ c, l.eval a = some true
  reasonValid : ∀ e ∈ st.trail, ∀ r ∈ e.reason,
    Reason.Valid problem constraintHolds r e.literal
  chrono : ∀ e ∈ st.trail, e.Chronological st.trail
  rootFacts' : RootFacts problem constraintHolds st.trail
  normReasons : ∀ e ∈ st.trail, ∀ r ∈ e.reason, ∀ l ∈ r.clause, l = l.norm
  rooted : ∀ e ∈ st.trail, e.level ≤ st.decisionLevel

/-! ## Trail soundness of a single enqueue

The master lemma: enqueuing a literal that every internal solution
(already satisfying the trail and the clause database) makes true
preserves exactly that property. This is the executable counterpart of
`Transitions.enqueue_implied_preserves` phrased directly on
`trailSatOfSol`/`clausesSatOfSol`, with the two degenerate branches
(already-on-trail skip and opposing-fact conflict) included: both leave
the trail unchanged, so the property is preserved trivially there too. -/

/-- Folding the seed trail: the initial state satisfies trail-soundness
    vacuously (empty trail) and clause-soundness by construction. -/
theorem initialState_trailSat (problem : Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop)
    (a : Assignment) (hsol : ProblemSolution problem constraintHolds a) :
    (initialState problem).TrailSatisfied a := by
  intro _ he
  exact absurd he (by simp [initialState])

/-! ### The enqueue step

Every trail extension performed by the engine goes through
`enqueueNorm`. The fresh branch appends `(l.norm, decisionLevel,
reason)` and narrows the domains with `domOfLit`. For an internal
solution `a` that satisfies the old state entirely:

* the opposing-fact skip and the already-on-trail skip leave the
  trail untouched — trail soundness transfers verbatim;
* in the fresh branch, every old entry still evaluates the same, and
  the new entry's literal `l = l0.norm` is satisfied by hypothesis
  (it is `st.litOnTrail`-fresh and `st.negOnTrail`-free, so the
  enqueue really appends). -/

/-- Trail-soundness step for `enqueueNorm`'s fresh branch: `hlit` says
    the enqueued literal is true at every internal solution. -/
theorem enqueueNorm_fresh_trailSat
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st : State} {l0 : Literal} {reason : Option Reason}
    (hnew : st.litOnTrail l0.norm = false)
    (hneg : st.negOnTrail l0.norm = false)
    {a : Assignment} (hsol : ProblemSolution problem constraintHolds a)
    (hold : st.TrailSatisfied a)
    (hlit : l0.norm.eval a = some true) :
    (enqueueNorm st l0 reason).TrailSatisfied a := by
  unfold enqueueNorm
  simp only [hnew, hneg, Bool.false_eq_true, if_false]
  -- the new state's trail is the old trail plus the enqueued entry
  intro entry hentry
  have htr : (enqueue st l0.norm reason).trail
      = st.trail ++ [TrailEntry.mk l0.norm st.decisionLevel reason] := rfl
  rw [htr, List.mem_append] at hentry
  rcases hentry with hentry | hentry
  · exact hold entry hentry
  · -- entry is the newly appended one: its literal is l0.norm
    have hentry' : entry = TrailEntry.mk l0.norm st.decisionLevel reason := by
      simpa using hentry
    rw [hentry']
    exact hlit

/-! ### Falsification transfer: trail facts vs. entry literals

The scanning soundness lemmas of `Proofs/Engine.lean` speak about
assignment-level truth (`l.eval a`). The scanning code reads trail
literals. This re-sketch of the falsification argument records where
they meet: `negOnTrail l` asserts the existence of a trail entry whose
literal is (up to norm) `l.negate.norm`; a trail-satisfying assignment
makes that entry's literal true, hence `l` false — via
`Literal.norm_eval` and `Literal.eval_negate` (see
`negOnTrail_falsifies`). All transfer judgments inside the propagation
proofs go through that single gate. -/

/-- Norm transfer for entailment, re-exported for the lift: an
    entailed normalized clause list stays entailed after mapping each
    literal's evaluation identity. -/
theorem entailed_of_eval_transfer
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop} {C C' : Clause}
    (hsub : ∀ l ∈ C, ∃ l' ∈ C', l'.eval = l.eval)
    (h : Clause.EntailedBy problem constraintHolds C) :
    Clause.EntailedBy problem constraintHolds C' :=
  norm_transfer hsub h

/-! ### The propagator-implied entry soundness

Each propagator's `.implied` output enqueues through `enqueueNorm`; the
trail gains a reason entry. Soundness of the new entry needs the
implied literal to be TRUE at every internal solution that the current
state still represents. An explanation clause alone does not give that
(the witness of the clause could be some other disjunct), so the
required premise is the full justification shape: the reason clause's
OTHER disjuncts are falsified by the assignment, forcing the pivot to
be the clause's only possible witness. That is the shape the
per-propagator theorems (Step 2.2) establish from integer-validity of
the propagator nogoods. -/

/-- A justified implied literal is true at every internal solution that
    is represented by the pre-enqueue state: the reason clause is
    entailed, the pivot is a member, and every other disjunct is
    falsified at the represented assignment. -/
theorem implied_sat_of_represented
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {reason : Reason} {l : Literal} {a : Assignment}
    (hcl : reason.clause.EntailedBy problem constraintHolds)
    (hmem : decide (l ∈ reason.clause) = true)
    (hothers : ∀ q ∈ reason.clause, q ≠ l → q.eval a = some false)
    (hsol : ProblemSolution problem constraintHolds a) :
    l.eval a = some true := by
  obtain ⟨w, hw, hevw⟩ := hcl a hsol
  by_cases hwl : w = l
  · rw [← hwl]; exact hevw
  · exfalso
    have hf := hothers w hw hwl
    rw [hevw] at hf
    exact absurd hf (by simp)

end LeanFzn.Solver.LCG

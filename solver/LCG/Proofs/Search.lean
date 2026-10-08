/-
File: solver/LCG/Proofs/Search.lean

Purpose:
  End-to-end internal SAT/UNSAT obligations. Public solve contracts now
  use Proofs.Frontier's exhaustive pending-branch coverage. The remaining
  go/terminal lemmas describe the retained historical analysis loop only;
  its UnsatRun invariants are not prerequisites of the frontier driver.

  Historical analysis-loop proof: SAT is fully discharged and near premise-free: every `.sat` outcome
  passes the engine's leaf test (domain fit + all constraints), proved
  by fuel induction over `lcgSearch.go` (`go_sat_leaf`), so
  `solve_sat_correct` takes only evaluator agreement.

  UNSAT is fully discharged relative to one explicit, honest premise —
  `UnsatRun` — plus the fragment premises (int/bool-viewed domains,
  original-database entitlement, state-universal propagator soundness,
  evaluator agreement). The old `EngineSafe` (obligations over
  ARBITRARY terminal states — unprovable, PLAN.md's central
  objection) is retired. `UnsatRun` instead pins every `.unsat`
  outcome to its generating ENTRY iterate (a state the engine
  actually passes to propagation, at level 0, conflict-free,
  representing every internal solution, with the problem's original
  clause database and entailed learned clauses) and disjoins the
  terminal report into (A) an entitled conflict clause or (B) a
  failed level-0 all-singleton leaf. Both arms are closed by fully
  proved constructive theorems:

  * `unsat_root_conflict_constructive` (arm A): the entry-relative
    master exclusion `propagateLoop_excludes` plus the entitled
    report's witness literal;
  * `unsat_root_leaf_constructive` (arm B): the conflict-free
    transfer `propagateLoop_solvedBy` (proved in `Proofs/Theory`)
    plus the singleton characterization (`Proofs/Singleton`).

  The remaining run-link obligation — carrying `SolvedBy` through
  conflict analysis (repair keeps the sub-trail; the asserting
  enqueue re-justifies via the entailed learned clause) and the
  decision descent — is exactly `UnsatRun`; its discharge is the
  next proof target, not hidden in any `sorry` (this file is
  sorry-free; only the three standard Lean axioms are used).

Dependencies:
  - solver.LCG.Search: executable LCG entry point.
  - solver.LCG.Proofs.Transitions: local transition obligations.
  - solver.LCG.Proofs.Singleton: the singleton characterization
    (Step 2.E item 1) consumed by the leaf exclusion.
  - solver.LCG.Proofs.Theory: the `SolvedBy` master invariant, the
    entry-relative loop transfer pair
    (`propagateLoop_excludes` / `propagateLoop_solvedBy`), the
    decision-level preservation (`propagateLoop_decisionLevel`),
    and the scan inversion twins.
  - solver.LCG.Proofs.Reachability: `IntViewed` (the int/bool
    fragment invariant) used by the initial reachability base.

DAG:
  LCG.Search + LCG.Proofs.Transitions + LCG.Proofs.Lift
  + LCG.Proofs.Singleton + LCG.Proofs.Theory -> LCG.Proofs.Search
-/

import solver.LCG.Search
import solver.LCG.Proofs.Frontier
import solver.LCG.Proofs.Transitions
import solver.LCG.Proofs.Lift
import solver.LCG.Proofs.Singleton
import solver.LCG.Proofs.Theory
import solver.LCG.Proofs.Reachability

namespace LeanFzn.Solver.LCG

open LeanFzn LeanFzn.Solver.Core

/-- Every `.sat` outcome of the engine loop passes the leaf test: the
    assignment fits the original problem domains and satisfies every
    constraint under the Boolean semantics. -/
theorem go_sat_leaf {problem : Problem Constraint Objective}
    {constraintHoldsB : Constraint → Assignment → Bool}
    {props : List Propagator} :
    ∀ (fuel : Nat) (st : State) (a : Assignment),
      lcgSearch.go problem constraintHoldsB props fuel st = .sat a →
        fitsB problem a = true ∧
          problem.constraints.all (fun c => constraintHoldsB c a) = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro st a h
      simp only [lcgSearch.go, lcgSearchGo] at h
      cases h
  | succ fuel ih =>
      intro st a h
      simp only [lcgSearch.go, lcgSearchGo] at h
      -- outermost match: (conflict, decisionLevel)
      split at h
      · -- conflict at 0: unsat, contradiction
        cases h
      · -- conflict above 0
        split at h
        · -- no analysis: chronological fallback; the match on the
          -- conflict clause gates the learning (some [] learns,
          -- backjumps to the second-max falsifier level and flips
          -- the max-level entry's negation; the flip arm splits on
          -- the find?, otherwise the plain chronological retreat)
          split at h
          · -- the conflict clause is some []: the pins gate decides
            split at h
            · -- gate true: the find? split on the max-level entry
              split at h
              · -- some de: the bjL==0 if decides the flip's level
                -- (level 1 at bjL = 0 — the soundness fix; the flip
                -- lands at a positive level either way)
                split at h
                · exact ih _ _ h
                · exact ih _ _ h
              · -- none: the plain retreated state
                exact ih _ _ h
            · exact ih _ _ h
          · -- a nonempty conflict: the plain retreat
            exact ih _ _ h
        · -- analysis: backjump + learn + assert
          exact ih _ _ h
      · -- no conflict: match allSingleton
        split at h
        · -- allSingleton true: match singletonAssignment
          split at h
          · -- some a': leaf if
            split at h
            · -- leaf check true: SAT
              injection h with hinj
              subst hinj
              rename_i hleaf
              rw [Bool.and_eq_true] at hleaf
              exact hleaf
            · -- leaf check false: level if
              split at h
              · -- level 0: unsat, contradiction
                cases h
              · -- level > 0: retreat (gated leaf-nogood learning)
                split at h
                · -- pins gate false: plain retreat
                  exact ih _ _ h
                · -- pins gate true: learn + retreat
                  exact ih _ _ h
          · -- singletonAssignment none: unknown, contradiction
            cases h
        · -- not allSingleton: match decideLiteral
          split at h
          · -- none: unknown, contradiction
            cases h
          · -- some l: recurse
            exact ih _ _ h

/-- Every `.unsat` outcome of the engine loop occurs at some
    post-propagation state in one of the two root-terminal shapes,
    RETAINING the leaf facts (PLAN Step 2.E item 2): at the leaf failure
    the terminal state's domains are all singletons, the complete
    assignment is `some a`, and the leaf test failed at `a`. The stored
    `st0` is the terminal post-propagation state itself. -/
theorem go_unsat_shape {problem : Problem Constraint Objective}
    {constraintHoldsB : Constraint → Assignment → Bool}
    {props : List Propagator} :
    ∀ (fuel : Nat) (st : State),
      lcgSearch.go problem constraintHoldsB props fuel st = .unsat →
        ∃ st0 : State,
          (st0.conflict.isSome = true ∧ st0.decisionLevel = 0)
          ∨
          (∃ a : Assignment,
            st0.conflict = none ∧
            st0.decisionLevel = 0 ∧
            allSingleton st0 = true ∧
            singletonAssignment st0 = some a ∧
            ¬ (fitsB problem a &&
                problem.constraints.all (fun c => constraintHoldsB c a))) := by
  intro fuel
  induction fuel with
  | zero => intro st h; simp only [lcgSearch.go, lcgSearchGo] at h; cases h
  | succ fuel ih =>
      intro st h
      simp only [lcgSearch.go, lcgSearchGo] at h
      split at h
      · -- conflict at level 0: store the terminal state
        next val hval hconf =>
          refine ⟨propagateLoop
              (32 + 8 * st.domains.length + 4 * st.trail.length) props st,
            Or.inl ⟨?_, ?_⟩⟩
          · simp only [Option.isSome_iff_exists]; exact ⟨val, hval⟩
          · simpa using hconf
      · -- conflict above 0: the .unsat (if any) comes from the recursion
        split at h
        · -- no analysis: the fallback's sub-arms (the conflict-clause
          -- match gates the learning; the some [] arm backjumps to
          -- the second-max falsifier level and flips, the nonempty
          -- arm retreats chronologically)
          split at h
          · -- some []: the pins gate decides
            split at h
            · -- gate true: the find? split on the max-level entry
              split at h
              · -- some de: the bjL==0 if (flip level soundness fix)
                split at h
                · exact ih _ h
                · exact ih _ h
              · exact ih _ h
            · exact ih _ h
          · -- nonempty: the plain retreat
            exact ih _ h
        · exact ih _ h
      · -- no conflict; the outermost match already established none
        rename_i hconfnone
        split at h
        · rename_i hsingle
          split at h
          · split at h
            · -- leaf check passed: sat, contradiction with unsat
              cases h
            · split at h
              · -- leaf failed at level 0: retain the full leaf facts
                rename_i a0 hassign hfail hlevel
                refine ⟨propagateLoop
                    (32 + 8 * st.domains.length + 4 * st.trail.length) props st,
                  Or.inr ⟨a0, hconfnone, by simpa using hlevel, hsingle,
                    hassign, hfail⟩⟩
              · -- leaf failed above 0: the .unsat comes from the
                -- retreat (gated leaf-nogood learning)
                split at h
                · -- pins gate false: plain retreat
                  exact ih _ h
                · -- pins gate true: learn + retreat
                  exact ih _ h
          · -- singletonAssignment none: unknown, contradiction
            cases h
        · -- not allSingleton: decide or unknown
          split at h
          · -- unknown, contradiction
            cases h
          · -- decision: the .unsat comes from the recursion
            next l hl => exact ih _ h

/-- A SAT result is an internal problem solution. -/
theorem solve_sat_correct
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {constraintHoldsB : Constraint → Assignment → Bool}
    {propagators : List Propagator} {assignment : Assignment}
    (hagrees : ∀ constraint assignment,
      constraintHoldsB constraint assignment = true ↔
        constraintHolds constraint assignment)
    (hsolve : solve problem constraintHoldsB propagators = .sat assignment) :
    ProblemSolution problem constraintHolds assignment := by
  exact chronological_sat_correct hagrees hsolve

/-! ### The constructive leaf exclusion (PLAN Step 2.E item 2)

The leaf arm, discharged from exactly two explicit obligations the
reachability layer supplies for the leaf state the engine's check
actually observes:

* `hsolvedBy`: the leaf state REPRESENTS every internal solution (the
  master `SolvedBy` invariant threaded through the loop — its
  propagation half is the proved `propagateLoop_solvedBy`);
* `hagrees`: the engine's Boolean leaf semantics agrees with the
  declarative constraint semantics.

Given those, the singleton characterization
(`fits_allSingleton_eq`, `Proofs/Singleton`) forces any fitting
assignment to equal the complete assignment `a`; the leaf test then
fails at `a`, contradicting the solution property. No opaque
engine-safety premise beyond these two remains. -/

/-- THE CONSTRUCTIVE LEAF EXCLUSION. -/
theorem unsat_root_leaf_constructive
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {constraintHoldsB : Constraint → Assignment → Bool}
    {props : List Propagator}
    (st0 : State) (a : Assignment)
    (_hconf : st0.conflict = none) (_hlevel : st0.decisionLevel = 0)
    (hsingle : allSingleton st0 = true)
    (hassign : singletonAssignment st0 = some a)
    (hfail : ¬ (fitsB problem a &&
        problem.constraints.all (fun c => constraintHoldsB c a)))
    (hsolvedBy : ∀ b, ProblemSolution problem constraintHolds b →
      st0.Represents b)
    (hagrees : ∀ constraint assignment,
      constraintHoldsB constraint assignment = true ↔
        constraintHolds constraint assignment) :
    ¬ ∃ assignment, ProblemSolution problem constraintHolds assignment := by
  rintro ⟨assignment, hfit, hcs⟩
  -- the state represents every internal solution, in particular this one:
  obtain ⟨fitLen, trailSat, clsSat, learnedSat⟩ := hsolvedBy assignment
    ⟨hfit, hcs⟩
  -- the internal solution fits the state's domains:
  have hfitsSt : assignment.Fits st0.domains := fitLen
  -- the singleton characterization: every fitting assignment IS a
  have hEq : assignment = a := fits_allSingleton_eq hsingle hfitsSt hassign
  subst hEq
  -- the leaf test fails at a, but the solution property (fit +
  -- constraints under the agreed semantics) makes the test pass:
  apply hfail
  rw [Bool.and_eq_true]
  refine ⟨fitsB_iff.mpr ⟨hfit.1, hfit.2⟩, ?_⟩
  rw [List.all_eq_true]
  intro constraint hcons
  have hval : constraintHoldsB constraint assignment = true :=
    (hagrees constraint assignment).mpr (hcs constraint hcons)
  exact hval

/-- The root-fact fold's conflict and learned fields are preserved
    (enqueue writes neither). -/
theorem enqueue_learned {st : State} {l : Literal} :
    (enqueue st l none).learned = st.learned := rfl

theorem enqueue_conflict {st : State} {l : Literal} :
    (enqueue st l none).conflict = st.conflict := rfl

theorem fold_preserves_fields : ∀ (rs : List Literal) (acc : State),
    acc.conflict = none → acc.learned = [] →
      ((rs.foldl (fun st l => if st.litOnTrail l = true then st
          else enqueue st l none) acc)).conflict = none ∧
      ((rs.foldl (fun st l => if st.litOnTrail l = true then st
          else enqueue st l none) acc)).learned = [] := by
  intro rs acc hc hl
  induction rs generalizing acc with
  | nil => exact ⟨hc, hl⟩
  | cons l rest ih =>
      rw [List.foldl_cons]
      cases hb : acc.litOnTrail l with
      | true =>
          exact ih acc hc hl
      | false =>
          show ((rest.foldl (fun st l => if st.litOnTrail l = true then st
            else enqueue st l none)
            ((enqueue acc l none : State)) : State)).conflict = none ∧ _
          have hc2 : (enqueue acc l none).conflict = none :=
            enqueue_conflict (st := acc) (l := l) ▸ hc
          have hl2 : (enqueue acc l none).learned = [] :=
            enqueue_learned (st := acc) (l := l) ▸ hl
          exact ih (enqueue acc l none) hc2 hl2

/-- The initial state's conflict is clear and its learned list is
    empty. -/
theorem initialWithRoots_fields (problem : Problem Constraint Objective) :
    (initialStateWithRoots problem).conflict = none ∧
    (initialStateWithRoots problem).learned = [] := by
  unfold initialStateWithRoots
  exact fold_preserves_fields (rootFacts problem.domains)
    (initialState problem) rfl rfl

/-! ### The initial reachability base (PLAN item 7, obligation (a))

The initial state solves-by: every internal solution is represented by
`initialStateWithRoots`. The trail is the root-fact list (each entry's
literal is a root fact, true at every fitting assignment under the
int/bool fragment invariant `IntViewed`); the clause database is the
problem's; the learned database is empty. -/

/-- Every value of any indexed domain slot lies in some member of the
    domain list. -/
theorem exists_mem_of_mem_getD : ∀ (doms : List (List Value)) (i : Nat)
    (x : Value), x ∈ doms.getD i [] → ∃ d ∈ doms, x ∈ d := by
  intro doms
  induction doms with
  | nil => intro i x h; simp at h
  | cons d rest ih =>
      intro i x h
      match i, h with
      | 0, h =>
          rw [show (d :: rest).getD 0 [] = d from rfl] at h
          exact ⟨d, List.mem_cons_self, h⟩
      | (i + 1), h =>
          rw [show (d :: rest).getD (i + 1) [] = rest.getD i [] from rfl] at h
          obtain ⟨d2, hd, hxd⟩ := ih i x h
          exact ⟨d2, List.mem_cons_of_mem _ hd, hxd⟩

/-- Under `IntViewedDoms`, every value of any indexed slot has an
    integer view. -/
theorem intViewedDoms_getD {doms : List (List Value)}
    (h : IntViewedDoms doms) :
    ∀ (i : Nat) (v : Value), v ∈ doms.getD i [] → Value.intView v ≠ none := by
  intro i v hv
  obtain ⟨d, hd, hvd⟩ := exists_mem_of_mem_getD doms i v hv
  exact h d hd v hvd

/-- One root-fact fold step: the resulting trail contains only old
    entries plus (possibly) one new entry carrying the fold's literal. -/
theorem fold_step_trail {st : State} {l : Literal} :
    ∀ e : TrailEntry, e ∈
      (if st.litOnTrail l then st else enqueue st l none).trail →
      e.literal = l ∨ e ∈ st.trail := by
  intro e he
  cases hb : st.litOnTrail l with
  | true =>
      rw [if_pos hb] at he
      exact Or.inr he
  | false =>
      rw [if_neg (by rw [hb]; simp)] at he
      have htr : (enqueue st l none).trail
          = st.trail ++ [TrailEntry.mk l st.decisionLevel none] := rfl
      rw [htr, List.mem_append] at he
      rcases he with he | he
      · exact Or.inr he
      · have heq : e = TrailEntry.mk l st.decisionLevel none := by simpa using he
        rw [heq]
        exact Or.inl rfl

/-- The root-fact fold's trail: every entry either carries one of the
    folded literals or came from the seed state's trail. -/
theorem fold_trail_mem : ∀ (rs : List Literal) (st : State) (e : TrailEntry),
    e ∈ ((rs.foldl (fun st l =>
      if st.litOnTrail l then st else enqueue st l none) st).trail) →
    e.literal ∈ rs ∨ e ∈ st.trail := by
  intro rs
  induction rs with
  | nil => intro st e he; exact Or.inr he
  | cons l rest ih =>
      intro st e he
      rw [List.foldl_cons] at he
      rcases ih (if st.litOnTrail l then st else enqueue st l none) e he with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · rcases fold_step_trail (st := st) (l := l) e h with h' | h'
        · exact Or.inl (h' ▸ List.mem_cons_self)
        · exact Or.inr h'

/-- The root-fact fold preserves the clause list. -/
theorem rootFold_clauses : ∀ (rs : List Literal) (st : State),
    ((rs.foldl (fun st l =>
      if st.litOnTrail l then st else enqueue st l none) st).clauses)
      = st.clauses := by
  intro rs
  induction rs with
  | nil => intro st; rfl
  | cons l rest ih =>
      intro st
      rw [List.foldl_cons]
      split
      · exact ih st
      · have h1 := ih (enqueue st l none)
        rw [(show (enqueue st l none).clauses = st.clauses from rfl)] at h1
        exact h1

/-- The initial state's trail carries only root facts (the seed trail is
    empty). -/
theorem initialWithRoots_trail_mem (problem : Problem Constraint Objective) :
    ∀ e ∈ (initialStateWithRoots problem).trail,
      e.literal ∈ rootFacts problem.domains := by
  intro e he
  unfold initialStateWithRoots at he
  rcases fold_trail_mem (rootFacts problem.domains) (initialState problem) e he
    with h | h
  · exact h
  · exfalso
    have htr : (initialState problem).trail = [] := rfl
    rw [htr] at h
    exact absurd h (by simp)

/-- The initial state's clause database is the problem's. -/
theorem initialWithRoots_clauses (problem : Problem Constraint Objective) :
    (initialStateWithRoots problem).clauses = problem.clauses := by
  unfold initialStateWithRoots
  have h1 := rootFold_clauses (rootFacts problem.domains) (initialState problem)
  have h2 : (initialState problem).clauses = problem.clauses := rfl
  rw [h1, h2]

/-- THE INITIAL REACHABILITY BASE: under the int/bool fragment invariant
    (`IntViewed problem`) and entitlement of the initial clause database,
    every internal problem solution is represented by the state the search
    actually starts from. -/
theorem initialWithRoots_solvedBy {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    (hview : IntViewed problem)
    (hdb0 : ∀ c ∈ problem.clauses,
      ∀ a, ProblemSolution problem constraintHolds a →
        ∃ l ∈ c, l.eval a = some true) :
    SolvedBy problem constraintHolds (initialStateWithRoots problem) := by
  intro a ha
  refine ⟨?fit, ?trail, ?clauses, ?learned⟩
  · rw [initialStateWithRoots_domains]
    exact ha.1
  · intro e he
    have hmem : e.literal ∈ rootFacts problem.domains :=
      initialWithRoots_trail_mem problem e he
    refine rootFacts_valid (hfit := ha.1) (hview := ?_) e.literal hmem
    intro l hl v hv
    exact intViewedDoms_getD hview l.atom.slot v hv
  · intro c hc
    rw [initialWithRoots_clauses] at hc
    exact hdb0 c hc a ha
  · have h2 := (initialWithRoots_fields problem).2
    intro c hc
    rw [h2] at hc
    exact absurd hc (by simp)

/-! ### The constructive conflict exclusion (PLAN Step 2.E items 3–6)

The conflict arm, discharged from the master loop results: a conflict
reported by a conflict-free propagation run that starts at a
solved-by iterate with entitled databases refutes every internal
solution — `propagateLoop_excludes` excludes all solutions and hands
back the reported clause; each entailed-database clause then supplies
its witness literal, contradicting the exclusion at the assumed
solution. The per-family soundness (`PropSafeUniv`) is the fragment
assumption (PLAN Step 2.2); the clause entitlements are stated at the
ENTRY state's fixed databases (the lists never change during a run),
not universally over all states. -/

/-- THE CONSTRUCTIVE CONFLICT EXCLUSION (entry-relative form).

    A conflict reported by the engine-fuel propagation run from a
    conflict-free solved-by entry state refutes every internal
    solution — GIVEN the reported clause's entitlement (true at every
    solution). The exclusion half is fully discharged from the master
    loop result (`propagateLoop_excludes`, `Proofs/Theory`); the
    entitlement half (`hent`) is the remaining obligation, whose
    discharge decomposes by the report's origin (`propagateLoop_lift`,
    `Proofs/Lift`): a scan-witnessed conflict draws it from the entry
    databases (fixed through the run), a propagator report from
    `PropEntitled`, and the opposing-fact pair from the fold
    justification (the justified implied literal makes the pair
    satisfied, contradicting exclusion). -/
theorem unsat_root_conflict_constructive
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {props : List Propagator}
    (st' : State)
    (hconfEntry : st'.conflict = none)
    (huniv : CoherentSafeUniv problem constraintHolds props)
    (hsolvedBy : SolvedBy problem constraintHolds st')
    (hclauses : st'.clauses = problem.clauses)
    (hlearned : ∀ c ∈ st'.learned,
      c.EntailedBy problem constraintHolds)
    (hdb0 : ∀ c ∈ problem.clauses,
      ∀ a, ProblemSolution problem constraintHolds a →
        ∃ l ∈ c, l.eval a = some true)
    (hcohEntry : DomainCoherent problem st')
    (hisolvable : ∃ b, ProblemSolution problem constraintHolds b)
    (hentFam : ∀ (st : State), DomainCoherent problem st →
      ∀ (p : Propagator), p ∈ props → ∀ (c : Clause),
      p.run st = .conflict c →
        SolvedBy problem constraintHolds st →
        ∀ a, ProblemSolution problem constraintHolds a →
          ∃ l ∈ c, l.eval a = some true)
    (hrep : (propagateLoop
        (32 + 8 * st'.domains.length + 4 * st'.trail.length)
        props st').conflict.isSome = true) :
    ¬ ∃ assignment, ProblemSolution problem constraintHolds assignment := by
  -- entitlement of the entry databases (witness form over solutions):
  have hentO : ∀ c ∈ st'.clauses, ∀ a, ProblemSolution
      problem constraintHolds a → ∃ l ∈ c, l.eval a = some true := by
    intro c hc a ha
    rw [hclauses] at hc
    exact hdb0 c hc a ha
  have hentL : ∀ c ∈ st'.learned, ∀ a, ProblemSolution
      problem constraintHolds a → ∃ l ∈ c, l.eval a = some true := by
    intro c hc a ha
    obtain ⟨w, hw, hev⟩ := hlearned c hc a ha
    exact ⟨w, hw, hev⟩
  -- the loop-level ORIGIN ENTITLEMENT (proved in Theory.lean): the
  -- reported clause carries a true literal at every internal solution
  have hentRun := propagateLoop_conflict_entitled
    (problem := problem) (constraintHolds := constraintHolds)
    (props := props) hisolvable huniv hentFam st'.clauses st'.learned
    hentO hentL
    (32 + 8 * st'.domains.length + 4 * st'.trail.length) st'
    hconfEntry hsolvedBy hcohEntry rfl rfl
  -- the master exclusion: the reported clause is satisfied at no solution
  obtain ⟨cc, hrepC, hexc⟩ := propagateLoop_excludes
    (problem := problem) (constraintHolds := constraintHolds)
    (props := props) huniv hisolvable st'.clauses st'.learned
    hentO hentL
    (32 + 8 * st'.domains.length + 4 * st'.trail.length) st'
    hconfEntry hsolvedBy hcohEntry rfl rfl hrep
  -- the two theorems speak of the same reported clause:
  have hentCla : ∀ a, ProblemSolution problem constraintHolds a →
      ∃ l ∈ cc, l.eval a = some true := hentRun cc hrepC
  rintro ⟨assignment, hsol⟩
  have hexcla : ¬ cc.SatisfiedBy assignment := hexc assignment hsol
  obtain ⟨w, hw, hev⟩ := hentCla assignment hsol
  exact hexcla ⟨w, hw, hev⟩

/-! ### The constructive conflict exclusion (PLAN Step 2.E items 3–6)

The conflict arm of `EngineSafe`, discharged from the master
`propagateLoop_excludes` result (item 6): a conflict reported by a
conflict-free propagation run over state-universally sound propagators
excludes every internal solution. The per-family soundness
(`PropSafeUniv`) is the fragment assumption — the PLAN's Step 2.2
obligation — together with the clause-entitlement chain (originals via
the problem's proved clauses, learned via Step 1's entailment). -/

/-! ### The go-level structural inversion

`go_unsat_entry`: every `.unsat` outcome of the engine loop arises at
a level-0 post-propagation state whose generating ENTRY iterate — the
state the engine passed to propagation — is exhibited. The conflict
arm's entry level and the leaf arm's level both transfer from the
observed post-propagation level via `propagateLoop_decisionLevel`
(with the engine's explicit fuel expression), and the leaf facts
(conflict-free run, all-singleton, complete assignment, failed leaf
test) come from the arm's own scrutinee splits. The recursion arms
(analysis, retreat, decision) delegate to the induction hypothesis,
carrying the entry identification through. -/

/-- Structural inversion: any `.unsat` of the engine occurs at a level-0
    post-propagation state whose ENTRY (pre-propagation iterate) we can
    exhibit — the fuel induction carries nothing but the entry
    identification. -/
theorem go_unsat_entry
    {problem : Problem Constraint Objective}
    {constraintHoldsB : Constraint → Assignment → Bool}
    {props : List Propagator} :
    ∀ (fuel : Nat) (st : State),
      lcgSearch.go problem constraintHoldsB props fuel st = .unsat →
        ∃ st' : State,
          st'.decisionLevel = 0 ∧
          ((propagateLoop (engineFuel st') props st').conflict.isSome = true
            ∨
          ((propagateLoop (engineFuel st') props st').conflict = none ∧
            allSingleton (propagateLoop (engineFuel st') props st') = true ∧
            ∃ a, singletonAssignment (propagateLoop (engineFuel st') props st')
              = some a ∧
              ¬ (fitsB problem a &&
                  problem.constraints.all (fun c => constraintHoldsB c a))))
  := by
  intro fuel
  induction fuel with
  | zero => intro st h; simp only [lcgSearch.go, lcgSearchGo] at h; cases h
  | succ fuel ih =>
      intro st h
      simp only [lcgSearch.go, lcgSearchGo] at h
      split at h
      · -- conflict at level 0: the terminal arm; st is the entry
        next w hw hlev =>
          -- the entry level: propagation preserves the level
          have hpl := propagateLoop_decisionLevel props
            (32 + 8 * st.domains.length + 4 * st.trail.length) st
          rw [hpl] at hlev
          refine ⟨st, hlev, Or.inl ?_⟩
          -- the observed post-propagation conflict is SOME clause
          simp only [Option.isSome_iff_exists]
          exact ⟨w, hw⟩
      · -- conflict above 0: recursion through the analysis arms
        split at h
        · -- no analysis: the fallback's sub-arms (the conflict-clause
          -- match gates the learning; the some [] arm backjumps to
          -- the second-max falsifier level and flips, the nonempty
          -- arm retreats chronologically)
          split at h
          · -- some []: the pins gate decides
            split at h
            · -- gate true: the find? split on the max-level entry
              split at h
              · -- some de: the bjL==0 if (flip level soundness fix)
                split at h
                · exact ih _ h
                · exact ih _ h
              · exact ih _ h
            · exact ih _ h
          · -- nonempty: the plain retreat
            exact ih _ h
        · exact ih _ h
      · -- no conflict: leaf or decision arms
        next hnone =>
        split at h
        · next hsingle =>
          split at h
          · split at h
            · cases h
            · split at h
              · -- leaf failed at level 0: st is the entry; leaf facts
                next a0 hassign hfail hlevel0 =>
                  -- entry level via preservation (Bool-level first)
                  have hl0 : (propagateLoop
                      (32 + 8 * st.domains.length + 4 * st.trail.length)
                      props st).decisionLevel = 0 := by
                    simp only [beq_iff_eq] at hlevel0
                    exact hlevel0
                  have hpl := propagateLoop_decisionLevel props
                    (32 + 8 * st.domains.length + 4 * st.trail.length) st
                  rw [hpl] at hl0
                  exact ⟨st, hl0, Or.inr ⟨hnone, hsingle, a0, hassign, hfail⟩⟩
              · -- leaf failed above 0: the gated retreat
                split at h
                · exact ih _ h
                · exact ih _ h
          · cases h
        · split at h
          · cases h
          · exact ih _ h


/-! ### The run-level UNSAT premise (retiring `EngineSafe`)

The old `EngineSafe` bundle quantified over arbitrary terminal
states — unprovable from facts about the engine's actual run
(PLAN.md's central objection). `UnsatRun` replaces it: every `.unsat`
outcome of the engine loop arises at a post-propagation state whose
generating ENTRY iterate (a state the engine actually passes to
propagation) sits at decision level 0, represents every internal
solution (`SolvedBy`), holds the problem's original clause database,
and carries only entailed learned clauses. Its discharge decomposes
into proved entry-relative results (`propagateLoop_solvedBy`,
`propagateLoop_excludes`, `propagateLoop_decisionLevel` —
`Proofs/Theory`) plus the registered run-link obligation: the
`SolvedBy`-preservation through conflict analysis (repair keeps the
sub-trail) and the decision descent, the PLAN's next proof target. -/

/-- The remaining UNSAT obligation, now stated over the REAL run shape
    (not arbitrary terminal states): every `.unsat` outcome of the
    engine loop arises from a generating pre-propagation ENTRY iterate
    — a state the engine actually passes to propagation — that sits
    at decision level 0, is conflict-free, represents every internal
    solution (`SolvedBy`), holds the problem's original clause
    database, carries only entailed learned clauses, and whose
    engine-fuel propagation run reports either (A) an entitled
    conflict clause (true literal at every solution — feeds
    `unsat_root_conflict_constructive` below), or (B) the failed
    level-0 leaf (all-singleton, complete assignment failing the leaf
    test — feeds `unsat_root_leaf_constructive` below, via
    `propagateLoop_solvedBy`).

    Downstream discharge (the remaining run-link obligation): a fuel
    induction over `lcgSearch.go` carrying the invariant through the
    six arms. The propagation halves are all proved
    (`propagateLoop_solvedBy` for the conflict-free run,
    `propagateLoop_conflict_entitled` for the reported clause's
    entitlement — consumed directly by
    `unsat_root_conflict_constructive` below, so the conflict arm of
    this premise needs only `isSome` — and
    `propagateLoop_decisionLevel` for the level); the repair half is
    proved for the level-0 case (`repair_solvedBy0` +
    `enqueueNorm_level0_sound` via `Level0TrailSound`). REMAINING:
    the analysis-arm transfer at positive levels (the asserting
    enqueue re-justifies via the entailed learned clause —
    `analyzeConflict_correct` supplies the entailment under
    `AnalysisReady`) and the decision descent. Unlike the retired
    `EngineSafe`, this premise quantifies only over iterates the
    engine actually reaches, and both arms are consumed by fully
    proved constructive theorems. -/
structure UnsatRun (problem : Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop)
    (constraintHoldsB : Constraint → Assignment → Bool)
    (props : List Propagator) : Prop where
  unsat_entry : ∀ (fuel : Nat) (st : State),
    lcgSearch.go problem constraintHoldsB props fuel st = .unsat →
    ∃ st' : State,
      st'.decisionLevel = 0 ∧
      st'.conflict = none ∧
      SolvedBy problem constraintHolds st' ∧
      DomainCoherent problem st' ∧
      st'.clauses = problem.clauses ∧
      (∀ c ∈ st'.learned, c.EntailedBy problem constraintHolds) ∧
      ((propagateLoop (engineFuel st') props st').conflict.isSome = true
        ∨
        ((propagateLoop (engineFuel st') props st').conflict = none ∧
          allSingleton (propagateLoop (engineFuel st') props st') = true ∧
          ∃ a, singletonAssignment (propagateLoop (engineFuel st') props st')
            = some a ∧
            ¬ (fitsB problem a &&
                problem.constraints.all (fun c => constraintHoldsB c a))))

/-- An UNSAT result excludes every internal problem solution —
    fully proved relative to the run-link premise (see `UnsatRun`)
    and the fragment premises: entitlement of the original clause
    database, state-universal propagator soundness, and evaluator
    agreement. (The int/bool fragment invariant `IntViewed` enters at
    `UnsatRun`'s discharge — the initial solvedBy — not here: the
    entry-state facts arrive ready-made.) The engine inversion
    `go_unsat_shape` pins every `.unsat` outcome to one of the two
    root-terminal shapes; `UnsatRun` pins its generating entry; the
    two constructive theorems then refute every internal
    solution. -/
theorem solve_unsat_correct
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {constraintHoldsB : Constraint → Assignment → Bool}
    {propagators : List Propagator}
    (hdb0 : ∀ c ∈ problem.clauses,
      ∀ a, ProblemSolution problem constraintHolds a →
        ∃ l ∈ c, l.eval a = some true)
    (huniv : CoherentSafeUniv problem constraintHolds propagators)
    (hentFam : ∀ (st : State), DomainCoherent problem st →
      ∀ (p : Propagator), p ∈ propagators →
      ∀ (c : Clause), p.run st = .conflict c →
        SolvedBy problem constraintHolds st →
        ∀ a, ProblemSolution problem constraintHolds a →
          ∃ l ∈ c, l.eval a = some true)
    (hagrees : ∀ constraint assignment,
      constraintHoldsB constraint assignment = true ↔
        constraintHolds constraint assignment)
    (hsafe : UnsatRun problem constraintHolds constraintHoldsB propagators)
    (hsolve : solve problem constraintHoldsB propagators = .unsat) :
    ¬ ∃ assignment, ProblemSolution problem constraintHolds assignment := by
  exact chronological_unsat_correct hagrees hdb0 hsolve

/-! ### The decision-free fragment's discharge of `UnsatRun`

At a disciplined entry (level 0, ≤1 per slot, the run invariants),
the engine loop neither decides nor recurses (`go_fragment_no_decide`,
`Proofs/Theory`): the `.unsat` outcome arises at that very state.
The `UnsatRun` premise, however, must exhibit the invariants at the
entry itself; within the fragment those inflate to the initial state's
facts only when the entry came from the initial descent. The honest
fragment discharge therefore ASSUMES the run invariants at the entry
(they hold at the initial state by the base lemmas and survive the
fragment's decision-free run) — a restricted, honest premise. -/

/-- THE FRAGMENT-DISCIPLINED DISCHARGE of `UnsatRun`'s obligation:
    at a level-0, ≤1-disciplined, conflict-free, solved-by entry
    with the problem's clauses and entailed learned clauses, the
    `.unsat` outcome occurs at THIS state in one of the two terminal
    shapes. -/
theorem unsat_entry_fragment
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {constraintHoldsB : Constraint → Assignment → Bool}
    {props : List Propagator}
    (hfrag : PropFragment problem) :
    ∀ (fuel : Nat) (st : State),
      st.decisionLevel = 0 →
      st.conflict = none →
      SolvedBy problem constraintHolds st →
      st.clauses = problem.clauses →
      (∀ c ∈ st.learned, c.EntailedBy problem constraintHolds) →
      (∀ s : Nat, (st.domains.getD s []).length ≤ 1) →
      DomainCoherent problem st →
      lcgSearch.go problem constraintHoldsB props fuel st = .unsat →
        ∃ st' : State,
          st'.decisionLevel = 0 ∧
          st'.conflict = none ∧
          SolvedBy problem constraintHolds st' ∧
          DomainCoherent problem st' ∧
          st'.clauses = problem.clauses ∧
          (∀ c ∈ st'.learned, c.EntailedBy problem constraintHolds) ∧
          ((propagateLoop (engineFuel st') props st').conflict.isSome = true
            ∨
          ((propagateLoop (engineFuel st') props st').conflict = none ∧
            allSingleton (propagateLoop (engineFuel st') props st') = true ∧
            ∃ a, singletonAssignment (propagateLoop (engineFuel st') props st')
              = some a ∧
            ¬ (fitsB problem a &&
                problem.constraints.all (fun c => constraintHoldsB c a)))) := by
  intro fuel st hlev hconf hsolvedBy hclauses hlearned hdisc hcoh hgo
  exact ⟨st, hlev, hconf, hsolvedBy, hcoh, hclauses, hlearned,
    go_fragment_no_decide fuel st hlev hdisc hgo⟩

/-! ### The fragment's certified solve -/

/-- THE FRAGMENT'S `solve_certified`: for a decision-free fragment
    problem (all-singleton initial domains), both SAT and UNSAT are
    fully proved relative ONLY to the fragment's own checks —
    `IntViewed` (the int/bool fragment invariant), the original
    database's entitlement, state-universal propagator soundness
    (with its report-entitlement refinement), and evaluator
    agreement. The `UnsatRun` premise is DISCHARGED internally: the
    engine's entry is the rooted initial state, whose level-0,
    conflict-free, solved-by, clause, empty-learned, and ≤1 facts
    are the proved base lemmas; `go_fragment_no_decide` then exhibits
    the entry itself as the generating state. -/
theorem solve_certified_fragment
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {constraintHoldsB : Constraint → Assignment → Bool}
    {propagators : List Propagator}
    (hview : IntViewed problem)
    (hfrag : PropFragment problem)
    (hdb0 : ∀ c ∈ problem.clauses,
      ∀ a, ProblemSolution problem constraintHolds a →
        ∃ l ∈ c, l.eval a = some true)
    (huniv : CoherentSafeUniv problem constraintHolds propagators)
    (hentFam : ∀ (st : State), DomainCoherent problem st →
      ∀ (p : Propagator), p ∈ propagators →
      ∀ (c : Clause), p.run st = .conflict c →
        SolvedBy problem constraintHolds st →
        ∀ a, ProblemSolution problem constraintHolds a →
          ∃ l ∈ c, l.eval a = some true)
    (hagrees : ∀ constraint assignment,
      constraintHoldsB constraint assignment = true ↔
        constraintHolds constraint assignment)
    (hsat : solve problem constraintHoldsB propagators = .sat assignment) :
    ProblemSolution problem constraintHolds assignment := by
  -- the SAT direction needs only the evaluator agreement (the leaf
  -- test establishes Fits + every constraint directly); the fragment,
  -- database, and safety premises are the UNSAT direction's inputs,
  -- kept here so the two front-door theorems share one shape
  exact solve_sat_correct (problem := problem)
    (constraintHolds := constraintHolds) hagrees hsat

theorem solve_certified_fragment_unsat
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {constraintHoldsB : Constraint → Assignment → Bool}
    {propagators : List Propagator}
    (hview : IntViewed problem)
    (hfrag : PropFragment problem)
    (hdb0 : ∀ c ∈ problem.clauses,
      ∀ a, ProblemSolution problem constraintHolds a →
        ∃ l ∈ c, l.eval a = some true)
    (huniv : CoherentSafeUniv problem constraintHolds propagators)
    (hentFam : ∀ (st : State), DomainCoherent problem st →
      ∀ (p : Propagator), p ∈ propagators →
      ∀ (c : Clause), p.run st = .conflict c →
        SolvedBy problem constraintHolds st →
        ∀ a, ProblemSolution problem constraintHolds a →
          ∃ l ∈ c, l.eval a = some true)
    (hagrees : ∀ constraint assignment,
      constraintHoldsB constraint assignment = true ↔
        constraintHolds constraint assignment)
    (hunsat : solve problem constraintHoldsB propagators = .unsat) :
    ¬ ∃ assignment, ProblemSolution problem constraintHolds assignment := by
  exact chronological_unsat_correct hagrees hdb0 hunsat

end LeanFzn.Solver.LCG

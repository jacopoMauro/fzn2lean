/- Shared rooted-state soundness, independent of search strategies. -/
import LeanFzn.Solver.Propagation.Proofs.Theory
import LeanFzn.Solver.Propagation.Proofs.Reachability


namespace LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Reference
open LeanFzn LeanFzn.Solver.Core

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
theorem initialWithRoots_fields (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective) :
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
theorem exists_mem_of_mem_getD : ∀ (doms : List Domain) (i : Nat)
    (x : Value), x ∈ doms.getD i Dom.empty → ∃ d ∈ doms, x ∈ d := by
  intro doms
  induction doms with
  | nil => intro i x h; simp at h
  | cons d rest ih =>
      intro i x h
      match i, h with
      | 0, h =>
          rw [show (d :: rest).getD 0 Dom.empty = d from rfl] at h
          exact ⟨d, List.mem_cons_self, h⟩
      | (i + 1), h =>
          rw [show (d :: rest).getD (i + 1) Dom.empty = rest.getD i Dom.empty from rfl] at h
          obtain ⟨d2, hd, hxd⟩ := ih i x h
          exact ⟨d2, List.mem_cons_of_mem _ hd, hxd⟩

/-- Under `IntViewedDoms`, every value of any indexed slot has an
    integer view. -/
theorem intViewedDoms_getD {doms : List Domain}
    (h : IntViewedDoms doms) :
    ∀ (i : Nat) (v : Value), v ∈ doms.getD i Dom.empty → Value.intView v ≠ none := by
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
theorem initialWithRoots_trail_mem (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective) :
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
theorem initialWithRoots_clauses (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective) :
    (initialStateWithRoots problem).clauses = problem.clauses := by
  unfold initialStateWithRoots
  have h1 := rootFold_clauses (rootFacts problem.domains) (initialState problem)
  have h2 : (initialState problem).clauses = problem.clauses := rfl
  rw [h1, h2]

/-- THE INITIAL REACHABILITY BASE: under the int/bool fragment invariant
    (`IntViewed problem`) and entitlement of the initial clause database,
    every internal problem solution is represented by the state the search
    actually starts from. -/
theorem initialWithRoots_solvedBy {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
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


end LeanFzn.Solver.Propagation

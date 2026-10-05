/-
File: solver/LCG/Proofs/Reason.lean

Purpose:
  The premise-discharge layer for the decision-descent master theorem
  `go_unsat_entry_invariant` (PLAN.md §5 item 2): the three explicit
  premises the wide UNSAT front door must supply —

  * `ReasonSafeUniv` (hreason): every propagator-implied literal
    carries a VALID, NORMALIZED reason — proved here STATE-FREE (no
    coherence/representation premises) for ten of the eleven
    registered families via the two-case disjunction on each
    family's constraint (e.g. for `x ≤ y` the nogood `[x ≤ yj,
    y > yj]` reads "x ≤ yj ∨ y > yj", entailed by x ≤ y alone:
    either y > yj (tail true) or y ≤ yj (then x ≤ y ≤ yj, head
    true)). linLe is EXCLUDED (machine-checked obstruction, see
    `solver/LCG/Proofs/Obstructions.lean`'s linLeObstruction
    witnesses:
    propLinLe emits causes only for ±1-coefficient terms, so e.g.
    `x + 2t ≤ 0` emits the unit clause `[x ≤ 0]`, falsified by the
    solution x=3, t=-2). The obstruction witness is preserved in
    `solver/LCG/Proofs/Obstructions.lean`.) The wide front door gates
    linLe away; the singleton front door (`solve_certified_unsat_real`)
    keeps its SolvedBy-based coverage.

  * the level-0 justification (hjust, rooted form): at a ROOTED
    level-0 coherent accumulator with RootFacts, every
    propagator-implied literal is true at every internal solution
    (root facts pin the domain bounds, so every solution fits the
    folded domains, and each family's impliedTrueAt half applies).

  * the run-scoped conflict entitlement (hconfent, the cc ≠ []
    version): every NONEMPTY conflict clause reported by the
    propagation loop at a RunInv state is entailed. The neSlot
    family's conflict clause is the EMPTY clause (Propagate.lean:
    `| [x], [y] => if x.eqB y then .conflict []`) — never entailed
    at decision-narrowed states — but also never analyzed
    (`analyzeConflict_empty_none` in Proofs/Run.lean), which is
    exactly why the master theorem's hconfent carries `cc ≠ []`.

  Also here: the initial-state seeds for the master theorem's
  application (`initialStateWithRoots_runInv`,
  `initialStateWithRoots_level0Solved` — from the RunInv/Level0Solved
  base lemmas of Proofs/Search.lean + the fold-level facts).

Dependencies:
  - solver.LCG.Proofs.Propagators (the family views, the
    propagatorOfProved emission inversion)
  - solver.LCG.Proofs.ConstFamilies (the narrow inversions, the
    const families' own reason/entitlement lemmas)
  - solver.LCG.Proofs.Run (ReasonSafeUniv, RunInv, Level0Solved,
    the empty-conflict lemmas)

DAG:
  Propagate + Theory + ConstFamilies + Run -> Reason -> Certified
-/

import solver.LCG.Proofs.Propagators
import solver.LCG.Proofs.ConstFamilies
import solver.LCG.Proofs.Run
import solver.LCG.Proofs.Search

namespace LeanFzn.Solver.LCG

open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Solver (DomConstraint)

/-! ## Shared structural kernels -/

/-- Reason validity from clause truth: when some member of the reason
    clause is true at every internal solution, the reason's clause is
    entailed; with pivot membership the reason is valid. -/
theorem reason_valid_of_clause_true
    {problem : Problem DomConstraint Unit}
    {l : Literal} {r : Reason}
    (hmem : l ∈ r.clause)
    (htrue : ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
      ∃ l' ∈ r.clause, l'.eval a = some true) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l :=
  ⟨fun a ha => htrue a ha, decide_eq_true hmem⟩

/-- Normalization transfer from the raw emitted clause. -/
theorem reason_clause_norm_sf {r : Reason} {ng : Clause}
    (hcl : r = { clause := ng })
    (hnorm : ∀ q ∈ ng, q = q.norm) :
    ∀ q ∈ r.clause, q = q.norm := by
  intro q hq
  rw [hcl] at hq
  exact hnorm q hq

/-- A two-literal order clause is normalized: on `posLe`/`negLe`
    literals `Literal.norm` is the identity. -/
theorem order2_norm {l1 l2 : Literal}
    (h1 : l1 = l1.norm) (h2 : l2 = l2.norm) :
    ∀ q ∈ [l1, l2], q = q.norm := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact h1
  · rw [List.mem_singleton.mp hq]
    exact h2

/-- A three-literal order clause is normalized. -/
theorem order3_norm {l1 l2 l3 : Literal}
    (h1 : l1 = l1.norm) (h2 : l2 = l2.norm) (h3 : l3 = l3.norm) :
    ∀ q ∈ [l1, l2, l3], q = q.norm := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact h1
  · rcases List.mem_cons.mp hq with rfl | hq
    · exact h2
    · rw [List.mem_singleton.mp hq]
      exact h3

/-! ## The opposing-fact pair (the sweep's third conflict origin)

The propagator sweep sets a conflict `[l.norm, ¬l.norm]` when an
implied literal contradicts the trail. At a `ProblemSolution` the pair
is satisfied whenever the implied literal is DECIDED there (evaluates
to `some b`) — each family's constraint forces the relevant raw reads,
so its implied order/Boolean literals are decided at every internal
solution with no state premise. -/

/-- A decided literal's opposing pair carries a true literal. -/
theorem pair_true_of_decided {l : Literal} {a : Assignment}
    (hdec : ∃ b, l.eval a = some b) :
    ∃ q ∈ [l.norm, (l.norm).negate], q.eval a = some true := by
  obtain ⟨b, hb⟩ := hdec
  cases b with
  | true =>
      exact ⟨l.norm, List.mem_cons_self, by
        rw [Literal.norm_eval l a]; exact hb⟩
  | false =>
      exact ⟨(l.norm).negate, List.mem_cons_of_mem _ List.mem_cons_self, by
        rw [Literal.eval_negate (l.norm) a, Literal.norm_eval l a, hb]
        rfl⟩

/-- Normalization is invisible to `negOnTrail` (the trail matches the
    canonical negation either way). -/
theorem negOnTrail_norm {st : State} {l : Literal} :
    st.negOnTrail l.norm = st.negOnTrail l := by
  unfold State.negOnTrail
  rw [norm_negate_norm l]

/-- `enqueueNorm` either leaves the conflict slot alone or sets the
    two-literal opposing pair. -/
theorem enqueueNorm_conflict_cases {st : State} {l0 : Literal}
    {reason : Option Reason} :
    (enqueueNorm st l0 reason).conflict = st.conflict ∨
      (enqueueNorm st l0 reason).conflict
        = some [l0.norm, (l0.norm).negate] := by
  simp only [enqueueNorm]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- When the canonical negation of `l0` is not on the trail, the
    opposing branch cannot fire and `enqueueNorm` preserves the
    conflict slot. -/
theorem enqueueNorm_conflict_of_negNotOnTrail {st : State} {l0 : Literal}
    {reason : Option Reason}
    (h : st.negOnTrail l0.norm = false) :
    (enqueueNorm st l0 reason).conflict = st.conflict := by
  simp only [enqueueNorm]
  split
  · rfl
  · split
    · exfalso
      rename_i hneg
      rw [hneg] at h
      exact absurd h (by simp)
    · rfl

/-- The scan's unit verdict survives the trail-negation filter, so
    its literal's negation is not on the trail. -/
theorem scanClause_unit_negNotOnTrail {st : State} {c : Clause}
    {l : Literal} {r : Reason}
    (h : scanClause st c = some (.inr (l, r))) :
    st.negOnTrail l = false := by
  unfold scanClause at h
  split at h
  · exact absurd h (by simp)
  · match hf : c.filter (fun l => !st.negOnTrail l) with
    | [] => rw [hf] at h; exact absurd h (by simp)
    | [l2] =>
        rw [hf] at h
        injection h with h1
        cases h1
        have hmem : l ∈ c.filter (fun l => !st.negOnTrail l) := by
          rw [hf]
          exact List.mem_cons_self
        have h3 := (List.mem_filter.mp hmem).2
        simpa using h3
    | l1 :: l2 :: rest => rw [hf] at h; exact absurd h (by simp)

/-! ## The nogood-true helpers (the two-case disjunctions)

Each helper proves, from the family constraint's semantics at ONE
assignment, that the emitted nogood carries a true literal. These are
the single place the family arithmetic lives; both TASK A (clause
entailment inside `Reason.Valid`) and TASK B (conflict entitlement)
consume them. -/

/-- leSlot nogood 1: `[x ≤ yj, y > yj]` — if `y > yj` the tail is
    true; if `y ≤ yj` then `x ≤ y ≤ yj` makes the head true. -/
theorem le_nogood_hi_true {a : Assignment} {i j : Nat} {yj : Int}
    (hcons : (DomConstraint.leSlot i j).SatisfiedBy a) :
    ∃ l ∈ [posLe i yj, negLe j yj], l.eval a = some true := by
  obtain ⟨x, y, hx, hy⟩ := leSlot_views a i j hcons
  have hxy : x ≤ y := leSlot_sem hcons hx hy
  by_cases hyyj : y ≤ yj
  · exact ⟨posLe i yj, List.mem_cons_self, by
      rw [eval_posLe_iff]; exact ⟨x, hx, by omega⟩⟩
  · exact ⟨negLe j yj, List.mem_cons_of_mem _ List.mem_cons_self, by
      rw [eval_negLe_iff]; exact ⟨y, hy, by omega⟩⟩

/-- leSlot nogood 2: `[y > xi'−1, x ≤ xi'−1]` — if `x ≤ xi'−1` the
    tail is true; else `y ≥ x > xi'−1` makes the head true. -/
theorem le_nogood_lo_true {a : Assignment} {i j : Nat} {xi' : Int}
    (hcons : (DomConstraint.leSlot i j).SatisfiedBy a) :
    ∃ l ∈ [negLe j (xi' - 1), posLe i (xi' - 1)], l.eval a = some true := by
  obtain ⟨x, y, hx, hy⟩ := leSlot_views a i j hcons
  have hxy : x ≤ y := leSlot_sem hcons hx hy
  by_cases hxle : x ≤ xi' - 1
  · exact ⟨posLe i (xi' - 1), List.mem_cons_of_mem _ List.mem_cons_self, by
      rw [eval_posLe_iff]; exact ⟨x, hx, by omega⟩⟩
  · exact ⟨negLe j (xi' - 1), List.mem_cons_self, by
      rw [eval_negLe_iff]; exact ⟨y, hy, by omega⟩⟩

/-- ltSlot nogood 1: `[x ≤ yj−1, y > yj]` — under `x < y`: if
    `y > yj` the tail is true; else `x < y ≤ yj` gives `x ≤ yj−1`. -/
theorem lt_nogood_hi_true {a : Assignment} {i j : Nat} {yj : Int}
    (hcons : (DomConstraint.ltSlot i j).SatisfiedBy a) :
    ∃ l ∈ [posLe i (yj - 1), negLe j yj], l.eval a = some true := by
  obtain ⟨x, y, hx, hy⟩ := ltSlot_views a i j hcons
  have hxy : x < y := ltSlot_sem hcons hx hy
  by_cases hyyj : y ≤ yj
  · exact ⟨posLe i (yj - 1), List.mem_cons_self, by
      rw [eval_posLe_iff]; exact ⟨x, hx, by omega⟩⟩
  · exact ⟨negLe j yj, List.mem_cons_of_mem _ List.mem_cons_self, by
      rw [eval_negLe_iff]; exact ⟨y, hy, by omega⟩⟩

/-- ltSlot nogood 2: `[y > xi', x ≤ xi'−1]` — if `x ≤ xi'−1` the
    tail is true; else `y > x ≥ xi'` gives `y > xi'`. -/
theorem lt_nogood_lo_true {a : Assignment} {i j : Nat} {xi' : Int}
    (hcons : (DomConstraint.ltSlot i j).SatisfiedBy a) :
    ∃ l ∈ [negLe j xi', posLe i (xi' - 1)], l.eval a = some true := by
  obtain ⟨x, y, hx, hy⟩ := ltSlot_views a i j hcons
  have hxy : x < y := ltSlot_sem hcons hx hy
  by_cases hxle : x ≤ xi' - 1
  · exact ⟨posLe i (xi' - 1), List.mem_cons_of_mem _ List.mem_cons_self, by
      rw [eval_posLe_iff]; exact ⟨x, hx, by omega⟩⟩
  · exact ⟨negLe j xi', List.mem_cons_self, by
      rw [eval_negLe_iff]; exact ⟨y, hy, by omega⟩⟩

/-! ### eqSlot views at the problem's domains

`eqSlot`'s `SatisfiedBy` is the RAW equality, which does not by
itself force integer views; at int-viewed PROBLEM domains (the front
door's `hview` premise) every fitting read is viewed, so both views
exist and are equal. -/

theorem eqSlot_views_prob
    {problem : Problem DomConstraint Unit}
    {a : Assignment} {i j : Nat}
    (hview : IntViewedDoms problem.domains)
    (hprob : DomConstraint.eqSlot i j ∈ problem.constraints)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ x y, slotInt a i = some x ∧ slotInt a j = some y ∧ x = y := by
  have hcons : (DomConstraint.eqSlot i j).SatisfiedBy a := ha.2 _ hprob
  obtain ⟨p, q, hsx, hsy, hpq⟩ := hcons
  have hvmem1 : p ∈ problem.domains.getD i [] := ha.1.2 i p hsx
  have hvmem2 : q ∈ problem.domains.getD j [] := ha.1.2 j q hsy
  have hv1 := view_of_fit hview hvmem1
  have hv2 := view_of_fit hview hvmem2
  match hv : Value.intView p with
  | none => exact absurd hv hv1
  | some x2 =>
      have hqview : Value.intView q = some x2 := by
        rw [← hpq]
        exact hv
      refine ⟨x2, x2, ?_, ?_, rfl⟩
      · show (a[i]?.bind Value.intView) = some x2
        rw [hsx, Option.bind_some, hv]
      · show (a[j]?.bind Value.intView) = some x2
        rw [hsy, Option.bind_some, hqview]

/-- eqSlot nogood 1: `[x > mj−1, y ≤ mj−1]` — under `x = y`: if
    `y ≤ mj−1` the tail is true; else `x = y > mj−1`, the head. -/
theorem eq_nogood_1_true {a : Assignment} {i j : Nat} {mj : Int}
    {x y : Int}
    (hx : slotInt a i = some x) (hy : slotInt a j = some y)
    (hxy : x = y) :
    ∃ l ∈ [negLe i (mj - 1), posLe j (mj - 1)], l.eval a = some true := by
  by_cases hymin : y ≤ mj - 1
  · exact ⟨posLe j (mj - 1), List.mem_cons_of_mem _ List.mem_cons_self, by
      rw [eval_posLe_iff]; exact ⟨y, hy, by omega⟩⟩
  · exact ⟨negLe i (mj - 1), List.mem_cons_self, by
      rw [eval_negLe_iff]; exact ⟨x, hx, by omega⟩⟩

/-- eqSlot nogood 2: `[x ≤ Mj, y > Mj]` — if `y > Mj` the tail is
    true; else `x = y ≤ Mj`, the head. -/
theorem eq_nogood_2_true {a : Assignment} {i j : Nat} {Mj : Int}
    {x y : Int}
    (hx : slotInt a i = some x) (hy : slotInt a j = some y)
    (hxy : x = y) :
    ∃ l ∈ [posLe i Mj, negLe j Mj], l.eval a = some true := by
  by_cases hyMj : y ≤ Mj
  · exact ⟨posLe i Mj, List.mem_cons_self, by
      rw [eval_posLe_iff]; exact ⟨x, hx, by omega⟩⟩
  · exact ⟨negLe j Mj, List.mem_cons_of_mem _ List.mem_cons_self, by
      rw [eval_negLe_iff]; exact ⟨y, hy, by omega⟩⟩

/-- eqSlot nogood 3: `[y > mi−1, x ≤ mi−1]` — symmetric on y. -/
theorem eq_nogood_3_true {a : Assignment} {i j : Nat} {mi : Int}
    {x y : Int}
    (hx : slotInt a i = some x) (hy : slotInt a j = some y)
    (hxy : x = y) :
    ∃ l ∈ [negLe j (mi - 1), posLe i (mi - 1)], l.eval a = some true := by
  by_cases hxmi : x ≤ mi - 1
  · exact ⟨posLe i (mi - 1), List.mem_cons_of_mem _ List.mem_cons_self, by
      rw [eval_posLe_iff]; exact ⟨x, hx, by omega⟩⟩
  · exact ⟨negLe j (mi - 1), List.mem_cons_self, by
      rw [eval_negLe_iff]; exact ⟨y, hy, by omega⟩⟩

/-- eqSlot nogood 4: `[y ≤ Mi, x > Mi]` — symmetric on y. -/
theorem eq_nogood_4_true {a : Assignment} {i j : Nat} {Mi : Int}
    {x y : Int}
    (hx : slotInt a i = some x) (hy : slotInt a j = some y)
    (hxy : x = y) :
    ∃ l ∈ [posLe j Mi, negLe i Mi], l.eval a = some true := by
  by_cases hxMi : x ≤ Mi
  · exact ⟨posLe j Mi, List.mem_cons_self, by
      rw [eval_posLe_iff]; exact ⟨y, hy, by omega⟩⟩
  · exact ⟨negLe i Mi, List.mem_cons_of_mem _ List.mem_cons_self, by
      rw [eval_negLe_iff]; exact ⟨x, hx, by omega⟩⟩

/-! ### plusSlot nogoods (six arms, under `x + y = z`) -/

/-- plusSlot nogood 1: `[x > zk'−yj−1, z ≤ zk'−1, y > yj]` — if
    `y > yj` the third is true; else if `z ≤ zk'−1` the second;
    else `x = z−y ≥ zk'−yj > zk'−yj−1`, the head. -/
theorem plus_nogood_1_true {a : Assignment} {i j k : Nat}
    {zk' yj : Int}
    (hcons : (DomConstraint.plusSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [negLe i (zk' - yj - 1), posLe k (zk' - 1), negLe j yj],
      l.eval a = some true := by
  obtain ⟨x, y, z, hx, hy, hz⟩ := plusSlot_views a i j k hcons
  have hxyz : x + y = z := plusSlot_sem hcons hx hy hz
  by_cases hyj : yj < y
  · exact ⟨negLe j yj, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self), by
      rw [eval_negLe_iff]; exact ⟨y, hy, by omega⟩⟩
  · by_cases hzk : z ≤ zk' - 1
    · exact ⟨posLe k (zk' - 1), List.mem_cons_of_mem _
        List.mem_cons_self, by
        rw [eval_posLe_iff]; exact ⟨z, hz, by omega⟩⟩
    · exact ⟨negLe i (zk' - yj - 1), List.mem_cons_self, by
        rw [eval_negLe_iff]; exact ⟨x, hx, by omega⟩⟩

/-- plusSlot nogood 2: `[x ≤ zk−yj', z > zk, y ≤ yj'−1]`. -/
theorem plus_nogood_2_true {a : Assignment} {i j k : Nat}
    {zk yj' : Int}
    (hcons : (DomConstraint.plusSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [posLe i (zk - yj'), negLe k zk, posLe j (yj' - 1)],
      l.eval a = some true := by
  obtain ⟨x, y, z, hx, hy, hz⟩ := plusSlot_views a i j k hcons
  have hxyz : x + y = z := plusSlot_sem hcons hx hy hz
  by_cases hzk : zk < z
  · exact ⟨negLe k zk, List.mem_cons_of_mem _ List.mem_cons_self, by
      rw [eval_negLe_iff]; exact ⟨z, hz, by omega⟩⟩
  · by_cases hyj : y ≤ yj' - 1
    · exact ⟨posLe j (yj' - 1), List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self), by
        rw [eval_posLe_iff]; exact ⟨y, hy, by omega⟩⟩
    · exact ⟨posLe i (zk - yj'), List.mem_cons_self, by
        rw [eval_posLe_iff]; exact ⟨x, hx, by omega⟩⟩

/-- plusSlot nogood 3: `[y > zk'−xi−1, z ≤ zk'−1, x > xi]`. -/
theorem plus_nogood_3_true {a : Assignment} {i j k : Nat}
    {zk' xi : Int}
    (hcons : (DomConstraint.plusSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [negLe j (zk' - xi - 1), posLe k (zk' - 1), negLe i xi],
      l.eval a = some true := by
  obtain ⟨x, y, z, hx, hy, hz⟩ := plusSlot_views a i j k hcons
  have hxyz : x + y = z := plusSlot_sem hcons hx hy hz
  by_cases hxi : xi < x
  · exact ⟨negLe i xi, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self), by
      rw [eval_negLe_iff]; exact ⟨x, hx, by omega⟩⟩
  · by_cases hzk : z ≤ zk' - 1
    · exact ⟨posLe k (zk' - 1), List.mem_cons_of_mem _
        List.mem_cons_self, by
        rw [eval_posLe_iff]; exact ⟨z, hz, by omega⟩⟩
    · exact ⟨negLe j (zk' - xi - 1), List.mem_cons_self, by
        rw [eval_negLe_iff]; exact ⟨y, hy, by omega⟩⟩

/-- plusSlot nogood 4: `[y ≤ zk−xi', z > zk, x ≤ xi'−1]`. -/
theorem plus_nogood_4_true {a : Assignment} {i j k : Nat}
    {zk xi' : Int}
    (hcons : (DomConstraint.plusSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [posLe j (zk - xi'), negLe k zk, posLe i (xi' - 1)],
      l.eval a = some true := by
  obtain ⟨x, y, z, hx, hy, hz⟩ := plusSlot_views a i j k hcons
  have hxyz : x + y = z := plusSlot_sem hcons hx hy hz
  by_cases hzk : zk < z
  · exact ⟨negLe k zk, List.mem_cons_of_mem _ List.mem_cons_self, by
      rw [eval_negLe_iff]; exact ⟨z, hz, by omega⟩⟩
  · by_cases hxi : x ≤ xi' - 1
    · exact ⟨posLe i (xi' - 1), List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self), by
        rw [eval_posLe_iff]; exact ⟨x, hx, by omega⟩⟩
    · exact ⟨posLe j (zk - xi'), List.mem_cons_self, by
        rw [eval_posLe_iff]; exact ⟨y, hy, by omega⟩⟩

/-- plusSlot nogood 5: `[z > xi'+yj'−1, x ≤ xi'−1, y ≤ yj'−1]`. -/
theorem plus_nogood_5_true {a : Assignment} {i j k : Nat}
    {xi' yj' : Int}
    (hcons : (DomConstraint.plusSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [negLe k (xi' + yj' - 1), posLe i (xi' - 1),
        posLe j (yj' - 1)], l.eval a = some true := by
  obtain ⟨x, y, z, hx, hy, hz⟩ := plusSlot_views a i j k hcons
  have hxyz : x + y = z := plusSlot_sem hcons hx hy hz
  by_cases hxi : x ≤ xi' - 1
  · exact ⟨posLe i (xi' - 1), List.mem_cons_of_mem _
        List.mem_cons_self, by
        rw [eval_posLe_iff]; exact ⟨x, hx, by omega⟩⟩
  · by_cases hyj : y ≤ yj' - 1
    · exact ⟨posLe j (yj' - 1), List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self), by
        rw [eval_posLe_iff]; exact ⟨y, hy, by omega⟩⟩
    · exact ⟨negLe k (xi' + yj' - 1), List.mem_cons_self, by
        rw [eval_negLe_iff]; exact ⟨z, hz, by omega⟩⟩

/-- plusSlot nogood 6: `[z ≤ xi+yj, x > xi, y > yj]`. -/
theorem plus_nogood_6_true {a : Assignment} {i j k : Nat}
    {xi yj : Int}
    (hcons : (DomConstraint.plusSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [posLe k (xi + yj), negLe i xi, negLe j yj],
      l.eval a = some true := by
  obtain ⟨x, y, z, hx, hy, hz⟩ := plusSlot_views a i j k hcons
  have hxyz : x + y = z := plusSlot_sem hcons hx hy hz
  by_cases hxi : xi < x
  · exact ⟨negLe i xi, List.mem_cons_of_mem _ List.mem_cons_self, by
      rw [eval_negLe_iff]; exact ⟨x, hx, by omega⟩⟩
  · by_cases hyj : yj < y
    · exact ⟨negLe j yj, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self), by
        rw [eval_negLe_iff]; exact ⟨y, hy, by omega⟩⟩
    · exact ⟨posLe k (xi + yj), List.mem_cons_self, by
        rw [eval_posLe_iff]; exact ⟨z, hz, by omega⟩⟩

/-! ## TASK A — state-free reason validity -/

/-- The state-free reason-validity lemma for the `leSlot` family: an
    implied emission of `propLe` carries a valid (entailed,
    pivot-member) and normalized reason clause — the clause
    `[x ≤ yj, y > yj]` / `[y > xi'−1, x ≤ xi'−1]` is integer-valid
    under `x ≤ y` alone. -/
theorem propLe_reason_valid
    {problem : Problem DomConstraint Unit}
    {st : State} {i j : Nat} {l : Literal} {r : Reason}
    (hprob : DomConstraint.leSlot i j ∈ problem.constraints)
    (hrun : propLe st i j = .implied l r) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  unfold propLe at hrun
  split at hrun
  next _ _ yj xi' _ _ =>
    rcases firstEvent_mem
        [narrowHi st i yj [posLe i yj, negLe j yj],
         narrowLo st j xi' [negLe j (xi' - 1), posLe i (xi' - 1)]]
        (.implied l r) hrun with hstable | hmem
    · exact absurd hstable (by intro hc; cases hc)
    · rcases List.mem_cons.mp hmem with harm | harm
      · -- emission 1: implied posLe i yj with the nogood
        -- [posLe i yj, negLe j yj]
        obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (Eq.symm harm)
        have hpivmem : l ∈ r.clause := by
          subst hl
          rw [hcl]
          exact List.mem_cons_self
        refine ⟨reason_valid_of_clause_true hpivmem ?_,
          reason_clause_norm_sf hcl (order2_norm rfl rfl)⟩
        intro a ha
        have hcl2 : r.clause = [posLe i yj, negLe j yj] := by
          rw [hcl]
        rw [hcl2]
        exact le_nogood_hi_true (ha.2 _ hprob)
      · -- emission 2: implied negLe j (xi'-1)
        obtain ⟨hl, hcl⟩ := narrowLo_implied_inv
          (Eq.symm (List.mem_singleton.mp harm))
        have hpivmem : l ∈ r.clause := by
          subst hl
          rw [hcl]
          exact List.mem_cons_self
        refine ⟨reason_valid_of_clause_true hpivmem ?_,
          reason_clause_norm_sf hcl (order2_norm rfl rfl)⟩
        intro a ha
        have hcl2 : r.clause =
            [negLe j (xi' - 1), posLe i (xi' - 1)] := by
          rw [hcl]
        rw [hcl2]
        exact le_nogood_lo_true (ha.2 _ hprob)
  next => exact absurd hrun (by intro hc; simp at hc)

/-- The state-free reason-validity lemma for the `ltSlot` family
    (`x < y`): both nogoods are integer-valid under the constraint
    alone. -/
theorem propLt_reason_valid
    {problem : Problem DomConstraint Unit}
    {st : State} {i j : Nat} {l : Literal} {r : Reason}
    (hprob : DomConstraint.ltSlot i j ∈ problem.constraints)
    (hrun : propLt st i j = .implied l r) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  unfold propLt at hrun
  split at hrun
  next _ _ yj xi' _ _ =>
    rcases firstEvent_mem
        [narrowHi st i (yj - 1) [posLe i (yj - 1), negLe j yj],
         narrowLo st j (xi' + 1) [negLe j xi', posLe i (xi' - 1)]]
        (.implied l r) hrun with hstable | hmem
    · exact absurd hstable (by intro hc; cases hc)
    · rcases List.mem_cons.mp hmem with harm | harm
      · obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (Eq.symm harm)
        have hpivmem : l ∈ r.clause := by
          subst hl; rw [hcl]; exact List.mem_cons_self
        refine ⟨reason_valid_of_clause_true hpivmem ?_,
          reason_clause_norm_sf hcl (order2_norm rfl rfl)⟩
        intro a ha
        have hcl2 : r.clause = [posLe i (yj - 1), negLe j yj] := by
          rw [hcl]
        rw [hcl2]
        exact lt_nogood_hi_true (ha.2 _ hprob)
      · obtain ⟨hl, hcl⟩ := narrowLo_implied_inv
          (Eq.symm (List.mem_singleton.mp harm))
        have hpivmem : l ∈ r.clause := by
          subst hl
          rw [hcl]
          have heq : xi' + 1 - 1 = xi' := by omega
          rw [heq]
          exact List.mem_cons_self
        refine ⟨reason_valid_of_clause_true hpivmem ?_,
          reason_clause_norm_sf hcl (order2_norm rfl rfl)⟩
        intro a ha
        have hcl2 : r.clause = [negLe j xi', posLe i (xi' - 1)] := by
          rw [hcl]
        rw [hcl2]
        exact lt_nogood_lo_true (ha.2 _ hprob)
  next => exact absurd hrun (by intro hc; simp at hc)

/-- The state-free reason-validity lemma for the `eqSlot` family
    (`x = y`): all four nogoods are integer-valid under the
    constraint alone (with the problem-level int-viewed-domains
    premise supplying the views — the one honest addition this family
    needs, already carried by the front doors). -/
theorem propEq_reason_valid
    {problem : Problem DomConstraint Unit}
    (hview : IntViewedDoms problem.domains)
    {st : State} {i j : Nat} {l : Literal} {r : Reason}
    (hprob : DomConstraint.eqSlot i j ∈ problem.constraints)
    (hrun : propEq st i j = .implied l r) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  unfold propEq at hrun
  split at hrun
  next _ _ _ _ mi Mi mj Mj _ _ _ _ =>
    rcases firstEvent_mem
        [narrowLo st i mj [negLe i (mj - 1), posLe j (mj - 1)],
         narrowHi st i Mj [posLe i Mj, negLe j Mj],
         narrowLo st j mi [negLe j (mi - 1), posLe i (mi - 1)],
         narrowHi st j Mi [posLe j Mi, negLe i Mi]]
        (.implied l r) hrun with hstable | hmem
    · exact absurd hstable (by intro hc; cases hc)
    · rcases List.mem_cons.mp hmem with harm1 | hrest1
      · obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (Eq.symm harm1)
        have hpivmem : l ∈ r.clause := by
          subst hl; rw [hcl]; exact List.mem_cons_self
        refine ⟨reason_valid_of_clause_true hpivmem ?_,
          reason_clause_norm_sf hcl (order2_norm rfl rfl)⟩
        intro a ha
        obtain ⟨x, y, hx, hy, hxy⟩ := eqSlot_views_prob hview hprob ha
        have hcl2 : r.clause =
            [negLe i (mj - 1), posLe j (mj - 1)] := by
          rw [hcl]
        rw [hcl2]
        exact eq_nogood_1_true hx hy hxy
      · rcases List.mem_cons.mp hrest1 with harm2 | hrest2
        · obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (Eq.symm harm2)
          have hpivmem : l ∈ r.clause := by
            subst hl; rw [hcl]; exact List.mem_cons_self
          refine ⟨reason_valid_of_clause_true hpivmem ?_,
            reason_clause_norm_sf hcl (order2_norm rfl rfl)⟩
          intro a ha
          obtain ⟨x, y, hx, hy, hxy⟩ :=
            eqSlot_views_prob hview hprob ha
          have hcl2 : r.clause = [posLe i Mj, negLe j Mj] := by
            rw [hcl]
          rw [hcl2]
          exact eq_nogood_2_true hx hy hxy
        · rcases List.mem_cons.mp hrest2 with harm3 | hrest3
          · obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (Eq.symm harm3)
            have hpivmem : l ∈ r.clause := by
              subst hl; rw [hcl]; exact List.mem_cons_self
            refine ⟨reason_valid_of_clause_true hpivmem ?_,
              reason_clause_norm_sf hcl (order2_norm rfl rfl)⟩
            intro a ha
            obtain ⟨x, y, hx, hy, hxy⟩ :=
              eqSlot_views_prob hview hprob ha
            have hcl2 : r.clause =
                [negLe j (mi - 1), posLe i (mi - 1)] := by
              rw [hcl]
            rw [hcl2]
            exact eq_nogood_3_true hx hy hxy
          · obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (Eq.symm
              (List.mem_singleton.mp hrest3))
            have hpivmem : l ∈ r.clause := by
              subst hl; rw [hcl]; exact List.mem_cons_self
            refine ⟨reason_valid_of_clause_true hpivmem ?_,
              reason_clause_norm_sf hcl (order2_norm rfl rfl)⟩
            intro a ha
            obtain ⟨x, y, hx, hy, hxy⟩ :=
              eqSlot_views_prob hview hprob ha
            have hcl2 : r.clause = [posLe j Mi, negLe i Mi] := by
              rw [hcl]
            rw [hcl2]
            exact eq_nogood_4_true hx hy hxy
  next => exact absurd hrun (by intro hc; simp at hc)

/-- The neSlot nogood, stated at views: under the raw `x ≠ y`, at
    any assignment whose two reads carry integer views, one of the
    five disjuncts is true. -/
theorem ne_nogood_true {a : Assignment} {i j : Nat} {c : Int}
    (hcons : (DomConstraint.neSlot i j).SatisfiedBy a)
    (hxi : ∃ x, slotInt a i = some x)
    (hyj : ∃ y, slotInt a j = some y) :
    ∃ l ∈ [posNe j c, posLe i (c - 1), negLe i c,
        posBool i (decide (c = 1)), posBool j (decide (c = 1))],
      l.eval a = some true := by
  obtain ⟨x, hx⟩ := hxi
  obtain ⟨y, hy⟩ := hyj
  obtain ⟨p, q, hrawi, hrawj, hpq⟩ := hcons
  -- the views come from the raw reads
  have hviewi : Value.intView p = some x := by
    have hsi : slotInt a i = some x := hx
    rw [slotInt, hrawi] at hsi
    exact hsi
  have hviewj : Value.intView q = some y := by
    have hsj : slotInt a j = some y := hy
    rw [slotInt, hrawj] at hsj
    exact hsj
  -- membership helpers for the five-element disjunction
  have mem1 : posNe j c ∈
      [posNe j c, posLe i (c - 1), negLe i c,
        posBool i (decide (c = 1)), posBool j (decide (c = 1))] :=
    List.mem_cons_self
  have mem3 : negLe i c ∈
      [posNe j c, posLe i (c - 1), negLe i c,
        posBool i (decide (c = 1)), posBool j (decide (c = 1))] :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have mem4 : posBool i (decide (c = 1)) ∈
      [posNe j c, posLe i (c - 1), negLe i c,
        posBool i (decide (c = 1)), posBool j (decide (c = 1))] :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self))
  have mem5 : posBool j (decide (c = 1)) ∈
      [posNe j c, posLe i (c - 1), negLe i c,
        posBool i (decide (c = 1)), posBool j (decide (c = 1))] :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self)))
  by_cases hxeq : x = c
  · -- x's view is c: the two bound causes are false; close by the
    -- raw shapes of the reads
    cases hp : p with
    | int p2 =>
        have hpc : p2 = x := by
          rw [hp] at hviewi
          exact Option.some.inj hviewi
        cases hq : q with
        | int q2 =>
            have hqx : q2 = y := by
              rw [hq] at hviewj
              exact Option.some.inj hviewj
            by_cases hyc : y = c
            · -- q views to c too: the raw reads are both the int c —
              -- raw-EQUAL, contradicting the constraint
              exfalso
              apply hpq
              rw [hp, hq, hpc, hqx]
              rw [show x = y from by omega]
            · -- y ≠ c: the head posNe j c is true
              exact ⟨posNe j c, mem1, by
                rw [eval_posNe_iff]; exact ⟨y, hy, hyc⟩⟩
        | bool b2 =>
            -- q is a bool: if it views to c the y = B disjunct is
            -- true, else the head is true
            by_cases hbc : (if b2 then 1 else 0) = c
            · -- b2 views to c, so c ∈ {0,1} and b2 = decide (c = 1)
              have hbdec : b2 = decide (c = 1) := by
                cases b2 with
                | true =>
                    have hc1 : c = 1 := by
                      have h1 : (1 : Int) = c := by simpa using hbc
                      omega
                    rw [decide_eq_true hc1]
                | false =>
                    have hc0 : c = 0 := by
                      have h0 : (0 : Int) = c := by simpa using hbc
                      omega
                    rw [decide_eq_false (by omega : c ≠ 1)]
              exact ⟨posBool j (decide (c = 1)), mem5, by
                rw [eval_posBool_iff, ← hbdec, hrawj, hq]⟩
            · exact ⟨posNe j c, mem1, by
                rw [eval_posNe_iff]
                refine ⟨(if b2 then 1 else 0), ?_, hbc⟩
                show (a[j]?.bind Value.intView) =
                  some (if b2 then 1 else 0)
                rw [hrawj, hq]
                rfl⟩
        | setOfInt s =>
            rw [hq] at hviewj
            exact absurd hviewj (by simp [Value.intView])
        | array s =>
            rw [hq] at hviewj
            exact absurd hviewj (by simp [Value.intView])
    | bool bi =>
        -- p is the bool viewing to c (x = c): the x = B disjunct is
        -- true
        have hxc : (if bi then 1 else 0) = x := by
          rw [hp] at hviewi
          exact Option.some.inj hviewi
        have hxc' : (if bi then 1 else 0) = c := by omega
        have hbdec : bi = decide (c = 1) := by
          cases bi with
          | true =>
              have hc1 : c = 1 := by
                have h1 : (1 : Int) = c := by simpa using hxc'
                omega
              rw [decide_eq_true hc1]
          | false =>
              have hc0 : c = 0 := by
                have h0 : (0 : Int) = c := by simpa using hxc'
                omega
              rw [decide_eq_false (by omega : c ≠ 1)]
        exact ⟨posBool i (decide (c = 1)), mem4, by
          rw [eval_posBool_iff, ← hbdec, hrawi, hp]⟩
    | setOfInt s =>
        rw [hp] at hviewi
        exact absurd hviewi (by simp [Value.intView])
    | array s =>
        rw [hp] at hviewi
        exact absurd hviewi (by simp [Value.intView])
  · -- x's view differs from c: one of the two bound causes is true
    by_cases hxlt : x < c
    · exact ⟨posLe i (c - 1), List.mem_cons_of_mem _
        List.mem_cons_self, by
        rw [eval_posLe_iff]; exact ⟨x, hx, by omega⟩⟩
    · exact ⟨negLe i c, mem3, by
        rw [eval_negLe_iff]; exact ⟨x, hx, by omega⟩⟩

/-- The state-free reason-validity lemma for the `neSlot` family:
    the emitted nogood is raw-valid under the constraint at every
    internal solution (the constraint forces both reads to exist,
    and the problem's int-viewed domains force both reads to carry
    views). -/
theorem propNe_reason_valid
    {problem : Problem DomConstraint Unit}
    (hview : IntViewedDoms problem.domains)
    {st : State} {i j : Nat} {l : Literal} {r : Reason}
    (hprob : DomConstraint.neSlot i j ∈ problem.constraints)
    (hrun : propNe st i j = .implied l r) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  -- the views at an internal solution: the constraint gives both
  -- reads; the fit at the int-viewed problem domains gives the views
  have hviews : ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
      (∃ x, slotInt a i = some x) ∧ (∃ y, slotInt a j = some y) := by
    intro a ha
    have hcons : (DomConstraint.neSlot i j).SatisfiedBy a := ha.2 _ hprob
    obtain ⟨p, q, hpi, hqj, _⟩ := hcons
    have hmemi : p ∈ problem.domains.getD i [] := ha.1.2 i p hpi
    have hmemj : q ∈ problem.domains.getD j [] := ha.1.2 j q hqj
    have hvi : Value.intView p ≠ none :=
      intViewedDoms_getD hview i p hmemi
    have hvj : Value.intView q ≠ none :=
      intViewedDoms_getD hview j q hmemj
    refine ⟨?_, ?_⟩
    · show ∃ x, (a[i]?.bind Value.intView) = some x
      rw [hpi]
      cases hv : Value.intView p with
      | none => exact absurd hv hvi
      | some w => exact ⟨w, by rw [Option.bind_some]; exact hv⟩
    · show ∃ y, (a[j]?.bind Value.intView) = some y
      rw [hqj]
      cases hv : Value.intView q with
      | none => exact absurd hv hvj
      | some w => exact ⟨w, by rw [Option.bind_some]; exact hv⟩
  rcases propNe_implied_inv hrun with
    ⟨x, c, hsi, hlit, hcl, hc, hmem, hgate⟩ |
    ⟨y, c, hsj, hlit, hcl, hc, hmem, hgate⟩
  · subst hlit
    rw [hcl]
    refine ⟨⟨?_, by simp⟩, ?_⟩
    · intro a ha
      obtain ⟨hxi, hyj⟩ := hviews a ha
      exact ne_nogood_true (ha.2 _ hprob) hxi hyj
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hrest
      · rfl
      · rcases List.mem_cons.mp hrest with rfl | hrest
        · rfl
        · rcases List.mem_cons.mp hrest with rfl | hrest
          · rfl
          · rcases List.mem_cons.mp hrest with rfl | hrest
            · rfl
            · cases List.mem_singleton.mp hrest; rfl
  · subst hlit
    rw [hcl]
    refine ⟨⟨?_, by simp⟩, ?_⟩
    · intro a ha
      obtain ⟨hxi, hyj⟩ := hviews a ha
      -- the swapped constraint's raw-disequality symmetry
      have hcons' : (DomConstraint.neSlot j i).SatisfiedBy a := by
        obtain ⟨p, q, hp, hq, hpq⟩ := ha.2 _ hprob
        exact ⟨q, p, hq, hp, hpq.symm⟩
      exact ne_nogood_true (i := j) (j := i) hcons' hyj hxi
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hrest
      · rfl
      · rcases List.mem_cons.mp hrest with rfl | hrest
        · rfl
        · rcases List.mem_cons.mp hrest with rfl | hrest
          · rfl
          · rcases List.mem_cons.mp hrest with rfl | hrest
            · rfl
            · cases List.mem_singleton.mp hrest; rfl

/-- The state-free reason-validity lemma for the `plusSlot` family
    (`x + y = z`): all six nogoods are integer-valid under the
    constraint alone. -/
theorem propPlus_reason_valid
    {problem : Problem DomConstraint Unit}
    {st : State} {i j k : Nat} {l : Literal} {r : Reason}
    (hprob : DomConstraint.plusSlot i j k ∈ problem.constraints)
    (hrun : propPlus st i j k = .implied l r) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  unfold propPlus at hrun
  split at hrun
  next _ _ _ _ _ _ xi' xi yj' yj zk' zk _ _ _ _ _ _ =>
    rcases firstEvent_mem
        [narrowLo st i (zk' - yj)
            [negLe i (zk' - yj - 1), posLe k (zk' - 1), negLe j yj],
         narrowHi st i (zk - yj')
            [posLe i (zk - yj'), negLe k zk, posLe j (yj' - 1)],
         narrowLo st j (zk' - xi)
            [negLe j (zk' - xi - 1), posLe k (zk' - 1), negLe i xi],
         narrowHi st j (zk - xi')
            [posLe j (zk - xi'), negLe k zk, posLe i (xi' - 1)],
         narrowLo st k (xi' + yj')
            [negLe k (xi' + yj' - 1), posLe i (xi' - 1),
              posLe j (yj' - 1)],
         narrowHi st k (xi + yj)
            [posLe k (xi + yj), negLe i xi, negLe j yj]]
        (.implied l r) hrun with hstable | hmem
    · exact absurd hstable (by intro hc; cases hc)
    · rcases List.mem_cons.mp hmem with h1' | hrest1
      · obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (Eq.symm h1')
        have hpivmem : l ∈ r.clause := by
          subst hl; rw [hcl]; exact List.mem_cons_self
        refine ⟨reason_valid_of_clause_true hpivmem ?_,
          reason_clause_norm_sf hcl (order3_norm rfl rfl rfl)⟩
        intro a ha
        have hcl2 : r.clause =
            [negLe i (zk' - yj - 1), posLe k (zk' - 1), negLe j yj] := by
          rw [hcl]
        rw [hcl2]
        exact plus_nogood_1_true (ha.2 _ hprob)
      · rcases List.mem_cons.mp hrest1 with h2' | hrest2
        · obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (Eq.symm h2')
          have hpivmem : l ∈ r.clause := by
            subst hl; rw [hcl]; exact List.mem_cons_self
          refine ⟨reason_valid_of_clause_true hpivmem ?_,
            reason_clause_norm_sf hcl (order3_norm rfl rfl rfl)⟩
          intro a ha
          have hcl2 : r.clause =
              [posLe i (zk - yj'), negLe k zk, posLe j (yj' - 1)] := by
            rw [hcl]
          rw [hcl2]
          exact plus_nogood_2_true (ha.2 _ hprob)
        · rcases List.mem_cons.mp hrest2 with h3' | hrest3
          · obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (Eq.symm h3')
            have hpivmem : l ∈ r.clause := by
              subst hl; rw [hcl]; exact List.mem_cons_self
            refine ⟨reason_valid_of_clause_true hpivmem ?_,
              reason_clause_norm_sf hcl (order3_norm rfl rfl rfl)⟩
            intro a ha
            have hcl2 : r.clause =
                [negLe j (zk' - xi - 1), posLe k (zk' - 1),
                  negLe i xi] := by
              rw [hcl]
            rw [hcl2]
            exact plus_nogood_3_true (ha.2 _ hprob)
          · rcases List.mem_cons.mp hrest3 with h4' | hrest4
            · obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (Eq.symm h4')
              have hpivmem : l ∈ r.clause := by
                subst hl; rw [hcl]; exact List.mem_cons_self
              refine ⟨reason_valid_of_clause_true hpivmem ?_,
                reason_clause_norm_sf hcl (order3_norm rfl rfl rfl)⟩
              intro a ha
              have hcl2 : r.clause =
                  [posLe j (zk - xi'), negLe k zk,
                    posLe i (xi' - 1)] := by
                rw [hcl]
              rw [hcl2]
              exact plus_nogood_4_true (ha.2 _ hprob)
            · rcases List.mem_cons.mp hrest4 with h5' | hrest5
              · obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (Eq.symm h5')
                have hpivmem : l ∈ r.clause := by
                  subst hl; rw [hcl]; exact List.mem_cons_self
                refine ⟨reason_valid_of_clause_true hpivmem ?_,
                  reason_clause_norm_sf hcl (order3_norm rfl rfl rfl)⟩
                intro a ha
                have hcl2 : r.clause =
                    [negLe k (xi' + yj' - 1), posLe i (xi' - 1),
                      posLe j (yj' - 1)] := by
                  rw [hcl]
                rw [hcl2]
                exact plus_nogood_5_true (ha.2 _ hprob)
              · obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (Eq.symm
                  (List.mem_singleton.mp hrest5))
                have hpivmem : l ∈ r.clause := by
                  subst hl; rw [hcl]; exact List.mem_cons_self
                refine ⟨reason_valid_of_clause_true hpivmem ?_,
                  reason_clause_norm_sf hcl (order3_norm rfl rfl rfl)⟩
                intro a ha
                have hcl2 : r.clause =
                    [posLe k (xi + yj), negLe i xi, negLe j yj] := by
                  rw [hcl]
                rw [hcl2]
                exact plus_nogood_6_true (ha.2 _ hprob)
  next => exact absurd hrun (by intro hc; simp at hc)

/-! ## TASK A, the five const families

Their reason-validity lemmas are already state-premise-free in
solver/LCG/Proofs/ConstFamilies.lean (unit nogoods pinned by the
constraint alone); these are the exact task-shape restatements at the
concrete `DomConstraint.SatisfiedBy` semantics. -/

theorem propLeConstHi_reason_valid
    {problem : Problem DomConstraint Unit}
    {st : State} {i : Nat} {c : Int} {l : Literal} {r : Reason}
    (hprob : DomConstraint.leConstHi i c ∈ problem.constraints)
    (hrun : propLeConstHi st i c = .implied l r) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l ∧
      (∀ q ∈ r.clause, q = q.norm) :=
  propLeConstHi_reason_safe_sat hprob hrun

theorem propLeConstLo_reason_valid
    {problem : Problem DomConstraint Unit}
    {st : State} {i : Nat} {c : Int} {l : Literal} {r : Reason}
    (hprob : DomConstraint.leConstLo i c ∈ problem.constraints)
    (hrun : propLeConstLo st i c = .implied l r) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l ∧
      (∀ q ∈ r.clause, q = q.norm) :=
  propLeConstLo_reason_safe_sat hprob hrun

theorem propLtConstHi_reason_valid
    {problem : Problem DomConstraint Unit}
    {st : State} {i : Nat} {c : Int} {l : Literal} {r : Reason}
    (hprob : DomConstraint.ltConstHi i c ∈ problem.constraints)
    (hrun : propLtConstHi st i c = .implied l r) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l ∧
      (∀ q ∈ r.clause, q = q.norm) :=
  propLtConstHi_reason_safe_sat hprob hrun

theorem propLtConstLo_reason_valid
    {problem : Problem DomConstraint Unit}
    {st : State} {i : Nat} {c : Int} {l : Literal} {r : Reason}
    (hprob : DomConstraint.ltConstLo i c ∈ problem.constraints)
    (hrun : propLtConstLo st i c = .implied l r) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l ∧
      (∀ q ∈ r.clause, q = q.norm) :=
  propLtConstLo_reason_safe_sat hprob hrun

theorem propConstEq_reason_valid
    {problem : Problem DomConstraint Unit}
    {st : State} {i : Nat} {v : Value} {l : Literal} {r : Reason}
    (hprob : DomConstraint.constEq i v ∈ problem.constraints)
    (hrun : propConstEq st i v = .implied l r) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l ∧
      (∀ q ∈ r.clause, q = q.norm) :=
  propConstEq_reason_safe_sat hprob hrun

/-! ## TASK B — state-free conflict entitlement

For each family that can report `.conflict` with a NONEMPTY clause:
the conflict clause is the SAME nogood, so the same two-case
disjunction gives a true literal at every internal solution. neSlot
is EXCLUDED: `propNe`'s conflict clause is `[]`
(`propNe_conflict_clause_empty` below) — the master theorem's
`cc ≠ []` gate is exactly for it. -/

/-- The state-free conflict entitlement for the `leSlot` family: the
    conflict clause is the same nogood, so it carries a true literal
    at every internal solution. -/
theorem propLe_conflict_entitled
    {problem : Problem DomConstraint Unit} {st : State} {i j : Nat}
    {c : Clause}
    (hprob : DomConstraint.leSlot i j ∈ problem.constraints)
    (hrun : propLe st i j = .conflict c)
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ c, l.eval a = some true := by
  unfold propLe at hrun
  split at hrun
  next _ _ yj xi' _ _ =>
    rcases firstEvent_mem
        [narrowHi st i yj [posLe i yj, negLe j yj],
         narrowLo st j xi' [negLe j (xi' - 1), posLe i (xi' - 1)]]
        (.conflict c) hrun with hstable | hmem
    · exact absurd hstable (by intro hc; cases hc)
    · rcases List.mem_cons.mp hmem with harm | harm
      · obtain ⟨_, _, _, _, _, hcc⟩ :=
          narrowHi_conflict_inv (Eq.symm harm)
        rw [hcc]
        exact le_nogood_hi_true (ha.2 _ hprob)
      · obtain ⟨_, _, _, _, _, hcc⟩ :=
          narrowLo_conflict_inv (Eq.symm (List.mem_singleton.mp harm))
        rw [hcc]
        exact le_nogood_lo_true (ha.2 _ hprob)
  next => exact absurd hrun (by intro hc; simp at hc)

/-- The state-free conflict entitlement for the `ltSlot` family. -/
theorem propLt_conflict_entitled
    {problem : Problem DomConstraint Unit} {st : State} {i j : Nat}
    {c : Clause}
    (hprob : DomConstraint.ltSlot i j ∈ problem.constraints)
    (hrun : propLt st i j = .conflict c)
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ c, l.eval a = some true := by
  unfold propLt at hrun
  split at hrun
  next _ _ yj xi' _ _ =>
    rcases firstEvent_mem
        [narrowHi st i (yj - 1) [posLe i (yj - 1), negLe j yj],
         narrowLo st j (xi' + 1) [negLe j xi', posLe i (xi' - 1)]]
        (.conflict c) hrun with hstable | hmem
    · exact absurd hstable (by intro hc; cases hc)
    · rcases List.mem_cons.mp hmem with harm | harm
      · obtain ⟨_, _, _, _, _, hcc⟩ :=
          narrowHi_conflict_inv (Eq.symm harm)
        rw [hcc]
        exact lt_nogood_hi_true (ha.2 _ hprob)
      · obtain ⟨_, _, _, _, _, hcc⟩ :=
          narrowLo_conflict_inv (Eq.symm (List.mem_singleton.mp harm))
        rw [hcc]
        exact lt_nogood_lo_true (ha.2 _ hprob)
  next => exact absurd hrun (by intro hc; simp at hc)

/-- The state-free conflict entitlement for the `eqSlot` family
    (with the problem-level int-viewed-domains premise the family's
    views need). -/
theorem propEq_conflict_entitled
    {problem : Problem DomConstraint Unit}
    (hview : IntViewedDoms problem.domains)
    {st : State} {i j : Nat} {c : Clause}
    (hprob : DomConstraint.eqSlot i j ∈ problem.constraints)
    (hrun : propEq st i j = .conflict c)
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ c, l.eval a = some true := by
  obtain ⟨x, y, hx, hy, hxy⟩ := eqSlot_views_prob hview hprob ha
  unfold propEq at hrun
  split at hrun
  next _ _ _ _ mi Mi mj Mj _ _ _ _ =>
    rcases firstEvent_mem
        [narrowLo st i mj [negLe i (mj - 1), posLe j (mj - 1)],
         narrowHi st i Mj [posLe i Mj, negLe j Mj],
         narrowLo st j mi [negLe j (mi - 1), posLe i (mi - 1)],
         narrowHi st j Mi [posLe j Mi, negLe i Mi]]
        (.conflict c) hrun with hstable | hmem
    · exact absurd hstable (by intro hc; cases hc)
    · rcases List.mem_cons.mp hmem with harm1 | hrest1
      · obtain ⟨_, _, _, _, _, hcc⟩ :=
          narrowLo_conflict_inv (Eq.symm harm1)
        rw [hcc]
        exact eq_nogood_1_true hx hy hxy
      · rcases List.mem_cons.mp hrest1 with harm2 | hrest2
        · obtain ⟨_, _, _, _, _, hcc⟩ :=
            narrowHi_conflict_inv (Eq.symm harm2)
          rw [hcc]
          exact eq_nogood_2_true hx hy hxy
        · rcases List.mem_cons.mp hrest2 with harm3 | hrest3
          · obtain ⟨_, _, _, _, _, hcc⟩ :=
              narrowLo_conflict_inv (Eq.symm harm3)
            rw [hcc]
            exact eq_nogood_3_true hx hy hxy
          · obtain ⟨_, _, _, _, _, hcc⟩ :=
              narrowHi_conflict_inv (Eq.symm
                (List.mem_singleton.mp hrest3))
            rw [hcc]
            exact eq_nogood_4_true hx hy hxy
  next => exact absurd hrun (by intro hc; simp at hc)

/-- The state-free conflict entitlement for the `plusSlot` family. -/
theorem propPlus_conflict_entitled
    {problem : Problem DomConstraint Unit} {st : State} {i j k : Nat}
    {c : Clause}
    (hprob : DomConstraint.plusSlot i j k ∈ problem.constraints)
    (hrun : propPlus st i j k = .conflict c)
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ c, l.eval a = some true := by
  unfold propPlus at hrun
  split at hrun
  next _ _ _ _ _ _ xi' xi yj' yj zk' zk _ _ _ _ _ _ =>
    rcases firstEvent_mem
        [narrowLo st i (zk' - yj)
            [negLe i (zk' - yj - 1), posLe k (zk' - 1), negLe j yj],
         narrowHi st i (zk - yj')
            [posLe i (zk - yj'), negLe k zk, posLe j (yj' - 1)],
         narrowLo st j (zk' - xi)
            [negLe j (zk' - xi - 1), posLe k (zk' - 1), negLe i xi],
         narrowHi st j (zk - xi')
            [posLe j (zk - xi'), negLe k zk, posLe i (xi' - 1)],
         narrowLo st k (xi' + yj')
            [negLe k (xi' + yj' - 1), posLe i (xi' - 1),
              posLe j (yj' - 1)],
         narrowHi st k (xi + yj)
            [posLe k (xi + yj), negLe i xi, negLe j yj]]
        (.conflict c) hrun with hstable | hmem
    · exact absurd hstable (by intro hc; cases hc)
    · rcases List.mem_cons.mp hmem with h1' | hrest1
      · obtain ⟨_, _, _, _, _, hcc⟩ :=
          narrowLo_conflict_inv (Eq.symm h1')
        rw [hcc]
        exact plus_nogood_1_true (ha.2 _ hprob)
      · rcases List.mem_cons.mp hrest1 with h2' | hrest2
        · obtain ⟨_, _, _, _, _, hcc⟩ :=
            narrowHi_conflict_inv (Eq.symm h2')
          rw [hcc]
          exact plus_nogood_2_true (ha.2 _ hprob)
        · rcases List.mem_cons.mp hrest2 with h3' | hrest3
          · obtain ⟨_, _, _, _, _, hcc⟩ :=
              narrowLo_conflict_inv (Eq.symm h3')
            rw [hcc]
            exact plus_nogood_3_true (ha.2 _ hprob)
          · rcases List.mem_cons.mp hrest3 with h4' | hrest4
            · obtain ⟨_, _, _, _, _, hcc⟩ :=
                narrowHi_conflict_inv (Eq.symm h4')
              rw [hcc]
              exact plus_nogood_4_true (ha.2 _ hprob)
            · rcases List.mem_cons.mp hrest4 with h5' | hrest5
              · obtain ⟨_, _, _, _, _, hcc⟩ :=
                  narrowLo_conflict_inv (Eq.symm h5')
                rw [hcc]
                exact plus_nogood_5_true (ha.2 _ hprob)
              · obtain ⟨_, _, _, _, _, hcc⟩ :=
                  narrowHi_conflict_inv (Eq.symm
                    (List.mem_singleton.mp hrest5))
                rw [hcc]
                exact plus_nogood_6_true (ha.2 _ hprob)
  next => exact absurd hrun (by intro hc; simp at hc)

/-! ### neSlot's exclusion

`propNe`'s only conflict report is the EMPTY clause: its entitlement
is exactly "no internal solution exists", which is a genuinely
state-dependent fact (the raw both-singleton comparison reads the
STATE's narrowed domains). This is precisely why the master theorem's
`hconfent` carries `cc ≠ []`. -/

/-- `propNe`'s conflict report is the empty clause (so its
    nonempty-clause entitlement is vacuous — and its unconstrained
    form is FALSE, which is why it is excluded from Task B). -/
theorem propNe_conflict_clause_empty {st : State} {i j : Nat}
    {c : Clause} (hrun : propNe st i j = .conflict c) : c = [] := by
  obtain ⟨x, y, hx, hy, hcond, hc2⟩ := propNe_conflict_inv hrun
  exact hc2

/-! ### The five const families' conflict entitlement (reuse)

ConstFamilies.lean's `_entitled` lemmas are already
state-premise-free. -/

theorem propLeConstHi_conflict_entitled
    {problem : Problem DomConstraint Unit} {st : State} {i : Nat}
    {c : Int} {cc : Clause}
    (hprob : DomConstraint.leConstHi i c ∈ problem.constraints)
    (hrun : propLeConstHi st i c = .conflict cc)
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ cc, l.eval a = some true :=
  propLeConstHi_entitled hprob hrun a ha

theorem propLeConstLo_conflict_entitled
    {problem : Problem DomConstraint Unit} {st : State} {i : Nat}
    {c : Int} {cc : Clause}
    (hprob : DomConstraint.leConstLo i c ∈ problem.constraints)
    (hrun : propLeConstLo st i c = .conflict cc)
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ cc, l.eval a = some true :=
  propLeConstLo_entitled hprob hrun a ha

theorem propLtConstHi_conflict_entitled
    {problem : Problem DomConstraint Unit} {st : State} {i : Nat}
    {c : Int} {cc : Clause}
    (hprob : DomConstraint.ltConstHi i c ∈ problem.constraints)
    (hrun : propLtConstHi st i c = .conflict cc)
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ cc, l.eval a = some true :=
  propLtConstHi_entitled hprob hrun a ha

theorem propLtConstLo_conflict_entitled
    {problem : Problem DomConstraint Unit} {st : State} {i : Nat}
    {c : Int} {cc : Clause}
    (hprob : DomConstraint.ltConstLo i c ∈ problem.constraints)
    (hrun : propLtConstLo st i c = .conflict cc)
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ cc, l.eval a = some true :=
  propLtConstLo_entitled hprob hrun a ha

theorem propConstEq_conflict_entitled
    {problem : Problem DomConstraint Unit} {st : State} {i : Nat}
    {v : Value} {cc : Clause}
    (hprob : DomConstraint.constEq i v ∈ problem.constraints)
    (hrun : propConstEq st i v = .conflict cc)
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ cc, l.eval a = some true :=
  propConstEq_entitled hprob hrun a ha

/-! ## Decidedness helpers (for the opposing-pair arm of Task C.2)

An order literal on a slot with an integer view is DECIDED at the
assignment (evaluates to `some b`), whatever the bound: this is what
closes the sweep's opposing-fact pair `[l.norm, ¬l.norm]` arm at every
internal solution with no state premise. -/

theorem posLe_decided {a : Assignment} {s : Nat} {k : Int}
    (hx : ∃ x, slotInt a s = some x) :
    ∃ b, (posLe s k).eval a = some b := by
  obtain ⟨x, hx⟩ := hx
  rw [eval_posLe, hx]
  exact ⟨_, rfl⟩

theorem negLe_decided {a : Assignment} {s : Nat} {k : Int}
    (hx : ∃ x, slotInt a s = some x) :
    ∃ b, (negLe s k).eval a = some b := by
  obtain ⟨x, hx⟩ := hx
  rw [eval_negLe, hx]
  exact ⟨_, rfl⟩

theorem posNe_decided {a : Assignment} {s : Nat} {k : Int}
    (hx : ∃ x, slotInt a s = some x) :
    ∃ b, (posNe s k).eval a = some b := by
  obtain ⟨x, hx⟩ := hx
  rw [eval_posNe, hx]
  exact ⟨_, rfl⟩

/-! ## TASK C — the assemblies

### C.1: the ReasonSafeUniv discharge

`ReasonSafeUniv` (Run.lean:346) quantifies an ABSTRACT
`constraintHolds`; at the concrete `DomConstraint.SatisfiedBy` the
bridge premise is the identity. Coverage is restricted to NON-linLe
registrations — the honest, purely syntactic problem-level gate for
the linLe obstruction (see the header and
`linLe_reason_valid_state_free_false`). -/
/-- A Boolean-pin literal is decided whenever the slot reads ANY
    Boolean (the eval is the equality test, total on Boolean
    reads). -/
theorem posBool_decided {a : Assignment} {s : Nat} {b : Bool}
    (hx : ∃ x : Bool, a[s]? = some (.bool x)) :
    ∃ b2, (posBool s b).eval a = some b2 := by
  obtain ⟨x, hx⟩ := hx
  refine ⟨x == b, ?_⟩
  rw [eval_posBool_eq_atom]
  simp only [Atom.eval, hx]


/-- **ReasonSafeUniv for the proved-propagator list (non-linLe
    coverage)**: every propagator's implied literal carries a VALID,
    normalized explanation, with NO state premises consumed
    (`DomainCoherent` is discharged unused). The eqSlot arm consumes
    the problem-level `IntViewedDoms` premise; every other family is
    fully state-free. -/
theorem propagatorsOfProved_reasonSafeUniv
    {problem : Problem DomConstraint Unit}
    (hview : IntViewedDoms problem.domains)
    {props : List Propagator}
    (hprops : ∀ p ∈ props, ∃ dc ∈ problem.constraints,
      propagatorOfProved dc = some p)
    (hlin : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linLe coeffs is b → coeffs.length = is.length)
    (hlinE : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linEq coeffs is b → coeffs.length = is.length) :
    ReasonSafeUniv problem DomConstraint.SatisfiedBy props := by
  intro st _hcoh p hp l r hrun
  obtain ⟨dc, hdc, hprop⟩ := hprops p hp
  rcases propagatorOfProved_run hprop hrun with
    ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, hdc2, hrun2⟩ |
    ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, k, hdc2, hrun2⟩ |
    ⟨coeffs, is, b2, hdc2, hrun2⟩ | ⟨i, c, hdc2, hrun2⟩ |
    ⟨i, c, hdc2, hrun2⟩ | ⟨i, c, hdc2, hrun2⟩ |
    ⟨i, c, hdc2, hrun2⟩ | ⟨i, v, hdc2, hrun2⟩ |
    ⟨ia, ja, hdca, hruna⟩ | ⟨ib, jb, kb, hdcb, hrunb⟩ |
    ⟨ic, jc, kc, hdcc, hrunc⟩ | ⟨id, jd, kd, hdcd, hrund⟩ |
    ⟨ie, je, ke, hdce, hrune⟩ | ⟨ig, kg, hdcg, hrung⟩ |
    ⟨lc, li, lb2, hdcl, hrunl⟩ | ⟨ti, tj, tk2, hdct, hrunt⟩ |
    ⟨ais, hdcai, hrunad⟩
  · rw [hdc2] at hdc
    exact propLe_reason_valid hdc hrun2
  · rw [hdc2] at hdc
    exact propLt_reason_valid hdc hrun2
  · rw [hdc2] at hdc
    exact propEq_reason_valid hview hdc hrun2
  · rw [hdc2] at hdc
    exact propNe_reason_valid hview hdc hrun2
  · rw [hdc2] at hdc
    exact propPlus_reason_valid hdc hrun2
  · -- linLe: the FIXED propagator's reasons are state-free valid
    rw [hdc2] at hdc
    have hlenL : coeffs.length = is.length :=
      hlin _ hdc coeffs is b2 rfl
    exact propLinLe2_reason_valid hdc hlenL hrun2
  · rw [hdc2] at hdc
    exact propLeConstHi_reason_valid hdc hrun2
  · rw [hdc2] at hdc
    exact propLeConstLo_reason_valid hdc hrun2
  · rw [hdc2] at hdc
    exact propLtConstHi_reason_valid hdc hrun2
  · rw [hdc2] at hdc
    exact propLtConstLo_reason_valid hdc hrun2
  · rw [hdc2] at hdc
    exact propConstEq_reason_valid hdc hrun2
  · rw [hdca] at hdc
    exact propBoolNot_reason_safe_sat hdc hruna
  · rw [hdcb] at hdc
    exact propBoolAnd_reason_safe_sat hdc hrunb
  · rw [hdcc] at hdc
    exact propBoolOr_reason_safe_sat hdc hrunc
  · rw [hdcd] at hdc
    exact propMin_reason_valid hdc hrund
  · rw [hdce] at hdc
    exact propMax_reason_valid hdc hrune
  · rw [hdcg] at hdc
    exact propAbs_reason_valid hdc hrung
  · rw [hdcl] at hdc
    have hlenL : lc.length = li.length :=
      hlinE _ hdc lc li lb2 rfl
    exact propLinEq2_reason_valid hdc hlenL hrunl
  · rw [hdct] at hdc
    exact propTimes_reason_valid hdc hrunt
  · rw [hdcai] at hdc
    exact propAllDiffLCG_reason_valid hrunad

/-! ### C.2: the conflict entitlement (the cc ≠ [] version)

The loop-level assembly, mirroring `propagateLoop_conflict_entitled`
(Theory.lean:1430) but with the STATE-FREE per-family entitlement in
place of its `hent` premise (which demanded `SolvedBy`): the
per-family entitlement holds at every internal solution
unconditionally, so no `SolvedBy`/`DomainCoherent` threading is
needed through the recursion — only the SCAN arm's database routing
(RunInv.clausesFixed / RunInv.learnedEntailed), which is the
`hdb`/`hlearned` pair below (with `hlearned` coming from RunInv
itself).

The neSlot arm of the per-family dispatch is handled by the `cc ≠ []`
gate: `propNe`'s conflict clause is EMPTY. The linLe arm is excluded
by the coverage premise (its conflict entitlement is also
state-dependent — see `linLe_conflict_entitled_state_free_false`). -/

/-- The sweep-level state-free conflict entitlement: every conflict
    clause reported by the sweep carries a true literal at every
    internal solution (per-family state-free entitlement for the
    propagator reports; the opposing-fact pair arm closes via the
    implied literal's DECIDEDNESS at the solution — each family's
    constraint forces the relevant views, so its implied order
    literals are decided at every internal solution). -/
theorem runPropagators_conflict_entitled_statefree
    {problem : Problem DomConstraint Unit}
    (hview : IntViewedDoms problem.domains)
    {props : List Propagator}
    (hprops : ∀ p ∈ props, ∃ dc ∈ problem.constraints,
      propagatorOfProved dc = some p)
    (hlin : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linLe coeffs is b → coeffs.length = is.length)
    (hlinE : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linEq coeffs is b → coeffs.length = is.length)
    (st0 : State) (hnone : st0.conflict = none)
    (c : Clause) (hrep : (runPropagators props st0).conflict = some c)
    (hcne : c ≠ [])
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ c, l.eval a = some true := by
  have hent : ∀ (p : Propagator) (st : State),
      p ∈ props → ∀ (cc : Clause), p.run st = .conflict cc →
        cc ≠ [] → ∃ l ∈ cc, l.eval a = some true := by
    intro p st hp cc hrun hne0
    obtain ⟨dc, hdc, hprop⟩ := hprops p hp
    rcases propagatorOfProved_run hprop hrun with
      ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, hdc2, hrun2⟩ |
      ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, k, hdc2, hrun2⟩ |
      ⟨coeffs, is, b2, hdc2, hrun2⟩ | ⟨i, c2, hdc2, hrun2⟩ |
        ⟨i, c2, hdc2, hrun2⟩ | ⟨i, c2, hdc2, hrun2⟩ |
        ⟨i, c2, hdc2, hrun2⟩ | ⟨i, v, hdc2, hrun2⟩ |
      ⟨ia, ja, hdca, hruna⟩ | ⟨ib, jb, kb, hdcb, hrunb⟩ |
      ⟨ic, jc, kc, hdcc, hrunc⟩ | ⟨id, jd, kd, hdcd, hrund⟩ |
      ⟨ie, je, ke, hdce, hrune⟩ | ⟨ig, kg, hdcg, hrung⟩ |
      ⟨lc, li, lb2, hdcl, hrunl⟩ | ⟨ti, tj, tk2, hdct, hrunt⟩ |
      ⟨ais, hdcai, hrunad⟩
    · rw [hdc2] at hdc
      exact propLe_conflict_entitled hdc hrun2 a ha
    · rw [hdc2] at hdc
      exact propLt_conflict_entitled hdc hrun2 a ha
    · rw [hdc2] at hdc
      exact propEq_conflict_entitled hview hdc hrun2 a ha
    · -- neSlot: its conflict clause is EMPTY, contradicting cc ≠ []
      exact absurd rfl (propNe_conflict_clause_empty hrun2 ▸ hne0)
    · rw [hdc2] at hdc
      exact propPlus_conflict_entitled hdc hrun2 a ha
    · rw [hdc2] at hdc
      have hlenL : coeffs.length = is.length :=
        hlin _ hdc coeffs is b2 rfl
      exact propLinLe2_entitled hdc hlenL hrun2 a ha
    · rw [hdc2] at hdc
      exact propLeConstHi_conflict_entitled hdc hrun2 a ha
    · rw [hdc2] at hdc
      exact propLeConstLo_conflict_entitled hdc hrun2 a ha
    · rw [hdc2] at hdc
      exact propLtConstHi_conflict_entitled hdc hrun2 a ha
    · rw [hdc2] at hdc
      exact propLtConstLo_conflict_entitled hdc hrun2 a ha
    · rw [hdc2] at hdc
      exact propConstEq_conflict_entitled hdc hrun2 a ha
    · rw [hdca] at hdc
      exact propBoolNot_entitled hdc hruna a ha
    · rw [hdcb] at hdc
      exact propBoolAnd_entitled hdc hrunb a ha
    · rw [hdcc] at hdc
      exact propBoolOr_entitled hdc hrunc a ha
    · rw [hdcd] at hdc
      exact propMin_entitled hdc hrund a ha
    · rw [hdce] at hdc
      exact propMax_entitled hdc hrune a ha
    · rw [hdcg] at hdc
      exact propAbs_entitled hdc hrung a ha
    · rw [hdcl] at hdc
      have hlenL : lc.length = li.length :=
        hlinE _ hdc lc li lb2 rfl
      exact propLinEq2_entitled hdc hlenL hrunl a ha
    · rw [hdct] at hdc
      exact propTimes_entitled hdc hrunt a ha
    · -- allDiff: its conflict clause is EMPTY, contradicting cc ≠ []
      exact absurd rfl (propAllDiffLCG_conflict_clause_empty hrunad ▸ hne0)
  -- the per-family implied-literal DECIDEDNESS (for the opposing-pair
  -- arm): each family's implied literal is an order/Boolean literal
  -- on a slot whose view the family's constraint forces
  have hdec : ∀ (p : Propagator) (st : State),
      p ∈ props → ∀ (lg : Literal) (rsn : Reason),
      p.run st = .implied lg rsn →
      ∃ b, lg.eval a = some b := by
    intro p st hp lg rsn hrun
    obtain ⟨dc, hdc, hprop⟩ := hprops p hp
    rcases propagatorOfProved_run hprop hrun with
      ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, hdc2, hrun2⟩ |
      ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, k, hdc2, hrun2⟩ |
      ⟨coeffs, is, b2, hdc2, hrun2⟩ | ⟨i, c2, hdc2, hrun2⟩ |
        ⟨i, c2, hdc2, hrun2⟩ | ⟨i, c2, hdc2, hrun2⟩ |
        ⟨i, c2, hdc2, hrun2⟩ | ⟨i, v, hdc2, hrun2⟩ |
      ⟨ia, ja, hdca, hruna⟩ | ⟨ib, jb, kb, hdcb, hrunb⟩ |
      ⟨ic, jc, kc, hdcc, hrunc⟩ | ⟨id, jd, kd, hdcd, hrund⟩ |
      ⟨ie, je, ke, hdce, hrune⟩ | ⟨ig, kg, hdcg, hrung⟩ |
      ⟨lc, li, lb2, hdcl, hrunl⟩ | ⟨ti, tj, tk2, hdct, hrunt⟩ |
      ⟨ais, hdcai, hrunad⟩
    · rw [hdc2] at hdc
      have hcons : (DomConstraint.leSlot i j).SatisfiedBy a :=
        ha.2 _ hdc
      obtain ⟨x, y, hx, hy⟩ := leSlot_views a i j hcons
      unfold propLe at hrun2
      split at hrun2
      · rcases firstEvent_mem
          [narrowHi st i _ [posLe i _, negLe j _],
           narrowLo st j _ [negLe j _, posLe i _]]
          (.implied lg rsn) hrun2 with hstable | hmem
        · exact absurd hstable (by intro hc; cases hc)
        · rcases List.mem_cons.mp hmem with harm | harm
          · obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm harm)
            subst hl
            exact posLe_decided ⟨x, hx⟩
          · obtain ⟨hl, _⟩ := narrowLo_implied_inv
              (Eq.symm (List.mem_singleton.mp harm))
            subst hl
            exact negLe_decided ⟨y, hy⟩
      · exact absurd hrun2 (by intro hc; simp at hc)
    · rw [hdc2] at hdc
      have hcons : (DomConstraint.ltSlot i j).SatisfiedBy a :=
        ha.2 _ hdc
      obtain ⟨x, y, hx, hy⟩ := ltSlot_views a i j hcons
      unfold propLt at hrun2
      split at hrun2
      · rcases firstEvent_mem
          [narrowHi st i _ [posLe i _, negLe j _],
           narrowLo st j _ [negLe j _, posLe i _]]
          (.implied lg rsn) hrun2 with hstable | hmem
        · exact absurd hstable (by intro hc; cases hc)
        · rcases List.mem_cons.mp hmem with harm | harm
          · obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm harm)
            subst hl
            exact posLe_decided ⟨x, hx⟩
          · obtain ⟨hl, _⟩ := narrowLo_implied_inv
              (Eq.symm (List.mem_singleton.mp harm))
            subst hl
            exact negLe_decided ⟨y, hy⟩
      · exact absurd hrun2 (by intro hc; simp at hc)
    · rw [hdc2] at hdc
      obtain ⟨x, y, hx, hy, _⟩ := eqSlot_views_prob hview hdc ha
      unfold propEq at hrun2
      split at hrun2
      · rcases firstEvent_mem
          [narrowLo st i _ [negLe i _, posLe j _],
           narrowHi st i _ [posLe i _, negLe j _],
           narrowLo st j _ [negLe j _, posLe i _],
           narrowHi st j _ [posLe j _, negLe i _]]
          (.implied lg rsn) hrun2 with hstable | hmem
        · exact absurd hstable (by intro hc; cases hc)
        · rcases List.mem_cons.mp hmem with harm1 | hrest1
          · obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm harm1)
            subst hl
            exact negLe_decided ⟨x, hx⟩
          · rcases List.mem_cons.mp hrest1 with harm2 | hrest2
            · obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm harm2)
              subst hl
              exact posLe_decided ⟨x, hx⟩
            · rcases List.mem_cons.mp hrest2 with harm3 | hrest3
              · obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm harm3)
                subst hl
                exact negLe_decided ⟨y, hy⟩
              · obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm
                  (List.mem_singleton.mp hrest3))
                subst hl
                exact posLe_decided ⟨y, hy⟩
      · exact absurd hrun2 (by intro hc; simp at hc)
    · -- neSlot: the implied literal is posNe on one of the two
      -- slots; the constraint forces both reads, and the fit at the
      -- problem's int-viewed domains gives both views
      rw [hdc2] at hdc
      have hcons : (DomConstraint.neSlot i j).SatisfiedBy a :=
        ha.2 _ hdc
      obtain ⟨p, q, hpi, hqj, _⟩ := hcons
      have hmemi : p ∈ problem.domains.getD i [] := ha.1.2 i p hpi
      have hmemj : q ∈ problem.domains.getD j [] := ha.1.2 j q hqj
      have hvi : Value.intView p ≠ none :=
        intViewedDoms_getD hview i p hmemi
      have hvj : Value.intView q ≠ none :=
        intViewedDoms_getD hview j q hmemj
      have hxi : ∃ x, slotInt a i = some x := by
        show ∃ x, (a[i]?.bind Value.intView) = some x
        rw [hpi]
        cases hv : Value.intView p with
        | none => exact absurd hv hvi
        | some w => exact ⟨w, by rw [Option.bind_some]; exact hv⟩
      have hyj : ∃ y, slotInt a j = some y := by
        show ∃ y, (a[j]?.bind Value.intView) = some y
        rw [hqj]
        cases hv : Value.intView q with
        | none => exact absurd hv hvj
        | some w => exact ⟨w, by rw [Option.bind_some]; exact hv⟩
      rcases propNe_implied_inv hrun2 with
        ⟨x2, c2, _, hl, _, _, _, _⟩ | ⟨y2, c2, _, hl, _, _, _, _⟩
      · subst hl; exact posNe_decided hyj
      · subst hl; exact posNe_decided hxi
    · rw [hdc2] at hdc
      have hcons : (DomConstraint.plusSlot i j k).SatisfiedBy a :=
        ha.2 _ hdc
      obtain ⟨x, y, z, hx, hy, hz⟩ := plusSlot_views a i j k hcons
      unfold propPlus at hrun2
      split at hrun2
      · rcases firstEvent_mem
          [narrowLo st i _ [_, _, _], narrowHi st i _ [_, _, _],
           narrowLo st j _ [_, _, _], narrowHi st j _ [_, _, _],
           narrowLo st k _ [_, _, _], narrowHi st k _ [_, _, _]]
          (.implied lg rsn) hrun2 with hstable | hmem
        · exact absurd hstable (by intro hc; cases hc)
        · rcases List.mem_cons.mp hmem with h1' | hrest1
          · obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm h1')
            subst hl
            exact negLe_decided ⟨x, hx⟩
          · rcases List.mem_cons.mp hrest1 with h2' | hrest2
            · obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm h2')
              subst hl
              exact posLe_decided ⟨x, hx⟩
            · rcases List.mem_cons.mp hrest2 with h3' | hrest3
              · obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm h3')
                subst hl
                exact negLe_decided ⟨y, hy⟩
              · rcases List.mem_cons.mp hrest3 with h4' | hrest4
                · obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm h4')
                  subst hl
                  exact posLe_decided ⟨y, hy⟩
                · rcases List.mem_cons.mp hrest4 with h5' | hrest5
                  · obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm h5')
                    subst hl
                    exact negLe_decided ⟨z, hz⟩
                  · obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm
                      (List.mem_singleton.mp hrest5))
                    subst hl
                    exact posLe_decided ⟨z, hz⟩
      · exact absurd hrun2 (by intro hc; simp at hc)
    · -- linLe: the implied literal is an order literal on the FIRST
      -- ±1 slot of the sweep; the constraint's reads-int bridge at
      -- the zipped pair (derived from the emission inversion's
      -- zipIdx membership) gives the slotInt read
      rw [hdc2] at hdc
      have hlenL : coeffs.length = is.length :=
        hlin _ hdc coeffs is b2 rfl
      have hreads := linLe2_reads_int (ha.2 _ hdc) hlenL
      rcases propLinLe2_emission_inv hrun2 with hstable |
        ⟨m, i, rest, lr, hmem, _, _, _, hnarrow⟩ |
        ⟨m, i, rest, lr, hmem, _, _, _, hnarrow⟩ |
        ⟨m, i, rest, lr, c, hmem, _, _, _, _, hnarrow⟩ |
        ⟨m, i, rest, lr, c, hmem, _, _, _, _, hnarrow⟩
      · exact absurd hstable (by intro hc; cases hc)
      · obtain ⟨hl, _⟩ := narrowHi_implied_inv hnarrow.symm
        subst hl
        obtain ⟨xt, hxt⟩ :=
          hreads (1, m) (lin2_mem_zip_of_zipIdx _ 0 ((1, m), i) hmem)
        exact posLe_decided ⟨xt, hxt⟩
      · obtain ⟨hl, _⟩ := narrowLo_implied_inv hnarrow.symm
        subst hl
        obtain ⟨xt, hxt⟩ :=
          hreads (-1, m) (lin2_mem_zip_of_zipIdx _ 0 ((-1, m), i) hmem)
        exact negLe_decided ⟨xt, hxt⟩
      · -- the general c > 0 slot: the implied literal is an order
        -- literal on the zipped slot (the head of a narrowHi call)
        obtain ⟨hl, _⟩ := narrowHi_implied_inv hnarrow.symm
        subst hl
        obtain ⟨xt, hxt⟩ :=
          hreads (c, m) (lin2_mem_zip_of_zipIdx _ 0 ((c, m), i) hmem)
        exact posLe_decided ⟨xt, hxt⟩
      · -- the general c < 0 slot: the head of a narrowLo call
        obtain ⟨hl, _⟩ := narrowLo_implied_inv hnarrow.symm
        subst hl
        obtain ⟨xt, hxt⟩ :=
          hreads (c, m) (lin2_mem_zip_of_zipIdx _ 0 ((c, m), i) hmem)
        exact negLe_decided ⟨xt, hxt⟩
    · -- leConstHi: implied posLe i c2; the constraint pins the view
      rw [hdc2] at hdc
      obtain ⟨hl, _⟩ := narrowHi_implied_inv hrun2
      subst hl
      obtain ⟨p, hread, _⟩ := leConstHi_views (ha.2 _ hdc)
      exact posLe_decided ⟨p, hread⟩
    · rw [hdc2] at hdc
      obtain ⟨hl, _⟩ := narrowLo_implied_inv hrun2
      subst hl
      obtain ⟨p, hread, _⟩ := leConstLo_views (ha.2 _ hdc)
      exact negLe_decided ⟨p, hread⟩
    · rw [hdc2] at hdc
      obtain ⟨hl, _⟩ := narrowHi_implied_inv hrun2
      subst hl
      obtain ⟨p, hread, _⟩ := ltConstHi_views (ha.2 _ hdc)
      exact posLe_decided ⟨p, hread⟩
    · rw [hdc2] at hdc
      obtain ⟨hl, _⟩ := narrowLo_implied_inv hrun2
      subst hl
      obtain ⟨p, hread, _⟩ := ltConstLo_views (ha.2 _ hdc)
      exact negLe_decided ⟨p, hread⟩
    · rw [hdc2] at hdc
      -- constEq: int arm — the view is pinned; bool arm — posBool;
      -- set/array — never implied
      cases v with
      | int k2 =>
          have hxk : slotInt a i = some k2 :=
            constEqInt_views (ha.2 _ hdc)
          simp only [propConstEq] at hrun2
          rcases firstEvent_mem [narrowHi st i k2 [posLe i k2],
              narrowLo st i k2 [negLe i (k2 - 1)]]
              (.implied lg rsn) hrun2 with hstable | hmem
          · exact absurd hstable (by intro hc; cases hc)
          · rcases List.mem_cons.mp hmem with harm | harm
            · obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm harm)
              subst hl
              exact posLe_decided ⟨k2, hxk⟩
            · obtain ⟨hl, _⟩ := narrowLo_implied_inv
                (Eq.symm (List.mem_singleton.mp harm))
              subst hl
              exact negLe_decided ⟨k2, hxk⟩
      | bool b2 =>
          simp only [propConstEq] at hrun2
          split at hrun2
          · split at hrun2
            · exact absurd hrun2 (by intro hc; cases hc)
            · injection hrun2 with hl hr2
              cases hl
              cases hr2
              exact ⟨_, by rw [eval_posBool_iff]; exact ha.2 _ hdc⟩
          · exact absurd hrun2 (by intro hc; cases hc)
      | setOfInt s2 =>
          have hst : propConstEq st i (.setOfInt s2) = .stable := rfl
          rw [hst] at hrun2
          exact absurd hrun2 (by intro hc; cases hc)
      | array xs2 =>
          have hst : propConstEq st i (.array xs2) = .stable := rfl
          rw [hst] at hrun2
          exact absurd hrun2 (by intro hc; cases hc)
    · -- boolNotSlot: the implied literal is a posBool on i or j;
      -- the constraint forces both reads to be Booleans
      rw [hdca] at hdc
      have hcons : (DomConstraint.boolNotSlot ia ja).SatisfiedBy a :=
        ha.2 _ hdc
      obtain ⟨p, q, hp, hq, _⟩ := boolNotSlot_views hcons
      rcases propBoolNot_emit hruna with
        ⟨_, himit⟩ | ⟨_, himit⟩ | ⟨_, himit⟩ | ⟨_, himit⟩ | hstable
      · obtain ⟨hl, _⟩ := implyBool_implied_inv himit
        subst hl
        exact posBool_decided ⟨p, hp⟩
      · obtain ⟨hl, _⟩ := implyBool_implied_inv himit
        subst hl
        exact posBool_decided ⟨p, hp⟩
      · obtain ⟨hl, _⟩ := implyBool_implied_inv himit
        subst hl
        exact posBool_decided ⟨q, hq⟩
      · obtain ⟨hl, _⟩ := implyBool_implied_inv himit
        subst hl
        exact posBool_decided ⟨q, hq⟩
      · exact absurd hstable (by intro hc; cases hc)
    · -- boolAndSlot: the implied literal is a posBool on i, j, or k
      rw [hdcb] at hdc
      have hcons : (DomConstraint.boolAndSlot ib jb kb).SatisfiedBy a :=
        ha.2 _ hdc
      obtain ⟨p, q, r2, hp, hq, hr⟩ := boolAndSlot_views hcons
      rcases propBoolAnd_emit hrunb with
        ⟨_, _, himit⟩ | ⟨_, _, himit⟩ | ⟨_, _, himit⟩ | ⟨_, himit⟩ |
        ⟨_, himit⟩ | hstable
      · obtain ⟨hl, _⟩ := implyBool_implied_inv himit
        subst hl
        exact posBool_decided ⟨r2, hr.1⟩
      · obtain ⟨hl, _⟩ := implyBool_implied_inv himit
        subst hl
        exact posBool_decided ⟨q, hq⟩
      · obtain ⟨hl, _⟩ := implyBool_implied_inv himit
        subst hl
        exact posBool_decided ⟨p, hp⟩
      · obtain ⟨hl, _⟩ := implyBool_implied_inv himit
        subst hl
        exact posBool_decided ⟨r2, hr.1⟩
      · obtain ⟨hl, _⟩ := implyBool_implied_inv himit
        subst hl
        exact posBool_decided ⟨r2, hr.1⟩
      · exact absurd hstable (by intro hc; cases hc)
    · -- boolOrSlot: dually
      rw [hdcc] at hdc
      have hcons : (DomConstraint.boolOrSlot ic jc kc).SatisfiedBy a :=
        ha.2 _ hdc
      obtain ⟨p, q, r2, hp, hq, hr⟩ := boolOrSlot_views hcons
      rcases propBoolOr_emit hrunc with
        ⟨_, _, himit⟩ | ⟨_, _, himit⟩ | ⟨_, _, himit⟩ | ⟨_, himit⟩ |
        ⟨_, himit⟩ | hstable
      · obtain ⟨hl, _⟩ := implyBool_implied_inv himit
        subst hl
        exact posBool_decided ⟨r2, hr.1⟩
      · obtain ⟨hl, _⟩ := implyBool_implied_inv himit
        subst hl
        exact posBool_decided ⟨q, hq⟩
      · obtain ⟨hl, _⟩ := implyBool_implied_inv himit
        subst hl
        exact posBool_decided ⟨p, hp⟩
      · obtain ⟨hl, _⟩ := implyBool_implied_inv himit
        subst hl
        exact posBool_decided ⟨r2, hr.1⟩
      · obtain ⟨hl, _⟩ := implyBool_implied_inv himit
        subst hl
        exact posBool_decided ⟨r2, hr.1⟩
      · exact absurd hstable (by intro hc; cases hc)
    · -- minSlot: implied literals are order literals on i/j/k; the
      -- views give all three slotInt reads
      rw [hdcd] at hdc
      have hcons : (DomConstraint.minSlot id jd kd).SatisfiedBy a :=
        ha.2 _ hdc
      obtain ⟨x, y, z, hx, hy, hz, _⟩ := minSlot_views a id jd kd hcons
      unfold propMin at hrund
      split at hrund
      · rcases firstEvent_mem
          [narrowLo st kd _ [_, _, _], narrowHi st kd _ [_, _, _],
           narrowLo st id _ [_, _], narrowLo st jd _ [_, _]]
          (.implied lg rsn) hrund with hstable | hmem
        · exact absurd hstable (by intro hc; cases hc)
        · rcases List.mem_cons.mp hmem with h1' | hrest1
          · obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm h1')
            subst hl
            exact negLe_decided ⟨z, hz⟩
          · rcases List.mem_cons.mp hrest1 with h2' | hrest2
            · obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm h2')
              subst hl
              exact posLe_decided ⟨z, hz⟩
            · rcases List.mem_cons.mp hrest2 with h3' | hrest3
              · obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm h3')
                subst hl
                exact negLe_decided ⟨x, hx⟩
              · obtain ⟨hl, _⟩ := narrowLo_implied_inv
                  (Eq.symm (List.mem_singleton.mp hrest3))
                subst hl
                exact negLe_decided ⟨y, hy⟩
      · exact absurd hrund (by intro hc; simp at hc)
    · -- maxSlot: dually
      rw [hdce] at hdc
      have hcons : (DomConstraint.maxSlot ie je ke).SatisfiedBy a :=
        ha.2 _ hdc
      obtain ⟨x, y, z, hx, hy, hz, _⟩ := maxSlot_views a ie je ke hcons
      unfold propMax at hrune
      split at hrune
      · rcases firstEvent_mem
          [narrowLo st ke _ [_, _, _], narrowHi st ke _ [_, _, _],
           narrowHi st ie _ [_, _], narrowHi st je _ [_, _]]
          (.implied lg rsn) hrune with hstable | hmem
        · exact absurd hstable (by intro hc; cases hc)
        · rcases List.mem_cons.mp hmem with h1' | hrest1
          · obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm h1')
            subst hl
            exact negLe_decided ⟨z, hz⟩
          · rcases List.mem_cons.mp hrest1 with h2' | hrest2
            · obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm h2')
              subst hl
              exact posLe_decided ⟨z, hz⟩
            · rcases List.mem_cons.mp hrest2 with h3' | hrest3
              · obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm h3')
                subst hl
                exact posLe_decided ⟨x, hx⟩
              · obtain ⟨hl, _⟩ := narrowHi_implied_inv
                  (Eq.symm (List.mem_singleton.mp hrest3))
                subst hl
                exact posLe_decided ⟨y, hy⟩
      · exact absurd hrune (by intro hc; simp at hc)
    · -- absSlot: implied literals are order literals on i or k
      rw [hdcg] at hdc
      have hcons : (DomConstraint.absSlot ig kg).SatisfiedBy a :=
        ha.2 _ hdc
      obtain ⟨x, r2, hx, hr, _⟩ := absSlot_views a ig kg hcons
      unfold propAbs at hrung
      split at hrung
      · rcases firstEvent_mem
          [narrowLo st kg 0 [negLe kg (-1)], narrowLo st kg _ [_, _, _],
           narrowHi st kg _ [_, _, _], narrowHi st ig _ [_, _],
           narrowLo st ig _ [_, _]]
          (.implied lg rsn) hrung with hstable | hmem
        · exact absurd hstable (by intro hc; cases hc)
        · rcases List.mem_cons.mp hmem with h1' | hrest1
          · obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm h1')
            subst hl
            exact negLe_decided ⟨r2, hr⟩
          · rcases List.mem_cons.mp hrest1 with h2' | hrest2
            · obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm h2')
              subst hl
              exact negLe_decided ⟨r2, hr⟩
            · rcases List.mem_cons.mp hrest2 with h3' | hrest3
              · obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm h3')
                subst hl
                exact posLe_decided ⟨r2, hr⟩
              · rcases List.mem_cons.mp hrest3 with h4' | hrest4
                · obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm h4')
                  subst hl
                  exact posLe_decided ⟨x, hx⟩
                · obtain ⟨hl, _⟩ := narrowLo_implied_inv
                    (Eq.symm (List.mem_singleton.mp hrest4))
                  subst hl
                  exact negLe_decided ⟨x, hx⟩
      · exact absurd hrung (by intro hc; simp at hc)
    · -- linEq: the implied literal is an order literal on the ±1
      -- slot; the constraint's reads-int bridge at the zipped pair
      -- (derived from the emission inversion's zipIdx membership)
      -- gives the slotInt read
      rw [hdcl] at hdc
      have hlenL : lc.length = li.length :=
        hlinE _ hdc lc li lb2 rfl
      have hreads := linEq2_reads_int (ha.2 _ hdc) hlenL
      rcases propLinEq2_emission_inv hrunl with hstable |
        ⟨m, i, rest, lr, hmem, _, _, _, hnarrow⟩ |
        ⟨m, i, rest, hr, hmem, _, _, _, hnarrow⟩ |
        ⟨m, i, rest, lr, hmem, _, _, _, hnarrow⟩ |
        ⟨m, i, rest, hr, hmem, _, _, _, hnarrow⟩ |
        ⟨m, i, rest, lr, c, hmem, _, _, _, _, hnarrow⟩ |
        ⟨m, i, rest, hr, c, hmem, _, _, _, _, hnarrow⟩ |
        ⟨m, i, rest, lr, c, hmem, _, _, _, _, hnarrow⟩ |
        ⟨m, i, rest, hr, c, hmem, _, _, _, _, hnarrow⟩
      · exact absurd hstable (by intro hc; cases hc)
      · obtain ⟨hl, _⟩ := narrowHi_implied_inv hnarrow.symm
        subst hl
        obtain ⟨xt, hxt⟩ :=
          hreads (1, m) (lin2_mem_zip_of_zipIdx _ 0 ((1, m), i) hmem)
        exact posLe_decided ⟨xt, hxt⟩
      · obtain ⟨hl, _⟩ := narrowLo_implied_inv hnarrow.symm
        subst hl
        obtain ⟨xt, hxt⟩ :=
          hreads (1, m) (lin2_mem_zip_of_zipIdx _ 0 ((1, m), i) hmem)
        exact negLe_decided ⟨xt, hxt⟩
      · obtain ⟨hl, _⟩ := narrowLo_implied_inv hnarrow.symm
        subst hl
        obtain ⟨xt, hxt⟩ :=
          hreads (-1, m) (lin2_mem_zip_of_zipIdx _ 0 ((-1, m), i) hmem)
        exact negLe_decided ⟨xt, hxt⟩
      · obtain ⟨hl, _⟩ := narrowHi_implied_inv hnarrow.symm
        subst hl
        obtain ⟨xt, hxt⟩ :=
          hreads (-1, m) (lin2_mem_zip_of_zipIdx _ 0 ((-1, m), i) hmem)
        exact posLe_decided ⟨xt, hxt⟩
      · -- the general c > 0 HiMin arm's implied literal
        obtain ⟨hl, _⟩ := narrowHi_implied_inv hnarrow.symm
        subst hl
        obtain ⟨xt, hxt⟩ :=
          hreads (c, m) (lin2_mem_zip_of_zipIdx _ 0 ((c, m), i) hmem)
        exact posLe_decided ⟨xt, hxt⟩
      · -- the general c > 0 LoMax arm's implied literal
        obtain ⟨hl, _⟩ := narrowLo_implied_inv hnarrow.symm
        subst hl
        obtain ⟨xt, hxt⟩ :=
          hreads (c, m) (lin2_mem_zip_of_zipIdx _ 0 ((c, m), i) hmem)
        exact negLe_decided ⟨xt, hxt⟩
      · -- the general c < 0 LoMin arm's implied literal
        obtain ⟨hl, _⟩ := narrowLo_implied_inv hnarrow.symm
        subst hl
        obtain ⟨xt, hxt⟩ :=
          hreads (c, m) (lin2_mem_zip_of_zipIdx _ 0 ((c, m), i) hmem)
        exact negLe_decided ⟨xt, hxt⟩
      · -- the general c < 0 HiMax arm's implied literal
        obtain ⟨hl, _⟩ := narrowHi_implied_inv hnarrow.symm
        subst hl
        obtain ⟨xt, hxt⟩ :=
          hreads (c, m) (lin2_mem_zip_of_zipIdx _ 0 ((c, m), i) hmem)
        exact posLe_decided ⟨xt, hxt⟩
    · -- timesSlot: the implied literal is an order literal on one of
      -- the three slots; the constraint's views give the slotInt
      -- read, and the emission-slot inversion routes it
      rw [hdct] at hdc
      obtain ⟨x, y, z, hx, hy, hz, _⟩ :=
        timesSlot_views a ti tj tk2 (ha.2 _ hdc)
      rcases propTimes_implied_slot hrunt with
        ⟨_, hl⟩ | ⟨_, hl⟩ | ⟨_, hl⟩ | ⟨_, hl⟩ | ⟨_, hl⟩ | ⟨_, hl⟩
      · subst hl; exact negLe_decided ⟨x, hx⟩
      · subst hl; exact posLe_decided ⟨x, hx⟩
      · subst hl; exact negLe_decided ⟨y, hy⟩
      · subst hl; exact posLe_decided ⟨y, hy⟩
      · subst hl; exact negLe_decided ⟨z, hz⟩
      · subst hl; exact posLe_decided ⟨z, hz⟩
    · -- allDiff: never implies
      exact (propAllDiffLCG_never_implied hrunad).elim
  -- the sweep induction (mirroring runPropagators_conflict_entitled's
  -- goInv, with the state-free per-family entitlement)
  have goInv : ∀ (ps : List Propagator) (acc : State),
      (∀ q ∈ ps, q ∈ props) →
      acc.conflict = none →
      ∀ d, (runPropagators.go ps acc).conflict = some d →
        d ≠ [] →
        ∃ l ∈ d, l.eval a = some true := by
    intro ps
    induction ps with
    | nil =>
        intro acc _ hacnone d hgo _
        rw [show (runPropagators.go [] acc) = acc from rfl, hacnone] at hgo
        exact absurd hgo (by intro hc; cases hc)
    | cons p rest ih =>
        intro acc hmem hacnone d hgo hdne
        have hp : p ∈ props := hmem p (List.mem_cons_self)
        have hrest : ∀ q ∈ rest, q ∈ props := fun q hq =>
          hmem q (List.mem_cons_of_mem _ hq)
        simp only [runPropagators.go] at hgo
        split at hgo
        · rename_i his
          rw [hacnone] at his
          exact absurd his (by simp)
        · split at hgo
          · exact ih acc hrest hacnone d hgo hdne
          · rename_i c2 heq
            have hc2d : c2 = d := by injection hgo
            subst hc2d
            exact hent p acc hp c2 heq hdne
          · rename_i lg rsn hres
            -- the opposing-pair arm: enqueueNorm either preserves
            -- the conflict slot (recurse) or sets [lg.norm, ¬lg.norm]
            -- (close via the literal's decidedness)
            obtain ⟨b, hb⟩ := hdec p acc hp lg rsn hres
            have hbn : st0.negOnTrail (lg.norm) = false → True := by
              intro _
              trivial
            cases hb1 : acc.litOnTrail lg.norm with
            | true =>
                have hstate : enqueueNorm acc lg (some rsn) = acc := by
                  simp only [enqueueNorm, hb1, if_true]
                rw [hstate] at hgo
                exact ih acc hrest hacnone d hgo hdne
            | false =>
                cases hb2 : acc.negOnTrail lg.norm with
                | true =>
                    have hpair : (enqueueNorm acc lg (some rsn)).conflict
                        = some [lg.norm, lg.norm.negate] := by
                      simp only [enqueueNorm, hb1, Bool.false_eq_true,
                        if_false, hb2, if_true]
                    have hpass : (runPropagators.go rest
                        (enqueueNorm acc lg (some rsn))).conflict
                        = some [lg.norm, lg.norm.negate] :=
                      runPropagators_go_conflict_fixed props rest
                        (enqueueNorm acc lg (some rsn))
                        [lg.norm, lg.norm.negate] hpair
                    rw [hpass] at hgo
                    injection hgo with hgo4
                    -- lg is decided at a, so lg.norm is decided
                    have hbn2 : ∃ b2, (lg.norm).eval a = some b2 := by
                      rw [Literal.norm_eval lg a]
                      exact ⟨b, hb⟩
                    obtain ⟨q, hq, hqe⟩ := pair_true_of_decided hbn2
                    refine ⟨q, ?_, hqe⟩
                    rw [← hgo4]
                    have hmem2 : q ∈ [lg.norm.norm, lg.norm.norm.negate] :=
                      hq
                    rcases List.mem_cons.mp hmem2 with h | h
                    · rw [h, norm_norm lg]
                      exact List.mem_cons_self
                    · rw [List.mem_singleton.mp h, norm_norm lg]
                      exact List.mem_cons_of_mem _ List.mem_cons_self
                | false =>
                    have hstate2 : (enqueueNorm acc lg (some rsn)).conflict
                        = none := by
                      simp only [enqueueNorm, hb1, hb2,
                        Bool.false_eq_true, if_false]
                      exact hacnone
                    exact ih (enqueueNorm acc lg (some rsn)) hrest
                      hstate2 d hgo hdne
  exact goInv props st0 (fun _ hq => hq) hnone c hrep hcne

/-! ### The scan-unit enqueue is unconditionally conflict-clear

`scanClause`'s unit verdict `(l, r)` requires: no literal of the
scanned clause is on the trail (the `any litOnTrail` guard), and `l`
itself is not trail-negated (the filter kept it). Both facts transfer
to the NORMALIZED literal (`norm_norm`, `norm_negate_norm`), so
`enqueueNorm`'s skip and opposing-pair branches are both unreachable
— the fresh branch leaves the conflict slot alone. This is what makes
the loop's unit arm state-free (no justification premise needed). -/

/-- The scan-unit inversion: the reported unit is neither on the
    trail nor trail-negated. -/
theorem scanClause_unit_inv {st : State} {c : Clause} {l : Literal}
    {r : Reason} (hcs : scanClause st c = some (.inr (l, r))) :
    st.litOnTrail l = false ∧ st.negOnTrail l = false := by
  unfold scanClause at hcs
  split at hcs
  · exact absurd hcs (by simp)
  · rename_i hany
    have hanyf : (c.any fun l => st.litOnTrail l) = false := by
      simpa using hany
    match hf : c.filter (fun l => !st.negOnTrail l) with
    | [] => rw [hf] at hcs; exact absurd hcs (by simp)
    | [l2] =>
        rw [hf] at hcs
        injection hcs with h1
        cases h1
        have hmem : l ∈ c.filter (fun l => !st.negOnTrail l) := by
          rw [hf]
          exact List.mem_cons_self
        have hlmem : l ∈ c := (List.mem_filter.mp hmem).1
        have hneg : st.negOnTrail l = false := by
          simpa using (List.mem_filter.mp hmem).2
        have hlit : st.litOnTrail l = false := by
          have := List.any_eq_false.mp hanyf l hlmem
          simpa using this
        exact ⟨hlit, hneg⟩
    | l1 :: l2 :: rest => rw [hf] at hcs; exact absurd hcs (by simp)

/-- The scan-unit enqueue is unconditionally conflict-clear (the skip
    and opposing-pair branches are both unreachable: normalization is
    invisible to the trail queries). -/
theorem enqueueNorm_scanUnit_conflict_none {st : State} {c : Clause}
    {l : Literal} {r : Reason}
    (hcs : scanClause st c = some (.inr (l, r)))
    (hnone : st.conflict = none) :
    (enqueueNorm st l (some r)).conflict = none := by
  obtain ⟨hlit, hneg⟩ := scanClause_unit_inv hcs
  simp only [enqueueNorm]
  have h1 : st.litOnTrail l.norm = false := by
    unfold State.litOnTrail
    rw [norm_norm l]
    exact hlit
  have h2 : st.negOnTrail l.norm = false := by
    unfold State.negOnTrail
    rw [norm_negate_norm l]
    exact hneg
  rw [h1, h2]
  rw [show (enqueue st l.norm (some r)).conflict = st.conflict from rfl]
  exact hnone

/-! ### C.3: the loop-level conflict entitlement (the hconfent shape)

Mirrors `propagateLoop_conflict_entitled`'s (Theory.lean:1430) fuel
induction, but with NO `SolvedBy`/`DomainCoherent` threading:

* the per-family conflict entitlement (Task B) is state-free — the
  sweep arm closes by C.2 at ANY state;
* the unit arm is unconditionally conflict-clear
  (`enqueueNorm_scanUnit_conflict_none`: the scan's own trail checks
  transfer through normalization);
* the only facts the recursion threads are the two DATABASE routings
  of the scan arm — `st.clauses = problem.clauses`
  (RunInv.clausesFixed) and the learned clauses' entitlement
  (RunInv.learnedEntailed) — both unconditionally preserved by the
  loop's state transformers (`enqueueNorm_clauses` /
  `enqueueNorm_learned`, `runPropagators_go_clauses` /
  `runPropagators_go_learned`).

Coverage gates (both in `hprops`): linLe (state-dependent nogoods —
see the header and the counterexamples below) and neSlot (empty
conflict clause — the `cc ≠ []` gate). -/

/-- The loop-level state-free conflict entitlement: every NONEMPTY
    conflict clause reported by a conflict-free propagation run from a
    RunInv state carries a true literal at every internal solution —
    the `hconfent` consumption site's shape (cc ≠ []).

    `hsolvable` is carried for signature compatibility with the
    master theorem's premise list; the state-free route does not
    consume it. -/
theorem propagatorsOfProved_conflictEntitled
    {problem : Problem DomConstraint Unit}
    (hview : IntViewedDoms problem.domains)
    {props : List Propagator}
    (_hsolvable : ∃ b, ProblemSolution problem DomConstraint.SatisfiedBy b)
    (hprops : ∀ p ∈ props, ∃ dc ∈ problem.constraints,
      propagatorOfProved dc = some p)
    (hlin : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linLe coeffs is b → coeffs.length = is.length)
    (hlinE : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linEq coeffs is b → coeffs.length = is.length)
    (hdb : ∀ c ∈ problem.clauses, ∀ a,
      ProblemSolution problem DomConstraint.SatisfiedBy a →
        ∃ l ∈ c, l.eval a = some true) :
    ∀ (st : State), st.conflict = none →
      RunInv problem DomConstraint.SatisfiedBy props st →
      ∀ cc, (propagateLoop (engineFuel st) props st).conflict
        = some cc →
        cc ≠ [] → cc.EntailedBy problem DomConstraint.SatisfiedBy := by
  intro st hc hinv cc hrep hne a ha
  -- the loop induction over fuel, threading only the state's
  -- conflict-clearness and the two database facts
  have main : ∀ (fuel : Nat) (s : State),
      s.conflict = none →
      s.clauses = problem.clauses →
      (∀ c ∈ s.learned, c.EntailedBy problem
        DomConstraint.SatisfiedBy) →
      ∀ c, (propagateLoop fuel props s).conflict = some c →
        c ≠ [] →
        ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
          ∃ l ∈ c, l.eval a = some true := by
    intro fuel
    induction fuel with
    | zero =>
        intro s hcl _ _ c hrep2 _
        simp only [propagateLoop] at hrep2
        rw [hcl] at hrep2
        exact absurd hrep2 (by simp)
    | succ fuel ih =>
        intro s hcl sclfix slearned c hrep2 hcne a ha
        cases hscan : scanAll s with
        | none =>
            have hUnf : propagateLoop (fuel + 1) props s =
                (if ((runPropagators props s).trail.length ==
                    s.trail.length) = true
                  then runPropagators props s
                  else propagateLoop fuel props
                    (runPropagators props s)) := by
              simp [propagateLoop, hcl, hscan, Option.isSome_none]
            rw [hUnf] at hrep2
            by_cases hlen : ((runPropagators props s).trail.length ==
                s.trail.length) = true
            · -- quiesced: the sweep's own conflict — the STATE-FREE
              -- per-family entitlement (C.2), gated by cc ≠ []
              -- (neSlot's empty clause never reaches here)
              rw [if_pos hlen] at hrep2
              exact runPropagators_conflict_entitled_statefree hview
                hprops hlin hlinE s hcl c hrep2 hcne a ha
            · rw [if_neg hlen] at hrep2
              -- the swept state's two database facts (both
              -- unconditionally preserved by the sweep)
              have hcl2 : (runPropagators props s).clauses
                  = s.clauses := by
                unfold runPropagators
                exact runPropagators_go_clauses props s
              have hln2 : (runPropagators props s).learned
                  = s.learned := by
                unfold runPropagators
                exact runPropagators_go_learned props s
              cases hconf2 : (runPropagators props s).conflict with
              | none =>
                  exact ih (runPropagators props s) hconf2
                    (by rw [hcl2]; exact sclfix)
                    (by rw [hln2]; exact slearned) c hrep2 hcne a ha
              | some c2 =>
                  -- the swept conflict is final (the loop head
                  -- returns a conflict-carrying state unchanged)
                  have hfix : propagateLoop fuel props
                      (runPropagators props s)
                      = runPropagators props s :=
                    propagateLoop_conflict_fix props fuel
                      (runPropagators props s) c2 hconf2
                  rw [hfix] at hrep2
                  have hc2c : c2 = c := by
                    rw [hconf2] at hrep2
                    injection hrep2
                  subst hc2c
                  exact runPropagators_conflict_entitled_statefree
                    hview hprops hlin hlinE s hcl c2 hconf2 hcne a ha
        | some verdict =>
            cases verdict with
            | inl c2 =>
                -- scan conflict: the reported clause is in the
                -- state's database — entailed BY PREMISE (hdb via
                -- clausesFixed; learnedEntailed)
                have hUnf : propagateLoop (fuel + 1) props s
                    = { s with conflict := some c2 } := by
                  simp [propagateLoop, hcl, hscan, Option.isSome_none]
                rw [hUnf] at hrep2
                injection hrep2 with hrep3
                subst hrep3
                obtain ⟨d, hdm, hds⟩ :=
                  scanAll_inl_full (st := s) (c := c2) hscan
                have hdc : d = c2 :=
                  (scanClause_inl_eq (st := s) (c := c2)
                    (d := d) hds).symm
                subst hdc
                rcases List.mem_append.mp hdm with hclm | hlnm
                · rw [sclfix] at hclm
                  exact hdb d hclm a ha
                · exact slearned d hlnm a ha
            | inr w =>
                obtain ⟨l, r⟩ := w
                have hUnf : propagateLoop (fuel + 1) props s
                    = propagateLoop fuel props
                      (enqueueNorm s l (some r)) := by
                  simp [propagateLoop, hcl, hscan, Option.isSome_none]
                rw [hUnf] at hrep2
                -- the enqueued state: conflict-clear (the scan-unit
                -- enqueue never opposes — the scan's own trail
                -- checks transfer through normalization), databases
                -- preserved; recurse
                have hcs : scanClause s r.clause
                    = some (.inr (l, r)) := by
                  obtain ⟨c2, _, hcr, hcscan⟩ :=
                    scanAll_unit_reason hscan
                  rw [hcr] at hcscan
                  rw [hcr]
                  exact hcscan
                have hconf2 : (enqueueNorm s l (some r)).conflict
                    = none :=
                  enqueueNorm_scanUnit_conflict_none hcs hcl
                have hcl2 : (enqueueNorm s l (some r)).clauses
                    = s.clauses := enqueueNorm_clauses
                have hln2 : (enqueueNorm s l (some r)).learned
                    = s.learned := enqueueNorm_learned
                exact ih (enqueueNorm s l (some r)) hconf2
                  (by rw [hcl2]; exact sclfix)
                  (by rw [hln2]; exact slearned) c hrep2 hcne a ha
  exact main (engineFuel st) st hc hinv.clausesFixed
    hinv.learnedEntailed cc hrep hne a ha


/-! ## The level-0 justification (hjust, the rooted repair) -/

theorem fits_of_rootFacts_level0
    {Constraint : Type} {Objective : Type}
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {acc : State}
    (hcoh : DomainCoherent problem acc)
    (hlv : acc.decisionLevel = 0)
    (hrooted : ∀ e ∈ acc.trail, e.level ≤ acc.decisionLevel)
    (hrootF : RootFacts problem constraintHolds acc.trail)
    {a : Assignment}
    (hsol : ProblemSolution problem constraintHolds a) :
    a.Fits acc.domains := by
  -- rootedness + level 0: every entry IS a level-0 entry, so
  -- RootFacts makes the WHOLE trail true at every internal solution
  have htrue : ∀ e ∈ acc.trail, e.literal.eval a = some true := by
    intro e he
    have hle : e.level ≤ acc.decisionLevel := hrooted e he
    have hzero : e.level = 0 := by omega
    exact hrootF e he hzero a hsol
  -- the trail's domOfLit fold stays within a's fits (iterated firing)
  have hfit := fold_fits acc.trail a problem.domains hsol.1 htrue
  -- coherence identifies the fold with the state's domains
  have hfold : acc.domains = acc.trail.foldl
      (fun acc e => domOfLit acc e.literal) problem.domains := hcoh
  rw [hfold]
  exact hfit

/-! ## The hjust discharge (rootedness-strengthened) -/

/-- **THE `hjust` PREMISE, DISCHARGED for the registered propagator
    list** (the honest form): at every ROOTED level-0
    domain-coherent accumulator carrying the root facts, every
    implied emission of every registered propagator is TRUE at every
    internal problem solution, at the concrete
    `DomConstraint.SatisfiedBy` semantics.

    Route (per family): `fits_of_rootFacts_level0` supplies
    `a.Fits acc.domains`; the solution satisfies the family's own
    constraint (the concrete semantics makes `ProblemSolution`'s
    constraint half exactly `SatisfiedBy` — no bridge premise); the
    family soundness lemma's first conjunct gives
    `l.eval a = some true`; `Literal.norm_eval` transfers it to
    `l.norm`. The `leSlot`/`ltSlot`/`plusSlot`/`linLe`/constant-bound
    families read domain extrema, hence need the fits; `eqSlot`
    additionally needs the state's domains int-viewed
    (`intViewedDoms_of_coherent` from the problem's own view plus
    coherence); `neSlot` never implies (the obligation is vacuous but
    still discharged uniformly).

    Premises `hview` / `hprops` / `hlin` are exactly the
    `propagatorsOfProved_safeUniv` premise set — no new obligations.
    The one addition over the master theorem's `hjust` is ROOTEDNESS,
    which the exact statement unjustifiably omits (it is FALSE
    without it; see `hjust_unrooted_false`) and which the
    consumption site already carries. -/
theorem propagatorsOfProved_just
    {problem : Problem DomConstraint Unit}
    (hview : IntViewedDoms problem.domains)
    {props : List Propagator}
    (hprops : ∀ p ∈ props, ∃ dc ∈ problem.constraints,
      propagatorOfProved dc = some p)
    (hlin : ∀ dc ∈ problem.constraints, ∀ (coeffs : List Int)
      (is : List Nat) (b : Int),
      dc = DomConstraint.linLe coeffs is b → coeffs.length = is.length)
    (hlinE : ∀ dc ∈ problem.constraints, ∀ (coeffs : List Int)
      (is : List Nat) (b : Int),
      dc = DomConstraint.linEq coeffs is b → coeffs.length = is.length) :
    ∀ (acc : State), DomainCoherent problem acc →
      acc.decisionLevel = 0 →
      (∀ e ∈ acc.trail, e.level ≤ acc.decisionLevel) →
      RootFacts problem DomConstraint.SatisfiedBy acc.trail →
      ∀ p ∈ props, ∀ l r, p.run acc = .implied l r →
        ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
          l.norm.eval a = some true := by
  intro acc hcoh hlv hrooted hrootF p hp l r hrun a hsol
  -- the solution fits the state's (root-pinned, folded) domains
  have hfit : a.Fits acc.domains :=
    fits_of_rootFacts_level0 hcoh hlv hrooted hrootF hsol
  -- the family dispatch: the propagator comes from a problem
  -- constraint; the emission reduces to the family propagator
  obtain ⟨dc, hdc, hprop⟩ := hprops p hp
  rcases propagatorOfProved_run hprop hrun with
    ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, hdc2, hrun2⟩ |
    ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, k, hdc2, hrun2⟩ |
    ⟨coeffs, is, b2, hdc2, hrun2⟩ | ⟨i, c, hdc2, hrun2⟩ |
    ⟨i, c, hdc2, hrun2⟩ | ⟨i, c, hdc2, hrun2⟩ |
    ⟨i, c, hdc2, hrun2⟩ | ⟨i, v, hdc2, hrun2⟩ |
    ⟨ia, ja, hdca, hruna⟩ | ⟨ib, jb, kb, hdcb, hrunb⟩ |
    ⟨ic, jc, kc, hdcc, hrunc⟩ | ⟨id, jd, kd, hdcd, hrund⟩ |
    ⟨ie, je, ke, hdce, hrune⟩ | ⟨ig, kg, hdcg, hrung⟩ |
    ⟨lc, li, lb2, hdcl, hrunl⟩ | ⟨ti, tj, tk2, hdct, hrunt⟩ |
    ⟨ais, hdcai, hrunad⟩
  · -- leSlot
    rw [hdc2] at hdc
    rw [Literal.norm_eval l a]
    exact (propLe_safe acc i j).1 l r hrun2 a hfit (hsol.2 _ hdc)
  · -- ltSlot
    rw [hdc2] at hdc
    rw [Literal.norm_eval l a]
    exact (propLt_safe acc i j).1 l r hrun2 a hfit (hsol.2 _ hdc)
  · -- eqSlot (needs the state's domains int-viewed)
    rw [hdc2] at hdc
    have hviewst : IntViewedDoms acc.domains :=
      intViewedDoms_of_coherent hview hcoh
    rw [Literal.norm_eval l a]
    exact (propEq_safe acc i j hviewst).1 l r hrun2 a hfit
      (hsol.2 _ hdc)
  · -- neSlot: the value-removal implied literal at the state's
    -- int-viewed domains (coherence-transferred)
    rw [hdc2] at hdc
    have hviewst : IntViewedDoms acc.domains :=
      intViewedDoms_of_coherent hview hcoh
    rw [Literal.norm_eval l a]
    exact (propNe_safe acc i j hviewst).1 l r hrun2 a hfit (hsol.2 _ hdc)
  · -- plusSlot
    rw [hdc2] at hdc
    rw [Literal.norm_eval l a]
    exact (propPlus_safe acc i j k).1 l r hrun2 a hfit (hsol.2 _ hdc)
  · -- linLe (the extractor's equal-length gate)
    rw [hdc2] at hdc
    have hlen : coeffs.length = is.length :=
      hlin _ hdc coeffs is b2 rfl
    rw [Literal.norm_eval l a]
    exact (propLinLe2_safe acc coeffs is b2 hlen).1 l r hrun2 a hfit
      (hsol.2 _ hdc)
  · -- leConstHi
    rw [hdc2] at hdc
    rw [Literal.norm_eval l a]
    exact (propLeConstHi_safe acc i c).1 l r hrun2 a hfit
      (hsol.2 _ hdc)
  · -- leConstLo
    rw [hdc2] at hdc
    rw [Literal.norm_eval l a]
    exact (propLeConstLo_safe acc i c).1 l r hrun2 a hfit
      (hsol.2 _ hdc)
  · -- ltConstHi
    rw [hdc2] at hdc
    rw [Literal.norm_eval l a]
    exact (propLtConstHi_safe acc i c).1 l r hrun2 a hfit
      (hsol.2 _ hdc)
  · -- ltConstLo
    rw [hdc2] at hdc
    rw [Literal.norm_eval l a]
    exact (propLtConstLo_safe acc i c).1 l r hrun2 a hfit
      (hsol.2 _ hdc)
  · -- constEq
    rw [hdc2] at hdc
    rw [Literal.norm_eval l a]
    exact (propConstEq_safe acc i v).1 l r hrun2 a hfit
      (hsol.2 _ hdc)
  · -- boolNotSlot
    rw [hdca] at hdc
    rw [Literal.norm_eval l a]
    exact (propBoolNot_safe acc ia ja).1 l r hruna a hfit
      (hsol.2 _ hdc)
  · -- boolAndSlot
    rw [hdcb] at hdc
    rw [Literal.norm_eval l a]
    exact (propBoolAnd_safe acc ib jb kb).1 l r hrunb a hfit
      (hsol.2 _ hdc)
  · -- boolOrSlot
    rw [hdcc] at hdc
    rw [Literal.norm_eval l a]
    exact (propBoolOr_safe acc ic jc kc).1 l r hrunc a hfit
      (hsol.2 _ hdc)
  · -- minSlot
    rw [hdcd] at hdc
    rw [Literal.norm_eval l a]
    exact (propMin_safe acc id jd kd).1 l r hrund a hfit
      (hsol.2 _ hdc)
  · -- maxSlot
    rw [hdce] at hdc
    rw [Literal.norm_eval l a]
    exact (propMax_safe acc ie je ke).1 l r hrune a hfit
      (hsol.2 _ hdc)
  · -- absSlot
    rw [hdcg] at hdc
    rw [Literal.norm_eval l a]
    exact (propAbs_safe acc ig kg).1 l r hrung a hfit
      (hsol.2 _ hdc)
  · -- linEq
    rw [hdcl] at hdc
    rw [Literal.norm_eval l a]
    exact (propLinEq2_safe acc lc li lb2
      (hlinE _ hdc lc li lb2 rfl)).1 l r hrunl a hfit
      (hsol.2 _ hdc)
  · -- timesSlot
    rw [hdct] at hdc
    rw [Literal.norm_eval l a]
    exact (propTimes_safe acc ti tj tk2).1 l r hrunt a hfit
      (hsol.2 _ hdc)
  · -- allDiff (never implies; the shape still discharges)
    rw [hdcai] at hdc
    rw [Literal.norm_eval l a]
    exact (propAllDiffLCG_safe acc ais).1 l r hrunad a hfit
      (hsol.2 _ hdc)

/-- The concrete front-door instantiation: the hjust obligation over
    the registered list
    `problem.constraints.filterMap propagatorOfProved`, with the
    membership premise derived by `propagatorsOfProved_mem`. -/
theorem propagatorsOfProved_just_filterMap
    {problem : Problem DomConstraint Unit}
    (hview : IntViewedDoms problem.domains)
    (hlin : ∀ dc ∈ problem.constraints, ∀ (coeffs : List Int)
      (is : List Nat) (b : Int),
      dc = DomConstraint.linLe coeffs is b → coeffs.length = is.length)
    (hlinE : ∀ dc ∈ problem.constraints, ∀ (coeffs : List Int)
      (is : List Nat) (b : Int),
      dc = DomConstraint.linEq coeffs is b → coeffs.length = is.length) :
    ∀ (acc : State), DomainCoherent problem acc →
      acc.decisionLevel = 0 →
      (∀ e ∈ acc.trail, e.level ≤ acc.decisionLevel) →
      RootFacts problem DomConstraint.SatisfiedBy acc.trail →
      ∀ p ∈ problem.constraints.filterMap propagatorOfProved,
        ∀ l r, p.run acc = .implied l r →
        ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
          l.norm.eval a = some true :=
  propagatorsOfProved_just hview
    (fun p hp => propagatorsOfProved_mem hp) hlin hlinE

/-- The equivalent level-uniform form: at a level-0 state whose trail
    entries ALL sit at level 0 (the naive reading of "level-0
    coherent accumulator"), the same hjust obligation holds. The
    premise is interderivable with rootedness at level 0. -/
theorem propagatorsOfProved_just_level0trail
    {problem : Problem DomConstraint Unit}
    (hview : IntViewedDoms problem.domains)
    {props : List Propagator}
    (hprops : ∀ p ∈ props, ∃ dc ∈ problem.constraints,
      propagatorOfProved dc = some p)
    (hlin : ∀ dc ∈ problem.constraints, ∀ (coeffs : List Int)
      (is : List Nat) (b : Int),
      dc = DomConstraint.linLe coeffs is b → coeffs.length = is.length)
    (hlinE : ∀ dc ∈ problem.constraints, ∀ (coeffs : List Int)
      (is : List Nat) (b : Int),
      dc = DomConstraint.linEq coeffs is b → coeffs.length = is.length) :
    ∀ (acc : State), DomainCoherent problem acc →
      acc.decisionLevel = 0 →
      (∀ e ∈ acc.trail, e.level = 0) →
      RootFacts problem DomConstraint.SatisfiedBy acc.trail →
      ∀ p ∈ props, ∀ l r, p.run acc = .implied l r →
        ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
          l.norm.eval a = some true := by
  intro acc hcoh hlv huniform hrootF
  refine propagatorsOfProved_just hview hprops hlin hlinE acc hcoh hlv
    (fun e he => ?_) hrootF
  have h0 : e.level = 0 := huniform e he
  have h2 : acc.decisionLevel = 0 := hlv
  rw [h0, h2]
  exact Nat.le_refl 0

/-! ## Axiom checks -/

#print axioms LeanFzn.Solver.LCG.fits_of_rootFacts_level0
#print axioms LeanFzn.Solver.LCG.propagatorsOfProved_just
#print axioms LeanFzn.Solver.LCG.propagatorsOfProved_just_filterMap
#print axioms LeanFzn.Solver.LCG.propagatorsOfProved_just_level0trail


/-! ## The initial-state seeds (the master theorem's application base) -/

theorem enqueue_step_level {st : State} {l : Literal} {r : Option Reason}
    (h : ∀ e ∈ st.trail, e.level = st.decisionLevel) :
    ∀ e ∈ (enqueue st l r).trail,
      e.level = (enqueue st l r).decisionLevel := by
  intro e he
  have htr : (enqueue st l r).trail
      = st.trail ++ [TrailEntry.mk l st.decisionLevel r] := rfl
  rw [htr, List.mem_append] at he
  rcases he with hold | hnew
  · exact h e hold
  · have hlast : e = TrailEntry.mk l st.decisionLevel r :=
      by simpa using hnew
    rw [hlast]
    rfl

/-- One enqueue step with a `none` reason: old entries keep their
    `none` reasons and the fresh entry carries `none` too. -/
theorem enqueue_step_reason_none {st : State} {l : Literal}
    (h : ∀ e ∈ st.trail, e.reason = none) :
    ∀ e ∈ (enqueue st l none).trail, e.reason = none := by
  intro e he
  have htr : (enqueue st l none).trail
      = st.trail ++ [TrailEntry.mk l st.decisionLevel none] := rfl
  rw [htr, List.mem_append] at he
  rcases he with hold | hnew
  · exact h e hold
  · have hlast : e = TrailEntry.mk l st.decisionLevel none :=
      by simpa using hnew
    rw [hlast]

/-- The root-fact fold keeps every entry at the fold's (unchanged)
    decision level. -/
theorem fold_enqueue_entries_level :
    ∀ (rs : List Literal) (st : State),
      (∀ e ∈ st.trail, e.level = st.decisionLevel) →
      ∀ e ∈ (rs.foldl (fun st l =>
        if st.litOnTrail l then st else enqueue st l none) st).trail,
        e.level = st.decisionLevel := by
  intro rs
  induction rs with
  | nil => intro st h e he; exact h e he
  | cons l rest ih =>
      intro st h e he
      rw [List.foldl_cons] at he
      cases hb : st.litOnTrail l with
      | true =>
          rw [if_pos hb] at he
          exact ih st h e he
      | false =>
          rw [if_neg (by rw [hb]; simp)] at he
          exact ih (enqueue st l none) (enqueue_step_level h) e he

/-- The root-fact fold keeps every entry's reason `none`. -/
theorem fold_enqueue_reasons_none :
    ∀ (rs : List Literal) (st : State),
      (∀ e ∈ st.trail, e.reason = none) →
      ∀ e ∈ (rs.foldl (fun st l =>
        if st.litOnTrail l then st else enqueue st l none) st).trail,
        e.reason = none := by
  intro rs
  induction rs with
  | nil => intro st h e he; exact h e he
  | cons l rest ih =>
      intro st h e he
      rw [List.foldl_cons] at he
      cases hb : st.litOnTrail l with
      | true =>
          rw [if_pos hb] at he
          exact ih st h e he
      | false =>
          rw [if_neg (by rw [hb]; simp)] at he
          exact ih (enqueue st l none) (enqueue_step_reason_none h) e he

/-- Every entry of the initial state's trail is at level 0. -/
theorem initialStateWithRoots_entries_level0
    (problem : Problem Constraint Objective) :
    ∀ e ∈ (initialStateWithRoots problem).trail, e.level = 0 := by
  intro e he
  have h := fold_enqueue_entries_level (rootFacts problem.domains)
    (initialState problem) (by
      intro e2 he2
      exact absurd he2 (by simp [initialState])) e he
  exact h

/-- Every entry of the initial state's trail carries a `none`
    reason. -/
theorem initialStateWithRoots_reasons_none
    (problem : Problem Constraint Objective) :
    ∀ e ∈ (initialStateWithRoots problem).trail, e.reason = none := by
  intro e he
  exact fold_enqueue_reasons_none (rootFacts problem.domains)
    (initialState problem) (by
      intro e2 he2
      exact absurd he2 (by simp [initialState])) e he

/-! ## Level0Solved at the initial state -/

/-- The initial state is level-0 solved: at a level-0 state whose
    entries all sit at level 0, the level-0 projection is the state
    itself (`repair0_id`), so `Level0Solved` transfers from the
    initial reachability base `initialWithRoots_solvedBy`. -/
theorem initialStateWithRoots_level0Solved
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    (hview : IntViewed problem)
    (hdb : ∀ c ∈ problem.clauses, ∀ a,
      ProblemSolution problem constraintHolds a →
        ∃ l ∈ c, l.eval a = some true) :
    Level0Solved problem constraintHolds (initialStateWithRoots problem) := by
  have hlevel : (initialStateWithRoots problem).decisionLevel = 0 :=
    initialStateWithRoots_level problem
  have hcoh : DomainCoherent problem (initialStateWithRoots problem) :=
    initialStateWithRoots_coherent problem
  have hrepair : repairAfterBackjump problem 0 (initialStateWithRoots problem)
      = initialStateWithRoots problem :=
    repair0_id problem (initialStateWithRoots problem)
      (fun e he => by
        have := initialStateWithRoots_entries_level0 problem e he
        omega)
      hcoh (initialWithRoots_fields problem).1 hlevel
  show SolvedBy problem constraintHolds
    (repairAfterBackjump problem 0 (initialStateWithRoots problem))
  rw [hrepair]
  exact initialWithRoots_solvedBy hview hdb

/-! ## RunInv at the initial state -/

/-- THE RUN-INVARIANT SEED: the state the engine actually starts from
    (`lcgSearch`'s `initialStateWithRoots`) carries the full run
    invariant.

    Premises actually needed: only `IntViewed` (the root facts' truth
    at internal solutions) and the problem's own clause normalization
    (`clausesNorm`). The clause-entitlement premise is NOT needed —
    the initial learned database is empty, so `learnedEntailed` is
    vacuous. The reason fields are vacuous (every entry's reason is
    `none`). -/
theorem initialStateWithRoots_runInv
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {props : List Propagator}
    (hview : IntViewed problem)
    (hclnorm : ∀ c ∈ problem.clauses, ∀ l ∈ c, l = l.norm) :
    RunInv problem constraintHolds props (initialStateWithRoots problem) := by
  refine ⟨?coherent, ?clausesFixed, ?learnedEntailed, ?rooted, ?trailNorm,
    ?reasonNorm, ?reasonValid, ?rootFacts, ?clausesNorm, ?learnedNorm⟩
  · exact initialStateWithRoots_coherent problem
  · exact initialWithRoots_clauses problem
  · -- learned is empty
    intro c hc
    have h2 := (initialWithRoots_fields problem).2
    rw [h2] at hc
    exact absurd hc (by simp)
  · -- every entry is at level 0 = the decision level
    intro e he
    rw [initialStateWithRoots_level problem]
    rw [initialStateWithRoots_entries_level0 problem e he]
    omega
  · -- every trail literal is a root fact, and root facts are normalized
    intro e he
    have hmem : e.literal ∈ rootFacts problem.domains :=
      initialWithRoots_trail_mem problem e he
    have hgo : rootFacts problem.domains
        = rootFacts.go 0 problem.domains := rfl
    rw [hgo] at hmem
    exact rootFacts_norm 0 problem.domains e.literal hmem
  · -- every reason is none: vacuous
    intro e he r hr
    have hnone : e.reason = none :=
      initialStateWithRoots_reasons_none problem e he
    rw [hnone] at hr
    exact absurd hr (by simp)
  · -- every reason is none: vacuous
    intro e he r hr
    have hnone : e.reason = none :=
      initialStateWithRoots_reasons_none problem e he
    rw [hnone] at hr
    exact absurd hr (by simp)
  · -- every level-0 entry's literal is a root fact, true at every
    -- internal solution (rootFacts_valid under IntViewed)
    intro e he _ a ha
    have hmem : e.literal ∈ rootFacts problem.domains :=
      initialWithRoots_trail_mem problem e he
    refine rootFacts_valid (hfit := ha.1) (hview := ?_) e.literal hmem
    intro l hl v hv
    exact intViewedDoms_getD hview l.atom.slot v hv
  · -- the original database is the problem's own
    intro c hc l hl
    have hcl : (initialStateWithRoots problem).clauses
        = problem.clauses := initialWithRoots_clauses problem
    rw [hcl] at hc
    exact hclnorm c hc l hl
  · -- the learned database is empty
    intro c hc l hl
    have h2 := (initialWithRoots_fields problem).2
    rw [h2] at hc
    exact absurd hc (by simp)

/-! ## Requested wrappers (front-door convenience)

`go_unsat_entry_invariant` (Run.lean:3756) demands the
witness-literal clause entitlement `hdb : ∀ c ∈ problem.clauses, ∀ a,
ProblemSolution problem constraintHolds a → ∃ l ∈ c, l.eval a =
some true`, so the front door carries it anyway; these wrappers give
the coordinator the exact 2/3-premise shapes requested, at the cost of
a redundant clause-entitlement premise on `runInv`. -/

/-- `Level0Solved` at the initial state (see
    `initialStateWithRoots_level0Solved`; identical statement, spelled
    with the redundant `hdb` binder for caller convenience). -/
theorem initialStateWithRoots_level0Solved'
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    (hview : IntViewed problem)
    (hdb : ∀ c ∈ problem.clauses, ∀ a,
      ProblemSolution problem constraintHolds a →
        ∃ l ∈ c, l.eval a = some true) :
    Level0Solved problem constraintHolds (initialStateWithRoots problem) :=
  initialStateWithRoots_level0Solved hview hdb

/-- `RunInv` at the initial state, spelled with the redundant
    clause-entitlement premise the front door already carries. -/
theorem initialStateWithRoots_runInv'
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {props : List Propagator}
    (hview : IntViewed problem)
    (_hdb : ∀ c ∈ problem.clauses,
      c.EntailedBy problem constraintHolds)
    (hclnorm : ∀ c ∈ problem.clauses, ∀ l ∈ c, l = l.norm) :
    RunInv problem constraintHolds props (initialStateWithRoots problem) :=
  initialStateWithRoots_runInv hview hclnorm

#print axioms initialStateWithRoots_level0Solved'
#print axioms initialStateWithRoots_runInv'
#print axioms initialStateWithRoots_level0Solved
#print axioms initialStateWithRoots_runInv
#print axioms initialStateWithRoots_entries_level0
#print axioms initialStateWithRoots_reasons_none


/-! ## Axiom checks (compile-time confirmation) -/

#print axioms LeanFzn.Solver.LCG.propagatorsOfProved_reasonSafeUniv
#print axioms LeanFzn.Solver.LCG.propagatorsOfProved_conflictEntitled
#print axioms LeanFzn.Solver.LCG.propagatorsOfProved_just
#print axioms LeanFzn.Solver.LCG.fits_of_rootFacts_level0
#print axioms LeanFzn.Solver.LCG.initialStateWithRoots_runInv
#print axioms LeanFzn.Solver.LCG.initialStateWithRoots_level0Solved

theorem posLe_eval_false_of_gt {a : Assignment} {s : Nat} {k i : Int}
    (hsi : slotInt a s = some i) (hki : k < i) :
    (posLe s k).eval a = some false := by
  rw [eval_posLe, hsi]
  show some (decide (i ≤ k)) = some false
  have hdi : decide (i ≤ k) = false := decide_eq_false (by omega)
  rw [hdi]

/-- A negative order literal is FALSE at a slot whose integer view is
    at most the bound. -/
theorem negLe_eval_false_of_le {a : Assignment} {s : Nat} {k i : Int}
    (hsi : slotInt a s = some i) (hik : i ≤ k) :
    (negLe s k).eval a = some false := by
  rw [eval_negLe, hsi]
  show some (!(decide (i ≤ k))) = some false
  have hdi : decide (i ≤ k) = true := decide_eq_true (by omega)
  rw [hdi]
  rfl

/-- A positive Boolean literal is FALSE at a slot carrying a different
    Boolean. -/
theorem posBool_eval_false_of_ne {a : Assignment} {s : Nat} {b x : Bool}
    (hslot : a[s]? = some (.bool x)) (hxb : x ≠ b) :
    (posBool s b).eval a = some false := by
  have hmap : (posBool s b).eval a = some (x == b) := by
    show ((match a[s]? with
      | some (.bool actual) => some (actual == b)
      | _ => none) : Option Bool).map
      (fun value => if (posBool s b).positive then value else !value) =
      some (x == b)
    rw [hslot]
    cases x <;> cases b <;> rfl
  rw [hmap]
  cases x <;> cases b <;> simp [hxb]

/-! ## `domOfLit` plumbing -/

/-- Updating a slot past the end of the list is the identity, so
    `domOfLit` at an out-of-range slot leaves the domains alone. -/
theorem domOfLit_ge {doms : List (List Value)} {l : Literal}
    (hge : doms.length ≤ l.atom.slot) : domOfLit doms l = doms := by
  cases l with
  | mk atom positive =>
    cases atom with
    | intLe s k =>
        have hge' : doms.length ≤ s := hge
        unfold domOfLit updateSlot
        cases positive <;> exact setSlot_eq_self_of_le doms _ s hge'
    | boolEq s b =>
        have hge' : doms.length ≤ s := hge
        unfold domOfLit updateSlot
        cases positive <;> exact setSlot_eq_self_of_le doms _ s hge'
    | intNe s k =>
        have hge' : doms.length ≤ s := hge
        unfold domOfLit updateSlot
        cases positive <;> exact setSlot_eq_self_of_le doms _ s hge'

/-- At a slot other than the literal's, `domOfLit` leaves the slot
    domain alone. -/
theorem domOfLit_getD_ne_eq {doms : List (List Value)} {l : Literal}
    {s0 : Nat} (hne : s0 ≠ l.atom.slot) :
    (domOfLit doms l).getD s0 [] = doms.getD s0 [] := by
  cases l with
  | mk atom positive =>
    cases atom with
    | intLe s k =>
        unfold domOfLit
        cases positive <;>
          exact updateSlot_getD_ne doms s _ s0 hne
    | boolEq s b =>
        unfold domOfLit
        cases positive <;>
          exact updateSlot_getD_ne doms s _ s0 hne
    | intNe s k =>
        unfold domOfLit
        cases positive <;>
          exact updateSlot_getD_ne doms s _ s0 hne

/-- THE SURVIVE STEP: if `a` fits the running domains, reads `w` at the
    literal's slot, and `w` survives the literal's narrowing of that
    slot, then `a` fits the narrowed domains. -/
theorem fits_domOfLit_of_survive {R : List (List Value)} {l : Literal}
    {a : Assignment} {w : Value}
    (hfit : a.Fits R)
    (hread : a[l.atom.slot]? = some w)
    (hsurv : w ∈ (domOfLit R l).getD l.atom.slot []) :
    a.Fits (domOfLit R l) := by
  have hlen : a.length = (domOfLit R l).length := by
    rw [domOfLit_length l]; exact hfit.1
  refine ⟨hlen, ?_⟩
  intro slot u hu
  by_cases hsl : slot = l.atom.slot
  · subst hsl
    have huw : u = w := by
      have hs1 : some u = some w := by rw [← hu]; exact hread
      exact Option.some.inj hs1
    rw [huw]
    exact hsurv
  · rw [domOfLit_getD_ne_eq hsl]
    exact hfit.2 slot u hu

/-- Past the end of `a` (hence of `R`, whose length `a` fits), the
    literal's slot is out of range and `domOfLit` is the identity. -/
theorem fits_domOfLit_of_ge {R : List (List Value)} {l : Literal}
    {a : Assignment}
    (hfit : a.Fits R) (hge : a.length ≤ l.atom.slot) :
    a.Fits (domOfLit R l) := by
  have hge' : R.length ≤ l.atom.slot := by
    have := hfit.1
    omega
  rw [domOfLit_ge hge']
  exact hfit

/-! ## The single-step divergence lemma -/

/-- THE SINGLE STEP: processing one trail entry `e` over running
    domains `R` (which `a` fits), either `e`'s literal evaluates FALSE
    at `a`, or `a` fits the narrowed domains.

    * Order entries (`intLe`): `a`'s value at the slot is `w ∈ R[s]`
      (the fit). If `w` passes the literal's bound filter it survives
      (the survive step); if it fails, its integer view violates the
      bound and the literal is FALSE at `a`. Values with no integer
      view (sets/arrays) pass every filter, so they never diverge. A
      read past the end of `a` means the slot is past the end of `R`
      too (the fit equates the lengths), where `domOfLit` is the
      identity.
    * Boolean pins (`boolEq`): the pin replaces the slot with one
      Boolean. A diverging `w` must be a Boolean ≠ the pin for the
      literal to be FALSE; `w` comes from `a`'s own value, which lies
      in the PROBLEM domain at that slot, so the `hpin` premise (all
      problem values there are Booleans) supplies the Booleanhood.
      This is the one place the extra premise is used. -/
theorem step_fits_or_false {R D : List (List Value)} {e : TrailEntry}
    {a : Assignment}
    (hfit : a.Fits R) (hprob : a.Fits D)
    (hpin : ∀ (s : Nat) (b : Bool), e.literal.atom = Atom.boolEq s b →
      ∀ v ∈ D.getD s [], ∃ x : Bool, v = Value.bool x) :
    e.literal.eval a = some false ∨ a.Fits (domOfLit R e.literal) := by
  -- destructure entry / literal / atom so every hypothesis (hpin in
  -- particular) speaks about the constructor forms
  cases e with
  | mk l level reason =>
    cases l with
    | mk atom positive =>
      cases atom with
      | intLe s k =>
          cases positive with
          | true =>
              cases hget : a[s]? with
              | none =>
                  -- past the end of a, hence of R: identity step
                  right
                  exact fits_domOfLit_of_ge hfit
                    (List.getElem?_eq_none_iff.mp hget)
              | some w =>
                  have hs : s < R.length := by
                    have hlt : s < a.length :=
                      (List.getElem?_eq_some_iff.mp hget).1
                    have hlen : a.length = R.length := hfit.1
                    rw [hlen] at hlt
                    exact hlt
                  have hwR : w ∈ R.getD s [] := hfit.2 s w hget
                  by_cases hsurv0 :
                    w ∈ domFilterInt (fun p => decide (p ≤ k)) (R.getD s [])
                  · -- survives the ≤ k filter
                    right
                    refine fits_domOfLit_of_survive hfit hget ?_
                    show w ∈ (domOfLit R
                      (Literal.mk (Atom.intLe s k) true)).getD s []
                    rw [show (domOfLit R
                        (Literal.mk (Atom.intLe s k) true)).getD s []
                        = domFilterInt (fun p => decide (p ≤ k)) (R.getD s [])
                        from updateSlot_getD_eq R s _ hs]
                    exact hsurv0
                  · -- diverges: the keep test on w fails
                    cases w with
                    | int i =>
                        have hkeep : ¬ (decide (i ≤ k) = true) := by
                          intro hc
                          exact hsurv0 (List.mem_filter.mpr ⟨hwR, hc⟩)
                        left
                        have hd : decide (i ≤ k) = false := by
                          cases hbb : decide (i ≤ k) with
                          | true => exact absurd hbb hkeep
                          | false => rfl
                        exact posLe_eval_false_of_gt
                          (by show (a[s]?.bind Value.intView) = some i
                              rw [hget]; rfl)
                          (by have := of_decide_eq_false hd; omega)
                    | bool bx =>
                        have hkeep :
                            ¬ (decide ((if bx then 1 else 0) ≤ k) = true) := by
                          intro hc
                          exact hsurv0 (List.mem_filter.mpr ⟨hwR, hc⟩)
                        left
                        have hd : decide ((if bx then 1 else 0) ≤ k) = false := by
                          cases hbb : decide ((if bx then 1 else 0) ≤ k) with
                          | true => exact absurd hbb hkeep
                          | false => rfl
                        have hnot : ¬ ((if bx then 1 else 0) ≤ k) :=
                          of_decide_eq_false hd
                        cases bx with
                        | true =>
                            have hnot2 : ¬ ((1 : Int) ≤ k) := hnot
                            exact posLe_eval_false_of_gt
                              (by show (a[s]?.bind Value.intView) = some 1
                                  rw [hget]; rfl)
                              (by omega)
                        | false =>
                            have hnot2 : ¬ ((0 : Int) ≤ k) := hnot
                            exact posLe_eval_false_of_gt
                              (by show (a[s]?.bind Value.intView) = some 0
                                  rw [hget]; rfl)
                              (by omega)
                    | setOfInt j =>
                        -- set values pass every int filter
                        exact absurd (List.mem_filter.mpr ⟨hwR, rfl⟩) hsurv0
                    | array j =>
                        exact absurd (List.mem_filter.mpr ⟨hwR, rfl⟩) hsurv0
          | false =>
              cases hget : a[s]? with
              | none =>
                  right
                  exact fits_domOfLit_of_ge hfit
                    (List.getElem?_eq_none_iff.mp hget)
              | some w =>
                  have hs : s < R.length := by
                    have hlt : s < a.length :=
                      (List.getElem?_eq_some_iff.mp hget).1
                    have hlen : a.length = R.length := hfit.1
                    rw [hlen] at hlt
                    exact hlt
                  have hwR : w ∈ R.getD s [] := hfit.2 s w hget
                  by_cases hsurv0 :
                    w ∈ domFilterInt (fun p => decide (p > k)) (R.getD s [])
                  · right
                    refine fits_domOfLit_of_survive hfit hget ?_
                    show w ∈ (domOfLit R
                      (Literal.mk (Atom.intLe s k) false)).getD s []
                    rw [show (domOfLit R
                        (Literal.mk (Atom.intLe s k) false)).getD s []
                        = domFilterInt (fun p => decide (p > k)) (R.getD s [])
                        from updateSlot_getD_eq R s _ hs]
                    exact hsurv0
                  · cases w with
                    | int i =>
                        have hkeep : ¬ (decide (i > k) = true) := by
                          intro hc
                          exact hsurv0 (List.mem_filter.mpr ⟨hwR, hc⟩)
                        left
                        have hd : decide (i > k) = false := by
                          cases hbb : decide (i > k) with
                          | true => exact absurd hbb hkeep
                          | false => rfl
                        exact negLe_eval_false_of_le
                          (by show (a[s]?.bind Value.intView) = some i
                              rw [hget]; rfl)
                          (by have := of_decide_eq_false hd; omega)
                    | bool bx =>
                        have hkeep :
                            ¬ (decide ((if bx then 1 else 0) > k) = true) := by
                          intro hc
                          exact hsurv0 (List.mem_filter.mpr ⟨hwR, hc⟩)
                        left
                        have hd : decide ((if bx then 1 else 0) > k) = false := by
                          cases hbb : decide ((if bx then 1 else 0) > k) with
                          | true => exact absurd hbb hkeep
                          | false => rfl
                        have hnot : ¬ ((if bx then 1 else 0) > k) :=
                          of_decide_eq_false hd
                        cases bx with
                        | true =>
                            have hnot2 : ¬ ((1 : Int) > k) := hnot
                            exact negLe_eval_false_of_le
                              (by show (a[s]?.bind Value.intView) = some 1
                                  rw [hget]; rfl)
                              (by omega)
                        | false =>
                            have hnot2 : ¬ ((0 : Int) > k) := hnot
                            exact negLe_eval_false_of_le
                              (by show (a[s]?.bind Value.intView) = some 0
                                  rw [hget]; rfl)
                              (by omega)
                    | setOfInt j =>
                        exact absurd (List.mem_filter.mpr ⟨hwR, rfl⟩) hsurv0
                    | array j =>
                        exact absurd (List.mem_filter.mpr ⟨hwR, rfl⟩) hsurv0
      | boolEq s b =>
          cases positive with
          | true =>
              cases hget : a[s]? with
              | none =>
                  right
                  exact fits_domOfLit_of_ge hfit
                    (List.getElem?_eq_none_iff.mp hget)
              | some w =>
                  have hs : s < R.length := by
                    have hlt : s < a.length :=
                      (List.getElem?_eq_some_iff.mp hget).1
                    have hlen : a.length = R.length := hfit.1
                    rw [hlen] at hlt
                    exact hlt
                  -- a's own value at the slot lies in the problem's
                  -- domain, which the pin premise makes all-Boolean
                  have hwD : w ∈ D.getD s [] := hprob.2 s w hget
                  obtain ⟨x, hx⟩ := hpin s b rfl w hwD
                  by_cases hxb : w = Value.bool b
                  · -- w IS the pinned Boolean: survives
                    right
                    refine fits_domOfLit_of_survive hfit hget ?_
                    show w ∈ (domOfLit R
                      (Literal.mk (Atom.boolEq s b) true)).getD s []
                    have hgoal : (domOfLit R
                        (Literal.mk (Atom.boolEq s b) true)).getD s []
                        = [Value.bool b] := by
                      unfold domOfLit
                      rw [updateSlot_getD_eq R s _ hs]
                      cases b <;> rfl
                    rw [hgoal]
                    exact List.mem_singleton.mpr hxb
                  · -- w is a DIFFERENT Boolean: the pin is false at a
                    have hxbne : x ≠ b := fun h => hxb (by rw [hx, h])
                    left
                    have hget' : a[s]? = some (Value.bool x) := by
                      rw [hget, hx]
                    exact posBool_eval_false_of_ne hget' hxbne
          | false =>
              cases hget : a[s]? with
              | none =>
                  right
                  exact fits_domOfLit_of_ge hfit
                    (List.getElem?_eq_none_iff.mp hget)
              | some w =>
                  have hs : s < R.length := by
                    have hlt : s < a.length :=
                      (List.getElem?_eq_some_iff.mp hget).1
                    have hlen : a.length = R.length := hfit.1
                    rw [hlen] at hlt
                    exact hlt
                  have hwD : w ∈ D.getD s [] := hprob.2 s w hget
                  obtain ⟨x, hx⟩ := hpin s b rfl w hwD
                  by_cases hxb : w = Value.bool (!b)
                  · right
                    refine fits_domOfLit_of_survive hfit hget ?_
                    show w ∈ (domOfLit R
                      (Literal.mk (Atom.boolEq s b) false)).getD s []
                    have hgoal : (domOfLit R
                        (Literal.mk (Atom.boolEq s b) false)).getD s []
                        = [Value.bool (!b)] := by
                      unfold domOfLit
                      rw [updateSlot_getD_eq R s _ hs]
                      cases b <;> rfl
                    rw [hgoal]
                    exact List.mem_singleton.mpr hxb
                  · have hxbne : x ≠ (!b) := fun h => hxb (by rw [hx, h])
                    left
                    have hget' : a[s]? = some (Value.bool x) := by
                      rw [hget, hx]
                    -- the negative Boolean literal evaluates like its
                    -- normalized positive form `posBool s (!b)`
                    rw [← Literal.norm_eval
                      (Literal.mk (Atom.boolEq s b) false) a]
                    show (posBool s (!b)).eval a = some false
                    exact posBool_eval_false_of_ne hget' hxbne
      | intNe s k =>
          cases positive with
          | true =>
              cases hget : a[s]? with
              | none =>
                  right
                  exact fits_domOfLit_of_ge hfit
                    (List.getElem?_eq_none_iff.mp hget)
              | some w =>
                  have hs : s < R.length := by
                    have hlt : s < a.length :=
                      (List.getElem?_eq_some_iff.mp hget).1
                    have hlen : a.length = R.length := hfit.1
                    rw [hlen] at hlt
                    exact hlt
                  have hwR : w ∈ R.getD s [] := hfit.2 s w hget
                  by_cases hsurv0 :
                    w ∈ domFilterInt (fun p => decide (p ≠ k)) (R.getD s [])
                  · -- survives the ≠ k filter
                    right
                    refine fits_domOfLit_of_survive hfit hget ?_
                    show w ∈ (domOfLit R
                      (Literal.mk (Atom.intNe s k) true)).getD s []
                    rw [show (domOfLit R
                        (Literal.mk (Atom.intNe s k) true)).getD s []
                        = domFilterInt (fun p => decide (p ≠ k)) (R.getD s [])
                        from updateSlot_getD_eq R s _ hs]
                    exact hsurv0
                  · -- diverges: the keep test on w fails, so its view
                    -- IS k and the positive value-removal literal is
                    -- FALSE at a
                    cases w with
                    | int i =>
                        have hkeep : ¬ (decide (i ≠ k) = true) := by
                          intro hc
                          exact hsurv0 (List.mem_filter.mpr ⟨hwR, hc⟩)
                        have hd : decide (i ≠ k) = false := by
                          cases hbb : decide (i ≠ k) with
                          | true => exact absurd hbb hkeep
                          | false => rfl
                        have hik : i = k := by
                          have hnn : ¬ (i ≠ k) := of_decide_eq_false hd
                          omega
                        left
                        have hsk : slotInt a s = some k := by
                          show (a[s]?.bind Value.intView) = some k
                          rw [hget]
                          show (Value.int i).intView = some k
                          rw [hik]
                          rfl
                        exact posNe_eval_false_of_eq hsk rfl
                    | bool bx =>
                        have hkeep :
                            ¬ (decide ((if bx then 1 else 0) ≠ k) = true) := by
                          intro hc
                          exact hsurv0 (List.mem_filter.mpr ⟨hwR, hc⟩)
                        have hd : decide ((if bx then 1 else 0) ≠ k) = false := by
                          cases hbb : decide ((if bx then 1 else 0) ≠ k) with
                          | true => exact absurd hbb hkeep
                          | false => rfl
                        have hnot : (if bx then 1 else 0) = k := by
                          have hnn : ¬ ((if bx then 1 else 0) ≠ k) :=
                            of_decide_eq_false hd
                          omega
                        left
                        have hsk : slotInt a s = some k := by
                          show (a[s]?.bind Value.intView) = some k
                          rw [hget]
                          show (Value.bool bx).intView = some k
                          show (some (if bx then 1 else 0)) = some k
                          rw [hnot]
                        exact posNe_eval_false_of_eq hsk rfl
                    | setOfInt j =>
                        -- set values pass every int filter
                        exact absurd (List.mem_filter.mpr ⟨hwR, rfl⟩) hsurv0
                    | array j =>
                        exact absurd (List.mem_filter.mpr ⟨hwR, rfl⟩) hsurv0
          | false =>
              cases hget : a[s]? with
              | none =>
                  right
                  exact fits_domOfLit_of_ge hfit
                    (List.getElem?_eq_none_iff.mp hget)
              | some w =>
                  have hs : s < R.length := by
                    have hlt : s < a.length :=
                      (List.getElem?_eq_some_iff.mp hget).1
                    have hlen : a.length = R.length := hfit.1
                    rw [hlen] at hlt
                    exact hlt
                  have hwR : w ∈ R.getD s [] := hfit.2 s w hget
                  by_cases hsurv0 :
                    w ∈ domFilterInt (fun p => decide (p = k)) (R.getD s [])
                  · -- survives the = k filter
                    right
                    refine fits_domOfLit_of_survive hfit hget ?_
                    show w ∈ (domOfLit R
                      (Literal.mk (Atom.intNe s k) false)).getD s []
                    rw [show (domOfLit R
                        (Literal.mk (Atom.intNe s k) false)).getD s []
                        = domFilterInt (fun p => decide (p = k)) (R.getD s [])
                        from updateSlot_getD_eq R s _ hs]
                    exact hsurv0
                  · -- diverges: the keep test fails, so w's view is NOT
                    -- k; the negative value-removal literal "s = k" is
                    -- FALSE at a
                    left
                    have hvi : Value.intView w ≠ some k := by
                      intro hc
                      apply hsurv0
                      rw [domFilterInt, List.mem_filter]
                      refine ⟨hwR, ?_⟩
                      cases hw : w with
                      | int i =>
                          rw [hw] at hc
                          have hqc : Value.intView (Value.int i)
                              = some i := rfl
                          rw [hqc] at hc
                          rw [Option.some.injEq] at hc
                          show (match Value.int i with
                            | Value.int i => decide (i = k)
                            | Value.bool b => decide ((if b = true then 1 else 0) = k)
                            | x => true) = true
                          rw [show k = i from hc.symm]
                          exact decide_eq_true rfl
                      | bool bx =>
                          rw [hw] at hc
                          have hqc : Value.intView (Value.bool bx)
                              = some (if bx then 1 else 0) := rfl
                          rw [hqc] at hc
                          rw [Option.some.injEq] at hc
                          show (match Value.bool bx with
                            | Value.int i => decide (i = k)
                            | Value.bool b => decide ((if b = true then 1 else 0) = k)
                            | x => true) = true
                          rw [show k = (if bx then 1 else 0) from hc.symm]
                          exact decide_eq_true rfl
                      | setOfInt j => exact absurd hc (by simp [Value.intView])
                      | array j => exact absurd hc (by simp [Value.intView])
                    -- the negative value-removal literal "s = k" is
                    -- FALSE at a: its atom (the removal "s ≠ k") is
                    -- TRUE there (a's view at s differs from k)
                    show Literal.eval
                      (Literal.mk (Atom.intNe s k) false) a = some false
                    show (Atom.eval (Atom.intNe s k) a).map
                      (fun value =>
                        if (Literal.mk (Atom.intNe s k) false).positive
                        then value else !value) = some false
                    show (slotInt a s).map
                      (fun actual => decide (actual ≠ k)) = some true
                    rw [slotInt, hget]
                    -- w's view differs from k (hvi), so the removal
                    -- atom is TRUE at a
                    have hviewne : (Value.intView w).map
                        (fun i => decide (i ≠ k)) = some true := by
                      cases hv : Value.intView w with
                      | none => exact absurd hv (by
                          intro hcon
                          apply hvi
                          exact hcon)
                      | some i =>
                          refine congrArg some ?_
                          have hik : i ≠ k := by
                            intro hik2
                            apply hvi
                            exact hik2 ▸ hv
                          exact decide_eq_true hik
                    show (Value.intView w).map
                      (fun i => decide (i ≠ k)) = some true
                    exact hviewne

/-! ## The iterated divergence -/

/-! ## The leaf nogood (§5 item 5): the failed-leaf retreat's learned
clause is entitled

On a FAILED leaf check (all-singleton propagated state whose complete
assignment fails the problem), the engine learns
`(trail.filter level > 0).map (·.literal.negate.norm)` — the
negations of the positive-level trail literals. Every ProblemSolution
makes one of them true: a represented solution would equal the failed
assignment and pass the leaf test, so every solution either falsifies
a POSITIVE-level trail literal (its negation is the witness) or
falsifies a level-0 one — impossible by RootFacts. The one honest
extra premise is `TrailBoolPins` (Boolean-pin trail entries sit on
slots whose PROBLEM domains are all-Bool; the machine-checked
counterexample in `solver/LCG/Proofs/Obstructions.lean`
    (`boolPins_premise_necessary`) shows it is necessary
for mixed domains — which compiled models never produce: `varDomain`
yields only intDom or boolDom). -/

/-- Every Boolean-pin entry of the trail sits on a slot whose
    problem-domain values are all Booleans. The one premise this
    layer adds beyond the master theorem's other premises — see
    `solver/LCG/Proofs/Obstructions.lean`
    (`boolPins_premise_necessary`) for the machine-checked
    counterexample that makes it necessary. -/
def TrailBoolPins (D : List (List Value)) (trail : List TrailEntry) :
    Prop :=
  ∀ e ∈ trail, ∀ (s : Nat) (b : Bool), e.literal.atom = Atom.boolEq s b →
    ∀ v ∈ D.getD s [], ∃ x : Bool, v = Value.bool x

/-- THE ITERATED DIVERGENCE: walking `trail` with the `domOfLit` fold
    from running domains `R`, either some entry's literal evaluates
    FALSE at `a`, or `a` fits the fully folded domains. `hprob`
    (`a` fits the PROBLEM domains `D`) feeds the Boolean-pin case:
    the diverging value is `a`'s own value, which lies in `D`. -/
theorem fold_fits_or_falsifies {D : List (List Value)} {a : Assignment}
    (hprob : a.Fits D) :
    ∀ (trail : List TrailEntry) (R : List (List Value)),
      TrailBoolPins D trail → a.Fits R →
      (∃ e ∈ trail, e.literal.eval a = some false) ∨
        a.Fits (trail.foldl (fun acc e => domOfLit acc e.literal) R) := by
  intro trail
  induction trail with
  | nil => intro R _ hfit; exact Or.inr hfit
  | cons e rest ih =>
      intro R hbs hfit
      have hbsr : TrailBoolPins D rest :=
        fun e' he' s b hv => hbs e' (List.mem_cons_of_mem _ he') s b hv
      rcases step_fits_or_false (D := D) hfit hprob
          (hbs e List.mem_cons_self) with hev | hfit'
      · exact Or.inl ⟨e, List.mem_cons_self, hev⟩
      · rcases ih (domOfLit R e.literal) hbsr hfit' with
          ⟨e', he', hev⟩ | hf
        · exact Or.inl ⟨e', List.mem_cons_of_mem _ he', hev⟩
        · rw [List.foldl_cons]
          exact Or.inr hf

/-! ## The singleton companion -/

/-- At an all-singleton state, any two assignments fitting the
    state's domains are equal: every slot's domain is a one-value
    list, and a fitting assignment reads exactly that value. (Kept as
    a wiring convenience for the call site; the entitlement proof
    itself consumes `fits_allSingleton_eq` directly.) -/
theorem solution_eq_of_singleton_represented {st : State}
    {b1 b2 : Assignment}
    (hsingle : allSingleton st = true)
    (h1 : b1.Fits st.domains) (h2 : b2.Fits st.domains) :
    b1 = b2 := by
  have hall : ∀ i (h : i < st.domains.length), ∃ v, st.domains[i] = [v] :=
    fun i h => dom_of_allSingleton hsingle h
  refine List.ext_get ?_ ?_
  · rw [h1.1, h2.1]
  · intro n hn1 hn2
    have hnd : n < st.domains.length := by rw [← h1.1]; exact hn1
    obtain ⟨v, hv⟩ := hall n hnd
    have hgetD : st.domains.getD n [] = [v] := by
      show (st.domains[n]?.getD []) = [v]
      rw [List.getElem?_eq_some_iff.mpr ⟨hnd, hv⟩]
      rfl
    have hget1 : b1[n]? = some b1[n] :=
      List.getElem?_eq_some_iff.mpr ⟨hn1, rfl⟩
    have hget2 : b2[n]? = some b2[n] :=
      List.getElem?_eq_some_iff.mpr ⟨hn2, rfl⟩
    have hmem1 : b1[n] ∈ st.domains.getD n [] := h1.2 n b1[n] hget1
    have hmem2 : b2[n] ∈ st.domains.getD n [] := h2.2 n b2[n] hget2
    rw [hgetD] at hmem1 hmem2
    have heq1 : b1[n] = v := List.mem_singleton.mp hmem1
    have heq2 : b2[n] = v := List.mem_singleton.mp hmem2
    show b1.get ⟨n, hn1⟩ = b2.get ⟨n, hn2⟩
    rw [show b1.get ⟨n, hn1⟩ = b1[n] from rfl,
      show b2.get ⟨n, hn2⟩ = b2[n] from rfl, heq1, heq2]

/-! ## THE LEAF NOGOOD ENTITLEMENT -/

/-- THE LEAF NOGOOD ENTITLEMENT (PLAN §5 item 5). At an all-singleton,
    domain-coherent state whose complete assignment `a0` FAILED the
    engine's leaf test, the clause the engine learns at the retreat —

      (st.trail.filter fun e => e.level > 0).map
        fun e => e.literal.negate.norm

    — is entailed at every internal problem solution: every solution
    either falsifies some positive-level trail literal (whose negated,
    normalized form is IN the clause and TRUE there), or fits the
    state's domains, hence EQUALS `a0`, at which the leaf test passes —
    contradicting the failure.

    Premises (beyond the engine-observed `hsingle`/`ha`/`hfail`):
    `hcoh` (RunInv.coherent), `hroot` (RunInv.rootFacts), and
    `hboolpins` (the documented new premise; vacuous when the trail
    carries no Boolean pins). No solvability premise, no trail
    distinctness, no domains-length premise (it follows from `hcoh`). -/
theorem leafNogood_entailed
    {problem : Problem DomConstraint Unit}
    {constraintHoldsB : DomConstraint → Assignment → Bool}
    {a0 : Assignment}
    (hagrees : ∀ (c : DomConstraint) (a : Assignment),
      constraintHoldsB c a = true ↔ c.SatisfiedBy a)
    (st : State)
    (hcoh : DomainCoherent problem st)
    (hsingle : allSingleton st = true)
    (ha : singletonAssignment st = some a0)
    (hfail : ¬ (fitsB problem a0 &&
        problem.constraints.all (fun c => constraintHoldsB c a0)))
    (hroot : RootFacts problem DomConstraint.SatisfiedBy st.trail)
    (hboolpins : TrailBoolPins problem.domains st.trail) :
    ∀ (a : Assignment), ProblemSolution problem DomConstraint.SatisfiedBy a →
      ∃ l ∈ (st.trail.filter fun e => e.level > 0).map
        (fun e => e.literal.negate.norm), l.eval a = some true := by
  intro a ha2
  obtain ⟨hafit, hacs⟩ := ha2
  -- (1) the fold divergence over the state's own trail
  have hsol : ProblemSolution problem DomConstraint.SatisfiedBy a :=
    ⟨hafit, hacs⟩
  rcases fold_fits_or_falsifies (D := problem.domains) hafit st.trail
      problem.domains hboolpins hafit with
    ⟨e, hemem, hevfalse⟩ | hfits
  · -- (3) a falsifying entry: level 0 is impossible, level > 0 gives
    -- the leafNg witness
    rcases Nat.lt_or_ge e.level 1 with hzero | hpos
    · exfalso
      have hlev0 : e.level = 0 := by omega
      have htrue := hroot e hemem hlev0 a hsol
      rw [hevfalse] at htrue
      simp at htrue
    · refine ⟨e.literal.negate.norm, ?_, ?_⟩
      · exact List.mem_map_of_mem
          (List.mem_filter.mpr ⟨hemem, decide_eq_true hpos⟩)
      · rw [Literal.norm_eval, Literal.eval_negate, hevfalse]
        rfl
  · -- (2) a fits st.domains, hence a = a0, and the leaf test PASSES
    -- at a — contradicting hfail
    exfalso
    have hcoheq : st.domains = st.trail.foldl
        (fun acc e => domOfLit acc e.literal) problem.domains := hcoh
    have hfitst : a.Fits st.domains := by
      rw [hcoheq]
      exact hfits
    have haeq : a = a0 := fits_allSingleton_eq hsingle hfitst ha
    rw [← haeq] at hfail
    apply hfail
    rw [Bool.and_eq_true]
    refine ⟨fitsB_iff.mpr hafit, ?_⟩
    rw [List.all_eq_true]
    intro c hc
    exact (hagrees c a).mpr (hacs c hc)

/-! ## The corollary at the engine's retreat call-site shape

The engine's leaf arm observes the POST-PROPAGATION state `st1` (an
all-singleton, conflict-free state at a positive level whose leaf test
failed); the entitlement is consumed there with the state's own
coherence (RunInv.coherent at the entry, preserved through
`propagateLoop_coherent` in Proofs/Theory) and root facts (RunInv's
own field, preserved through `runPropagators`/`propagateLoop`). This
corollary packages the exact statement the coordinator's `hentN`
obligation for the inserted `leafNg` needs: the learned clause is
`EntailedBy` (true at every internal solution). -/

/-- The leaf nogood, packaged as clause entailment (the
    `RunInv.learnedEntailed` shape for the coordinator's insertion
    obligation). -/
theorem leafNogood_entailed_by
    {problem : Problem DomConstraint Unit}
    {constraintHoldsB : DomConstraint → Assignment → Bool}
    {a0 : Assignment}
    (hagrees : ∀ (c : DomConstraint) (a : Assignment),
      constraintHoldsB c a = true ↔ c.SatisfiedBy a)
    (st : State)
    (hcoh : DomainCoherent problem st)
    (hsingle : allSingleton st = true)
    (ha : singletonAssignment st = some a0)
    (hfail : ¬ (fitsB problem a0 &&
        problem.constraints.all (fun c => constraintHoldsB c a0)))
    (hroot : RootFacts problem DomConstraint.SatisfiedBy st.trail)
    (hboolpins : TrailBoolPins problem.domains st.trail) :
    Clause.EntailedBy problem DomConstraint.SatisfiedBy
      ((st.trail.filter fun e => e.level > 0).map
        (fun e => e.literal.negate.norm)) := by
  intro a hsa
  obtain ⟨l, hl, hev⟩ :=
    leafNogood_entailed (a0 := a0) hagrees st hcoh hsingle ha hfail hroot
      hboolpins a hsa
  exact ⟨l, hl, hev⟩

#print axioms LeanFzn.Solver.LCG.leafNogood_entailed
#print axioms LeanFzn.Solver.LCG.leafNogood_entailed_by



/-! ### The master-theorem `hleafng` premise's discharge (the gated
leaf-nogood entitlement, assembled over the proved propagators) -/

/-- `trailBoolPinsOk = true` implies `TrailBoolPins` (the executable
    gate and the Prop premise agree). -/
theorem trailBoolPinsOk_iff {problem : Problem DomConstraint Unit}
    {trail : List TrailEntry}
    (h : trailBoolPinsOk problem trail = true) :
    TrailBoolPins problem.domains trail := by
  intro e he s b hv
  have hall := List.all_eq_true.mp h e he
  cases hatom : e.literal.atom with
  | intLe s2 k => rw [hatom] at hv; cases hv
  | intNe s2 k => rw [hatom] at hv; cases hv
  | boolEq s2 b2 =>
      rw [hatom] at hv
      injection hv with hsb hb
      subst hsb
      subst hb
      rw [hatom] at hall
      intro v hv2
      have hallv := List.all_eq_true.mp hall v hv2
      cases v with
      | int i => exact absurd hallv (by simp)
      | bool x => exact ⟨x, rfl⟩
      | setOfInt si => exact absurd hallv (by simp)
      | array xs => exact absurd hallv (by simp)

/-- THE hleafng DISCHARGE: at a conflict-free run-invariant entry,
    when the executable pins gate passes, the failed leaf's nogood is
    entailed (via `leafNogood_entailed_by` at the propagated state,
    whose coherence and root facts come from the run invariant). -/
theorem propagatorsOfProved_leafng
    {problem : Problem DomConstraint Unit}
    (hview : IntViewedDoms problem.domains)
    {props : List Propagator}
    (hprops : ∀ p ∈ props, ∃ dc ∈ problem.constraints,
      propagatorOfProved dc = some p ∧
        (∀ coeffs is b, dc ≠ .linLe coeffs is b))
    (hreason : ReasonSafeUniv problem DomConstraint.SatisfiedBy props)
    (hjust : ∀ (acc : State), DomainCoherent problem acc →
      acc.decisionLevel = 0 →
      RootFacts problem DomConstraint.SatisfiedBy acc.trail →
      (∀ e ∈ acc.trail, e.level ≤ acc.decisionLevel) →
      ∀ p ∈ props, ∀ l r, p.run acc = .implied l r →
        ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
          l.norm.eval a = some true)
    (hdb : ∀ c ∈ problem.clauses,
      Clause.EntailedBy problem DomConstraint.SatisfiedBy c)
    (hagrees : ∀ (c : DomConstraint) (a : Assignment),
      DomConstraint.satisfiedB c a = true ↔ c.SatisfiedBy a) :
    ∀ (st : State), st.conflict = none →
      RunInv problem DomConstraint.SatisfiedBy props st →
      TrailDistinct st.trail →
      trailBoolPinsOk problem
        (propagateLoop (engineFuel st) props st).trail = true →
      ∀ a0, allSingleton
          (propagateLoop (engineFuel st) props st) = true →
        singletonAssignment
          (propagateLoop (engineFuel st) props st) = some a0 →
        ¬ (fitsB problem a0 &&
            problem.constraints.all
              (fun c => DomConstraint.satisfiedB c a0)) →
        Clause.EntailedBy problem DomConstraint.SatisfiedBy
          (List.map (fun e => e.literal.negate.norm)
            (List.filter (fun e => decide (e.level > 0))
              (propagateLoop (engineFuel st) props st).trail)) := by
  intro st hnone hinv hdist hgate a0 hsingle hassign hfail
  have hinv1 := propagateLoop_runInv hreason hjust hdb
    (engineFuel st) st hnone hinv
  exact leafNogood_entailed_by (a0 := a0) hagrees
    (propagateLoop (engineFuel st) props st) hinv1.coherent
    hsingle hassign hfail hinv1.rootFacts
    (trailBoolPinsOk_iff hgate)

#print axioms LeanFzn.Solver.LCG.trailBoolPinsOk_iff
#print axioms LeanFzn.Solver.LCG.propagatorsOfProved_leafng

end LeanFzn.Solver.LCG
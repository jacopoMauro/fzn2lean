/-
File: solver/LCG/Proofs/Propagators.lean

Purpose:
  Per-family propagator soundness for the real `propagatorsOf` list:
  `PropSafeUniv` (implied literals are true at every represented
  solution; conflict clauses exclude every represented solution) and
  the relativized entitlement (conflict clauses carry a true literal
  at every solution fitting the STATE's domains — the shape
  `propagateLoop_conflict_entitled` consumes) for the six registered
  families: `leSlot`, `ltSlot`, `eqSlot`, `neSlot`, `plusSlot`,
  `linLe`.

  With these theorems the certified LCG front door runs the REAL
  propagator list (Step 2's expansion obligation, PLAN item 2.3).

Method: at a solution `a` of the family's constraint
(`DomConstraint.SatisfiedBy a`), the constraint's own match arms
force every watched slot's raw read to be `.int p`, so the integer
views exist (`slotInt a s = some p`).  A solution fitting the
state's domains has each view bounded by that domain's `domMinI`/
`domMaxI` (the coherence bridges).  Each `narrowLo`/`narrowHi` arm's
implied literal — exactly `posLe s hi` / `negLe s (lo−1)` by the
implied-head inversions — then follows from the constraint plus the
bounds by arithmetic; each conflict arm fires only when the bounds
already contradict the constraint at every fitting solution; and the
nogoods are integer-valid under their constraints, giving
entitlement at every fitting solution.

Dependencies:
  - solver.LCG.Propagate: the propagator definitions.
  - solver.LCG.Proofs.Theory: gate inverses, coherence bridges.
  - solver.LCG.Encoding: literal evaluation bridges.

DAG:
  LCG.Propagate + LCG.Proofs.Theory -> LCG.Proofs.Propagators
    -> LCG.Certified (the front door with real propagators)
-/

import solver.LCG.Proofs.Theory
import solver.LCG.Propagate
import solver.LCG.Encoding

namespace LeanFzn.Solver.LCG

open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Solver (DomConstraint)

/-! ## False-evaluation inversions for order literals -/

theorem eval_posLe_false (a : Assignment) (s : Nat) (k : Int)
    (h : (posLe s k).eval a = some false) :
    ∃ i, slotInt a s = some i ∧ k < i := by
  rw [eval_posLe] at h
  match hs : slotInt a s with
  | none => rw [hs] at h; simp at h
  | some i =>
      have hdec : (decide (i ≤ k)) = false := by
        have hh : (some (decide (i ≤ k))) = some false := by rw [hs] at h; exact h
        exact Option.some.inj hh
      refine ⟨i, rfl, ?_⟩
      have : ¬ (i ≤ k) := of_decide_eq_false hdec
      omega

theorem eval_negLe_false (a : Assignment) (s : Nat) (k : Int)
    (h : (negLe s k).eval a = some false) :
    ∃ i, slotInt a s = some i ∧ i ≤ k := by
  rw [eval_negLe] at h
  match hs : slotInt a s with
  | none => rw [hs] at h; simp at h
  | some i =>
      have hdec : (!(decide (i ≤ k))) = false := by
        have hh : (some (!(decide (i ≤ k)))) = some false := by rw [hs] at h; exact h
        exact Option.some.inj hh
      have htrue : decide (i ≤ k) = true := by
        cases hdec2 : decide (i ≤ k) with
        | true => rfl
        | false => rw [hdec2] at hdec; simp at hdec
      exact ⟨i, rfl, of_decide_eq_true htrue⟩

/-! ## The fitting-assignment slot view -/

/-- A raw `.int` read determines the slot's integer view. -/
theorem slotInt_of_int_read {a : Assignment} {s : Nat} {p : Int}
    (h : a[s]? = some (Value.int p)) : slotInt a s = some p := by
  unfold slotInt
  rw [h]
  rfl

/-- The maximum-domain bound on a fitting assignment's view. -/
theorem fits_max_bound {st : State} {a : Assignment} {s : Nat}
    (hfit : Core.Assignment.Fits st.domains a) {mx : Int}
    (hmx : domMaxI (st.domains.getD s []) = some mx)
    {i : Int} (hi : slotInt a s = some i) : i ≤ mx :=
  fits_domMaxI_ge (st := st) hfit hmx hi

/-- The minimum-domain bound on a fitting assignment's view. -/
theorem fits_min_bound {st : State} {a : Assignment} {s : Nat}
    (hfit : Core.Assignment.Fits st.domains a) {mn : Int}
    (hmn : domMinI (st.domains.getD s []) = some mn)
    {i : Int} (hi : slotInt a s = some i) : mn ≤ i :=
  fits_domMinI_le (st := st) hfit hmn hi

/-! ## The implied-head and firstEvent inversions -/

/-- `narrowHi`'s implied literal is exactly `posLe s hi`. -/
theorem narrowHi_implied_inv {st : State} {s : Nat} {hi : Int}
    {ng : Clause} {l : Literal} {r : Reason}
    (h : narrowHi st s hi ng = .implied l r) :
    l = posLe s hi ∧ r = { clause := ng } := by
  unfold narrowHi at h
  split at h
  · rename_i mn mx hmn hmx
    by_cases hgt : mn > hi
    · rw [if_pos (by simpa using hgt)] at h; cases h
    · rw [if_neg (by simpa using hgt)] at h
      by_cases hlt : decide (hi < mx) = true
      · rw [if_pos hlt] at h
        cases h
        exact ⟨rfl, rfl⟩
      · rw [if_neg hlt] at h; cases h
  · cases h

/-- `narrowLo`'s implied literal is exactly `negLe s (lo−1)`. -/
theorem narrowLo_implied_inv {st : State} {s : Nat} {lo : Int}
    {ng : Clause} {l : Literal} {r : Reason}
    (h : narrowLo st s lo ng = .implied l r) :
    l = negLe s (lo - 1) ∧ r = { clause := ng } := by
  unfold narrowLo at h
  split at h
  · rename_i mn mx hmn hmx
    by_cases hlt : mx < lo
    · rw [if_pos (by simpa using hlt)] at h; cases h
    · rw [if_neg (by simpa using hlt)] at h
      by_cases hlt2 : decide (mn < lo) = true
      · rw [if_pos hlt2] at h
        cases h
        exact ⟨rfl, rfl⟩
      · rw [if_neg hlt2] at h; cases h
  · cases h

/-- `firstEvent`'s result is a list member (unless stable). -/
theorem firstEvent_mem : ∀ (rs : List PropagationResult)
    (r : PropagationResult), firstEvent rs = r →
    r = .stable ∨ r ∈ rs := by
  intro rs
  induction rs with
  | nil => intro r h; cases h; exact Or.inl rfl
  | cons hd rest ih =>
      intro r h
      cases hd with
      | stable =>
          simp only [firstEvent] at h
          rcases ih r h with hmem | hmem
          · exact Or.inl hmem
          · exact Or.inr (List.mem_cons_of_mem _ hmem)
      | implied l reason =>
          cases h
          exact Or.inr List.mem_cons_self
      | conflict c =>
          cases h
          exact Or.inr List.mem_cons_self

/-! ## Constraint semantics at integer views -/

theorem leSlot_sem {a : Assignment} {i j : Nat}
    (h : (DomConstraint.leSlot i j).SatisfiedBy a)
    {xi yj : Int}
    (hxi : slotInt a i = some xi) (hyj : slotInt a j = some yj) :
    xi ≤ yj := by
  obtain ⟨p, q, hpi, hqj, hpq⟩ := h
  rw [slotInt_of_int_read hpi] at hxi
  rw [slotInt_of_int_read hqj] at hyj
  injection hxi with hxi2
  injection hyj with hyj2
  subst hxi2; subst hyj2
  exact hpq

theorem ltSlot_sem {a : Assignment} {i j : Nat}
    (h : (DomConstraint.ltSlot i j).SatisfiedBy a)
    {xi yj : Int}
    (hxi : slotInt a i = some xi) (hyj : slotInt a j = some yj) :
    xi < yj := by
  obtain ⟨p, q, hpi, hqj, hpq⟩ := h
  rw [slotInt_of_int_read hpi] at hxi
  rw [slotInt_of_int_read hqj] at hyj
  injection hxi with hxi2
  injection hyj with hyj2
  subst hxi2; subst hyj2
  exact hpq

theorem eqSlot_sem {a : Assignment} {i j : Nat}
    (h : (DomConstraint.eqSlot i j).SatisfiedBy a)
    {xi yj : Int}
    (hxi : slotInt a i = some xi) (hyj : slotInt a j = some yj) :
    xi = yj := by
  obtain ⟨x, y, hsx, hsy, hxy⟩ := h
  -- the views are determined by the raw values
  unfold slotInt at hxi hyj
  rw [hsx, Option.bind_some] at hxi
  rw [hsy, Option.bind_some] at hyj
  cases hvx : Value.intView x with
  | none => rw [hvx] at hxi; simp at hxi
  | some p =>
      rw [hvx] at hxi
      cases hvy : Value.intView y with
      | none => rw [hvy] at hyj; simp at hyj
      | some q =>
          rw [hvy] at hyj
          injection hxi with hxi2
          injection hyj with hyj2
          -- the raw values are equal, so their views are equal
          have : x = y := hxy
          subst this
          rw [hvy] at hvx
          injection hvx with hpq
          subst hxi2; subst hyj2
          exact hpq.symm

theorem plusSlot_sem {a : Assignment} {i j k : Nat}
    (h : (DomConstraint.plusSlot i j k).SatisfiedBy a)
    {xi yj zk : Int}
    (hxi : slotInt a i = some xi) (hyj : slotInt a j = some yj)
    (hzk : slotInt a k = some zk) :
    xi + yj = zk := by
  obtain ⟨p, q, r, hpi, hqj, hread, hpqr⟩ := h
  rw [slotInt_of_int_read hpi] at hxi
  rw [slotInt_of_int_read hqj] at hyj
  rw [slotInt_of_int_read hread] at hzk
  injection hxi with hxi2
  injection hyj with hyj2
  injection hzk with hzk2
  subst hxi2; subst hyj2; subst hzk2
  exact hpqr

/-- The constraint's semantics force the watched slots' views to
    exist (the `SatisfiedBy` match arms read `.int` values). -/
theorem leSlot_views (a : Assignment) (i j : Nat)
    (h : (DomConstraint.leSlot i j).SatisfiedBy a) :
    ∃ x y, slotInt a i = some x ∧ slotInt a j = some y := by
  obtain ⟨p, q, hpi, hqj, _⟩ := h
  exact ⟨p, q, slotInt_of_int_read hpi, slotInt_of_int_read hqj⟩

/-! ## propLe soundness: `x ≤ y` over slots i j -/

/-- The propagator of a `leSlot i j` constraint: implied-literal
    soundness, conflict soundness, and entitlement, at every state. -/
theorem propLe_safe (st : State) (i j : Nat) :
    (∀ l r, propLe st i j = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.leSlot i j).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ c, propLe st i j = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.leSlot i j).SatisfiedBy a → False) ∧
    (∀ c, propLe st i j = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.leSlot i j).SatisfiedBy a →
        ∃ l ∈ c, l.eval a = some true) := by
  constructor
  · intro l r hrun a hfit hcons
    unfold propLe at hrun
    split at hrun
    next _ _ yj xi' hyj hxi' =>
      rcases firstEvent_mem [narrowHi st i yj [posLe i yj, negLe j yj],
          narrowLo st j xi' [negLe j (xi' - 1), posLe i (xi' - 1)]]
          (.implied l r) hrun with hstable | hmem
      · exact absurd hstable (by intro hc; cases hc)
      · rcases List.mem_cons.mp hmem with harm | harm
        · obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm harm)
          subst hl
          -- posLe i yj is true at a: x ≤ y (constraint) and
          -- y ≤ yj (domain max)
          obtain ⟨x, y, hx, hy⟩ := leSlot_views a i j hcons
          have hxy : x ≤ y := leSlot_sem hcons hx hy
          have hyyj : y ≤ yj := fits_max_bound hfit hyj hy
          rw [eval_posLe_iff]
          exact ⟨x, hx, by omega⟩
        · obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm
            (List.mem_singleton.mp harm))
          subst hl
          -- negLe j (xi'-1) is true at a: y > xi'-1, i.e.
          -- y ≥ xi'; x ≥ xi' (domain min) and x ≤ y
          obtain ⟨x, y, hx, hy⟩ := leSlot_views a i j hcons
          have hxy : x ≤ y := leSlot_sem hcons hx hy
          have hxix : xi' ≤ x := fits_min_bound hfit hxi' hx
          rw [eval_negLe_iff]
          refine ⟨y, hy, ?_⟩
          omega
    case h_2 => exact absurd hrun (by intro hc; simp at hc)
  · constructor
    · intro c hrun a hfit hcons
      unfold propLe at hrun
      split at hrun
      next _ _ yj xi' hyj hxi' =>
        rcases firstEvent_mem [narrowHi st i yj [posLe i yj, negLe j yj],
            narrowLo st j xi' [negLe j (xi' - 1), posLe i (xi' - 1)]]
            (.conflict c) hrun with hstable | hmem
        · exact absurd hstable (by intro hc; cases hc)
        · rcases List.mem_cons.mp hmem with harm | harm
          · -- arm-1 conflict: mn_i > yj
            obtain ⟨mn, mx, hmn, hmx, hgt, hcc⟩ :=
              narrowHi_conflict_inv (Eq.symm harm)
            -- every fitting value of slot i is > yj ≥ y ≥ x
            obtain ⟨x, y, hx, hy⟩ := leSlot_views a i j hcons
            have hxy : x ≤ y := leSlot_sem hcons hx hy
            have hyyj : y ≤ yj := fits_max_bound hfit hyj hy
            have hmnx : mn ≤ x := fits_min_bound hfit hmn hx
            omega
          · -- arm-2 conflict: mx_j < xi'
            obtain ⟨mn, mx, hmn, hmx, hlt, hcc⟩ :=
              narrowLo_conflict_inv (Eq.symm (List.mem_singleton.mp harm))
            obtain ⟨x, y, hx, hy⟩ := leSlot_views a i j hcons
            have hxy : x ≤ y := leSlot_sem hcons hx hy
            have hxix : xi' ≤ x := fits_min_bound hfit hxi' hx
            have hmxy : y ≤ mx := fits_max_bound hfit hmx hy
            omega
      next => exact absurd hrun (by intro hc; simp at hc)
    · intro c hrun a hfit hcons
      -- entitlement: the nogood is integer-valid under x ≤ y
      unfold propLe at hrun
      split at hrun
      next _ _ yj xi' hyj hxi' =>
        rcases firstEvent_mem [narrowHi st i yj [posLe i yj, negLe j yj],
            narrowLo st j xi' [negLe j (xi' - 1), posLe i (xi' - 1)]]
            (.conflict c) hrun with hstable | hmem
        · exact absurd hstable (by intro hc; cases hc)
        · rcases List.mem_cons.mp hmem with harm | harm
          · obtain ⟨mn, mx, hmn, hmx, hgt, hcc⟩ :=
              narrowHi_conflict_inv (Eq.symm harm)
            -- nogood [posLe i yj, negLe j yj]: x ≤ y ≤ yj gives
            -- posLe i yj true
            obtain ⟨x, y, hx, hy⟩ := leSlot_views a i j hcons
            have hxy : x ≤ y := leSlot_sem hcons hx hy
            have hyyj : y ≤ yj := fits_max_bound hfit hyj hy
            refine ⟨posLe i yj, by rw [hcc]; exact List.mem_cons_self, ?_⟩
            rw [eval_posLe_iff]
            exact ⟨x, hx, by omega⟩
          · obtain ⟨mn, mx, hmn, hmx, hlt, hcc⟩ :=
              narrowLo_conflict_inv (Eq.symm (List.mem_singleton.mp harm))
            -- nogood [negLe j (xi'-1), posLe i (xi'-1)]:
            -- x ≥ xi' (min) and x ≤ y gives y ≥ xi' > xi'-1
            obtain ⟨x, y, hx, hy⟩ := leSlot_views a i j hcons
            have hxy : x ≤ y := leSlot_sem hcons hx hy
            have hxix : xi' ≤ x := fits_min_bound hfit hxi' hx
            refine ⟨negLe j (xi' - 1), by
              rw [hcc]
              exact List.mem_cons_self, ?_⟩
            rw [eval_negLe_iff]
            exact ⟨y, hy, by omega⟩
      next => exact absurd hrun (by intro hc; simp at hc)

/-! ## The propagator registration lemmas -/

/-- A propagator in `propagatorsOf dcs` comes from a constraint in
    `dcs` via `propagatorOf`. -/
theorem propagatorsOf_mem : ∀ (dcs : List DomConstraint)
    (p : Propagator), p ∈ propagatorsOf dcs →
    ∃ dc ∈ dcs, propagatorOf dc = some p := by
  intro dcs
  induction dcs with
  | nil => intro p hp; cases hp
  | cons dc rest ih =>
      intro p hp
      cases hpdc : propagatorOf dc with
      | none =>
          simp only [propagatorsOf, List.filterMap_cons, hpdc,
            Option.map_none] at hp
          obtain ⟨dc2, hdc2mem, hdc2⟩ := ih p hp
          exact ⟨dc2, List.mem_cons_of_mem _ hdc2mem, hdc2⟩
      | some p0 =>
          simp only [propagatorsOf, List.filterMap_cons, hpdc,
            Option.map_some] at hp
          rcases List.mem_cons.mp hp with hp2 | hp2
          · rw [hp2]
            exact ⟨dc, List.mem_cons_self, hpdc⟩
          · obtain ⟨dc2, hdc2mem, hdc2⟩ := ih p hp2
            exact ⟨dc2, List.mem_cons_of_mem _ hdc2mem, hdc2⟩

/-- The per-family dispatcher: for a `leSlot` constraint in the
    problem, its propagator's implied literals are true at every
    represented solution. -/
theorem propagatorOf_leSlot_implied {problem : Problem DomConstraint Unit}
    {st : State} {i j : Nat} {l : Literal} {r : Reason}
    (hprob : DomConstraint.leSlot i j ∈ problem.constraints)
    (hr : propLe st i j = .implied l r)
    (a : Assignment)
    (hsol : ProblemSolution problem DomConstraint.SatisfiedBy a)
    (hrep : st.Represents a) :
    l.eval a = some true := by
  -- the solution satisfies this constraint
  have hcons : (DomConstraint.leSlot i j).SatisfiedBy a :=
    hsol.2 _ hprob
  -- the representation gives Fits
  obtain ⟨hfit, _, _, _⟩ := hrep
  exact (propLe_safe st i j).1 l r hr a hfit hcons

/-- The per-family dispatcher: for a `leSlot` constraint in the
    problem, its propagator's conflicts exclude every represented
    solution. -/
theorem propagatorOf_leSlot_conflict {problem : Problem DomConstraint Unit}
    {st : State} {i j : Nat} {c : Clause}
    (hprob : DomConstraint.leSlot i j ∈ problem.constraints)
    (hr : propLe st i j = .conflict c)
    (a : Assignment)
    (hsol : ProblemSolution problem DomConstraint.SatisfiedBy a)
    (hrep : st.Represents a) :
    ¬ c.SatisfiedBy a := by
  have hcons : (DomConstraint.leSlot i j).SatisfiedBy a :=
    hsol.2 _ hprob
  obtain ⟨hfit, _, _, _⟩ := hrep
  -- conflict excludes: derive False from c being satisfied
  intro hcsat
  obtain ⟨w, hw, hwe⟩ := hcsat
  -- but propLe_safe's conflict arm shows no fitting solution exists
  have := (propLe_safe st i j).2.1 c hr a hfit hcons
  exact this

/-- The per-family dispatcher: for a `leSlot` constraint in the
    problem, its propagator's conflict clauses carry a true literal
    at every solution fitting the state's domains. -/
theorem propagatorOf_leSlot_entitled
    {problem : Problem DomConstraint Unit}
    {st : State} {i j : Nat} {c : Clause}
    (hprob : DomConstraint.leSlot i j ∈ problem.constraints)
    (hr : propLe st i j = .conflict c)
    (hsol : SolvedBy problem DomConstraint.SatisfiedBy st)
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ c, l.eval a = some true := by
  have hcons : (DomConstraint.leSlot i j).SatisfiedBy a :=
    ha.2 _ hprob
  -- solutions fit the state's domains (SolvedBy)
  have hfit : a.Fits st.domains := (hsol a ha).1
  exact (propLe_safe st i j).2.2 c hr a hfit hcons


/-! ## propLt soundness: `x < y` over slots i j -/

theorem ltSlot_views (a : Assignment) (i j : Nat)
    (h : (DomConstraint.ltSlot i j).SatisfiedBy a) :
    ∃ x y, slotInt a i = some x ∧ slotInt a j = some y := by
  obtain ⟨p, q, hpi, hqj, _⟩ := h
  exact ⟨p, q, slotInt_of_int_read hpi, slotInt_of_int_read hqj⟩

theorem propLt_safe (st : State) (i j : Nat) :
    (∀ l r, propLt st i j = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.ltSlot i j).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ c, propLt st i j = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.ltSlot i j).SatisfiedBy a → False) ∧
    (∀ c, propLt st i j = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.ltSlot i j).SatisfiedBy a →
        ∃ l ∈ c, l.eval a = some true) := by
  constructor
  · intro l r hrun a hfit hcons
    unfold propLt at hrun
    split at hrun
    next _ _ yj xi' hyj hxi' =>
      rcases firstEvent_mem [narrowHi st i (yj - 1) [posLe i (yj - 1), negLe j yj],
          narrowLo st j (xi' + 1) [negLe j xi', posLe i (xi' - 1)]]
          (.implied l r) hrun with hstable | hmem
      · exact absurd hstable (by intro hc; cases hc)
      · rcases List.mem_cons.mp hmem with harm | harm
        · obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm harm)
          subst hl
          -- posLe i (yj-1) true: x < y ≤ yj gives x ≤ yj-1
          obtain ⟨x, y, hx, hy⟩ := ltSlot_views a i j hcons
          have hxy : x < y := ltSlot_sem hcons hx hy
          have hyyj : y ≤ yj := fits_max_bound hfit hyj hy
          rw [eval_posLe_iff]
          exact ⟨x, hx, by omega⟩
        · obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm
            (List.mem_singleton.mp harm))
          subst hl
          -- negLe j xi' true: x ≥ xi' and x < y gives y > xi'
          obtain ⟨x, y, hx, hy⟩ := ltSlot_views a i j hcons
          have hxy : x < y := ltSlot_sem hcons hx hy
          have hxix : xi' ≤ x := fits_min_bound hfit hxi' hx
          rw [eval_negLe_iff]
          refine ⟨y, hy, ?_⟩
          omega
    next => exact absurd hrun (by intro hc; simp at hc)
  · constructor
    · intro c hrun a hfit hcons
      unfold propLt at hrun
      split at hrun
      next _ _ yj xi' hyj hxi' =>
        rcases firstEvent_mem [narrowHi st i (yj - 1) [posLe i (yj - 1), negLe j yj],
            narrowLo st j (xi' + 1) [negLe j xi', posLe i (xi' - 1)]]
            (.conflict c) hrun with hstable | hmem
        · exact absurd hstable (by intro hc; cases hc)
        · rcases List.mem_cons.mp hmem with harm | harm
          · obtain ⟨mn, mx, hmn, hmx, hgt, hcc⟩ :=
              narrowHi_conflict_inv (Eq.symm harm)
            obtain ⟨x, y, hx, hy⟩ := ltSlot_views a i j hcons
            have hxy : x < y := ltSlot_sem hcons hx hy
            have hyyj : y ≤ yj := fits_max_bound hfit hyj hy
            have hmnx : mn ≤ x := fits_min_bound hfit hmn hx
            omega
          · obtain ⟨mn, mx, hmn, hmx, hlt, hcc⟩ :=
              narrowLo_conflict_inv (Eq.symm (List.mem_singleton.mp harm))
            obtain ⟨x, y, hx, hy⟩ := ltSlot_views a i j hcons
            have hxy : x < y := ltSlot_sem hcons hx hy
            have hxix : xi' ≤ x := fits_min_bound hfit hxi' hx
            have hmxy : y ≤ mx := fits_max_bound hfit hmx hy
            omega
      next => exact absurd hrun (by intro hc; simp at hc)
    · intro c hrun a hfit hcons
      unfold propLt at hrun
      split at hrun
      next _ _ yj xi' hyj hxi' =>
        rcases firstEvent_mem [narrowHi st i (yj - 1) [posLe i (yj - 1), negLe j yj],
            narrowLo st j (xi' + 1) [negLe j xi', posLe i (xi' - 1)]]
            (.conflict c) hrun with hstable | hmem
        · exact absurd hstable (by intro hc; cases hc)
        · rcases List.mem_cons.mp hmem with harm | harm
          · obtain ⟨mn, mx, hmn, hmx, hgt, hcc⟩ :=
              narrowHi_conflict_inv (Eq.symm harm)
            obtain ⟨x, y, hx, hy⟩ := ltSlot_views a i j hcons
            have hxy : x < y := ltSlot_sem hcons hx hy
            have hyyj : y ≤ yj := fits_max_bound hfit hyj hy
            refine ⟨posLe i (yj - 1), by rw [hcc]; exact List.mem_cons_self, ?_⟩
            rw [eval_posLe_iff]
            exact ⟨x, hx, by omega⟩
          · obtain ⟨mn, mx, hmn, hmx, hlt, hcc⟩ :=
              narrowLo_conflict_inv (Eq.symm (List.mem_singleton.mp harm))
            obtain ⟨x, y, hx, hy⟩ := ltSlot_views a i j hcons
            have hxy : x < y := ltSlot_sem hcons hx hy
            have hxix : xi' ≤ x := fits_min_bound hfit hxi' hx
            refine ⟨negLe j xi', by rw [hcc]; exact List.mem_cons_self, ?_⟩
            rw [eval_negLe_iff]
            exact ⟨y, hy, by omega⟩
      next => exact absurd hrun (by intro hc; simp at hc)


/-- At an int-viewed domain list, every fitting read has an
    integer view. -/
theorem view_of_fit {doms : List (List Value)}
    (hview : IntViewedDoms doms) {s : Nat} {p : Value}
    (hmem : p ∈ doms.getD s []) :
    Value.intView p ≠ none := by
  match doms with
  | [] => exact absurd hmem (by simp)
  | d :: rest =>
      match s with
      | 0 => exact hview d (List.mem_cons_self) p hmem
      | s+1 =>
          have hrest : IntViewedDoms rest := fun d hd => hview d
            (List.mem_cons_of_mem _ hd)
          have : p ∈ rest.getD s [] := hmem
          exact view_of_fit hrest this

/-! ## propEq soundness: `x = y` over slots i j -/

theorem eqSlot_views {st : State} (a : Assignment) (i j : Nat)
    (hview : IntViewedDoms st.domains)
    (hfit : Core.Assignment.Fits st.domains a)
    (h : (DomConstraint.eqSlot i j).SatisfiedBy a) :
    ∃ x y, slotInt a i = some x ∧ slotInt a j = some y ∧ x = y := by
  obtain ⟨p, q, hsx, hsy, hpq⟩ := h
  -- both raw reads are in their slots' domains, so int-viewed
  have hvmem1 : p ∈ st.domains.getD i [] := hfit.2 i p hsx
  have hvmem2 : q ∈ st.domains.getD j [] := hfit.2 j q hsy
  have hv1 := view_of_fit hview hvmem1
  have hv2 := view_of_fit hview hvmem2
  match hv : Value.intView p with
  | none => exact absurd hv hv1
  | some x2 =>
      -- q = p (hpq), so q's view is also x2: q's view can't be none
      have hqview : Value.intView q = some x2 := by
        rw [← hpq]
        exact hv
      refine ⟨x2, x2, ?_, ?_, rfl⟩
      · show (a[i]?.bind Value.intView) = some x2
        rw [hsx, Option.bind_some, hv]
      · show (a[j]?.bind Value.intView) = some x2
        rw [hsy, Option.bind_some, hqview]

theorem propEq_safe (st : State) (i j : Nat)
    (hview : IntViewedDoms st.domains) :
    (∀ l r, propEq st i j = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.eqSlot i j).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ c, propEq st i j = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.eqSlot i j).SatisfiedBy a → False) ∧
    (∀ c, propEq st i j = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.eqSlot i j).SatisfiedBy a →
        ∃ l ∈ c, l.eval a = some true) := by
  constructor
  · -- implied soundness: four arms, each a bound copy through x = y
    intro l r hrun a hfit hcons
    unfold propEq at hrun
    split at hrun
    next _ _ _ _ mi Mi mj Mj hmi hMi hmj hMj =>
      rcases firstEvent_mem
          [narrowLo st i mj [negLe i (mj - 1), posLe j (mj - 1)],
           narrowHi st i Mj [posLe i Mj, negLe j Mj],
           narrowLo st j mi [negLe j (mi - 1), posLe i (mi - 1)],
           narrowHi st j Mi [posLe j Mi, negLe i Mi]]
          (.implied l r) hrun with hstable | hmem
      · exact absurd hstable (by intro hc; cases hc)
      · rcases List.mem_cons.mp hmem with harm1 | hrest1
        · -- arm 1: implied negLe i (mj-1); x = y ≥ mj
          obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm harm1)
          subst hl
          obtain ⟨x, y, hx, hy, hxy⟩ := eqSlot_views (st := st) a i j hview hfit hcons
          have hmjy : mj ≤ y := fits_min_bound hfit hmj hy
          rw [eval_negLe_iff]
          exact ⟨x, hx, by omega⟩
        · rcases List.mem_cons.mp hrest1 with harm2 | hrest2
          · -- arm 2: implied posLe i Mj; x = y ≤ Mj
            obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm harm2)
            subst hl
            obtain ⟨x, y, hx, hy, hxy⟩ := eqSlot_views (st := st) a i j hview hfit hcons
            have hyMj : y ≤ Mj := fits_max_bound hfit hMj hy
            rw [eval_posLe_iff]
            exact ⟨x, hx, by omega⟩
          · rcases List.mem_cons.mp hrest2 with harm3 | hrest3
            · -- arm 3: implied negLe j (mi-1); y = x ≥ mi
              obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm harm3)
              subst hl
              obtain ⟨x, y, hx, hy, hxy⟩ := eqSlot_views (st := st) a i j hview hfit hcons
              have hmix : mi ≤ x := fits_min_bound hfit hmi hx
              rw [eval_negLe_iff]
              exact ⟨y, hy, by omega⟩
            · -- arm 4: implied posLe j Mi; y = x ≤ Mi
              obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm
                (List.mem_singleton.mp hrest3))
              subst hl
              obtain ⟨x, y, hx, hy, hxy⟩ := eqSlot_views (st := st) a i j hview hfit hcons
              have hxMi : x ≤ Mi := fits_max_bound hfit hMi hx
              rw [eval_posLe_iff]
              exact ⟨y, hy, by omega⟩
    next => exact absurd hrun (by intro hc; simp at hc)
  · constructor
    · -- conflict soundness: the bounds contradict x = y at every
      -- fitting solution
      intro c hrun a hfit hcons
      unfold propEq at hrun
      split at hrun
      next _ _ _ _ mi Mi mj Mj hmi hMi hmj hMj =>
        rcases firstEvent_mem
            [narrowLo st i mj [negLe i (mj - 1), posLe j (mj - 1)],
             narrowHi st i Mj [posLe i Mj, negLe j Mj],
             narrowLo st j mi [negLe j (mi - 1), posLe i (mi - 1)],
             narrowHi st j Mi [posLe j Mi, negLe i Mi]]
            (.conflict c) hrun with hstable | hmem
        · exact absurd hstable (by intro hc; cases hc)
        · rcases List.mem_cons.mp hmem with harm1 | hrest1
          · -- arm 1 conflict: mx_i < mj; but x = y ≥ mj and x ≤ mx
            obtain ⟨mn, mx, hmn, hmx, hlt, _⟩ :=
              narrowLo_conflict_inv (Eq.symm harm1)
            obtain ⟨x, y, hx, hy, hxy⟩ := eqSlot_views (st := st) a i j hview hfit hcons
            have hmjy : mj ≤ y := fits_min_bound hfit hmj hy
            have hmxx : x ≤ mx := fits_max_bound hfit hmx hx
            omega
          · rcases List.mem_cons.mp hrest1 with harm2 | hrest2
            · -- arm 2 conflict: mn_i > Mj; but x = y ≤ Mj and x ≥ mn
              obtain ⟨mn, mx, hmn, hmx, hgt, _⟩ :=
                narrowHi_conflict_inv (Eq.symm harm2)
              obtain ⟨x, y, hx, hy, hxy⟩ := eqSlot_views (st := st) a i j hview hfit hcons
              have hyMj : y ≤ Mj := fits_max_bound hfit hMj hy
              have hmnx : mn ≤ x := fits_min_bound hfit hmn hx
              omega
            · rcases List.mem_cons.mp hrest2 with harm3 | hrest3
              · -- arm 3 conflict: mx_j < mi; but y = x ≥ mi and y ≤ mx
                obtain ⟨mn, mx, hmn, hmx, hlt, _⟩ :=
                  narrowLo_conflict_inv (Eq.symm harm3)
                obtain ⟨x, y, hx, hy, hxy⟩ := eqSlot_views (st := st) a i j hview hfit hcons
                have hmix : mi ≤ x := fits_min_bound hfit hmi hx
                have hmyy : y ≤ mx := fits_max_bound hfit hmx hy
                omega
              · -- arm 4 conflict: mn_j > Mi; but y = x ≤ Mi and y ≥ mn
                obtain ⟨mn, mx, hmn, hmx, hgt, _⟩ :=
                  narrowHi_conflict_inv (Eq.symm
                    (List.mem_singleton.mp hrest3))
                obtain ⟨x, y, hx, hy, hxy⟩ := eqSlot_views (st := st) a i j hview hfit hcons
                have hxMi : x ≤ Mi := fits_max_bound hfit hMi hx
                have hmny : mn ≤ y := fits_min_bound hfit hmn hy
                omega
      next => exact absurd hrun (by intro hc; simp at hc)
    · -- entitlement: each nogood is integer-valid under x = y at a
      -- fitting solution (the bounds pin the true literal)
      intro c hrun a hfit hcons
      unfold propEq at hrun
      split at hrun
      next _ _ _ _ mi Mi mj Mj hmi hMi hmj hMj =>
        rcases firstEvent_mem
            [narrowLo st i mj [negLe i (mj - 1), posLe j (mj - 1)],
             narrowHi st i Mj [posLe i Mj, negLe j Mj],
             narrowLo st j mi [negLe j (mi - 1), posLe i (mi - 1)],
             narrowHi st j Mi [posLe j Mi, negLe i Mi]]
            (.conflict c) hrun with hstable | hmem
        · exact absurd hstable (by intro hc; cases hc)
        · rcases List.mem_cons.mp hmem with harm1 | hrest1
          · obtain ⟨_, _, _, _, hlt, hcc⟩ :=
              narrowLo_conflict_inv (Eq.symm harm1)
            obtain ⟨x, y, hx, hy, hxy⟩ := eqSlot_views (st := st) a i j hview hfit hcons
            have hmjy : mj ≤ y := fits_min_bound hfit hmj hy
            refine ⟨negLe i (mj - 1), by rw [hcc]; exact List.mem_cons_self, ?_⟩
            rw [eval_negLe_iff]
            exact ⟨x, hx, by omega⟩
          · rcases List.mem_cons.mp hrest1 with harm2 | hrest2
            · obtain ⟨_, _, _, _, hgt, hcc⟩ :=
                narrowHi_conflict_inv (Eq.symm harm2)
              obtain ⟨x, y, hx, hy, hxy⟩ := eqSlot_views (st := st) a i j hview hfit hcons
              have hyMj : y ≤ Mj := fits_max_bound hfit hMj hy
              refine ⟨posLe i Mj, by rw [hcc]; exact List.mem_cons_self, ?_⟩
              rw [eval_posLe_iff]
              exact ⟨x, hx, by omega⟩
            · rcases List.mem_cons.mp hrest2 with harm3 | hrest3
              · obtain ⟨_, _, _, _, hlt, hcc⟩ :=
                  narrowLo_conflict_inv (Eq.symm harm3)
                obtain ⟨x, y, hx, hy, hxy⟩ := eqSlot_views (st := st) a i j hview hfit hcons
                have hmix : mi ≤ x := fits_min_bound hfit hmi hx
                refine ⟨negLe j (mi - 1), by rw [hcc]; exact List.mem_cons_self, ?_⟩
                rw [eval_negLe_iff]
                exact ⟨y, hy, by omega⟩
              · obtain ⟨_, _, _, _, hgt, hcc⟩ :=
                  narrowHi_conflict_inv (Eq.symm
                    (List.mem_singleton.mp hrest3))
                obtain ⟨x, y, hx, hy, hxy⟩ := eqSlot_views (st := st) a i j hview hfit hcons
                have hxMi : x ≤ Mi := fits_max_bound hfit hMi hx
                refine ⟨posLe j Mi, by rw [hcc]; exact List.mem_cons_self, ?_⟩
                rw [eval_posLe_iff]
                exact ⟨y, hy, by omega⟩
      next => exact absurd hrun (by intro hc; simp at hc)




/-! ## The state-domain view bridge and the PropSafeUniv packaging -/

/-- At a domain-coherent state over an int-viewed problem, every
    state-domain value has an integer view (each value is either a
    Boolean — viewed as 0/1 — or an original problem-domain value,
    by `fits_fold_original`). -/
theorem mem_getD : ∀ (doms : List (List Value)) (d : List Value),
    d ∈ doms → ∃ s, doms.getD s [] = d := by
  intro doms
  induction doms with
  | nil => intro d hd; cases hd
  | cons d0 rest ih =>
      intro d hd
      rcases List.mem_cons.mp hd with hd2 | hd2
      · rw [hd2]; exact ⟨0, rfl⟩
      · obtain ⟨s, hs⟩ := ih d hd2
        exact ⟨s + 1, by
          simp only [List.getD_cons_succ]
          exact hs⟩

/-- Out-of-range `getD` is the default. -/
theorem getD_default_of_ge : ∀ (doms : List (List Value))
    (s : Nat), ¬ s < doms.length → doms.getD s [] = [] := by
  intro doms s
  induction doms generalizing s with
  | nil => intro _; rfl
  | cons d0 rest ih =>
      intro h
      match s with
      | 0 => exact absurd (Nat.zero_lt_succ _) h
      | s2+1 =>
          have hs2 : ¬ s2 < rest.length := by
            intro hlt
            apply h
            simp only [List.length_cons]
            omega
          exact ih s2 hs2

theorem intViewedDoms_of_coherent {problem : Problem DomConstraint Unit}
    {st : State} (hview : IntViewedDoms problem.domains)
    (hcoh : DomainCoherent problem st) :
    IntViewedDoms st.domains := by
  intro d hd v hv
  -- d is at some position of st.domains
  obtain ⟨s, hs⟩ := mem_getD st.domains d hd
  -- the fold's value at s0=s is bool or original (fits_fold_original)
  have hfold : st.domains = st.trail.foldl
      (fun acc e => domOfLit acc e.literal) problem.domains := hcoh
  -- membership at the position (via the fold equation)
  have hvpos : v ∈ (st.trail.foldl
      (fun acc e => domOfLit acc e.literal) problem.domains).getD s [] := by
    rw [← hfold, hs]; exact hv
  have horig := fits_fold_original st.trail problem.domains s v hvpos
  rcases horig with ⟨b, hb⟩ | hmem
  · -- Boolean: viewed (intView of .bool is some)
    have hbool : Value.intView (Value.bool b) ≠ none := by
      cases b <;> decide
    rw [hb]
    exact hbool
  · -- original problem-domain value: viewed by IntViewedDoms
    -- v is in the original domain at position s; the original
    -- domain list at s IS problem.domains.getD s [], and its values
    -- are viewed
    -- the fold preserves length (domOfLit preserves length per step)
    have hlenfold : (st.trail.foldl
        (fun acc e => domOfLit acc e.literal) problem.domains).length
        = problem.domains.length := by
      have main : ∀ (tr : List TrailEntry)
          (doms : List (List Value)),
          (tr.foldl (fun acc e => domOfLit acc e.literal) doms).length
            = doms.length := by
        intro tr
        induction tr with
        | nil => intro _; rfl
        | cons e rest ih =>
            intro doms
            rw [List.foldl_cons]
            rw [ih (domOfLit doms e.literal)]
            exact domOfLit_length e.literal
      exact main st.trail problem.domains
    have hdlt : s < problem.domains.length := by
      have hlen : st.domains.length = problem.domains.length := by
        rw [hcoh]
        rw [← hlenfold]
      have hne : st.domains.getD s [] ≠ [] := by
        rw [hs]
        intro hc
        rw [hc] at hv
        exact absurd hv (by simp)
      by_cases hcon : s < st.domains.length
      · -- in range at the state: also in range at the problem (same
        -- length); the goal follows
        omega
      · exfalso
        have : st.domains.getD s [] = [] := getD_default_of_ge st.domains s hcon
        exact hne this
    -- getD of an in-range position IS the member list
    have hdorig : problem.domains.getD s [] ∈ problem.domains := by
      have hget : problem.domains.getD s [] = problem.domains[s] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hdlt]
        rfl
      rw [hget]
      exact List.getElem_mem hdlt
    exact hview _ hdorig v hmem


/-! ## The proved-propagator packaging -/

/-- The propagator of a constraint whose family soundness is proved
    (`leSlot`, `ltSlot`, `eqSlot`); `none` for the families whose
    proofs remain the documented expansion path (`plusSlot`,
    `neSlot`, `linLe`). -/
def propagatorOfProved : DomConstraint → Option Propagator
  | .leSlot i j => some { watches := [], run := fun st => propLe st i j }
  | .ltSlot i j => some { watches := [], run := fun st => propLt st i j }
  | .eqSlot i j => some { watches := [], run := fun st => propEq st i j }
  | _ => none

/-- Membership inversion for the proved registration. -/

theorem propagatorsOfProved_mem {dcs : List DomConstraint}
    {p : Propagator} (hp : p ∈ dcs.filterMap propagatorOfProved) :
    ∃ dc ∈ dcs, propagatorOfProved dc = some p := by
  induction dcs with
  | nil => cases hp
  | cons dc rest ih =>
      cases hpdc : propagatorOfProved dc with
      | none =>
          simp only [List.filterMap_cons, hpdc, Option.map_none] at hp
          obtain ⟨dc2, hdc2mem, hdc2⟩ := ih hp
          exact ⟨dc2, List.mem_cons_of_mem _ hdc2mem, hdc2⟩
      | some p0 =>
          simp only [List.filterMap_cons, hpdc, Option.map_some] at hp
          rcases List.mem_cons.mp hp with hp2 | hp2
          · rw [hp2]
            exact ⟨dc, List.mem_cons_self, hpdc⟩
          · obtain ⟨dc2, hdc2mem, hdc2⟩ := ih hp2
            exact ⟨dc2, List.mem_cons_of_mem _ hdc2mem, hdc2⟩

theorem propagatorOfProved_run {dc : DomConstraint} {p : Propagator}
    {st : State} {res : PropagationResult}
    (hprop : propagatorOfProved dc = some p)
    (hrun : p.run st = res) :
    (∃ i j, dc = .leSlot i j ∧ propLe st i j = res) ∨
    (∃ i j, dc = .ltSlot i j ∧ propLt st i j = res) ∨
    (∃ i j, dc = .eqSlot i j ∧ propEq st i j = res) := by
  match hdc : dc with
  | .leSlot i j =>
      simp only [propagatorOfProved] at hprop
      refine Or.inl ⟨i, j, rfl, ?_⟩
      have hp2 : p = { watches := [], run := fun st => propLe st i j } :=
        (Option.some.inj hprop).symm
      rw [hp2] at hrun
      exact hrun
  | .ltSlot i j =>
      simp only [propagatorOfProved] at hprop
      refine Or.inr (Or.inl ⟨i, j, rfl, ?_⟩)
      have hp2 : p = { watches := [], run := fun st => propLt st i j } :=
        (Option.some.inj hprop).symm
      rw [hp2] at hrun
      exact hrun
  | .eqSlot i j =>
      simp only [propagatorOfProved] at hprop
      refine Or.inr (Or.inr ⟨i, j, rfl, ?_⟩)
      have hp2 : p = { watches := [], run := fun st => propEq st i j } :=
        (Option.some.inj hprop).symm
      rw [hp2] at hrun
      exact hrun
  | .neSlot i j | .constEq i v | .plusSlot i j k
  | .leConstHi i c | .leConstLo i c | .allDiff is
  | .timesSlot i j k | .minSlot i j k | .maxSlot i j k | .absSlot i k2
  | .linEq coeffs is b | .linLe coeffs is b
  | .ltConstHi i c | .ltConstLo i c | .boolNotSlot i j
  | .boolAndSlot i j k | .boolOrSlot i j k =>
      exfalso
      simp only [propagatorOfProved] at hprop
      exact absurd hprop (by intro hc; cases hc)


/-- **PropSafeUniv for the proved-propagator list**: every implied
    literal is true at every represented solution and every conflict
    clause excludes every represented solution — at every
    domain-coherent state of an int-viewed problem (the engine's
    run invariant; `intViewedDoms_of_coherent` supplies the state's
    view from the problem's). -/
theorem propagatorsOfProved_safeUniv
    {problem : Problem DomConstraint Unit}
    (hview : IntViewedDoms problem.domains)
    {props : List Propagator}
    (hprops : ∀ p ∈ props, ∃ dc ∈ problem.constraints,
      propagatorOfProved dc = some p) :
    ∀ st, DomainCoherent problem st →
    PropSafe problem DomConstraint.SatisfiedBy props st := by
  intro st hcoh
  refine ⟨?_, ?_⟩
  · intro p hp l r hrun a ⟨hsol, hrep⟩
    obtain ⟨dc, hdc, hprop⟩ := hprops p hp
    rcases propagatorOfProved_run hprop hrun with
      ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, hdc2, hrun2⟩
    · rw [hdc2] at hdc
      exact propagatorOf_leSlot_implied (problem := problem)
        (i := i) (j := j) hdc hrun2 a hsol hrep
    · rw [hdc2] at hdc
      exact (propLt_safe st i j).1 l r hrun2 a hrep.1 (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      have hviewst := intViewedDoms_of_coherent hview hcoh
      exact (propEq_safe st i j hviewst).1 l r hrun2 a hrep.1
        (hsol.2 _ hdc)
  · intro p hp c hrun a ⟨hsol, hrep⟩
    obtain ⟨dc, hdc, hprop⟩ := hprops p hp
    rcases propagatorOfProved_run hprop hrun with
      ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, hdc2, hrun2⟩
    · rw [hdc2] at hdc
      exact propagatorOf_leSlot_conflict (problem := problem)
        (i := i) (j := j) hdc hrun2 a hsol hrep
    · rw [hdc2] at hdc
      intro hcsat
      obtain ⟨w, hw, hwe⟩ := hcsat
      exact (propLt_safe st i j).2.1 c hrun2 a hrep.1 (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      have hviewst := intViewedDoms_of_coherent hview hcoh
      intro hcsat
      obtain ⟨w, hw, hwe⟩ := hcsat
      exact (propEq_safe st i j hviewst).2.1 c hrun2 a hrep.1
        (hsol.2 _ hdc)

/-- **The relativized entitlement for the proved-propagator list**:
    every conflict clause carries a true literal at every solution
    that fits the state's domains (the shape
    `propagateLoop_conflict_entitled` consumes, under the state's
    SolvedBy). -/
theorem propagatorsOfProved_entitled
    {problem : Problem DomConstraint Unit}
    (hview : IntViewedDoms problem.domains)
    {props : List Propagator}
    (hprops : ∀ p ∈ props, ∃ dc ∈ problem.constraints,
      propagatorOfProved dc = some p) :
    ∀ (st : State), SolvedBy problem DomConstraint.SatisfiedBy st →
    DomainCoherent problem st →
    ∀ p ∈ props, ∀ (c : Clause), p.run st = .conflict c →
    ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
    ∃ l ∈ c, l.eval a = some true := by
  intro st hsol hcoh p hp c hrun a ha
  obtain ⟨dc, hdc, hprop⟩ := hprops p hp
  rcases propagatorOfProved_run hprop hrun with
    ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, hdc2, hrun2⟩
  · rw [hdc2] at hdc
    exact propagatorOf_leSlot_entitled (problem := problem)
      (i := i) (j := j) hdc hrun2 hsol a ha
  · rw [hdc2] at hdc
    exact (propLt_safe st i j).2.2 c hrun2 a (hsol a ha).1
      (ha.2 _ hdc)
  · rw [hdc2] at hdc
    have hviewst := intViewedDoms_of_coherent hview hcoh
    exact (propEq_safe st i j hviewst).2.2 c hrun2 a (hsol a ha).1
      (ha.2 _ hdc)

end LeanFzn.Solver.LCG




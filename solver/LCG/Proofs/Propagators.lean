/-
File: solver/LCG/Proofs/Propagators.lean

Purpose:
  Per-family propagator soundness for the real `propagatorsOf` list:
  `PropSafeUniv` (implied literals are true at every represented
  solution; conflict clauses exclude every represented solution) and
  the relativized entitlement (conflict clauses carry a true literal
  at every solution fitting the STATE's domains — the shape
  `propagateLoop_conflict_entitled` consumes) for the eleven
  registered families: `leSlot`, `ltSlot`, `eqSlot`, `neSlot`,
  `plusSlot`, `linLe`, plus the constant-bound and constant-equality
  families `leConstHi`, `leConstLo`, `ltConstHi`, `ltConstLo`,
  `constEq` (whose per-family packages live in ConstFamilies).

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
  - solver.LCG.Proofs.ConstFamilies: the constant-bound and
    constant-equality family packages, plus the shared
    narrowHi/narrowLo/firstEvent inversions.

DAG:
  LCG.Propagate + LCG.Proofs.Theory + LCG.Proofs.ConstFamilies
    -> LCG.Proofs.Propagators
    -> LCG.Certified (the front door with real propagators)
-/

import solver.LCG.Proofs.Theory
import solver.LCG.Propagate
import solver.LCG.Encoding
import solver.LCG.Proofs.ConstFamilies
import solver.LCG.Proofs.Fam.Bool
import solver.LCG.Proofs.Fam.Arith
import solver.LCG.Proofs.Fam.Lin
import solver.LCG.Proofs.Fam.Times
import solver.LCG.Proofs.Fam.AllDiff

namespace LeanFzn.Solver.LCG

open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Solver (DomConstraint)

/-! ## False-evaluation inversions for order literals -/

/-! ## The fitting-assignment slot view

The inversions and coherence bridges this file previously hosted
(`slotInt_of_int_read`, `fits_max_bound` / `fits_min_bound`,
`narrowHi_implied_inv` / `narrowLo_implied_inv`, `firstEvent_mem`)
now live in solver.LCG.Proofs.ConstFamilies (upstream), which this
module imports. -/

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
    (the seventeen registered families: `leSlot`, `ltSlot`, `eqSlot`,
    `neSlot`, `plusSlot`, `linLe`, the constant-bound and
    constant-equality families `leConstHi`, `leConstLo`, `ltConstHi`,
    `ltConstLo`, `constEq` from ConstFamilies, the Boolean families
    `boolNotSlot`, `boolAndSlot`, `boolOrSlot` from Fam/Bool, and the
    arithmetic families `minSlot`, `maxSlot`, `absSlot` from
    Fam/Arith). -/
def propagatorOfProved : DomConstraint → Option Propagator
  | .leSlot i j => some { watches := [], run := fun st => propLe st i j }
  | .ltSlot i j => some { watches := [], run := fun st => propLt st i j }
  | .eqSlot i j => some { watches := [], run := fun st => propEq st i j }
  | .neSlot i j => some { watches := [], run := fun st => propNe st i j }
  | .plusSlot i j k =>
      some { watches := [], run := fun st => propPlus st i j k }
  | .linLe coeffs is b =>
      some { watches := [], run := fun st =>
        propLinLe2 st coeffs is b }
  | .leConstHi i c =>
      some { watches := [], run := fun st => propLeConstHi st i c }
  | .leConstLo i c =>
      some { watches := [], run := fun st => propLeConstLo st i c }
  | .ltConstHi i c =>
      some { watches := [], run := fun st => propLtConstHi st i c }
  | .ltConstLo i c =>
      some { watches := [], run := fun st => propLtConstLo st i c }
  | .constEq i v =>
      some { watches := [], run := fun st => propConstEq st i v }
  | .boolNotSlot i j =>
      some { watches := [], run := fun st => propBoolNot st i j }
  | .boolAndSlot i j k =>
      some { watches := [], run := fun st => propBoolAnd st i j k }
  | .boolOrSlot i j k =>
      some { watches := [], run := fun st => propBoolOr st i j k }
  | .minSlot i j k =>
      some { watches := [], run := fun st => propMin st i j k }
  | .maxSlot i j k =>
      some { watches := [], run := fun st => propMax st i j k }
  | .absSlot i k =>
      some { watches := [], run := fun st => propAbs st i k }
  | .linEq coeffs is b =>
      some { watches := [], run := fun st =>
        propLinEq2 st coeffs is b }
  | .timesSlot i j k =>
      some { watches := [], run := fun st => propTimes st i j k }
  | .allDiff is =>
      some { watches := [], run := fun st =>
        propAllDiffLCG st is }

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
    (∃ i j, dc = .eqSlot i j ∧ propEq st i j = res) ∨
    (∃ i j, dc = .neSlot i j ∧ propNe st i j = res) ∨
    (∃ i j k, dc = .plusSlot i j k ∧ propPlus st i j k = res) ∨
    (∃ coeffs is b, dc = .linLe coeffs is b ∧
      propLinLe2 st coeffs is b = res) ∨
    (∃ i c, dc = .leConstHi i c ∧ propLeConstHi st i c = res) ∨
    (∃ i c, dc = .leConstLo i c ∧ propLeConstLo st i c = res) ∨
    (∃ i c, dc = .ltConstHi i c ∧ propLtConstHi st i c = res) ∨
    (∃ i c, dc = .ltConstLo i c ∧ propLtConstLo st i c = res) ∨
    (∃ i v, dc = .constEq i v ∧ propConstEq st i v = res) ∨
    (∃ i j, dc = .boolNotSlot i j ∧ propBoolNot st i j = res) ∨
    (∃ i j k, dc = .boolAndSlot i j k ∧ propBoolAnd st i j k = res) ∨
    (∃ i j k, dc = .boolOrSlot i j k ∧ propBoolOr st i j k = res) ∨
    (∃ i j k, dc = .minSlot i j k ∧ propMin st i j k = res) ∨
    (∃ i j k, dc = .maxSlot i j k ∧ propMax st i j k = res) ∨
    (∃ i k, dc = .absSlot i k ∧ propAbs st i k = res) ∨
    (∃ coeffs is b, dc = .linEq coeffs is b ∧
      propLinEq2 st coeffs is b = res) ∨
    (∃ i j k, dc = .timesSlot i j k ∧
      propTimes st i j k = res) ∨
    (∃ is, dc = .allDiff is ∧
      propAllDiffLCG st is = res) := by
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
      refine Or.inr (Or.inr (Or.inl ⟨i, j, rfl, ?_⟩))
      have hp2 : p = { watches := [], run := fun st => propEq st i j } :=
        (Option.some.inj hprop).symm
      rw [hp2] at hrun
      exact hrun
  | .neSlot i j =>
      simp only [propagatorOfProved] at hprop
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨i, j, rfl, ?_⟩)))
      have hp2 : p = { watches := [], run := fun st => propNe st i j } :=
        (Option.some.inj hprop).symm
      rw [hp2] at hrun
      exact hrun
  | .plusSlot i j k =>
      simp only [propagatorOfProved] at hprop
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, j, k, rfl, ?_⟩))))
      have hp2 : p = { watches := [], run := fun st => propPlus st i j k } :=
        (Option.some.inj hprop).symm
      rw [hp2] at hrun
      exact hrun
  | .linLe coeffs is b =>
      simp only [propagatorOfProved] at hprop
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨coeffs, is, b, rfl, ?_⟩)))))
      rw [(Option.some.inj hprop).symm] at hrun
      exact hrun
  | .leConstHi i c =>
      simp only [propagatorOfProved] at hprop
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨i, c, rfl, ?_⟩))))))
      rw [(Option.some.inj hprop).symm] at hrun
      exact hrun
  | .leConstLo i c =>
      simp only [propagatorOfProved] at hprop
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl ⟨i, c, rfl, ?_⟩)))))))
      rw [(Option.some.inj hprop).symm] at hrun
      exact hrun
  | .ltConstHi i c =>
      simp only [propagatorOfProved] at hprop
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl ⟨i, c, rfl, ?_⟩))))))))
      rw [(Option.some.inj hprop).symm] at hrun
      exact hrun
  | .ltConstLo i c =>
      simp only [propagatorOfProved] at hprop
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl ⟨i, c, rfl, ?_⟩)))))))))
      rw [(Option.some.inj hprop).symm] at hrun
      exact hrun
  | .constEq i v =>
      simp only [propagatorOfProved] at hprop
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, v, rfl, ?_⟩))))))))))
      rw [(Option.some.inj hprop).symm] at hrun
      exact hrun
  | .boolNotSlot i j =>
      simp only [propagatorOfProved] at hprop
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, j, rfl, ?_⟩)))))))))))
      rw [(Option.some.inj hprop).symm] at hrun
      exact hrun
  | .boolAndSlot i j k =>
      simp only [propagatorOfProved] at hprop
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, j, k, rfl, ?_⟩))))))))))))
      rw [(Option.some.inj hprop).symm] at hrun
      exact hrun
  | .boolOrSlot i j k =>
      simp only [propagatorOfProved] at hprop
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, j, k, rfl, ?_⟩)))))))))))))
      rw [(Option.some.inj hprop).symm] at hrun
      exact hrun
  | .minSlot i j k =>
      simp only [propagatorOfProved] at hprop
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, j, k, rfl, ?_⟩))))))))))))))
      rw [(Option.some.inj hprop).symm] at hrun
      exact hrun
  | .maxSlot i j k =>
      simp only [propagatorOfProved] at hprop
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, j, k, rfl, ?_⟩)))))))))))))))
      rw [(Option.some.inj hprop).symm] at hrun
      exact hrun
  | .absSlot i k =>
      simp only [propagatorOfProved] at hprop
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, k, rfl, ?_⟩))))))))))))))))
      rw [(Option.some.inj hprop).symm] at hrun
      exact hrun
  | .linEq coeffs is b =>
      simp only [propagatorOfProved] at hprop
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨coeffs, is, b, rfl, ?_⟩)))))))))))))))))
      rw [(Option.some.inj hprop).symm] at hrun
      exact hrun
  | .timesSlot i j k =>
      simp only [propagatorOfProved] at hprop
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, j, k, rfl, ?_⟩))))))))))))))))))
      rw [(Option.some.inj hprop).symm] at hrun
      exact hrun
  | .allDiff is =>
      simp only [propagatorOfProved] at hprop
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨is, rfl, ?_⟩)))))))))))))))))))
      rw [(Option.some.inj hprop).symm] at hrun
      exact hrun


/-! ## propPlus soundness: `x + y = z` over slots i j k -/

theorem plusSlot_views (a : Assignment) (i j k : Nat)
    (h : (DomConstraint.plusSlot i j k).SatisfiedBy a) :
    ∃ x y z, slotInt a i = some x ∧ slotInt a j = some y ∧
      slotInt a k = some z := by
  obtain ⟨p, q, r, hpi, hqj, hzk, _⟩ := h
  exact ⟨p, q, r, slotInt_of_int_read hpi, slotInt_of_int_read hqj,
    slotInt_of_int_read hzk⟩

/-- The per-arm arithmetic pack for propPlus at a fitting solution:
    the equation and the six domain bounds. -/
theorem plusSlot_pack {st : State} {a : Assignment} {i j k : Nat}
    (hfit : Core.Assignment.Fits st.domains a)
    (hcons : (DomConstraint.plusSlot i j k).SatisfiedBy a)
    {xi' xi yj' yj zk' zk : Int}
    (hxi' : domMinI (st.domains.getD i []) = some xi')
    (hxi : domMaxI (st.domains.getD i []) = some xi)
    (hyj' : domMinI (st.domains.getD j []) = some yj')
    (hyj : domMaxI (st.domains.getD j []) = some yj)
    (hzk' : domMinI (st.domains.getD k []) = some zk')
    (hzk : domMaxI (st.domains.getD k []) = some zk) :
    ∃ x y z,
      slotInt a i = some x ∧ slotInt a j = some y ∧
      slotInt a k = some z ∧
      x + y = z ∧ xi' ≤ x ∧ x ≤ xi ∧ yj' ≤ y ∧ y ≤ yj ∧
      zk' ≤ z ∧ z ≤ zk := by
  obtain ⟨x, y, z, hx, hy, hz⟩ := plusSlot_views a i j k hcons
  refine ⟨x, y, z, hx, hy, hz, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact plusSlot_sem hcons hx hy hz
  · exact fits_min_bound hfit hxi' hx
  · exact fits_max_bound hfit hxi hx
  · exact fits_min_bound hfit hyj' hy
  · exact fits_max_bound hfit hyj hy
  · exact fits_min_bound hfit hzk' hz
  · exact fits_max_bound hfit hzk hz

theorem propPlus_safe (st : State) (i j k : Nat) :
    (∀ l r, propPlus st i j k = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.plusSlot i j k).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ c, propPlus st i j k = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.plusSlot i j k).SatisfiedBy a → False) ∧
    (∀ c, propPlus st i j k = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.plusSlot i j k).SatisfiedBy a →
        ∃ l ∈ c, l.eval a = some true) := by
  constructor
  · intro l r hrun a hfit hcons
    unfold propPlus at hrun
    split at hrun
    next _ _ _ _ _ _ xi' xi yj' yj zk' zk hxi' hxi hyj' hyj hzk' hzk =>
      rcases firstEvent_mem
          [narrowLo st i (zk' - yj) [negLe i (zk' - yj - 1), posLe k (zk' - 1), negLe j yj],
           narrowHi st i (zk - yj') [posLe i (zk - yj'), negLe k zk, posLe j (yj' - 1)],
           narrowLo st j (zk' - xi) [negLe j (zk' - xi - 1), posLe k (zk' - 1), negLe i xi],
           narrowHi st j (zk - xi') [posLe j (zk - xi'), negLe k zk, posLe i (xi' - 1)],
           narrowLo st k (xi' + yj') [negLe k (xi' + yj' - 1), posLe i (xi' - 1), posLe j (yj' - 1)],
           narrowHi st k (xi + yj) [posLe k (xi + yj), negLe i xi, negLe j yj]]
          (.implied l r) hrun with hstable | hmem
      · exact absurd hstable (by intro hc; cases hc)
      · obtain ⟨x, y, z, hx, hy, hz, heq, h1, h2, h3, h4, h5, h6⟩ :=
          plusSlot_pack hfit hcons hxi' hxi hyj' hyj hzk' hzk
        rcases List.mem_cons.mp hmem with h1' | hrest1
        · obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm h1')
          subst hl; rw [eval_negLe_iff]
          exact ⟨x, hx, by omega⟩
        · rcases List.mem_cons.mp hrest1 with h2' | hrest2
          · obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm h2')
            subst hl; rw [eval_posLe_iff]
            exact ⟨x, hx, by omega⟩
          · rcases List.mem_cons.mp hrest2 with h3' | hrest3
            · obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm h3')
              subst hl; rw [eval_negLe_iff]
              exact ⟨y, hy, by omega⟩
            · rcases List.mem_cons.mp hrest3 with h4' | hrest4
              · obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm h4')
                subst hl; rw [eval_posLe_iff]
                exact ⟨y, hy, by omega⟩
              · rcases List.mem_cons.mp hrest4 with h5' | hrest5
                · obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm h5')
                  subst hl; rw [eval_negLe_iff]
                  exact ⟨z, hz, by omega⟩
                · obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm
                    (List.mem_singleton.mp hrest5))
                  subst hl; rw [eval_posLe_iff]
                  exact ⟨z, hz, by omega⟩
    next => exact absurd hrun (by intro hc; simp at hc)
  · constructor
    · intro c hrun a hfit hcons
      unfold propPlus at hrun
      split at hrun
      next _ _ _ _ _ _ xi' xi yj' yj zk' zk hxi' hxi hyj' hyj hzk' hzk =>
        rcases firstEvent_mem
            [narrowLo st i (zk' - yj) [negLe i (zk' - yj - 1), posLe k (zk' - 1), negLe j yj],
             narrowHi st i (zk - yj') [posLe i (zk - yj'), negLe k zk, posLe j (yj' - 1)],
             narrowLo st j (zk' - xi) [negLe j (zk' - xi - 1), posLe k (zk' - 1), negLe i xi],
             narrowHi st j (zk - xi') [posLe j (zk - xi'), negLe k zk, posLe i (xi' - 1)],
             narrowLo st k (xi' + yj') [negLe k (xi' + yj' - 1), posLe i (xi' - 1), posLe j (yj' - 1)],
             narrowHi st k (xi + yj) [posLe k (xi + yj), negLe i xi, negLe j yj]]
            (.conflict c) hrun with hstable | hmem
        · exact absurd hstable (by intro hc; cases hc)
        · obtain ⟨x, y, z, hx, hy, hz, heq, b1, b2, b3, b4, b5, b6⟩ :=
            plusSlot_pack hfit hcons hxi' hxi hyj' hyj hzk' hzk
          rcases List.mem_cons.mp hmem with h1' | hrest1
          · obtain ⟨mn, mx, hmn, hmx, hlt, _⟩ :=
              narrowLo_conflict_inv (Eq.symm h1')
            have hmnx : mn ≤ x := fits_min_bound hfit hmn hx
            have hmxy : x ≤ mx := fits_max_bound hfit hmx hx
            omega
          · rcases List.mem_cons.mp hrest1 with h2' | hrest2
            · obtain ⟨mn, mx, hmn, hmx, hgt, _⟩ :=
                narrowHi_conflict_inv (Eq.symm h2')
              have hmnx : mn ≤ x := fits_min_bound hfit hmn hx
              have hmxy : x ≤ mx := fits_max_bound hfit hmx hx
              omega
            · rcases List.mem_cons.mp hrest2 with h3' | hrest3
              · obtain ⟨mn, mx, hmn, hmx, hlt, _⟩ :=
                  narrowLo_conflict_inv (Eq.symm h3')
                have hmny : mn ≤ y := fits_min_bound hfit hmn hy
                have hmxy : y ≤ mx := fits_max_bound hfit hmx hy
                omega
              · rcases List.mem_cons.mp hrest3 with h4' | hrest4
                · obtain ⟨mn, mx, hmn, hmx, hgt, _⟩ :=
                    narrowHi_conflict_inv (Eq.symm h4')
                  have hmny : mn ≤ y := fits_min_bound hfit hmn hy
                  have hmxy : y ≤ mx := fits_max_bound hfit hmx hy
                  omega
                · rcases List.mem_cons.mp hrest4 with h5' | hrest5
                  · obtain ⟨mn, mx, hmn, hmx, hlt, _⟩ :=
                      narrowLo_conflict_inv (Eq.symm h5')
                    have hmnz : mn ≤ z := fits_min_bound hfit hmn hz
                    have hmxz : z ≤ mx := fits_max_bound hfit hmx hz
                    omega
                  · obtain ⟨mn, mx, hmn, hmx, hgt, _⟩ :=
                      narrowHi_conflict_inv (Eq.symm
                        (List.mem_singleton.mp hrest5))
                    have hmnz : mn ≤ z := fits_min_bound hfit hmn hz
                    have hmxz : z ≤ mx := fits_max_bound hfit hmx hz
                    omega
      next => exact absurd hrun (by intro hc; simp at hc)
    · intro c hrun a hfit hcons
      unfold propPlus at hrun
      split at hrun
      next _ _ _ _ _ _ xi' xi yj' yj zk' zk hxi' hxi hyj' hyj hzk' hzk =>
        rcases firstEvent_mem
            [narrowLo st i (zk' - yj) [negLe i (zk' - yj - 1), posLe k (zk' - 1), negLe j yj],
             narrowHi st i (zk - yj') [posLe i (zk - yj'), negLe k zk, posLe j (yj' - 1)],
             narrowLo st j (zk' - xi) [negLe j (zk' - xi - 1), posLe k (zk' - 1), negLe i xi],
             narrowHi st j (zk - xi') [posLe j (zk - xi'), negLe k zk, posLe i (xi' - 1)],
             narrowLo st k (xi' + yj') [negLe k (xi' + yj' - 1), posLe i (xi' - 1), posLe j (yj' - 1)],
             narrowHi st k (xi + yj) [posLe k (xi + yj), negLe i xi, negLe j yj]]
            (.conflict c) hrun with hstable | hmem
        · exact absurd hstable (by intro hc; cases hc)
        · obtain ⟨x, y, z, hx, hy, hz, heq, b1, b2, b3, b4, b5, b6⟩ :=
            plusSlot_pack hfit hcons hxi' hxi hyj' hyj hzk' hzk
          rcases List.mem_cons.mp hmem with h1' | hrest1
          · obtain ⟨_, _, _, _, hlt, hcc⟩ :=
              narrowLo_conflict_inv (Eq.symm h1')
            exact ⟨negLe i (zk' - yj - 1), by
              rw [hcc]; exact List.mem_cons_self, by
              rw [eval_negLe_iff]; exact ⟨x, hx, by omega⟩⟩
          · rcases List.mem_cons.mp hrest1 with h2' | hrest2
            · obtain ⟨_, _, _, _, hgt, hcc⟩ :=
                narrowHi_conflict_inv (Eq.symm h2')
              exact ⟨posLe i (zk - yj'), by
                rw [hcc]; exact List.mem_cons_self, by
                rw [eval_posLe_iff]; exact ⟨x, hx, by omega⟩⟩
            · rcases List.mem_cons.mp hrest2 with h3' | hrest3
              · obtain ⟨_, _, _, _, hlt, hcc⟩ :=
                  narrowLo_conflict_inv (Eq.symm h3')
                exact ⟨negLe j (zk' - xi - 1), by
                  rw [hcc]; exact List.mem_cons_self, by
                  rw [eval_negLe_iff]; exact ⟨y, hy, by omega⟩⟩
              · rcases List.mem_cons.mp hrest3 with h4' | hrest4
                · obtain ⟨_, _, _, _, hgt, hcc⟩ :=
                    narrowHi_conflict_inv (Eq.symm h4')
                  exact ⟨posLe j (zk - xi'), by
                    rw [hcc]; exact List.mem_cons_self, by
                    rw [eval_posLe_iff]; exact ⟨y, hy, by omega⟩⟩
                · rcases List.mem_cons.mp hrest4 with h5' | hrest5
                  · obtain ⟨_, _, _, _, hlt, hcc⟩ :=
                      narrowLo_conflict_inv (Eq.symm h5')
                    exact ⟨negLe k (xi' + yj' - 1), by
                      rw [hcc]; exact List.mem_cons_self, by
                      rw [eval_negLe_iff]; exact ⟨z, hz, by omega⟩⟩
                  · obtain ⟨_, _, _, _, hgt, hcc⟩ :=
                      narrowHi_conflict_inv (Eq.symm
                        (List.mem_singleton.mp hrest5))
                    exact ⟨posLe k (xi + yj), by
                      rw [hcc]; exact List.mem_cons_self, by
                      rw [eval_posLe_iff]; exact ⟨z, hz, by omega⟩⟩
      next => exact absurd hrun (by intro hc; simp at hc)


/-! ## linLe arithmetic infrastructure -/

theorem sweep_inv {f : Nat → Int → List (Int × Nat) → PropagationResult}
    {coeffs : List Int} {is : List Nat}
    {ps : List ((Int × Nat) × Nat)} {idx : Nat} {res : PropagationResult}
    (h : propLinLe.sweep coeffs is f ps idx = res) :
    res = .stable ∨ ∃ m c i,
      ((c, m), i) ∈ ps ∧
      res = f m c ((((coeffs.zip is).zipIdx).filter (fun p => p.2 != i)).map (·.1)) := by
  induction ps generalizing idx with
  | nil =>
      have h2 : propLinLe.sweep coeffs is f [] idx = .stable := rfl
      rw [h2] at h
      left
      exact h.symm
  | cons entry ps' ih =>
      obtain ⟨p, i⟩ := entry
      obtain ⟨c, m⟩ := p
      have hrw : propLinLe.sweep coeffs is f (((c, m), i) :: ps') idx =
        (match f m c ((((coeffs.zip is).zipIdx).filter (fun p => p.2 != i)).map (·.1)) with
         | .stable => propLinLe.sweep coeffs is f ps' (idx + 1)
         | r => r) := rfl
      rw [hrw] at h
      cases hf : f m c ((((coeffs.zip is).zipIdx).filter (fun p => p.2 != i)).map (·.1)) with
      | stable =>
          rw [hf] at h
          simp only [] at h
          rcases ih (idx := idx + 1) h with h1 | ⟨m2, c2, i2, hmem, hres⟩
          · exact Or.inl h1
          · exact Or.inr ⟨m2, c2, i2, List.mem_cons_of_mem _ hmem, hres⟩
      | implied l r =>
          rw [hf] at h
          exact Or.inr ⟨m, c, i, List.mem_cons_self, by rw [hf]; exact h.symm⟩
      | conflict c2 =>
          rw [hf] at h
          exact Or.inr ⟨m, c, i, List.mem_cons_self, by rw [hf]; exact h.symm⟩

/-! ### viewed domain membership -/

theorem min_contrib_le {st : State} {a : Assignment} {t : Nat}
    {ct mn mx : Int}
    (hfit : Assignment.Fits st.domains a)
    (hmn : domMinI (st.domains.getD t []) = some mn)
    (hmx : domMaxI (st.domains.getD t []) = some mx)
    {xt : Int} (hxt : slotInt a t = some xt) :
    (if ct ≥ 0 then ct * mn else ct * mx) ≤ ct * xt := by
  have h1 : mn ≤ xt := fits_min_bound hfit hmn hxt
  have h2 : xt ≤ mx := fits_max_bound hfit hmx hxt
  by_cases hct : ct ≥ 0
  · simp only [if_pos hct]
    exact Int.mul_le_mul_of_nonneg_left h1 hct
  · have hct2 : ct ≤ 0 := by omega
    simp only [if_neg (by omega : ¬ ct ≥ 0)]
    exact Int.mul_comm ct xt ▸ Int.mul_comm ct mx ▸
      Int.mul_le_mul_of_nonpos_right h2 hct2


theorem viewed_mem_of_mem {d : List Value} {v : Value} {i : Int}
    (hmem : v ∈ d) (hvi : Value.intView v = some i) :
    i ∈ domInts d := by
  induction d with
  | nil => cases hmem
  | cons w rest ih =>
      rcases List.mem_cons.mp hmem with rfl | hrest
      · cases v with
        | int j =>
            rw [Value.intView] at hvi
            have hij : j = i := Option.some.inj hvi
            rw [← hij]
            exact List.mem_cons_self
        | bool b =>
            rw [Value.intView] at hvi
            cases b with
            | true =>
                rw [if_pos rfl] at hvi
                have h1 : (1 : Int) = i := Option.some.inj hvi
                rw [← h1]
                exact List.mem_cons_self
            | false =>
                rw [if_neg (by simp)] at hvi
                have h0 : (0 : Int) = i := Option.some.inj hvi
                rw [← h0]
                exact List.mem_cons_self
        | setOfInt s =>
            have hnone : (Value.setOfInt s).intView = none := rfl
            rw [hnone] at hvi
            exact absurd hvi (by intro hc; cases hc)
        | array xs =>
            have hnone : (Value.array xs).intView = none := rfl
            rw [hnone] at hvi
            exact absurd hvi (by intro hc; cases hc)
      · -- tail: the cons cases reduce to filterMap-cons equations
        -- by the per-constructor shows that worked above
        match hw : w with
        | .int j2 =>
            show i ∈ domInts (Value.int j2 :: rest)
            exact List.mem_cons_of_mem _ (ih hrest)
        | .bool b2 =>
            show i ∈ domInts (Value.bool b2 :: rest)
            exact List.mem_cons_of_mem _ (ih hrest)
        | .setOfInt s2 =>
            show i ∈ List.filterMap (fun v =>
              match v with
              | .int i2 => some i2
              | .bool b => some (if b then 1 else 0)
              | _ => none) (Value.setOfInt s2 :: rest)
            rw [List.filterMap_cons]
            exact ih hrest
        | .array as2 =>
            show i ∈ List.filterMap (fun v =>
              match v with
              | .int i2 => some i2
              | .bool b => some (if b then 1 else 0)
              | _ => none) (Value.array as2 :: rest)
            rw [List.filterMap_cons]
            exact ih hrest

/-! ## propNe soundness: `x ≠ y` over slots i j -/

/-! ### eqB inversion lemmas -/

theorem list_ext' {xs ys : List Int}
    (hlen : xs.length = ys.length)
    (hzip : ∀ a b, (a, b) ∈ xs.zip ys → a = b) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons y yt => simp at hlen
  | cons x xt ih =>
      cases ys with
      | nil => simp at hlen
      | cons y yt =>
          have hxy : x = y := hzip x y (by simp)
          have hlen2 : xt.length = yt.length := by
            simp at hlen; omega
          have hzip2 : ∀ a b, (a, b) ∈ xt.zip yt → a = b := by
            intro a b hab
            exact hzip a b (by
              simp only [List.zip_cons_cons]
              exact List.mem_cons_of_mem _ hab)
          rw [hxy, ih hlen2 hzip2]

theorem IntSetValue_eqB_true {s t : IntSetValue}
    (h : s.eqB t = true) : s = t := by
  match s, t with
  | .enumeration xs, .enumeration ys =>
      simp only [IntSetValue.eqB, Bool.and_eq_true] at h
      obtain ⟨h1, hall⟩ := h
      simp only [List.all_eq_true] at hall
      have : xs = ys := by
        refine list_ext' (hlen := by simpa using h1) ?_
        intro a b hab
        have := hall (a, b) hab
        simpa using this
      rw [this]
  | .interval lo hi, .interval lo' hi' =>
      simp only [IntSetValue.eqB, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1, h.2]
  | .enumeration _, .interval _ _ => exact absurd h (by
      simp [IntSetValue.eqB])
  | .interval _ _, .enumeration _ => exact absurd h (by
      simp [IntSetValue.eqB])

mutual
theorem Value_eqB_true {x y : Value} (h : x.eqB y = true) :
    x = y := by
  match x, y with
  | .bool a, .bool b => simp only [Value.eqB, beq_iff_eq] at h; rw [h]
  | .int a, .int b => simp only [Value.eqB, beq_iff_eq] at h; rw [h]
  | .setOfInt a, .setOfInt b =>
      have := IntSetValue_eqB_true h; rw [this]
  | .array xs, .array ys =>
      have := valuesEqB_true h; rw [this]
  | .bool _, .int _ => exact absurd h (by simp [Value.eqB])
  | .bool _, .setOfInt _ => exact absurd h (by simp [Value.eqB])
  | .bool _, .array _ => exact absurd h (by simp [Value.eqB])
  | .int _, .bool _ => exact absurd h (by simp [Value.eqB])
  | .int _, .setOfInt _ => exact absurd h (by simp [Value.eqB])
  | .int _, .array _ => exact absurd h (by simp [Value.eqB])
  | .setOfInt _, .bool _ => exact absurd h (by simp [Value.eqB])
  | .setOfInt _, .int _ => exact absurd h (by simp [Value.eqB])
  | .setOfInt _, .array _ => exact absurd h (by simp [Value.eqB])
  | .array _, .bool _ => exact absurd h (by simp [Value.eqB])
  | .array _, .int _ => exact absurd h (by simp [Value.eqB])
  | .array _, .setOfInt _ => exact absurd h (by simp [Value.eqB])

theorem valuesEqB_true {xs ys : List Value}
    (h : valuesEqB xs ys = true) : xs = ys := by
  match xs, ys with
  | [], [] => rfl
  | x :: xt, y :: yt =>
      simp only [valuesEqB, Bool.and_eq_true] at h
      rw [Value_eqB_true h.1, valuesEqB_true h.2]
  | [], _ :: _ => exact absurd h (by simp [valuesEqB])
  | _ :: _, [] => exact absurd h (by simp [valuesEqB])
end

/-! ### Domain singleton helpers -/

theorem domSingleton_cons (v : Value) :
    domSingletonI [v] = Value.intView v := by
  cases v <;> rfl

theorem domSingleton_nil : domSingletonI ([] : List Value) = none := rfl

theorem domSingleton_cons2 (v v2 : Value) (rest : List Value) :
    domSingletonI (v :: v2 :: rest) = none := by
  cases v <;> cases v2 <;> cases rest <;> rfl

/-- `domSingletonI d = some c` forces `d` to be the singleton whose
    value views to `c`. -/
theorem domSingleton_inv {d : List Value} {c : Int}
    (h : domSingletonI d = some c) : ∃ v, d = [v] ∧
      Value.intView v = some c := by
  match hd : d with
  | [] => rw [domSingleton_nil] at h; cases h
  | [v] =>
      rw [domSingleton_cons] at h
      cases hvv : Value.intView v with
      | none => rw [hvv] at h; cases h
      | some c2 =>
          have hc2 : c2 = c := Option.some.inj (hvv.symm.trans h)
          rw [hc2] at hvv
          exact ⟨v, rfl, hvv⟩
  | v :: v2 :: rest =>
      rw [domSingleton_cons2] at h; cases h

theorem lt_of_getD_ne : ∀ (doms : List (List Value))
    (s : Nat), doms.getD s [] ≠ [] → s < doms.length := by
  intro doms s h
  match hd : doms with
  | [] => exact absurd h (by simp [List.getD])
  | d0 :: rest =>
      match s with
      | 0 => exact Nat.zero_lt_succ _
      | s2+1 =>
          have hc2 : rest.getD s2 [] ≠ [] := by
            intro hc
            apply h
            have hstep : (d0 :: rest).getD (s2+1) [] = rest.getD s2 [] := rfl
            rw [hstep]
            exact hc
          exact Nat.succ_lt_succ (lt_of_getD_ne rest s2 hc2)

/-- A fitting read in a singleton domain IS the singleton's value. -/
theorem fits_singleton_read {st : State} {a : Assignment} {s : Nat}
    {v : Value} (hsingle : st.domains.getD s [] = [v])
    (hfit : Core.Assignment.Fits st.domains a) :
    a[s]? = some v := by
  have hlen : a.length = st.domains.length := hfit.1
  have hne : st.domains.getD s [] ≠ [] := by
    rw [hsingle]; intro hc; exact absurd hc (by simp)
  have hs : s < st.domains.length := lt_of_getD_ne st.domains s hne
  have hget : st.domains.getD s [] = st.domains[s] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  have hmem : ∀ w, a[s]? = some w →
      w ∈ st.domains.getD s [] := hfit.2 s
  cases hr : a[s]? with
  | none =>
      exfalso
      have hs2 : s < a.length := by omega
      have hle : a.length ≤ s := by
        rw [List.getElem?_eq_none_iff] at hr; exact hr
      omega
  | some w =>
      have hwm : w ∈ st.domains[s] := by
        have hmemw := hmem w hr
        rw [hget] at hmemw
        exact hmemw
      rw [← hget, hsingle] at hwm
      rcases List.mem_cons.mp hwm with hwv | hnil
      · rw [hwv]
      · exact absurd hnil (by simp)

/-- The getD-to-membership bridge: a value read out of `getD`
    belongs to some domain list. -/
theorem exists_mem_of_getD : ∀ (doms : List (List Value)) (j : Nat)
    (v : Value), v ∈ doms.getD j [] → ∃ d ∈ doms, v ∈ d := by
  intro doms
  induction doms with
  | nil => intro j v hv; cases hv
  | cons d0 rest ih =>
      intro j v hv
      match j with
      | 0 => exact ⟨d0, List.mem_cons_self, hv⟩
      | j' + 1 =>
          rw [List.getD_cons_succ] at hv
          obtain ⟨d, hd, hvd⟩ := ih j' v hv
          exact ⟨d, List.mem_cons_of_mem _ hd, hvd⟩

/-- `propNe`'s implied emissions are exactly the two value-removal
    arms: one side a singleton viewing to `c`, the other side
    containing the raw singleton under the raw-view gate. -/
theorem propNe_implied_inv {st : State} {i j : Nat} {l : Literal}
    {r : Reason} (hrun : propNe st i j = .implied l r) :
    (∃ x c, st.domains.getD i [] = [x] ∧
        l = posNe j c ∧ r = { clause :=
          [posNe j c, posLe i (c - 1), negLe i c,
            posBool i (decide (c = 1)), posBool j (decide (c = 1))] } ∧
        domSingletonI [x] = some c ∧ valueMemB x (st.domains.getD j []) ∧
        domNeGate x c (st.domains.getD j [])) ∨
    (∃ y c, st.domains.getD j [] = [y] ∧
        l = posNe i c ∧ r = { clause :=
          [posNe i c, posLe j (c - 1), negLe j c,
            posBool j (decide (c = 1)), posBool i (decide (c = 1))] } ∧
        domSingletonI [y] = some c ∧ valueMemB y (st.domains.getD i []) ∧
        domNeGate y c (st.domains.getD i [])) := by
  unfold propNe at hrun
  split at hrun
  · -- both singletons: never implied
    split at hrun
    · exact absurd hrun (by simp)
    · exact absurd hrun (by simp)
  · -- i singleton, j multi-value: the value-removal arm
    rename_i _ _ x hdi hnsingle
    split at hrun
    · next c hc =>
        split at hrun
        · rename_i hcond
          injection hrun with hlit hreason
          have ⟨hmem, hgate⟩ := (Bool.and_eq_true _ _).mp hcond
          exact Or.inl ⟨x, c, hdi, hlit.symm, hreason.symm, hc,
            hmem, hgate⟩
        · exact absurd hrun (by simp)
    · exact absurd hrun (by simp)
  · -- j singleton, i multi-value: the symmetric arm
    rename_i _ _ y hdj hnsingle
    split at hrun
    · next c hc =>
        split at hrun
        · rename_i hcond
          injection hrun with hlit hreason
          have ⟨hmem, hgate⟩ := (Bool.and_eq_true _ _).mp hcond
          exact Or.inr ⟨y, c, hdj, hlit.symm, hreason.symm, hc,
            hmem, hgate⟩
        · exact absurd hrun (by simp)
    · exact absurd hrun (by simp)
  · -- both multi-value: never implied
    exact absurd hrun (by simp)

/-- `propNe`'s conflict reports come only from the both-singleton
    raw-equal arm, with the EMPTY clause. -/
theorem propNe_conflict_inv {st : State} {i j : Nat}
    {c : Clause} (hrun : propNe st i j = .conflict c) :
    ∃ x y, st.domains.getD i [] = [x] ∧ st.domains.getD j [] = [y] ∧
      x.eqB y = true ∧ c = [] := by
  unfold propNe at hrun
  split at hrun
  · split at hrun
    · rename_i x y hx hy hcond
      refine ⟨x, y, hx, hy, hcond, ?_⟩
      injection hrun with hc2
      cases hc2
      rfl
    · exact absurd hrun (by simp)
  · split at hrun
    · split at hrun
      · exact absurd hrun (by simp)
      · exact absurd hrun (by simp)
    · exact absurd hrun (by simp)
  · split at hrun
    · split at hrun
      · exact absurd hrun (by simp)
      · exact absurd hrun (by simp)
    · exact absurd hrun (by simp)
  · exact absurd hrun (by simp)

/-- THE IMPLIED-TRUTH STEP for the value-removal arm: a fitting
    solution of the raw `neSlot` whose other-side read views to the
    removed value reads the PINNED raw value there (the gate forces
    every domain value viewing to `c` to BE `x` raw), so the pinned
    slot and the other slot read raw-equal — contradicting the
    disequality. Hence the read's view differs from `c`: the posNe
    literal is TRUE. The one premise beyond the fit: the other
    slot's CURRENT domain is int-viewed (the problem-level views
    transfer through coherence, `intViewedDoms_of_coherent`). -/
theorem propNe_implied_true_of_fits {st : State} {i j : Nat}
    {x : Value} {c : Int} {a : Assignment}
    (hsi : st.domains.getD i [] = [x])
    (hgate : domNeGate x c (st.domains.getD j []) = true)
    (hview : IntViewedDoms st.domains)
    (hfit : Core.Assignment.Fits st.domains a)
    (hcons : (DomConstraint.neSlot i j).SatisfiedBy a) :
    (posNe j c).eval a = some true := by
  -- the pinned read: a[i] = x (the singleton fit)
  have hreadi : a[i]? = some x := fits_singleton_read hsi hfit
  obtain ⟨p, q, hpi, hqj, hpq⟩ := hcons
  -- the constraint's own i-read is the pinned value
  have hpiEqx : p = x := by
    rw [hpi] at hreadi
    exact Option.some.inj hreadi
  -- the gate: every value of j's domain viewing to c IS x raw
  have hgateq : ∀ vq ∈ st.domains.getD j [],
      Value.intView vq = some c → vq = x := by
    intro vq hvq hvqview
    have hall := List.all_eq_true.mp hgate vq hvq
    have htest : (match Value.intView vq with
        | some p => if p = c then Value.eqB vq x else true
        | none => true) = true := hall
    rw [hvqview] at htest
    have h2 : (if c = c then Value.eqB vq x else true) = true := htest
    have hvx : Value.eqB vq x = true := by
      rw [if_pos rfl] at h2
      exact h2
    exact Value_eqB_true hvx
  -- q's membership in j's domain (the fit) gives its view
  have hqmem : q ∈ st.domains.getD j [] := hfit.2 j q hqj
  have hvq : Value.intView q ≠ none := by
    obtain ⟨d, hd, hqd⟩ := exists_mem_of_getD st.domains j q hqmem
    exact hview d hd q hqd
  rw [eval_posNe_iff]
  cases hv : Value.intView q with
  | none => exact absurd hv hvq
  | some y2 =>
      by_cases hyc : y2 = c
      · -- q views to c: the gate forces q = x raw; with p = x, the
        -- reads are raw-equal — the constraint is violated
        exfalso
        have hqx : q = x := hgateq q hqmem (by rw [hv, hyc])
        apply hpq
        rw [hqx, hpiEqx]
      · refine ⟨y2, ?_, hyc⟩
        show (a[j]?.bind Value.intView) = some y2
        rw [hqj]
        show Value.intView q = some y2
        exact hv

/-- `propNe` soundness over `x ≠ y` (the raw disequality): the
    raw-singleton conflict is true (no fitting solution of `neSlot`
    exists), the value-removal implied literal is true at every
    fitting solution (the `domNeGate` raw-view correspondence), and
    the empty conflict set carries no entitlement obligation beyond
    the exclusion itself. The `hview` premise (the state's domains
    int-viewed) is the eqSlot-family shape: the problem's views
    transfer through coherence. -/
theorem propNe_safe (st : State) (i j : Nat)
    (hview : IntViewedDoms st.domains) :
    (∀ l r, propNe st i j = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.neSlot i j).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ c, propNe st i j = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.neSlot i j).SatisfiedBy a → False) ∧
    (∀ c, propNe st i j = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.neSlot i j).SatisfiedBy a →
        ∃ l ∈ c, l.eval a = some true) := by
  constructor
  · -- implied: the two value-removal arms
    intro l r hrun a hfit hcons
    rcases propNe_implied_inv hrun with
      ⟨x, c, hsi, hlit, hcl, hc, hmem, hgate⟩ |
      ⟨y, c, hsj, hlit, hcl, hc, hmem, hgate⟩
    · subst hlit
      exact propNe_implied_true_of_fits hsi hgate hview hfit hcons
    · subst hlit
      -- the swapped arm: the constraint's raw disequality is
      -- symmetric
      have hcons' : (DomConstraint.neSlot j i).SatisfiedBy a := by
        obtain ⟨p, q, hp, hq, hpq⟩ := hcons
        exact ⟨q, p, hq, hp, hpq.symm⟩
      exact propNe_implied_true_of_fits hsj hgate hview hfit hcons'
  · refine ⟨?_, ?_⟩
    · -- conflict soundness: equal RAW singletons contradict x ≠ y
      intro c hrun a hfit hcons
      obtain ⟨x, y, hx, hy, hcond, _⟩ := propNe_conflict_inv hrun
      have hri : a[i]? = some x := fits_singleton_read hx hfit
      have hrj : a[j]? = some y := fits_singleton_read hy hfit
      have hcd : x = y := Value_eqB_true hcond
      rw [show (DomConstraint.neSlot i j).SatisfiedBy a =
        ∃ x y, a[i]? = some x ∧ a[j]? = some y ∧ x ≠ y from rfl] at hcons
      rw [hri, hrj] at hcons
      obtain ⟨x2, y2, hx2, hy2, hne⟩ := hcons
      rw [← Option.some.inj hx2, ← Option.some.inj hy2] at hne
      exact hne hcd
    · -- entitlement: the exclusion makes the hypotheses contradictory
      intro c hrun a hfit hcons
      obtain ⟨x, y, hx, hy, hcond, _⟩ := propNe_conflict_inv hrun
      have hri : a[i]? = some x := fits_singleton_read hx hfit
      have hrj : a[j]? = some y := fits_singleton_read hy hfit
      have hcd : x = y := Value_eqB_true hcond
      rw [show (DomConstraint.neSlot i j).SatisfiedBy a =
        ∃ x y, a[i]? = some x ∧ a[j]? = some y ∧ x ≠ y from rfl] at hcons
      rw [hri, hrj] at hcons
      obtain ⟨x2, y2, hx2, hy2, hne⟩ := hcons
      rw [← Option.some.inj hx2, ← Option.some.inj hy2] at hne
      exact absurd hcd hne

/-! ### zipIdx and dotOver list infrastructure -/

/-! ### linLe min-contribution sums -/

def foldMin (ts : List (Nat × Int × Int)) (acc : Option Int) :
    Option Int :=
  ts.foldl (fun acc t => match acc, t with
    | none, (_, _, lw) => some lw
    | some a2, (_, _, lw) => some (a2 + lw)) acc

theorem foldMin_cons (t : Nat × Int × Int) (ts : List (Nat × Int × Int))
    (acc : Option Int) :
    foldMin (t :: ts) acc =
      foldMin ts (match acc, t with
        | none, (_, _, lw) => some lw
        | some a2, (_, _, lw) => some (a2 + lw)) := by
  induction ts generalizing acc with
  | nil => cases acc <;> rfl
  | cons t2 ts2 ih => rfl

theorem foldMin_nil_of (ts : List (Nat × Int × Int))
    (h : foldMin ts none = none) : ts = [] := by
  cases ts with
  | nil => rfl
  | cons t2 ts2 =>
      exfalso
      have : foldMin (t2 :: ts2) none =
          foldMin ts2 (some t2.2.2) := rfl
      rw [this] at h
      -- fold from some never returns none
      have hgen : ∀ (l : List (Nat × Int × Int)) (acc : Int),
          foldMin l (some acc) ≠ none := by
        intro l acc
        induction l generalizing acc with
        | nil => intro hc; cases hc
        | cons t3 l3 ih3 => exact ih3 (acc + t3.2.2)
      exact hgen ts2 t2.2.2 h

-- deduce's loRest is (terms.foldl ... none) where terms =
-- rest.filterMap (minContrib st) — the fold is the SAME as sumMin:
-- foldMin l (some v) = (foldMin l none).map (· + v)
-- foldMin l (some v) = some (s + v) when the base fold is some s
theorem foldMin_add_some {l : List (Nat × Int × Int)} {s v : Int}
    (h : foldMin l none = some s) :
    foldMin l (some v) = some (s + v) := by
  -- general stepping lemma: for any two SOME-starting accs,
  -- foldMin l (some v2) = (foldMin l (some v1)).map (· + (v2 - v1))
  have hstep : ∀ (l2 : List (Nat × Int × Int)) (v1 v2 : Int),
      foldMin l2 (some v2) =
        (foldMin l2 (some v1)).map (fun s2 => s2 + (v2 - v1)) := by
    intro l2 v1 v2
    induction l2 generalizing v1 v2 with
    | nil =>
        show (some v2 : Option Int) =
          ((some v1 : Option Int)).map (fun s2 => s2 + (v2 - v1))
        rw [Option.map_some]
        exact congrArg some (by omega)
    | cons t l3 ih =>
        have e1 : foldMin (t :: l3) (some v1) =
            foldMin l3 (some (v1 + t.2.2)) := rfl
        have e2 : foldMin (t :: l3) (some v2) =
            foldMin l3 (some (v2 + t.2.2)) := rfl
        rw [e1, e2]
        rw [ih (v1 + t.2.2) (v2 + t.2.2)]
        cases hf : foldMin l3 (some (v1 + t.2.2)) with
        | none => rfl
        | some s2 =>
            show (some (s2 + (v2 + t.2.2 - (v1 + t.2.2))) : Option Int) =
              (some (s2 + (v2 - v1)) : Option Int)
            exact congrArg some (by omega)
  -- base: foldMin l none; the hstep at v1 = 0 connects:
  have hbase : foldMin l (some v) =
      (foldMin l (some (0 : Int))).map (fun s2 => s2 + (v - 0)) :=
    hstep l 0 v
  -- and foldMin l (some 0) = foldMin l none (both: the first step
  -- from some 0 or none coincide since 0 + t = t):
  -- apply hstep relating starts s and v: foldMin l (some v) =
  -- (foldMin l (some s)).map (· + (v - s)); and foldMin l (some s)
  -- vs foldMin l none — relate via the nil/cons structure:
  cases l with
  | nil => exact absurd h (by intro hc; cases hc)
  | cons t l2 =>
      show foldMin l2 (some (v + t.2.2)) = some (s + v)
      rw [show foldMin (t :: l2) none =
        foldMin l2 (some t.2.2) from rfl] at h
      have hrel := hstep l2 t.2.2 (v + t.2.2)
      rw [h] at hrel
      rw [hrel, Option.map_some]
      exact congrArg some (by omega)

theorem sumMin_eq_fold (st : State) (rest : List (Int × Nat)) :
    sumMin st rest = foldMin (rest.filterMap (minContrib st)) none := by
  induction rest with
  | nil => rfl
  | cons p ps ih =>
      rw [sumMin, List.filterMap_cons]
      cases hmc : minContrib st p with
      | none => exact ih
      | some t =>
          show (match sumMin st ps with
            | none => some t.2.2
            | some s => some (s + t.2.2)) =
            foldMin (t :: List.filterMap (minContrib st) ps) none
          rw [foldMin_cons]
          conv => lhs; rw [ih]
          cases hsum : foldMin (List.filterMap (minContrib st) ps) none with
          | none =>
              have hnil : (List.filterMap (minContrib st) ps) = [] :=
                foldMin_nil_of _ hsum
              show (some t.2.2 : Option Int) =
                foldMin (List.filterMap (minContrib st) ps) (some t.2.2)
              rw [hnil]
              rfl
          | some s =>
              show (some (s + t.2.2) : Option Int) =
                foldMin (List.filterMap (minContrib st) ps) (some t.2.2)
              rw [foldMin_add_some hsum]

theorem domInts_mem_of_mem {d : List Value} {v : Int}
    (h : Value.int v ∈ d) : v ∈ domInts d := by
  induction d with
  | nil => cases h
  | cons w rest ih =>
      rcases List.mem_cons.mp h with rfl | hrest
      · show v ∈ domInts (Value.int v :: rest)
        simp only [domInts, List.filterMap_cons]
        exact List.mem_cons_self
      · show v ∈ List.filterMap (fun v =>
            match v with
            | .int i => some i
            | .bool b => some (if b then 1 else 0)
            | _ => none) (w :: rest)
        rw [List.mem_filterMap]
        exact ⟨Value.int v, List.mem_cons_of_mem _ hrest, rfl⟩

-- fold over nonempty list is some
theorem foldl_minI_some (l : List Int) (h : l ≠ []) :
    (l.foldl (fun acc i => match acc with
      | none => some i
      | some c => some (minI c i)) none) ≠ none := by
  cases l with
  | nil => exact absurd rfl h
  | cons x xs =>
      show (List.foldl (fun acc i => match acc with
        | none => some i
        | some c => some (minI c i)) (some x) xs) ≠ none
      -- the fold preserves some-ness by induction
      have hgen : ∀ (l2 : List Int) (acc : Int),
          (l2.foldl (fun acc i => match acc with
            | none => some i
            | some c => some (minI c i)) (some acc)) ≠ none := by
        intro l2 acc
        induction l2 generalizing acc with
        | nil => intro hc; cases hc
        | cons y ys ih2 =>
            show (List.foldl _ (some (minI acc y)) ys) ≠ none
            exact ih2 (minI acc y)
      exact hgen xs x

theorem domMinI_ne_none {d : List Value}
    (h : domInts d ≠ []) : domMinI d ≠ none := by
  unfold domMinI
  exact foldl_minI_some _ h

theorem domMaxI_ne_none {d : List Value}
    (h : domInts d ≠ []) : domMaxI d ≠ none := by
  unfold domMaxI
  match hd : domInts d with
  | [] => exact absurd hd h
  | x :: xs =>
      have hrec : ∀ (l3 : List Int) (acc : Int),
          (l3.foldl (fun acc i => match acc with
            | none => some i
            | some c => some (maxI c i)) (some acc)) ≠ none := by
        intro l3 acc
        induction l3 generalizing acc with
        | nil => intro hc; cases hc
        | cons y ys ih2 => exact ih2 (maxI acc y)
      exact hrec xs x

theorem dotOver_split {coeffs : List Int} {is : List Nat}
    {i : Nat} {a : Assignment} {acc : Int} :
    dotOver ((coeffs.zip is).take i ++ (coeffs.zip is).drop (i+1)) a acc =
      (dotOver ((coeffs.zip is).take i) a acc).bind
        (fun acc' => dotOver ((coeffs.zip is).drop (i+1)) a acc') :=
  dotOver_append _ _ _ acc


theorem sumMin_le_dotOver {st : State} {a : Assignment}
    (hfit : Assignment.Fits st.domains a) :
    ∀ (rest : List (Int × Nat)),
    (∀ p, p ∈ rest → ∃ i, slotInt a p.2 = some i) →
    ∀ loRest, sumMin st rest = some loRest →
    ∀ acc d, dotOver rest a acc = some d →
      loRest + acc ≤ d := by
  intro rest hreads
  induction rest with
  | nil => intro loRest hloRest; cases hloRest
  | cons p ps ih =>
      intro loRest hloRest acc d hd
      -- the head's read and extrema
      obtain ⟨xt, hxt⟩ := hreads p List.mem_cons_self
      obtain ⟨v, hv, hvi⟩ := read_of_slotInt hxt
      -- in-range: a[p.2]? = some v gives range (via Fits' length)
      have hrng : p.2 < a.length := by
        cases hr : Nat.lt_or_ge p.2 a.length with
        | inl h => exact h
        | inr hge =>
            exfalso
            have hnone : a[p.2]? = none :=
              List.getElem?_eq_none_iff.mpr (by omega)
            rw [hnone] at hv
            cases hv
      have hread : a[p.2]! = v := getElem_bang_of_read hv hrng
      have hmem : v ∈ st.domains.getD p.2 [] := hfit.2 p.2 v hv
      -- the viewed value xt is in domInts of the slot's domain
      have hviewmem : xt ∈ domInts (st.domains.getD p.2 []) :=
        viewed_mem_of_mem hmem hvi
      have hne : domInts (st.domains.getD p.2 []) ≠ [] := by
        intro hc
        rw [hc] at hviewmem
        cases hviewmem
      have hmn : domMinI (st.domains.getD p.2 []) ≠ none :=
        domMinI_ne_none hne
      have hmx : domMaxI (st.domains.getD p.2 []) ≠ none :=
        domMaxI_ne_none hne
      match hmn2 : domMinI (st.domains.getD p.2 []) with
      | none => exact absurd hmn2 hmn
      | some mn =>
      match hmx2 : domMaxI (st.domains.getD p.2 []) with
      | none => exact absurd hmx2 hmx
      | some mx =>
      have hcontrib : (if p.1 ≥ 0 then p.1 * mn else p.1 * mx) ≤ p.1 * xt :=
        min_contrib_le hfit hmn2 hmx2 hxt
      -- the dot's cons-unfolding (before casing on the read)
      have hdotcase : (match a[p.2]! with
        | .int x => dotOver ps a (acc + p.1 * x)
        | _ => (none : Option Int)) = some d := hd
      -- case on the read's constructor; non-int arms contradict hd
      cases v with
      | int x =>
        have hxt : x = xt := by
          rw [Value.intView] at hvi
          exact Option.some.inj hvi
        rw [hread] at hdotcase
        rw [show (match (Value.int x : Value) with
          | .int y => dotOver ps a (acc + p.1 * y)
          | _ => (none : Option Int)) =
          dotOver ps a (acc + p.1 * x) from rfl] at hdotcase
        -- sumMin cons and the bound
        have hmc : minContrib st (p.1, p.2) =
            some (p.2, p.1, if p.1 ≥ 0 then p.1 * mn else p.1 * mx) := by
          show (match domMinI (st.domains.getD p.2 []),
              domMaxI (st.domains.getD p.2 []) with
            | some mn2, some mx2 =>
                if p.1 ≥ 0 then some (p.2, p.1, p.1 * mn2)
                else some (p.2, p.1, p.1 * mx2)
            | _, _ => none) = _
          rw [hmn2, hmx2]
          by_cases hge : p.1 ≥ 0
          · show (if p.1 ≥ 0 then some (p.2, p.1, p.1 * mn)
              else some (p.2, p.1, p.1 * mx)) = _
            rw [if_pos hge, if_pos hge]
          · show (if p.1 ≥ 0 then some (p.2, p.1, p.1 * mn)
              else some (p.2, p.1, p.1 * mx)) = _
            rw [if_neg (by omega : ¬ p.1 ≥ 0),
              if_neg (by omega : ¬ p.1 ≥ 0)]
        rw [sumMin, hmc] at hloRest
        cases hs : sumMin st ps with
        | none =>
            have hlo : loRest = (if p.1 ≥ 0 then p.1 * mn else p.1 * mx) := by
              have h2 := hloRest
              rw [hs] at h2
              injection h2 with h4
              exact h4.symm
            -- ps's sum is none ⟹ ps = [] (each entry's minContrib
            -- is some; a cons with some-minContrib makes sumMin some)
            have hpsnil : ps = [] := by
              cases ps with
              | nil => rfl
              | cons p2 ps2 =>
                  exfalso
                  have hmemhead : p2 ∈ p :: p2 :: ps2 :=
                    List.mem_cons_of_mem _ List.mem_cons_self
                  obtain ⟨xt2, hxt2⟩ := hreads p2 hmemhead
                  obtain ⟨v2, hv2, hvi2⟩ := read_of_slotInt hxt2
                  have hmem2 : v2 ∈ st.domains.getD p2.2 [] :=
                    hfit.2 p2.2 v2 hv2
                  have hvm2 : xt2 ∈ domInts (st.domains.getD p2.2 []) :=
                    viewed_mem_of_mem hmem2 hvi2
                  have hne2 : domInts (st.domains.getD p2.2 []) ≠ [] := by
                    intro hc; rw [hc] at hvm2; cases hvm2
                  obtain ⟨mn2, hq1⟩ : ∃ mn2,
                      domMinI (st.domains.getD p2.2 []) = some mn2 := by
                    cases hq : domMinI (st.domains.getD p2.2 []) with
                    | none => exact absurd hq (domMinI_ne_none hne2)
                    | some w => exact ⟨w, rfl⟩
                  obtain ⟨mx2, hq2⟩ : ∃ mx2,
                      domMaxI (st.domains.getD p2.2 []) = some mx2 := by
                    cases hq : domMaxI (st.domains.getD p2.2 []) with
                    | none => exact absurd hq (domMaxI_ne_none hne2)
                    | some w => exact ⟨w, rfl⟩
                  obtain ⟨w2, hw2⟩ : ∃ w2, minContrib st p2 = some w2 := by
                    refine ⟨(if p2.1 ≥ 0 then (p2.2, p2.1, p2.1 * mn2)
                      else (p2.2, p2.1, p2.1 * mx2)), ?_⟩
                    show (match domMinI (st.domains.getD p2.2 []),
                        domMaxI (st.domains.getD p2.2 []) with
                      | some mn3, some mx3 =>
                          if p2.1 ≥ 0 then some (p2.2, p2.1, p2.1 * mn3)
                          else some (p2.2, p2.1, p2.1 * mx3)
                      | _, _ => none) = _
                    rw [hq1, hq2]
                    by_cases hge2 : p2.1 ≥ 0
                    · show (if p2.1 ≥ 0 then some (p2.2, p2.1, p2.1 * mn2)
                        else some (p2.2, p2.1, p2.1 * mx2)) = _
                      rw [if_pos hge2, if_pos hge2]
                    · show (if p2.1 ≥ 0 then some (p2.2, p2.1, p2.1 * mn2)
                        else some (p2.2, p2.1, p2.1 * mx2)) = _
                      rw [if_neg (by omega : ¬ p2.1 ≥ 0),
                        if_neg (by omega : ¬ p2.1 ≥ 0)]
                  rw [sumMin, hw2] at hs
                  cases hinner : sumMin st ps2 with
                  | none => exact absurd hs (by rw [hinner]; intro hc; cases hc)
                  | some s => exact absurd hs (by rw [hinner]; intro hc; cases hc)
            -- ps = [] ⟹ dotOver [] = some (acc + p.1*xt):
            rw [hpsnil, hxt] at hdotcase
            have hd2 : d = acc + p.1 * xt := by
              have hdotnil : dotOver ([] : List (Int × Nat)) a
                  (acc + p.1 * xt) = some (acc + p.1 * xt) := rfl
              rw [hdotnil] at hdotcase
              exact (Option.some.inj hdotcase).symm
            rw [hlo, hd2]
            omega
        | some s =>
            have hlo : loRest = s + (if p.1 ≥ 0 then p.1 * mn else p.1 * mx) := by
              have h2 := hloRest
              rw [hs] at h2
              injection h2 with h4
              exact h4.symm
            rw [hxt] at hdotcase
            have htail := ih
              (fun p2 hp2 => hreads p2 (List.mem_cons_of_mem _ hp2)) s hs
              (acc + p.1 * xt) d hdotcase
            omega
      | bool b =>
        rw [hread] at hdotcase
        cases hdotcase
      | setOfInt s =>
        rw [hread] at hdotcase
        cases hdotcase
      | array xs =>
        rw [hread] at hdotcase
        cases hdotcase


theorem linLe_entry_arith {st : State} {a : Assignment}
    {coeffs : List Int} {is : List Nat} {b : Int}
    (hlen : coeffs.length = is.length)
    (hfit : Assignment.Fits st.domains a)
    (hcons : (DomConstraint.linLe coeffs is b).SatisfiedBy a)
    (hreads : ∀ p, p ∈ coeffs.zip is → ∃ x, slotInt a p.2 = some x)
    {m : Nat} {c : Int} {i : Nat}
    (himem : ((c, m), i) ∈ (coeffs.zip is).zipIdx)
    {loRest : Int}
    (hsum : sumMin st
        (((coeffs.zip is).zipIdx.filter (fun p => p.2 != i)).map (·.1))
        = some loRest) :
    ∃ d xt, dotOver (coeffs.zip is) a 0 = some d ∧ d ≤ b ∧
      slotInt a m = some xt ∧ loRest ≤ d - c * xt := by
  -- the entry's length bound and getD:
  have hlen2 : i - 0 < (coeffs.zip is).length :=
    zipIdx_mem_length _ 0 i (c, m) himem
  have hi : i < (coeffs.zip is).length := by omega
  have hentry : (coeffs.zip is).getD i (c, m) = (c, m) :=
    zipIdx_getD (coeffs.zip is) i (c, m) himem
  -- the full dot at the solution:
  obtain ⟨d, hdot, hdle⟩ := linLe_dot hcons hlen
  -- the split at i:
  have hreads' : ∀ p, p ∈ (coeffs.zip is).take i ++
      (coeffs.zip is).drop (i+1) → ∃ x, slotInt a p.2 = some x := by
    intro p hp
    rw [List.mem_append] at hp
    rcases hp with h1 | h2
    · exact hreads p (List.take_subset _ _ h1)
    · exact hreads p (List.drop_subset _ _ h2)
  obtain ⟨c2, m2, xt2, rest, hcm2, hxt2, hrest, hdotrest⟩ :=
    dotOver_split_mid (coeffs := coeffs) (is := is) hi hreads hdot
  -- reconcile: c2 = c, m2 = m (getD at i is unique):
  -- getD at an in-range index ignores the default:
  have hget : ∀ df : Int × Nat, (coeffs.zip is).getD i df =
      (coeffs.zip is).getD i (0, 0) := by
    intro df
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi]
    rfl
  -- reconcile the entry components:
  obtain ⟨hc, hm⟩ : c2 = c ∧ m2 = m := by
    have h1 : (coeffs.zip is).getD i (0, 0) = (c, m) := by
      rw [show (coeffs.zip is).getD i (0, 0) =
        (coeffs.zip is).getD i (c, m) from (hget (c, m)).symm]
      rw [hentry]
    -- h1 : getD (0,0) = (c,m); hcm2 : getD (0,0) = (c2,m2)
    have h2 : (c2, m2) = (c, m) := hcm2.symm.trans h1
    exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩
  -- the reads-int for the rest list:
  subst hc
  subst hm
  -- the reads-int for the rest list:
  have hreadsRest : ∀ p, p ∈ rest → ∃ x, slotInt a p.2 = some x := by
    intro p hp
    rw [hrest] at hp
    exact hreads' p hp
  -- the sumMin bound: loRest + 0 ≤ dot rest 0 = d - c*xt
  have hfilter : (((coeffs.zip is).zipIdx.filter
      (fun p => p.2 != i)).map (·.1)) = rest := by
    have hilt : i < (coeffs.zip is).length := hi
    rw [zipIdx_filter_remove (coeffs.zip is) i hilt, hrest]
  rw [← hfilter] at hreadsRest
  have hbound := sumMin_le_dotOver hfit
    (((coeffs.zip is).zipIdx.filter (fun p => p.2 != i)).map (·.1))
    hreadsRest loRest hsum
  -- hbound : ∀ acc d2, dot (filtered) a acc = some d2 → ...
  -- the filtered list's dot = rest's dot = d - c*xt (by hdotrest
  -- + hfilter):
  refine ⟨d, xt2, hdot, hdle, hxt2, ?_⟩
  -- goal: loRest ≤ d - c2*xt
  have hdrest : dotOver
      (((coeffs.zip is).zipIdx.filter (fun p => p.2 != i)).map (·.1))
      a 0 = some (d - c2 * xt2) := by
    rw [hfilter]
    exact hdotrest
  have := hbound 0 (d - c2 * xt2) hdrest
  omega


theorem propLinLe_safe (st : State) (coeffs : List Int) (is : List Nat)
    (b : Int) (hlen : coeffs.length = is.length) :
    (∀ l r, propLinLe st coeffs is b = .implied l r →
      ∀ a, Assignment.Fits st.domains a →
        (DomConstraint.linLe coeffs is b).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ c, propLinLe st coeffs is b = .conflict c →
      ∀ a, Assignment.Fits st.domains a →
        (DomConstraint.linLe coeffs is b).SatisfiedBy a → False) := by
  constructor
  · -- implied-literal soundness
    intro l r hrun a hfit hcons
    unfold propLinLe at hrun
    split at hrun
    · cases hrun
    · rcases sweep_inv hrun with hstable | ⟨m, c, i, hmem, hdet⟩
      · cases hstable
      have hreads := linLe_reads_int hcons hlen
      have hc3 : c = 1 ∨ c = -1 ∨ (c ≠ 1 ∧ c ≠ -1) := by omega
      match hc3 with
      | Or.inl hc =>
        rw [hc] at hdet
        cases hlr : sumMin st
            (((coeffs.zip is).zipIdx.filter
              (fun p => p.2 != i)).map (·.1)) with
        | none =>
            exfalso
            have hF2n : (List.foldl (fun acc t =>
                match acc, t with
                | none, (fst, fst_1, l) => some l
                | some a, (fst, fst_1, l) => some (a + l)) none
                (List.filterMap
                  (fun p =>
                    match domMinI (st.domains.getD p.snd []),
                      domMaxI (st.domains.getD p.snd []) with
                    | some mn, some mx =>
                        if p.fst ≥ (0 : Int) then
                          some (p.snd, p.fst, p.fst * mn)
                        else some (p.snd, p.fst, p.fst * mx)
                    | x, x_1 => none)
                  (List.map (fun x => x.fst)
                    (List.filter (fun p => p.snd != i)
                      (coeffs.zip is).zipIdx)))) = none := by
              have h1 := sumMin_eq_fold st
                (((coeffs.zip is).zipIdx.filter
                  (fun p => p.2 != i)).map (·.1))
              rw [hlr] at h1
              exact h1.symm
            have hdet2 : PropagationResult.implied l r = .stable := by
              rw [hdet]
              dsimp only
              generalize hFV : (List.foldl (fun acc t =>
                  match acc, t with
                  | none, (fst, fst_1, l) => some l
                  | some a, (fst, fst_1, l) => some (a + l)) none
                  (List.filterMap
                    (fun p =>
                      match domMinI (st.domains.getD p.snd []),
                        domMaxI (st.domains.getD p.snd []) with
                      | some mn, some mx =>
                          if p.fst ≥ (0 : Int) then
                            some (p.snd, p.fst, p.fst * mn)
                          else some (p.snd, p.fst, p.fst * mx)
                      | x, x_1 => none)
                    (List.map (fun x => x.fst)
                      (List.filter (fun p => p.snd != i)
                        (coeffs.zip is).zipIdx)))) = FOV
              rw [hF2n] at hFV
              subst hFV
              rfl
            cases hdet2
        | some lr =>
            have hgate : PropagationResult.implied l r =
                narrowHi st m (b - lr)
                  ([posLe m (b - lr)] ++
                    (List.filterMap (fun t =>
                      match t with
                      | (slot, ct, lw) =>
                          if ct == 1 then some (posLe slot (lw - 1))
                          else if ct == -1 then
                            some (negLe slot (-lw))
                          else none)
                      (List.filterMap (fun p =>
                        match p with
                        | (ct, t) =>
                            match domMinI (st.domains.getD t []),
                              domMaxI (st.domains.getD t []) with
                            | some mn, some mx =>
                                if ct ≥ 0 then some (t, ct, ct * mn)
                                else some (t, ct, ct * mx)
                            | _, _ => none)
                        ((List.map (fun x => x.fst)
                          (List.filter (fun p => p.2 != i)
                            (coeffs.zip is).zipIdx)))))) := by
              rw [hdet]
              dsimp only
              have hF2 : (List.foldl (fun acc t =>
                  match acc, t with
                  | none, (fst, fst_1, l) => some l
                  | some a, (fst, fst_1, l) => some (a + l)) none
                  (List.filterMap
                    (fun p =>
                      match domMinI (st.domains.getD p.snd []),
                        domMaxI (st.domains.getD p.snd []) with
                      | some mn, some mx =>
                          if p.fst ≥ (0 : Int) then
                            some (p.snd, p.fst, p.fst * mn)
                          else some (p.snd, p.fst, p.fst * mx)
                      | x, x_1 => none)
                    (List.map (fun x => x.fst)
                      (List.filter (fun p => p.snd != i)
                        (coeffs.zip is).zipIdx)))) = some lr := by
                have h1 := sumMin_eq_fold st
                  (((coeffs.zip is).zipIdx.filter
                    (fun p => p.2 != i)).map (·.1))
                rw [hlr] at h1
                exact h1.symm
              generalize hFV : (List.foldl (fun acc t =>
                  match acc, t with
                  | none, (fst, fst_1, l) => some l
                  | some a, (fst, fst_1, l) => some (a + l)) none
                  (List.filterMap
                    (fun p =>
                      match domMinI (st.domains.getD p.snd []),
                        domMaxI (st.domains.getD p.snd []) with
                      | some mn, some mx =>
                          if p.fst ≥ (0 : Int) then
                            some (p.snd, p.fst, p.fst * mn)
                          else some (p.snd, p.fst, p.fst * mx)
                      | x, x_1 => none)
                    (List.map (fun x => x.fst)
                      (List.filter (fun p => p.snd != i)
                        (coeffs.zip is).zipIdx)))) = FOV
              rw [hF2] at hFV
              subst hFV
              rfl
            obtain ⟨hl, _⟩ := narrowHi_implied_inv hgate.symm
            subst hl
            rw [eval_posLe_iff]
            obtain ⟨d, xt, hdot, hdle, hxtm, hlr_le⟩ := linLe_entry_arith
              (st := st) (a := a) (coeffs := coeffs) (is := is) (b := b)
              hlen hfit hcons hreads hmem hlr
            exact ⟨xt, hxtm, by rw [hc] at hlr_le; omega⟩
      | Or.inr (Or.inl hc) =>
        rw [hc] at hdet
        cases hlr : sumMin st
            (((coeffs.zip is).zipIdx.filter
              (fun p => p.2 != i)).map (·.1)) with
        | none =>
            exfalso
            have hF2n : (List.foldl (fun acc t =>
                match acc, t with
                | none, (fst, fst_1, l) => some l
                | some a, (fst, fst_1, l) => some (a + l)) none
                (List.filterMap
                  (fun p =>
                    match domMinI (st.domains.getD p.snd []),
                      domMaxI (st.domains.getD p.snd []) with
                    | some mn, some mx =>
                        if p.fst ≥ (0 : Int) then
                          some (p.snd, p.fst, p.fst * mn)
                        else some (p.snd, p.fst, p.fst * mx)
                    | x, x_1 => none)
                  (List.map (fun x => x.fst)
                    (List.filter (fun p => p.snd != i)
                      (coeffs.zip is).zipIdx)))) = none := by
              have h1 := sumMin_eq_fold st
                (((coeffs.zip is).zipIdx.filter
                  (fun p => p.2 != i)).map (·.1))
              rw [hlr] at h1
              exact h1.symm
            have hdet2 : PropagationResult.implied l r = .stable := by
              rw [hdet]
              dsimp only
              generalize hFV : (List.foldl (fun acc t =>
                  match acc, t with
                  | none, (fst, fst_1, l) => some l
                  | some a, (fst, fst_1, l) => some (a + l)) none
                  (List.filterMap
                    (fun p =>
                      match domMinI (st.domains.getD p.snd []),
                        domMaxI (st.domains.getD p.snd []) with
                      | some mn, some mx =>
                          if p.fst ≥ (0 : Int) then
                            some (p.snd, p.fst, p.fst * mn)
                          else some (p.snd, p.fst, p.fst * mx)
                      | x, x_1 => none)
                    (List.map (fun x => x.fst)
                      (List.filter (fun p => p.snd != i)
                        (coeffs.zip is).zipIdx)))) = FOV
              rw [hF2n] at hFV
              subst hFV
              rfl
            cases hdet2
        | some lr =>
            have hgate : PropagationResult.implied l r =
                narrowLo st m (lr - b)
                  ([negLe m (lr - b - 1)] ++
                    (List.filterMap (fun t =>
                      match t with
                      | (slot, ct, lw) =>
                          if ct == 1 then some (posLe slot (lw - 1))
                          else if ct == -1 then
                            some (negLe slot (-lw))
                          else none)
                      (List.filterMap (fun p =>
                        match p with
                        | (ct, t) =>
                            match domMinI (st.domains.getD t []),
                              domMaxI (st.domains.getD t []) with
                            | some mn, some mx =>
                                if ct ≥ 0 then some (t, ct, ct * mn)
                                else some (t, ct, ct * mx)
                            | _, _ => none)
                        ((List.map (fun x => x.fst)
                          (List.filter (fun p => p.2 != i)
                            (coeffs.zip is).zipIdx)))))) := by
              rw [hdet]
              dsimp only
              have hF2 : (List.foldl (fun acc t =>
                  match acc, t with
                  | none, (fst, fst_1, l) => some l
                  | some a, (fst, fst_1, l) => some (a + l)) none
                  (List.filterMap
                    (fun p =>
                      match domMinI (st.domains.getD p.snd []),
                        domMaxI (st.domains.getD p.snd []) with
                      | some mn, some mx =>
                          if p.fst ≥ (0 : Int) then
                            some (p.snd, p.fst, p.fst * mn)
                          else some (p.snd, p.fst, p.fst * mx)
                      | x, x_1 => none)
                    (List.map (fun x => x.fst)
                      (List.filter (fun p => p.snd != i)
                        (coeffs.zip is).zipIdx)))) = some lr := by
                have h1 := sumMin_eq_fold st
                  (((coeffs.zip is).zipIdx.filter
                    (fun p => p.2 != i)).map (·.1))
                rw [hlr] at h1
                exact h1.symm
              generalize hFV : (List.foldl (fun acc t =>
                  match acc, t with
                  | none, (fst, fst_1, l) => some l
                  | some a, (fst, fst_1, l) => some (a + l)) none
                  (List.filterMap
                    (fun p =>
                      match domMinI (st.domains.getD p.snd []),
                        domMaxI (st.domains.getD p.snd []) with
                      | some mn, some mx =>
                          if p.fst ≥ (0 : Int) then
                            some (p.snd, p.fst, p.fst * mn)
                          else some (p.snd, p.fst, p.fst * mx)
                      | x, x_1 => none)
                    (List.map (fun x => x.fst)
                      (List.filter (fun p => p.snd != i)
                        (coeffs.zip is).zipIdx)))) = FOV
              rw [hF2] at hFV
              subst hFV
              rfl
            obtain ⟨hl, _⟩ := narrowLo_implied_inv hgate.symm
            subst hl
            rw [eval_negLe_iff]
            obtain ⟨d, xt, hdot, hdle, hxtm, hlr_le⟩ := linLe_entry_arith
              (st := st) (a := a) (coeffs := coeffs) (is := is) (b := b)
              hlen hfit hcons hreads hmem hlr
            exact ⟨xt, hxtm, by rw [hc] at hlr_le; omega⟩
      | Or.inr (Or.inr hc1) =>
        exfalso
        -- c is neither 1 nor -1: the deduce match's catch-all arm
        -- is stable
        have hdet2 : PropagationResult.implied l r = .stable := by
          rw [hdet]
          dsimp only
          -- split the match; the first two arms require c = 1 /
          -- c = -1, contradicting hc1; the third is stable:
          split
          · exfalso; exact hc1.1 rfl
          · exfalso; exact hc1.2 rfl
          · rfl
        cases hdet2
  · -- conflict soundness
    intro c hrun a hfit hcons
    unfold propLinLe at hrun
    split at hrun
    · cases hrun
    · rcases sweep_inv hrun with hstable | ⟨m, c2, i2, hmem, hdet⟩
      · cases hstable
      have hreads := linLe_reads_int hcons hlen
      have hc3 : c2 = 1 ∨ c2 = -1 ∨ (c2 ≠ 1 ∧ c2 ≠ -1) := by omega
      match hc3 with
      | Or.inl hc =>
        rw [hc] at hdet
        cases hlr : sumMin st
            (((coeffs.zip is).zipIdx.filter
              (fun p => p.2 != i2)).map (·.1)) with
        | none =>
            exfalso
            have hdet2 : PropagationResult.conflict c = .stable := by
              rw [hdet]
              dsimp only
              generalize hFV : (List.foldl (fun acc t =>
                  match acc, t with
                  | none, (fst, fst_1, l) => some l
                  | some a, (fst, fst_1, l) => some (a + l)) none
                  (List.filterMap
                    (fun p =>
                      match domMinI (st.domains.getD p.snd []),
                        domMaxI (st.domains.getD p.snd []) with
                      | some mn, some mx =>
                          if p.fst ≥ (0 : Int) then
                            some (p.snd, p.fst, p.fst * mn)
                          else some (p.snd, p.fst, p.fst * mx)
                      | x, x_1 => none)
                    (List.map (fun x => x.fst)
                      (List.filter (fun p => p.snd != i2)
                        (coeffs.zip is).zipIdx)))) = FOV
              have hF2n : (List.foldl (fun acc t =>
                  match acc, t with
                  | none, (fst, fst_1, l) => some l
                  | some a, (fst, fst_1, l) => some (a + l)) none
                  (List.filterMap
                    (fun p =>
                      match domMinI (st.domains.getD p.snd []),
                        domMaxI (st.domains.getD p.snd []) with
                      | some mn, some mx =>
                          if p.fst ≥ (0 : Int) then
                          some (p.snd, p.fst, p.fst * mn)
                          else some (p.snd, p.fst, p.fst * mx)
                      | x, x_1 => none)
                    (List.map (fun x => x.fst)
                      (List.filter (fun p => p.snd != i2)
                        (coeffs.zip is).zipIdx)))) = none := by
                have h1 := sumMin_eq_fold st
                  (((coeffs.zip is).zipIdx.filter
                    (fun p => p.2 != i2)).map (·.1))
                rw [hlr] at h1
                exact h1.symm
              rw [hF2n] at hFV
              subst hFV
              rfl
            cases hdet2
        | some lr =>
            exfalso
            have hgate : PropagationResult.conflict c =
                narrowHi st m (b - lr)
                  ([posLe m (b - lr)] ++
                    (List.filterMap (fun t =>
                      match t with
                      | (slot, ct, lw) =>
                          if ct == 1 then some (posLe slot (lw - 1))
                          else if ct == -1 then
                            some (negLe slot (-lw))
                          else none)
                      (List.filterMap (fun p =>
                        match p with
                        | (ct, t) =>
                            match domMinI (st.domains.getD t []),
                              domMaxI (st.domains.getD t []) with
                            | some mn, some mx =>
                                if ct ≥ 0 then some (t, ct, ct * mn)
                                else some (t, ct, ct * mx)
                            | _, _ => none)
                        ((List.map (fun x => x.fst)
                          (List.filter (fun p => p.2 != i2)
                            (coeffs.zip is).zipIdx)))))) := by
              rw [hdet]
              dsimp only
              have hF2 : (List.foldl (fun acc t =>
                  match acc, t with
                  | none, (fst, fst_1, l) => some l
                  | some a, (fst, fst_1, l) => some (a + l)) none
                  (List.filterMap
                    (fun p =>
                      match domMinI (st.domains.getD p.snd []),
                        domMaxI (st.domains.getD p.snd []) with
                      | some mn, some mx =>
                          if p.fst ≥ (0 : Int) then
                            some (p.snd, p.fst, p.fst * mn)
                          else some (p.snd, p.fst, p.fst * mx)
                      | x, x_1 => none)
                    (List.map (fun x => x.fst)
                      (List.filter (fun p => p.snd != i2)
                        (coeffs.zip is).zipIdx)))) = some lr := by
                have h1 := sumMin_eq_fold st
                  (((coeffs.zip is).zipIdx.filter
                    (fun p => p.2 != i2)).map (·.1))
                rw [hlr] at h1
                exact h1.symm
              generalize hFV : (List.foldl (fun acc t =>
                  match acc, t with
                  | none, (fst, fst_1, l) => some l
                  | some a, (fst, fst_1, l) => some (a + l)) none
                  (List.filterMap
                    (fun p =>
                      match domMinI (st.domains.getD p.snd []),
                        domMaxI (st.domains.getD p.snd []) with
                      | some mn, some mx =>
                          if p.fst ≥ (0 : Int) then
                            some (p.snd, p.fst, p.fst * mn)
                          else some (p.snd, p.fst, p.fst * mx)
                      | x, x_1 => none)
                    (List.map (fun x => x.fst)
                      (List.filter (fun p => p.snd != i2)
                        (coeffs.zip is).zipIdx)))) = FOV
              rw [hF2] at hFV
              subst hFV
              rfl
            obtain ⟨mn, mx, hmn, hmx, hgt, _⟩ :=
              narrowHi_conflict_inv hgate.symm
            obtain ⟨d, xt, hdot, hdle, hxtm, hlr_le⟩ :=
              linLe_entry_arith (st := st) (a := a) (coeffs := coeffs)
                (is := is) (b := b) hlen hfit hcons hreads hmem hlr
            have hfitm : mn ≤ xt := fits_min_bound hfit hmn hxtm
            rw [hc] at hlr_le
            omega
      | Or.inr (Or.inl hc) =>
        rw [hc] at hdet
        cases hlr : sumMin st
            (((coeffs.zip is).zipIdx.filter
              (fun p => p.2 != i2)).map (·.1)) with
        | none =>
            exfalso
            have hdet2 : PropagationResult.conflict c = .stable := by
              rw [hdet]
              dsimp only
              generalize hFV : (List.foldl (fun acc t =>
                  match acc, t with
                  | none, (fst, fst_1, l) => some l
                  | some a, (fst, fst_1, l) => some (a + l)) none
                  (List.filterMap
                    (fun p =>
                      match domMinI (st.domains.getD p.snd []),
                        domMaxI (st.domains.getD p.snd []) with
                      | some mn, some mx =>
                          if p.fst ≥ (0 : Int) then
                            some (p.snd, p.fst, p.fst * mn)
                          else some (p.snd, p.fst, p.fst * mx)
                      | x, x_1 => none)
                    (List.map (fun x => x.fst)
                      (List.filter (fun p => p.snd != i2)
                        (coeffs.zip is).zipIdx)))) = FOV
              have hF2n : (List.foldl (fun acc t =>
                  match acc, t with
                  | none, (fst, fst_1, l) => some l
                  | some a, (fst, fst_1, l) => some (a + l)) none
                  (List.filterMap
                    (fun p =>
                      match domMinI (st.domains.getD p.snd []),
                        domMaxI (st.domains.getD p.snd []) with
                      | some mn, some mx =>
                          if p.fst ≥ (0 : Int) then
                          some (p.snd, p.fst, p.fst * mn)
                          else some (p.snd, p.fst, p.fst * mx)
                      | x, x_1 => none)
                    (List.map (fun x => x.fst)
                      (List.filter (fun p => p.snd != i2)
                        (coeffs.zip is).zipIdx)))) = none := by
                have h1 := sumMin_eq_fold st
                  (((coeffs.zip is).zipIdx.filter
                    (fun p => p.2 != i2)).map (·.1))
                rw [hlr] at h1
                exact h1.symm
              rw [hF2n] at hFV
              subst hFV
              rfl
            cases hdet2
        | some lr =>
            exfalso
            have hgate : PropagationResult.conflict c =
                narrowLo st m (lr - b)
                  ([negLe m (lr - b - 1)] ++
                    (List.filterMap (fun t =>
                      match t with
                      | (slot, ct, lw) =>
                          if ct == 1 then some (posLe slot (lw - 1))
                          else if ct == -1 then
                            some (negLe slot (-lw))
                          else none)
                      (List.filterMap (fun p =>
                        match p with
                        | (ct, t) =>
                            match domMinI (st.domains.getD t []),
                              domMaxI (st.domains.getD t []) with
                            | some mn, some mx =>
                                if ct ≥ 0 then some (t, ct, ct * mn)
                                else some (t, ct, ct * mx)
                            | _, _ => none)
                        ((List.map (fun x => x.fst)
                          (List.filter (fun p => p.2 != i2)
                            (coeffs.zip is).zipIdx)))))) := by
              rw [hdet]
              dsimp only
              have hF2 : (List.foldl (fun acc t =>
                  match acc, t with
                  | none, (fst, fst_1, l) => some l
                  | some a, (fst, fst_1, l) => some (a + l)) none
                  (List.filterMap
                    (fun p =>
                      match domMinI (st.domains.getD p.snd []),
                        domMaxI (st.domains.getD p.snd []) with
                      | some mn, some mx =>
                          if p.fst ≥ (0 : Int) then
                            some (p.snd, p.fst, p.fst * mn)
                          else some (p.snd, p.fst, p.fst * mx)
                      | x, x_1 => none)
                    (List.map (fun x => x.fst)
                      (List.filter (fun p => p.snd != i2)
                        (coeffs.zip is).zipIdx)))) = some lr := by
                have h1 := sumMin_eq_fold st
                  (((coeffs.zip is).zipIdx.filter
                    (fun p => p.2 != i2)).map (·.1))
                rw [hlr] at h1
                exact h1.symm
              generalize hFV : (List.foldl (fun acc t =>
                  match acc, t with
                  | none, (fst, fst_1, l) => some l
                  | some a, (fst, fst_1, l) => some (a + l)) none
                  (List.filterMap
                    (fun p =>
                      match domMinI (st.domains.getD p.snd []),
                        domMaxI (st.domains.getD p.snd []) with
                      | some mn, some mx =>
                          if p.fst ≥ (0 : Int) then
                            some (p.snd, p.fst, p.fst * mn)
                          else some (p.snd, p.fst, p.fst * mx)
                      | x, x_1 => none)
                    (List.map (fun x => x.fst)
                      (List.filter (fun p => p.snd != i2)
                        (coeffs.zip is).zipIdx)))) = FOV
              rw [hF2] at hFV
              subst hFV
              rfl
            obtain ⟨mn, mx, hmn, hmx, hlt, _⟩ :=
              narrowLo_conflict_inv hgate.symm
            obtain ⟨d, xt, hdot, hdle, hxtm, hlr_le⟩ :=
              linLe_entry_arith (st := st) (a := a) (coeffs := coeffs)
                (is := is) (b := b) hlen hfit hcons hreads hmem hlr
            have hfitm : xt ≤ mx := fits_max_bound hfit hmx hxtm
            rw [hc] at hlr_le
            omega
      | Or.inr (Or.inr hc1) =>
        exfalso
        have hdet2 : PropagationResult.conflict c = .stable := by
          rw [hdet]
          dsimp only
          split
          · exfalso; exact hc1.1 rfl
          · exfalso; exact hc1.2 rfl
          · rfl
        cases hdet2

/-- The FULL three-bullet soundness (with entitlement). The
    entitlement is vacuous: a conflict excludes every fitting
    solution, so no such `a` exists. -/
theorem propLinLe_safe_full (st : State) (coeffs : List Int) (is : List Nat)
    (b : Int) (hlen : coeffs.length = is.length) :
    (∀ l r, propLinLe st coeffs is b = .implied l r →
      ∀ a, Assignment.Fits st.domains a →
        (DomConstraint.linLe coeffs is b).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ c, propLinLe st coeffs is b = .conflict c →
      ∀ a, Assignment.Fits st.domains a →
        (DomConstraint.linLe coeffs is b).SatisfiedBy a → False) ∧
    (∀ c, propLinLe st coeffs is b = .conflict c →
      ∀ a, Assignment.Fits st.domains a →
        (DomConstraint.linLe coeffs is b).SatisfiedBy a →
        ∃ l ∈ c, l.eval a = some true) := by
  obtain ⟨h1, h2⟩ := propLinLe_safe st coeffs is b hlen
  exact ⟨h1, h2, fun c hrun a hfit hcons =>
    absurd hrun (fun hc => h2 c hc a hfit hcons)⟩


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
      propagatorOfProved dc = some p)
    -- the compiled shape: every linLe constraint has equal-length
    -- coefficient/index lists (the extractor's gate)
    (hlin : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linLe coeffs is b → coeffs.length = is.length)
    (hlinE : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linEq coeffs is b → coeffs.length = is.length) :
    ∀ st, DomainCoherent problem st →
    PropSafe problem DomConstraint.SatisfiedBy props st := by
  intro st hcoh
  refine ⟨?_, ?_⟩
  · intro p hp l r hrun a ⟨hsol, hrep⟩
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
      ⟨lc, li, lb2, ldca, hrunl⟩ | ⟨ti, tj, tk2, hdct, hrunt⟩ |
      ⟨ais, hadca, hrunad⟩
    · rw [hdc2] at hdc
      exact propagatorOf_leSlot_implied (problem := problem)
        (i := i) (j := j) hdc hrun2 a hsol hrep
    · rw [hdc2] at hdc
      exact (propLt_safe st i j).1 l r hrun2 a hrep.1 (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      have hviewst := intViewedDoms_of_coherent hview hcoh
      exact (propEq_safe st i j hviewst).1 l r hrun2 a hrep.1
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      have hviewst := intViewedDoms_of_coherent hview hcoh
      exact (propNe_safe st i j hviewst).1 l r hrun2 a hrep.1
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      exact (propPlus_safe st i j k).1 l r hrun2 a hrep.1 (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      -- linLe needs equal lengths (the compiled shape):
      have hlen : coeffs.length = is.length :=
        hlin _ hdc coeffs is b2 rfl
      exact (propLinLe2_safe st coeffs is b2 hlen).1 l r hrun2 a hrep.1
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      exact (propLeConstHi_safe st i c).1 l r hrun2 a hrep.1
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      exact (propLeConstLo_safe st i c).1 l r hrun2 a hrep.1
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      exact (propLtConstHi_safe st i c).1 l r hrun2 a hrep.1
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      exact (propLtConstLo_safe st i c).1 l r hrun2 a hrep.1
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      exact (propConstEq_safe st i v).1 l r hrun2 a hrep.1
        (hsol.2 _ hdc)
    · rw [hdca] at hdc
      exact (propBoolNot_safe st ia ja).1 l r hruna a hrep.1
        (hsol.2 _ hdc)
    · rw [hdcb] at hdc
      exact (propBoolAnd_safe st ib jb kb).1 l r hrunb a hrep.1
        (hsol.2 _ hdc)
    · rw [hdcc] at hdc
      exact (propBoolOr_safe st ic jc kc).1 l r hrunc a hrep.1
        (hsol.2 _ hdc)
    · rw [hdcd] at hdc
      exact (propMin_safe st id jd kd).1 l r hrund a hrep.1
        (hsol.2 _ hdc)
    · rw [hdce] at hdc
      exact (propMax_safe st ie je ke).1 l r hrune a hrep.1
        (hsol.2 _ hdc)
    · rw [hdcg] at hdc
      exact (propAbs_safe st ig kg).1 l r hrung a hrep.1
        (hsol.2 _ hdc)
    · rw [ldca] at hdc
      have hlenL : lc.length = li.length :=
        hlinE _ hdc lc li lb2 rfl
      exact (propLinEq2_safe st lc li lb2 hlenL).1 l r hrunl a hrep.1
        (hsol.2 _ hdc)
    · rw [hdct] at hdc
      exact (propTimes_safe st ti tj tk2).1 l r hrunt a hrep.1
        (hsol.2 _ hdc)
    · rw [hadca] at hdc
      exact (propAllDiffLCG_safe st ais).1 l r hrunad a hrep.1
        (hsol.2 _ hdc)
  · intro p hp c hrun a ⟨hsol, hrep⟩
    obtain ⟨dc, hdc, hprop⟩ := hprops p hp
    rcases propagatorOfProved_run hprop hrun with
      ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, hdc2, hrun2⟩ |
      ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, k, hdc2, hrun2⟩ |
      ⟨coeffs, is, b2, hdc2, hrun2⟩ | ⟨i, k, hdc2, hrun2⟩ |
      ⟨i, k, hdc2, hrun2⟩ | ⟨i, k, hdc2, hrun2⟩ |
      ⟨i, k, hdc2, hrun2⟩ | ⟨i, v, hdc2, hrun2⟩ |
      ⟨ia, ja, hdca, hruna⟩ | ⟨ib, jb, kb, hdcb, hrunb⟩ |
      ⟨ic, jc, kc, hdcc, hrunc⟩ | ⟨id, jd, kd, hdcd, hrund⟩ |
      ⟨ie, je, ke, hdce, hrune⟩ | ⟨ig, kg, hdcg, hrung⟩ |
      ⟨lc, li, lb2, ldca, hrunl⟩ | ⟨ti, tj, tk2, hdct, hrunt⟩ |
      ⟨ais, hadca, hrunad⟩
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
    · rw [hdc2] at hdc
      have hviewst := intViewedDoms_of_coherent hview hcoh
      intro hcsat
      obtain ⟨w, hw, hwe⟩ := hcsat
      exact (propNe_safe st i j hviewst).2.1 c hrun2 a hrep.1
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      intro hcsat
      exact (propPlus_safe st i j k).2.1 c hrun2 a hrep.1 (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      intro hcsat
      have hlen : coeffs.length = is.length :=
        hlin _ hdc coeffs is b2 rfl
      exact (propLinLe2_safe st coeffs is b2 hlen).2.1 c hrun2 a hrep.1
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      intro hcsat
      exact (propLeConstHi_safe st i k).2.1 c hrun2 a hrep.1
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      intro hcsat
      exact (propLeConstLo_safe st i k).2.1 c hrun2 a hrep.1
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      intro hcsat
      exact (propLtConstHi_safe st i k).2.1 c hrun2 a hrep.1
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      intro hcsat
      exact (propLtConstLo_safe st i k).2.1 c hrun2 a hrep.1
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      intro hcsat
      exact (propConstEq_safe st i v).2.1 c hrun2 a hrep.1
        (hsol.2 _ hdc)
    · rw [hdca] at hdc
      intro hcsat
      exact (propBoolNot_safe st ia ja).2.1 c hruna a hrep.1
        (hsol.2 _ hdc)
    · rw [hdcb] at hdc
      intro hcsat
      exact (propBoolAnd_safe st ib jb kb).2.1 c hrunb a hrep.1
        (hsol.2 _ hdc)
    · rw [hdcc] at hdc
      intro hcsat
      exact (propBoolOr_safe st ic jc kc).2.1 c hrunc a hrep.1
        (hsol.2 _ hdc)
    · rw [hdcd] at hdc
      intro hcsat
      exact (propMin_safe st id jd kd).2.1 c hrund a hrep.1
        (hsol.2 _ hdc)
    · rw [hdce] at hdc
      intro hcsat
      exact (propMax_safe st ie je ke).2.1 c hrune a hrep.1
        (hsol.2 _ hdc)
    · rw [hdcg] at hdc
      intro hcsat
      exact (propAbs_safe st ig kg).2.1 c hrung a hrep.1
        (hsol.2 _ hdc)
    · rw [ldca] at hdc
      intro hcsat
      have hlenL : lc.length = li.length :=
        hlinE _ hdc lc li lb2 rfl
      exact (propLinEq2_safe st lc li lb2 hlenL).2.1 c hrunl a hrep.1
        (hsol.2 _ hdc)
    · rw [hdct] at hdc
      intro hcsat
      exact (propTimes_safe st ti tj tk2).2.1 c hrunt a hrep.1
        (hsol.2 _ hdc)
    · rw [hadca] at hdc
      intro hcsat
      exact (propAllDiffLCG_safe st ais).2.1 c hrunad a hrep.1
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
      propagatorOfProved dc = some p)
    (hlin : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linLe coeffs is b → coeffs.length = is.length)
    (hlinE : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linEq coeffs is b → coeffs.length = is.length) :
    ∀ (st : State), SolvedBy problem DomConstraint.SatisfiedBy st →
    DomainCoherent problem st →
    ∀ p ∈ props, ∀ (c : Clause), p.run st = .conflict c →
    ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
    ∃ l ∈ c, l.eval a = some true := by
  intro st hsol hcoh p hp c hrun a ha
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
    ⟨lc, li, lb2, ldca, hrunl⟩ | ⟨ti, tj, tk2, hdct, hrunt⟩ |
    ⟨ais, hadca, hrunad⟩
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
  · rw [hdc2] at hdc
    have hviewst := intViewedDoms_of_coherent hview hcoh
    exact (propNe_safe st i j hviewst).2.2 c hrun2 a (hsol a ha).1
      (ha.2 _ hdc)
  · rw [hdc2] at hdc
    exact (propPlus_safe st i j k).2.2 c hrun2 a (hsol a ha).1
      (ha.2 _ hdc)
  · rw [hdc2] at hdc
    have hlen : coeffs.length = is.length :=
      hlin _ hdc coeffs is b2 rfl
    exact propLinLe2_entitled hdc hlen hrun2 a ha
  · rw [hdc2] at hdc
    exact propLeConstHi_entitled hdc hrun2 a ha
  · rw [hdc2] at hdc
    exact propLeConstLo_entitled hdc hrun2 a ha
  · rw [hdc2] at hdc
    exact propLtConstHi_entitled hdc hrun2 a ha
  · rw [hdc2] at hdc
    exact propLtConstLo_entitled hdc hrun2 a ha
  · rw [hdc2] at hdc
    exact propConstEq_entitled hdc hrun2 a ha
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
  · rw [ldca] at hdc
    have hlenL : lc.length = li.length :=
      hlinE _ hdc lc li lb2 rfl
    exact propLinEq2_entitled hdc hlenL hrunl a ha
  · rw [hdct] at hdc
    exact propTimes_entitled hdc hrunt a ha
  · rw [hadca] at hdc
    exact propAllDiffLCG_entitled hdc hrunad hsol a ha


/-! ### The linLe min-sum bound -/

end LeanFzn.Solver.LCG

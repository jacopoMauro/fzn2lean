/-
File: solver/LCG/Proofs/ConstFamilies.lean

Purpose:
  Per-family propagator soundness for the five CONSTANT-BOUND and
  constant-equality families: `leConstHi` / `leConstLo` (compiled
  from `int_le(x, c)` / `int_le(c, x)` and the `int_ge` duals),
  `ltConstHi` / `ltConstLo` (from `int_lt(x, c)` / `int_lt(c, x)`
  and the `int_gt` duals), and `constEq` (from `int_eq(x, c)` with a
  literal constant, and Boolean `x = b`).

  For each family the package carries:

  * the view lemmas (`..._views`): the constraint's semantics at the
    integer (resp. raw Boolean) view of the constrained slot;
  * the order-literal hygiene lemmas (`posLe_norm` / `negLe_norm` /
    `posBool_norm`): `Literal.norm` is the identity on the emitted
    order and canonical Boolean literals;
  * per-family soundness triples (`..._safe`): implied-literal truth
    at every fitting solution, conflict exclusion, conflict-clause
    entitlement — at EVERY state (the constant-bound deductions and
    nogoods are entailed by their own constraint alone);
  * per-family entitlement lemmas (`..._entitled`): the conflict
    clause carries a true literal at every internal problem
    solution, with NO state premises (the truth literal is pinned
    by the constraint itself);
  * per-family reason-validity lemmas (`..._reason_safe` plus
    `..._reason_safe_sat` at the concrete `DomConstraint.SatisfiedBy`
    semantics): `Reason.Valid` plus clause normalization — the
    `ReasonSafeUniv` obligation shape;
  * the standalone B3/B4 registrations (`propagatorOfProvedB3` /
    `propagatorOfProvedB4`) with their membership inversions, run
    inversions, per-family reason bridges, and the three front
    doors (`propagatorsOfProvedB3/B4_safeUniv`, `_entitled`,
    `_reason`) restricted to these families.

  Design, settled affirmatively: a unit clause CAN be its own
  reason. `Reason.Valid` demands clause entailment plus
  pivot-membership; the unit nogoods here are entailed by their own
  constraint ALONE, and the pivot is the sole member.

  This module also hosts the SHARED narrowHi/narrowLo/firstEvent
  inversion helpers and fitting-assignment coherence bridges
  (formerly in Proofs/Propagators.lean): they are pure
  Propagate-level facts needed by both this module and the
  six-family proofs, so they live upstream of both.

Dependencies:
  - solver.LCG.Proofs.Theory: `fits_domMaxI_ge` / `fits_domMinI_le`,
    `narrowHi_conflict_inv` / `narrowLo_conflict_inv`,
    `SolvedBy`, `PropSafeUniv`.
  - solver.LCG.Propagate: the propagator definitions
    (`propLeConstHi`, `propLeConstLo`, `propLtConstHi`,
    `propLtConstLo`, `propConstEq`).
  - solver.LCG.Encoding: `eval_posLe_iff` / `eval_negLe_iff` /
    `eval_posBool_iff`.
  - solver.LCG.Proofs.Run: `ReasonSafeUniv` (the statement shape the
    reason front door discharges for the families).

DAG:
  LCG.Proofs.Theory + LCG.Propagate + LCG.Encoding + LCG.Proofs.Run
    -> LCG.Proofs.ConstFamilies -> LCG.Proofs.Propagators
    (the six-family module; consumes the shared inversions above)
    -> LCG.Certified
-/

import solver.LCG.Proofs.Theory
import solver.LCG.Propagate
import solver.LCG.Encoding
import solver.LCG.Proofs.Run

namespace LeanFzn.Solver.LCG

open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Solver (DomConstraint valueMemB valueMemB_iff)

/-! ## The shared inversions and coherence bridges

These six lemmas are the Propagate-level facts both this module and
the six-family module (Proofs/Propagators.lean) consume; they live
here so that both are downstream of one copy. -/

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

/-! ## Order-literal hygiene

The emitted nogoods are built solely from `posLe`/`negLe`/`posBool`
constructors. `Literal.norm` is the identity on order literals (it
only rewrites negative Boolean literals) and on the normalized
positive Boolean literal `posBool`, so every emitted clause is
normalized by construction. -/

/-- Normalization is the identity on positive order literals. -/
theorem posLe_norm (s : Nat) (k : Int) : (posLe s k).norm = posLe s k :=
  rfl

/-- Normalization is the identity on negative order literals. -/
theorem negLe_norm (s : Nat) (k : Int) : (negLe s k).norm = negLe s k :=
  rfl

/-- Normalization is the identity on the canonical positive Boolean
    literal (`posBool` is already in normalized position). -/
theorem posBool_norm (s : Nat) (b : Bool) :
    (posBool s b).norm = posBool s b :=
  rfl

/-! ## Constraint semantics at the integer / Boolean views -/

/-- The `leConstHi` semantics at the integer view: the constrained
    slot's view exists and is at most `c`. -/
theorem leConstHi_views {a : Assignment} {i : Nat} {c : Int}
    (h : (DomConstraint.leConstHi i c).SatisfiedBy a) :
    ∃ p, slotInt a i = some p ∧ p ≤ c := by
  obtain ⟨p, hread, hle⟩ := h
  exact ⟨p, slotInt_of_int_read hread, hle⟩

/-- The `leConstLo` semantics at the integer view: the constrained
    slot's view exists and is at least `c`. -/
theorem leConstLo_views {a : Assignment} {i : Nat} {c : Int}
    (h : (DomConstraint.leConstLo i c).SatisfiedBy a) :
    ∃ p, slotInt a i = some p ∧ c ≤ p := by
  obtain ⟨p, hread, hle⟩ := h
  exact ⟨p, slotInt_of_int_read hread, hle⟩

/-- The `ltConstHi` semantics at the integer view: the constrained
    slot's view exists and is strictly below `c`. -/
theorem ltConstHi_views {a : Assignment} {i : Nat} {c : Int}
    (h : (DomConstraint.ltConstHi i c).SatisfiedBy a) :
    ∃ p, slotInt a i = some p ∧ p < c := by
  obtain ⟨p, hread, hlt⟩ := h
  exact ⟨p, slotInt_of_int_read hread, hlt⟩

/-- The `ltConstLo` semantics at the integer view: the constrained
    slot's view exists and is strictly above `c`. -/
theorem ltConstLo_views {a : Assignment} {i : Nat} {c : Int}
    (h : (DomConstraint.ltConstLo i c).SatisfiedBy a) :
    ∃ p, slotInt a i = some p ∧ c < p := by
  obtain ⟨p, hread, hgt⟩ := h
  exact ⟨p, slotInt_of_int_read hread, hgt⟩

/-- The `constEq` semantics at the integer view: the constrained
    slot's view IS the constant. -/
theorem constEqInt_views {a : Assignment} {i : Nat} {k : Int}
    (h : (DomConstraint.constEq i (.int k)).SatisfiedBy a) :
    slotInt a i = some k :=
  slotInt_of_int_read h

/-- The `constEq` semantics at the Boolean read: the constrained
    slot carries exactly `.bool b` (definitionally the
    `SatisfiedBy` arm). -/
theorem constEqBool_views {a : Assignment} {i : Nat} {b : Bool}
    (h : (DomConstraint.constEq i (.bool b)).SatisfiedBy a) :
    a[i]? = some (.bool b) :=
  h

/-! ## propLeConstHi soundness: the `x ≤ c` family -/

/-- The propagator of a `leConstHi i c` constraint: implied-literal
    soundness, conflict soundness, and entitlement, at every state
    (the six-family `propLe_safe` triple shape,
    Propagators.lean). All three bullets need only the constraint's
    own semantics at the solution: the implied literal `posLe i c`
    is true at every fitting solution of the constraint (`x ≤ c` —
    the domain extrema only decide WHETHER an emission fires); a
    conflict fires only when the domain's minimum already exceeds
    `c`, contradicting every fitting solution; and the conflict
    clause `[posLe i c]` then carries the true literal `posLe i c`
    itself. -/
theorem propLeConstHi_safe (st : State) (i : Nat) (c : Int) :
    (∀ l r, propLeConstHi st i c = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.leConstHi i c).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ cc, propLeConstHi st i c = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.leConstHi i c).SatisfiedBy a → False) ∧
    (∀ cc, propLeConstHi st i c = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.leConstHi i c).SatisfiedBy a →
        ∃ l ∈ cc, l.eval a = some true) := by
  constructor
  · -- implied: the head is posLe i c, true by x ≤ c alone
    intro l r hrun a _ hcons
    obtain ⟨hl, _⟩ := narrowHi_implied_inv hrun
    subst hl
    obtain ⟨p, hread, hle⟩ := hcons
    rw [eval_posLe_iff]
    exact ⟨p, slotInt_of_int_read hread, hle⟩
  · constructor
    · -- conflict: mn > c excludes every fitting solution (mn ≤ x ≤ c)
      intro cc hrun a hfit hcons
      obtain ⟨mn, _, hmn, _, hgt, _⟩ := narrowHi_conflict_inv hrun
      obtain ⟨p, hread, hle⟩ := hcons
      have hx : slotInt a i = some p := slotInt_of_int_read hread
      have hmnx : mn ≤ p := fits_min_bound hfit hmn hx
      omega
    · -- entitlement: the clause's only literal is true at the solution
      intro cc hrun a _ hcons
      obtain ⟨_, _, _, _, _, hcc⟩ := narrowHi_conflict_inv hrun
      obtain ⟨p, hread, hle⟩ := hcons
      refine ⟨posLe i c, ?_, ?_⟩
      · rw [hcc]
        exact List.mem_cons_self
      · rw [eval_posLe_iff]
        exact ⟨p, slotInt_of_int_read hread, hle⟩

/-- The per-family entitlement: for a `leConstHi` constraint in the
    problem, the propagator's conflict clause carries a true literal
    at every internal problem solution.

    NOTE: the six-family sibling `propagatorOf_leSlot_entitled`
    takes `SolvedBy problem … st` because the `leSlot` truth
    literal needs the solution to fit the STATE's domains. The
    `leConstHi` truth literal `posLe i c` is pinned by the
    constraint alone, so NO state premise (and no `DomainCoherent`)
    is needed — this lemma is strictly stronger than the requested
    `SolvedBy`-relativized shape, which follows from it trivially. -/
theorem propLeConstHi_entitled
    {problem : Problem DomConstraint Unit}
    {st : State} {i : Nat} {c : Int} {cc : Clause}
    (hprob : DomConstraint.leConstHi i c ∈ problem.constraints)
    (hrun : propLeConstHi st i c = .conflict cc)
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ cc, l.eval a = some true := by
  obtain ⟨_, _, _, _, _, hcc⟩ := narrowHi_conflict_inv hrun
  obtain ⟨p, hread, hle⟩ := leConstHi_views (ha.2 _ hprob)
  refine ⟨posLe i c, ?_, ?_⟩
  · rw [hcc]
    exact List.mem_cons_self
  · rw [eval_posLe_iff]
    exact ⟨p, hread, hle⟩

/-- The reason-validity lemma for the `leConstHi` family: an implied
    emission of `propLeConstHi` carries a valid (entailed,
    pivot-member) and normalized reason clause — the unit nogood
    `[posLe i c]` is entailed by the constraint `.leConstHi i c` at
    every internal problem solution, for any constraint semantics
    implying `SatisfiedBy` on the problem's constraints.

    The `himp` bridge premise is REQUIRED for an abstract
    `constraintHolds` (with `constraintHolds := fun _ _ => True` every
    assignment is a solution and `x = c+1` falsifies the nogood). No
    `SolvedBy` / `DomainCoherent` premise is needed: the clause is
    unconditionally entailed by its own constraint. -/
theorem propLeConstHi_reason_safe
    {problem : Problem DomConstraint Unit}
    {constraintHolds : DomConstraint → Assignment → Prop}
    {st : State} {i : Nat} {c : Int} {l : Literal} {r : Reason}
    (himp : ∀ c a, c ∈ problem.constraints →
      constraintHolds c a → c.SatisfiedBy a)
    (hprob : DomConstraint.leConstHi i c ∈ problem.constraints)
    (hrun : propLeConstHi st i c = .implied l r) :
    Reason.Valid problem constraintHolds r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  obtain ⟨hl, hcl⟩ := narrowHi_implied_inv hrun
  refine ⟨⟨?_, by subst hl; rw [hcl]; simp⟩, ?_⟩
  · -- EntailedBy: the unit clause's only literal is true at every
    -- ProblemSolution (constraint semantics via himp)
    intro a ha
    obtain ⟨p, hread, hle⟩ :=
      leConstHi_views (himp _ a hprob (ha.2 _ hprob))
    refine ⟨posLe i c, ?_, ?_⟩
    · rw [hcl]
      exact List.mem_cons_self
    · rw [eval_posLe_iff]
      exact ⟨p, hread, hle⟩
  · -- normalization: the only literal is an order literal
    intro q hq
    rw [hcl] at hq
    rcases List.mem_cons.mp hq with hq | hq
    · subst hq
      exact (posLe_norm i c).symm
    · exact absurd hq (by simp)

/-- The canonical `DomConstraint.SatisfiedBy` instantiation: no
    bridge premise. This is the shape the engine's front door uses. -/
theorem propLeConstHi_reason_safe_sat
    {problem : Problem DomConstraint Unit}
    {st : State} {i : Nat} {c : Int} {l : Literal} {r : Reason}
    (hprob : DomConstraint.leConstHi i c ∈ problem.constraints)
    (hrun : propLeConstHi st i c = .implied l r) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l ∧
      (∀ q ∈ r.clause, q = q.norm) :=
  propLeConstHi_reason_safe (fun _ _ _ h => h) hprob hrun

/-! ## propLeConstLo soundness: the `c ≤ x` family -/

/-- The propagator of a `leConstLo i c` constraint: the dual triple of
    `propLeConstHi_safe`. -/
theorem propLeConstLo_safe (st : State) (i : Nat) (c : Int) :
    (∀ l r, propLeConstLo st i c = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.leConstLo i c).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ cc, propLeConstLo st i c = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.leConstLo i c).SatisfiedBy a → False) ∧
    (∀ cc, propLeConstLo st i c = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.leConstLo i c).SatisfiedBy a →
        ∃ l ∈ cc, l.eval a = some true) := by
  constructor
  · -- implied: the head is negLe i (c-1), true by c ≤ x alone
    intro l r hrun a _ hcons
    obtain ⟨hl, _⟩ := narrowLo_implied_inv hrun
    subst hl
    obtain ⟨p, hread, hle⟩ := hcons
    rw [eval_negLe_iff]
    exact ⟨p, slotInt_of_int_read hread, by omega⟩
  · constructor
    · -- conflict: mx < c excludes every fitting solution (c ≤ x ≤ mx)
      intro cc hrun a hfit hcons
      obtain ⟨_, mx, _, hmx, hlt, _⟩ := narrowLo_conflict_inv hrun
      obtain ⟨p, hread, hle⟩ := hcons
      have hx : slotInt a i = some p := slotInt_of_int_read hread
      have hmxy : p ≤ mx := fits_max_bound hfit hmx hx
      omega
    · -- entitlement: the clause's only literal is true at the solution
      intro cc hrun a _ hcons
      obtain ⟨_, _, _, _, _, hcc⟩ := narrowLo_conflict_inv hrun
      obtain ⟨p, hread, hle⟩ := hcons
      refine ⟨negLe i (c - 1), ?_, ?_⟩
      · rw [hcc]
        exact List.mem_cons_self
      · rw [eval_negLe_iff]
        exact ⟨p, slotInt_of_int_read hread, by omega⟩

/-- The per-family entitlement for the `leConstLo` family (same
    honesty note as `propLeConstHi_entitled`: no state premises
    needed — the truth literal is pinned by the constraint alone). -/
theorem propLeConstLo_entitled
    {problem : Problem DomConstraint Unit}
    {st : State} {i : Nat} {c : Int} {cc : Clause}
    (hprob : DomConstraint.leConstLo i c ∈ problem.constraints)
    (hrun : propLeConstLo st i c = .conflict cc)
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ cc, l.eval a = some true := by
  obtain ⟨_, _, _, _, _, hcc⟩ := narrowLo_conflict_inv hrun
  obtain ⟨p, hread, hle⟩ := leConstLo_views (ha.2 _ hprob)
  refine ⟨negLe i (c - 1), ?_, ?_⟩
  · rw [hcc]
    exact List.mem_cons_self
  · rw [eval_negLe_iff]
    exact ⟨p, hread, by omega⟩

/-- The reason-validity lemma for the `leConstLo` family (same shape
    and honesty notes as `propLeConstHi_reason_safe`). -/
theorem propLeConstLo_reason_safe
    {problem : Problem DomConstraint Unit}
    {constraintHolds : DomConstraint → Assignment → Prop}
    {st : State} {i : Nat} {c : Int} {l : Literal} {r : Reason}
    (himp : ∀ c a, c ∈ problem.constraints →
      constraintHolds c a → c.SatisfiedBy a)
    (hprob : DomConstraint.leConstLo i c ∈ problem.constraints)
    (hrun : propLeConstLo st i c = .implied l r) :
    Reason.Valid problem constraintHolds r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  obtain ⟨hl, hcl⟩ := narrowLo_implied_inv hrun
  refine ⟨⟨?_, by subst hl; rw [hcl]; simp⟩, ?_⟩
  · intro a ha
    obtain ⟨p, hread, hle⟩ :=
      leConstLo_views (himp _ a hprob (ha.2 _ hprob))
    refine ⟨negLe i (c - 1), ?_, ?_⟩
    · rw [hcl]
      exact List.mem_cons_self
    · rw [eval_negLe_iff]
      exact ⟨p, hread, by omega⟩
  · intro q hq
    rw [hcl] at hq
    rcases List.mem_cons.mp hq with hq | hq
    · subst hq
      exact (negLe_norm i (c - 1)).symm
    · exact absurd hq (by simp)

/-- The canonical `DomConstraint.SatisfiedBy` instantiation. -/
theorem propLeConstLo_reason_safe_sat
    {problem : Problem DomConstraint Unit}
    {st : State} {i : Nat} {c : Int} {l : Literal} {r : Reason}
    (hprob : DomConstraint.leConstLo i c ∈ problem.constraints)
    (hrun : propLeConstLo st i c = .implied l r) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l ∧
      (∀ q ∈ r.clause, q = q.norm) :=
  propLeConstLo_reason_safe (fun _ _ _ h => h) hprob hrun

/-! ## propLtConstHi soundness: the `x < c` family -/

/-- The propagator of a `ltConstHi i c` constraint: implied-literal
    soundness, conflict soundness, and entitlement, at every state
    (the six-family `propLt_safe` triple shape). All three bullets
    need only the constraint's own semantics at the solution: the
    implied literal `posLe i (c − 1)` is true at every fitting
    solution of the constraint (`p < c` gives `p ≤ c − 1`); a
    conflict fires only when the domain's minimum is already `≥ c`,
    contradicting every fitting solution; and the conflict clause
    `[posLe i (c − 1)]` then carries the true literal
    `posLe i (c − 1)` itself. -/
theorem propLtConstHi_safe (st : State) (i : Nat) (c : Int) :
    (∀ l r, propLtConstHi st i c = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.ltConstHi i c).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ cc, propLtConstHi st i c = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.ltConstHi i c).SatisfiedBy a → False) ∧
    (∀ cc, propLtConstHi st i c = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.ltConstHi i c).SatisfiedBy a →
        ∃ l ∈ cc, l.eval a = some true) := by
  constructor
  · -- implied: the head is posLe i (c-1), true by p < c alone
    intro l r hrun a _ hcons
    obtain ⟨hl, _⟩ := narrowHi_implied_inv hrun
    subst hl
    obtain ⟨p, hread, hlt⟩ := hcons
    rw [eval_posLe_iff]
    exact ⟨p, slotInt_of_int_read hread, by omega⟩
  · constructor
    · -- conflict: mn > c-1 excludes every fitting solution
        -- (mn ≤ p < c)
      intro cc hrun a hfit hcons
      obtain ⟨mn, _, hmn, _, hgt, _⟩ := narrowHi_conflict_inv hrun
      obtain ⟨p, hread, hlt⟩ := hcons
      have hx : slotInt a i = some p := slotInt_of_int_read hread
      have hmnx : mn ≤ p := fits_min_bound hfit hmn hx
      omega
    · -- entitlement: the clause's only literal is true at the solution
      intro cc hrun a _ hcons
      obtain ⟨_, _, _, _, _, hcc⟩ := narrowHi_conflict_inv hrun
      obtain ⟨p, hread, hlt⟩ := hcons
      refine ⟨posLe i (c - 1), ?_, ?_⟩
      · rw [hcc]
        exact List.mem_cons_self
      · rw [eval_posLe_iff]
        exact ⟨p, slotInt_of_int_read hread, by omega⟩

/-- The per-family entitlement: for a `ltConstHi` constraint in the
    problem, the propagator's conflict clause carries a true literal
    at every internal problem solution. No state premise is needed —
    the truth literal `posLe i (c − 1)` is pinned by the constraint
    alone. -/
theorem propLtConstHi_entitled
    {problem : Problem DomConstraint Unit}
    {st : State} {i : Nat} {c : Int} {cc : Clause}
    (hprob : DomConstraint.ltConstHi i c ∈ problem.constraints)
    (hrun : propLtConstHi st i c = .conflict cc)
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ cc, l.eval a = some true := by
  obtain ⟨_, _, _, _, _, hcc⟩ := narrowHi_conflict_inv hrun
  obtain ⟨p, hread, hlt⟩ := ltConstHi_views (ha.2 _ hprob)
  refine ⟨posLe i (c - 1), ?_, ?_⟩
  · rw [hcc]
    exact List.mem_cons_self
  · rw [eval_posLe_iff]
    exact ⟨p, hread, by omega⟩

/-- The reason-validity lemma for the `ltConstHi` family: an implied
    emission of `propLtConstHi` carries a valid (entitled,
    pivot-member) and normalized reason clause — the unit nogood
    `[posLe i (c − 1)]` is entailed by the constraint
    `.ltConstHi i c` at every internal problem solution, for any
    constraint semantics implying `SatisfiedBy` on the problem's
    constraints (the `himp` bridge — REQUIRED for an abstract
    `constraintHolds`). No `SolvedBy` / `DomainCoherent` premise is
    needed. -/
theorem propLtConstHi_reason_safe
    {problem : Problem DomConstraint Unit}
    {constraintHolds : DomConstraint → Assignment → Prop}
    {st : State} {i : Nat} {c : Int} {l : Literal} {r : Reason}
    (himp : ∀ c a, c ∈ problem.constraints →
      constraintHolds c a → c.SatisfiedBy a)
    (hprob : DomConstraint.ltConstHi i c ∈ problem.constraints)
    (hrun : propLtConstHi st i c = .implied l r) :
    Reason.Valid problem constraintHolds r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  obtain ⟨hl, hcl⟩ := narrowHi_implied_inv hrun
  refine ⟨⟨?_, by subst hl; rw [hcl]; simp⟩, ?_⟩
  · -- EntitledBy: the unit clause's only literal is true at every
    -- ProblemSolution (constraint semantics via himp)
    intro a ha
    obtain ⟨p, hread, hlt⟩ :=
      ltConstHi_views (himp _ a hprob (ha.2 _ hprob))
    refine ⟨posLe i (c - 1), ?_, ?_⟩
    · rw [hcl]
      exact List.mem_cons_self
    · rw [eval_posLe_iff]
      exact ⟨p, hread, by omega⟩
  · -- normalization: the only literal is an order literal
    intro q hq
    rw [hcl] at hq
    rcases List.mem_cons.mp hq with hq | hq
    · subst hq
      exact (posLe_norm i (c - 1)).symm
    · exact absurd hq (by simp)

/-- The canonical `DomConstraint.SatisfiedBy` instantiation: no
    bridge premise. This is the shape the engine's front door uses. -/
theorem propLtConstHi_reason_safe_sat
    {problem : Problem DomConstraint Unit}
    {st : State} {i : Nat} {c : Int} {l : Literal} {r : Reason}
    (hprob : DomConstraint.ltConstHi i c ∈ problem.constraints)
    (hrun : propLtConstHi st i c = .implied l r) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l ∧
      (∀ q ∈ r.clause, q = q.norm) :=
  propLtConstHi_reason_safe (fun _ _ _ h => h) hprob hrun

/-! ## propLtConstLo soundness: the `c < x` family -/

/-- The propagator of a `ltConstLo i c` constraint: the dual triple
    of `propLtConstHi_safe`. -/
theorem propLtConstLo_safe (st : State) (i : Nat) (c : Int) :
    (∀ l r, propLtConstLo st i c = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.ltConstLo i c).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ cc, propLtConstLo st i c = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.ltConstLo i c).SatisfiedBy a → False) ∧
    (∀ cc, propLtConstLo st i c = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.ltConstLo i c).SatisfiedBy a →
        ∃ l ∈ cc, l.eval a = some true) := by
  constructor
  · -- implied: the head is negLe i (c+1-1), true by c < p alone
    intro l r hrun a _ hcons
    obtain ⟨hl, _⟩ := narrowLo_implied_inv hrun
    subst hl
    obtain ⟨p, hread, hgt⟩ := hcons
    rw [eval_negLe_iff]
    exact ⟨p, slotInt_of_int_read hread, by omega⟩
  · constructor
    · -- conflict: mx < c+1 excludes every fitting solution
        -- (c < p ≤ mx)
      intro cc hrun a hfit hcons
      obtain ⟨_, mx, _, hmx, hlt, _⟩ := narrowLo_conflict_inv hrun
      obtain ⟨p, hread, hgt⟩ := hcons
      have hx : slotInt a i = some p := slotInt_of_int_read hread
      have hmxy : p ≤ mx := fits_max_bound hfit hmx hx
      omega
    · -- entitlement: the clause's only literal is true at the solution
      intro cc hrun a _ hcons
      obtain ⟨_, _, _, _, _, hcc⟩ := narrowLo_conflict_inv hrun
      obtain ⟨p, hread, hgt⟩ := hcons
      refine ⟨negLe i c, ?_, ?_⟩
      · rw [hcc]
        exact List.mem_cons_self
      · rw [eval_negLe_iff]
        exact ⟨p, slotInt_of_int_read hread, by omega⟩

/-- The per-family entitlement for the `ltConstLo` family (same
    honesty note as `propLtConstHi_entitled`: no state premises
    needed — the truth literal is pinned by the constraint alone). -/
theorem propLtConstLo_entitled
    {problem : Problem DomConstraint Unit}
    {st : State} {i : Nat} {c : Int} {cc : Clause}
    (hprob : DomConstraint.ltConstLo i c ∈ problem.constraints)
    (hrun : propLtConstLo st i c = .conflict cc)
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ cc, l.eval a = some true := by
  obtain ⟨_, _, _, _, _, hcc⟩ := narrowLo_conflict_inv hrun
  obtain ⟨p, hread, hgt⟩ := ltConstLo_views (ha.2 _ hprob)
  refine ⟨negLe i c, ?_, ?_⟩
  · rw [hcc]
    exact List.mem_cons_self
  · rw [eval_negLe_iff]
    exact ⟨p, hread, by omega⟩

/-- The reason-validity lemma for the `ltConstLo` family (same shape
    and honesty notes as `propLtConstHi_reason_safe`). The pivot is
    narrowLo's implied head `negLe i (c + 1 − 1)`, a member of the
    clause `[negLe i c]` by the integer arithmetic
    `c + 1 − 1 = c`. -/
theorem propLtConstLo_reason_safe
    {problem : Problem DomConstraint Unit}
    {constraintHolds : DomConstraint → Assignment → Prop}
    {st : State} {i : Nat} {c : Int} {l : Literal} {r : Reason}
    (himp : ∀ c a, c ∈ problem.constraints →
      constraintHolds c a → c.SatisfiedBy a)
    (hprob : DomConstraint.ltConstLo i c ∈ problem.constraints)
    (hrun : propLtConstLo st i c = .implied l r) :
    Reason.Valid problem constraintHolds r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  obtain ⟨hl, hcl⟩ := narrowLo_implied_inv hrun
  refine ⟨⟨?_, by
    subst hl
    rw [hcl]
    have heq : c + 1 - 1 = c := by omega
    rw [heq]
    simp⟩, ?_⟩
  · -- EntitledBy: the unit clause's only literal is true at every
    -- ProblemSolution (constraint semantics via himp)
    intro a ha
    obtain ⟨p, hread, hgt⟩ :=
      ltConstLo_views (himp _ a hprob (ha.2 _ hprob))
    refine ⟨negLe i c, ?_, ?_⟩
    · rw [hcl]
      exact List.mem_cons_self
    · rw [eval_negLe_iff]
      exact ⟨p, hread, by omega⟩
  · -- normalization: the only literal is an order literal
    intro q hq
    rw [hcl] at hq
    rcases List.mem_cons.mp hq with hq | hq
    · subst hq
      exact (negLe_norm i c).symm
    · exact absurd hq (by simp)

/-- The canonical `DomConstraint.SatisfiedBy` instantiation. -/
theorem propLtConstLo_reason_safe_sat
    {problem : Problem DomConstraint Unit}
    {st : State} {i : Nat} {c : Int} {l : Literal} {r : Reason}
    (hprob : DomConstraint.ltConstLo i c ∈ problem.constraints)
    (hrun : propLtConstLo st i c = .implied l r) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l ∧
      (∀ q ∈ r.clause, q = q.norm) :=
  propLtConstLo_reason_safe (fun _ _ _ h => h) hprob hrun

/-! ## propConstEq soundness: the `x = v` family, integer constants -/

/-- The propagator of a `constEq i (.int k)` constraint: the
    b3-style triple, at every state. The constraint pins the slot's
    integer view to `k`, so the implied heads (`posLe i k` from
    narrowHi, `negLe i (k − 1)` from narrowLo) are true at every
    fitting solution by `k ≤ k` / `¬(k ≤ k − 1)` alone; a narrowHi
    conflict fires only when `mn > k` and a narrowLo conflict only
    when `mx < k`, both contradicting `slotInt a i = some k`; and
    each conflict clause is its own true-literal witness. -/
theorem propConstEqInt_safe (st : State) (i : Nat) (k : Int) :
    (∀ l r, propConstEq st i (.int k) = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.constEq i (.int k)).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ cc, propConstEq st i (.int k) = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.constEq i (.int k)).SatisfiedBy a → False) ∧
    (∀ cc, propConstEq st i (.int k) = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.constEq i (.int k)).SatisfiedBy a →
        ∃ l ∈ cc, l.eval a = some true) := by
  constructor
  · -- implied: either head is true at every fitting solution,
    -- because the constraint pins the view to k
    intro l r hrun a _ hcons
    have hx : slotInt a i = some k := constEqInt_views hcons
    simp only [propConstEq] at hrun
    rcases firstEvent_mem [narrowHi st i k [posLe i k],
        narrowLo st i k [negLe i (k - 1)]] (.implied l r) hrun with
      hstable | hmem
    · exact absurd hstable (by intro hc; cases hc)
    · rcases List.mem_cons.mp hmem with harm | harm
      · obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm harm)
        subst hl
        rw [eval_posLe_iff]
        exact ⟨k, hx, by omega⟩
      · obtain ⟨hl, _⟩ := narrowLo_implied_inv
          (Eq.symm (List.mem_singleton.mp harm))
        subst hl
        rw [eval_negLe_iff]
        exact ⟨k, hx, by omega⟩
  · constructor
    · -- conflict: mn > k or mx < k contradicts slotInt a i = some k
      intro cc hrun a hfit hcons
      have hx : slotInt a i = some k := constEqInt_views hcons
      simp only [propConstEq] at hrun
      rcases firstEvent_mem [narrowHi st i k [posLe i k],
          narrowLo st i k [negLe i (k - 1)]] (.conflict cc) hrun with
        hstable | hmem
      · exact absurd hstable (by intro hc; cases hc)
      · rcases List.mem_cons.mp hmem with harm | harm
        · obtain ⟨mn, _, hmn, _, _, _⟩ :=
            narrowHi_conflict_inv (Eq.symm harm)
          have hmnx : mn ≤ k := fits_min_bound hfit hmn hx
          omega
        · obtain ⟨_, mx, _, hmx, _, _⟩ :=
            narrowLo_conflict_inv (Eq.symm (List.mem_singleton.mp harm))
          have hmxy : k ≤ mx := fits_max_bound hfit hmx hx
          omega
    · -- entitlement: each conflict clause's only literal is true at
      -- the solution (x = k entails x ≤ k and x ≥ k)
      intro cc hrun a _ hcons
      have hx : slotInt a i = some k := constEqInt_views hcons
      simp only [propConstEq] at hrun
      rcases firstEvent_mem [narrowHi st i k [posLe i k],
          narrowLo st i k [negLe i (k - 1)]] (.conflict cc) hrun with
        hstable | hmem
      · exact absurd hstable (by intro hc; cases hc)
      · rcases List.mem_cons.mp hmem with harm | harm
        · obtain ⟨_, _, _, _, _, hcc⟩ :=
            narrowHi_conflict_inv (Eq.symm harm)
          refine ⟨posLe i k, ?_, ?_⟩
          · rw [hcc]
            exact List.mem_cons_self
          · rw [eval_posLe_iff]
            exact ⟨k, hx, by omega⟩
        · obtain ⟨_, _, _, _, _, hcc⟩ :=
            narrowLo_conflict_inv (Eq.symm (List.mem_singleton.mp harm))
          refine ⟨negLe i (k - 1), ?_, ?_⟩
          · rw [hcc]
            exact List.mem_cons_self
          · rw [eval_negLe_iff]
            exact ⟨k, hx, by omega⟩

/-- The per-family entitlement for the integer `constEq`
    sub-family: the conflict clause (whichever bound fired) carries
    a true literal at every internal problem solution. -/
theorem propConstEqInt_entitled
    {problem : Problem DomConstraint Unit}
    {st : State} {i : Nat} {k : Int} {cc : Clause}
    (hprob : DomConstraint.constEq i (.int k) ∈ problem.constraints)
    (hrun : propConstEq st i (.int k) = .conflict cc)
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ cc, l.eval a = some true := by
  have hx : slotInt a i = some k := constEqInt_views (ha.2 _ hprob)
  simp only [propConstEq] at hrun
  rcases firstEvent_mem [narrowHi st i k [posLe i k],
      narrowLo st i k [negLe i (k - 1)]] (.conflict cc) hrun with
    hstable | hmem
  · exact absurd hstable (by intro hc; cases hc)
  · rcases List.mem_cons.mp hmem with harm | harm
    · obtain ⟨_, _, _, _, _, hcc⟩ := narrowHi_conflict_inv (Eq.symm harm)
      refine ⟨posLe i k, ?_, ?_⟩
      · rw [hcc]
        exact List.mem_cons_self
      · rw [eval_posLe_iff]
        exact ⟨k, hx, by omega⟩
    · obtain ⟨_, _, _, _, _, hcc⟩ :=
        narrowLo_conflict_inv (Eq.symm (List.mem_singleton.mp harm))
      refine ⟨negLe i (k - 1), ?_, ?_⟩
      · rw [hcc]
        exact List.mem_cons_self
      · rw [eval_negLe_iff]
        exact ⟨k, hx, by omega⟩

/-- The reason-validity lemma for the integer `constEq`
    sub-family: each implied emission carries the unit nogood of its
    own bound (`[posLe i k]` resp. `[negLe i (k − 1)]`), entailed by
    `x = k` at every internal problem solution (the `himp` bridge,
    as in the constant-bound families). -/
theorem propConstEqInt_reason_safe
    {problem : Problem DomConstraint Unit}
    {constraintHolds : DomConstraint → Assignment → Prop}
    {st : State} {i : Nat} {k : Int} {l : Literal} {r : Reason}
    (himp : ∀ c a, c ∈ problem.constraints →
      constraintHolds c a → c.SatisfiedBy a)
    (hprob : DomConstraint.constEq i (.int k) ∈ problem.constraints)
    (hrun : propConstEq st i (.int k) = .implied l r) :
    Reason.Valid problem constraintHolds r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  simp only [propConstEq] at hrun
  rcases firstEvent_mem [narrowHi st i k [posLe i k],
      narrowLo st i k [negLe i (k - 1)]] (.implied l r) hrun with
    hstable | hmem
  · exact absurd hstable (by intro hc; cases hc)
  · rcases List.mem_cons.mp hmem with harm | harm
    · obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (Eq.symm harm)
      refine ⟨⟨?_, by subst hl; rw [hcl]; simp⟩, ?_⟩
      · intro a ha
        have hx : slotInt a i = some k :=
          constEqInt_views (himp _ a hprob (ha.2 _ hprob))
        refine ⟨posLe i k, ?_, ?_⟩
        · rw [hcl]
          exact List.mem_cons_self
        · rw [eval_posLe_iff]
          exact ⟨k, hx, by omega⟩
      · intro q hq
        rw [hcl] at hq
        rcases List.mem_cons.mp hq with hq | hq
        · subst hq
          exact (posLe_norm i k).symm
        · exact absurd hq (by simp)
    · obtain ⟨hl, hcl⟩ := narrowLo_implied_inv
        (Eq.symm (List.mem_singleton.mp harm))
      refine ⟨⟨?_, by subst hl; rw [hcl]; simp⟩, ?_⟩
      · intro a ha
        have hx : slotInt a i = some k :=
          constEqInt_views (himp _ a hprob (ha.2 _ hprob))
        refine ⟨negLe i (k - 1), ?_, ?_⟩
        · rw [hcl]
          exact List.mem_cons_self
        · rw [eval_negLe_iff]
          exact ⟨k, hx, by omega⟩
      · intro q hq
        rw [hcl] at hq
        rcases List.mem_cons.mp hq with hq | hq
        · subst hq
          exact (negLe_norm i (k - 1)).symm
        · exact absurd hq (by simp)

/-- The canonical `DomConstraint.SatisfiedBy` instantiation. -/
theorem propConstEqInt_reason_safe_sat
    {problem : Problem DomConstraint Unit}
    {st : State} {i : Nat} {k : Int} {l : Literal} {r : Reason}
    (hprob : DomConstraint.constEq i (.int k) ∈ problem.constraints)
    (hrun : propConstEq st i (.int k) = .implied l r) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l ∧
      (∀ q ∈ r.clause, q = q.norm) :=
  propConstEqInt_reason_safe (fun _ _ _ h => h) hprob hrun

/-! ## propConstEq soundness: the `x = v` family, Boolean constants -/

/-- The propagator of a `constEq i (.bool b)` constraint: the
    b3-style triple, at every state. The implied head is the
    canonical Boolean literal `posBool i b`, true at every fitting
    solution because `SatisfiedBy` IS the raw read
    `a[i]? = some (.bool b)`; a conflict fires only when the domain
    contains no `.bool b` at all, when no fitting assignment can
    exist; the conflict clause `[posBool i b]` is its own true
    literal at every solution. -/
theorem propConstEqBool_safe (st : State) (i : Nat) (b : Bool) :
    (∀ l r, propConstEq st i (.bool b) = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.constEq i (.bool b)).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ cc, propConstEq st i (.bool b) = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.constEq i (.bool b)).SatisfiedBy a → False) ∧
    (∀ cc, propConstEq st i (.bool b) = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.constEq i (.bool b)).SatisfiedBy a →
        ∃ l ∈ cc, l.eval a = some true) := by
  constructor
  · -- implied: the head is posBool i b, true by the raw read
    intro l r hrun a _ hcons
    simp only [propConstEq] at hrun
    split at hrun
    · split at hrun
      · exact absurd hrun (by intro hc; cases hc)
      · injection hrun with hl _
        subst hl
        exact (eval_posBool_iff a i b).mpr hcons
    · exact absurd hrun (by intro hc; cases hc)
  · constructor
    · -- conflict: no .bool b in the domain contradicts the raw read
      intro cc hrun a hfit hcons
      simp only [propConstEq] at hrun
      split at hrun
      · split at hrun
        · exact absurd hrun (by intro hc; cases hc)
        · exact absurd hrun (by intro hc; cases hc)
      · rename_i hmem
        exact hmem (valueMemB_iff.mpr (hfit.2 i (.bool b) hcons))
    · -- entitlement: the clause's only literal is true at the solution
      intro cc hrun a _ hcons
      simp only [propConstEq] at hrun
      split at hrun
      · split at hrun
        · exact absurd hrun (by intro hc; cases hc)
        · exact absurd hrun (by intro hc; cases hc)
      · rename_i _
        injection hrun with hcc
        subst hcc
        refine ⟨posBool i b, List.mem_cons_self, ?_⟩
        exact (eval_posBool_iff a i b).mpr hcons

/-- The per-family entitlement for the Boolean `constEq`
    sub-family. -/
theorem propConstEqBool_entitled
    {problem : Problem DomConstraint Unit}
    {st : State} {i : Nat} {b : Bool} {cc : Clause}
    (hprob : DomConstraint.constEq i (.bool b) ∈ problem.constraints)
    (hrun : propConstEq st i (.bool b) = .conflict cc)
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ cc, l.eval a = some true := by
  simp only [propConstEq] at hrun
  split at hrun
  · split at hrun
    · exact absurd hrun (by intro hc; cases hc)
    · exact absurd hrun (by intro hc; cases hc)
  · rename_i _
    injection hrun with hcc
    subst hcc
    refine ⟨posBool i b, List.mem_cons_self, ?_⟩
    exact (eval_posBool_iff a i b).mpr (ha.2 _ hprob)

/-- The reason-validity lemma for the Boolean `constEq`
    sub-family: the implied emission carries the unit nogood
    `[posBool i b]`, entailed by `x = b` at every internal problem
    solution (the `himp` bridge — with
    `constraintHolds := fun _ _ => True` an assignment reading
    `.bool ¬b` at the slot would falsify it). -/
theorem propConstEqBool_reason_safe
    {problem : Problem DomConstraint Unit}
    {constraintHolds : DomConstraint → Assignment → Prop}
    {st : State} {i : Nat} {b : Bool} {l : Literal} {r : Reason}
    (himp : ∀ c a, c ∈ problem.constraints →
      constraintHolds c a → c.SatisfiedBy a)
    (hprob : DomConstraint.constEq i (.bool b) ∈ problem.constraints)
    (hrun : propConstEq st i (.bool b) = .implied l r) :
    Reason.Valid problem constraintHolds r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  simp only [propConstEq] at hrun
  split at hrun
  · split at hrun
    · exact absurd hrun (by intro hc; cases hc)
    · injection hrun with hl hr
      subst hl
      subst hr
      refine ⟨⟨?_, by simp⟩, ?_⟩
      · intro a ha
        refine ⟨posBool i b, List.mem_cons_self, ?_⟩
        exact (eval_posBool_iff a i b).mpr
          (himp _ a hprob (ha.2 _ hprob))
      · intro q hq
        rcases List.mem_cons.mp hq with hq | hq
        · subst hq
          exact (posBool_norm i b).symm
        · exact absurd hq (by simp)
  · exact absurd hrun (by intro hc; cases hc)

/-- The canonical `DomConstraint.SatisfiedBy` instantiation. -/
theorem propConstEqBool_reason_safe_sat
    {problem : Problem DomConstraint Unit}
    {st : State} {i : Nat} {b : Bool} {l : Literal} {r : Reason}
    (hprob : DomConstraint.constEq i (.bool b) ∈ problem.constraints)
    (hrun : propConstEq st i (.bool b) = .implied l r) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l ∧
      (∀ q ∈ r.clause, q = q.norm) :=
  propConstEqBool_reason_safe (fun _ _ _ h => h) hprob hrun

/-! ## propConstEq over arbitrary constants

The set/array arms of `propConstEq` are constantly `.stable`, so
their obligations hold vacuously; these dispatchers reduce the
general-`v` obligations to the integer and Boolean sub-families. -/

/-- The no-emission schema: a propagator that is constantly `.stable`
    satisfies every obligation vacuously. -/
theorem propConstEqNoEmit_safe (st : State) (i : Nat) (v : Value)
    (hst : propConstEq st i v = .stable) :
    (∀ l r, propConstEq st i v = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.constEq i v).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ cc, propConstEq st i v = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.constEq i v).SatisfiedBy a → False) ∧
    (∀ cc, propConstEq st i v = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.constEq i v).SatisfiedBy a →
        ∃ l ∈ cc, l.eval a = some true) := by
  refine ⟨fun l r h => ?_, fun cc h => ?_, fun cc h => ?_⟩ <;>
    · rw [hst] at h
      exact absurd h (by intro hc; cases hc)

/-- The general-`v` soundness triple for `propConstEq`. -/
theorem propConstEq_safe (st : State) (i : Nat) (v : Value) :
    (∀ l r, propConstEq st i v = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.constEq i v).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ cc, propConstEq st i v = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.constEq i v).SatisfiedBy a → False) ∧
    (∀ cc, propConstEq st i v = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.constEq i v).SatisfiedBy a →
        ∃ l ∈ cc, l.eval a = some true) := by
  cases v with
  | int k => exact propConstEqInt_safe st i k
  | bool b => exact propConstEqBool_safe st i b
  | setOfInt x => exact propConstEqNoEmit_safe st i (.setOfInt x) rfl
  | array xs => exact propConstEqNoEmit_safe st i (.array xs) rfl

/-- The general-`v` entitlement for `propConstEq`. -/
theorem propConstEq_entitled
    {problem : Problem DomConstraint Unit}
    {st : State} {i : Nat} {v : Value} {cc : Clause}
    (hprob : DomConstraint.constEq i v ∈ problem.constraints)
    (hrun : propConstEq st i v = .conflict cc)
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ cc, l.eval a = some true := by
  cases v with
  | int k => exact propConstEqInt_entitled hprob hrun a ha
  | bool b => exact propConstEqBool_entitled hprob hrun a ha
  | setOfInt x =>
      have hst : propConstEq st i (.setOfInt x) = .stable := rfl
      rw [hst] at hrun
      exact absurd hrun (by intro hc; cases hc)
  | array xs =>
      have hst : propConstEq st i (.array xs) = .stable := rfl
      rw [hst] at hrun
      exact absurd hrun (by intro hc; cases hc)

/-- The general-`v` reason-validity lemma for `propConstEq`. -/
theorem propConstEq_reason_safe
    {problem : Problem DomConstraint Unit}
    {constraintHolds : DomConstraint → Assignment → Prop}
    {st : State} {i : Nat} {v : Value} {l : Literal} {r : Reason}
    (himp : ∀ c a, c ∈ problem.constraints →
      constraintHolds c a → c.SatisfiedBy a)
    (hprob : DomConstraint.constEq i v ∈ problem.constraints)
    (hrun : propConstEq st i v = .implied l r) :
    Reason.Valid problem constraintHolds r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  cases v with
  | int k => exact propConstEqInt_reason_safe himp hprob hrun
  | bool b => exact propConstEqBool_reason_safe himp hprob hrun
  | setOfInt x =>
      have hst : propConstEq st i (.setOfInt x) = .stable := rfl
      rw [hst] at hrun
      exact absurd hrun (by intro hc; cases hc)
  | array xs =>
      have hst : propConstEq st i (.array xs) = .stable := rfl
      rw [hst] at hrun
      exact absurd hrun (by intro hc; cases hc)

/-- The canonical `DomConstraint.SatisfiedBy` instantiation. -/
theorem propConstEq_reason_safe_sat
    {problem : Problem DomConstraint Unit}
    {st : State} {i : Nat} {v : Value} {l : Literal} {r : Reason}
    (hprob : DomConstraint.constEq i v ∈ problem.constraints)
    (hrun : propConstEq st i v = .implied l r) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l ∧
      (∀ q ∈ r.clause, q = q.norm) :=
  propConstEq_reason_safe (fun _ _ _ h => h) hprob hrun

/-! ## The B3 registration

The standalone registration of the two `leConst` families (in the
real registration `propagatorOfProved` these are arms; this
standalone packaging keeps the front-door theorems of this module
usable before composition). -/

/-- The B3 registration: the proved propagators of the two
    constant-bound families (in the integrated registration, arms
    of `propagatorOfProved`). -/
def propagatorOfProvedB3 : DomConstraint → Option Propagator
  | .leConstHi i c =>
      some { watches := [], run := fun st => propLeConstHi st i c }
  | .leConstLo i c =>
      some { watches := [], run := fun st => propLeConstLo st i c }
  | _ => none

/-- Membership inversion for the B3 registration (the
    `propagatorsOfProved_mem` shape). -/
theorem propagatorOfProvedB3_mem {dcs : List DomConstraint}
    {p : Propagator}
    (hp : p ∈ dcs.filterMap propagatorOfProvedB3) :
    ∃ dc ∈ dcs, propagatorOfProvedB3 dc = some p := by
  induction dcs with
  | nil => cases hp
  | cons dc rest ih =>
      cases hpdc : propagatorOfProvedB3 dc with
      | none =>
          simp only [List.filterMap_cons, hpdc] at hp
          obtain ⟨dc2, hdc2mem, hdc2⟩ := ih hp
          exact ⟨dc2, List.mem_cons_of_mem _ hdc2mem, hdc2⟩
      | some p0 =>
          simp only [List.filterMap_cons, hpdc] at hp
          rcases List.mem_cons.mp hp with hp2 | hp2
          · rw [hp2]
            exact ⟨dc, List.mem_cons_self, hpdc⟩
          · obtain ⟨dc2, hdc2mem, hdc2⟩ := ih hp2
            exact ⟨dc2, List.mem_cons_of_mem _ hdc2mem, hdc2⟩

/-- The run inversion for the B3 registration (the
    `propagatorOfProved_run` shape): an emission of a
    B3-registered propagator reduces to one of the two family
    propagators at the same parameters. -/
theorem propagatorOfProvedB3_run {dc : DomConstraint} {p : Propagator}
    {st : State} {res : PropagationResult}
    (hprop : propagatorOfProvedB3 dc = some p)
    (hrun : p.run st = res) :
    (∃ i c, dc = .leConstHi i c ∧ propLeConstHi st i c = res) ∨
    (∃ i c, dc = .leConstLo i c ∧ propLeConstLo st i c = res) := by
  match hdc : dc with
  | .leConstHi i c =>
      simp only [propagatorOfProvedB3] at hprop
      refine Or.inl ⟨i, c, rfl, ?_⟩
      rw [(Option.some.inj hprop).symm] at hrun
      exact hrun
  | .leConstLo i c =>
      simp only [propagatorOfProvedB3] at hprop
      refine Or.inr ⟨i, c, rfl, ?_⟩
      rw [(Option.some.inj hprop).symm] at hrun
      exact hrun
  | .eqSlot i j
  | .neSlot i j | .leSlot i j | .constEq i v
  | .plusSlot i j k | .allDiff is | .timesSlot i j k
  | .minSlot i j k | .maxSlot i j k | .absSlot i k2
  | .linEq coeffs is b | .linLe coeffs is b
  | .ltSlot i j | .ltConstHi i c | .ltConstLo i c
  | .boolNotSlot i j | .boolAndSlot i j k | .boolOrSlot i j k =>
      exfalso
      simp only [propagatorOfProvedB3] at hprop
      exact absurd hprop (by intro hc; cases hc)

/-! ### The per-family reason bridges

An emission of the propagator registered from a problem constraint of
one of the two families reduces to the family's reason-validity lemma
at the same parameters. -/

/-- The membership bridge for the `leConstHi` family. -/
theorem propagatorOfProvedB3_leConstHi_reason
    {problem : Problem DomConstraint Unit}
    {constraintHolds : DomConstraint → Assignment → Prop}
    {st : State} {i : Nat} {c : Int} {p : Propagator} {l : Literal}
    {r : Reason}
    (himp : ∀ c a, c ∈ problem.constraints →
      constraintHolds c a → c.SatisfiedBy a)
    (hprop : propagatorOfProvedB3 (DomConstraint.leConstHi i c)
      = some p)
    (hprob : DomConstraint.leConstHi i c ∈ problem.constraints)
    (hrun : p.run st = .implied l r) :
    Reason.Valid problem constraintHolds r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  have hrun2 : propLeConstHi st i c = .implied l r := by
    rw [(Option.some.inj hprop).symm] at hrun
    exact hrun
  exact propLeConstHi_reason_safe himp hprob hrun2

/-- The membership bridge for the `leConstLo` family. -/
theorem propagatorOfProvedB3_leConstLo_reason
    {problem : Problem DomConstraint Unit}
    {constraintHolds : DomConstraint → Assignment → Prop}
    {st : State} {i : Nat} {c : Int} {p : Propagator} {l : Literal}
    {r : Reason}
    (himp : ∀ c a, c ∈ problem.constraints →
      constraintHolds c a → c.SatisfiedBy a)
    (hprop : propagatorOfProvedB3 (DomConstraint.leConstLo i c)
      = some p)
    (hprob : DomConstraint.leConstLo i c ∈ problem.constraints)
    (hrun : p.run st = .implied l r) :
    Reason.Valid problem constraintHolds r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  have hrun2 : propLeConstLo st i c = .implied l r := by
    rw [(Option.some.inj hprop).symm] at hrun
    exact hrun
  exact propLeConstLo_reason_safe himp hprob hrun2

/-! ## The front doors for the two `leConst` families

Each mirrors the corresponding six-family assembly
    (`propagatorsOfProved_safeUniv`, `propagatorsOfProved_entitled`,
    and the ReasonSafeUniv obligation of Run.lean), restricted to
    the B3 families — with only the premises these families
    actually need (no `IntViewedDoms`, no `hlin`; safety holds at
    EVERY state, not just coherent ones). -/

/-- **PropSafeUniv for the B3 registration**: every implied literal is
    true at every represented internal solution and every conflict
    clause excludes every represented internal solution — at EVERY
    state (the six-family version needs `IntViewedDoms` for `eqSlot`
    and `DomainCoherent` relativization; neither is needed here, so
    this statement is strictly stronger than the six-family shape). -/
theorem propagatorsOfProvedB3_safeUniv
    {problem : Problem DomConstraint Unit}
    {props : List Propagator}
    (hprops : ∀ p ∈ props, ∃ dc ∈ problem.constraints,
      propagatorOfProvedB3 dc = some p) :
    PropSafeUniv problem DomConstraint.SatisfiedBy props := by
  intro st
  refine ⟨?_, ?_⟩
  · intro p hp l r hrun a ⟨hsol, hrep⟩
    obtain ⟨dc, hdc, hprop⟩ := hprops p hp
    rcases propagatorOfProvedB3_run hprop hrun with
      ⟨i, c, hdc2, hrun2⟩ | ⟨i, c, hdc2, hrun2⟩
    · rw [hdc2] at hdc
      exact (propLeConstHi_safe st i c).1 l r hrun2 a hrep.1
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      exact (propLeConstLo_safe st i c).1 l r hrun2 a hrep.1
        (hsol.2 _ hdc)
  · intro p hp cc hrun a ⟨hsol, hrep⟩
    obtain ⟨dc, hdc, hprop⟩ := hprops p hp
    rcases propagatorOfProvedB3_run hprop hrun with
      ⟨i, c, hdc2, hrun2⟩ | ⟨i, c, hdc2, hrun2⟩
    · rw [hdc2] at hdc
      intro _
      exact (propLeConstHi_safe st i c).2.1 cc hrun2 a hrep.1
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      intro _
      exact (propLeConstLo_safe st i c).2.1 cc hrun2 a hrep.1
        (hsol.2 _ hdc)

/-- **The relativized entitlement for the B3 registration** (the exact
    `propagatorsOfProved_entitled` signature): every conflict clause
    carries a true literal at every internal solution that fits the
    state's domains.

    The `SolvedBy`/`DomainCoherent` premises are VACUOUS for these
    families (the truth literal is pinned by the constraint alone —
    see `propLeConstHi_entitled`); they are kept, unused, purely for
    drop-in signature compatibility with the six-family assembly. -/
theorem propagatorsOfProvedB3_entitled
    {problem : Problem DomConstraint Unit}
    {props : List Propagator}
    (hprops : ∀ p ∈ props, ∃ dc ∈ problem.constraints,
      propagatorOfProvedB3 dc = some p) :
    ∀ (st : State), SolvedBy problem DomConstraint.SatisfiedBy st →
    DomainCoherent problem st →
    ∀ p ∈ props, ∀ (cc : Clause), p.run st = .conflict cc →
    ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
    ∃ l ∈ cc, l.eval a = some true := by
  intro st _hsol _hcoh p hp cc hrun a ha
  obtain ⟨dc, hdc, hprop⟩ := hprops p hp
  rcases propagatorOfProvedB3_run hprop hrun with
    ⟨i, c, hdc2, hrun2⟩ | ⟨i, c, hdc2, hrun2⟩
  · rw [hdc2] at hdc
    exact propLeConstHi_entitled hdc hrun2 a ha
  · rw [hdc2] at hdc
    exact propLeConstLo_entitled hdc hrun2 a ha

/-- **ReasonSafeUniv for the B3 registration**: every propagator's
    implied literal carries a VALID, normalized explanation — the
    obligation `runPropagators_runInv` consumes via its `hreason`
    premise. The `DomainCoherent` premise of `ReasonSafeUniv` is
    vacuous here (the unit nogoods are unconditionally entailed);
    the `himp` semantics bridge is the same one the reason front
    doors need, and disappears at the concrete
    `DomConstraint.SatisfiedBy` semantics. -/
theorem propagatorsOfProvedB3_reason
    {problem : Problem DomConstraint Unit}
    {constraintHolds : DomConstraint → Assignment → Prop}
    (himp : ∀ c a, c ∈ problem.constraints →
      constraintHolds c a → c.SatisfiedBy a)
    {props : List Propagator}
    (hprops : ∀ p ∈ props, ∃ dc ∈ problem.constraints,
      propagatorOfProvedB3 dc = some p) :
    ReasonSafeUniv problem constraintHolds props := by
  intro st _hcoh p hp l r hrun
  obtain ⟨dc, hdc, hprop⟩ := hprops p hp
  rcases propagatorOfProvedB3_run hprop hrun with
    ⟨i, c, hdc2, hrun2⟩ | ⟨i, c, hdc2, hrun2⟩
  · rw [hdc2] at hdc
    exact propLeConstHi_reason_safe himp hdc hrun2
  · rw [hdc2] at hdc
    exact propLeConstLo_reason_safe himp hdc hrun2

/-! ## The B4 registration

The standalone registration of the two `ltConst` families and the
    constant-equality family. -/

/-- The B4 registration: the proved propagators of the two strict
    constant-bound families and the constant-equality family (in
    the integrated registration, arms of `propagatorOfProved`). -/
def propagatorOfProvedB4 : DomConstraint → Option Propagator
  | .ltConstHi i c =>
      some { watches := [], run := fun st => propLtConstHi st i c }
  | .ltConstLo i c =>
      some { watches := [], run := fun st => propLtConstLo st i c }
  | .constEq i v =>
      some { watches := [], run := fun st => propConstEq st i v }
  | _ => none

/-- Membership inversion for the B4 registration (the
    `propagatorsOfProved_mem` shape). -/
theorem propagatorOfProvedB4_mem {dcs : List DomConstraint}
    {p : Propagator}
    (hp : p ∈ dcs.filterMap propagatorOfProvedB4) :
    ∃ dc ∈ dcs, propagatorOfProvedB4 dc = some p := by
  induction dcs with
  | nil => cases hp
  | cons dc rest ih =>
      cases hpdc : propagatorOfProvedB4 dc with
      | none =>
          simp only [List.filterMap_cons, hpdc] at hp
          obtain ⟨dc2, hdc2mem, hdc2⟩ := ih hp
          exact ⟨dc2, List.mem_cons_of_mem _ hdc2mem, hdc2⟩
      | some p0 =>
          simp only [List.filterMap_cons, hpdc] at hp
          rcases List.mem_cons.mp hp with hp2 | hp2
          · rw [hp2]
            exact ⟨dc, List.mem_cons_self, hpdc⟩
          · obtain ⟨dc2, hdc2mem, hdc2⟩ := ih hp2
            exact ⟨dc2, List.mem_cons_of_mem _ hdc2mem, hdc2⟩

/-- The run inversion for the B4 registration (the
    `propagatorOfProved_run` shape): an emission of a B4-registered
    propagator reduces to one of the three family propagators at
    the same parameters. -/
theorem propagatorOfProvedB4_run {dc : DomConstraint} {p : Propagator}
    {st : State} {res : PropagationResult}
    (hprop : propagatorOfProvedB4 dc = some p)
    (hrun : p.run st = res) :
    (∃ i c, dc = .ltConstHi i c ∧ propLtConstHi st i c = res) ∨
    (∃ i c, dc = .ltConstLo i c ∧ propLtConstLo st i c = res) ∨
    (∃ i v, dc = .constEq i v ∧ propConstEq st i v = res) := by
  match hdc : dc with
  | .ltConstHi i c =>
      simp only [propagatorOfProvedB4] at hprop
      refine Or.inl ⟨i, c, rfl, ?_⟩
      rw [(Option.some.inj hprop).symm] at hrun
      exact hrun
  | .ltConstLo i c =>
      simp only [propagatorOfProvedB4] at hprop
      refine Or.inr (Or.inl ⟨i, c, rfl, ?_⟩)
      rw [(Option.some.inj hprop).symm] at hrun
      exact hrun
  | .constEq i v =>
      simp only [propagatorOfProvedB4] at hprop
      refine Or.inr (Or.inr ⟨i, v, rfl, ?_⟩)
      rw [(Option.some.inj hprop).symm] at hrun
      exact hrun
  | .eqSlot i j
  | .neSlot i j | .leSlot i j | .leConstHi i c | .leConstLo i c
  | .plusSlot i j k | .allDiff is
  | .timesSlot i j k | .minSlot i j k | .maxSlot i j k | .absSlot i k2
  | .linEq coeffs is b | .linLe coeffs is b
  | .ltSlot i j | .boolNotSlot i j | .boolAndSlot i j k
  | .boolOrSlot i j k =>
      exfalso
      simp only [propagatorOfProvedB4] at hprop
      exact absurd hprop (by intro hc; cases hc)

/-! ### The per-family reason bridges (B4) -/

/-- The membership bridge for the `ltConstHi` family. -/
theorem propagatorOfProvedB4_ltConstHi_reason
    {problem : Problem DomConstraint Unit}
    {constraintHolds : DomConstraint → Assignment → Prop}
    {st : State} {i : Nat} {c : Int} {p : Propagator} {l : Literal}
    {r : Reason}
    (himp : ∀ c a, c ∈ problem.constraints →
      constraintHolds c a → c.SatisfiedBy a)
    (hprop : propagatorOfProvedB4 (DomConstraint.ltConstHi i c)
      = some p)
    (hprob : DomConstraint.ltConstHi i c ∈ problem.constraints)
    (hrun : p.run st = .implied l r) :
    Reason.Valid problem constraintHolds r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  have hrun2 : propLtConstHi st i c = .implied l r := by
    rw [(Option.some.inj hprop).symm] at hrun
    exact hrun
  exact propLtConstHi_reason_safe himp hprob hrun2

/-- The membership bridge for the `ltConstLo` family. -/
theorem propagatorOfProvedB4_ltConstLo_reason
    {problem : Problem DomConstraint Unit}
    {constraintHolds : DomConstraint → Assignment → Prop}
    {st : State} {i : Nat} {c : Int} {p : Propagator} {l : Literal}
    {r : Reason}
    (himp : ∀ c a, c ∈ problem.constraints →
      constraintHolds c a → c.SatisfiedBy a)
    (hprop : propagatorOfProvedB4 (DomConstraint.ltConstLo i c)
      = some p)
    (hprob : DomConstraint.ltConstLo i c ∈ problem.constraints)
    (hrun : p.run st = .implied l r) :
    Reason.Valid problem constraintHolds r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  have hrun2 : propLtConstLo st i c = .implied l r := by
    rw [(Option.some.inj hprop).symm] at hrun
    exact hrun
  exact propLtConstLo_reason_safe himp hprob hrun2

/-- The membership bridge for the `constEq` family. -/
theorem propagatorOfProvedB4_constEq_reason
    {problem : Problem DomConstraint Unit}
    {constraintHolds : DomConstraint → Assignment → Prop}
    {st : State} {i : Nat} {v : Value} {p : Propagator} {l : Literal}
    {r : Reason}
    (himp : ∀ c a, c ∈ problem.constraints →
      constraintHolds c a → c.SatisfiedBy a)
    (hprop : propagatorOfProvedB4 (DomConstraint.constEq i v)
      = some p)
    (hprob : DomConstraint.constEq i v ∈ problem.constraints)
    (hrun : p.run st = .implied l r) :
    Reason.Valid problem constraintHolds r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  have hrun2 : propConstEq st i v = .implied l r := by
    rw [(Option.some.inj hprop).symm] at hrun
    exact hrun
  exact propConstEq_reason_safe himp hprob hrun2

/-! ## The front doors for the three B4 families

Each mirrors the corresponding six-family assembly
    (`propagatorsOfProved_safeUniv`, `propagatorsOfProved_entitled`,
    and the ReasonSafeUniv obligation of Run.lean), restricted to
    the B4 families — with only the premises these families
    actually need (no `IntViewedDoms`, no `hlin`; safety holds at
    EVERY state, not just coherent ones). -/

/-- **PropSafeUniv for the B4 registration**: every implied literal
    is true at every represented internal solution and every
    conflict clause excludes every represented internal solution —
    at EVERY state (the six-family version needs `IntViewedDoms` for
    `eqSlot` and `DomainCoherent` relativization; neither is needed
    here, so this statement is strictly stronger than the six-family
    shape). -/
theorem propagatorsOfProvedB4_safeUniv
    {problem : Problem DomConstraint Unit}
    {props : List Propagator}
    (hprops : ∀ p ∈ props, ∃ dc ∈ problem.constraints,
      propagatorOfProvedB4 dc = some p) :
    PropSafeUniv problem DomConstraint.SatisfiedBy props := by
  intro st
  refine ⟨?_, ?_⟩
  · intro p hp l r hrun a ⟨hsol, hrep⟩
    obtain ⟨dc, hdc, hprop⟩ := hprops p hp
    rcases propagatorOfProvedB4_run hprop hrun with
      ⟨i, c, hdc2, hrun2⟩ | ⟨i, c, hdc2, hrun2⟩ | ⟨i, v, hdc2, hrun2⟩
    · rw [hdc2] at hdc
      exact (propLtConstHi_safe st i c).1 l r hrun2 a hrep.1
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      exact (propLtConstLo_safe st i c).1 l r hrun2 a hrep.1
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      exact (propConstEq_safe st i v).1 l r hrun2 a hrep.1
        (hsol.2 _ hdc)
  · intro p hp cc hrun a ⟨hsol, hrep⟩
    obtain ⟨dc, hdc, hprop⟩ := hprops p hp
    rcases propagatorOfProvedB4_run hprop hrun with
      ⟨i, c, hdc2, hrun2⟩ | ⟨i, c, hdc2, hrun2⟩ | ⟨i, v, hdc2, hrun2⟩
    · rw [hdc2] at hdc
      intro _
      exact (propLtConstHi_safe st i c).2.1 cc hrun2 a hrep.1
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      intro _
      exact (propLtConstLo_safe st i c).2.1 cc hrun2 a hrep.1
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      intro _
      exact (propConstEq_safe st i v).2.1 cc hrun2 a hrep.1
        (hsol.2 _ hdc)

/-- **The relativized entitlement for the B4 registration** (the
    exact `propagatorsOfProved_entitled` signature): every conflict
    clause carries a true literal at every internal solution that
    fits the state's domains.

    The `SolvedBy`/`DomainCoherent` premises are VACUOUS for these
    families (the truth literal is pinned by the constraint alone);
    they are kept, unused, purely for drop-in signature
    compatibility with the six-family assembly. -/
theorem propagatorsOfProvedB4_entitled
    {problem : Problem DomConstraint Unit}
    {props : List Propagator}
    (hprops : ∀ p ∈ props, ∃ dc ∈ problem.constraints,
      propagatorOfProvedB4 dc = some p) :
    ∀ (st : State), SolvedBy problem DomConstraint.SatisfiedBy st →
    DomainCoherent problem st →
    ∀ p ∈ props, ∀ (cc : Clause), p.run st = .conflict cc →
    ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
    ∃ l ∈ cc, l.eval a = some true := by
  intro st _hsol _hcoh p hp cc hrun a ha
  obtain ⟨dc, hdc, hprop⟩ := hprops p hp
  rcases propagatorOfProvedB4_run hprop hrun with
    ⟨i, c, hdc2, hrun2⟩ | ⟨i, c, hdc2, hrun2⟩ | ⟨i, v, hdc2, hrun2⟩
  · rw [hdc2] at hdc
    exact propLtConstHi_entitled hdc hrun2 a ha
  · rw [hdc2] at hdc
    exact propLtConstLo_entitled hdc hrun2 a ha
  · rw [hdc2] at hdc
    exact propConstEq_entitled hdc hrun2 a ha

/-- **ReasonSafeUniv for the B4 registration**: every propagator's
    implied literal carries a VALID, normalized explanation — the
    obligation `runPropagators_runInv` consumes via its `hreason`
    premise. The `DomainCoherent` premise of `ReasonSafeUniv` is
    vacuous here (the unit nogoods are unconditionally entailed);
    the `himp` semantics bridge disappears at the concrete
    `DomConstraint.SatisfiedBy` semantics. -/
theorem propagatorsOfProvedB4_reason
    {problem : Problem DomConstraint Unit}
    {constraintHolds : DomConstraint → Assignment → Prop}
    (himp : ∀ c a, c ∈ problem.constraints →
      constraintHolds c a → c.SatisfiedBy a)
    {props : List Propagator}
    (hprops : ∀ p ∈ props, ∃ dc ∈ problem.constraints,
      propagatorOfProvedB4 dc = some p) :
    ReasonSafeUniv problem constraintHolds props := by
  intro st _hcoh p hp l r hrun
  obtain ⟨dc, hdc, hprop⟩ := hprops p hp
  rcases propagatorOfProvedB4_run hprop hrun with
    ⟨i, c, hdc2, hrun2⟩ | ⟨i, c, hdc2, hrun2⟩ | ⟨i, v, hdc2, hrun2⟩
  · rw [hdc2] at hdc
    exact propLtConstHi_reason_safe himp hdc hrun2
  · rw [hdc2] at hdc
    exact propLtConstLo_reason_safe himp hdc hrun2
  · rw [hdc2] at hdc
    exact propConstEq_reason_safe himp hdc hrun2

/-! ## Shared linear-arithmetic kernels (moved from
Proofs/Propagators.lean so the Fam/Lin family module can consume
them without an import cycle) -/

def dotOver : List (Int × Nat) → Assignment → Int → Option Int
  | [], _, acc => some acc
  | (c, s) :: rest, a, acc =>
      match a[s]! with
      | .int x => dotOver rest a (acc + c * x)
      | _ => none

theorem dotOver_shift (ps : List (Int × Nat)) (a : Assignment) (k acc : Int) :
    dotOver ps a (acc + k) = (dotOver ps a acc).map (fun d => d + k) := by
  induction ps generalizing acc with
  | nil =>
      show some (acc + k) = (some acc).map (fun d => d + k)
      simp
  | cons p rest ih =>
      obtain ⟨c, s⟩ := p
      rw [dotOver, dotOver]
      match ha : a[s]! with
      | .int x =>
          show dotOver rest a (acc + k + c * x) =
            (dotOver rest a (acc + c * x)).map (fun d => d + k)
          rw [show acc + k + c * x = (acc + c * x) + k by omega]
          exact ih (acc + c * x)
      | .bool x => rfl
      | .setOfInt x => rfl
      | .array x => rfl

theorem dotProduct_eq_dotOver {coeffs : List Int} {is : List Nat}
    {a : Assignment} (hlen : coeffs.length = is.length) :
    dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) =
      dotOver (coeffs.zip is) a 0 := by
  induction coeffs generalizing is with
  | nil =>
      cases is with
      | nil => rfl
      | cons s ss => simp at hlen
  | cons c cs ih =>
      match his : is with
      | [] => simp at hlen
      | s :: ss =>
          have hlen2 : cs.length = ss.length := by
            simp only [List.length_cons] at hlen; omega
          show dotProduct (.int c :: intVals cs)
              (a[s]! :: ss.map (fun i => a[i]!)) =
            dotOver ((c, s) :: cs.zip ss) a 0
          match ha : a[s]! with
          | .int x =>
              rw [dotProduct]
              have hih := ih hlen2
              cases hd : dotProduct (intVals cs) (ss.map (fun i => a[i]!)) with
              | none =>
                  rw [hd] at hih
                  have hshift : dotOver (cs.zip ss) a (0 + c * x) =
                      (dotOver (cs.zip ss) a 0).map (fun d => d + c * x) :=
                    dotOver_shift (ps := cs.zip ss) (a := a) (k := c * x) (acc := 0)
                  rw [← hih] at hshift
                  simp only [Option.map_none] at hshift
                  rw [dotOver, ha]
                  show (match none with
                    | some s => some (c * x + s)
                    | none => none) =
                    dotOver (cs.zip ss) a (0 + c * x)
                  rw [hshift]
              | some d =>
                  rw [hd] at hih
                  cases hih2 : dotOver (cs.zip ss) a 0 with
                  | none => exact absurd hih (by rw [hih2]; simp)
                  | some d2 =>
                      have hshift : dotOver (cs.zip ss) a (0 + c * x) =
                          (dotOver (cs.zip ss) a 0).map (fun d => d + c * x) :=
                        dotOver_shift (ps := cs.zip ss) (a := a) (k := c * x) (acc := 0)
                      rw [dotOver, ha]
                      show (match some d with
                        | some s2 => some (c * x + s2)
                        | none => none) =
                        dotOver (cs.zip ss) a (0 + c * x)
                      rw [hshift, hih2]
                      have hd2d : d2 = d := by
                        have h3 : some d = some d2 := hih.trans hih2
                        injection h3 with h4
                        exact h4.symm
                      have harith : c * x + d = d2 + c * x := by omega
                      exact congrArg some harith
          | .bool x =>
              have hd0 : dotProduct (Value.int c :: intVals cs)
                  (Value.bool x :: ss.map (fun i => a[i]!)) = none := rfl
              rw [hd0, dotOver, ha]
          | .setOfInt x =>
              have hd0 : dotProduct (Value.int c :: intVals cs)
                  (Value.setOfInt x :: ss.map (fun i => a[i]!)) = none := rfl
              rw [hd0, dotOver, ha]
          | .array x =>
              have hd0 : dotProduct (Value.int c :: intVals cs)
                  (Value.array x :: ss.map (fun i => a[i]!)) = none := rfl
              rw [hd0, dotOver, ha]

theorem getElem_bang_of_read {a : Assignment} {s : Nat} {v : Value}
    (hv : a[s]? = some v) (hrng : s < a.length) : a[s]! = v := by
  rw [List.getElem!_eq_getElem?_getD, hv]
  rfl

/-- The read behind an int-viewed slot. -/

theorem read_of_slotInt {a : Assignment} {s : Nat} {i : Int}
    (hslot : slotInt a s = some i) :
    ∃ v, a[s]? = some v ∧ Value.intView v = some i := by
  unfold slotInt at hslot
  rw [Option.bind_eq_some_iff] at hslot
  obtain ⟨v, hv, hvi⟩ := hslot
  exact ⟨v, hv, hvi⟩

theorem zipIdx_succ_shift {α : Type} (ys : List α) (k : Nat) :
    ys.zipIdx (k+1) = (ys.zipIdx k).map (fun p => (p.1, p.2 + 1)) := by
  induction ys generalizing k with
  | nil => rfl
  | cons y ys2 ih2 =>
      simp only [List.zipIdx, List.map_cons, Nat.zero_add]
      exact congrArg _ (ih2 (k+1))

theorem zipIdx_k_eq_map {α : Type} (ys : List α) (k : Nat) :
    ys.zipIdx k = (ys.zipIdx (0 : Nat)).map (fun p => (p.1, p.2 + k)) := by
  induction k with
  | zero =>
      induction ys with
      | nil => rfl
      | cons y ys2 ih2 =>
          simp only [List.zipIdx, List.map_cons, Nat.zero_add]
          rw [zipIdx_succ_shift ys2 0]
          simp only [List.map_map]
          rw [ih2]
          exact congrArg _ (List.map_congr_left (fun p => by
            intro _
            rfl))
  | succ k ih =>
      rw [zipIdx_succ_shift, ih, List.map_map]
      exact List.map_congr_left (fun p => by
        intro _
        show ((fun p => (p.1, p.2 + 1)) ∘ fun p => (p.1, p.2 + k)) p
          = (p.1, p.2 + (k + 1))
        rfl)

-- Filter at threshold (j+k) over zipIdx k = map (+k) of filter at j
-- over zipIdx 0 — now a one-liner via zipIdx_k_eq_map.
-- goal: filter P (map σ l) = map σ (filter Q l) where σ p = (p.1,
-- p.2+k), P p = p.2 != j+k, Q p = p.2 != j — filter-map commute.

theorem filter_map_comm {α β : Type} (l : List α) (f : α → β)
    (P : β → Bool) (Q : α → Bool)
    (h : ∀ x, P (f x) = Q x) :
    List.filter P (l.map f) = (List.filter Q l).map f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.filter_cons]
      rw [h x]
      cases hQ : Q x with
      | true =>
          show f x :: List.filter P (List.map f xs) =
            f x :: List.map f (List.filter Q xs)
          exact congrArg _ ih
      | false =>
          show List.filter P (List.map f xs) =
            List.map f (List.filter Q xs)
          exact ih

theorem filter_zipIdx_shift {α : Type} (ys : List α) (k j : Nat) :
    List.filter (fun p => p.snd != j + k) (ys.zipIdx k) =
      (List.filter (fun p => p.snd != j) (ys.zipIdx 0)).map
        (fun p => (p.1, p.2 + k)) := by
  rw [zipIdx_k_eq_map ys k]
  exact filter_map_comm _ _ _ _
    (fun p => by
      show ((p.1, p.2 + k).2 != j + k) = (p.2 != j)
      by_cases h : p.2 = j
      · subst h; simp
      · have hne1 : ¬ (p.2 + k = j + k) := by
          intro hcon
          rw [Nat.add_right_cancel hcon] at h
          exact h rfl
        have h1 : ((p.1, p.2 + k).2 != j + k) = true := by
          show (!(p.2 + k == j + k)) = true
          cases hc : (p.2 + k == j + k) with
          | false => rfl
          | true =>
              exfalso
              apply hne1
              exact (beq_iff_eq (a := p.2 + k) (b := j + k)).mp hc
        have h2 : (p.2 != j) = true := by
          show (!(p.2 == j)) = true
          cases hc : (p.2 == j) with
          | false => rfl
          | true =>
              exfalso
              apply h
              exact (beq_iff_eq (a := p.2) (b := j)).mp hc
        rw [h1, h2])

theorem map_fst_zipIdx {α : Type} (ys : List α) (k : Nat) :
    (ys.zipIdx k).map (fun p => p.1) = ys := by
  induction ys generalizing k with
  | nil => rfl
  | cons y ys2 ih2 =>
      simp only [List.zipIdx, List.map_cons]
      exact congrArg _ (ih2 (k+1))

-- entries of zipIdx k have indices ≥ k; a threshold t < k keeps all

theorem filter_ne_below_shift {α : Type} (ys : List α) (k t : Nat)
    (hlt : t < k) :
    List.filter (fun p => p.snd != t) (ys.zipIdx k) = ys.zipIdx k := by
  induction ys generalizing k hlt with
  | nil => rfl
  | cons y ys2 ih2 =>
      simp only [List.zipIdx, List.filter_cons, beq_iff_eq]
      have hne : ¬ (0 + k = t) := by omega
      have hcond : (k != t) = true := by
        cases hc2 : (k == t) with
        | true =>
            have hEq : k = t := by
              simpa using (beq_iff_eq (a := k) (b := t)).mp hc2
            exact absurd hEq (by omega)
        | false => show (!(k == t)) = true; rw [hc2]; rfl
      rw [if_pos (show (k != t) = true from hcond)]
      exact congrArg _ (ih2 (k+1) (by omega))

theorem zipIdx_filter_remove {α : Type} (l : List α) (i : Nat)
    (hlt : i < l.length) :
    ((l.zipIdx.filter (fun p => p.2 != i)).map (·.1)) =
      l.take i ++ l.drop (i+1) := by
  induction l generalizing i with
  | nil => simp at hlt
  | cons x xs ih =>
      match i with
      | 0 =>
          -- head (x,0) fails the ≠0 filter; tail is zipIdx 1
          show List.map (fun p => p.1)
              (List.filter (fun p => p.snd != 0) (xs.zipIdx 1)) =
            (x :: xs).take 0 ++ (x :: xs).drop (0+1)
          -- every index in zipIdx 1 is ≥ 1, so the ≠0 filter keeps all
          have hkeep : List.filter (fun p => p.snd != 0) (xs.zipIdx 1)
              = xs.zipIdx 1 := filter_ne_below_shift xs 1 0 (by omega)
          rw [hkeep, map_fst_zipIdx xs 1]
          rfl
      | i2+1 =>
          have hlt2 : i2 < xs.length := by
            simp only [List.length_cons] at hlt; omega
          -- head (x, 0) passes the ≠(i2+1) filter; the tail at
          -- zipIdx 1 filters ≠(i2+1) — shift it to zipIdx 0 at ≠i2,
          -- dropping the index bump in the result
          simp only [List.zipIdx, List.filter_cons, beq_iff_eq,
            Nat.zero_add]
          have hcond : ((0 : Nat) != i2 + 1) = true := by
            cases hc : ((0 : Nat) == i2 + 1) with
            | true =>
                exact absurd (by simpa using hc)
                  (fun h => Nat.succ_ne_zero i2 h)
            | false => rfl
          rw [if_pos hcond]
          have hshift := filter_zipIdx_shift xs 1 i2
          rw [hshift]
          have hcomp : (fun p : α × Nat => p.1) ∘
              (fun p : α × Nat => (p.1, p.2 + 1)) =
              (fun p : α × Nat => p.1) := by
            funext p; rfl
          simp only [List.map_cons, List.map_map]
          rw [hcomp, ih i2 hlt2]
          simp only [List.take_succ_cons, List.drop_succ_cons]
          rfl

theorem dotOver_append (l1 l2 : List (Int × Nat)) (a : Assignment)
    (acc : Int) :
    dotOver (l1 ++ l2) a acc =
      (dotOver l1 a acc).bind (fun acc' => dotOver l2 a acc') := by
  induction l1 generalizing acc with
  | nil => simp [dotOver]
  | cons p rest ih =>
      obtain ⟨c, s⟩ := p
      cases ha : a[s]! with
      | int x =>
          have h1 : dotOver ((c, s) :: rest ++ l2) a acc
              = dotOver (rest ++ l2) a (acc + c * x) := by
            show (match a[s]! with
              | .int y => dotOver (rest ++ l2) a (acc + c * y)
              | _ => none) = dotOver (rest ++ l2) a (acc + c * x)
            rw [ha]
          have h2 : dotOver ((c, s) :: rest) a acc
              = dotOver rest a (acc + c * x) := by
            show (match a[s]! with
              | .int y => dotOver rest a (acc + c * y)
              | _ => none) = dotOver rest a (acc + c * x)
            rw [ha]
          rw [h1, h2]
          exact ih (acc + c * x)
      | bool x =>
          have h1 : dotOver ((c, s) :: rest ++ l2) a acc = none := by
            show (match a[s]! with
              | .int y => dotOver (rest ++ l2) a (acc + c * y)
              | _ => none) = none
            rw [ha]
          have h2 : dotOver ((c, s) :: rest) a acc = none := by
            show (match a[s]! with
              | .int y => dotOver rest a (acc + c * y)
              | _ => none) = none
            rw [ha]
          rw [h1, h2]
          rfl
      | setOfInt x =>
          have h1 : dotOver ((c, s) :: rest ++ l2) a acc = none := by
            show (match a[s]! with
              | .int y => dotOver (rest ++ l2) a (acc + c * y)
              | _ => none) = none
            rw [ha]
          have h2 : dotOver ((c, s) :: rest) a acc = none := by
            show (match a[s]! with
              | .int y => dotOver rest a (acc + c * y)
              | _ => none) = none
            rw [ha]
          rw [h1, h2]
          rfl
      | array x =>
          have h1 : dotOver ((c, s) :: rest ++ l2) a acc = none := by
            show (match a[s]! with
              | .int y => dotOver (rest ++ l2) a (acc + c * y)
              | _ => none) = none
            rw [ha]
          have h2 : dotOver ((c, s) :: rest) a acc = none := by
            show (match a[s]! with
              | .int y => dotOver rest a (acc + c * y)
              | _ => none) = none
            rw [ha]
          rw [h1, h2]
          rfl

theorem mem_zip_snd {α β : Type} {l1 : List α} {l2 : List β}
    {p : α × β} (hp : p ∈ l1.zip l2) : p.2 ∈ l2 := by
  induction l1 generalizing l2 with
  | nil => cases hp
  | cons a as ih =>
      match l2 with
      | [] => cases hp
      | b :: bs =>
          rw [show (a :: as).zip (b :: bs) = (a, b) :: as.zip bs from rfl] at hp
          rcases List.mem_cons.mp hp with hp2 | hp3
          · rw [hp2]; exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih hp3)

theorem dotProduct_reads_int {vals : List Value} {is : List Nat}
    {d : Int} {a : Assignment}
    (hd : dotProduct vals (is.map (fun i => a[i]!)) = some d) :
    ∀ t, t ∈ is → ∃ x, a[t]! = .int x := by
  induction vals generalizing is d with
  | nil =>
      match his : is with
      | [] => intro t ht; cases ht
      | u :: us =>
          exfalso
          rw [List.map_cons] at hd
          have hnone : dotProduct ([] : List Value)
              (a[u]! :: us.map (fun i => a[i]!)) = none := rfl
          rw [hnone] at hd
          cases hd
  | cons v vs ih =>
      match his : is with
      | [] =>
          exfalso
          rw [List.map_nil] at hd
          cases v with
          | int w =>
              exfalso
              have hnone : dotProduct (Value.int w :: vs)
                  (([] : List Value)) = none := rfl
              rw [hnone] at hd
              cases hd
          | bool w =>
              have hnone : dotProduct (Value.bool w :: vs)
                  (([] : List Value)) = none := rfl
              rw [hnone] at hd; cases hd
          | setOfInt w =>
              have hnone : dotProduct (Value.setOfInt w :: vs)
                  (([] : List Value)) = none := rfl
              rw [hnone] at hd; cases hd
          | array w =>
              have hnone : dotProduct (Value.array w :: vs)
                  (([] : List Value)) = none := rfl
              rw [hnone] at hd; cases hd
      | t :: ts =>
          rw [List.map_cons] at hd
          match ha : a[t]! with
          | .int x =>
              intro u hu
              rcases List.mem_cons.mp hu with hu1 | hu2
              · rw [hu1]; exact ⟨x, ha⟩
              · -- v must be .int w for the dot to exist; other
                -- heads give none — but v is a VARIABLE here (we
                -- already matched on a[t]!). Case on v:
                cases v with
                | int w =>
                    have hred : dotProduct (Value.int w :: vs)
                        (a[t]! :: ts.map (fun i => a[i]!)) =
                        (match dotProduct vs (ts.map (fun i => a[i]!)) with
                        | some s => some (w * x + s)
                        | none => none) := by
                      rw [ha, dotProduct]
                      rfl
                    rw [hred] at hd
                    cases hd2 : dotProduct vs (ts.map (fun i => a[i]!)) with
                    | none => rw [hd2] at hd; cases hd
                    | some s => rw [hd2] at hd; exact ih hd2 u hu2
                | bool w =>
                    exfalso
                    have hnone : dotProduct (Value.bool w :: vs)
                        (a[t]! :: ts.map (fun i => a[i]!)) = none := rfl
                    rw [hnone] at hd
                    cases hd
                | setOfInt w =>
                    exfalso
                    have hnone : dotProduct (Value.setOfInt w :: vs)
                        (a[t]! :: ts.map (fun i => a[i]!)) = none := rfl
                    rw [hnone] at hd
                    cases hd
                | array w =>
                    exfalso
                    have hnone : dotProduct (Value.array w :: vs)
                        (a[t]! :: ts.map (fun i => a[i]!)) = none := rfl
                    rw [hnone] at hd
                    cases hd
          | .bool y =>
              exfalso
              have hnone : dotProduct (v :: vs)
                  ((.bool y : Value) :: ts.map (fun i => a[i]!)) = none := by
                cases v with
                | int w =>
                    show (match (Value.bool y : Value) with
                      | .int z => (match dotProduct vs
                          (ts.map (fun i => a[i]!)) with
                        | some s => some (w * z + s)
                        | none => none)
                      | _ => none) = none
                    rfl
                | bool w2 => rfl
                | setOfInt w2 => rfl
                | array w2 => rfl
              rw [ha, hnone] at hd
              cases hd
          | .setOfInt y =>
              exfalso
              have hnone : dotProduct (v :: vs)
                  ((.setOfInt y : Value) :: ts.map (fun i => a[i]!)) = none := by
                cases v with
                | int w =>
                    show (match (Value.setOfInt y : Value) with
                      | .int z => (match dotProduct vs
                          (ts.map (fun i => a[i]!)) with
                        | some s => some (w * z + s)
                        | none => none)
                      | _ => none) = none
                    rfl
                | bool w2 => rfl
                | setOfInt w2 => rfl
                | array w2 => rfl
              rw [ha, hnone] at hd
              cases hd
          | .array y =>
              exfalso
              have hnone : dotProduct (v :: vs)
                  ((.array y : Value) :: ts.map (fun i => a[i]!)) = none := by
                cases v with
                | int w =>
                    show (match (Value.array y : Value) with
                      | .int z => (match dotProduct vs
                          (ts.map (fun i => a[i]!)) with
                        | some s => some (w * z + s)
                        | none => none)
                      | _ => none) = none
                    rfl
                | bool w2 => rfl
                | setOfInt w2 => rfl
                | array w2 => rfl
              rw [ha, hnone] at hd
              cases hd

theorem linLe_dot {coeffs : List Int} {is : List Nat} {b : Int}
    {a : Assignment}
    (hcons : (DomConstraint.linLe coeffs is b).SatisfiedBy a)
    (hlen : coeffs.length = is.length) :
    ∃ d, dotOver (coeffs.zip is) a 0 = some d ∧ d ≤ b := by
  rw [show DomConstraint.SatisfiedBy (DomConstraint.linLe coeffs is b) a =
    (dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b = true) from rfl] at hcons
  unfold dotLe at hcons
  cases hd : dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) with
  | none =>
      rw [hd] at hcons
      simp at hcons
  | some d =>
      rw [hd] at hcons
      simp only [] at hcons
      have hle : d ≤ b := by
        have hdec : decide (d ≤ b) = true := by
          cases hb : decide (d ≤ b) with
          | true => rfl
          | false => rw [hb] at hcons; simp at hcons
        exact of_decide_eq_true hdec
      rw [dotProduct_eq_dotOver hlen] at hd
      exact ⟨d, hd, hle⟩

theorem zipIdx_indices_ge' {α : Type} : ∀ (ys : List α) (k : Nat)
    (p : α × Nat), p ∈ ys.zipIdx k → k ≤ p.2 := by
  intro ys k
  induction ys generalizing k with
  | nil => intro p h; cases h
  | cons z zs ih3 =>
      intro p h
      rcases List.mem_cons.mp h with hc1 | hc2
      · rw [hc1]; exact Nat.le_refl k
      · exact Nat.le_trans (Nat.le_succ k) (ih3 (k+1) p hc2)

theorem zipIdx_getD' {α : Type} : ∀ (l : List α) (k i : Nat) (x : α),
    (x, i) ∈ l.zipIdx k → l.getD (i - k) x = x := by
  intro l
  induction l with
  | nil => intro k i x h; cases h
  | cons y ys ih =>
      intro k i x h
      match i with
      | 0 =>
          rcases List.mem_cons.mp h with h1 | h2
          · injection h1 with h11 _
            rw [h11]
            show (y :: ys).getD (0 - k) y = y
            cases k with
            | zero => rfl
            | succ k2 =>
                rw [show (0 : Nat) - (k2 + 1) = 0 from Nat.zero_sub _]
                rfl
          · exfalso
            have hge : k + 1 ≤ (x, 0).2 :=
              zipIdx_indices_ge' ys (k + 1) (x, 0) h2
            omega
      | i2+1 =>
          rcases List.mem_cons.mp h with h1 | h2
          · injection h1 with h11 h12
            rw [h11, h12]
            show (y :: ys).getD (k - k) y = y
            rw [Nat.sub_self]
            rfl
          · have hge : k + 1 ≤ (x, i2 + 1).2 :=
              zipIdx_indices_ge' ys (k + 1) (x, i2 + 1) h2
            rw [show (i2 + 1 - k) = (i2 - k) + 1 from by omega]
            rw [List.getD_cons_succ]
            have hih := ih (k+1) (i2+1) x h2
            have hidx : i2 + 1 - (k + 1) = i2 - k := by omega
            rw [hidx] at hih
            exact hih

theorem zipIdx_getD {α : Type} (l : List α) (i : Nat) (x : α)
    (h : (x, i) ∈ l.zipIdx) : l.getD i x = x := by
  have h' : (x, i) ∈ l.zipIdx 0 := h
  have := zipIdx_getD' l 0 i x h'
  rw [Nat.sub_zero] at this
  exact this

-- entry membership gives length bound:

theorem zipIdx_mem_length {α : Type} : ∀ (l : List α) (k i : Nat)
    (x : α), (x, i) ∈ l.zipIdx k → i - k < l.length := by
  intro l
  induction l with
  | nil => intro k i x h; cases h
  | cons y ys ih =>
      intro k i x h
      match i with
      | 0 =>
          cases k with
          | zero => exact Nat.zero_lt_succ _
          | succ k2 =>
              -- 0 - (k2+1) = 0
              show (0 : Nat) - (k2 + 1) < Nat.succ ys.length
              rw [Nat.zero_sub]
              exact Nat.zero_lt_succ _
      | i2+1 =>
          rcases List.mem_cons.mp h with h1 | h2
          · injection h1 with _ h12
            -- h12 : i2 + 1 = k; goal (i2+1-k) = 0 < len
            rw [h12, Nat.sub_self]
            exact Nat.zero_lt_succ _
          · -- h2 : (x, i2+1) ∈ ys.zipIdx (k+1); indices ≥ k+1
            have hge : k + 1 ≤ (x, i2 + 1).2 :=
              zipIdx_indices_ge' ys (k + 1) (x, i2 + 1) h2
            have hih := ih (k+1) (i2+1) x h2
            have hsub : i2 + 1 - (k + 1) = i2 - k := by omega
            rw [hsub] at hih
            have hstep : i2 + 1 - k = (i2 - k) + 1 := by omega
            rw [hstep]
            exact Nat.succ_lt_succ hih

-- the full list = take i ++ [getD i] ++ drop (i+1):

theorem list_split {α : Type} (l : List α) (i : Nat) (dflt : α)
    (hi : i < l.length) :
    l = l.take i ++ [l.getD i dflt] ++ l.drop (i+1) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      match i with
      | 0 =>
          show x :: xs = [x] ++ xs
          simp
      | i2+1 =>
          have hi2 : i2 < xs.length := by
            simp only [List.length_cons] at hi; omega
          rw [List.take_succ_cons, List.drop_succ_cons,
            List.getD_cons_succ]
          exact congrArg (x :: ·) (ih i2 hi2)

-- dotOver over the split:

theorem dotOver_split_mid {coeffs : List Int} {is : List Nat}
    {a : Assignment} {i : Nat} {d : Int}
    (hi : i < (coeffs.zip is).length)
    (hreads : ∀ p, p ∈ coeffs.zip is → ∃ x, slotInt a p.2 = some x)
    (hdot : dotOver (coeffs.zip is) a 0 = some d) :
    ∃ c m xt rest,
      (coeffs.zip is).getD i (0, 0) = (c, m) ∧
      slotInt a m = some xt ∧
      rest = (coeffs.zip is).take i ++ (coeffs.zip is).drop (i+1) ∧
      dotOver rest a 0 = some (d - c * xt) := by
  -- the full list splits at i:
  have hsplit : (coeffs.zip is) =
      (coeffs.zip is).take i ++ [(coeffs.zip is).getD i (0, 0)] ++
      (coeffs.zip is).drop (i+1) :=
    list_split _ i (0, 0) hi
  -- getD membership helper (local):
  have hmem : ∀ (l : List (Int × Nat)) (i2 : Nat) (df : Int × Nat),
      i2 < l.length → l.getD i2 df ∈ l := by
    intro l i2 df hlt
    rw [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem hlt]
    exact List.getElem_mem hlt
  -- the entry's membership and the read at its slot:
  have hentry : (coeffs.zip is).getD i (0, 0) ∈ coeffs.zip is :=
    hmem _ i _ hi
  obtain ⟨c, m, hcm⟩ : ∃ c m, (coeffs.zip is).getD i (0, 0) = (c, m) := by
    refine ⟨((coeffs.zip is).getD i (0, 0)).1,
      ((coeffs.zip is).getD i (0, 0)).2, ?_⟩
    rfl
  rw [hcm] at hentry
  obtain ⟨xt, hxt⟩ := hreads (c, m) hentry
  -- in-range for the read bridge:
  obtain ⟨v, hv, hvi⟩ := read_of_slotInt hxt
  have hrng : m < a.length := by
    cases hlt : Nat.lt_or_ge m a.length with
    | inl h => exact h
    | inr hge =>
        exfalso
        have hnone : a[m]? = none :=
          List.getElem?_eq_none_iff.mpr hge
        rw [hnone] at hv
        cases hv
  have hread : a[m]! = v := getElem_bang_of_read hv hrng
  -- dotOver over the split:
  rw [hsplit] at hdot
  -- append: dot (l1 ++ [e] ++ l2) 0 = bind (dot l1 0) ...
  rw [List.append_assoc] at hdot
  -- the middle singleton ++ drop is one list:
  have hmid : [(coeffs.zip is).getD i (0, 0)] ++
      (coeffs.zip is).drop (i+1) =
      [(c, m)] ++ (coeffs.zip is).drop (i+1) := by
    rw [hcm]
  rw [hmid, dotOver_append] at hdot
  -- case on the prefix's dot:
  cases hl1 : dotOver ((coeffs.zip is).take i) a 0 with
  | none =>
      rw [hl1] at hdot
      cases hdot
  | some d1 =>
      rw [hl1] at hdot
      -- (some d1).bind f = f d1:
      rw [show ((some d1 : Option Int).bind
        (fun acc' => dotOver ([(c, m)] ++ (coeffs.zip is).drop (i+1)) a acc')) =
        dotOver ([(c, m)] ++ (coeffs.zip is).drop (i+1)) a d1 from rfl] at hdot
      rw [dotOver_append] at hdot
      -- dot [e] d1 = (if a[m]! int then some (d1 + c*xt) else none)
      have hdotE : dotOver [(c, m)] a d1 =
          (match a[m]! with
            | .int y => some (d1 + c * y)
            | _ => none) := rfl
      rw [hdotE, hread] at hdot
      -- v is int (view some xt forces... v could be bool!)
      -- from hdot being some d, v must be .int:
      cases v with
      | int y =>
          -- view: int y → some y = some xt → y = xt
          rw [Value.intView] at hvi
          have hyx : y = xt := Option.some.inj hvi
          rw [hyx] at hdot
          rw [show ((some (d1 + c * xt) : Option Int).bind
            (fun acc2 => dotOver ((coeffs.zip is).drop (i+1)) a acc2)) =
            dotOver ((coeffs.zip is).drop (i+1)) a (d1 + c * xt) from rfl] at hdot
          -- hdot : dot l2 (d1 + c*xt) = some d
          refine ⟨c, m, xt, (coeffs.zip is).take i ++
            (coeffs.zip is).drop (i+1), hcm, hxt, rfl, ?_⟩
          -- goal: dotOver (take i ++ drop (i+1)) a 0 =
          --   some (d - c*xt)
          rw [dotOver_append, hl1]
          -- goal: (some d1).bind (fun acc' => dot l2 acc') =
          --   some (d - c*xt); unfold the bind:
          rw [show ((some d1 : Option Int).bind
            (fun acc' => dotOver ((coeffs.zip is).drop (i+1)) a acc')) =
            dotOver ((coeffs.zip is).drop (i+1)) a d1 from rfl]
          -- need: dot l2 d1 = some (d - c*xt), have
          -- dot l2 (d1 + c*xt) = some d — NOT the same! The rest
          -- excludes the middle entry — wait: rest = take ++ drop;
          -- the bind's acc is d1 (from take only). The drop's dot
          -- at d1 vs at d1+c*xt... The entry's contribution is
          -- ADDED between take and drop in the FULL list. For the
          -- REST (entry excluded), dot l2 d1 continues from d1.
          -- hdot is about the FULL list = take ++ [entry] ++ drop.
          -- The rest's dot at 0: (take ++ drop) via append:
          -- bind (dot take 0) (dot drop) — with dot take 0 = d1,
          -- the result is dot drop d1. And we need
          -- d1 + (dot drop 0-style-sum)?? — use the shift:
          have hshift2 := dotOver_shift
            ((coeffs.zip is).drop (i+1)) a (c * xt) d1
          -- hshift2 : dot drop (d1 + c*xt) =
          --   map (·+c*xt) (dot drop d1)
          rw [hshift2] at hdot
          -- hdot : map (·+c*xt) (dot drop d1) = some d
          cases hdd : dotOver ((coeffs.zip is).drop (i+1)) a d1 with
          | none => rw [hdd] at hdot; cases hdot
          | some d2 =>
              rw [hdd] at hdot
              -- hdot : some (d2 + c*xt) = some d
              have hdeq : d2 + c * xt = d := by
                injection hdot
              refine congrArg some ?_
              omega
      | bool w =>
          exfalso
          rw [show ((match (Value.bool w : Value) with
            | .int y => some (d1 + c * y)
            | _ => (none : Option Int))) = none from rfl] at hdot
          cases hdot
      | setOfInt w =>
          exfalso
          rw [show ((match (Value.setOfInt w : Value) with
            | .int y => some (d1 + c * y)
            | _ => (none : Option Int))) = none from rfl] at hdot
          cases hdot
      | array w =>
          exfalso
          rw [show ((match (Value.array w : Value) with
            | .int y => some (d1 + c * y)
            | _ => (none : Option Int))) = none from rfl] at hdot
          cases hdot

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


theorem linLe_reads_int {coeffs : List Int} {is : List Nat} {b : Int}
    {a : Assignment}
    (hcons : (DomConstraint.linLe coeffs is b).SatisfiedBy a)
    (hlen : coeffs.length = is.length) :
    ∀ p, p ∈ coeffs.zip is → ∃ i, slotInt a p.2 = some i := by
  rw [show DomConstraint.SatisfiedBy (DomConstraint.linLe coeffs is b) a =
    (dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b = true) from rfl] at hcons
  unfold dotLe at hcons
  cases hd : dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) with
  | none => rw [hd] at hcons; simp at hcons
  | some d =>
      rw [hd] at hcons
      simp only [] at hcons
      intro p hp
      have hmem : p.2 ∈ is := mem_zip_snd hp
      obtain ⟨x, hx⟩ := dotProduct_reads_int hd p.2 hmem
      refine ⟨x, ?_⟩
      show a[p.2]?.bind Value.intView = some x
      have hrng : p.2 < a.length := by
        cases hlt : Nat.lt_or_ge p.2 a.length with
        | inl h => exact h
        | inr hge =>
            exfalso
            have hdef : a[p.2]! = (default : Value) := by
              rw [List.getElem!_eq_getElem?_getD]
              rw [List.getElem?_eq_none_iff.mpr hge]
              rfl
            rw [hdef] at hx
            cases hx
      have hread : a[p.2]? = some (.int x) := by
        rw [List.getElem?_eq_getElem hrng]
        have h1 : a[p.2]! = a[p.2] := by
          rw [List.getElem!_eq_getElem?_getD (l := a) (i := p.2)]
          · rw [List.getElem?_eq_getElem hrng]
            rfl
        rw [← h1]
        exact congrArg some hx
      rw [hread]
      show (some (Value.int x)).bind Value.intView = some x
      rfl

end LeanFzn.Solver.LCG

/-
File: LeanFzn/Solver/Propagation/Proofs/Fam/Bool.lean

Purpose:
  The LCG propagators and proof packages for the three Boolean
  connective families of PLAN.md §5 item 3:

  * `boolNotSlot i j` (`bool_not`): the `SatisfiedBy` arm is
    SYMMETRIC — the two slots carry opposite Booleans
    (`x = true ∧ y = false ∨ x = false ∧ y = true` at `i`/`j`);
  * `boolAndSlot i j k` (`bool_and`): slot `k`, the THIRD argument,
    is the OUTPUT — `(p && q) = r` over the Booleans at `i`, `j`, `k`;
  * `boolOrSlot i j k` (`bool_or`), dually `(p || q) = r`.

  Design (mirrors `propConstEq`'s Boolean arm, Propagate.lean:393-404):
  every deduction is a `posBool` head literal emitted by the shared
  `implyBool` helper — implied when the target domain still contains
  the head Boolean alongside something else, conflict (same clause)
  when it contains no head Boolean at all, stable when the target is
  already pinned to exactly the head Boolean. Each reason clause is a
  NOGOOD: the head literal first, then the negations of the pinned
  cause facts, CONSTRAINT-VALID under the family's own constraint
  alone (for `x_i = ¬x_j` with `j` pinned `true`, the nogood is
  `[x_i = false, x_j = false]` — "not both false"). NOTE: UNIT nogoods
  (e.g. `[posBool i false]` for the j-true branch) are NOT valid
  under `boolNotSlot` alone — a solution with `x_j = false,
  x_i = true` falsifies them — so they would break `Reason.Valid`'s
  entailment half; the head+causes form here is the sound repair,
  matching the `narrowHi`/`narrowLo` discipline of Propagate.lean.

  Per family the package carries (mirroring ConstFamilies.lean):

  * views: the constraint's semantics at the Boolean reads;
  * head lemmas: the implied literal's truth at every solution of the
    constraint, from the pinned causes;
  * nogood lemmas: each emitted clause carries a true literal at
    every solution of the constraint (entitlement / entailment);
  * the soundness triple (`..._safe`): implied-true at fitting
    solutions, conflict exclusion, conflict entitlement — at EVERY
    state;
  * state-free entitlement (`..._entitled`) at every internal
    problem solution;
  * reason validity (`..._reason_safe` plus the canonical
    `..._reason_safe_sat` instantiation): `Reason.Valid` plus clause
    normalization;
  * the standalone B5 registration (`propagatorOfProvedB5`) with its
    membership/run inversions, per-family reason bridges, and the
    three front doors (`propagatorsOfProvedB5_safeUniv`,
    `_entitled`, `_reason`), restricted to the three bool families.

Dependencies:
  - LeanFzn.Solver.Propagation.Proofs.ConstFamilies: the shared `posBool_norm` lemma
    and, transitively, Theory (PropSafeUniv, SolvedBy), Propagate
    (State, the narrow/firstEvent propagator style), Encoding
    (`eval_posBool_iff`), Run (ReasonSafeUniv), Invariants
    (ProblemSolution, Reason.Valid, Clause.EntailedBy), and the
    DomConstraint layer (LeanFzn.Solver.Propagation.DomainConstraints).

DAG:
  LeanFzn.Solver.UIP.Proofs.ConstFamilies -> LeanFzn.Solver.UIP.Proofs.Fam.Bool
    -> (future, coordinator-owned) the `propagatorOfProved`
       registration extension and the Reason.lean front-door wiring.
-/

import LeanFzn.Solver.Propagation.Proofs.ConstFamilies
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Reference


open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Reference

/-! ## The Boolean pin of a slot domain -/

/-- `true` when slot `s`'s domain is exactly the singleton `[.bool b]`
    (one candidate value, and it is the Boolean `b`). -/
def domBoolPin (doms : List Domain) (s : Nat) (b : Bool) : Bool :=
  (doms.getD s []).length == 1 && valueMemB (.bool b) (doms.getD s [])

/-- Out of range, `getD` returns the empty default. -/
theorem getD_nil_of_length_le {l : List Domain} {s : Nat}
    (h : ¬ s < l.length) : l.getD s [] = [] := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none_iff.mpr (by omega)]
  rfl

/-- The pin test decides the exact singleton domain. -/
theorem domBoolPin_eq {doms : List Domain} {s : Nat} {b : Bool}
    (h : domBoolPin doms s b = true) :
    doms.getD s [] = [.bool b] := by
  obtain ⟨h1, h2⟩ := by simpa [domBoolPin, Bool.and_eq_true] using h
  have hlen : (doms.getD s []).length = 1 := by simpa using h1
  have hmem : (.bool b : Value) ∈ doms.getD s [] := valueMemB_iff.mp h2
  match hl : doms.getD s [] with
  | [] => rw [hl] at hlen; simp at hlen
  | [v] =>
      rw [hl] at hmem
      have hv : v = .bool b := (List.mem_singleton.mp hmem).symm
      subst hv
      rfl
  | v :: w :: r => rw [hl] at hlen; simp at hlen

/-- A pinned slot's read at any fitting assignment is exactly the
    pinned Boolean. -/
theorem fits_of_domBoolPin {st : State} {a : Assignment} {s : Nat} {b : Bool}
    (hfit : Core.Assignment.Fits st.domains a)
    (hpin : domBoolPin st.domains s b = true) :
    a[s]? = some (.bool b) := by
  have hd := domBoolPin_eq hpin
  have hrange : s < st.domains.length := by
    by_cases hns : s < st.domains.length
    · exact hns
    · exfalso
      rw [getD_nil_of_length_le hns] at hd
      exact absurd hd (by simp)
  have hs2 : s < a.length := by rw [hfit.1]; exact hrange
  have hread : a[s]? = some a[s] := (List.getElem?_eq_some_iff).mpr ⟨hs2, rfl⟩
  have hmem : a[s] ∈ st.domains.getD s [] := hfit.2 s a[s] hread
  rw [hd] at hmem
  have hval : a[s] = .bool b := List.mem_singleton.mp hmem
  rw [hval] at hread
  exact hread

/-! ## The single-deduction emitter

The `propConstEq` Boolean arm (Propagate.lean:393-404), generalized
    from a unit nogood to an arbitrary head-first nogood clause: the
    cause pins live OUTSIDE (the caller's branch conditions), so the
    emitter only decides the TARGET slot's shape. -/

/-- Emit one Boolean implication: the head literal `posBool s b` with
    the nogood `ng` (head first, causes negated after). Implied when
    the target domain still contains `.bool b` alongside something
    else; conflict (the same clause, then entitled but falsified by
    the domain) when it contains no `.bool b` at all; stable when the
    target is already pinned to exactly `[.bool b]`. -/
def implyBool (st : State) (s : Nat) (b : Bool) (ng : Clause) :
    PropagationResult :=
  if valueMemB (.bool b) (st.domains.getD s []) then
    if valuesEqB (st.domains.getD s []) [.bool b] then .stable
    else .implied (posBool s b) { clause := ng }
  else .conflict ng

/-- `implyBool`'s implied emission is exactly the head literal with
    the nogood as its reason clause. -/
theorem implyBool_implied_inv {st : State} {s : Nat} {b : Bool} {ng : Clause}
    {l : Literal} {r : Reason}
    (h : implyBool st s b ng = .implied l r) :
    l = posBool s b ∧ r = { clause := ng } := by
  simp only [implyBool] at h
  split at h
  · split at h
    · exact absurd h (by intro hc; cases hc)
    · injection h with h1 h2
      exact ⟨h1.symm, h2.symm⟩
  · exact absurd h (by intro hc; cases hc)

/-- `implyBool`'s conflict emission reports the nogood itself, and
    fires only when the target domain contains no head Boolean. -/
theorem implyBool_conflict_inv {st : State} {s : Nat} {b : Bool} {ng cc : Clause}
    (h : implyBool st s b ng = .conflict cc) :
    cc = ng ∧ ¬ (valueMemB (.bool b) (st.domains.getD s []) = true) := by
  simp only [implyBool] at h
  split at h
  · split at h
    · exact absurd h (by intro hc; cases hc)
    · exact absurd h (by intro hc; cases hc)
  · rename_i hnm
    refine ⟨?_, hnm⟩
    injection h with h2
    exact h2.symm

/-- The shared soundness triple of one Boolean deduction. All three
    obligations reduce to the family-independent facts about the
    emitter: the implied head is `posBool s b` (true at every fitting
    solution of the constraint by `hhead`); a conflict fires only when
    the target domain lacks the head Boolean, which contradicts
    `hhead` at any fitting solution of the constraint; and the
    conflict clause is the nogood, entitled by `hent`. -/
theorem implyBool_safe {st : State} {s : Nat} {b : Bool} {ng : Clause}
    {dom : DomConstraint}
    (hhead : ∀ a, Core.Assignment.Fits st.domains a →
      dom.SatisfiedBy a → a[s]? = some (.bool b))
    (hent : ∀ a, dom.SatisfiedBy a →
      ∃ l ∈ ng, l.eval a = some true)
    (_hmem : posBool s b ∈ ng) :
    (∀ l r, implyBool st s b ng = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        dom.SatisfiedBy a → l.eval a = some true) ∧
    (∀ cc, implyBool st s b ng = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        dom.SatisfiedBy a → False) ∧
    (∀ cc, implyBool st s b ng = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        dom.SatisfiedBy a →
        ∃ l ∈ cc, l.eval a = some true) := by
  refine ⟨?_, ?_, ?_⟩
  · intro l r hrun a hfit hsat
    obtain ⟨hl, _⟩ := implyBool_implied_inv hrun
    subst hl
    exact (eval_posBool_iff a s b).mpr (hhead a hfit hsat)
  · intro cc hrun a hfit hsat
    obtain ⟨_, hnm⟩ := implyBool_conflict_inv hrun
    exact hnm (valueMemB_iff.mpr (hfit.2 s (.bool b) (hhead a hfit hsat)))
  · intro cc hrun a _hfit hsat
    obtain ⟨hcc, _⟩ := implyBool_conflict_inv hrun
    rw [hcc]
    exact hent a hsat

/-- The shared reason-validity schema of one Boolean deduction: an
    implied emission carries the nogood as a valid (entailed via the
    family constraint, pivot-member) and normalized reason clause. -/
theorem implyBool_reason_safe
    {problem : Problem DomConstraint Unit}
    {constraintHolds : DomConstraint → Assignment → Prop}
    {st : State} {s : Nat} {b : Bool} {ng : Clause}
    {dom : DomConstraint} {l : Literal} {r : Reason}
    (himp : ∀ c a, c ∈ problem.constraints →
      constraintHolds c a → c.SatisfiedBy a)
    (hprob : dom ∈ problem.constraints)
    (hent : ∀ a, dom.SatisfiedBy a →
      ∃ q ∈ ng, q.eval a = some true)
    (hmem : posBool s b ∈ ng)
    (hnorm : ∀ q ∈ ng, q = q.norm)
    (hrun : implyBool st s b ng = .implied l r) :
    Reason.Valid problem constraintHolds r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  obtain ⟨hl, hcl⟩ := implyBool_implied_inv hrun
  refine ⟨⟨?_, by subst hl; rw [hcl]; simpa using hmem⟩, ?_⟩
  · intro a ha
    rw [hcl]
    exact hent a (himp _ a hprob (ha.2 _ hprob))
  · intro q hq
    rw [hcl] at hq
    exact hnorm q hq

/-! ## Shared literal hygiene -/

/-- A two-literal `posBool` clause is normalized. -/
theorem posBool2_norm (s1 : Nat) (b1 : Bool) (s2 : Nat) (b2 : Bool) :
    ∀ q ∈ [posBool s1 b1, posBool s2 b2], q = q.norm := by
  intro q hq
  rcases List.mem_cons.mp hq with hq | hq
  · subst hq; exact (posBool_norm s1 b1).symm
  · rw [List.mem_singleton.mp hq]
    exact (posBool_norm s2 b2).symm

/-- A three-literal `posBool` clause is normalized. -/
theorem posBool3_norm (s1 : Nat) (b1 : Bool) (s2 : Nat) (b2 : Bool)
    (s3 : Nat) (b3 : Bool) :
    ∀ q ∈ [posBool s1 b1, posBool s2 b2, posBool s3 b3], q = q.norm := by
  intro q hq
  rcases List.mem_cons.mp hq with hq | hq
  · subst hq; exact (posBool_norm s1 b1).symm
  · rcases List.mem_cons.mp hq with hq | hq
    · subst hq; exact (posBool_norm s2 b2).symm
    · rw [List.mem_singleton.mp hq]
      exact (posBool_norm s3 b3).symm

/-- Two Boolean reads of the same slot agree on the Boolean. -/
theorem bool_read_eq {a : Assignment} {s : Nat} {b b' : Bool}
    (h : a[s]? = some (.bool b)) (h' : a[s]? = some (.bool b')) :
    b = b' :=
  Value.bool.inj (Option.some.inj (h.symm.trans h'))

/-- Membership in a two-element list is order-independent. -/
theorem mem_comm2 {α : Type} {x y : α} {q : α} (h : q ∈ [x, y]) :
    q ∈ [y, x] := by
  rcases List.mem_cons.mp h with h | h
  · subst h; exact List.mem_cons_of_mem _ List.mem_cons_self
  · rw [List.mem_singleton.mp h]
    exact List.mem_cons_self

/-- The `boolNotSlot` semantics is symmetric in its two slots. -/
theorem boolNotSlot_comm (i j : Nat) (a : Assignment) :
    (DomConstraint.boolNotSlot i j).SatisfiedBy a ↔
      (DomConstraint.boolNotSlot j i).SatisfiedBy a := by
  constructor <;>
    · rintro ⟨x, y, hx, hy, hxy⟩
      rcases hxy with ⟨hx1, hy1⟩ | ⟨hx1, hy1⟩
      · exact ⟨y, x, hy, hx, Or.inr ⟨hy1, hx1⟩⟩
      · exact ⟨y, x, hy, hx, Or.inl ⟨hy1, hx1⟩⟩

/-! ## The `bool_not` family: `x_i = ¬ x_j` over slots i j -/

/-- The `boolNotSlot` semantics at the Boolean reads: opposite
    Booleans. -/
theorem boolNotSlot_views {a : Assignment} {i j : Nat}
    (h : (DomConstraint.boolNotSlot i j).SatisfiedBy a) :
    ∃ p q, a[i]? = some (.bool p) ∧ a[j]? = some (.bool q) ∧ q = !p := by
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  rcases hxy with ⟨hx1, hy1⟩ | ⟨hx1, hy1⟩
  · subst hx1; subst hy1
    exact ⟨true, false, hx, hy, rfl⟩
  · subst hx1; subst hy1
    exact ⟨false, true, hx, hy, rfl⟩

/-- Head: the read at `i`, given the read at `j`. -/
theorem boolNot_head_i_of_j {a : Assignment} {i j : Nat} {b : Bool}
    (h : (DomConstraint.boolNotSlot i j).SatisfiedBy a)
    (hj : a[j]? = some (.bool b)) :
    a[i]? = some (.bool (!b)) := by
  obtain ⟨p, q, hx, hy, hq⟩ := boolNotSlot_views h
  have hqb : q = b := bool_read_eq hy hj
  rw [hqb] at hq
  cases p with
  | true =>
      have hb : b = false := hq
      subst hb
      exact hx
  | false =>
      have hb : b = true := hq
      subst hb
      exact hx

/-- Head: the read at `j`, given the read at `i`. -/
theorem boolNot_head_j_of_i {a : Assignment} {i j : Nat} {b : Bool}
    (h : (DomConstraint.boolNotSlot i j).SatisfiedBy a)
    (hi : a[i]? = some (.bool b)) :
    a[j]? = some (.bool (!b)) := by
  obtain ⟨p, q, hx, hy, hq⟩ := boolNotSlot_views h
  have hpb : p = b := bool_read_eq hx hi
  rw [hpb] at hq
  rw [← hq]
  exact hy

/-- Nogood "not both true": one of the two slots is false at every
    solution. -/
theorem boolNot_ng_true {a : Assignment} {i j : Nat}
    (h : (DomConstraint.boolNotSlot i j).SatisfiedBy a) :
    ∃ l ∈ [posBool i true, posBool j true], l.eval a = some true := by
  obtain ⟨p, q, hx, hy, hq⟩ := boolNotSlot_views h
  cases p with
  | true =>
      exact ⟨posBool i true, List.mem_cons_self,
        (eval_posBool_iff a i true).mpr hx⟩
  | false =>
      have hq' : q = true := hq
      subst hq'
      exact ⟨posBool j true, List.mem_cons_of_mem _ List.mem_cons_self,
        (eval_posBool_iff a j true).mpr hy⟩

/-- Nogood "not both false": one of the two slots is true at every
    solution. -/
theorem boolNot_ng_false {a : Assignment} {i j : Nat}
    (h : (DomConstraint.boolNotSlot i j).SatisfiedBy a) :
    ∃ l ∈ [posBool i false, posBool j false], l.eval a = some true := by
  obtain ⟨p, q, hx, hy, hq⟩ := boolNotSlot_views h
  cases p with
  | true =>
      have hq' : q = false := hq
      subst hq'
      exact ⟨posBool j false, List.mem_cons_of_mem _ List.mem_cons_self,
        (eval_posBool_iff a j false).mpr hy⟩
  | false =>
      exact ⟨posBool i false, List.mem_cons_self,
        (eval_posBool_iff a i false).mpr hx⟩

/-- Nogood "not both false" (order-swapped variant). -/
theorem boolNot_ng_false' {a : Assignment} {i j : Nat}
    (h : (DomConstraint.boolNotSlot i j).SatisfiedBy a) :
    ∃ l ∈ [posBool j false, posBool i false], l.eval a = some true := by
  obtain ⟨l, hmem,hev⟩ := boolNot_ng_false h
  exact ⟨l, mem_comm2 hmem, hev⟩

/-- Nogood "not both true" (order-swapped variant). -/
theorem boolNot_ng_true' {a : Assignment} {i j : Nat}
    (h : (DomConstraint.boolNotSlot i j).SatisfiedBy a) :
    ∃ l ∈ [posBool j true, posBool i true], l.eval a = some true := by
  obtain ⟨l, hmem,hev⟩ := boolNot_ng_true h
  exact ⟨l, mem_comm2 hmem, hev⟩

/-- The `bool_not` propagator: when one slot is pinned, the other must
    carry the opposite Boolean. Each emission's nogood is the
    two-literal clause "one of the two slots is `<head>`" — valid
    under `x_i = ¬x_j` alone. -/
def propBoolNot (st : State) (i j : Nat) : PropagationResult :=
  if domBoolPin st.domains j true then
    implyBool st i false [posBool i false, posBool j false]
  else if domBoolPin st.domains j false then
    implyBool st i true [posBool i true, posBool j true]
  else if domBoolPin st.domains i true then
    implyBool st j false [posBool j false, posBool i false]
  else if domBoolPin st.domains i false then
    implyBool st j true [posBool j true, posBool i true]
  else .stable

/-- Emission inversion for `propBoolNot`: every non-stable result is
    one of the four pin branches at its own emitter. -/
theorem propBoolNot_emit {st : State} {i j : Nat} {res : PropagationResult}
    (h : propBoolNot st i j = res) :
    (domBoolPin st.domains j true = true ∧
       implyBool st i false [posBool i false, posBool j false] = res) ∨
    (domBoolPin st.domains j false = true ∧
       implyBool st i true [posBool i true, posBool j true] = res) ∨
    (domBoolPin st.domains i true = true ∧
       implyBool st j false [posBool j false, posBool i false] = res) ∨
    (domBoolPin st.domains i false = true ∧
       implyBool st j true [posBool j true, posBool i true] = res) ∨
    res = .stable := by
  simp only [propBoolNot] at h
  split at h
  · rename_i hpin
    exact Or.inl ⟨hpin, h⟩
  · split at h
    · rename_i hpin
      exact Or.inr (Or.inl ⟨hpin, h⟩)
    · split at h
      · rename_i hpin
        exact Or.inr (Or.inr (Or.inl ⟨hpin, h⟩))
      · split at h
        · rename_i hpin
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hpin, h⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr h.symm)))

/-- The internal soundness triple of `propBoolNot` at an abstract
    result (the public `propBoolNot_safe` is this at `rfl`). -/
theorem propBoolNot_emit_safe (st : State) (i j : Nat)
    {res : PropagationResult} (h : propBoolNot st i j = res) :
    (∀ l r, res = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.boolNotSlot i j).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ cc, res = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.boolNotSlot i j).SatisfiedBy a → False) ∧
    (∀ cc, res = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.boolNotSlot i j).SatisfiedBy a →
        ∃ l ∈ cc, l.eval a = some true) := by
  rcases propBoolNot_emit h with
    ⟨hpin, hrun2⟩ | ⟨hpin, hrun2⟩ | ⟨hpin, hrun2⟩ | ⟨hpin, hrun2⟩ | hstable
  · rw [← hrun2]
    exact implyBool_safe (st := st) (s := i) (b := false)
      (ng := [posBool i false, posBool j false])
      (dom := DomConstraint.boolNotSlot i j)
      (fun a hfit hsat =>
        boolNot_head_i_of_j hsat (fits_of_domBoolPin hfit hpin))
      (fun a hsat => boolNot_ng_false (i := i) (j := j) hsat)
      List.mem_cons_self
  · rw [← hrun2]
    exact implyBool_safe (st := st) (s := i) (b := true)
      (ng := [posBool i true, posBool j true])
      (dom := DomConstraint.boolNotSlot i j)
      (fun a hfit hsat =>
        boolNot_head_i_of_j hsat (fits_of_domBoolPin hfit hpin))
      (fun a hsat => boolNot_ng_true (i := i) (j := j) hsat)
      List.mem_cons_self
  · rw [← hrun2]
    exact implyBool_safe (st := st) (s := j) (b := false)
      (ng := [posBool j false, posBool i false])
      (dom := DomConstraint.boolNotSlot i j)
      (fun a hfit hsat =>
        boolNot_head_j_of_i hsat (fits_of_domBoolPin hfit hpin))
      (fun a hsat => boolNot_ng_false' (i := i) (j := j) hsat)
      List.mem_cons_self
  · rw [← hrun2]
    exact implyBool_safe (st := st) (s := j) (b := true)
      (ng := [posBool j true, posBool i true])
      (dom := DomConstraint.boolNotSlot i j)
      (fun a hfit hsat =>
        boolNot_head_j_of_i hsat (fits_of_domBoolPin hfit hpin))
      (fun a hsat => boolNot_ng_true' (i := i) (j := j) hsat)
      List.mem_cons_self
  · rw [hstable]
    exact ⟨fun l r h => absurd h (by intro hc; cases hc),
      fun cc h => absurd h (by intro hc; cases hc),
      fun cc h => absurd h (by intro hc; cases hc)⟩

/-- The propagator of a `boolNotSlot i j` constraint: implied-literal
    soundness, conflict soundness, and entitlement, at every state. -/
theorem propBoolNot_safe (st : State) (i j : Nat) :
    (∀ l r, propBoolNot st i j = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.boolNotSlot i j).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ cc, propBoolNot st i j = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.boolNotSlot i j).SatisfiedBy a → False) ∧
    (∀ cc, propBoolNot st i j = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.boolNotSlot i j).SatisfiedBy a →
        ∃ l ∈ cc, l.eval a = some true) :=
  propBoolNot_emit_safe st i j rfl

/-- The per-family entitlement: for a `boolNotSlot` constraint in the
    problem, the propagator's conflict clause carries a true literal
    at every internal problem solution. No state premise is needed —
    the truth literal is pinned by the constraint alone. -/
theorem propBoolNot_entitled
    {problem : Problem DomConstraint Unit}
    {st : State} {i j : Nat} {cc : Clause}
    (hprob : DomConstraint.boolNotSlot i j ∈ problem.constraints)
    (hrun : propBoolNot st i j = .conflict cc)
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ cc, l.eval a = some true := by
  rcases propBoolNot_emit hrun with
    ⟨_, hrun2⟩ | ⟨_, hrun2⟩ | ⟨_, hrun2⟩ | ⟨_, hrun2⟩ | hstable
  · rw [(implyBool_conflict_inv hrun2).1]
    exact boolNot_ng_false (i := i) (j := j) (ha.2 _ hprob)
  · rw [(implyBool_conflict_inv hrun2).1]
    exact boolNot_ng_true (i := i) (j := j) (ha.2 _ hprob)
  · rw [(implyBool_conflict_inv hrun2).1]
    exact boolNot_ng_false' (i := i) (j := j) (ha.2 _ hprob)
  · rw [(implyBool_conflict_inv hrun2).1]
    exact boolNot_ng_true' (i := i) (j := j) (ha.2 _ hprob)
  · exact absurd hstable (by intro hc; cases hc)

/-- The reason-validity lemma for the `boolNot` family: an implied
    emission of `propBoolNot` carries a valid (entailed,
    pivot-member) and normalized reason clause — each two-literal
    nogood is entailed by the constraint
    `.boolNotSlot i j` at every internal problem solution, for any
    constraint semantics implying `SatisfiedBy` on the problem's
    constraints. -/
theorem propBoolNot_reason_safe
    {problem : Problem DomConstraint Unit}
    {constraintHolds : DomConstraint → Assignment → Prop}
    {st : State} {i j : Nat} {l : Literal} {r : Reason}
    (himp : ∀ c a, c ∈ problem.constraints →
      constraintHolds c a → c.SatisfiedBy a)
    (hprob : DomConstraint.boolNotSlot i j ∈ problem.constraints)
    (hrun : propBoolNot st i j = .implied l r) :
    Reason.Valid problem constraintHolds r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  rcases propBoolNot_emit hrun with
    ⟨_, hrun2⟩ | ⟨_, hrun2⟩ | ⟨_, hrun2⟩ | ⟨_, hrun2⟩ | hstable
  · exact implyBool_reason_safe himp hprob
      (fun a hsat => boolNot_ng_false (i := i) (j := j) hsat)
      List.mem_cons_self
      (posBool2_norm i false j false) hrun2
  · exact implyBool_reason_safe himp hprob
      (fun a hsat => boolNot_ng_true (i := i) (j := j) hsat)
      List.mem_cons_self
      (posBool2_norm i true j true) hrun2
  · exact implyBool_reason_safe himp hprob
      (fun a hsat => boolNot_ng_false' (i := i) (j := j) hsat)
      List.mem_cons_self
      (posBool2_norm j false i false) hrun2
  · exact implyBool_reason_safe himp hprob
      (fun a hsat => boolNot_ng_true' (i := i) (j := j) hsat)
      List.mem_cons_self
      (posBool2_norm j true i true) hrun2
  · exact absurd hstable (by intro hc; cases hc)

/-- The canonical `DomConstraint.SatisfiedBy` instantiation: no
    bridge premise. -/
theorem propBoolNot_reason_safe_sat
    {problem : Problem DomConstraint Unit}
    {st : State} {i j : Nat} {l : Literal} {r : Reason}
    (hprob : DomConstraint.boolNotSlot i j ∈ problem.constraints)
    (hrun : propBoolNot st i j = .implied l r) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l ∧
      (∀ q ∈ r.clause, q = q.norm) :=
  propBoolNot_reason_safe (fun _ _ _ h => h) hprob hrun

/-! ## The `bool_and` family: `x_k = x_i ∧ x_j` (k is the output) -/

/-- The `boolAndSlot` semantics at the Boolean reads (the
    `SatisfiedBy` arm itself, re-packaged). -/
theorem boolAndSlot_views {a : Assignment} {i j k : Nat}
    (h : (DomConstraint.boolAndSlot i j k).SatisfiedBy a) :
    ∃ p q r, a[i]? = some (.bool p) ∧ a[j]? = some (.bool q) ∧
      a[k]? = some (.bool r) ∧ (p && q) = r := h

/-- Head: the output read, given both input reads. -/
theorem boolAnd_head_k_of_ij {a : Assignment} {i j k : Nat} {bi bj : Bool}
    (h : (DomConstraint.boolAndSlot i j k).SatisfiedBy a)
    (hi : a[i]? = some (.bool bi)) (hj : a[j]? = some (.bool bj)) :
    a[k]? = some (.bool (bi && bj)) := by
  obtain ⟨p, q, r, hx, hy, hz, hpq⟩ := h
  have h1 : p = bi := bool_read_eq hx hi
  have h2 : q = bj := bool_read_eq hy hj
  rw [h1, h2] at hpq
  rw [hpq]
  exact hz

/-- Head: the `j` read, given `i` pinned true and the output read. -/
theorem boolAnd_head_j_of_i_true {a : Assignment} {i j k : Nat} {bk : Bool}
    (h : (DomConstraint.boolAndSlot i j k).SatisfiedBy a)
    (hi : a[i]? = some (.bool true)) (hk : a[k]? = some (.bool bk)) :
    a[j]? = some (.bool bk) := by
  obtain ⟨p, q, r, hx, hy, hz, hpq⟩ := h
  have h1 : p = true := bool_read_eq hx hi
  rw [h1] at hpq
  have hqr : q = r := hpq
  have h3 : r = bk := bool_read_eq hz hk
  rw [h3] at hqr
  rw [hqr] at hy
  exact hy

/-- Head: the `i` read, given `j` pinned true and the output read. -/
theorem boolAnd_head_i_of_j_true {a : Assignment} {i j k : Nat} {bk : Bool}
    (h : (DomConstraint.boolAndSlot i j k).SatisfiedBy a)
    (hj : a[j]? = some (.bool true)) (hk : a[k]? = some (.bool bk)) :
    a[i]? = some (.bool bk) := by
  obtain ⟨p, q, r, hx, hy, hz, hpq⟩ := h
  have h2 : q = true := bool_read_eq hy hj
  rw [h2] at hpq
  cases p with
  | true =>
      have hr : r = true := hpq.symm
      subst hr
      have h3 : true = bk := bool_read_eq hz hk
      subst h3
      exact hx
  | false =>
      have hr : r = false := hpq.symm
      subst hr
      have h3 : false = bk := bool_read_eq hz hk
      subst h3
      exact hx

/-- Head: the output read, given `i` pinned false. -/
theorem boolAnd_head_k_of_i_false {a : Assignment} {i j k : Nat}
    (h : (DomConstraint.boolAndSlot i j k).SatisfiedBy a)
    (hi : a[i]? = some (.bool false)) :
    a[k]? = some (.bool false) := by
  obtain ⟨p, q, r, hx, hy, hz, hpq⟩ := h
  have h1 : p = false := bool_read_eq hx hi
  rw [h1] at hpq
  have hr : r = false := hpq.symm
  subst hr
  exact hz

/-- Head: the output read, given `j` pinned false. -/
theorem boolAnd_head_k_of_j_false {a : Assignment} {i j k : Nat}
    (h : (DomConstraint.boolAndSlot i j k).SatisfiedBy a)
    (hj : a[j]? = some (.bool false)) :
    a[k]? = some (.bool false) := by
  obtain ⟨p, q, r, hx, hy, hz, hpq⟩ := h
  have h2 : q = false := bool_read_eq hy hj
  rw [h2] at hpq
  cases p with
  | true =>
      have hr : r = false := hpq.symm
      subst hr
      exact hz
  | false =>
      have hr : r = false := hpq.symm
      subst hr
      exact hz

/-- Literal set of the three-literal and-nogoods: at every solution,
    one of `i = false`, `j = false`, `k = true` holds. -/
theorem boolAnd_ff_t_lits {a : Assignment} {i j k : Nat}
    (h : (DomConstraint.boolAndSlot i j k).SatisfiedBy a) :
    (posBool i false).eval a = some true ∨
      (posBool j false).eval a = some true ∨
      (posBool k true).eval a = some true := by
  obtain ⟨p, q, r, hx, hy, hz, hpq⟩ := h
  cases p with
  | false =>
      exact Or.inl ((eval_posBool_iff a i false).mpr hx)
  | true =>
      cases q with
      | false =>
          exact Or.inr (Or.inl ((eval_posBool_iff a j false).mpr hy))
      | true =>
          have hr : r = true := hpq.symm
          subst hr
          exact Or.inr (Or.inr ((eval_posBool_iff a k true).mpr hz))

/-- Literal set of the `[k = false, i = true]` nogood. -/
theorem boolAnd_kf_it_lits {a : Assignment} {i j k : Nat}
    (h : (DomConstraint.boolAndSlot i j k).SatisfiedBy a) :
    (posBool k false).eval a = some true ∨
      (posBool i true).eval a = some true := by
  obtain ⟨p, q, r, hx, hy, hz, hpq⟩ := h
  cases p with
  | true =>
      exact Or.inr ((eval_posBool_iff a i true).mpr hx)
  | false =>
      have hr : r = false := hpq.symm
      subst hr
      exact Or.inl ((eval_posBool_iff a k false).mpr hz)

/-- Literal set of the `[k = false, j = true]` nogood. -/
theorem boolAnd_kf_jt_lits {a : Assignment} {i j k : Nat}
    (h : (DomConstraint.boolAndSlot i j k).SatisfiedBy a) :
    (posBool k false).eval a = some true ∨
      (posBool j true).eval a = some true := by
  obtain ⟨p, q, r, hx, hy, hz, hpq⟩ := h
  cases q with
  | true =>
      exact Or.inr ((eval_posBool_iff a j true).mpr hy)
  | false =>
      cases p with
      | true =>
          have hr : r = false := hpq.symm
          subst hr
          exact Or.inl ((eval_posBool_iff a k false).mpr hz)
      | false =>
          have hr : r = false := hpq.symm
          subst hr
          exact Or.inl ((eval_posBool_iff a k false).mpr hz)

/-- Nogood `[k = true, i = false, j = false]` (both inputs true forces
    the output true). -/
theorem boolAnd_ng_k_true {a : Assignment} {i j k : Nat}
    (h : (DomConstraint.boolAndSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [posBool k true, posBool i false, posBool j false],
      l.eval a = some true := by
  rcases boolAnd_ff_t_lits h with hi | hj | hk
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hi⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self), hj⟩
  · exact ⟨_, List.mem_cons_self, hk⟩

/-- Nogood `[j = false, i = false, k = true]` (input true and output
    false forces the other input false). -/
theorem boolAnd_ng_j_false {a : Assignment} {i j k : Nat}
    (h : (DomConstraint.boolAndSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [posBool j false, posBool i false, posBool k true],
      l.eval a = some true := by
  rcases boolAnd_ff_t_lits h with hi | hj | hk
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hi⟩
  · exact ⟨_, List.mem_cons_self, hj⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self), hk⟩

/-- Nogood `[i = false, j = false, k = true]` (the symmetric backward
    deduction). -/
theorem boolAnd_ng_i_false {a : Assignment} {i j k : Nat}
    (h : (DomConstraint.boolAndSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [posBool i false, posBool j false, posBool k true],
      l.eval a = some true := by
  rcases boolAnd_ff_t_lits h with hi | hj | hk
  · exact ⟨_, List.mem_cons_self, hi⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hj⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self), hk⟩

/-- Nogood `[k = false, i = true]` (a false input forces the output
    false). -/
theorem boolAnd_ng_kf_i {a : Assignment} {i j k : Nat}
    (h : (DomConstraint.boolAndSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [posBool k false, posBool i true], l.eval a = some true := by
  rcases boolAnd_kf_it_lits h with hk | hi
  · exact ⟨_, List.mem_cons_self, hk⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hi⟩

/-- Nogood `[k = false, j = true]` (the symmetric false-input
    deduction). -/
theorem boolAnd_ng_kf_j {a : Assignment} {i j k : Nat}
    (h : (DomConstraint.boolAndSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [posBool k false, posBool j true], l.eval a = some true := by
  rcases boolAnd_kf_jt_lits h with hk | hj
  · exact ⟨_, List.mem_cons_self, hk⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hj⟩

/-- The `bool_and` propagator: five deductions over the three
    Booleans — forward (both inputs true → output true), backward
    (an input true and the output false → the other input false, both
    ways), and false-input (either input false → output false, both
    ways). Each nogood is constraint-valid under `x_k = x_i ∧ x_j`
    alone. -/
def propBoolAnd (st : State) (i j k : Nat) : PropagationResult :=
  if domBoolPin st.domains i true && domBoolPin st.domains j true then
    implyBool st k true [posBool k true, posBool i false, posBool j false]
  else if domBoolPin st.domains i true && domBoolPin st.domains k false then
    implyBool st j false [posBool j false, posBool i false, posBool k true]
  else if domBoolPin st.domains j true && domBoolPin st.domains k false then
    implyBool st i false [posBool i false, posBool j false, posBool k true]
  else if domBoolPin st.domains i false then
    implyBool st k false [posBool k false, posBool i true]
  else if domBoolPin st.domains j false then
    implyBool st k false [posBool k false, posBool j true]
  else .stable

/-- Emission inversion for `propBoolAnd`. -/
theorem propBoolAnd_emit {st : State} {i j k : Nat}
    {res : PropagationResult} (h : propBoolAnd st i j k = res) :
    (domBoolPin st.domains i true = true ∧
       domBoolPin st.domains j true = true ∧
       implyBool st k true
         [posBool k true, posBool i false, posBool j false] = res) ∨
    (domBoolPin st.domains i true = true ∧
       domBoolPin st.domains k false = true ∧
       implyBool st j false
         [posBool j false, posBool i false, posBool k true] = res) ∨
    (domBoolPin st.domains j true = true ∧
       domBoolPin st.domains k false = true ∧
       implyBool st i false
         [posBool i false, posBool j false, posBool k true] = res) ∨
    (domBoolPin st.domains i false = true ∧
       implyBool st k false [posBool k false, posBool i true] = res) ∨
    (domBoolPin st.domains j false = true ∧
       implyBool st k false [posBool k false, posBool j true] = res) ∨
    res = .stable := by
  simp only [propBoolAnd] at h
  split at h
  · rename_i hcond
    obtain ⟨h1, h2⟩ := by simpa [Bool.and_eq_true] using hcond
    exact Or.inl ⟨h1, h2, h⟩
  · split at h
    · rename_i hcond
      obtain ⟨h1, h2⟩ := by simpa [Bool.and_eq_true] using hcond
      exact Or.inr (Or.inl ⟨h1, h2, h⟩)
    · split at h
      · rename_i hcond
        obtain ⟨h1, h2⟩ := by simpa [Bool.and_eq_true] using hcond
        exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h⟩))
      · split at h
        · rename_i hpin
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hpin, h⟩)))
        · split at h
          · rename_i hpin
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hpin, h⟩))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h.symm))))

/-- The internal soundness triple of `propBoolAnd` at an abstract
    result. -/
theorem propBoolAnd_emit_safe (st : State) (i j k : Nat)
    {res : PropagationResult} (h : propBoolAnd st i j k = res) :
    (∀ l r, res = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.boolAndSlot i j k).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ cc, res = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.boolAndSlot i j k).SatisfiedBy a → False) ∧
    (∀ cc, res = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.boolAndSlot i j k).SatisfiedBy a →
        ∃ l ∈ cc, l.eval a = some true) := by
  rcases propBoolAnd_emit h with
    ⟨hpi, hpj, hrun2⟩ | ⟨hpi, hpk, hrun2⟩ | ⟨hpj, hpk, hrun2⟩ |
    ⟨hpi, hrun2⟩ | ⟨hpj, hrun2⟩ | hstable
  · rw [← hrun2]
    exact implyBool_safe (st := st) (s := k) (b := true)
      (ng := [posBool k true, posBool i false, posBool j false])
      (dom := DomConstraint.boolAndSlot i j k)
      (fun a hfit hsat =>
        boolAnd_head_k_of_ij hsat (fits_of_domBoolPin hfit hpi)
          (fits_of_domBoolPin hfit hpj))
      (fun a hsat => boolAnd_ng_k_true (i := i) (j := j) (k := k) hsat)
      List.mem_cons_self
  · rw [← hrun2]
    exact implyBool_safe (st := st) (s := j) (b := false)
      (ng := [posBool j false, posBool i false, posBool k true])
      (dom := DomConstraint.boolAndSlot i j k)
      (fun a hfit hsat =>
        boolAnd_head_j_of_i_true hsat (fits_of_domBoolPin hfit hpi)
          (fits_of_domBoolPin hfit hpk))
      (fun a hsat => boolAnd_ng_j_false (i := i) (j := j) (k := k) hsat)
      List.mem_cons_self
  · rw [← hrun2]
    exact implyBool_safe (st := st) (s := i) (b := false)
      (ng := [posBool i false, posBool j false, posBool k true])
      (dom := DomConstraint.boolAndSlot i j k)
      (fun a hfit hsat =>
        boolAnd_head_i_of_j_true hsat (fits_of_domBoolPin hfit hpj)
          (fits_of_domBoolPin hfit hpk))
      (fun a hsat => boolAnd_ng_i_false (i := i) (j := j) (k := k) hsat)
      List.mem_cons_self
  · rw [← hrun2]
    exact implyBool_safe (st := st) (s := k) (b := false)
      (ng := [posBool k false, posBool i true])
      (dom := DomConstraint.boolAndSlot i j k)
      (fun a hfit hsat =>
        boolAnd_head_k_of_i_false hsat (fits_of_domBoolPin hfit hpi))
      (fun a hsat => boolAnd_ng_kf_i (i := i) (j := j) (k := k) hsat)
      List.mem_cons_self
  · rw [← hrun2]
    exact implyBool_safe (st := st) (s := k) (b := false)
      (ng := [posBool k false, posBool j true])
      (dom := DomConstraint.boolAndSlot i j k)
      (fun a hfit hsat =>
        boolAnd_head_k_of_j_false hsat (fits_of_domBoolPin hfit hpj))
      (fun a hsat => boolAnd_ng_kf_j (i := i) (j := j) (k := k) hsat)
      List.mem_cons_self
  · rw [hstable]
    exact ⟨fun l r h => absurd h (by intro hc; cases hc),
      fun cc h => absurd h (by intro hc; cases hc),
      fun cc h => absurd h (by intro hc; cases hc)⟩

/-- The propagator of a `boolAndSlot i j k` constraint: the soundness
    triple, at every state. -/
theorem propBoolAnd_safe (st : State) (i j k : Nat) :
    (∀ l r, propBoolAnd st i j k = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.boolAndSlot i j k).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ cc, propBoolAnd st i j k = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.boolAndSlot i j k).SatisfiedBy a → False) ∧
    (∀ cc, propBoolAnd st i j k = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.boolAndSlot i j k).SatisfiedBy a →
        ∃ l ∈ cc, l.eval a = some true) :=
  propBoolAnd_emit_safe st i j k rfl

/-- The per-family entitlement for the `boolAndSlot` family. -/
theorem propBoolAnd_entitled
    {problem : Problem DomConstraint Unit}
    {st : State} {i j k : Nat} {cc : Clause}
    (hprob : DomConstraint.boolAndSlot i j k ∈ problem.constraints)
    (hrun : propBoolAnd st i j k = .conflict cc)
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ cc, l.eval a = some true := by
  rcases propBoolAnd_emit hrun with
    ⟨_, _, hrun2⟩ | ⟨_, _, hrun2⟩ | ⟨_, _, hrun2⟩ | ⟨_, hrun2⟩ |
    ⟨_, hrun2⟩ | hstable
  · rw [(implyBool_conflict_inv hrun2).1]
    exact boolAnd_ng_k_true (i := i) (j := j) (k := k) (ha.2 _ hprob)
  · rw [(implyBool_conflict_inv hrun2).1]
    exact boolAnd_ng_j_false (i := i) (j := j) (k := k) (ha.2 _ hprob)
  · rw [(implyBool_conflict_inv hrun2).1]
    exact boolAnd_ng_i_false (i := i) (j := j) (k := k) (ha.2 _ hprob)
  · rw [(implyBool_conflict_inv hrun2).1]
    exact boolAnd_ng_kf_i (i := i) (j := j) (k := k) (ha.2 _ hprob)
  · rw [(implyBool_conflict_inv hrun2).1]
    exact boolAnd_ng_kf_j (i := i) (j := j) (k := k) (ha.2 _ hprob)
  · exact absurd hstable (by intro hc; cases hc)

/-- The reason-validity lemma for the `boolAndSlot` family. -/
theorem propBoolAnd_reason_safe
    {problem : Problem DomConstraint Unit}
    {constraintHolds : DomConstraint → Assignment → Prop}
    {st : State} {i j k : Nat} {l : Literal} {r : Reason}
    (himp : ∀ c a, c ∈ problem.constraints →
      constraintHolds c a → c.SatisfiedBy a)
    (hprob : DomConstraint.boolAndSlot i j k ∈ problem.constraints)
    (hrun : propBoolAnd st i j k = .implied l r) :
    Reason.Valid problem constraintHolds r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  rcases propBoolAnd_emit hrun with
    ⟨_, _, hrun2⟩ | ⟨_, _, hrun2⟩ | ⟨_, _, hrun2⟩ | ⟨_, hrun2⟩ |
    ⟨_, hrun2⟩ | hstable
  · exact implyBool_reason_safe himp hprob
      (fun a hsat => boolAnd_ng_k_true (i := i) (j := j) (k := k) hsat)
      List.mem_cons_self
      (posBool3_norm k true i false j false) hrun2
  · exact implyBool_reason_safe himp hprob
      (fun a hsat => boolAnd_ng_j_false (i := i) (j := j) (k := k) hsat)
      List.mem_cons_self
      (posBool3_norm j false i false k true) hrun2
  · exact implyBool_reason_safe himp hprob
      (fun a hsat => boolAnd_ng_i_false (i := i) (j := j) (k := k) hsat)
      List.mem_cons_self
      (posBool3_norm i false j false k true) hrun2
  · exact implyBool_reason_safe himp hprob
      (fun a hsat => boolAnd_ng_kf_i (i := i) (j := j) (k := k) hsat)
      List.mem_cons_self
      (posBool2_norm k false i true) hrun2
  · exact implyBool_reason_safe himp hprob
      (fun a hsat => boolAnd_ng_kf_j (i := i) (j := j) (k := k) hsat)
      List.mem_cons_self
      (posBool2_norm k false j true) hrun2
  · exact absurd hstable (by intro hc; cases hc)

/-- The canonical `DomConstraint.SatisfiedBy` instantiation. -/
theorem propBoolAnd_reason_safe_sat
    {problem : Problem DomConstraint Unit}
    {st : State} {i j k : Nat} {l : Literal} {r : Reason}
    (hprob : DomConstraint.boolAndSlot i j k ∈ problem.constraints)
    (hrun : propBoolAnd st i j k = .implied l r) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l ∧
      (∀ q ∈ r.clause, q = q.norm) :=
  propBoolAnd_reason_safe (fun _ _ _ h => h) hprob hrun

/-! ## The `bool_or` family: `x_k = x_i ∨ x_j` (k is the output) -/

/-- The `boolOrSlot` semantics at the Boolean reads (the
    `SatisfiedBy` arm itself, re-packaged). -/
theorem boolOrSlot_views {a : Assignment} {i j k : Nat}
    (h : (DomConstraint.boolOrSlot i j k).SatisfiedBy a) :
    ∃ p q r, a[i]? = some (.bool p) ∧ a[j]? = some (.bool q) ∧
      a[k]? = some (.bool r) ∧ (p || q) = r := h

/-- Head: the output read, given both input reads. -/
theorem boolOr_head_k_of_ij {a : Assignment} {i j k : Nat} {bi bj : Bool}
    (h : (DomConstraint.boolOrSlot i j k).SatisfiedBy a)
    (hi : a[i]? = some (.bool bi)) (hj : a[j]? = some (.bool bj)) :
    a[k]? = some (.bool (bi || bj)) := by
  obtain ⟨p, q, r, hx, hy, hz, hpq⟩ := h
  have h1 : p = bi := bool_read_eq hx hi
  have h2 : q = bj := bool_read_eq hy hj
  rw [h1, h2] at hpq
  rw [hpq]
  exact hz

/-- Head: the `j` read, given `i` pinned false and the output read. -/
theorem boolOr_head_j_of_i_false {a : Assignment} {i j k : Nat} {bk : Bool}
    (h : (DomConstraint.boolOrSlot i j k).SatisfiedBy a)
    (hi : a[i]? = some (.bool false)) (hk : a[k]? = some (.bool bk)) :
    a[j]? = some (.bool bk) := by
  obtain ⟨p, q, r, hx, hy, hz, hpq⟩ := h
  have h1 : p = false := bool_read_eq hx hi
  rw [h1] at hpq
  have hqr : q = r := hpq
  have h3 : r = bk := bool_read_eq hz hk
  rw [h3] at hqr
  rw [hqr] at hy
  exact hy

/-- Head: the `i` read, given `j` pinned false and the output read. -/
theorem boolOr_head_i_of_j_false {a : Assignment} {i j k : Nat} {bk : Bool}
    (h : (DomConstraint.boolOrSlot i j k).SatisfiedBy a)
    (hj : a[j]? = some (.bool false)) (hk : a[k]? = some (.bool bk)) :
    a[i]? = some (.bool bk) := by
  obtain ⟨p, q, r, hx, hy, hz, hpq⟩ := h
  have h2 : q = false := bool_read_eq hy hj
  rw [h2] at hpq
  cases p with
  | true =>
      have hr : r = true := hpq.symm
      subst hr
      have h3 : true = bk := bool_read_eq hz hk
      subst h3
      exact hx
  | false =>
      have hr : r = false := hpq.symm
      subst hr
      have h3 : false = bk := bool_read_eq hz hk
      subst h3
      exact hx

/-- Head: the output read, given `i` pinned true. -/
theorem boolOr_head_k_of_i_true {a : Assignment} {i j k : Nat}
    (h : (DomConstraint.boolOrSlot i j k).SatisfiedBy a)
    (hi : a[i]? = some (.bool true)) :
    a[k]? = some (.bool true) := by
  obtain ⟨p, q, r, hx, hy, hz, hpq⟩ := h
  have h1 : p = true := bool_read_eq hx hi
  rw [h1] at hpq
  have hr : r = true := hpq.symm
  subst hr
  exact hz

/-- Head: the output read, given `j` pinned true. -/
theorem boolOr_head_k_of_j_true {a : Assignment} {i j k : Nat}
    (h : (DomConstraint.boolOrSlot i j k).SatisfiedBy a)
    (hj : a[j]? = some (.bool true)) :
    a[k]? = some (.bool true) := by
  obtain ⟨p, q, r, hx, hy, hz, hpq⟩ := h
  have h2 : q = true := bool_read_eq hy hj
  rw [h2] at hpq
  cases p with
  | true =>
      have hr : r = true := hpq.symm
      subst hr
      exact hz
  | false =>
      have hr : r = true := hpq.symm
      subst hr
      exact hz

/-- Literal set of the three-literal or-nogoods: at every solution,
    one of `i = true`, `j = true`, `k = false` holds. -/
theorem boolOr_tt_f_lits {a : Assignment} {i j k : Nat}
    (h : (DomConstraint.boolOrSlot i j k).SatisfiedBy a) :
    (posBool i true).eval a = some true ∨
      (posBool j true).eval a = some true ∨
      (posBool k false).eval a = some true := by
  obtain ⟨p, q, r, hx, hy, hz, hpq⟩ := h
  cases p with
  | true =>
      exact Or.inl ((eval_posBool_iff a i true).mpr hx)
  | false =>
      cases q with
      | true =>
          exact Or.inr (Or.inl ((eval_posBool_iff a j true).mpr hy))
      | false =>
          have hr : r = false := hpq.symm
          subst hr
          exact Or.inr (Or.inr ((eval_posBool_iff a k false).mpr hz))

/-- Literal set of the `[k = true, i = false]` nogood. -/
theorem boolOr_kt_if_lits {a : Assignment} {i j k : Nat}
    (h : (DomConstraint.boolOrSlot i j k).SatisfiedBy a) :
    (posBool k true).eval a = some true ∨
      (posBool i false).eval a = some true := by
  obtain ⟨p, q, r, hx, hy, hz, hpq⟩ := h
  cases p with
  | false =>
      exact Or.inr ((eval_posBool_iff a i false).mpr hx)
  | true =>
      have hr : r = true := hpq.symm
      subst hr
      exact Or.inl ((eval_posBool_iff a k true).mpr hz)

/-- Literal set of the `[k = true, j = false]` nogood. -/
theorem boolOr_kt_jf_lits {a : Assignment} {i j k : Nat}
    (h : (DomConstraint.boolOrSlot i j k).SatisfiedBy a) :
    (posBool k true).eval a = some true ∨
      (posBool j false).eval a = some true := by
  obtain ⟨p, q, r, hx, hy, hz, hpq⟩ := h
  cases q with
  | false =>
      exact Or.inr ((eval_posBool_iff a j false).mpr hy)
  | true =>
      cases p with
      | true =>
          have hr : r = true := hpq.symm
          subst hr
          exact Or.inl ((eval_posBool_iff a k true).mpr hz)
      | false =>
          have hr : r = true := hpq.symm
          subst hr
          exact Or.inl ((eval_posBool_iff a k true).mpr hz)

/-- Nogood `[k = false, i = true, j = true]` (both inputs false forces
    the output false). -/
theorem boolOr_ng_k_false {a : Assignment} {i j k : Nat}
    (h : (DomConstraint.boolOrSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [posBool k false, posBool i true, posBool j true],
      l.eval a = some true := by
  rcases boolOr_tt_f_lits h with hi | hj | hk
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hi⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self), hj⟩
  · exact ⟨_, List.mem_cons_self, hk⟩

/-- Nogood `[j = true, i = true, k = false]` (input false and output
    true forces the other input true). -/
theorem boolOr_ng_j_true {a : Assignment} {i j k : Nat}
    (h : (DomConstraint.boolOrSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [posBool j true, posBool i true, posBool k false],
      l.eval a = some true := by
  rcases boolOr_tt_f_lits h with hi | hj | hk
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hi⟩
  · exact ⟨_, List.mem_cons_self, hj⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self), hk⟩

/-- Nogood `[i = true, j = true, k = false]` (the symmetric backward
    deduction). -/
theorem boolOr_ng_i_true {a : Assignment} {i j k : Nat}
    (h : (DomConstraint.boolOrSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [posBool i true, posBool j true, posBool k false],
      l.eval a = some true := by
  rcases boolOr_tt_f_lits h with hi | hj | hk
  · exact ⟨_, List.mem_cons_self, hi⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hj⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self), hk⟩

/-- Nogood `[k = true, i = false]` (a true input forces the output
    true). -/
theorem boolOr_ng_kt_i {a : Assignment} {i j k : Nat}
    (h : (DomConstraint.boolOrSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [posBool k true, posBool i false], l.eval a = some true := by
  rcases boolOr_kt_if_lits h with hk | hi
  · exact ⟨_, List.mem_cons_self, hk⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hi⟩

/-- Nogood `[k = true, j = false]` (the symmetric true-input
    deduction). -/
theorem boolOr_ng_kt_j {a : Assignment} {i j k : Nat}
    (h : (DomConstraint.boolOrSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [posBool k true, posBool j false], l.eval a = some true := by
  rcases boolOr_kt_jf_lits h with hk | hj
  · exact ⟨_, List.mem_cons_self, hk⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hj⟩

/-- The `bool_or` propagator: the De Morgan dual of `propBoolAnd` —
    forward (both inputs false → output false), backward (an input
    false and the output true → the other input true, both ways), and
    true-input (either input true → output true, both ways). Each
    nogood is constraint-valid under `x_k = x_i ∨ x_j` alone. -/
def propBoolOr (st : State) (i j k : Nat) : PropagationResult :=
  if domBoolPin st.domains i false && domBoolPin st.domains j false then
    implyBool st k false [posBool k false, posBool i true, posBool j true]
  else if domBoolPin st.domains i false && domBoolPin st.domains k true then
    implyBool st j true [posBool j true, posBool i true, posBool k false]
  else if domBoolPin st.domains j false && domBoolPin st.domains k true then
    implyBool st i true [posBool i true, posBool j true, posBool k false]
  else if domBoolPin st.domains i true then
    implyBool st k true [posBool k true, posBool i false]
  else if domBoolPin st.domains j true then
    implyBool st k true [posBool k true, posBool j false]
  else .stable

/-- Emission inversion for `propBoolOr`. -/
theorem propBoolOr_emit {st : State} {i j k : Nat}
    {res : PropagationResult} (h : propBoolOr st i j k = res) :
    (domBoolPin st.domains i false = true ∧
       domBoolPin st.domains j false = true ∧
       implyBool st k false
         [posBool k false, posBool i true, posBool j true] = res) ∨
    (domBoolPin st.domains i false = true ∧
       domBoolPin st.domains k true = true ∧
       implyBool st j true
         [posBool j true, posBool i true, posBool k false] = res) ∨
    (domBoolPin st.domains j false = true ∧
       domBoolPin st.domains k true = true ∧
       implyBool st i true
         [posBool i true, posBool j true, posBool k false] = res) ∨
    (domBoolPin st.domains i true = true ∧
       implyBool st k true [posBool k true, posBool i false] = res) ∨
    (domBoolPin st.domains j true = true ∧
       implyBool st k true [posBool k true, posBool j false] = res) ∨
    res = .stable := by
  simp only [propBoolOr] at h
  split at h
  · rename_i hcond
    obtain ⟨h1, h2⟩ := by simpa [Bool.and_eq_true] using hcond
    exact Or.inl ⟨h1, h2, h⟩
  · split at h
    · rename_i hcond
      obtain ⟨h1, h2⟩ := by simpa [Bool.and_eq_true] using hcond
      exact Or.inr (Or.inl ⟨h1, h2, h⟩)
    · split at h
      · rename_i hcond
        obtain ⟨h1, h2⟩ := by simpa [Bool.and_eq_true] using hcond
        exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h⟩))
      · split at h
        · rename_i hpin
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hpin, h⟩)))
        · split at h
          · rename_i hpin
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hpin, h⟩))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h.symm))))

/-- The internal soundness triple of `propBoolOr` at an abstract
    result. -/
theorem propBoolOr_emit_safe (st : State) (i j k : Nat)
    {res : PropagationResult} (h : propBoolOr st i j k = res) :
    (∀ l r, res = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.boolOrSlot i j k).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ cc, res = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.boolOrSlot i j k).SatisfiedBy a → False) ∧
    (∀ cc, res = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.boolOrSlot i j k).SatisfiedBy a →
        ∃ l ∈ cc, l.eval a = some true) := by
  rcases propBoolOr_emit h with
    ⟨hpi, hpj, hrun2⟩ | ⟨hpi, hpk, hrun2⟩ | ⟨hpj, hpk, hrun2⟩ |
    ⟨hpi, hrun2⟩ | ⟨hpj, hrun2⟩ | hstable
  · rw [← hrun2]
    exact implyBool_safe (st := st) (s := k) (b := false)
      (ng := [posBool k false, posBool i true, posBool j true])
      (dom := DomConstraint.boolOrSlot i j k)
      (fun a hfit hsat =>
        boolOr_head_k_of_ij hsat (fits_of_domBoolPin hfit hpi)
          (fits_of_domBoolPin hfit hpj))
      (fun a hsat => boolOr_ng_k_false (i := i) (j := j) (k := k) hsat)
      List.mem_cons_self
  · rw [← hrun2]
    exact implyBool_safe (st := st) (s := j) (b := true)
      (ng := [posBool j true, posBool i true, posBool k false])
      (dom := DomConstraint.boolOrSlot i j k)
      (fun a hfit hsat =>
        boolOr_head_j_of_i_false hsat (fits_of_domBoolPin hfit hpi)
          (fits_of_domBoolPin hfit hpk))
      (fun a hsat => boolOr_ng_j_true (i := i) (j := j) (k := k) hsat)
      List.mem_cons_self
  · rw [← hrun2]
    exact implyBool_safe (st := st) (s := i) (b := true)
      (ng := [posBool i true, posBool j true, posBool k false])
      (dom := DomConstraint.boolOrSlot i j k)
      (fun a hfit hsat =>
        boolOr_head_i_of_j_false hsat (fits_of_domBoolPin hfit hpj)
          (fits_of_domBoolPin hfit hpk))
      (fun a hsat => boolOr_ng_i_true (i := i) (j := j) (k := k) hsat)
      List.mem_cons_self
  · rw [← hrun2]
    exact implyBool_safe (st := st) (s := k) (b := true)
      (ng := [posBool k true, posBool i false])
      (dom := DomConstraint.boolOrSlot i j k)
      (fun a hfit hsat =>
        boolOr_head_k_of_i_true hsat (fits_of_domBoolPin hfit hpi))
      (fun a hsat => boolOr_ng_kt_i (i := i) (j := j) (k := k) hsat)
      List.mem_cons_self
  · rw [← hrun2]
    exact implyBool_safe (st := st) (s := k) (b := true)
      (ng := [posBool k true, posBool j false])
      (dom := DomConstraint.boolOrSlot i j k)
      (fun a hfit hsat =>
        boolOr_head_k_of_j_true hsat (fits_of_domBoolPin hfit hpj))
      (fun a hsat => boolOr_ng_kt_j (i := i) (j := j) (k := k) hsat)
      List.mem_cons_self
  · rw [hstable]
    exact ⟨fun l r h => absurd h (by intro hc; cases hc),
      fun cc h => absurd h (by intro hc; cases hc),
      fun cc h => absurd h (by intro hc; cases hc)⟩

/-- The propagator of a `boolOrSlot i j k` constraint: the soundness
    triple, at every state. -/
theorem propBoolOr_safe (st : State) (i j k : Nat) :
    (∀ l r, propBoolOr st i j k = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.boolOrSlot i j k).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ cc, propBoolOr st i j k = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.boolOrSlot i j k).SatisfiedBy a → False) ∧
    (∀ cc, propBoolOr st i j k = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.boolOrSlot i j k).SatisfiedBy a →
        ∃ l ∈ cc, l.eval a = some true) :=
  propBoolOr_emit_safe st i j k rfl

/-- The per-family entitlement for the `boolOrSlot` family. -/
theorem propBoolOr_entitled
    {problem : Problem DomConstraint Unit}
    {st : State} {i j k : Nat} {cc : Clause}
    (hprob : DomConstraint.boolOrSlot i j k ∈ problem.constraints)
    (hrun : propBoolOr st i j k = .conflict cc)
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ cc, l.eval a = some true := by
  rcases propBoolOr_emit hrun with
    ⟨_, _, hrun2⟩ | ⟨_, _, hrun2⟩ | ⟨_, _, hrun2⟩ | ⟨_, hrun2⟩ |
    ⟨_, hrun2⟩ | hstable
  · rw [(implyBool_conflict_inv hrun2).1]
    exact boolOr_ng_k_false (i := i) (j := j) (k := k) (ha.2 _ hprob)
  · rw [(implyBool_conflict_inv hrun2).1]
    exact boolOr_ng_j_true (i := i) (j := j) (k := k) (ha.2 _ hprob)
  · rw [(implyBool_conflict_inv hrun2).1]
    exact boolOr_ng_i_true (i := i) (j := j) (k := k) (ha.2 _ hprob)
  · rw [(implyBool_conflict_inv hrun2).1]
    exact boolOr_ng_kt_i (i := i) (j := j) (k := k) (ha.2 _ hprob)
  · rw [(implyBool_conflict_inv hrun2).1]
    exact boolOr_ng_kt_j (i := i) (j := j) (k := k) (ha.2 _ hprob)
  · exact absurd hstable (by intro hc; cases hc)

/-- The reason-validity lemma for the `boolOrSlot` family. -/
theorem propBoolOr_reason_safe
    {problem : Problem DomConstraint Unit}
    {constraintHolds : DomConstraint → Assignment → Prop}
    {st : State} {i j k : Nat} {l : Literal} {r : Reason}
    (himp : ∀ c a, c ∈ problem.constraints →
      constraintHolds c a → c.SatisfiedBy a)
    (hprob : DomConstraint.boolOrSlot i j k ∈ problem.constraints)
    (hrun : propBoolOr st i j k = .implied l r) :
    Reason.Valid problem constraintHolds r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  rcases propBoolOr_emit hrun with
    ⟨_, _, hrun2⟩ | ⟨_, _, hrun2⟩ | ⟨_, _, hrun2⟩ | ⟨_, hrun2⟩ |
    ⟨_, hrun2⟩ | hstable
  · exact implyBool_reason_safe himp hprob
      (fun a hsat => boolOr_ng_k_false (i := i) (j := j) (k := k) hsat)
      List.mem_cons_self
      (posBool3_norm k false i true j true) hrun2
  · exact implyBool_reason_safe himp hprob
      (fun a hsat => boolOr_ng_j_true (i := i) (j := j) (k := k) hsat)
      List.mem_cons_self
      (posBool3_norm j true i true k false) hrun2
  · exact implyBool_reason_safe himp hprob
      (fun a hsat => boolOr_ng_i_true (i := i) (j := j) (k := k) hsat)
      List.mem_cons_self
      (posBool3_norm i true j true k false) hrun2
  · exact implyBool_reason_safe himp hprob
      (fun a hsat => boolOr_ng_kt_i (i := i) (j := j) (k := k) hsat)
      List.mem_cons_self
      (posBool2_norm k true i false) hrun2
  · exact implyBool_reason_safe himp hprob
      (fun a hsat => boolOr_ng_kt_j (i := i) (j := j) (k := k) hsat)
      List.mem_cons_self
      (posBool2_norm k true j false) hrun2
  · exact absurd hstable (by intro hc; cases hc)

/-- The canonical `DomConstraint.SatisfiedBy` instantiation. -/
theorem propBoolOr_reason_safe_sat
    {problem : Problem DomConstraint Unit}
    {st : State} {i j k : Nat} {l : Literal} {r : Reason}
    (hprob : DomConstraint.boolOrSlot i j k ∈ problem.constraints)
    (hrun : propBoolOr st i j k = .implied l r) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l ∧
      (∀ q ∈ r.clause, q = q.norm) :=
  propBoolOr_reason_safe (fun _ _ _ h => h) hprob hrun

/-! ## The B5 registration

The standalone registration of the three Boolean families (in the
    integrated registration `propagatorOfProved` these are arms; this
    standalone packaging keeps the front-door theorems of this module
    usable before composition). -/

/-- The B5 registration: the proved propagators of the three Boolean
    connective families. -/
def propagatorOfProvedB5 : DomConstraint → Option Propagator
  | .boolNotSlot i j =>
      some { watches := [], run := fun st => propBoolNot st i j }
  | .boolAndSlot i j k =>
      some { watches := [], run := fun st => propBoolAnd st i j k }
  | .boolOrSlot i j k =>
      some { watches := [], run := fun st => propBoolOr st i j k }
  | _ => none

/-- Membership inversion for the B5 registration (the
    `propagatorsOfProved_mem` shape). -/
theorem propagatorOfProvedB5_mem {dcs : List DomConstraint}
    {p : Propagator}
    (hp : p ∈ dcs.filterMap propagatorOfProvedB5) :
    ∃ dc ∈ dcs, propagatorOfProvedB5 dc = some p := by
  induction dcs with
  | nil => cases hp
  | cons dc rest ih =>
      cases hpdc : propagatorOfProvedB5 dc with
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

/-- The run inversion for the B5 registration (the
    `propagatorOfProved_run` shape): an emission of a B5-registered
    propagator reduces to one of the three family propagators at the
    same parameters. -/
theorem propagatorOfProvedB5_run {dc : DomConstraint} {p : Propagator}
    {st : State} {res : PropagationResult}
    (hprop : propagatorOfProvedB5 dc = some p)
    (hrun : p.run st = res) :
    (∃ i j, dc = .boolNotSlot i j ∧ propBoolNot st i j = res) ∨
    (∃ i j k, dc = .boolAndSlot i j k ∧ propBoolAnd st i j k = res) ∨
    (∃ i j k, dc = .boolOrSlot i j k ∧ propBoolOr st i j k = res) := by
  match hdc : dc with
  | .boolNotSlot i j =>
      simp only [propagatorOfProvedB5] at hprop
      refine Or.inl ⟨i, j, rfl, ?_⟩
      rw [(Option.some.inj hprop).symm] at hrun
      exact hrun
  | .boolAndSlot i j k =>
      simp only [propagatorOfProvedB5] at hprop
      refine Or.inr (Or.inl ⟨i, j, k, rfl, ?_⟩)
      rw [(Option.some.inj hprop).symm] at hrun
      exact hrun
  | .boolOrSlot i j k =>
      simp only [propagatorOfProvedB5] at hprop
      refine Or.inr (Or.inr ⟨i, j, k, rfl, ?_⟩)
      rw [(Option.some.inj hprop).symm] at hrun
      exact hrun
  | .eqSlot i j
  | .neSlot i j | .leSlot i j | .constEq i v
  | .plusSlot i j k | .allDiff is
  | .timesSlot i j k | .minSlot i j k | .maxSlot i j k | .absSlot i k2
  | .linEq coeffs is b | .linLe coeffs is b
  | .ltSlot i j | .ltConstHi i c | .ltConstLo i c
  | .leConstHi i c | .leConstLo i c =>
      exfalso
      simp only [propagatorOfProvedB5] at hprop
      exact absurd hprop (by intro hc; cases hc)

/-! ### The per-family reason bridges -/

/-- The membership bridge for the `boolNotSlot` family. -/
theorem propagatorOfProvedB5_boolNotSlot_reason
    {problem : Problem DomConstraint Unit}
    {constraintHolds : DomConstraint → Assignment → Prop}
    {st : State} {i j : Nat} {p : Propagator} {l : Literal} {r : Reason}
    (himp : ∀ c a, c ∈ problem.constraints →
      constraintHolds c a → c.SatisfiedBy a)
    (hprop : propagatorOfProvedB5 (DomConstraint.boolNotSlot i j)
      = some p)
    (hprob : DomConstraint.boolNotSlot i j ∈ problem.constraints)
    (hrun : p.run st = .implied l r) :
    Reason.Valid problem constraintHolds r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  have hrun2 : propBoolNot st i j = .implied l r := by
    rw [(Option.some.inj hprop).symm] at hrun
    exact hrun
  exact propBoolNot_reason_safe himp hprob hrun2

/-- The membership bridge for the `boolAndSlot` family. -/
theorem propagatorOfProvedB5_boolAndSlot_reason
    {problem : Problem DomConstraint Unit}
    {constraintHolds : DomConstraint → Assignment → Prop}
    {st : State} {i j k : Nat} {p : Propagator} {l : Literal} {r : Reason}
    (himp : ∀ c a, c ∈ problem.constraints →
      constraintHolds c a → c.SatisfiedBy a)
    (hprop : propagatorOfProvedB5 (DomConstraint.boolAndSlot i j k)
      = some p)
    (hprob : DomConstraint.boolAndSlot i j k ∈ problem.constraints)
    (hrun : p.run st = .implied l r) :
    Reason.Valid problem constraintHolds r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  have hrun2 : propBoolAnd st i j k = .implied l r := by
    rw [(Option.some.inj hprop).symm] at hrun
    exact hrun
  exact propBoolAnd_reason_safe himp hprob hrun2

/-- The membership bridge for the `boolOrSlot` family. -/
theorem propagatorOfProvedB5_boolOrSlot_reason
    {problem : Problem DomConstraint Unit}
    {constraintHolds : DomConstraint → Assignment → Prop}
    {st : State} {i j k : Nat} {p : Propagator} {l : Literal} {r : Reason}
    (himp : ∀ c a, c ∈ problem.constraints →
      constraintHolds c a → c.SatisfiedBy a)
    (hprop : propagatorOfProvedB5 (DomConstraint.boolOrSlot i j k)
      = some p)
    (hprob : DomConstraint.boolOrSlot i j k ∈ problem.constraints)
    (hrun : p.run st = .implied l r) :
    Reason.Valid problem constraintHolds r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  have hrun2 : propBoolOr st i j k = .implied l r := by
    rw [(Option.some.inj hprop).symm] at hrun
    exact hrun
  exact propBoolOr_reason_safe himp hprob hrun2

/-! ## The front doors for the three Boolean families

Each mirrors the corresponding B3/B4 assembly
    (`propagatorsOfProvedB3_safeUniv`, `_entitled`, and the
    ReasonSafeUniv obligation of Run.lean), restricted to the B5
    families — with only the premises these families actually need
    (safety holds at EVERY state; the entitlement and reason
    obligations are state-free). -/

/-- **PropSafeUniv for the B5 registration**: every implied literal is
    true at every represented internal solution and every conflict
    clause excludes every represented internal solution — at EVERY
    state. -/
theorem propagatorsOfProvedB5_safeUniv
    {problem : Problem DomConstraint Unit}
    {props : List Propagator}
    (hprops : ∀ p ∈ props, ∃ dc ∈ problem.constraints,
      propagatorOfProvedB5 dc = some p) :
    PropSafeUniv problem DomConstraint.SatisfiedBy props := by
  intro st
  refine ⟨?_, ?_⟩
  · intro p hp l r hrun a ⟨hsol, hrep⟩
    obtain ⟨dc, hdc, hprop⟩ := hprops p hp
    rcases propagatorOfProvedB5_run hprop hrun with
      ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, k, hdc2, hrun2⟩ |
      ⟨i, j, k, hdc2, hrun2⟩
    · rw [hdc2] at hdc
      exact (propBoolNot_safe st i j).1 l r hrun2 a hrep.1
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      exact (propBoolAnd_safe st i j k).1 l r hrun2 a hrep.1
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      exact (propBoolOr_safe st i j k).1 l r hrun2 a hrep.1
        (hsol.2 _ hdc)
  · intro p hp cc hrun a ⟨hsol, hrep⟩
    obtain ⟨dc, hdc, hprop⟩ := hprops p hp
    rcases propagatorOfProvedB5_run hprop hrun with
      ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, k, hdc2, hrun2⟩ |
      ⟨i, j, k, hdc2, hrun2⟩
    · rw [hdc2] at hdc
      intro _
      exact (propBoolNot_safe st i j).2.1 cc hrun2 a hrep.1
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      intro _
      exact (propBoolAnd_safe st i j k).2.1 cc hrun2 a hrep.1
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      intro _
      exact (propBoolOr_safe st i j k).2.1 cc hrun2 a hrep.1
        (hsol.2 _ hdc)

/-- **The relativized entitlement for the B5 registration** (the exact
    `propagatorsOfProved_entitled` signature): every conflict clause
    carries a true literal at every internal solution that fits the
    state's domains.

    The `SolvedBy`/`DomainCoherent` premises are VACUOUS for these
    families (the truth literal is pinned by the constraint alone);
    they are kept, unused, purely for drop-in signature
    compatibility with the six-family assembly. -/
theorem propagatorsOfProvedB5_entitled
    {problem : Problem DomConstraint Unit}
    {props : List Propagator}
    (hprops : ∀ p ∈ props, ∃ dc ∈ problem.constraints,
      propagatorOfProvedB5 dc = some p) :
    ∀ (st : State), SolvedBy problem DomConstraint.SatisfiedBy st →
    DomainCoherent problem st →
    ∀ p ∈ props, ∀ (cc : Clause), p.run st = .conflict cc →
    ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
    ∃ l ∈ cc, l.eval a = some true := by
  intro st _hsol _hcoh p hp cc hrun a ha
  obtain ⟨dc, hdc, hprop⟩ := hprops p hp
  rcases propagatorOfProvedB5_run hprop hrun with
    ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, k, hdc2, hrun2⟩ |
    ⟨i, j, k, hdc2, hrun2⟩
  · rw [hdc2] at hdc
    exact propBoolNot_entitled hdc hrun2 a ha
  · rw [hdc2] at hdc
    exact propBoolAnd_entitled hdc hrun2 a ha
  · rw [hdc2] at hdc
    exact propBoolOr_entitled hdc hrun2 a ha

/-- **ReasonSafeUniv for the B5 registration**: every propagator's
    implied literal carries a VALID, normalized explanation — the
    obligation `runPropagators_runInv` consumes via its `hreason`
    premise. The `DomainCoherent` premise of `ReasonSafeUniv` is
    vacuous here (the nogoods are unconditionally entailed); the
    `himp` semantics bridge disappears at the concrete
    `DomConstraint.SatisfiedBy` semantics. -/
theorem propagatorsOfProvedB5_reason
    {problem : Problem DomConstraint Unit}
    {constraintHolds : DomConstraint → Assignment → Prop}
    (himp : ∀ c a, c ∈ problem.constraints →
      constraintHolds c a → c.SatisfiedBy a)
    {props : List Propagator}
    (hprops : ∀ p ∈ props, ∃ dc ∈ problem.constraints,
      propagatorOfProvedB5 dc = some p) :
    ReasonSafeUniv problem constraintHolds props := by
  intro st _hcoh p hp l r hrun
  obtain ⟨dc, hdc, hprop⟩ := hprops p hp
  rcases propagatorOfProvedB5_run hprop hrun with
    ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, k, hdc2, hrun2⟩ |
    ⟨i, j, k, hdc2, hrun2⟩
  · rw [hdc2] at hdc
    exact propBoolNot_reason_safe himp hdc hrun2
  · rw [hdc2] at hdc
    exact propBoolAnd_reason_safe himp hdc hrun2
  · rw [hdc2] at hdc
    exact propBoolOr_reason_safe himp hdc hrun2

/-! ## Axiom checks -/

#print axioms LeanFzn.Solver.Propagation.getD_nil_of_length_le
#print axioms LeanFzn.Solver.Propagation.domBoolPin_eq
#print axioms LeanFzn.Solver.Propagation.fits_of_domBoolPin
#print axioms LeanFzn.Solver.Propagation.implyBool_implied_inv
#print axioms LeanFzn.Solver.Propagation.implyBool_conflict_inv
#print axioms LeanFzn.Solver.Propagation.implyBool_safe
#print axioms LeanFzn.Solver.Propagation.implyBool_reason_safe
#print axioms LeanFzn.Solver.Propagation.posBool2_norm
#print axioms LeanFzn.Solver.Propagation.posBool3_norm
#print axioms LeanFzn.Solver.Propagation.bool_read_eq
#print axioms LeanFzn.Solver.Propagation.boolNotSlot_views
#print axioms LeanFzn.Solver.Propagation.boolNot_head_i_of_j
#print axioms LeanFzn.Solver.Propagation.boolNot_head_j_of_i
#print axioms LeanFzn.Solver.Propagation.boolNot_ng_true
#print axioms LeanFzn.Solver.Propagation.boolNot_ng_false
#print axioms LeanFzn.Solver.Propagation.propBoolNot_emit
#print axioms LeanFzn.Solver.Propagation.propBoolNot_emit_safe
#print axioms LeanFzn.Solver.Propagation.propBoolNot_safe
#print axioms LeanFzn.Solver.Propagation.propBoolNot_entitled
#print axioms LeanFzn.Solver.Propagation.propBoolNot_reason_safe
#print axioms LeanFzn.Solver.Propagation.propBoolNot_reason_safe_sat
#print axioms LeanFzn.Solver.Propagation.boolAndSlot_views
#print axioms LeanFzn.Solver.Propagation.boolAnd_head_k_of_ij
#print axioms LeanFzn.Solver.Propagation.boolAnd_head_j_of_i_true
#print axioms LeanFzn.Solver.Propagation.boolAnd_head_i_of_j_true
#print axioms LeanFzn.Solver.Propagation.boolAnd_head_k_of_i_false
#print axioms LeanFzn.Solver.Propagation.boolAnd_head_k_of_j_false
#print axioms LeanFzn.Solver.Propagation.boolAnd_ff_t_lits
#print axioms LeanFzn.Solver.Propagation.boolAnd_kf_it_lits
#print axioms LeanFzn.Solver.Propagation.boolAnd_kf_jt_lits
#print axioms LeanFzn.Solver.Propagation.boolAnd_ng_k_true
#print axioms LeanFzn.Solver.Propagation.boolAnd_ng_j_false
#print axioms LeanFzn.Solver.Propagation.boolAnd_ng_i_false
#print axioms LeanFzn.Solver.Propagation.boolAnd_ng_kf_i
#print axioms LeanFzn.Solver.Propagation.boolAnd_ng_kf_j
#print axioms LeanFzn.Solver.Propagation.propBoolAnd_emit
#print axioms LeanFzn.Solver.Propagation.propBoolAnd_emit_safe
#print axioms LeanFzn.Solver.Propagation.propBoolAnd_safe
#print axioms LeanFzn.Solver.Propagation.propBoolAnd_entitled
#print axioms LeanFzn.Solver.Propagation.propBoolAnd_reason_safe
#print axioms LeanFzn.Solver.Propagation.propBoolAnd_reason_safe_sat
#print axioms LeanFzn.Solver.Propagation.boolOrSlot_views
#print axioms LeanFzn.Solver.Propagation.boolOr_head_k_of_ij
#print axioms LeanFzn.Solver.Propagation.boolOr_head_j_of_i_false
#print axioms LeanFzn.Solver.Propagation.boolOr_head_i_of_j_false
#print axioms LeanFzn.Solver.Propagation.boolOr_head_k_of_i_true
#print axioms LeanFzn.Solver.Propagation.boolOr_head_k_of_j_true
#print axioms LeanFzn.Solver.Propagation.boolOr_tt_f_lits
#print axioms LeanFzn.Solver.Propagation.boolOr_kt_if_lits
#print axioms LeanFzn.Solver.Propagation.boolOr_kt_jf_lits
#print axioms LeanFzn.Solver.Propagation.boolOr_ng_k_false
#print axioms LeanFzn.Solver.Propagation.boolOr_ng_j_true
#print axioms LeanFzn.Solver.Propagation.boolOr_ng_i_true
#print axioms LeanFzn.Solver.Propagation.boolOr_ng_kt_i
#print axioms LeanFzn.Solver.Propagation.boolOr_ng_kt_j
#print axioms LeanFzn.Solver.Propagation.propBoolOr_emit
#print axioms LeanFzn.Solver.Propagation.propBoolOr_emit_safe
#print axioms LeanFzn.Solver.Propagation.propBoolOr_safe
#print axioms LeanFzn.Solver.Propagation.propBoolOr_entitled
#print axioms LeanFzn.Solver.Propagation.propBoolOr_reason_safe
#print axioms LeanFzn.Solver.Propagation.propBoolOr_reason_safe_sat
#print axioms LeanFzn.Solver.Propagation.propagatorOfProvedB5_mem
#print axioms LeanFzn.Solver.Propagation.propagatorOfProvedB5_run
#print axioms LeanFzn.Solver.Propagation.propagatorOfProvedB5_boolNotSlot_reason
#print axioms LeanFzn.Solver.Propagation.propagatorOfProvedB5_boolAndSlot_reason
#print axioms LeanFzn.Solver.Propagation.propagatorOfProvedB5_boolOrSlot_reason
#print axioms LeanFzn.Solver.Propagation.propagatorsOfProvedB5_safeUniv
#print axioms LeanFzn.Solver.Propagation.propagatorsOfProvedB5_entitled
#print axioms LeanFzn.Solver.Propagation.propagatorsOfProvedB5_reason

/-! ## Smoke tests

Concrete small states exercising every emission shape (kernel
    reduction by `rfl`; no `native_decide`). -/

/-- The one-slot-per-column test state: empty trail and databases. -/
private def boolTestState (doms : List (List Value)) : State where
  domains := doms
  trail := []
  decisionLevel := 0
  clauses := []
  learned := []
  queue := []
  conflict := none

/-- Smoke: `bool_not` implies `i = false` when `j` is pinned true and
    `i` is still undecided. -/
theorem propBoolNot_smoke :
    propBoolNot (boolTestState [[.bool true, .bool false], [.bool true]])
        0 1 =
      .implied (posBool 0 false)
        { clause := [posBool 0 false, posBool 1 false] } := rfl

/-- Smoke: `bool_not` conflicts when both slots are pinned true. -/
theorem propBoolNot_smoke_conflict :
    propBoolNot (boolTestState [[.bool true], [.bool true]]) 0 1 =
      .conflict [posBool 0 false, posBool 1 false] := rfl

/-- Smoke: `bool_and` implies `k = true` when both inputs are pinned
    true. -/
theorem propBoolAnd_smoke :
    propBoolAnd (boolTestState
        [[.bool true], [.bool true], [.bool true, .bool false]]) 0 1 2 =
      .implied (posBool 2 true)
        { clause := [posBool 2 true, posBool 0 false, posBool 1 false] } :=
  rfl

/-- Smoke: `bool_and` implies `k = false` from one false input. -/
theorem propBoolAnd_smoke_false :
    propBoolAnd (boolTestState
        [[.bool false], [.bool true, .bool false],
         [.bool true, .bool false]]) 0 1 2 =
      .implied (posBool 2 false)
        { clause := [posBool 2 false, posBool 0 true] } := rfl

/-- Smoke: `bool_and` conflicts on two true inputs with a false
    output. -/
theorem propBoolAnd_smoke_conflict :
    propBoolAnd (boolTestState
        [[.bool true], [.bool true], [.bool false]]) 0 1 2 =
      .conflict [posBool 2 true, posBool 0 false, posBool 1 false] := rfl

/-- Smoke: `bool_or` implies `k = false` from two false inputs. -/
theorem propBoolOr_smoke :
    propBoolOr (boolTestState
        [[.bool false], [.bool false], [.bool true, .bool false]]) 0 1 2 =
      .implied (posBool 2 false)
        { clause := [posBool 2 false, posBool 0 true, posBool 1 true] } :=
  rfl

/-- Smoke: `bool_or` implies `k = true` from one true input. -/
theorem propBoolOr_smoke_true :
    propBoolOr (boolTestState
        [[.bool true], [.bool true, .bool false],
         [.bool true, .bool false]]) 0 1 2 =
      .implied (posBool 2 true)
        { clause := [posBool 2 true, posBool 0 false] } := rfl

/-- Smoke: all three propagators stay stable when nothing is
    pinned. -/
theorem propBool_smoke_stable :
    propBoolNot
        (boolTestState [[.bool true, .bool false], [.bool true, .bool false]])
        0 1 = .stable ∧
    propBoolAnd
        (boolTestState [[.bool true, .bool false], [.bool true, .bool false],
          [.bool true, .bool false]]) 0 1 2 = .stable ∧
    propBoolOr
        (boolTestState [[.bool true, .bool false], [.bool true, .bool false],
          [.bool true, .bool false]]) 0 1 2 = .stable :=
  ⟨rfl, rfl, rfl⟩

end LeanFzn.Solver.Propagation

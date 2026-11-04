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

/-- The enumeration of a slot's domain (out of range: the empty default). -/
def slotEnum (doms : List Domain) (s : Nat) : List Value :=
  Dom.enum (doms.getD s Dom.empty)

/-- Same-slot domain equality gives the same enumeration. -/
theorem slotEnum_congr {doms1 doms2 : List Domain} {s : Nat}
    (h : doms1.getD s Dom.empty = doms2.getD s Dom.empty) :
    slotEnum doms1 s = slotEnum doms2 s := by
  rw [slotEnum, slotEnum, h]

/-- `true` when slot `s`'s domain is exactly the singleton `[.bool b]`
    (one candidate value, and it is the Boolean `b`). -/
def domBoolPin (doms : List Domain) (s : Nat) (b : Bool) : Bool :=
  (slotEnum doms s).length == 1 && valueMemB (.bool b) (slotEnum doms s)

/-- Out of range, `getD` returns the empty default. -/
theorem getD_nil_of_length_le {l : List Domain} {s : Nat}
    (h : ¬ s < l.length) : l.getD s Dom.empty = Dom.empty := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none_iff.mpr (by omega)]
  rfl

/-- An out-of-range slot enumerates empty. -/
theorem slotEnum_nil_of_length_le {domains : List Domain} {s : Nat}
    (h : ¬ s < domains.length) : slotEnum domains s = [] := by
  show Dom.enum (domains.getD s Dom.empty) = []
  rw [getD_nil_of_length_le h]
  rfl

/-- The pin test decides the exact singleton domain. -/
theorem domBoolPin_eq {doms : List Domain} {s : Nat} {b : Bool}
    (h : domBoolPin doms s b = true) :
    slotEnum doms s = [.bool b] := by
  obtain ⟨h1, h2⟩ := by simpa [domBoolPin, Bool.and_eq_true] using h
  have hlen : (slotEnum doms s).length = 1 := by simpa using h1
  have hmem : (.bool b : Value) ∈ slotEnum doms s := valueMemB_iff.mp h2
  match hl : slotEnum doms s with
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
      have hnil := slotEnum_nil_of_length_le hns
      rw [hnil] at hd
      simp at hd
  have hs2 : s < a.length := by rw [hfit.1]; exact hrange
  have hread : a[s]? = some a[s] := (List.getElem?_eq_some_iff).mpr ⟨hs2, rfl⟩
  have hmem : a[s] ∈ st.domains.getD s Dom.empty := hfit.2 s a[s] hread
  have hmemE : a[s] ∈ slotEnum st.domains s := by
    simpa [slotEnum] using (DomainLike.mem_iff _ _).mp hmem
  rw [hd] at hmemE
  have hval : a[s] = .bool b := List.mem_singleton.mp hmemE
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
  if valueMemB (.bool b) (slotEnum st.domains s) then
    if valuesEqB (slotEnum st.domains s) [.bool b] then .stable
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
    cc = ng ∧ ¬ (valueMemB (.bool b) (slotEnum st.domains s) = true) := by
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
    have hmem : (.bool b : Value) ∈ slotEnum st.domains s := by
      simpa [slotEnum] using
        (DomainLike.mem_iff _ _).mp (hfit.2 s (.bool b) (hhead a hfit hsat))
    exact hnm (valueMemB_iff.mpr hmem)
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
  domains := doms.map Dom.ofList
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

/-! ## PLAN G1-B: the `bool2int` channel (`bool2intSlot i k`) -/

/-- The first integer view of `d` that fails `keep`. Values without an
    integer view (sets, arrays) are skipped. -/
def firstBadView (d : List Value) (keep : Int → Bool) : Option Int :=
  d.findSome? fun v => (Value.intView v).bind fun w => if keep w then none else some w

/-- `valuesEqB` only accepts equal lists (the family-local copy: the
    canonical `valuesEqB_sound` lives downstream in the scheduling layer). -/
theorem b2iValuesEqB_sound {xs ys : List Value} (h : valuesEqB xs ys = true) :
    xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons y ys => simp [valuesEqB] at h
  | cons x xs ih =>
      cases ys with
      | nil => simp [valuesEqB] at h
      | cons y ys =>
          simp only [valuesEqB, Bool.and_eq_true] at h
          rw [value_eqB_iff.mp h.1, ih h.2]

/-- The pinned rounds' removal emission: `posNe k w` with the negated pin
    as the falsified cause. -/
def b2iResPinned (i k : Nat) (b : Bool) (w : Int) : PropagationResult :=
  .implied (posNe k w) { clause := [posNe k w, posBool i (!b)] }

/-- The unpinned rounds' unit removal emission. -/
def b2iResUnit (k : Nat) (w : Int) : PropagationResult :=
  .implied (posNe k w) { clause := [posNe k w] }

/-- The unpinned rounds' impossible-view response: a bound conflict when the
    extrema separate the whole domain from `{0,1}`, else the unit removal. -/
def b2iBadRes (k : Nat) (w : Int) (mx mn : Option Int) : PropagationResult :=
  match mx, mn with
  | some mx, some mn =>
      if mx < 0 then .conflict [negLe k (-1)]
      else if 1 < mn then .conflict [posLe k 1]
      else b2iResUnit k w
  | _, _ => b2iResUnit k w

/-- PLAN G1-B: the explained channeling propagator of `bool2int(b, i)` —
    `bool2intSlot i k` in the `DomConstraint` naming (`i` the Boolean
    source, `k` the 0/1 integer target). Guarded rounds, in order:

    * aliasing (`i = k`), empty or out-of-range slots ⇒ `.stable`;
    * `i` pinned `true` (resp. `false`) ⇒ remove every `k`-value whose
      integer view is not `1` (resp. `0`), the negated pin as cause;
    * `i` with no Boolean value ⇒ conflict `[i = true, i = false]`;
    * `k` pinned to the raw singleton `[.int 0]` (resp. `[.int 1]`) ⇒
      imply `i = false` (resp. `i = true`) through `implyBool`, the
      falsified cause being `k ≠ 0` (resp. `k ≠ 1`);
    * otherwise remove one `k`-value with a view outside `{0,1}`; when
      the whole domain lies below `0` (resp. above `1`) report the
      bound conflict `[k > -1]` (resp. `[k ≤ 1]`).

    Every emission's clause is over the existing vocabulary: `posBool`
    pins and `posNe`/`posLe`/`negLe` integer literals. -/
def propBool2intSlot (st : State) (i k : Nat) : PropagationResult :=
  if i = k then .stable
  else if (slotEnum st.domains i).isEmpty || (slotEnum st.domains k).isEmpty then .stable
  else if domBoolPin st.domains i true then
    match firstBadView (slotEnum st.domains k) (fun w => decide (w = 1)) with
    | some w => b2iResPinned i k true w
    | none => .stable
  else if domBoolPin st.domains i false then
    match firstBadView (slotEnum st.domains k) (fun w => decide (w = 0)) with
    | some w => b2iResPinned i k false w
    | none => .stable
  else if (valueMemB (.bool true) (slotEnum st.domains i)
      || valueMemB (.bool false) (slotEnum st.domains i)) = false then
    .conflict [posBool i true, posBool i false]
  else if valuesEqB (slotEnum st.domains k) [.int 0] then
    implyBool st i false [posBool i false, posNe k 0]
  else if valuesEqB (slotEnum st.domains k) [.int 1] then
    implyBool st i true [posBool i true, posNe k 1]
  else
    match firstBadView (slotEnum st.domains k) (fun w => decide (w = 0 ∨ w = 1)) with
    | some w => b2iBadRes k w (domMaxI (st.domains.getD k Dom.empty)) (domMinI (st.domains.getD k Dom.empty))
    | none => .stable

/-! ### `firstBadView` views -/

/-- A found bad view comes from a domain value, and fails `keep`. -/
theorem firstBadView_some {d : List Value} {keep : Int → Bool} {w : Int}
    (h : firstBadView d keep = some w) :
    ∃ v ∈ d, Value.intView v = some w ∧ keep w = false := by
  unfold firstBadView at h
  obtain ⟨v, hv, hfv⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨u, hvu, hfu⟩ := Option.bind_eq_some_iff.mp hfv
  by_cases hk : keep u = true
  · rw [hk] at hfu; cases hfu
  · have hk' : keep u = false := Bool.eq_false_iff.mpr hk
    rw [hk'] at hfu
    simp only [Bool.false_eq_true, if_false] at hfu
    injection hfu with h1
    exact ⟨v, hv, by rw [h1] at hvu; exact hvu, by subst h1; exact hk'⟩

/-- When no bad view is found, every integer view of the domain passes
    `keep`. -/
theorem firstBadView_none {d : List Value} {keep : Int → Bool}
    (h : firstBadView d keep = none) :
    ∀ v ∈ d, ∀ w, Value.intView v = some w → keep w = true := by
  intro v hv w hvw
  by_cases hk : keep w = true
  · exact hk
  · exfalso
    have hfn : ((fun x => (Value.intView x).bind
        fun u => if keep u then none else some u) v) = none :=
      List.findSome?_eq_none_iff.mp h v hv
    have hfn' : (Value.intView v).bind
        (fun u => if keep u then none else some u) = none := hfn
    rw [hvw] at hfn'
    simp only [Option.bind_some] at hfn'
    have hk' : keep w = false := Bool.eq_false_iff.mpr hk
    rw [hk'] at hfn'
    simp only [Bool.false_eq_true, if_false] at hfn'
    cases hfn'

/-- The `keep = (· = 1)` arm's found view is not `1`. -/
theorem firstBadView_one_some {d : List Value} {w : Int}
    (h : firstBadView d (fun w => decide (w = 1)) = some w) : w ≠ 1 := by
  obtain ⟨-, -, -, hkw⟩ := firstBadView_some h
  exact of_decide_eq_false hkw

/-- The `keep = (· = 0)` arm's found view is not `0`. -/
theorem firstBadView_zero_some {d : List Value} {w : Int}
    (h : firstBadView d (fun w => decide (w = 0)) = some w) : w ≠ 0 := by
  obtain ⟨-, -, -, hkw⟩ := firstBadView_some h
  exact of_decide_eq_false hkw

/-- The unpinned arm's found view lies outside `{0,1}`. -/
theorem firstBadView_digit_some {d : List Value} {w : Int}
    (h : firstBadView d (fun w => decide (w = 0 ∨ w = 1)) = some w) :
    w ≠ 0 ∧ w ≠ 1 := by
  obtain ⟨-, -, -, hkw⟩ := firstBadView_some h
  have h : ¬ (w = 0 ∨ w = 1) := of_decide_eq_false hkw
  exact ⟨fun h0 => h (Or.inl h0), fun h1 => h (Or.inr h1)⟩

/-! ### The complete case split -/

/-- The unpinned rounds' response: unit removal, or a `negLe` conflict when
    the domain maximum is below zero, or a `posLe` conflict when the domain
    minimum is above one. -/
theorem b2iBadRes_cases {k : Nat} {w : Int} {mx mn : Option Int} :
    b2iBadRes k w mx mn = b2iResUnit k w ∨
    (∃ mx' mn', mx = some mx' ∧ mn = some mn' ∧ mx' < 0 ∧
      b2iBadRes k w mx mn = .conflict [negLe k (-1)]) ∨
    (∃ mx' mn', mx = some mx' ∧ mn = some mn' ∧ 1 < mn' ∧
      b2iBadRes k w mx mn = .conflict [posLe k 1]) := by
  unfold b2iBadRes
  split
  · next mx' mn' =>
      by_cases h : mx' < 0
      · rw [if_pos h]; exact Or.inr (Or.inl ⟨mx', mn', rfl, rfl, h, rfl⟩)
      · rw [if_neg h]
        by_cases h2 : 1 < mn'
        · rw [if_pos h2]; exact Or.inr (Or.inr ⟨mx', mn', rfl, rfl, h2, rfl⟩)
        · rw [if_neg h2]; exact Or.inl rfl
  · exact Or.inl rfl

/-- Complete case split of `propBool2intSlot`: `.stable`, a `posNe` removal
    through a Boolean pin, the no-Boolean conflict, a pin through the raw
    `[.int 0]`/`[.int 1]` singleton, an unpinned unit removal, or one of the
    two bound conflicts. -/
theorem propBool2intSlot_cases (st : State) (i k : Nat) :
    propBool2intSlot st i k = .stable ∨
    (domBoolPin st.domains i true = true ∧
      ∃ w, firstBadView (slotEnum st.domains k) (fun w => decide (w = 1)) = some w ∧
        propBool2intSlot st i k = b2iResPinned i k true w) ∨
    (domBoolPin st.domains i false = true ∧
      ∃ w, firstBadView (slotEnum st.domains k) (fun w => decide (w = 0)) = some w ∧
        propBool2intSlot st i k = b2iResPinned i k false w) ∨
    ((valueMemB (.bool true) (slotEnum st.domains i)
        || valueMemB (.bool false) (slotEnum st.domains i)) = false ∧
      propBool2intSlot st i k = .conflict [posBool i true, posBool i false]) ∨
    (slotEnum st.domains k = [.int 0] ∧
      propBool2intSlot st i k = implyBool st i false [posBool i false, posNe k 0]) ∨
    (slotEnum st.domains k = [.int 1] ∧
      propBool2intSlot st i k = implyBool st i true [posBool i true, posNe k 1]) ∨
    (∃ w, firstBadView (slotEnum st.domains k) (fun w => decide (w = 0 ∨ w = 1)) = some w ∧
      propBool2intSlot st i k = b2iResUnit k w) ∨
    (∃ mx mn, domMaxI (st.domains.getD k Dom.empty) = some mx ∧
      domMinI (st.domains.getD k Dom.empty) = some mn ∧ mx < 0 ∧
      propBool2intSlot st i k = .conflict [negLe k (-1)]) ∨
    (∃ mx mn, domMaxI (st.domains.getD k Dom.empty) = some mx ∧
      domMinI (st.domains.getD k Dom.empty) = some mn ∧ 1 < mn ∧
      propBool2intSlot st i k = .conflict [posLe k 1]) := by
  unfold propBool2intSlot
  by_cases halias : i = k
  · rw [if_pos halias]; exact Or.inl rfl
  · rw [if_neg halias]
    by_cases hemp : ((slotEnum st.domains i).isEmpty || (slotEnum st.domains k).isEmpty) = true
    · rw [if_pos hemp]; exact Or.inl rfl
    · rw [if_neg hemp]
      by_cases hpt : domBoolPin st.domains i true = true
      · rw [if_pos hpt]
        split
        · next w hfb => exact Or.inr (Or.inl ⟨hpt, w, hfb, rfl⟩)
        · next => exact Or.inl rfl
      · rw [if_neg hpt]
        by_cases hpf : domBoolPin st.domains i false = true
        · rw [if_pos hpf]
          split
          · next w hfb => exact Or.inr (Or.inr (Or.inl ⟨hpf, w, hfb, rfl⟩))
          · next => exact Or.inl rfl
        · rw [if_neg hpf]
          by_cases hnb : (valueMemB (.bool true) (slotEnum st.domains i)
              || valueMemB (.bool false) (slotEnum st.domains i)) = false
          · rw [if_pos hnb]
            exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hnb, rfl⟩)))
          · rw [if_neg hnb]
            by_cases hz : valuesEqB (slotEnum st.domains k) [.int 0] = true
            · rw [if_pos hz]
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨b2iValuesEqB_sound hz, rfl⟩))))
            · rw [if_neg hz]
              by_cases ho : valuesEqB (slotEnum st.domains k) [.int 1] = true
              · rw [if_pos ho]
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                  ⟨b2iValuesEqB_sound ho, rfl⟩)))))
              · rw [if_neg ho]
                split
                · next w hfb =>
                    rcases b2iBadRes_cases (k := k) (w := w)
                      (mx := domMaxI (st.domains.getD k Dom.empty))
                      (mn := domMinI (st.domains.getD k Dom.empty)) with
                      hU | ⟨mx, mn, hmx, hmn, hlt, hres⟩ | ⟨mx, mn, hmx, hmn, hlt, hres⟩
                    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (Or.inl ⟨w, hfb, hU⟩))))))
                    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (Or.inl ⟨mx, mn, hmx, hmn, hlt, hres⟩)))))))
                    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        ⟨mx, mn, hmx, hmn, hlt, hres⟩)))))))
                · next => exact Or.inl rfl

/-! ### The channel's satisfaction views and emission heads -/

/-- A positive Boolean literal is true at a reading of its value. -/
theorem b2i_posBool_eval_true {a : Assignment} {s : Nat} {b : Bool}
    (h : a[s]? = some (.bool b)) : (posBool s b).eval a = some true :=
  (eval_posBool_iff a s b).mpr h

/-- The `bool2intSlot` semantics at the reads: a Boolean source read and
    the matching 0/1 integer target read. -/
theorem bool2int_views {a : Assignment} {i k : Nat}
    (h : (DomConstraint.bool2intSlot i k).SatisfiedBy a) :
    ∃ b : Bool, a[i]? = some (.bool b) ∧
      a[k]? = some (.int (if b then 1 else 0)) := h

/-- The target's integer view at a solution, given the source read. -/
theorem bool2int_slotInt {a : Assignment} {i k : Nat} {b : Bool}
    (h : (DomConstraint.bool2intSlot i k).SatisfiedBy a)
    (hi : a[i]? = some (.bool b)) :
    slotInt a k = some (if b then 1 else 0) := by
  obtain ⟨b0, hi0, hk0⟩ := bool2int_views h
  have hb : b0 = b := bool_read_eq hi0 hi
  rw [hb] at hk0
  exact slotInt_of_int_read hk0

/-- A `posNe` head is true at a solution through the source read. -/
theorem b2i_posNe_eval_true {a : Assignment} {i k : Nat} {b : Bool} {w : Int}
    (h : (DomConstraint.bool2intSlot i k).SatisfiedBy a)
    (hi : a[i]? = some (.bool b)) (hw : w ≠ (if b then 1 else 0)) :
    (posNe k w).eval a = some true := by
  rw [eval_posNe_iff]
  exact ⟨_, bool2int_slotInt h hi, Ne.symm hw⟩

/-- A fitting read of a raw singleton domain. -/
theorem b2i_read_of_dom_singleton {st : State} {a : Assignment} {s : Nat}
    {v : Value} (hfit : Core.Assignment.Fits st.domains a)
    (hd : slotEnum st.domains s = [v]) : a[s]? = some v := by
  by_cases hs : s < st.domains.length
  · have hs2 : s < a.length := by rw [hfit.1]; exact hs
    have hread : a[s]? = some a[s] := List.getElem?_eq_getElem hs2
    have hmem : a[s] ∈ st.domains.getD s Dom.empty := hfit.2 s a[s] hread
    have hmemE : a[s] ∈ slotEnum st.domains s := by
      simpa [slotEnum] using (DomainLike.mem_iff _ _).mp hmem
    rw [hd] at hmemE
    rw [List.mem_singleton.mp hmemE] at hread
    exact hread
  · exfalso
    have hnil := slotEnum_nil_of_length_le hs
    rw [hnil] at hd
    simp at hd

/-- At a fitting solution of a raw `[.int 0]` target the source reads
    `false`. -/
theorem b2i_pinFalse_head {st : State} {a : Assignment} {i k : Nat}
    (hfit : Core.Assignment.Fits st.domains a)
    (hd0 : slotEnum st.domains k = [.int 0])
    (h : (DomConstraint.bool2intSlot i k).SatisfiedBy a) :
    a[i]? = some (.bool false) := by
  obtain ⟨b, hi, hk⟩ := bool2int_views h
  have hk0 : a[k]? = some (.int 0) := b2i_read_of_dom_singleton hfit hd0
  have hb : (if b then (1 : Int) else 0) = 0 :=
    Value.int.inj (Option.some.inj (hk.symm.trans hk0))
  cases b with
  | false => exact hi
  | true => simp at hb

/-- At a fitting solution of a raw `[.int 1]` target the source reads
    `true`. -/
theorem b2i_pinTrue_head {st : State} {a : Assignment} {i k : Nat}
    (hfit : Core.Assignment.Fits st.domains a)
    (hd1 : slotEnum st.domains k = [.int 1])
    (h : (DomConstraint.bool2intSlot i k).SatisfiedBy a) :
    a[i]? = some (.bool true) := by
  obtain ⟨b, hi, hk⟩ := bool2int_views h
  have hk1 : a[k]? = some (.int 1) := b2i_read_of_dom_singleton hfit hd1
  have hb : (if b then (1 : Int) else 0) = 1 :=
    Value.int.inj (Option.some.inj (hk.symm.trans hk1))
  cases b with
  | true => exact hi
  | false => simp at hb

/-! ### Clause entailment at solutions (the reason side) -/

/-- The pinned rounds' clause has a true literal at every solution. -/
theorem b2iResPinned_entailed {a : Assignment} {i k : Nat} {b : Bool} {w : Int}
    (h : (DomConstraint.bool2intSlot i k).SatisfiedBy a)
    (hw : w ≠ (if b then 1 else 0)) :
    ∃ l ∈ [posNe k w, posBool i (!b)], l.eval a = some true := by
  obtain ⟨b0, hi0, hk0⟩ := bool2int_views h
  by_cases hb : b0 = b
  · refine ⟨posNe k w, List.mem_cons_self, ?_⟩
    rw [eval_posNe_iff]
    exact ⟨_, bool2int_slotInt h hi0, by rw [hb]; exact Ne.symm hw⟩
  · have hb' : b0 = !b := by cases b <;> cases b0 <;> simp_all
    refine ⟨posBool i (!b), List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
    rw [hb'] at hi0
    exact b2i_posBool_eval_true hi0

/-- The unpinned unit removal's clause has a true literal at every
    solution. -/
theorem b2iResUnit_entailed {a : Assignment} {i k : Nat} {w : Int}
    (h : (DomConstraint.bool2intSlot i k).SatisfiedBy a)
    (hw0 : w ≠ 0) (hw1 : w ≠ 1) :
    ∃ l ∈ [posNe k w], l.eval a = some true := by
  obtain ⟨b, hi, hk⟩ := bool2int_views h
  refine ⟨posNe k w, List.mem_singleton_self _, ?_⟩
  rw [eval_posNe_iff]
  refine ⟨_, slotInt_of_int_read hk, ?_⟩
  cases b with
  | true => exact Ne.symm hw1
  | false => exact Ne.symm hw0

/-- The no-Boolean clause is entitled at every solution. -/
theorem b2iNoBool_entitled {a : Assignment} {i k : Nat}
    (h : (DomConstraint.bool2intSlot i k).SatisfiedBy a) :
    ∃ l ∈ [posBool i true, posBool i false], l.eval a = some true := by
  obtain ⟨b, hi, -⟩ := bool2int_views h
  cases b with
  | true => exact ⟨posBool i true, List.mem_cons_self, b2i_posBool_eval_true hi⟩
  | false =>
      exact ⟨posBool i false, List.mem_cons_of_mem _ (List.mem_singleton_self _),
        b2i_posBool_eval_true hi⟩

/-- The no-Boolean conflict is excluded at fitting solutions. -/
theorem b2iNoBool_excluded {st : State} {a : Assignment} {i k : Nat}
    (hfit : Core.Assignment.Fits st.domains a)
    (hnb : (valueMemB (.bool true) (slotEnum st.domains i)
        || valueMemB (.bool false) (slotEnum st.domains i)) = false)
    (h : (DomConstraint.bool2intSlot i k).SatisfiedBy a) : False := by
  obtain ⟨b, hi, -⟩ := bool2int_views h
  rw [Bool.or_eq_false_iff] at hnb
  have hmem : (.bool b : Value) ∈ st.domains.getD i Dom.empty := hfit.2 i (.bool b) hi
  have hmemE : (.bool b : Value) ∈ slotEnum st.domains i := by
    simpa [slotEnum] using (DomainLike.mem_iff _ _).mp hmem
  cases b with
  | true => exact absurd (valueMemB_iff.mpr hmemE) (by rw [hnb.1]; decide)
  | false => exact absurd (valueMemB_iff.mpr hmemE) (by rw [hnb.2]; decide)

/-- The `negLe k (-1)` conflict is excluded at fitting solutions. -/
theorem b2i_neg_excluded {st : State} {a : Assignment} {i k : Nat} {mx : Int}
    (hfit : Core.Assignment.Fits st.domains a)
    (hmx : domMaxI (st.domains.getD k Dom.empty) = some mx) (hlt : mx < 0)
    (h : (DomConstraint.bool2intSlot i k).SatisfiedBy a) : False := by
  obtain ⟨b, -, hk⟩ := bool2int_views h
  have hb := fits_max_bound hfit hmx (slotInt_of_int_read hk)
  cases b with
  | true => omega
  | false => omega

/-- The `posLe k 1` conflict is excluded at fitting solutions. -/
theorem b2i_pos_excluded {st : State} {a : Assignment} {i k : Nat} {mn : Int}
    (hfit : Core.Assignment.Fits st.domains a)
    (hmn : domMinI (st.domains.getD k Dom.empty) = some mn) (hgt : 1 < mn)
    (h : (DomConstraint.bool2intSlot i k).SatisfiedBy a) : False := by
  obtain ⟨b, -, hk⟩ := bool2int_views h
  have hb := fits_min_bound hfit hmn (slotInt_of_int_read hk)
  cases b with
  | true => omega
  | false => omega

/-- The `negLe k (-1)` clause is entitled at every solution. -/
theorem b2i_negLe_entailed {a : Assignment} {i k : Nat}
    (h : (DomConstraint.bool2intSlot i k).SatisfiedBy a) :
    ∃ l ∈ [negLe k (-1)], l.eval a = some true := by
  obtain ⟨b, -, hk⟩ := bool2int_views h
  refine ⟨negLe k (-1), List.mem_singleton_self _, ?_⟩
  rw [eval_negLe_iff]
  refine ⟨_, slotInt_of_int_read hk, ?_⟩
  cases b <;> simp

/-- The `posLe k 1` clause is entitled at every solution. -/
theorem b2i_posLe_entailed {a : Assignment} {i k : Nat}
    (h : (DomConstraint.bool2intSlot i k).SatisfiedBy a) :
    ∃ l ∈ [posLe k 1], l.eval a = some true := by
  obtain ⟨b, -, hk⟩ := bool2int_views h
  refine ⟨posLe k 1, List.mem_singleton_self _, ?_⟩
  rw [eval_posLe_iff]
  refine ⟨_, slotInt_of_int_read hk, ?_⟩
  cases b <;> simp

/-- The `[posBool i false, posNe k 0]` clause has a true literal at every
    solution. -/
theorem b2i_pinFalse_entailed {a : Assignment} {i k : Nat}
    (h : (DomConstraint.bool2intSlot i k).SatisfiedBy a) :
    ∃ l ∈ [posBool i false, posNe k 0], l.eval a = some true := by
  obtain ⟨b, hi, hk⟩ := bool2int_views h
  cases b with
  | false => exact ⟨posBool i false, List.mem_cons_self, b2i_posBool_eval_true hi⟩
  | true =>
      refine ⟨posNe k 0, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
      rw [eval_posNe_iff]
      exact ⟨_, slotInt_of_int_read hk, by simp⟩

/-- The `[posBool i true, posNe k 1]` clause has a true literal at every
    solution. -/
theorem b2i_pinTrue_entailed {a : Assignment} {i k : Nat}
    (h : (DomConstraint.bool2intSlot i k).SatisfiedBy a) :
    ∃ l ∈ [posBool i true, posNe k 1], l.eval a = some true := by
  obtain ⟨b, hi, hk⟩ := bool2int_views h
  cases b with
  | true => exact ⟨posBool i true, List.mem_cons_self, b2i_posBool_eval_true hi⟩
  | false =>
      refine ⟨posNe k 1, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
      rw [eval_posNe_iff]
      exact ⟨_, slotInt_of_int_read hk, by simp⟩

/-! ## PLAN G1e: the array-Boolean conjunction (`arrayBoolAndSlot is k`)

The family semantics: slot `k`'s read is the conjunction of the listed
slots' `= true` reads (`a[k]? = some (.bool (is.all (fun i =>
slotIsBoolB a i true)))`), so the EMPTY list forces `k = true`. The
explained propagator narrows in four guarded rounds:

* every input pinned `true` ⇒ imply `k = true` (causes: the inputs' `false`
  readings; the empty list included as the unit pin);
* some input pinned `false` ⇒ imply `k = false` through that input;
* `k` pinned `true` ⇒ imply the first input that is not already pinned
  `true`;
* `k` pinned `false` with the singleton input list `[i]` and a Boolean-only
  input domain ⇒ imply `i = false` (the Boolean-only guard is required:
  the family semantics lets a non-Boolean input satisfy `all = false`).

Guards: aliasing (`k ∈ is`) is `.stable`. Only `k` is typed by the family
semantics; the input-pruning pivots are typed by the state domain shape
under `DomsShapeTyped` + `DomSub` (`propArrayBoolAnd_implied_decided`), and
the state-free reason of the all-`true` round consumes the problem-level
`BoolDomsAt` gate (every input's problem domain Boolean-only). -/

/-- The compiled `array_bool_and` shape: every input slot is in range of
    the problem's box and its problem domain holds only Booleans (the
    all-`true` round's state-free reason consumes exactly this fact). -/
def BoolDomsAt (problem : Problem DomConstraint Unit) (is : List Nat) : Prop :=
  ∀ i ∈ is, i < problem.domains.length ∧
    ∀ v ∈ problem.domains.getD i Dom.empty, ∃ b : Bool, v = .bool b

/-- `implyBool`'s implied emission carries the head literal, the nogood
    and the presence of the head Boolean in the target domain. -/
theorem implyBool_implied_inv_mem {st : State} {s : Nat} {b : Bool}
    {ng : Clause} {l : Literal} {r : Reason}
    (h : implyBool st s b ng = .implied l r) :
    valueMemB (.bool b) (slotEnum st.domains s) = true ∧
      l = posBool s b ∧ r = { clause := ng } := by
  obtain ⟨hl, hr⟩ := implyBool_implied_inv h
  subst hl
  subst hr
  simp only [implyBool] at h
  split at h
  · split at h
    · exact absurd h (by intro hc; cases hc)
    · exact ⟨by assumption, rfl, rfl⟩
  · exact absurd h (by intro hc; cases hc)

/-- The `slotIsBoolB` positive read conversion. -/
theorem aba_slotIsBoolB_true_iff {a : List Value} {i : Nat} {b : Bool} :
    slotIsBoolB a i b = true ↔ a[i]? = some (.bool b) := by
  unfold slotIsBoolB
  cases h : a[i]? with
  | none => simp
  | some v => cases v <;> cases b <;> simp [value_eqB_iff]

/-- The positive `slotIsBoolB` read of a Boolean-valued slot is the read's
    Boolean. -/
theorem aba_slotIsBoolB_true_eq {a : List Value} {i : Nat} {p : Bool}
    (hi : a[i]? = some (.bool p)) : slotIsBoolB a i true = p := by
  cases p <;> simp [slotIsBoolB, hi, Value.eqB]

/-- A positive Boolean literal is decided whenever the slot reads any
    Boolean. -/
theorem aba_posBool_decided {a : Assignment} {s : Nat} {b : Bool}
    (h : ∃ b', a[s]? = some (.bool b')) :
    ∃ t, (posBool s b).eval a = some t := by
  obtain ⟨b', hb⟩ := h
  exact ⟨b' == b, by simp [posBool, Literal.eval, Atom.eval, hb]⟩

/-- The family-local Boolean-only domain guard (the `domBoolOnlyB` copy:
    `Fam/Lin.lean` owns the shared one downstream of this module). -/
def aba_domBoolOnlyB (d : List Value) : Bool :=
  decide (0 < d.length) &&
    d.all (fun v => match v with | .bool _ => true | _ => false)

/-- The family-local guard's semantics. -/
theorem aba_domBoolOnlyB_eq {d : List Value} (h : aba_domBoolOnlyB d = true) :
    0 < d.length ∧ ∀ v ∈ d, ∃ b : Bool, v = .bool b := by
  rw [aba_domBoolOnlyB, Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1, by
    intro v hv
    have hv' := List.all_eq_true.mp h.2 v hv
    cases v with
    | bool b => exact ⟨b, rfl⟩
    | int k => exact absurd hv' (by simp)
    | setOfInt s => exact absurd hv' (by simp)
    | array a => exact absurd hv' (by simp)⟩

/-- PLAN G1e: the explained propagator of `array_bool_and`. Round order:
    alias guard; all inputs pinned `true`; some input pinned `false`;
    `k` pinned `true`; `k` pinned `false` with a Boolean-only singleton
    input. Every emission's clause is over the existing vocabulary:
    positive Boolean literals on the input slots and `k`. -/
def propArrayBoolAnd (st : State) (is : List Nat) (k : Nat) :
    PropagationResult :=
  if k ∈ is then .stable
  else if is.all (fun i => domBoolPin st.domains i true) then
    implyBool st k true ([posBool k true] ++ is.map (fun i => posBool i false))
  else
    match is.find? (fun i => domBoolPin st.domains i false) with
    | some i => implyBool st k false [posBool k false, posBool i true]
    | none =>
        if domBoolPin st.domains k true then
          match is.find? (fun i => !domBoolPin st.domains i true) with
          | some i => implyBool st i true [posBool i true, posBool k false]
          | none => .stable
        else if domBoolPin st.domains k false then
          match is with
          | [i] =>
              if aba_domBoolOnlyB (slotEnum st.domains i) then
                implyBool st i false [posBool i false, posBool k true]
              else .stable
          | _ => .stable
        else .stable

/-- Complete case split of `propArrayBoolAnd`: `.stable`, the all-pinned
    target pin, the pinned-`false` input arm, the pinned-`true` target's
    input arm, or the Boolean-only singleton arm. -/
theorem propArrayBoolAnd_cases (st : State) (is : List Nat) (k : Nat) :
    propArrayBoolAnd st is k = .stable ∨
    (is.all (fun i => domBoolPin st.domains i true) = true ∧
      propArrayBoolAnd st is k = implyBool st k true
        ([posBool k true] ++ is.map (fun i => posBool i false))) ∨
    (∃ i, is.find? (fun i => domBoolPin st.domains i false) = some i ∧
      propArrayBoolAnd st is k =
        implyBool st k false [posBool k false, posBool i true]) ∨
    (domBoolPin st.domains k true = true ∧
      ∃ i, is.find? (fun i => !domBoolPin st.domains i true) = some i ∧
        propArrayBoolAnd st is k =
          implyBool st i true [posBool i true, posBool k false]) ∨
    (domBoolPin st.domains k false = true ∧
      ∃ i, is = [i] ∧ aba_domBoolOnlyB (slotEnum st.domains i) = true ∧
        propArrayBoolAnd st is k =
          implyBool st i false [posBool i false, posBool k true]) := by
  generalize hres : propArrayBoolAnd st is k = res
  unfold propArrayBoolAnd at hres
  by_cases halias : k ∈ is
  · rw [if_pos halias] at hres; exact Or.inl hres.symm
  · rw [if_neg halias] at hres
    by_cases hall : is.all (fun i => domBoolPin st.domains i true) = true
    · rw [if_pos hall] at hres
      exact Or.inr (Or.inl ⟨hall, hres.symm⟩)
    · rw [if_neg hall] at hres
      cases hfind : is.find? (fun i => domBoolPin st.domains i false) with
      | some i =>
          simp only [hfind] at hres
          exact Or.inr (Or.inr (Or.inl ⟨i, rfl, hres.symm⟩))
      | none =>
          simp only [hfind] at hres
          by_cases hk : domBoolPin st.domains k true = true
          · rw [if_pos hk] at hres
            cases hfind2 : is.find? (fun i => !domBoolPin st.domains i true) with
            | some i =>
                simp only [hfind2] at hres
                exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hk, i, rfl, hres.symm⟩)))
            | none =>
                simp only [hfind2] at hres
                exact Or.inl hres.symm
          · rw [if_neg hk] at hres
            by_cases hkf : domBoolPin st.domains k false = true
            · rw [if_pos hkf] at hres
              cases his : is with
              | nil => simp only [his] at hres; exact Or.inl hres.symm
              | cons i rest =>
                  cases rest with
                  | nil =>
                      simp only [his] at hres
                      by_cases hb : aba_domBoolOnlyB (slotEnum st.domains i) = true
                      · rw [if_pos hb] at hres
                        exact Or.inr (Or.inr (Or.inr (Or.inr
                          ⟨hkf, i, rfl, hb, hres.symm⟩)))
                      · rw [if_neg hb] at hres; exact Or.inl hres.symm
                  | cons j rest' => simp only [his] at hres; exact Or.inl hres.symm
            · rw [if_neg hkf] at hres; exact Or.inl hres.symm

/-- The family semantics at the read: `k` reads the conjunction of the
    listed slots' `= true` reads. -/
theorem aba_satisfied {a : Assignment} {is : List Nat} {k : Nat}
    (h : (DomConstraint.arrayBoolAndSlot is k).SatisfiedBy a) :
    a[k]? = some (.bool (is.all (fun i => slotIsBoolB a i true))) := h

/-- A successful `find?` returns a member satisfying the predicate. -/
theorem aba_find?_some_eq {α : Type} (f : α → Bool) {is : List α} {i : α}
    (h : is.find? f = some i) : f i = true :=
  List.find?_some (p := f) h

/-! ### The fitting pivot truths -/

/-- The all-`true` round's pin is true at every fitting solution. -/
theorem aba_allTrue_pivot {st : State} {a : Assignment} {is : List Nat} {k : Nat}
    (hfit : Core.Assignment.Fits st.domains a)
    (hcons : (DomConstraint.arrayBoolAndSlot is k).SatisfiedBy a)
    (hall : is.all (fun i => domBoolPin st.domains i true) = true) :
    (posBool k true).eval a = some true := by
  have hallT : is.all (fun i => slotIsBoolB a i true) = true := by
    apply List.all_eq_true.mpr
    intro i hi
    rw [aba_slotIsBoolB_true_eq
      (fits_of_domBoolPin hfit (List.all_eq_true.mp hall i hi))]
  have h := aba_satisfied hcons
  rw [hallT] at h
  exact b2i_posBool_eval_true h

/-- The pinned-`false` input round's pin is true at every fitting solution. -/
theorem aba_pinFalse_pivot {st : State} {a : Assignment} {is : List Nat} {k i : Nat}
    (hfit : Core.Assignment.Fits st.domains a)
    (hcons : (DomConstraint.arrayBoolAndSlot is k).SatisfiedBy a)
    (hi : i ∈ is) (hpin : domBoolPin st.domains i false = true) :
    (posBool k false).eval a = some true := by
  have hread := fits_of_domBoolPin hfit hpin
  have hallF : is.all (fun i => slotIsBoolB a i true) = false := by
    cases h : is.all (fun i => slotIsBoolB a i true) with
    | true =>
        have := List.all_eq_true.mp h i hi
        rw [aba_slotIsBoolB_true_eq hread] at this
        cases this
    | false => rfl
  have h := aba_satisfied hcons
  rw [hallF] at h
  exact b2i_posBool_eval_true h

/-- The pinned-`true` target round's input pin is true at every fitting
    solution. -/
theorem aba_kTrue_pivot {st : State} {a : Assignment} {is : List Nat} {k i : Nat}
    (hfit : Core.Assignment.Fits st.domains a)
    (hcons : (DomConstraint.arrayBoolAndSlot is k).SatisfiedBy a)
    (hi : i ∈ is) (hk : domBoolPin st.domains k true = true) :
    (posBool i true).eval a = some true := by
  have hkread := fits_of_domBoolPin hfit hk
  have hallT : is.all (fun i => slotIsBoolB a i true) = true := by
    have h := aba_satisfied hcons
    rw [hkread] at h
    injection h with h
    exact (Value.bool.inj h).symm
  exact b2i_posBool_eval_true
    (aba_slotIsBoolB_true_iff.mp (List.all_eq_true.mp hallT i hi))

/-- The Boolean-only singleton round's input pin is true at every fitting
    solution. -/
theorem aba_single_pivot {st : State} {a : Assignment} {is : List Nat} {k i : Nat}
    (hfit : Core.Assignment.Fits st.domains a)
    (hcons : (DomConstraint.arrayBoolAndSlot is k).SatisfiedBy a)
    (his : is = [i]) (hk : domBoolPin st.domains k false = true)
    (hb : aba_domBoolOnlyB (slotEnum st.domains i) = true) :
    (posBool i false).eval a = some true := by
  obtain ⟨hlen0, hallb⟩ := aba_domBoolOnlyB_eq hb
  have hne : slotEnum st.domains i ≠ [] := by
    intro h0
    rw [h0] at hlen0
    simp at hlen0
  have hlt : i < st.domains.length := by
    by_cases hlt' : i < st.domains.length
    · exact hlt'
    · exact absurd (slotEnum_nil_of_length_le hlt') hne
  have hs2 : i < a.length := by rw [hfit.1]; exact hlt
  have hread : a[i]? = some a[i] := List.getElem?_eq_getElem hs2
  have hmem : a[i] ∈ st.domains.getD i Dom.empty := hfit.2 i a[i] hread
  have hmemE : a[i] ∈ slotEnum st.domains i := by
    simpa [slotEnum] using (DomainLike.mem_iff _ _).mp hmem
  obtain ⟨p, hp⟩ := hallb a[i] hmemE
  have hreadp : a[i]? = some (.bool p) := by rw [hread, hp]
  have hkread := fits_of_domBoolPin hfit hk
  have hallp : p = false := by
    have h := aba_satisfied hcons
    rw [his, hkread] at h
    injection h with h
    have h' : ([i].all (fun i => slotIsBoolB a i true)) = false :=
      (Value.bool.inj h).symm
    have hallf : slotIsBoolB a i true = false := by simpa using h'
    rw [aba_slotIsBoolB_true_eq hreadp] at hallf
    exact hallf
  rw [hallp] at hreadp
  exact b2i_posBool_eval_true hreadp

/-- A fitting read of a Boolean-only slot is a Boolean. -/
theorem aba_read_bool_of_guard {st : State} {a : Assignment} {i : Nat}
    (hfit : Core.Assignment.Fits st.domains a)
    (hb : aba_domBoolOnlyB (slotEnum st.domains i) = true) :
    ∃ p : Bool, a[i]? = some (.bool p) := by
  obtain ⟨hlen0, hallb⟩ := aba_domBoolOnlyB_eq hb
  have hne : slotEnum st.domains i ≠ [] := by
    intro h0
    rw [h0] at hlen0
    simp at hlen0
  have hlt : i < st.domains.length := by
    by_cases hlt' : i < st.domains.length
    · exact hlt'
    · exact absurd (slotEnum_nil_of_length_le hlt') hne
  have hs2 : i < a.length := by rw [hfit.1]; exact hlt
  have hread : a[i]? = some a[i] := List.getElem?_eq_getElem hs2
  have hmem : a[i] ∈ st.domains.getD i Dom.empty := hfit.2 i a[i] hread
  have hmemE : a[i] ∈ slotEnum st.domains i := by
    simpa [slotEnum] using (DomainLike.mem_iff _ _).mp hmem
  obtain ⟨p, hp⟩ := hallb a[i] hmemE
  exact ⟨p, by rw [hread, hp]⟩

/-- A faithful read of a pinned-`true` slot is the Boolean `true`. -/
theorem aba_read_bool_of_faithful_pin {st : State} {a : Assignment} {i : Nat}
    (hfaith : FrameFaithful st.domains a)
    (hpin : domBoolPin st.domains i true = true) :
    ∃ p : Bool, a[i]? = some (.bool p) := by
  have hd := domBoolPin_eq hpin
  have hne : slotEnum st.domains i ≠ [] := by
    intro h0
    rw [h0] at hd
    simp at hd
  have hlt : i < st.domains.length := by
    by_cases hlt' : i < st.domains.length
    · exact hlt'
    · exact absurd (slotEnum_nil_of_length_le hlt') hne
  obtain ⟨y, hread, -, hsort⟩ := hfaith i hlt
  have hs := hsort (.bool true) ((DomainLike.mem_iff _ _).mpr (by
    show (.bool true : Value) ∈ slotEnum st.domains i
    rw [hd]; simp))
  rcases hs with ⟨⟨k, hk⟩, -⟩ | ⟨-, ⟨p, hp⟩⟩
  · exact absurd hk (by simp)
  · exact ⟨p, by rw [hread, hp]⟩

/-- A faithful read of a Boolean-only slot is a Boolean. -/
theorem aba_read_bool_of_faithful_guard {st : State} {a : Assignment} {i : Nat}
    (hfaith : FrameFaithful st.domains a)
    (hb : aba_domBoolOnlyB (slotEnum st.domains i) = true) :
    ∃ p : Bool, a[i]? = some (.bool p) := by
  obtain ⟨hlen0, hallb⟩ := aba_domBoolOnlyB_eq hb
  have hne : slotEnum st.domains i ≠ [] := by
    intro h0
    rw [h0] at hlen0
    simp at hlen0
  have hlt : i < st.domains.length := by
    by_cases hlt' : i < st.domains.length
    · exact hlt'
    · exact absurd (slotEnum_nil_of_length_le hlt') hne
  obtain ⟨x, hxmem⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨p, hp⟩ := hallb x hxmem
  obtain ⟨y, hread, -, hsort⟩ := hfaith i hlt
  have hxmemD : x ∈ st.domains.getD i Dom.empty := by
    simpa [slotEnum] using (DomainLike.mem_iff _ _).mpr hxmem
  have hs := hsort x hxmemD
  rw [hp] at hs
  rcases hs with ⟨⟨k, hk⟩, -⟩ | ⟨-, ⟨q, hq⟩⟩
  · exact absurd hk (by simp)
  · exact ⟨q, by rw [hread, hq]⟩

/-! ### The fitting exclusions -/

/-- A slot cannot read both `true` and `false`. -/
theorem aba_posBool_contra {a : Assignment} {s : Nat}
    (h1 : (posBool s true).eval a = some true)
    (h2 : (posBool s false).eval a = some true) : False := by
  have hb1 : a[s]? = some (.bool true) := (eval_posBool_iff a s true).mp h1
  have hb2 : a[s]? = some (.bool false) := (eval_posBool_iff a s false).mp h2
  have h : true = false := Value.bool.inj (Option.some.inj (hb1.symm.trans hb2))
  cases h

/-- The all-`true` round's conflict excludes every fitting solution. -/
theorem aba_allTrue_excluded {st : State} {a : Assignment} {is : List Nat} {k : Nat}
    (hfit : Core.Assignment.Fits st.domains a)
    (hcons : (DomConstraint.arrayBoolAndSlot is k).SatisfiedBy a)
    (hall : is.all (fun i => domBoolPin st.domains i true) = true)
    (hnot : ¬ (valueMemB (.bool true) (slotEnum st.domains k) = true)) : False := by
  have htrue := aba_allTrue_pivot hfit hcons hall
  have hread : a[k]? = some (.bool true) := (eval_posBool_iff a k true).mp htrue
  have hs2 : k < a.length := by
    by_cases h : k < a.length
    · exact h
    · exfalso
      rw [List.getElem?_eq_none_iff.mpr (by omega)] at hread
      cases hread
  have hmem : a[k] ∈ st.domains.getD k Dom.empty :=
    hfit.2 k a[k] (List.getElem?_eq_getElem hs2)
  have hmemE : a[k] ∈ slotEnum st.domains k := by
    simpa [slotEnum] using (DomainLike.mem_iff _ _).mp hmem
  have hai : a[k] = .bool true :=
    Option.some.inj ((List.getElem?_eq_getElem hs2).symm.trans hread)
  exact hnot (valueMemB_iff.mpr (by rw [← hai]; exact hmemE))

/-- The pinned-`false` input round's conflict excludes every fitting
    solution. -/
theorem aba_pinFalse_excluded {st : State} {a : Assignment} {is : List Nat}
    {k i : Nat}
    (hfit : Core.Assignment.Fits st.domains a)
    (hcons : (DomConstraint.arrayBoolAndSlot is k).SatisfiedBy a)
    (hi : i ∈ is) (hpin : domBoolPin st.domains i false = true)
    (hnot : ¬ (valueMemB (.bool false) (slotEnum st.domains k) = true)) : False := by
  have hfalse := aba_pinFalse_pivot hfit hcons hi hpin
  have hread : a[k]? = some (.bool false) := (eval_posBool_iff a k false).mp hfalse
  have hs2 : k < a.length := by
    by_cases h : k < a.length
    · exact h
    · exfalso
      rw [List.getElem?_eq_none_iff.mpr (by omega)] at hread
      cases hread
  have hmem : a[k] ∈ st.domains.getD k Dom.empty :=
    hfit.2 k a[k] (List.getElem?_eq_getElem hs2)
  have hmemE : a[k] ∈ slotEnum st.domains k := by
    simpa [slotEnum] using (DomainLike.mem_iff _ _).mp hmem
  have hai : a[k] = .bool false :=
    Option.some.inj ((List.getElem?_eq_getElem hs2).symm.trans hread)
  exact hnot (valueMemB_iff.mpr (by rw [← hai]; exact hmemE))

/-- The pinned-`true` target round's conflict excludes every fitting
    solution. -/
theorem aba_kTrue_excluded {st : State} {a : Assignment} {is : List Nat} {k i : Nat}
    (hfit : Core.Assignment.Fits st.domains a)
    (hcons : (DomConstraint.arrayBoolAndSlot is k).SatisfiedBy a)
    (hi : i ∈ is) (hk : domBoolPin st.domains k true = true)
    (hnot : ¬ (valueMemB (.bool true) (slotEnum st.domains i) = true)) : False := by
  have htrue := aba_kTrue_pivot hfit hcons hi hk
  have hreadtrue : a[i]? = some (.bool true) := (eval_posBool_iff a i true).mp htrue
  have hs2 : i < a.length := by
    by_cases h : i < a.length
    · exact h
    · exfalso
      rw [List.getElem?_eq_none_iff.mpr (by omega)] at hreadtrue
      cases hreadtrue
  have hlt : i < st.domains.length := by rw [← hfit.1]; exact hs2
  have hmem : a[i] ∈ st.domains.getD i Dom.empty :=
    hfit.2 i a[i] (List.getElem?_eq_getElem hs2)
  have hmemE : a[i] ∈ slotEnum st.domains i := by
    simpa [slotEnum] using (DomainLike.mem_iff _ _).mp hmem
  have hai : a[i] = .bool true :=
    Option.some.inj ((List.getElem?_eq_getElem hs2).symm.trans hreadtrue)
  exact hnot (valueMemB_iff.mpr (by rw [← hai]; exact hmemE))

/-- The Boolean-only singleton round's conflict excludes every fitting
    solution. -/
theorem aba_single_excluded {st : State} {a : Assignment} {is : List Nat}
    {k i : Nat}
    (hfit : Core.Assignment.Fits st.domains a)
    (hcons : (DomConstraint.arrayBoolAndSlot is k).SatisfiedBy a)
    (his : is = [i]) (hk : domBoolPin st.domains k false = true)
    (hb : aba_domBoolOnlyB (slotEnum st.domains i) = true)
    (hnot : ¬ (valueMemB (.bool false) (slotEnum st.domains i) = true)) : False := by
  have hfalse := aba_single_pivot hfit hcons his hk hb
  have hreadfalse : a[i]? = some (.bool false) :=
    (eval_posBool_iff a i false).mp hfalse
  have hs2 : i < a.length := by
    by_cases h : i < a.length
    · exact h
    · exfalso
      rw [List.getElem?_eq_none_iff.mpr (by omega)] at hreadfalse
      cases hreadfalse
  have hlt : i < st.domains.length := by rw [← hfit.1]; exact hs2
  have hmem : a[i] ∈ st.domains.getD i Dom.empty :=
    hfit.2 i a[i] (List.getElem?_eq_getElem hs2)
  have hmemE : a[i] ∈ slotEnum st.domains i := by
    simpa [slotEnum] using (DomainLike.mem_iff _ _).mp hmem
  have hai : a[i] = .bool false :=
    Option.some.inj ((List.getElem?_eq_getElem hs2).symm.trans hreadfalse)
  exact hnot (valueMemB_iff.mpr (by rw [← hai]; exact hmemE))

/-! ### Clause entailment at solutions -/

/-- The all-`true` round's clause carries a true literal at every solution
    once every input reads a Boolean. -/
theorem aba_allTrue_entailed {a : Assignment} {is : List Nat} {k : Nat}
    (hreads : ∀ i ∈ is, ∃ p : Bool, a[i]? = some (.bool p))
    (hcons : (DomConstraint.arrayBoolAndSlot is k).SatisfiedBy a) :
    ∃ l ∈ [posBool k true] ++ is.map (fun i => posBool i false),
      l.eval a = some true := by
  cases h : is.all (fun i => slotIsBoolB a i true) with
  | true =>
      have hc := aba_satisfied hcons
      rw [h] at hc
      exact ⟨posBool k true, List.mem_append_left _ (List.mem_singleton_self _),
        b2i_posBool_eval_true hc⟩
  | false =>
      obtain ⟨j, hj, hnot⟩ := List.all_eq_false.mp h
      have hfalse : slotIsBoolB a j true = false := by
        cases hv : slotIsBoolB a j true with
        | false => rfl
        | true => exact absurd (by simp [hv]) hnot
      obtain ⟨p, hp⟩ := hreads j hj
      have hp' : p = false := by
        rw [aba_slotIsBoolB_true_eq hp] at hfalse
        exact hfalse
      refine ⟨posBool j false,
        List.mem_append_right _ (List.mem_map.mpr ⟨j, hj, rfl⟩), ?_⟩
      rw [hp'] at hp
      exact b2i_posBool_eval_true hp

/-- The two-literal pair clause `[k = false, i = true]` carries a true
    literal at every solution for every listed input. -/
theorem aba_pair_entailed {a : Assignment} {is : List Nat} {k i : Nat}
    (hcons : (DomConstraint.arrayBoolAndSlot is k).SatisfiedBy a)
    (hi : i ∈ is) :
    ∃ l ∈ [posBool k false, posBool i true], l.eval a = some true := by
  cases h : is.all (fun i => slotIsBoolB a i true) with
  | false =>
      have hc := aba_satisfied hcons
      rw [h] at hc
      exact ⟨posBool k false, List.mem_cons_self, b2i_posBool_eval_true hc⟩
  | true =>
      have htrue := List.all_eq_true.mp h i hi
      rw [aba_slotIsBoolB_true_iff] at htrue
      exact ⟨posBool i true, List.mem_cons_of_mem _ (List.mem_singleton_self _),
        b2i_posBool_eval_true htrue⟩

/-- The pinned-`true` target round's clause `[i = true, k = false]`
    carries a true literal at every solution for every listed input. -/
theorem aba_pairTrue_entailed {a : Assignment} {is : List Nat} {k i : Nat}
    (hcons : (DomConstraint.arrayBoolAndSlot is k).SatisfiedBy a)
    (hi : i ∈ is) :
    ∃ l ∈ [posBool i true, posBool k false], l.eval a = some true := by
  cases h : is.all (fun i => slotIsBoolB a i true) with
  | false =>
      have hc := aba_satisfied hcons
      rw [h] at hc
      exact ⟨posBool k false, List.mem_cons_of_mem _ (List.mem_singleton_self _),
        b2i_posBool_eval_true hc⟩
  | true =>
      have htrue := List.all_eq_true.mp h i hi
      rw [aba_slotIsBoolB_true_iff] at htrue
      exact ⟨posBool i true, List.mem_cons_self, b2i_posBool_eval_true htrue⟩

/-- The singleton round's clause `[i = false, k = true]` carries a true
    literal at every solution once the input reads a Boolean. -/
theorem aba_single_entailed {a : Assignment} {is : List Nat} {k i : Nat}
    (hreads : ∃ p : Bool, a[i]? = some (.bool p))
    (hcons : (DomConstraint.arrayBoolAndSlot is k).SatisfiedBy a)
    (his : is = [i]) :
    ∃ l ∈ [posBool i false, posBool k true], l.eval a = some true := by
  cases h : is.all (fun i => slotIsBoolB a i true) with
  | true =>
      have hc := aba_satisfied hcons
      rw [h] at hc
      exact ⟨posBool k true, List.mem_cons_of_mem _ (List.mem_singleton_self _),
        b2i_posBool_eval_true hc⟩
  | false =>
      obtain ⟨p, hp⟩ := hreads
      have hp' : p = false := by
        rw [his] at h
        have h1 : slotIsBoolB a i true = false := by
          simpa using h
        rw [aba_slotIsBoolB_true_eq hp] at h1
        exact h1
      refine ⟨posBool i false, List.mem_cons_self, ?_⟩
      rw [hp'] at hp
      exact b2i_posBool_eval_true hp

/-! ### Clause normalization -/

/-- The all-`true` round's emitted clause is normalized. -/
theorem aba_allTrue_norm (k : Nat) (is : List Nat) :
    ∀ q ∈ [posBool k true] ++ is.map (fun i => posBool i false),
      q = q.norm := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · rw [List.mem_singleton.mp hq]
    exact (posBool_norm k true).symm
  · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hq
    exact (posBool_norm i false).symm

/-- The pinned-`false` input round's emitted clause is normalized. -/
theorem aba_pair_norm (k i : Nat) :
    ∀ q ∈ [posBool k false, posBool i true], q = q.norm := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact (posBool_norm k false).symm
  · rw [List.mem_singleton.mp hq]
    exact (posBool_norm i true).symm

/-- The pinned-`true` target round's emitted clause is normalized. -/
theorem aba_pairTrue_norm (i k : Nat) :
    ∀ q ∈ [posBool i true, posBool k false], q = q.norm := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact (posBool_norm i true).symm
  · rw [List.mem_singleton.mp hq]
    exact (posBool_norm k false).symm

/-- The singleton round's emitted clause is normalized. -/
theorem aba_single_norm (i k : Nat) :
    ∀ q ∈ [posBool i false, posBool k true], q = q.norm := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact (posBool_norm i false).symm
  · rw [List.mem_singleton.mp hq]
    exact (posBool_norm k true).symm

end LeanFzn.Solver.Propagation

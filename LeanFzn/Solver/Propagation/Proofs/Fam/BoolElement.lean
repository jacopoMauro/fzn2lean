/-
File: LeanFzn/Solver/Propagation/Proofs/Fam/BoolElement.lean

Purpose:
  The LCG propagator and proof package for the variable-table Boolean
  element family `array_var_bool_element` (`arrayVarBoolElementSlot is i
  k`), the PLAN §3.3 item 2 dedicated propagator:

  * pinned index (`i`'s domain the raw int singleton `[.int idx]`): an
    out-of-range table position is the conflict `[i ≠ idx]`; otherwise
    the entry slot and the Boolean target are narrowed towards each
    other's domains, each removal escaping through the falsified pin
    `i ≠ idx`;
  * pinned target (`k`'s domain the raw Boolean singleton `[.bool v]`):
    every index whose table slot cannot read `v` (or is out of range)
    is removed through the falsified target `k ≠ v`-cause `posBool k
    (!v)`;
  * unpinned index and target: every out-of-range index is removed by
    the unit clause `[i ≠ idx]`; an index whose table slot is the
    opposite Boolean singleton is removed through the two Boolean
    causes; and a target value missing from every table slot is removed
    by the clause `[k = !b, j₁ = b, …, jₙ = b]`.

  Every emission is over the existing literal vocabulary (`posNe` for
  index removals; `posBool` for Boolean pins and removals), its clause
  is CONSTRAINT-VALID under the `arrayVarBoolElementSlot` constraint
  alone (the true-literals half of `Reason.Valid`), and each non-pivot
  cause is falsified by the state's own domain shape (`FixExpl` for the
  raw int index pin, `AbsentExpl` for the Boolean causes). Guards:
  aliasing `i = k`, `i` or `k` occurring in the table, a repeated table
  slot, a non-integer index domain, and empty/out-of-range/non-Boolean
  target or table domains are `.stable`.

Dependencies:
  - LeanFzn.Solver.Propagation.Proofs.Fam.VarElement: the shared 1-based
    entry helpers (`avieEntry` and its reads) and, transitively,
    Fam.Element / Fam.Bool / Fam.Lin.

DAG:
  Fam.VarElement -> Fam.BoolElement -> Proofs.Propagators
    (registration + safety triple) -> Reason / BoxPropagators / FallbackFit
    -> the Lcg* consumer arms.
-/

import LeanFzn.Solver.Propagation.Proofs.Fam.VarElement
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Reference


open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Reference

/-! ## PLAN §3.3 item 2: the variable-table Boolean element propagator -/

/-- The first Boolean value of `d` that fails `keep` (values without a
    Boolean view are skipped; the guard makes them absent). -/
def avbeFirstBad (d : List Value) (keep : Bool → Bool) : Option Bool :=
  d.findSome? fun v =>
    match v with
    | .bool b => if keep b then none else some b
    | _ => none

/-- A found bad Boolean comes from a domain value, and fails `keep`. -/
theorem avbeFirstBad_some {d : List Value} {keep : Bool → Bool} {b : Bool}
    (h : avbeFirstBad d keep = some b) :
    ∃ v ∈ d, v = .bool b ∧ keep b = false := by
  unfold avbeFirstBad at h
  obtain ⟨v, hv, hfv⟩ := List.exists_of_findSome?_eq_some h
  cases v with
  | bool c =>
      dsimp only at hfv
      by_cases hk : keep c = true
      · rw [if_pos hk] at hfv
        cases hfv
      · rw [if_neg hk] at hfv
        have hcb : c = b := Option.some.inj hfv
        subst hcb
        exact ⟨.bool c, hv, rfl, Bool.eq_false_iff.mpr hk⟩
  | int c => simp at hfv
  | setOfInt s => simp at hfv
  | array a => simp at hfv

/-- When no bad Boolean is found, every Boolean value of the domain
    passes `keep`. -/
theorem avbeFirstBad_none {d : List Value} {keep : Bool → Bool}
    (h : avbeFirstBad d keep = none) :
    ∀ v ∈ d, ∀ b : Bool, v = .bool b → keep b = true := by
  intro v hv b hb
  by_cases hk : keep b = true
  · exact hk
  · exfalso
    have hfv := List.findSome?_eq_none_iff.mp h v hv
    rw [hb] at hfv
    dsimp only at hfv
    rw [if_neg hk] at hfv
    cases hfv

/-- The `arrayVarBoolElementSlot` semantics at the reads: the index reads
    an integer, the target and the entry slot read the same Boolean. -/
theorem arrayVarBoolElement_views {a : Assignment} {is : List Nat} {i k : Nat}
    (h : (DomConstraint.arrayVarBoolElementSlot is i k).SatisfiedBy a) :
    ∃ idx : Int, ∃ b : Bool, ∃ js : Nat,
      a[i]? = some (.int idx) ∧ a[k]? = some (.bool b) ∧
      avieEntry is idx = some js ∧ a[js]? = some (.bool b) := by
  obtain ⟨idx, b, hi, hk, hall, hget⟩ := h
  obtain ⟨j, hent, hj⟩ := avie_entry_of_valuesGet1 hall hget
  exact ⟨idx, b, j, hi, hk, hent, hj⟩

/-- With the index read at `idx`, the target and the entry slot read the
    same Boolean. -/
theorem avbe_entry_reads {a : Assignment} {is : List Nat} {i k : Nat}
    {idx : Int} {j : Nat}
    (h : (DomConstraint.arrayVarBoolElementSlot is i k).SatisfiedBy a)
    (hi : a[i]? = some (.int idx))
    (he : avieEntry is idx = some j) :
    ∃ b : Bool, a[k]? = some (.bool b) ∧ a[j]? = some (.bool b) := by
  obtain ⟨idx', b, j', hi', hk, hent', hj'⟩ := arrayVarBoolElement_views h
  have hidx' : idx' = idx :=
    Value.int.inj (Option.some.inj (hi'.symm.trans hi))
  rw [hidx'] at hent'
  have hjj : j' = j := Option.some.inj (hent'.symm.trans he)
  rw [hjj] at hj'
  exact ⟨b, hk, hj'⟩

/-- A fitting membership read of a Boolean value. -/
theorem avbe_fits_mem {st : State} {a : Assignment} {s : Nat} {v : Value}
    (hfit : Core.Assignment.Fits st.domains a) (h : a[s]? = some v) :
    v ∈ st.domains.getD s Dom.empty := hfit.2 s v h

/-- A value missing from a domain cannot be read at a fitting solution. -/
theorem avbe_not_mem_of_fit {st : State} {a : Assignment} {s : Nat} {b : Bool}
    (hfit : Core.Assignment.Fits st.domains a)
    (hread : a[s]? = some (.bool b))
    (hvm : valueMemB ((.bool b)) (slotEnum st.domains s) = false) : False := by
  have hmem : (.bool b : Value) ∈ st.domains.getD s Dom.empty :=
    hfit.2 s (.bool b) hread
  have hmemE : (.bool b : Value) ∈ slotEnum st.domains s := by
    simpa [slotEnum] using (DomainLike.mem_iff _ _).mp hmem
  have htrue : valueMemB ((.bool b)) (slotEnum st.domains s) = true :=
    valueMemB_iff.mpr hmemE
  rw [hvm] at htrue
  cases htrue

/-- A fitting read of a Boolean-only slot is a Boolean. -/
theorem avbe_read_bool_of_guard {st : State} {a : Assignment} {s : Nat}
    (hfit : Core.Assignment.Fits st.domains a)
    (hb : domBoolOnlyB (slotEnum st.domains s) = true) :
    ∃ p : Bool, a[s]? = some (.bool p) := by
  obtain ⟨hlen0, hallb⟩ := domBoolOnlyB_eq hb
  have hne : st.domains.getD s Dom.empty ≠ Dom.empty := by
    intro h0
    rw [slotEnum, h0, Dom.enum_empty] at hlen0
    simp at hlen0
  have hlt : s < st.domains.length := by
    by_cases hlt' : s < st.domains.length
    · exact hlt'
    · exact absurd (getD_nil_of_length_le hlt') hne
  have hs2 : s < a.length := by rw [hfit.1]; exact hlt
  have hread : a[s]? = some a[s] := List.getElem?_eq_getElem hs2
  have hmemE : a[s] ∈ slotEnum st.domains s := by
    simpa [slotEnum] using (DomainLike.mem_iff _ _).mp (hfit.2 s a[s] hread)
  obtain ⟨p, hp⟩ := hallb a[s] hmemE
  exact ⟨p, by rw [hread, hp]⟩

/-! ### The emissions -/

/-- The pinned-index out-of-range conflict. -/
def avbeResPinBad (i : Nat) (idx : Int) : PropagationResult :=
  .conflict [posNe i idx]

/-- The out-of-range index removal: the unit clause `[posNe i idx]`. -/
def avbeResOut (i : Nat) (idx : Int) : PropagationResult :=
  .implied (posNe i idx) { clause := [posNe i idx] }

/-- The pinned-target index removal through the falsified target
    `posBool k (!v)` and the falsified entry `posBool j v`. -/
def avbeResPinVal (i k j : Nat) (idx : Int) (v : Bool) : PropagationResult :=
  .implied (posNe i idx)
    { clause := [posNe i idx, posBool k (!v), posBool j v] }

/-- The opposite-singleton entry removal: the falsified entry pin and the
    falsified target value. -/
def avbeResSingle (i k j : Nat) (idx : Int) (b : Bool) : PropagationResult :=
  .implied (posNe i idx)
    { clause := [posNe i idx, posBool j (!b), posBool k b] }

/-- The pinned-index target removal: remove the first target value absent
    from the entry slot, escaping through the pin and the entry equality. -/
def avbeResTarget (st : State) (i k j : Nat) (idx : Int) (b : Bool) :
    PropagationResult :=
  implyBool st k (!b) [posBool k (!b), posNe i idx, posBool j b]

/-- The pinned-index entry removal: remove the first entry value absent
    from the target, escaping through the pin and the target equality. -/
def avbeResEntry (st : State) (i k j : Nat) (idx : Int) (b : Bool) :
    PropagationResult :=
  implyBool st j (!b) [posBool j (!b), posNe i idx, posBool k b]

/-- The target value supported by no table slot: `posBool k (!b)` with
    every table slot's `posBool j b` as the falsified causes. -/
def avbeResNoSupp (st : State) (k : Nat) (is : List Nat) (b : Bool) :
    PropagationResult :=
  implyBool st k (!b) (posBool k (!b) :: is.map (fun j => posBool j b))

/-- Does some table slot's domain contain the Boolean `b`? -/
def avbeTableMemB (st : State) (is : List Nat) (b : Bool) : Bool :=
  is.any (fun j => valueMemB ((.bool b)) (slotEnum st.domains j))

/-- The pinned-target round's keep test: the entry exists and can read the
    pinned target Boolean. -/
def avbePinTargetOkB (st : State) (is : List Nat) (idx : Int) (v : Bool) :
    Bool :=
  match avieEntry is idx with
  | none => false
  | some j => valueMemB ((.bool v)) (slotEnum st.domains j)

/-- The pinned-target round's response: the unit out-of-range removal, the
    supported `.stable`, or the entry-equality removal. -/
def avbePinTargetRes (st : State) (is : List Nat) (i k : Nat) (idx : Int)
    (v : Bool) : PropagationResult :=
  match avieEntry is idx with
  | none => avbeResOut i idx
  | some j =>
      if valueMemB ((.bool v)) (slotEnum st.domains j) then .stable
      else avbeResPinVal i k j idx v

/-- A failed pinned-target keep test is an out-of-range index or an entry
    slot that cannot read the target. -/
theorem avbePinTargetRes_of_bad {st : State} {is : List Nat} {i k : Nat}
    {idx : Int} {v : Bool}
    (hbad : avbePinTargetOkB st is idx v = false) :
    (avieEntry is idx = none ∧
      avbePinTargetRes st is i k idx v = avbeResOut i idx) ∨
    (∃ j : Nat, avieEntry is idx = some j ∧
      valueMemB ((.bool v)) (slotEnum st.domains j) = false ∧
      avbePinTargetRes st is i k idx v = avbeResPinVal i k j idx v) := by
  unfold avbePinTargetOkB at hbad
  split at hbad
  · next hnone =>
      left
      exact ⟨hnone, by unfold avbePinTargetRes; rw [hnone]⟩
  · next j hent =>
      right
      refine ⟨j, hent, hbad, ?_⟩
      unfold avbePinTargetRes
      rw [hent]
      dsimp only
      rw [hbad]
      rfl

/-- A singleton entry whose Boolean is absent from the target domain. -/
def avbeSingleBadB (st : State) (is : List Nat) (idx : Int) (k : Nat) : Bool :=
  match avieEntry is idx with
  | none => false
  | some j =>
      match slotEnum st.domains j with
      | [.bool b] => !valueMemB ((.bool b)) (slotEnum st.domains k)
      | _ => false

/-- The opposite-singleton entry separation response. -/
def avbeSingleRes (st : State) (is : List Nat) (i k : Nat) (idx : Int) :
    PropagationResult :=
  match avieEntry is idx with
  | none => .stable
  | some j =>
      match slotEnum st.domains j with
      | [.bool b] =>
          if valueMemB ((.bool b)) (slotEnum st.domains k) then .stable
          else avbeResSingle i k j idx b
      | _ => .stable

/-- A hit of the opposite-singleton round exposes the entry slot and its
    Boolean. -/
theorem avbeSingleRes_of_bad {st : State} {is : List Nat} {i k : Nat}
    {idx : Int} (hbad : avbeSingleBadB st is idx k = true) :
    ∃ j : Nat, ∃ b : Bool,
      avieEntry is idx = some j ∧
      slotEnum st.domains j = [.bool b] ∧
      valueMemB ((.bool b)) (slotEnum st.domains k) = false ∧
      avbeSingleRes st is i k idx = avbeResSingle i k j idx b := by
  unfold avbeSingleBadB at hbad
  split at hbad
  · cases hbad
  · next j hent =>
      split at hbad
      · next b hdj =>
          have hnot : valueMemB ((.bool b)) (slotEnum st.domains k) = false := by
            simpa using hbad
          refine ⟨j, b, hent, hdj, hnot, ?_⟩
          unfold avbeSingleRes
          rw [hent]
          dsimp only
          rw [hdj]
          dsimp only
          rw [hnot]
          rfl
      · next => cases hbad

/-! ### The propagator -/

/-- The family guard: the index domain is integer-only and nonempty; the
    target and every table slot are Boolean-only and nonempty. -/
def avbeGuardB (st : State) (is : List Nat) (i k : Nat) : Bool :=
  domsIntOnlyB st.domains [i] &&
    (domBoolOnlyB (slotEnum st.domains k) &&
      is.all (fun j => domBoolOnlyB (slotEnum st.domains j)))

/-- The guard's components. -/
theorem avbeGuardB_eq {st : State} {is : List Nat} {i k : Nat}
    (h : avbeGuardB st is i k = true) :
    domsIntOnlyB st.domains [i] = true ∧
      domBoolOnlyB (slotEnum st.domains k) = true ∧
      ∀ j ∈ is, domBoolOnlyB (slotEnum st.domains j) = true := by
  unfold avbeGuardB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hi, hb⟩ := h
  rw [Bool.and_eq_true] at hb
  exact ⟨hi, hb.1, fun j hj => List.all_eq_true.mp hb.2 j hj⟩

/-- PLAN §3.3 item 2: the explained propagator of `array_var_bool_element`
    — `arrayVarBoolElementSlot is i k` (the table slots `is`; `i` the
    1-based index slot, `k` the Boolean element slot). Guarded rounds, in
    order:

    * aliasing (`i = k`), the index or target occurring in the table, a
      repeated table slot, and non-integer/empty/out-of-range/non-Boolean
      slots ⇒ `.stable`;
    * pinned index `[.int idx]`: an out-of-range position is the conflict
      `[i ≠ idx]`; otherwise the target loses the first Boolean absent
      from the entry slot's domain, then the entry slot loses the first
      Boolean absent from the target domain (both escaping through
      `i ≠ idx`);
    * pinned target `[.bool v]`: removes the first index whose table slot
      cannot read `v` or is out of range (through the falsified target
      cause `k = !v`);
    * unpinned index: removes the first out-of-range index by the unit
      `posNe i idx`, then the first index whose entry is the opposite
      Boolean singleton; if no entry is separated, removes the first
      target value absent from every table slot.

    Every emission's clause is over the existing vocabulary: `posNe`
    index-removal literals and `posBool` Boolean pins/removals on the
    target and table slots. -/
def propArrayVarBoolElement (st : State) (is : List Nat) (i k : Nat) :
    PropagationResult :=
  if i = k then .stable
  else if is.elem i || is.elem k then .stable
  else if decide is.Nodup = false then .stable
  else if avbeGuardB st is i k = false then .stable
  else
    match slotEnum st.domains i with
    | [.int idx] =>
        match avieEntry is idx with
        | none => avbeResPinBad i idx
        | some j =>
            match avbeFirstBad (slotEnum st.domains k)
                (fun b => valueMemB ((.bool b)) (slotEnum st.domains j)) with
            | some b => avbeResTarget st i k j idx b
            | none =>
                match avbeFirstBad (slotEnum st.domains j)
                    (fun b => valueMemB ((.bool b)) (slotEnum st.domains k)) with
                | some b => avbeResEntry st i k j idx b
                | none => .stable
    | _ =>
        match slotEnum st.domains k with
        | [.bool v] =>
            match firstBadView (slotEnum st.domains i)
                (fun idx => avbePinTargetOkB st is idx v) with
            | some idx => avbePinTargetRes st is i k idx v
            | none => .stable
        | _ =>
            match firstBadView (slotEnum st.domains i)
                (fun idx => (avieEntry is idx).isSome) with
            | some idx => avbeResOut i idx
            | none =>
                match firstBadView (slotEnum st.domains i)
                    (fun idx => !avbeSingleBadB st is idx k) with
                | some idx => avbeSingleRes st is i k idx
                | none =>
                    match avbeFirstBad (slotEnum st.domains k)
                        (fun b => avbeTableMemB st is b) with
                    | some b => avbeResNoSupp st k is b
                    | none => .stable

/-- Complete case split of `propArrayVarBoolElement`: `.stable`, the
    pinned-index out-of-range conflict, the pinned-index target/entry
    removals, the pinned-target index removals (out-of-range or missing
    entry value), the unpinned out-of-range unit removal, the
    opposite-singleton entry removal, or the no-support target removal. -/
theorem propArrayVarBoolElement_cases (st : State) (is : List Nat) (i k : Nat) :
    propArrayVarBoolElement st is i k = .stable ∨
    (∃ idx : Int, slotEnum st.domains i = [.int idx] ∧
      avieEntry is idx = none ∧
      propArrayVarBoolElement st is i k = avbeResPinBad i idx) ∨
    (∃ idx : Int, ∃ j : Nat, ∃ b : Bool,
      slotEnum st.domains i = [.int idx] ∧ avieEntry is idx = some j ∧
      avbeFirstBad (slotEnum st.domains k)
        (fun b => valueMemB ((.bool b)) (slotEnum st.domains j)) = some b ∧
      propArrayVarBoolElement st is i k = avbeResTarget st i k j idx b) ∨
    (∃ idx : Int, ∃ j : Nat, ∃ b : Bool,
      slotEnum st.domains i = [.int idx] ∧ avieEntry is idx = some j ∧
      avbeFirstBad (slotEnum st.domains k)
        (fun b => valueMemB ((.bool b)) (slotEnum st.domains j)) = none ∧
      avbeFirstBad (slotEnum st.domains j)
        (fun b => valueMemB ((.bool b)) (slotEnum st.domains k)) = some b ∧
      propArrayVarBoolElement st is i k = avbeResEntry st i k j idx b) ∨
    (∃ idx : Int, ∃ v : Bool, slotEnum st.domains k = [.bool v] ∧
      avieEntry is idx = none ∧
      firstBadView (slotEnum st.domains i)
        (fun idx => avbePinTargetOkB st is idx v) = some idx ∧
      propArrayVarBoolElement st is i k = avbeResOut i idx) ∨
    (∃ idx : Int, ∃ v : Bool, ∃ j : Nat,
      slotEnum st.domains k = [.bool v] ∧ avieEntry is idx = some j ∧
      valueMemB ((.bool v)) (slotEnum st.domains j) = false ∧
      firstBadView (slotEnum st.domains i)
        (fun idx => avbePinTargetOkB st is idx v) = some idx ∧
      propArrayVarBoolElement st is i k = avbeResPinVal i k j idx v) ∨
    (∃ idx : Int, avieEntry is idx = none ∧
      firstBadView (slotEnum st.domains i)
        (fun idx => (avieEntry is idx).isSome) = some idx ∧
      propArrayVarBoolElement st is i k = avbeResOut i idx) ∨
    (∃ idx : Int, ∃ j : Nat, ∃ b : Bool,
      avieEntry is idx = some j ∧
      slotEnum st.domains j = [.bool b] ∧
      valueMemB ((.bool b)) (slotEnum st.domains k) = false ∧
      firstBadView (slotEnum st.domains i)
        (fun idx => !avbeSingleBadB st is idx k) = some idx ∧
      propArrayVarBoolElement st is i k = avbeResSingle i k j idx b) ∨
    (∃ b : Bool,
      firstBadView (slotEnum st.domains i)
        (fun idx => (avieEntry is idx).isSome) = none ∧
      firstBadView (slotEnum st.domains i)
        (fun idx => !avbeSingleBadB st is idx k) = none ∧
      avbeFirstBad (slotEnum st.domains k)
        (fun b => avbeTableMemB st is b) = some b ∧
      propArrayVarBoolElement st is i k = avbeResNoSupp st k is b) := by
  unfold propArrayVarBoolElement
  by_cases halias : i = k
  · rw [if_pos halias]; exact Or.inl rfl
  · rw [if_neg halias]
    by_cases htab : (is.elem i || is.elem k) = true
    · rw [if_pos htab]; exact Or.inl rfl
    · rw [if_neg htab]
      by_cases hnodup : decide is.Nodup = false
      · rw [if_pos hnodup]; exact Or.inl rfl
      · rw [if_neg hnodup]
        by_cases hguard : avbeGuardB st is i k = false
        · rw [if_pos hguard]; exact Or.inl rfl
        · rw [if_neg hguard]
          split
          · next idx hidx =>
            split
            · next hnone =>
                iterate 1 (apply Or.inr)
                left
                exact ⟨idx, hidx, hnone, rfl⟩
            · next j hent =>
                split
                · next b hfb =>
                    iterate 2 (apply Or.inr)
                    left
                    exact ⟨idx, j, b, hidx, hent, hfb, rfl⟩
                · next hfbK =>
                    split
                    · next b hfbJ =>
                        iterate 3 (apply Or.inr)
                        left
                        exact ⟨idx, j, b, hidx, hent, hfbK, hfbJ, rfl⟩
                    · next => exact Or.inl rfl
          · next =>
            split
            · next v hk =>
                split
                · next idx hfb =>
                    have hbad : avbePinTargetOkB st is idx v = false :=
                      avie_firstBadView_false
                        (d := slotEnum st.domains i)
                        (keep := fun idx => avbePinTargetOkB st is idx v)
                        (w := idx) hfb
                    rcases avbePinTargetRes_of_bad hbad with
                      ⟨hnone, hres⟩ | ⟨j, hent, hmem, hres⟩
                    · iterate 4 (apply Or.inr)
                      left
                      exact ⟨idx, v, hk, hnone, hfb, hres⟩
                    · iterate 5 (apply Or.inr)
                      left
                      exact ⟨idx, v, j, hk, hent, hmem, hfb, hres⟩
                · next => exact Or.inl rfl
            · next =>
                split
                · next idx hfb =>
                    have hnone : avieEntry is idx = none :=
                      avie_entry_none_of_isSome_false
                        (avie_firstBadView_false
                          (d := slotEnum st.domains i)
                          (keep := fun idx => (avieEntry is idx).isSome)
                          (w := idx) hfb)
                    iterate 6 (apply Or.inr)
                    left
                    exact ⟨idx, hnone, hfb, rfl⟩
                · next hfbOut =>
                    split
                    · next idx hfb =>
                        have hbad : avbeSingleBadB st is idx k = true := by
                          have hk := avie_firstBadView_false
                            (d := slotEnum st.domains i)
                            (keep := fun idx => !avbeSingleBadB st is idx k)
                            (w := idx) hfb
                          simpa using hk
                        rcases avbeSingleRes_of_bad hbad with
                          ⟨j, b, hent, hdj, hmem, hres⟩
                        iterate 7 (apply Or.inr)
                        left
                        exact ⟨idx, j, b, hent, hdj, hmem, hfb, hres⟩
                    · next hfbSingle =>
                        split
                        · next b hfbw =>
                            iterate 8 (apply Or.inr)
                            exact ⟨b, hfbOut, hfbSingle, hfbw, rfl⟩
                        · next => exact Or.inl rfl

/-- Any non-`.stable` emission happens past the Boolean/int domain guard. -/
theorem avbe_guard_of_res {st : State} {is : List Nat} {i k : Nat}
    {res : PropagationResult}
    (h : propArrayVarBoolElement st is i k = res) (hne : res ≠ .stable) :
    avbeGuardB st is i k = true := by
  unfold propArrayVarBoolElement at h
  by_cases halias : i = k
  · rw [if_pos halias] at h
    exact absurd h.symm hne
  · rw [if_neg halias] at h
    by_cases htab : (is.elem i || is.elem k) = true
    · rw [if_pos htab] at h
      exact absurd h.symm hne
    · rw [if_neg htab] at h
      by_cases hnodup : decide is.Nodup = false
      · rw [if_pos hnodup] at h
        exact absurd h.symm hne
      · rw [if_neg hnodup] at h
        by_cases hguard : avbeGuardB st is i k = false
        · rw [if_pos hguard] at h
          exact absurd h.symm hne
        · cases hv : avbeGuardB st is i k with
          | true => rfl
          | false => exact absurd hv hguard

/-! ### Clause entailment at solutions (the reason side) -/

/-- The out-of-range clause carries a true literal at every solution. -/
theorem avbeResOut_entailed {a : Assignment} {is : List Nat} {i k : Nat}
    {idx : Int}
    (h : (DomConstraint.arrayVarBoolElementSlot is i k).SatisfiedBy a)
    (hnone : avieEntry is idx = none) :
    ∃ l ∈ [posNe i idx], l.eval a = some true := by
  obtain ⟨idx', b, j', hi, hk, hent', hj'⟩ := arrayVarBoolElement_views h
  by_cases hidx : idx' = idx
  · rw [hidx] at hent'
    rw [hent'] at hnone
    cases hnone
  · exact ⟨posNe i idx, List.mem_singleton_self _,
      aie_posNe_eval_true (slotInt_of_int_read hi) hidx⟩

/-- The pinned-target removal's clause carries a true literal. -/
theorem avbeResPinVal_entailed {a : Assignment} {is : List Nat} {i k : Nat}
    {idx : Int} {j : Nat} {v : Bool}
    (h : (DomConstraint.arrayVarBoolElementSlot is i k).SatisfiedBy a)
    (he : avieEntry is idx = some j) :
    ∃ l ∈ [posNe i idx, posBool k (!v), posBool j v],
      l.eval a = some true := by
  by_cases hpin : a[i]? = some (.int idx)
  · obtain ⟨e, hk, hj⟩ := avbe_entry_reads h hpin he
    by_cases hev : e = v
    · exact ⟨posBool j v,
        List.mem_cons_of_mem (posNe i idx)
          (List.mem_cons_of_mem (posBool k (!v))
            (List.mem_singleton_self (posBool j v))),
        b2i_posBool_eval_true (by rw [hev] at hj; exact hj)⟩
    · have hev' : e = !v := by cases e <;> cases v <;> simp_all
      exact ⟨posBool k (!v), List.mem_cons_of_mem (posNe i idx)
        (List.mem_cons_self),
        b2i_posBool_eval_true (by rw [hev'] at hk; exact hk)⟩
  · obtain ⟨idx', b, j', hi, hk', hent', hj'⟩ := arrayVarBoolElement_views h
    have hne : idx' ≠ idx := by
      intro hidx
      apply hpin
      rw [hidx] at hi
      exact hi
    exact ⟨posNe i idx, List.mem_cons_self,
      aie_posNe_eval_true (slotInt_of_int_read hi) hne⟩

/-- The opposite-singleton removal's clause carries a true literal. -/
theorem avbeResSingle_entailed {a : Assignment} {is : List Nat} {i k : Nat}
    {idx : Int} {j : Nat} {b : Bool}
    (h : (DomConstraint.arrayVarBoolElementSlot is i k).SatisfiedBy a)
    (he : avieEntry is idx = some j) :
    ∃ l ∈ [posNe i idx, posBool j (!b), posBool k b],
      l.eval a = some true := by
  by_cases hpin : a[i]? = some (.int idx)
  · obtain ⟨e, hk, hj⟩ := avbe_entry_reads h hpin he
    by_cases hev : e = b
    · exact ⟨posBool k b,
        List.mem_cons_of_mem (posNe i idx)
          (List.mem_cons_of_mem (posBool j (!b))
            (List.mem_singleton_self (posBool k b))),
        b2i_posBool_eval_true (by rw [hev] at hk; exact hk)⟩
    · have hev' : e = !b := by cases e <;> cases b <;> simp_all
      exact ⟨posBool j (!b), List.mem_cons_of_mem (posNe i idx)
        (List.mem_cons_self),
        b2i_posBool_eval_true (by rw [hev'] at hj; exact hj)⟩
  · obtain ⟨idx', c, j', hi, hk', hent', hj'⟩ := arrayVarBoolElement_views h
    have hne : idx' ≠ idx := by
      intro hidx
      apply hpin
      rw [hidx] at hi
      exact hi
    exact ⟨posNe i idx, List.mem_cons_self,
      aie_posNe_eval_true (slotInt_of_int_read hi) hne⟩

/-- The pinned-index target removal's clause carries a true literal. -/
theorem avbeResTarget_entailed {a : Assignment} {is : List Nat} {i k : Nat}
    {idx : Int} {j : Nat} {b : Bool}
    (h : (DomConstraint.arrayVarBoolElementSlot is i k).SatisfiedBy a)
    (he : avieEntry is idx = some j) :
    ∃ l ∈ [posBool k (!b), posNe i idx, posBool j b],
      l.eval a = some true := by
  by_cases hpin : a[i]? = some (.int idx)
  · obtain ⟨e, hk, hj⟩ := avbe_entry_reads h hpin he
    by_cases hev : e = b
    · exact ⟨posBool j b,
        List.mem_cons_of_mem (posBool k (!b))
          (List.mem_cons_of_mem (posNe i idx)
            (List.mem_singleton_self (posBool j b))),
        b2i_posBool_eval_true (by rw [hev] at hj; exact hj)⟩
    · have hev' : e = !b := by cases e <;> cases b <;> simp_all
      exact ⟨posBool k (!b), List.mem_cons_self,
        b2i_posBool_eval_true (by rw [hev'] at hk; exact hk)⟩
  · obtain ⟨idx', c, j', hi, hk', hent', hj'⟩ := arrayVarBoolElement_views h
    have hne : idx' ≠ idx := by
      intro hidx
      apply hpin
      rw [hidx] at hi
      exact hi
    exact ⟨posNe i idx, List.mem_cons_of_mem (posBool k (!b))
        (List.mem_cons_self),
      aie_posNe_eval_true (slotInt_of_int_read hi) hne⟩

/-- The pinned-index entry removal's clause carries a true literal. -/
theorem avbeResEntry_entailed {a : Assignment} {is : List Nat} {i k : Nat}
    {idx : Int} {j : Nat} {b : Bool}
    (h : (DomConstraint.arrayVarBoolElementSlot is i k).SatisfiedBy a)
    (he : avieEntry is idx = some j) :
    ∃ l ∈ [posBool j (!b), posNe i idx, posBool k b],
      l.eval a = some true := by
  by_cases hpin : a[i]? = some (.int idx)
  · obtain ⟨e, hk, hj⟩ := avbe_entry_reads h hpin he
    by_cases hev : e = b
    · exact ⟨posBool k b,
        List.mem_cons_of_mem (posBool j (!b))
          (List.mem_cons_of_mem (posNe i idx)
            (List.mem_singleton_self (posBool k b))),
        b2i_posBool_eval_true (by rw [hev] at hk; exact hk)⟩
    · have hev' : e = !b := by cases e <;> cases b <;> simp_all
      exact ⟨posBool j (!b), List.mem_cons_self,
        b2i_posBool_eval_true (by rw [hev'] at hj; exact hj)⟩
  · obtain ⟨idx', c, j', hi, hk', hent', hj'⟩ := arrayVarBoolElement_views h
    have hne : idx' ≠ idx := by
      intro hidx
      apply hpin
      rw [hidx] at hi
      exact hi
    exact ⟨posNe i idx, List.mem_cons_of_mem (posBool j (!b))
        (List.mem_cons_self),
      aie_posNe_eval_true (slotInt_of_int_read hi) hne⟩

/-- The no-support clause carries a true literal at every solution. -/
theorem avbeResNoSupp_entailed {a : Assignment} {is : List Nat} {i k : Nat}
    {b : Bool}
    (h : (DomConstraint.arrayVarBoolElementSlot is i k).SatisfiedBy a) :
    ∃ l ∈ posBool k (!b) :: is.map (fun j => posBool j b),
      l.eval a = some true := by
  obtain ⟨idx', e, j', hi, hk, hent', hj'⟩ := arrayVarBoolElement_views h
  by_cases heb : e = b
  · refine ⟨posBool j' b, List.mem_cons_of_mem _ (List.mem_map.mpr
      ⟨j', avieEntry_mem hent', rfl⟩), ?_⟩
    exact b2i_posBool_eval_true (by rw [heb] at hj'; exact hj')
  · have heq : e = !b := by cases e <;> cases b <;> simp_all
    exact ⟨posBool k (!b), List.mem_cons_self,
      b2i_posBool_eval_true (by rw [heq] at hk; exact hk)⟩

/-! ### Fitting-solution heads and conflict exclusion -/

/-- The pinned-index out-of-range conflict excludes every fitting solution. -/
theorem avbeResPinBad_excluded {st : State} {a : Assignment} {is : List Nat}
    {i k : Nat} {idx : Int}
    (hfit : Core.Assignment.Fits st.domains a)
    (hidx : slotEnum st.domains i = [.int idx])
    (hnone : avieEntry is idx = none)
    (h : (DomConstraint.arrayVarBoolElementSlot is i k).SatisfiedBy a) : False := by
  have hi : a[i]? = some (.int idx) := aie_read_of_dom_singleton hfit hidx
  obtain ⟨idx', b, j', hi', hk, hent', hj'⟩ := arrayVarBoolElement_views h
  have hidx' : idx' = idx :=
    Value.int.inj (Option.some.inj (hi'.symm.trans hi))
  subst hidx'
  rw [hent'] at hnone
  cases hnone

/-- The unpinned out-of-range removal is true at every solution. -/
theorem avbe_out_true {a : Assignment} {is : List Nat} {i k : Nat} {idx : Int}
    (h : (DomConstraint.arrayVarBoolElementSlot is i k).SatisfiedBy a)
    (hnone : avieEntry is idx = none) :
    (posNe i idx).eval a = some true := by
  obtain ⟨idx', b, j', hi, hk, hent', hj'⟩ := arrayVarBoolElement_views h
  by_cases hidx : idx' = idx
  · rw [hidx] at hent'
    rw [hent'] at hnone
    cases hnone
  · exact aie_posNe_eval_true (slotInt_of_int_read hi) hidx

/-- The pinned-target removal is true at every fitting solution. -/
theorem avbe_pinVal_head {st : State} {a : Assignment} {is : List Nat}
    {i k : Nat} {idx : Int} {j : Nat} {v : Bool}
    (hfit : Core.Assignment.Fits st.domains a)
    (hk : slotEnum st.domains k = [.bool v])
    (h : (DomConstraint.arrayVarBoolElementSlot is i k).SatisfiedBy a)
    (he : avieEntry is idx = some j)
    (hvm : valueMemB ((.bool v)) (slotEnum st.domains j) = false) :
    (posNe i idx).eval a = some true := by
  obtain ⟨idx', b, j', hi, hkRead, hent', hj'⟩ := arrayVarBoolElement_views h
  by_cases hidx : idx' = idx
  · rw [hidx] at hent'
    have hjj : j' = j := Option.some.inj (hent'.symm.trans he)
    rw [hjj] at hj'
    have hmemk : (.bool b : Value) ∈ st.domains.getD k Dom.empty :=
      hfit.2 k (.bool b) hkRead
    have hmemkE : (.bool b : Value) ∈ slotEnum st.domains k := by
      simpa [slotEnum] using (DomainLike.mem_iff _ _).mp hmemk
    rw [hk] at hmemkE
    have hbv : b = v := Value.bool.inj (List.mem_singleton.mp hmemkE)
    have hmemj : (.bool b : Value) ∈ st.domains.getD j Dom.empty :=
      hfit.2 j (.bool b) hj'
    rw [hbv] at hmemj
    have hmemjE : (.bool v : Value) ∈ slotEnum st.domains j := by
      simpa [slotEnum] using (DomainLike.mem_iff _ _).mp hmemj
    have htrue : valueMemB ((.bool v)) (slotEnum st.domains j) = true :=
      valueMemB_iff.mpr hmemjE
    rw [hvm] at htrue
    cases htrue
  · exact aie_posNe_eval_true (slotInt_of_int_read hi) hidx

/-- The opposite-singleton removal is true at every fitting solution. -/
theorem avbe_single_head {st : State} {a : Assignment} {is : List Nat}
    {i k : Nat} {idx : Int} {j : Nat} {b : Bool}
    (hfit : Core.Assignment.Fits st.domains a)
    (h : (DomConstraint.arrayVarBoolElementSlot is i k).SatisfiedBy a)
    (he : avieEntry is idx = some j)
    (hdj : slotEnum st.domains j = [.bool b])
    (hvm : valueMemB ((.bool b)) (slotEnum st.domains k) = false) :
    (posNe i idx).eval a = some true := by
  obtain ⟨idx', c, j', hi, hk, hent', hj'⟩ := arrayVarBoolElement_views h
  by_cases hidx : idx' = idx
  · rw [hidx] at hent'
    have hjj : j' = j := Option.some.inj (hent'.symm.trans he)
    rw [hjj] at hj'
    have hmemj : (.bool c : Value) ∈ st.domains.getD j Dom.empty :=
      hfit.2 j (.bool c) hj'
    have hmemjE : (.bool c : Value) ∈ slotEnum st.domains j := by
      simpa [slotEnum] using (DomainLike.mem_iff _ _).mp hmemj
    rw [hdj] at hmemjE
    have hcb : c = b := Value.bool.inj (List.mem_singleton.mp hmemjE)
    have hmemk : (.bool c : Value) ∈ st.domains.getD k Dom.empty :=
      hfit.2 k (.bool c) hk
    rw [hcb] at hmemk
    have hmemkE : (.bool b : Value) ∈ slotEnum st.domains k := by
      simpa [slotEnum] using (DomainLike.mem_iff _ _).mp hmemk
    have htrue : valueMemB ((.bool b)) (slotEnum st.domains k) = true :=
      valueMemB_iff.mpr hmemkE
    rw [hvm] at htrue
    cases htrue
  · exact aie_posNe_eval_true (slotInt_of_int_read hi) hidx

/-- The table-membership test is false on every table slot. -/
theorem avbeTableMemB_false {st : State} {is : List Nat} {b : Bool} {j : Nat}
    (h : avbeTableMemB st is b = false) (hj : j ∈ is) :
    valueMemB ((.bool b)) (slotEnum st.domains j) = false := by
  unfold avbeTableMemB at h
  exact Bool.eq_false_iff.mpr (List.any_eq_false.mp h j hj)

/-- At a pinned index the target reads the negated missing entry Boolean. -/
theorem avbe_target_head {st : State} {a : Assignment} {is : List Nat}
    {i k : Nat} {idx : Int} {j : Nat} {b : Bool}
    (hfit : Core.Assignment.Fits st.domains a)
    (hidx : slotEnum st.domains i = [.int idx])
    (h : (DomConstraint.arrayVarBoolElementSlot is i k).SatisfiedBy a)
    (he : avieEntry is idx = some j)
    (hfb : avbeFirstBad (slotEnum st.domains k)
      (fun b => valueMemB ((.bool b)) (slotEnum st.domains j)) = some b) :
    a[k]? = some (.bool (!b)) := by
  obtain ⟨-, -, -, hbad⟩ := avbeFirstBad_some hfb
  have hi : a[i]? = some (.int idx) := aie_read_of_dom_singleton hfit hidx
  obtain ⟨e, hk, hj⟩ := avbe_entry_reads h hi he
  have hmemj : (.bool e : Value) ∈ st.domains.getD j Dom.empty :=
    hfit.2 j (.bool e) hj
  have hne : e ≠ b := by
    intro hev
    have hmemE : (.bool b : Value) ∈ slotEnum st.domains j := by
      have hw : (.bool b : Value) ∈ st.domains.getD j Dom.empty := by
        rw [← hev]; exact hmemj
      simpa [slotEnum] using (DomainLike.mem_iff _ _).mp hw
    have htrue : valueMemB ((.bool b)) (slotEnum st.domains j) = true :=
      valueMemB_iff.mpr hmemE
    rw [hbad] at htrue
    cases htrue
  have heq : e = !b := by cases e <;> cases b <;> simp_all
  rw [heq] at hk
  exact hk

/-- At a pinned index the entry reads the negated missing target Boolean. -/
theorem avbe_entry_head {st : State} {a : Assignment} {is : List Nat}
    {i k : Nat} {idx : Int} {j : Nat} {b : Bool}
    (hfit : Core.Assignment.Fits st.domains a)
    (hidx : slotEnum st.domains i = [.int idx])
    (h : (DomConstraint.arrayVarBoolElementSlot is i k).SatisfiedBy a)
    (he : avieEntry is idx = some j)
    (hfb : avbeFirstBad (slotEnum st.domains j)
      (fun b => valueMemB ((.bool b)) (slotEnum st.domains k)) = some b) :
    a[j]? = some (.bool (!b)) := by
  obtain ⟨-, -, -, hbad⟩ := avbeFirstBad_some hfb
  have hi : a[i]? = some (.int idx) := aie_read_of_dom_singleton hfit hidx
  obtain ⟨e, hk, hj⟩ := avbe_entry_reads h hi he
  have hmemk : (.bool e : Value) ∈ st.domains.getD k Dom.empty :=
    hfit.2 k (.bool e) hk
  have hne : e ≠ b := by
    intro hev
    have hmemE : (.bool b : Value) ∈ slotEnum st.domains k := by
      have hw : (.bool b : Value) ∈ st.domains.getD k Dom.empty := by
        rw [← hev]; exact hmemk
      simpa [slotEnum] using (DomainLike.mem_iff _ _).mp hw
    have htrue : valueMemB ((.bool b)) (slotEnum st.domains k) = true :=
      valueMemB_iff.mpr hmemE
    rw [hbad] at htrue
    cases htrue
  have heq : e = !b := by cases e <;> cases b <;> simp_all
  rw [heq] at hj
  exact hj

/-- A target Boolean absent from every table slot reads its negation. -/
theorem avbe_noSupp_head {st : State} {a : Assignment} {is : List Nat}
    {i k : Nat} {b : Bool}
    (hfit : Core.Assignment.Fits st.domains a)
    (h : (DomConstraint.arrayVarBoolElementSlot is i k).SatisfiedBy a)
    (hfb : avbeFirstBad (slotEnum st.domains k)
      (fun b => avbeTableMemB st is b) = some b) :
    a[k]? = some (.bool (!b)) := by
  obtain ⟨-, -, -, hbad⟩ := avbeFirstBad_some hfb
  obtain ⟨idx', e, j', hi, hk, hent', hj'⟩ := arrayVarBoolElement_views h
  by_cases heb : e = b
  · exfalso
    have hmem : (.bool b : Value) ∈ st.domains.getD j' Dom.empty := by
      rw [← heb]
      exact hfit.2 j' (.bool e) hj'
    have hmemE : (.bool b : Value) ∈ slotEnum st.domains j' := by
      simpa [slotEnum] using (DomainLike.mem_iff _ _).mp hmem
    have hfalse := avbeTableMemB_false hbad (avieEntry_mem hent')
    have htrue : valueMemB ((.bool b)) (slotEnum st.domains j') = true :=
      valueMemB_iff.mpr hmemE
    rw [hfalse] at htrue
    cases htrue
  · have heq : e = !b := by cases e <;> cases b <;> simp_all
    rw [heq] at hk
    exact hk

/-- The emitter bundles: soundness triples of the three `implyBool` rounds. -/
theorem avbeResTarget_safe {st : State} {is : List Nat} {i k : Nat}
    {idx : Int} {j : Nat} {b : Bool}
    (hidx : slotEnum st.domains i = [.int idx])
    (he : avieEntry is idx = some j)
    (hfb : avbeFirstBad (slotEnum st.domains k)
      (fun b => valueMemB ((.bool b)) (slotEnum st.domains j)) = some b) :
    (∀ l r, avbeResTarget st i k j idx b = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.arrayVarBoolElementSlot is i k).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ cc, avbeResTarget st i k j idx b = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.arrayVarBoolElementSlot is i k).SatisfiedBy a → False) ∧
    (∀ cc, avbeResTarget st i k j idx b = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.arrayVarBoolElementSlot is i k).SatisfiedBy a →
        ∃ l ∈ cc, l.eval a = some true) := by
  unfold avbeResTarget
  exact implyBool_safe
    (fun a hfit hsat => avbe_target_head hfit hidx hsat he hfb)
    (fun a hsat => avbeResTarget_entailed hsat he)
    (by simp)

theorem avbeResEntry_safe {st : State} {is : List Nat} {i k : Nat}
    {idx : Int} {j : Nat} {b : Bool}
    (hidx : slotEnum st.domains i = [.int idx])
    (he : avieEntry is idx = some j)
    (hfb : avbeFirstBad (slotEnum st.domains j)
      (fun b => valueMemB ((.bool b)) (slotEnum st.domains k)) = some b) :
    (∀ l r, avbeResEntry st i k j idx b = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.arrayVarBoolElementSlot is i k).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ cc, avbeResEntry st i k j idx b = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.arrayVarBoolElementSlot is i k).SatisfiedBy a → False) ∧
    (∀ cc, avbeResEntry st i k j idx b = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.arrayVarBoolElementSlot is i k).SatisfiedBy a →
        ∃ l ∈ cc, l.eval a = some true) := by
  unfold avbeResEntry
  exact implyBool_safe
    (fun a hfit hsat => avbe_entry_head hfit hidx hsat he hfb)
    (fun a hsat => avbeResEntry_entailed hsat he)
    (by simp)

theorem avbeResNoSupp_safe {st : State} {is : List Nat} {i k : Nat}
    {b : Bool}
    (hfb : avbeFirstBad (slotEnum st.domains k)
      (fun b => avbeTableMemB st is b) = some b) :
    (∀ l r, avbeResNoSupp st k is b = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.arrayVarBoolElementSlot is i k).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ cc, avbeResNoSupp st k is b = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.arrayVarBoolElementSlot is i k).SatisfiedBy a → False) ∧
    (∀ cc, avbeResNoSupp st k is b = .conflict cc →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.arrayVarBoolElementSlot is i k).SatisfiedBy a →
        ∃ l ∈ cc, l.eval a = some true) := by
  unfold avbeResNoSupp
  exact implyBool_safe
    (fun a hfit hsat => avbe_noSupp_head hfit hsat hfb)
    (fun a hsat => avbeResNoSupp_entailed hsat)
    (by simp)

end LeanFzn.Solver.Propagation

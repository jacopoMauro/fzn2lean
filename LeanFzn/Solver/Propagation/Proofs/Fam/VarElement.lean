/-
File: LeanFzn/Solver/Propagation/Proofs/Fam/VarElement.lean

Purpose:
  The LCG propagator and proof package for the variable-table element
  family `array_var_int_element` (`arrayVarIntElementSlot is i k`), the
  PLAN §3.3 item 1 dedicated propagator:

  * pinned index (`i`'s domain the raw int singleton `[.int idx]`): an
    out-of-range table position is the conflict `[i ≠ idx]`; otherwise
    the table slot `j = is[idx]` and the target `k` are filtered towards
    each other's domains (`k` loses values absent from `j`'s domain and
    vice versa), each removal escaping through the falsified pin
    `i ≠ idx`;
  * pinned target (`k`'s domain the raw int singleton `[.int v]`): every
    index whose table slot cannot read `v` (or is out of range) is
    removed through the falsified target `k ≠ v`;
  * unpinned index and target: every out-of-range index is removed by
    the unit clause `[i ≠ idx]`; an index whose table slot is separated
    from the target domain (singleton entry or disjoint interval hull)
    is removed through the two bound causes; and a target value missing
    from every table slot is removed by the clause
    `[k ≠ w, j₁ = w, …, jₙ = w]`.

  Every emission is over the existing literal vocabulary (`posNe` /
  `negNe` / `posLe` / `negLe`), its clause is CONSTRAINT-VALID under the
  `arrayVarIntElementSlot` constraint alone (the true-literals half of
  `Reason.Valid`), and each non-pivot cause is falsified by the state's
  own domain shape (`FixExpl` for raw int singletons,
  `BoundsExpl`/`HolesExpl` for the missing-value causes). Guards:
  aliasing `i = k`, `i` or `k` occurring in the table, a repeated table
  slot, and non-integer/empty/out-of-range slots are `.stable`.

Dependencies:
  - LeanFzn.Solver.Propagation.Proofs.Fam.Element: the shared
    `firstBadView` (transitively Fam.Bool) and the `domsIntOnlyB` guard
    (transitively Fam.Lin).

DAG:
  Fam.Element -> Fam.VarElement -> Proofs.Propagators
    (registration + safety triple) -> Reason / BoxPropagators / FallbackFit
    -> the Lcg* consumer arms.
-/

import LeanFzn.Solver.Propagation.Proofs.Fam.Element
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Reference


open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Reference

/-! ## PLAN §3.3: the variable-table element propagator -/

/-- 1-based access to the table slot list (the slot at position `idx`). -/
def avieEntry (is : List Nat) (idx : Int) : Option Nat :=
  if 0 < idx then is[idx.toNat - 1]? else none

/-- The entry slot at `idx`, when defined, is a table member. -/
theorem avieEntry_mem {is : List Nat} {idx : Int} {j : Nat}
    (h : avieEntry is idx = some j) : j ∈ is := by
  unfold avieEntry at h
  split at h
  · exact List.mem_of_getElem? h
  · cases h

/-- The entry equation unfolds to the 1-based `get?`. -/
theorem avieEntry_some_iff {is : List Nat} {idx : Int} {j : Nat} :
    avieEntry is idx = some j ↔ 0 < idx ∧ is[idx.toNat - 1]? = some j := by
  unfold avieEntry
  constructor
  · intro h
    split at h
    · exact ⟨‹0 < idx›, h⟩
    · cases h
  · rintro ⟨hpos, hget⟩
    rw [if_pos hpos]
    exact hget

/-- A defined table entry reads through to the mapped value list. -/
theorem avie_valuesGet1_of_entry {a : Assignment} {is : List Nat} {idx : Int}
    {j : Nat} {v : Value}
    (he : avieEntry is idx = some j) (hj : a[j]? = some v) :
    valuesGet1 (is.map (fun j => a[j]!)) idx = some v := by
  obtain ⟨hpos, hget⟩ := avieEntry_some_iff.mp he
  unfold valuesGet1
  rw [if_pos hpos]
  rw [List.getElem?_map, hget]
  simp only [Option.map_some]
  rw [List.getElem!_eq_getElem?_getD, hj]
  rfl

/-- A semantic read of the variable table is the entry slot's read. -/
theorem avie_entry_of_valuesGet1 {a : Assignment} {is : List Nat} {idx : Int}
    {v : Value}
    (hall : ∀ j ∈ is, ∃ u, a[j]? = some u)
    (h : valuesGet1 (is.map (fun j => a[j]!)) idx = some v) :
    ∃ j, avieEntry is idx = some j ∧ a[j]? = some v := by
  unfold valuesGet1 at h
  split at h
  · rename_i hpos
    rw [List.getElem?_map] at h
    cases hget : is[idx.toNat - 1]? with
    | none =>
        rw [hget] at h
        cases h
    | some j =>
        rw [hget] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨u, hu⟩ := hall j (List.mem_of_getElem? hget)
        have hju : a[j]! = u := by
          rw [List.getElem!_eq_getElem?_getD, hu]
          rfl
        have huv : u = v := by rw [← hju]; exact h
        exact ⟨j, avieEntry_some_iff.mpr ⟨hpos, hget⟩, by rw [hu, huv]⟩
  · cases h

/-- The `arrayVarIntElementSlot` semantics at the reads: the index, the
    target and the entry slot all read integers, and the entry slot's
    value is the target's value. -/
theorem arrayVarIntElement_views {a : Assignment} {is : List Nat} {i k : Nat}
    (h : (DomConstraint.arrayVarIntElementSlot is i k).SatisfiedBy a) :
    ∃ idx e : Int, ∃ js : Nat,
      a[i]? = some (.int idx) ∧ a[k]? = some (.int e) ∧
      avieEntry is idx = some js ∧ a[js]? = some (.int e) := by
  obtain ⟨idx, e, hi, hk, hall, hget⟩ := h
  obtain ⟨j, hent, hj⟩ := avie_entry_of_valuesGet1 hall hget
  exact ⟨idx, e, j, hi, hk, hent, hj⟩

/-! ### The keep tests and their inversions -/

/-- The index order literals at a fitting read. -/
theorem avie_posLe_eval_true {a : Assignment} {s : Nat} {v p : Int}
    (h : slotInt a s = some p) (hp : p ≤ v) :
    (posLe s v).eval a = some true :=
  (eval_posLe_iff a s v).mpr ⟨p, h, hp⟩

/-- The negative index order literals at a fitting read. -/
theorem avie_negLe_eval_true {a : Assignment} {s : Nat} {v p : Int}
    (h : slotInt a s = some p) (hp : v < p) :
    (negLe s v).eval a = some true :=
  (eval_negLe_iff a s v).mpr ⟨p, h, hp⟩

/-- A value missing from a domain cannot be read at a fitting solution. -/
theorem avie_fit_ne_of_not_mem {st : State} {a : Assignment} {s : Nat}
    {w : Int} (hfit : Core.Assignment.Fits st.domains a)
    (hread : a[s]? = some (.int w))
    (hvm : valueMemB ((.int w)) (slotEnum st.domains s) = false) : False := by
  have hmem : (.int w : Value) ∈ st.domains.getD s Dom.empty := hfit.2 s (.int w) hread
  have hmemE : (.int w : Value) ∈ slotEnum st.domains s := by
    simpa [slotEnum] using (DomainLike.mem_iff _ _).mp hmem
  have htrue : valueMemB ((.int w)) (slotEnum st.domains s) = true :=
    valueMemB_iff.mpr hmemE
  rw [hvm] at htrue
  cases htrue

/-! ### The emissions -/

/-- The pinned-index out-of-range conflict. -/
def avieResPinBad (i : Nat) (idx : Int) : PropagationResult :=
  .conflict [posNe i idx]

/-- The pinned-index target removal: `posNe k w`, the falsified pin
    `posNe i idx` and the falsified entry equality `negNe j w`. -/
def avieResK (i k j : Nat) (idx w : Int) : PropagationResult :=
  .implied (posNe k w) { clause := [posNe k w, posNe i idx, negNe j w] }

/-- The pinned-index entry removal: `posNe j w`, the falsified pin
    `posNe i idx` and the falsified target equality `negNe k w`. -/
def avieResJ (i k j : Nat) (idx w : Int) : PropagationResult :=
  .implied (posNe j w) { clause := [posNe j w, posNe i idx, negNe k w] }

/-- The pinned-target index removal through the falsified target
    `posNe k v` and the falsified entry equality `negNe j v`. -/
def avieResPinVal (i k j : Nat) (idx v : Int) : PropagationResult :=
  .implied (posNe i idx) { clause := [posNe i idx, posNe k v, negNe j v] }

/-- The out-of-range index removal: the unit clause `[posNe i idx]`. -/
def avieResOut (i : Nat) (idx : Int) : PropagationResult :=
  .implied (posNe i idx) { clause := [posNe i idx] }

/-- The separated singleton-entry removal: the falsified entry pin
    `posNe j w` and the falsified target equality `negNe k w`. -/
def avieResSingle (i k j : Nat) (idx w : Int) : PropagationResult :=
  .implied (posNe i idx) { clause := [posNe i idx, posNe j w, negNe k w] }

/-- The entry-hull-below-target removal: the entry's upper bound and the
    target's lower-bound predecessor. -/
def avieResBelow (i k j : Nat) (idx mx mn : Int) : PropagationResult :=
  .implied (posNe i idx) { clause := [posNe i idx, negLe j mx, posLe k (mn - 1)] }

/-- The target-hull-below-entry removal: the target's upper bound and the
    entry's lower-bound predecessor. -/
def avieResAbove (i k j : Nat) (idx mx mn : Int) : PropagationResult :=
  .implied (posNe i idx) { clause := [posNe i idx, negLe k mx, posLe j (mn - 1)] }

/-- The target value supported by no table slot: `posNe k w` with every
    table slot's `negNe j w` as the falsified causes. -/
def avieResNoSupp (k : Nat) (is : List Nat) (w : Int) : PropagationResult :=
  .implied (posNe k w) { clause := posNe k w :: is.map (fun j => negNe j w) }

/-- Does some table slot's domain contain `w`? -/
def avieTableMemB (st : State) (is : List Nat) (w : Int) : Bool :=
  is.any (fun j => valueMemB ((.int w)) (slotEnum st.domains j))

/-- `valueMemB` on an integer singleton enumeration is compact membership. -/
theorem valueMemB_int_slotEnum (doms : List Domain) (j : Nat) (w : Int) :
    valueMemB (Value.int w) (slotEnum doms j) =
      Dom.memBool (doms.getD j Dom.empty) (Value.int w) := by
  apply Bool.eq_iff_iff.mpr
  rw [valueMemB_iff, Dom.memBool_iff, slotEnum]

/-- Structural twin of `avieTableMemB`: test each table slot's compact
    membership instead of enumerating its domain. -/
def avieTableMemBFast (st : State) (is : List Nat) (w : Int) : Bool :=
  is.any (fun j => Dom.memBool (st.domains.getD j Dom.empty) (.int w))

theorem avieTableMemBFast_eq (st : State) (is : List Nat) (w : Int) :
    avieTableMemBFast st is w = avieTableMemB st is w := by
  unfold avieTableMemBFast avieTableMemB
  apply List.any_congr rfl
  intro j
  exact (valueMemB_int_slotEnum st.domains j w).symm

attribute [implemented_by avieTableMemBFast] avieTableMemB

/-- The table-membership scan over a materialised domain array.  A
    missing slot reads the empty domain, exactly as `slotEnum` does. -/
def avieTableMemArrB (a : Array Domain) (is : List Nat) (w : Int) : Bool :=
  is.any fun j =>
    Dom.memBool ((a[j]?).getD Dom.empty) (.int w)

theorem avieTableMemArrB_toArray_eq (st : State) (is : List Nat)
    (w : Int) :
    avieTableMemArrB st.domains.toArray is w = avieTableMemBFast st is w := by
  unfold avieTableMemArrB avieTableMemBFast
  apply List.any_congr rfl
  intro j
  rw [List.getElem?_toArray, ← List.getD_eq_getElem?_getD]

theorem avieTableMemArrB_eq (st : State) (is : List Nat) (w : Int) :
    avieTableMemArrB st.domains.toArray is w = avieTableMemB st is w := by
  rw [avieTableMemArrB_toArray_eq, avieTableMemBFast_eq]

/-! ### The pinned-target round -/

/-- The pinned-target round's keep test: the entry exists and can read the
    pinned target. -/
def aviePinTargetOkB (st : State) (is : List Nat) (idx : Int) (v : Int) :
    Bool :=
  match avieEntry is idx with
  | none => false
  | some j => valueMemB ((.int v)) (slotEnum st.domains j)

/-- Structural twin of the pinned-target keep test. -/
def aviePinTargetOkBFast (st : State) (is : List Nat) (idx : Int) (v : Int) :
    Bool :=
  match avieEntry is idx with
  | none => false
  | some j => Dom.memBool (st.domains.getD j Dom.empty) (.int v)

theorem aviePinTargetOkBFast_eq (st : State) (is : List Nat) (idx : Int)
    (v : Int) :
    aviePinTargetOkBFast st is idx v = aviePinTargetOkB st is idx v := by
  unfold aviePinTargetOkBFast aviePinTargetOkB
  cases h : avieEntry is idx with
  | none => rfl
  | some j =>
      simp only [h]
      exact (valueMemB_int_slotEnum st.domains j v).symm

attribute [implemented_by aviePinTargetOkBFast] aviePinTargetOkB

/-- The pinned-target round's response: the unit out-of-range removal, the
    supported `.stable`, or the entry-equality removal. -/
def aviePinTargetRes (st : State) (is : List Nat) (i k : Nat) (idx : Int)
    (v : Int) : PropagationResult :=
  match avieEntry is idx with
  | none => avieResOut i idx
  | some j =>
      if valueMemB ((.int v)) (slotEnum st.domains j) then .stable
      else avieResPinVal i k j idx v

/-- Structural twin of the pinned-target response. -/
def aviePinTargetResFast (st : State) (is : List Nat) (i k : Nat) (idx : Int)
    (v : Int) : PropagationResult :=
  match avieEntry is idx with
  | none => avieResOut i idx
  | some j =>
      if Dom.memBool (st.domains.getD j Dom.empty) (.int v) then .stable
      else avieResPinVal i k j idx v

theorem aviePinTargetResFast_eq (st : State) (is : List Nat) (i k : Nat)
    (idx : Int) (v : Int) :
    aviePinTargetResFast st is i k idx v = aviePinTargetRes st is i k idx v := by
  unfold aviePinTargetResFast aviePinTargetRes
  cases h : avieEntry is idx with
  | none => rfl
  | some j =>
      simp only [h]
      rw [valueMemB_int_slotEnum]

attribute [implemented_by aviePinTargetResFast] aviePinTargetRes

/-- A failed pinned-target keep test is an out-of-range index or an entry
    slot that cannot read the target. -/
theorem aviePinTargetRes_of_bad {st : State} {is : List Nat} {i k : Nat}
    {idx : Int} {v : Int}
    (hbad : aviePinTargetOkB st is idx v = false) :
    (avieEntry is idx = none ∧
      aviePinTargetRes st is i k idx v = avieResOut i idx) ∨
    (∃ j : Nat, avieEntry is idx = some j ∧
      valueMemB ((.int v)) (slotEnum st.domains j) = false ∧
      aviePinTargetRes st is i k idx v = avieResPinVal i k j idx v) := by
  unfold aviePinTargetOkB at hbad
  split at hbad
  · next hnone =>
      left
      exact ⟨hnone, by unfold aviePinTargetRes; rw [hnone]⟩
  · next j hent =>
      right
      refine ⟨j, hent, hbad, ?_⟩
      unfold aviePinTargetRes
      rw [hent]
      dsimp only
      rw [hbad]
      rfl

/-! ### The unpinned separation rounds -/

/-- The below-hull pair: the entry maximum and the target minimum when
    strictly ordered. -/
def avieBelowPair (dj dk : Domain) : Option (Int × Int) :=
  match domMaxI dj with
  | none => none
  | some mx =>
      match domMinI dk with
      | none => none
      | some mn => if mx < mn then some (mx, mn) else none

/-- The above-hull pair: the target maximum and the entry minimum when
    strictly ordered. -/
def avieAbovePair (dj dk : Domain) : Option (Int × Int) :=
  match domMaxI dk with
  | none => none
  | some mx =>
      match domMinI dj with
      | none => none
      | some mn => if mx < mn then some (mx, mn) else none

/-- Structural twin of `avieBelowPair`: read the compact bounds. -/
def avieBelowPairFast (dj dk : Domain) : Option (Int × Int) :=
  match dj.maxInt? with
  | none => none
  | some mx =>
      match dk.minInt? with
      | none => none
      | some mn => if mx < mn then some (mx, mn) else none

theorem avieBelowPairFast_eq (dj dk : Domain) :
    avieBelowPairFast dj dk = avieBelowPair dj dk := by
  unfold avieBelowPairFast avieBelowPair
  rw [maxInt?_eq_domMaxI, minInt?_eq_domMinI]

attribute [implemented_by avieBelowPairFast] avieBelowPair

/-- Structural twin of `avieAbovePair`: read the compact bounds. -/
def avieAbovePairFast (dj dk : Domain) : Option (Int × Int) :=
  match dk.maxInt? with
  | none => none
  | some mx =>
      match dj.minInt? with
      | none => none
      | some mn => if mx < mn then some (mx, mn) else none

theorem avieAbovePairFast_eq (dj dk : Domain) :
    avieAbovePairFast dj dk = avieAbovePair dj dk := by
  unfold avieAbovePairFast avieAbovePair
  rw [maxInt?_eq_domMaxI, minInt?_eq_domMinI]

attribute [implemented_by avieAbovePairFast] avieAbovePair

/-- The unique value of a raw integer singleton. -/
def avieSingleW (dj : Domain) : Option Int :=
  match Dom.enum dj with
  | [.int w] => some w
  | _ => none

/-- Structural twin of `avieSingleW`: read the compact singleton tag
    instead of materialising the enumeration. -/
def avieSingleWFast (dj : Domain) : Option Int :=
  dj.intSingleton?

theorem avieSingleWFast_eq (dj : Domain) : avieSingleWFast dj = avieSingleW dj := by
  unfold avieSingleWFast avieSingleW
  rw [Dom.intSingleton?_eq]
  cases h : Dom.enum dj with
  | nil => rfl
  | cons x xs => cases x <;> cases xs <;> rfl

attribute [implemented_by avieSingleWFast] avieSingleW

/-- A pair hit exposes the two extrema and their strict order. -/
theorem avieBelowPair_spec {dj dk : Domain} {mx mn : Int}
    (h : avieBelowPair dj dk = some (mx, mn)) :
    domMaxI dj = some mx ∧ domMinI dk = some mn ∧ mx < mn := by
  unfold avieBelowPair at h
  split at h
  · cases h
  · next mx' hmx =>
      split at h
      · cases h
      · next mn' hmn =>
          split at h
          · next hlt =>
              injection h with h1
              have h1' : mx' = mx ∧ mn' = mn := by
                simpa using h1
              exact ⟨hmx.trans (congrArg some h1'.1),
                hmn.trans (congrArg some h1'.2),
                by rw [← h1'.1, ← h1'.2]; exact hlt⟩
          · next => cases h

/-- A pair hit exposes the two extrema and their strict order. -/
theorem avieAbovePair_spec {dj dk : Domain} {mx mn : Int}
    (h : avieAbovePair dj dk = some (mx, mn)) :
    domMaxI dk = some mx ∧ domMinI dj = some mn ∧ mx < mn := by
  unfold avieAbovePair at h
  split at h
  · cases h
  · next mx' hmx =>
      split at h
      · cases h
      · next mn' hmn =>
          split at h
          · next hlt =>
              injection h with h1
              have h1' : mx' = mx ∧ mn' = mn := by
                simpa using h1
              exact ⟨hmx.trans (congrArg some h1'.1),
                hmn.trans (congrArg some h1'.2),
                by rw [← h1'.1, ← h1'.2]; exact hlt⟩
          · next => cases h

/-- A singleton-value hit identifies the raw singleton. -/
theorem avieSingleW_spec {dj : Domain} {w : Int}
    (h : avieSingleW dj = some w) : Dom.enum dj = [.int w] := by
  unfold avieSingleW at h
  split at h
  · rename_i heq
    injection h with h1
    rw [← h1]
    exact heq
  · cases h

/-- The entry hull is strictly below the target hull. -/
def avieBelowBadB (st : State) (is : List Nat) (idx : Int) (k : Nat) : Bool :=
  match avieEntry is idx with
  | none => false
  | some j => (avieBelowPair (st.domains.getD j Dom.empty)
      (st.domains.getD k Dom.empty)).isSome

/-- Structural twin of `avieBelowBadB` with the compact pair test spelled
    out (the small reference definition is inlined at its call sites, so the
    twin must name the fast pair explicitly). -/
def avieBelowBadBFast (st : State) (is : List Nat) (idx : Int) (k : Nat) :
    Bool :=
  match avieEntry is idx with
  | none => false
  | some j => (avieBelowPairFast (st.domains.getD j Dom.empty)
      (st.domains.getD k Dom.empty)).isSome

theorem avieBelowBadBFast_eq (st : State) (is : List Nat) (idx : Int)
    (k : Nat) :
    avieBelowBadBFast st is idx k = avieBelowBadB st is idx k := by
  unfold avieBelowBadBFast avieBelowBadB
  cases h : avieEntry is idx with
  | none => rfl
  | some j => simp only [h]; rw [avieBelowPairFast_eq]

/-- The below-hull response. -/
def avieBelowRes (st : State) (is : List Nat) (i k : Nat) (idx : Int) :
    PropagationResult :=
  match avieEntry is idx with
  | none => .stable
  | some j =>
      match avieBelowPair (st.domains.getD j Dom.empty)
          (st.domains.getD k Dom.empty) with
      | some p => avieResBelow i k j idx p.1 p.2
      | none => .stable

/-- A hit of the below-hull round exposes the entry slot and both hull
    extrema. -/
theorem avieBelowRes_of_bad {st : State} {is : List Nat} {i k : Nat} {idx : Int}
    (hbad : avieBelowBadB st is idx k = true) :
    ∃ j : Nat, ∃ mx : Int, ∃ mn : Int,
      avieEntry is idx = some j ∧
      domMaxI (st.domains.getD j Dom.empty) = some mx ∧
      domMinI (st.domains.getD k Dom.empty) = some mn ∧ mx < mn ∧
      avieBelowRes st is i k idx = avieResBelow i k j idx mx mn := by
  unfold avieBelowBadB at hbad
  split at hbad
  · cases hbad
  · next j hent =>
      cases hpair : avieBelowPair (st.domains.getD j Dom.empty)
          (st.domains.getD k Dom.empty) with
      | none =>
          rw [hpair] at hbad
          cases hbad
      | some p =>
          obtain ⟨mx, mn⟩ := p
          rw [hpair] at hbad
          have hspec := avieBelowPair_spec hpair
          refine ⟨j, mx, mn, hent, hspec.1, hspec.2.1, hspec.2.2, ?_⟩
          unfold avieBelowRes
          rw [hent]
          dsimp only
          rw [hpair]

/-- The target hull is strictly below the entry hull. -/
def avieAboveBadB (st : State) (is : List Nat) (idx : Int) (k : Nat) : Bool :=
  match avieEntry is idx with
  | none => false
  | some j => (avieAbovePair (st.domains.getD j Dom.empty)
      (st.domains.getD k Dom.empty)).isSome

/-- Structural twin of `avieAboveBadB`. -/
def avieAboveBadBFast (st : State) (is : List Nat) (idx : Int) (k : Nat) :
    Bool :=
  match avieEntry is idx with
  | none => false
  | some j => (avieAbovePairFast (st.domains.getD j Dom.empty)
      (st.domains.getD k Dom.empty)).isSome

theorem avieAboveBadBFast_eq (st : State) (is : List Nat) (idx : Int)
    (k : Nat) :
    avieAboveBadBFast st is idx k = avieAboveBadB st is idx k := by
  unfold avieAboveBadBFast avieAboveBadB
  cases h : avieEntry is idx with
  | none => rfl
  | some j => simp only [h]; rw [avieAbovePairFast_eq]

/-- The above-hull response. -/
def avieAboveRes (st : State) (is : List Nat) (i k : Nat) (idx : Int) :
    PropagationResult :=
  match avieEntry is idx with
  | none => .stable
  | some j =>
      match avieAbovePair (st.domains.getD j Dom.empty)
          (st.domains.getD k Dom.empty) with
      | some p => avieResAbove i k j idx p.1 p.2
      | none => .stable

/-- A hit of the above-hull round exposes the entry slot and both hull
    extrema. -/
theorem avieAboveRes_of_bad {st : State} {is : List Nat} {i k : Nat} {idx : Int}
    (hbad : avieAboveBadB st is idx k = true) :
    ∃ j : Nat, ∃ mx : Int, ∃ mn : Int,
      avieEntry is idx = some j ∧
      domMaxI (st.domains.getD k Dom.empty) = some mx ∧
      domMinI (st.domains.getD j Dom.empty) = some mn ∧ mx < mn ∧
      avieAboveRes st is i k idx = avieResAbove i k j idx mx mn := by
  unfold avieAboveBadB at hbad
  split at hbad
  · cases hbad
  · next j hent =>
      cases hpair : avieAbovePair (st.domains.getD j Dom.empty)
          (st.domains.getD k Dom.empty) with
      | none =>
          rw [hpair] at hbad
          cases hbad
      | some p =>
          obtain ⟨mx, mn⟩ := p
          rw [hpair] at hbad
          have hspec := avieAbovePair_spec hpair
          refine ⟨j, mx, mn, hent, hspec.1, hspec.2.1, hspec.2.2, ?_⟩
          unfold avieAboveRes
          rw [hent]
          dsimp only
          rw [hpair]

/-- A singleton entry whose value is absent from the target domain. -/
def avieSingleBadB (st : State) (is : List Nat) (idx : Int) (k : Nat) : Bool :=
  match avieEntry is idx with
  | none => false
  | some j =>
      match avieSingleW (st.domains.getD j Dom.empty) with
      | none => false
      | some w => !valueMemB ((.int w)) (slotEnum st.domains k)

/-- Structural twin of `avieSingleBadB`. -/
def avieSingleBadBFast (st : State) (is : List Nat) (idx : Int) (k : Nat) : Bool :=
  match avieEntry is idx with
  | none => false
  | some j =>
      match avieSingleW (st.domains.getD j Dom.empty) with
      | none => false
      | some w => !Dom.memBool (st.domains.getD k Dom.empty) (.int w)

theorem avieSingleBadBFast_eq (st : State) (is : List Nat) (idx : Int)
    (k : Nat) :
    avieSingleBadBFast st is idx k = avieSingleBadB st is idx k := by
  unfold avieSingleBadBFast avieSingleBadB
  cases h : avieEntry is idx with
  | none => rfl
  | some j =>
      simp only [h]
      cases hw : avieSingleW (st.domains.getD j Dom.empty) <;>
        simp only [hw, valueMemB_int_slotEnum]

attribute [implemented_by avieSingleBadBFast] avieSingleBadB

/-- The singleton-entry separation response. -/
def avieSingleRes (st : State) (is : List Nat) (i k : Nat) (idx : Int) :
    PropagationResult :=
  match avieEntry is idx with
  | none => .stable
  | some j =>
      match avieSingleW (st.domains.getD j Dom.empty) with
      | none => .stable
      | some w =>
          if valueMemB ((.int w)) (slotEnum st.domains k) then .stable
          else avieResSingle i k j idx w

/-- A hit of the singleton-entry round exposes the entry slot and its
    value. -/
theorem avieSingleRes_of_bad {st : State} {is : List Nat} {i k : Nat}
    {idx : Int} (hbad : avieSingleBadB st is idx k = true) :
    ∃ j : Nat, ∃ w : Int,
      avieEntry is idx = some j ∧
      slotEnum st.domains j = [.int w] ∧
      valueMemB ((.int w)) (slotEnum st.domains k) = false ∧
      avieSingleRes st is i k idx = avieResSingle i k j idx w := by
  unfold avieSingleBadB at hbad
  split at hbad
  · cases hbad
  · next j hent =>
      cases hw : avieSingleW (st.domains.getD j Dom.empty) with
      | none =>
          rw [hw] at hbad
          cases hbad
      | some w =>
          have hdj := avieSingleW_spec hw
          have hnot : valueMemB ((.int w)) (slotEnum st.domains k) = false := by
            rw [hw] at hbad
            dsimp only at hbad
            simpa using hbad
          refine ⟨j, w, hent, hdj, hnot, ?_⟩
          unfold avieSingleRes
          rw [hent]
          dsimp only
          rw [hw]
          dsimp only
          rw [hnot]
          rfl

/-- PLAN §3.3: the explained propagator of `array_var_int_element` —
    `arrayVarIntElementSlot is i k` (the table slots `is`; `i` the
    1-based index slot, `k` the element slot). Guarded rounds, in order:

    * aliasing (`i = k`), the index or target occurring in the table, a
      repeated table slot, and non-integer/empty/out-of-range slots ⇒
      `.stable`;
    * pinned index `[.int idx]`: an out-of-range position is the conflict
      `[i ≠ idx]`; otherwise the target loses the first value absent from
      the entry slot's domain, then the entry slot loses the first value
      absent from the target domain (both escaping through `i ≠ idx`);
    * pinned target `[.int v]`: removes the first index whose table slot
      cannot read `v` or is out of range (through the falsified `k ≠ v`);
    * unpinned index: removes the first out-of-range index by the unit
      `posNe i idx`, then the first index whose entry hull is separated
      from the target hull (below, above, or a singleton entry value
      absent from the target); if no hull is separated, removes the
      first target value absent from every table slot.

    Every emission's clause is over the existing vocabulary: `posNe` /
    `negNe` value-removal literals and `posLe` / `negLe` order literals
    on the index, target and table slots. -/
def propArrayVarIntElement (st : State) (is : List Nat) (i k : Nat) :
    PropagationResult :=
  if i = k then .stable
  else if is.elem i || is.elem k then .stable
  else if decide is.Nodup = false then .stable
  else if domsIntOnlyB st.domains (i :: k :: is) = false then .stable
  else
    match slotEnum st.domains i with
    | [.int idx] =>
        match avieEntry is idx with
        | none => avieResPinBad i idx
        | some j =>
            match firstBadView (slotEnum st.domains k)
                (fun w => valueMemB ((.int w)) (slotEnum st.domains j)) with
            | some w => avieResK i k j idx w
            | none =>
                match firstBadView (slotEnum st.domains j)
                    (fun w => valueMemB ((.int w)) (slotEnum st.domains k)) with
                | some w => avieResJ i k j idx w
                | none => .stable
    | _ =>
        match slotEnum st.domains k with
        | [.int v] =>
            match firstBadView (slotEnum st.domains i)
                (fun idx => aviePinTargetOkB st is idx v) with
            | some idx => aviePinTargetRes st is i k idx v
            | none => .stable
        | _ =>
            match firstBadView (slotEnum st.domains i)
                (fun idx => (avieEntry is idx).isSome) with
            | some idx => avieResOut i idx
            | none =>
                match firstBadView (slotEnum st.domains i)
                    (fun idx => !avieBelowBadB st is idx k) with
                | some idx => avieBelowRes st is i k idx
                | none =>
                    match firstBadView (slotEnum st.domains i)
                        (fun idx => !avieAboveBadB st is idx k) with
                    | some idx => avieAboveRes st is i k idx
                    | none =>
                        match firstBadView (slotEnum st.domains i)
                            (fun idx => !avieSingleBadB st is idx k) with
                        | some idx => avieSingleRes st is i k idx
                        | none =>
                            match firstBadView (slotEnum st.domains k)
                                (fun w => avieTableMemB st is w) with
                            | some w => avieResNoSupp k is w
                            | none => .stable

/-- `firstBadView` only depends on its keep test pointwise. -/
theorem firstBadView_congr {k₁ k₂ : Int → Bool}
    (h : ∀ w, k₁ w = k₂ w) :
    ∀ d : List Value, firstBadView d k₁ = firstBadView d k₂
  | [] => rfl
  | v :: vs => by
      show (v :: vs).findSome?
          (fun v => (Value.intView v).bind
            fun w => if k₁ w then none else some w) =
        (v :: vs).findSome?
          (fun v => (Value.intView v).bind
            fun w => if k₂ w then none else some w)
      simp only [List.findSome?_cons]
      cases hv : Value.intView v with
      | none =>
          simp only [hv, Option.bind_none]
          exact firstBadView_congr h vs
      | some u =>
          simp only [hv, Option.bind_some]
          rw [h u]
          by_cases hk : k₂ u = true
          · simp only [hk, if_true]
            exact firstBadView_congr h vs
          · simp [hk]

/-- Runtime twin of `propArrayVarIntElement`: the same rounds on one
    materialisation of each slot's enumeration, with the integer-only
    guard answered structurally. The logical body stays the reference
    definition; the `@[implemented_by]` seam below swaps compiled calls. -/
def propArrayVarIntElementFast (st : State) (is : List Nat) (i k : Nat) :
    PropagationResult :=
  if i = k then .stable
  else if is.elem i || is.elem k then .stable
  else if decide is.Nodup = false then .stable
  else if domsIntOnlyBFast st.domains (i :: k :: is) = false then .stable
  else
    let di := slotEnum st.domains i
    let dk := slotEnum st.domains k
    match di with
    | [.int idx] =>
        match avieEntry is idx with
        | none => avieResPinBad i idx
        | some j =>
            let dj := slotEnum st.domains j
            match firstBadView dk
                (fun w => valueMemB ((.int w)) dj) with
            | some w => avieResK i k j idx w
            | none =>
                match firstBadView dj
                    (fun w => valueMemB ((.int w)) dk) with
                | some w => avieResJ i k j idx w
                | none => .stable
    | _ =>
        match dk with
        | [.int v] =>
            match firstBadView di
                (fun idx => aviePinTargetOkBFast st is idx v) with
            | some idx => aviePinTargetResFast st is i k idx v
            | none => .stable
        | _ =>
            match firstBadView di
                (fun idx => (avieEntry is idx).isSome) with
            | some idx => avieResOut i idx
            | none =>
                match firstBadView di
                    (fun idx => !avieBelowBadBFast st is idx k) with
                | some idx => avieBelowRes st is i k idx
                | none =>
                    match firstBadView di
                        (fun idx => !avieAboveBadBFast st is idx k) with
                    | some idx => avieAboveRes st is i k idx
                    | none =>
                        match firstBadView di
                            (fun idx => !avieSingleBadBFast st is idx k) with
                        | some idx => avieSingleRes st is i k idx
                        | none =>
                            let da := st.domains.toArray
                            match firstBadView dk
                                (fun w => avieTableMemArrB da is w) with
                            | some w => avieResNoSupp k is w
                            | none => .stable

theorem propArrayVarIntElementFast_eq (st : State) (is : List Nat)
    (i k : Nat) :
    propArrayVarIntElementFast st is i k =
      propArrayVarIntElement st is i k := by
  unfold propArrayVarIntElementFast propArrayVarIntElement
  dsimp only
  simp only [domsIntOnlyBFast_eq, aviePinTargetOkBFast_eq,
    aviePinTargetResFast_eq, avieBelowBadBFast_eq, avieAboveBadBFast_eq,
    avieSingleBadBFast_eq, avieTableMemBFast_eq,
    avieTableMemArrB_toArray_eq]

attribute [implemented_by propArrayVarIntElementFast]
  propArrayVarIntElement

/-- A failed `isSome` keep test is a missing entry. -/
theorem avie_entry_none_of_isSome_false {is : List Nat} {idx : Int}
    (h : (avieEntry is idx).isSome = false) : avieEntry is idx = none := by
  cases hv : avieEntry is idx with
  | none => rfl
  | some j => rw [hv] at h; cases h

/-- A `firstBadView` hit fails its keep test. -/
theorem avie_firstBadView_false {d : List Value} {keep : Int → Bool} {w : Int}
    (h : firstBadView d keep = some w) : keep w = false := by
  obtain ⟨-, -, -, hk⟩ := firstBadView_some h
  exact hk

/-- Complete case split of `propArrayVarIntElement`: `.stable`, the
    pinned-index out-of-range conflict, the pinned-index target/entry
    removals, the pinned-target index removals (out-of-range or missing
    entry value), the unpinned out-of-range unit removal, the separated
    entry removals, or the no-support target removal. -/
theorem propArrayVarIntElement_cases (st : State) (is : List Nat) (i k : Nat) :
    propArrayVarIntElement st is i k = .stable ∨
    (∃ idx : Int, slotEnum st.domains i = [.int idx] ∧
      avieEntry is idx = none ∧
      propArrayVarIntElement st is i k = avieResPinBad i idx) ∨
    (∃ idx : Int, ∃ j : Nat, ∃ w : Int,
      slotEnum st.domains i = [.int idx] ∧ avieEntry is idx = some j ∧
      firstBadView (slotEnum st.domains k)
        (fun w => valueMemB ((.int w)) (slotEnum st.domains j)) = some w ∧
      propArrayVarIntElement st is i k = avieResK i k j idx w) ∨
    (∃ idx : Int, ∃ j : Nat, ∃ w : Int,
      slotEnum st.domains i = [.int idx] ∧ avieEntry is idx = some j ∧
      firstBadView (slotEnum st.domains k)
        (fun w => valueMemB ((.int w)) (slotEnum st.domains j)) = none ∧
      firstBadView (slotEnum st.domains j)
        (fun w => valueMemB ((.int w)) (slotEnum st.domains k)) = some w ∧
      propArrayVarIntElement st is i k = avieResJ i k j idx w) ∨
    (∃ idx : Int, ∃ v : Int, slotEnum st.domains k = [.int v] ∧
      avieEntry is idx = none ∧
      firstBadView (slotEnum st.domains i)
        (fun idx => aviePinTargetOkB st is idx v) = some idx ∧
      propArrayVarIntElement st is i k = avieResOut i idx) ∨
    (∃ idx : Int, ∃ v : Int, ∃ j : Nat,
      slotEnum st.domains k = [.int v] ∧ avieEntry is idx = some j ∧
      valueMemB ((.int v)) (slotEnum st.domains j) = false ∧
      firstBadView (slotEnum st.domains i)
        (fun idx => aviePinTargetOkB st is idx v) = some idx ∧
      propArrayVarIntElement st is i k = avieResPinVal i k j idx v) ∨
    (∃ idx : Int, avieEntry is idx = none ∧
      firstBadView (slotEnum st.domains i)
        (fun idx => (avieEntry is idx).isSome) = some idx ∧
      propArrayVarIntElement st is i k = avieResOut i idx) ∨
    (∃ idx : Int, ∃ j : Nat, ∃ mx : Int, ∃ mn : Int,
      avieEntry is idx = some j ∧
      domMaxI (st.domains.getD j Dom.empty) = some mx ∧
      domMinI (st.domains.getD k Dom.empty) = some mn ∧ mx < mn ∧
      firstBadView (slotEnum st.domains i)
        (fun idx => !avieBelowBadB st is idx k) = some idx ∧
      propArrayVarIntElement st is i k = avieResBelow i k j idx mx mn) ∨
    (∃ idx : Int, ∃ j : Nat, ∃ mx : Int, ∃ mn : Int,
      avieEntry is idx = some j ∧
      domMaxI (st.domains.getD k Dom.empty) = some mx ∧
      domMinI (st.domains.getD j Dom.empty) = some mn ∧ mx < mn ∧
      firstBadView (slotEnum st.domains i)
        (fun idx => !avieAboveBadB st is idx k) = some idx ∧
      propArrayVarIntElement st is i k = avieResAbove i k j idx mx mn) ∨
    (∃ idx : Int, ∃ j : Nat, ∃ w : Int,
      avieEntry is idx = some j ∧
      slotEnum st.domains j = [.int w] ∧
      valueMemB ((.int w)) (slotEnum st.domains k) = false ∧
      firstBadView (slotEnum st.domains i)
        (fun idx => !avieSingleBadB st is idx k) = some idx ∧
      propArrayVarIntElement st is i k = avieResSingle i k j idx w) ∨
    (∃ w : Int,
      firstBadView (slotEnum st.domains i)
        (fun idx => (avieEntry is idx).isSome) = none ∧
      firstBadView (slotEnum st.domains i)
        (fun idx => !avieBelowBadB st is idx k) = none ∧
      firstBadView (slotEnum st.domains i)
        (fun idx => !avieAboveBadB st is idx k) = none ∧
      firstBadView (slotEnum st.domains i)
        (fun idx => !avieSingleBadB st is idx k) = none ∧
      firstBadView (slotEnum st.domains k)
        (fun w => avieTableMemB st is w) = some w ∧
      propArrayVarIntElement st is i k = avieResNoSupp k is w) := by
  unfold propArrayVarIntElement
  by_cases halias : i = k
  · rw [if_pos halias]; exact Or.inl rfl
  · rw [if_neg halias]
    by_cases htab : (is.elem i || is.elem k) = true
    · rw [if_pos htab]; exact Or.inl rfl
    · rw [if_neg htab]
      by_cases hnodup : decide is.Nodup = false
      · rw [if_pos hnodup]; exact Or.inl rfl
      · rw [if_neg hnodup]
        by_cases hint : domsIntOnlyB st.domains (i :: k :: is) = false
        · rw [if_pos hint]; exact Or.inl rfl
        · rw [if_neg hint]
          split
          · next idx hidx =>
            split
            · next hnone =>
                iterate 1 (apply Or.inr)
                left
                exact ⟨idx, hidx, hnone, rfl⟩
            · next j hent =>
                split
                · next w hfb =>
                    iterate 2 (apply Or.inr)
                    left
                    exact ⟨idx, j, w, hidx, hent, hfb, rfl⟩
                · next hfbK =>
                    split
                    · next w hfbJ =>
                        iterate 3 (apply Or.inr)
                        left
                        exact ⟨idx, j, w, hidx, hent, hfbK, hfbJ, rfl⟩
                    · next => exact Or.inl rfl
          · next =>
            split
            · next v hk =>
                split
                · next idx hfb =>
                    have hbad : aviePinTargetOkB st is idx v = false :=
                      avie_firstBadView_false
                        (d := slotEnum st.domains i)
                        (keep := fun idx => aviePinTargetOkB st is idx v)
                        (w := idx) hfb
                    rcases aviePinTargetRes_of_bad hbad with
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
                        have hbad : avieBelowBadB st is idx k = true := by
                          have hk := avie_firstBadView_false
                            (d := slotEnum st.domains i)
                            (keep := fun idx => !avieBelowBadB st is idx k)
                            (w := idx) hfb
                          simpa using hk
                        rcases avieBelowRes_of_bad hbad with
                          ⟨j, mx, mn, hent, hmx, hmn, hlt, hres⟩
                        iterate 7 (apply Or.inr)
                        left
                        exact ⟨idx, j, mx, mn, hent, hmx, hmn, hlt, hfb, hres⟩
                    · next hfbBelow =>
                        split
                        · next idx hfb =>
                            have hbad : avieAboveBadB st is idx k = true := by
                              have hk := avie_firstBadView_false
                                (d := slotEnum st.domains i)
                                (keep := fun idx => !avieAboveBadB st is idx k)
                                (w := idx) hfb
                              simpa using hk
                            rcases avieAboveRes_of_bad hbad with
                              ⟨j, mx, mn, hent, hmx, hmn, hlt, hres⟩
                            iterate 8 (apply Or.inr)
                            left
                            exact ⟨idx, j, mx, mn, hent, hmx, hmn, hlt, hfb, hres⟩
                        · next hfbAbove =>
                            split
                            · next idx hfb =>
                                have hbad : avieSingleBadB st is idx k = true := by
                                  have hk := avie_firstBadView_false
                                    (d := slotEnum st.domains i)
                                    (keep := fun idx => !avieSingleBadB st is idx k)
                                    (w := idx) hfb
                                  simpa using hk
                                rcases avieSingleRes_of_bad hbad with
                                  ⟨j, w, hent, hdj, hmem, hres⟩
                                iterate 9 (apply Or.inr)
                                left
                                exact ⟨idx, j, w, hent, hdj, hmem, hfb, hres⟩
                            · next hfbSingle =>
                                split
                                · next w hfbw =>
                                    iterate 10 (apply Or.inr)
                                    exact ⟨w, hfbOut, hfbBelow, hfbAbove,
                                      hfbSingle, hfbw, rfl⟩
                                · next => exact Or.inl rfl

/-! ### The constraint's reads -/

/-- With the index read at `idx`, the target and the entry slot read the
    same integer. -/
theorem avie_entry_reads {a : Assignment} {is : List Nat} {i k : Nat}
    {idx : Int} {j : Nat}
    (h : (DomConstraint.arrayVarIntElementSlot is i k).SatisfiedBy a)
    (hi : a[i]? = some (.int idx))
    (he : avieEntry is idx = some j) :
    ∃ e : Int, a[k]? = some (.int e) ∧ a[j]? = some (.int e) := by
  obtain ⟨idx', e, j', hi', hk, hent', hj'⟩ := arrayVarIntElement_views h
  have hidx' : idx' = idx :=
    Value.int.inj (Option.some.inj (hi'.symm.trans hi))
  rw [hidx'] at hent'
  have hjj : j' = j := Option.some.inj (hent'.symm.trans he)
  rw [hjj] at hj'
  exact ⟨e, hk, hj'⟩

/-- A value missing from a domain cannot occur in a fitting read. -/
theorem avie_not_mem_of_fit {st : State} {a : Assignment} {s : Nat} {w : Int}
    (hfit : Core.Assignment.Fits st.domains a)
    (hread : a[s]? = some (.int w))
    (hvm : valueMemB ((.int w)) (slotEnum st.domains s) = false) : False := by
  have hmem : (.int w : Value) ∈ st.domains.getD s Dom.empty :=
    hfit.2 s (.int w) hread
  have hmemE : (.int w : Value) ∈ slotEnum st.domains s := by
    simpa [slotEnum] using (DomainLike.mem_iff _ _).mp hmem
  have htrue : valueMemB ((.int w)) (slotEnum st.domains s) = true :=
    valueMemB_iff.mpr hmemE
  rw [hvm] at htrue
  cases htrue

/-- The table-membership test is false on every table slot. -/
theorem avieTableMemB_false {st : State} {is : List Nat} {w : Int} {j : Nat}
    (h : avieTableMemB st is w = false) (hj : j ∈ is) :
    valueMemB ((.int w)) (slotEnum st.domains j) = false := by
  unfold avieTableMemB at h
  exact Bool.eq_false_iff.mpr (List.any_eq_false.mp h j hj)

/-! ### Clause entailment at solutions (the reason side) -/

/-- The out-of-range clause carries a true literal at every solution. -/
theorem avieResOut_entailed {a : Assignment} {is : List Nat} {i k : Nat}
    {idx : Int}
    (h : (DomConstraint.arrayVarIntElementSlot is i k).SatisfiedBy a)
    (hnone : avieEntry is idx = none) :
    ∃ l ∈ [posNe i idx], l.eval a = some true := by
  obtain ⟨idx', e, j', hi, hk, hent', hj'⟩ := arrayVarIntElement_views h
  by_cases hidx : idx' = idx
  · rw [hidx] at hent'
    rw [hent'] at hnone
    cases hnone
  · exact ⟨posNe i idx, List.mem_singleton_self _,
      aie_posNe_eval_true (slotInt_of_int_read hi) hidx⟩

/-- The pinned-index target removal's clause carries a true literal. -/
theorem avieResK_entailed {a : Assignment} {is : List Nat} {i k : Nat}
    {idx : Int} {j : Nat} {w : Int}
    (h : (DomConstraint.arrayVarIntElementSlot is i k).SatisfiedBy a)
    (he : avieEntry is idx = some j) :
    ∃ l ∈ [posNe k w, posNe i idx, negNe j w], l.eval a = some true := by
  by_cases hpin : a[i]? = some (.int idx)
  · obtain ⟨e, hk, hj⟩ := avie_entry_reads h hpin he
    by_cases hew : e = w
    · exact ⟨negNe j w,
        List.mem_cons_of_mem (posNe k w)
          (List.mem_cons_of_mem (posNe i idx)
            (List.mem_singleton_self (negNe j w))),
        aie_negNe_eval_true (slotInt_of_int_read hj) hew⟩
    · exact ⟨posNe k w, List.mem_cons_self,
        aie_posNe_eval_true (slotInt_of_int_read hk) hew⟩
  · obtain ⟨idx', e', j', hi, hk', hent', hj'⟩ := arrayVarIntElement_views h
    have hne : idx' ≠ idx := by
      intro hidx
      apply hpin
      rw [hidx] at hi
      exact hi
    exact ⟨posNe i idx,
      List.mem_cons_of_mem (posNe k w) (List.mem_cons_self),
      aie_posNe_eval_true (slotInt_of_int_read hi) hne⟩

/-- The pinned-index entry removal's clause carries a true literal. -/
theorem avieResJ_entailed {a : Assignment} {is : List Nat} {i k : Nat}
    {idx : Int} {j : Nat} {w : Int}
    (h : (DomConstraint.arrayVarIntElementSlot is i k).SatisfiedBy a)
    (he : avieEntry is idx = some j) :
    ∃ l ∈ [posNe j w, posNe i idx, negNe k w], l.eval a = some true := by
  by_cases hpin : a[i]? = some (.int idx)
  · obtain ⟨e, hk, hj⟩ := avie_entry_reads h hpin he
    by_cases hew : e = w
    · exact ⟨negNe k w,
        List.mem_cons_of_mem (posNe j w)
          (List.mem_cons_of_mem (posNe i idx)
            (List.mem_singleton_self (negNe k w))),
        aie_negNe_eval_true (slotInt_of_int_read hk) hew⟩
    · exact ⟨posNe j w, List.mem_cons_self,
        aie_posNe_eval_true (slotInt_of_int_read hj) hew⟩
  · obtain ⟨idx', e', j', hi, hk', hent', hj'⟩ := arrayVarIntElement_views h
    have hne : idx' ≠ idx := by
      intro hidx
      apply hpin
      rw [hidx] at hi
      exact hi
    exact ⟨posNe i idx,
      List.mem_cons_of_mem (posNe j w) (List.mem_cons_self),
      aie_posNe_eval_true (slotInt_of_int_read hi) hne⟩

/-- The pinned-target removal's clause carries a true literal. -/
theorem avieResPinVal_entailed {a : Assignment} {is : List Nat} {i k : Nat}
    {idx : Int} {j : Nat} {v : Int}
    (h : (DomConstraint.arrayVarIntElementSlot is i k).SatisfiedBy a)
    (he : avieEntry is idx = some j) :
    ∃ l ∈ [posNe i idx, posNe k v, negNe j v], l.eval a = some true := by
  by_cases hpin : a[i]? = some (.int idx)
  · obtain ⟨e, hk, hj⟩ := avie_entry_reads h hpin he
    by_cases hev : e = v
    · exact ⟨negNe j v,
        List.mem_cons_of_mem (posNe i idx)
          (List.mem_cons_of_mem (posNe k v)
            (List.mem_singleton_self (negNe j v))),
        aie_negNe_eval_true (slotInt_of_int_read hj) hev⟩
    · exact ⟨posNe k v, List.mem_cons_of_mem (posNe i idx)
        (List.mem_cons_self),
        aie_posNe_eval_true (slotInt_of_int_read hk) hev⟩
  · obtain ⟨idx', e', j', hi, hk', hent', hj'⟩ := arrayVarIntElement_views h
    have hne : idx' ≠ idx := by
      intro hidx
      apply hpin
      rw [hidx] at hi
      exact hi
    exact ⟨posNe i idx, List.mem_cons_self,
      aie_posNe_eval_true (slotInt_of_int_read hi) hne⟩

/-- The singleton-entry separation's clause carries a true literal. -/
theorem avieResSingle_entailed {a : Assignment} {is : List Nat} {i k : Nat}
    {idx : Int} {j : Nat} {w : Int}
    (h : (DomConstraint.arrayVarIntElementSlot is i k).SatisfiedBy a)
    (he : avieEntry is idx = some j) :
    ∃ l ∈ [posNe i idx, posNe j w, negNe k w], l.eval a = some true := by
  by_cases hpin : a[i]? = some (.int idx)
  · obtain ⟨e, hk, hj⟩ := avie_entry_reads h hpin he
    by_cases hew : e = w
    · exact ⟨negNe k w,
        List.mem_cons_of_mem (posNe i idx)
          (List.mem_cons_of_mem (posNe j w)
            (List.mem_singleton_self (negNe k w))),
        aie_negNe_eval_true (slotInt_of_int_read hk) hew⟩
    · exact ⟨posNe j w, List.mem_cons_of_mem (posNe i idx)
        (List.mem_cons_self),
        aie_posNe_eval_true (slotInt_of_int_read hj) hew⟩
  · obtain ⟨idx', e', j', hi, hk', hent', hj'⟩ := arrayVarIntElement_views h
    have hne : idx' ≠ idx := by
      intro hidx
      apply hpin
      rw [hidx] at hi
      exact hi
    exact ⟨posNe i idx, List.mem_cons_self,
      aie_posNe_eval_true (slotInt_of_int_read hi) hne⟩

/-- The below-hull separation's clause carries a true literal. -/
theorem avieResBelow_entailed {a : Assignment} {is : List Nat} {i k : Nat}
    {idx : Int} {j : Nat} {mx mn : Int}
    (h : (DomConstraint.arrayVarIntElementSlot is i k).SatisfiedBy a)
    (he : avieEntry is idx = some j) (hlt : mx < mn) :
    ∃ l ∈ [posNe i idx, negLe j mx, posLe k (mn - 1)],
      l.eval a = some true := by
  by_cases hpin : a[i]? = some (.int idx)
  · obtain ⟨e, hk, hj⟩ := avie_entry_reads h hpin he
    by_cases hgt : mx < e
    · exact ⟨negLe j mx, List.mem_cons_of_mem (posNe i idx)
        (List.mem_cons_self),
        avie_negLe_eval_true (slotInt_of_int_read hj) hgt⟩
    · have hle : e ≤ mn - 1 := by omega
      exact ⟨posLe k (mn - 1),
        List.mem_cons_of_mem (posNe i idx)
          (List.mem_cons_of_mem (negLe j mx)
            (List.mem_singleton_self (posLe k (mn - 1)))),
        avie_posLe_eval_true (slotInt_of_int_read hk) hle⟩
  · obtain ⟨idx', e', j', hi, hk', hent', hj'⟩ := arrayVarIntElement_views h
    have hne : idx' ≠ idx := by
      intro hidx
      apply hpin
      rw [hidx] at hi
      exact hi
    exact ⟨posNe i idx, List.mem_cons_self,
      aie_posNe_eval_true (slotInt_of_int_read hi) hne⟩

/-- The above-hull separation's clause carries a true literal. -/
theorem avieResAbove_entailed {a : Assignment} {is : List Nat} {i k : Nat}
    {idx : Int} {j : Nat} {mx mn : Int}
    (h : (DomConstraint.arrayVarIntElementSlot is i k).SatisfiedBy a)
    (he : avieEntry is idx = some j) (hlt : mx < mn) :
    ∃ l ∈ [posNe i idx, negLe k mx, posLe j (mn - 1)],
      l.eval a = some true := by
  by_cases hpin : a[i]? = some (.int idx)
  · obtain ⟨e, hk, hj⟩ := avie_entry_reads h hpin he
    by_cases hgt : mx < e
    · exact ⟨negLe k mx, List.mem_cons_of_mem (posNe i idx)
        (List.mem_cons_self),
        avie_negLe_eval_true (slotInt_of_int_read hk) hgt⟩
    · have hle : e ≤ mn - 1 := by omega
      exact ⟨posLe j (mn - 1),
        List.mem_cons_of_mem (posNe i idx)
          (List.mem_cons_of_mem (negLe k mx)
            (List.mem_singleton_self (posLe j (mn - 1)))),
        avie_posLe_eval_true (slotInt_of_int_read hj) hle⟩
  · obtain ⟨idx', e', j', hi, hk', hent', hj'⟩ := arrayVarIntElement_views h
    have hne : idx' ≠ idx := by
      intro hidx
      apply hpin
      rw [hidx] at hi
      exact hi
    exact ⟨posNe i idx, List.mem_cons_self,
      aie_posNe_eval_true (slotInt_of_int_read hi) hne⟩

/-- The no-support clause carries a true literal at every solution. -/
theorem avieResNoSupp_entailed {a : Assignment} {is : List Nat} {i k : Nat}
    {w : Int}
    (h : (DomConstraint.arrayVarIntElementSlot is i k).SatisfiedBy a) :
    ∃ l ∈ posNe k w :: is.map (fun j => negNe j w), l.eval a = some true := by
  obtain ⟨idx', e, j', hi, hk, hent', hj'⟩ := arrayVarIntElement_views h
  by_cases hew : e = w
  · refine ⟨negNe j' w, List.mem_cons_of_mem _ (List.mem_map.mpr
      ⟨j', avieEntry_mem hent', rfl⟩), ?_⟩
    exact aie_negNe_eval_true (slotInt_of_int_read hj') hew
  · exact ⟨posNe k w, List.mem_cons_self,
      aie_posNe_eval_true (slotInt_of_int_read hk) hew⟩

/-! ### Fitting-solution heads and conflict exclusion -/

/-- The pinned-index out-of-range conflict excludes every fitting solution. -/
theorem avieResPinBad_excluded {st : State} {a : Assignment} {is : List Nat}
    {i k : Nat} {idx : Int}
    (hfit : Core.Assignment.Fits st.domains a)
    (hidx : slotEnum st.domains i = [.int idx])
    (hnone : avieEntry is idx = none)
    (h : (DomConstraint.arrayVarIntElementSlot is i k).SatisfiedBy a) : False := by
  have hi : a[i]? = some (.int idx) := aie_read_of_dom_singleton hfit hidx
  obtain ⟨idx', e, j', hi', hk, hent', hj'⟩ := arrayVarIntElement_views h
  have hidx' : idx' = idx :=
    Value.int.inj (Option.some.inj (hi'.symm.trans hi))
  subst hidx'
  rw [hent'] at hnone
  cases hnone

/-- The pinned-index target removal is true at every fitting solution. -/
theorem avie_pinK_head {st : State} {a : Assignment} {is : List Nat} {i k : Nat}
    {idx : Int} {j : Nat} {w : Int}
    (hfit : Core.Assignment.Fits st.domains a)
    (hidx : slotEnum st.domains i = [.int idx])
    (h : (DomConstraint.arrayVarIntElementSlot is i k).SatisfiedBy a)
    (he : avieEntry is idx = some j)
    (hfb : firstBadView (slotEnum st.domains k)
      (fun w => valueMemB ((.int w)) (slotEnum st.domains j)) = some w) :
    (posNe k w).eval a = some true := by
  obtain ⟨-, -, -, hbad⟩ := firstBadView_some hfb
  have hi : a[i]? = some (.int idx) := aie_read_of_dom_singleton hfit hidx
  obtain ⟨e, hk, hj⟩ := avie_entry_reads h hi he
  have hmem : (.int e : Value) ∈ st.domains.getD j Dom.empty := hfit.2 j (.int e) hj
  have hne : e ≠ w := by
    intro hew
    have hmemE : (.int w : Value) ∈ slotEnum st.domains j := by
      have hw : (.int w : Value) ∈ st.domains.getD j Dom.empty := by
        rw [← hew]; exact hmem
      simpa [slotEnum] using (DomainLike.mem_iff _ _).mp hw
    have htrue : valueMemB ((.int w)) (slotEnum st.domains j) = true :=
      valueMemB_iff.mpr hmemE
    rw [hbad] at htrue
    cases htrue
  exact aie_posNe_eval_true (slotInt_of_int_read hk) hne

/-- The pinned-index entry removal is true at every fitting solution. -/
theorem avie_pinJ_head {st : State} {a : Assignment} {is : List Nat} {i k : Nat}
    {idx : Int} {j : Nat} {w : Int}
    (hfit : Core.Assignment.Fits st.domains a)
    (hidx : slotEnum st.domains i = [.int idx])
    (h : (DomConstraint.arrayVarIntElementSlot is i k).SatisfiedBy a)
    (he : avieEntry is idx = some j)
    (hfb : firstBadView (slotEnum st.domains j)
      (fun w => valueMemB ((.int w)) (slotEnum st.domains k)) = some w) :
    (posNe j w).eval a = some true := by
  obtain ⟨-, -, -, hbad⟩ := firstBadView_some hfb
  have hi : a[i]? = some (.int idx) := aie_read_of_dom_singleton hfit hidx
  obtain ⟨e, hk, hj⟩ := avie_entry_reads h hi he
  have hmemk : (.int e : Value) ∈ st.domains.getD k Dom.empty := hfit.2 k (.int e) hk
  have hne : e ≠ w := by
    intro hew
    have hmemE : (.int w : Value) ∈ slotEnum st.domains k := by
      have hw : (.int w : Value) ∈ st.domains.getD k Dom.empty := by
        rw [← hew]; exact hmemk
      simpa [slotEnum] using (DomainLike.mem_iff _ _).mp hw
    have htrue : valueMemB ((.int w)) (slotEnum st.domains k) = true :=
      valueMemB_iff.mpr hmemE
    rw [hbad] at htrue
    cases htrue
  exact aie_posNe_eval_true (slotInt_of_int_read hj) hne

/-- The unpinned out-of-range removal is true at every solution (uses only
    the missing entry and the index read). -/
theorem avie_out_true {a : Assignment} {is : List Nat} {i k : Nat} {idx : Int}
    (h : (DomConstraint.arrayVarIntElementSlot is i k).SatisfiedBy a)
    (hnone : avieEntry is idx = none) :
    (posNe i idx).eval a = some true := by
  obtain ⟨idx', e, j', hi, hk, hent', hj'⟩ := arrayVarIntElement_views h
  by_cases hidx : idx' = idx
  · rw [hidx] at hent'
    rw [hent'] at hnone
    cases hnone
  · exact aie_posNe_eval_true (slotInt_of_int_read hi) hidx

/-- The pinned-target removal is true at every fitting solution. -/
theorem avie_pinVal_head {st : State} {a : Assignment} {is : List Nat}
    {i k : Nat} {idx : Int} {j : Nat} {v : Int}
    (hfit : Core.Assignment.Fits st.domains a)
    (hk : slotEnum st.domains k = [.int v])
    (h : (DomConstraint.arrayVarIntElementSlot is i k).SatisfiedBy a)
    (he : avieEntry is idx = some j)
    (hvm : valueMemB ((.int v)) (slotEnum st.domains j) = false) :
    (posNe i idx).eval a = some true := by
  obtain ⟨idx', e, j', hi, hkRead, hent', hj'⟩ := arrayVarIntElement_views h
  by_cases hidx : idx' = idx
  · rw [hidx] at hent'
    have hjj : j' = j := Option.some.inj (hent'.symm.trans he)
    rw [hjj] at hj'
    rw [hjj] at hent'

    have hmemk : (.int e : Value) ∈ st.domains.getD k Dom.empty :=
      hfit.2 k (.int e) hkRead
    have hmemkE : (.int e : Value) ∈ slotEnum st.domains k := by
      simpa [slotEnum] using (DomainLike.mem_iff _ _).mp hmemk
    rw [hk] at hmemkE
    have hev : e = v := Value.int.inj (List.mem_singleton.mp hmemkE)
    have hmemj : (.int e : Value) ∈ st.domains.getD j Dom.empty :=
      hfit.2 j (.int e) hj'
    rw [hev] at hmemj
    have hmemjE : (.int v : Value) ∈ slotEnum st.domains j := by
      simpa [slotEnum] using (DomainLike.mem_iff _ _).mp hmemj
    have htrue : valueMemB ((.int v)) (slotEnum st.domains j) = true :=
      valueMemB_iff.mpr hmemjE
    rw [hvm] at htrue
    cases htrue
  · exact aie_posNe_eval_true (slotInt_of_int_read hi) hidx

/-- The singleton-entry removal is true at every fitting solution. -/
theorem avie_single_head {st : State} {a : Assignment} {is : List Nat}
    {i k : Nat} {idx : Int} {j : Nat} {w : Int}
    (hfit : Core.Assignment.Fits st.domains a)
    (h : (DomConstraint.arrayVarIntElementSlot is i k).SatisfiedBy a)
    (he : avieEntry is idx = some j)
    (hdj : slotEnum st.domains j = [.int w])
    (hvm : valueMemB ((.int w)) (slotEnum st.domains k) = false) :
    (posNe i idx).eval a = some true := by
  obtain ⟨idx', e, j', hi, hk, hent', hj'⟩ := arrayVarIntElement_views h
  by_cases hidx : idx' = idx
  · rw [hidx] at hent'
    have hjj : j' = j := Option.some.inj (hent'.symm.trans he)
    rw [hjj] at hj'
    rw [hjj] at hent'

    have hmemj : (.int e : Value) ∈ st.domains.getD j Dom.empty :=
      hfit.2 j (.int e) hj'
    have hmemjE : (.int e : Value) ∈ slotEnum st.domains j := by
      simpa [slotEnum] using (DomainLike.mem_iff _ _).mp hmemj
    rw [hdj] at hmemjE
    have hew : e = w := Value.int.inj (List.mem_singleton.mp hmemjE)
    have hmemk : (.int e : Value) ∈ st.domains.getD k Dom.empty :=
      hfit.2 k (.int e) hk
    rw [hew] at hmemk
    have hmemkE : (.int w : Value) ∈ slotEnum st.domains k := by
      simpa [slotEnum] using (DomainLike.mem_iff _ _).mp hmemk
    have htrue : valueMemB ((.int w)) (slotEnum st.domains k) = true :=
      valueMemB_iff.mpr hmemkE
    rw [hvm] at htrue
    cases htrue
  · exact aie_posNe_eval_true (slotInt_of_int_read hi) hidx

/-- The below-hull removal is true at every fitting solution. -/
theorem avie_below_head {st : State} {a : Assignment} {is : List Nat}
    {i k : Nat} {idx : Int} {j : Nat} {mx mn : Int}
    (hfit : Core.Assignment.Fits st.domains a)
    (h : (DomConstraint.arrayVarIntElementSlot is i k).SatisfiedBy a)
    (he : avieEntry is idx = some j)
    (hmx : domMaxI (st.domains.getD j Dom.empty) = some mx)
    (hmn : domMinI (st.domains.getD k Dom.empty) = some mn)
    (hlt : mx < mn) :
    (posNe i idx).eval a = some true := by
  obtain ⟨idx', e, j', hi, hk, hent', hj'⟩ := arrayVarIntElement_views h
  by_cases hidx : idx' = idx
  · rw [hidx] at hent'
    have hjj : j' = j := Option.some.inj (hent'.symm.trans he)
    rw [hjj] at hj'
    rw [hjj] at hent'

    have hxl : slotInt a j = some e := slotInt_of_int_read hj'
    have hkl : slotInt a k = some e := slotInt_of_int_read hk
    have h1 : e ≤ mx :=
      fits_max_bound (st := st) hfit hmx hxl
    have h2 : mn ≤ e :=
      fits_min_bound (st := st) hfit hmn hkl
    omega
  · exact aie_posNe_eval_true (slotInt_of_int_read hi) hidx

/-- The above-hull removal is true at every fitting solution. -/
theorem avie_above_head {st : State} {a : Assignment} {is : List Nat}
    {i k : Nat} {idx : Int} {j : Nat} {mx mn : Int}
    (hfit : Core.Assignment.Fits st.domains a)
    (h : (DomConstraint.arrayVarIntElementSlot is i k).SatisfiedBy a)
    (he : avieEntry is idx = some j)
    (hmx : domMaxI (st.domains.getD k Dom.empty) = some mx)
    (hmn : domMinI (st.domains.getD j Dom.empty) = some mn)
    (hlt : mx < mn) :
    (posNe i idx).eval a = some true := by
  obtain ⟨idx', e, j', hi, hk, hent', hj'⟩ := arrayVarIntElement_views h
  by_cases hidx : idx' = idx
  · rw [hidx] at hent'
    have hjj : j' = j := Option.some.inj (hent'.symm.trans he)
    rw [hjj] at hj'
    rw [hjj] at hent'

    have hxl : slotInt a j = some e := slotInt_of_int_read hj'
    have hkl : slotInt a k = some e := slotInt_of_int_read hk
    have h1 : e ≤ mx :=
      fits_max_bound (st := st) hfit hmx hkl
    have h2 : mn ≤ e :=
      fits_min_bound (st := st) hfit hmn hxl
    omega
  · exact aie_posNe_eval_true (slotInt_of_int_read hi) hidx

/-- The no-support target removal is true at every fitting solution. -/
theorem avie_noSupp_head {st : State} {a : Assignment} {is : List Nat}
    {i k : Nat} {w : Int}
    (hfit : Core.Assignment.Fits st.domains a)
    (h : (DomConstraint.arrayVarIntElementSlot is i k).SatisfiedBy a)
    (hfb : firstBadView (slotEnum st.domains k)
      (fun w => avieTableMemB st is w) = some w) :
    (posNe k w).eval a = some true := by
  obtain ⟨-, -, -, hbad⟩ := firstBadView_some hfb
  obtain ⟨idx', e, j', hi, hk, hent', hj'⟩ := arrayVarIntElement_views h
  by_cases hew : e = w
  · have hmem : (.int w : Value) ∈ st.domains.getD j' Dom.empty := by
      rw [← hew]
      exact hfit.2 j' (.int e) hj'
    have hmemE : (.int w : Value) ∈ slotEnum st.domains j' := by
      simpa [slotEnum] using (DomainLike.mem_iff _ _).mp hmem
    have hfalse := avieTableMemB_false hbad (avieEntry_mem hent')
    have htrue : valueMemB ((.int w)) (slotEnum st.domains j') = true :=
      valueMemB_iff.mpr hmemE
    rw [hfalse] at htrue
    cases htrue
  · exact aie_posNe_eval_true (slotInt_of_int_read hk) hew

/-- Any non-`.stable` emission happens past the integer-domain guard. -/
theorem avie_guard_of_res {st : State} {is : List Nat} {i k : Nat}
    {res : PropagationResult}
    (h : propArrayVarIntElement st is i k = res) (hne : res ≠ .stable) :
    domsIntOnlyB st.domains (i :: k :: is) = true := by
  unfold propArrayVarIntElement at h
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
        by_cases hguard : domsIntOnlyB st.domains (i :: k :: is) = false
        · rw [if_pos hguard] at h
          exact absurd h.symm hne
        · cases hv : domsIntOnlyB st.domains (i :: k :: is) with
          | true => rfl
          | false => exact absurd hv hguard

end LeanFzn.Solver.Propagation

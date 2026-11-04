/-
File: LeanFzn/Solver/Propagation/Proofs/PropCheck.lean

PLAN L0a: a GENERIC checking propagator for any `DomConstraint`. `propCheck dc`
watches nothing; once every slot `dc` reads (`dcSlotsFull dc`, the TOTAL
extension of `LeanFzn.Solver.UIP.LcgEmissionTyped.dcSlots` that also covers the
`DomIntArg` operands of the general two/array-operand families and the four
plain-slot families `dcSlots` drops to `[]`) is pinned to a singleton frame
domain, it checks `dc.satisfiedB` on the forced assignment: failure reports a
conflict clause built from the singleton facts (`posNe s c` for an integer
singleton, `posBool s (!b)` for a Boolean singleton — the exact falsified
normal forms `FixExpl`/`AbsentExpl` certify, see
`LeanFzn/Solver/UIP/Proofs/LcgPropCheck.lean`); it never implies.

This module carries ONLY the definition and the obligations provable without
the UIP trail vocabulary: the generic slot list, the propagator itself, that
it never implies, that `satisfiedB` depends only on `dcSlotsFull` lookups
(the congruence lemma), and that its conflict clause is entailed by every
leaf solution faithful to the frame. The UIP module adds the semantic
(`ResSem`), canonical (`ResCanonical`) and typed (`ResTyped`) obligations,
which need `FrameExplainedFull`/`ClauseCanonical`/`LitWF` — all UIP-layer
vocabulary `propCheck` itself must stay below (Propagation never imports
UIP).

Dependencies:
  - LeanFzn.Solver.Propagation.Propagate: `DomConstraint`, `satisfiedB`,
    `Propagator`, `State`, the order/removal literal constructors.
  - LeanFzn.Solver.Propagation.Encoding: `Atom.slot`.
  - LeanFzn.Solver.Core.Semantics: `Assignment.Fits`.

DAG:
  LeanFzn.Solver.Propagation.Propagate + LeanFzn.Solver.Propagation.Encoding
  -> LeanFzn.Solver.Propagation.Proofs.PropCheck
  -> LeanFzn.Solver.UIP.Proofs.LcgPropCheck (the semantic/typed/canonical obligations).
-/
import LeanFzn.Solver.Propagation.Propagate
import LeanFzn.Solver.Propagation.Encoding
import LeanFzn.Solver.Core.Semantics
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation.DomainFiltering

/-! ## 1. The full slot list -/

/-- Every slot position a constraint reads: the TOTAL extension of
`dcSlots` that also covers the `DomIntArg` operands of the general
two/array-operand families (`maxGen`/`minGen`/`divGen`/`modGen`/
`minPair`/`maxPair`) and the plain-slot families `timesSlot`/`minSlot`/
`maxSlot`/`absSlot` that `dcSlots` drops to `[]` (no currently-LCG-routed
family needs them there; `propCheck` is generic over every constructor). -/
def dcSlotsFull : DomConstraint → List Nat
  | .eqSlot i j | .neSlot i j | .leSlot i j | .ltSlot i j => [i, j]
  | .constEq i _ | .leConstHi i _ | .leConstLo i _
  | .ltConstHi i _ | .ltConstLo i _ => [i]
  | .plusSlot i j k | .boolAndSlot i j k | .boolOrSlot i j k
  | .timesSlot i j k | .minSlot i j k | .maxSlot i j k => [i, j, k]
  | .absSlot i k => [i, k]
  | .boolNotSlot i j => [i, j]
  | .allDiff is | .linLe _ is _ | .linEq _ is _ | .linNe _ is _ => is
  | .boolClauseSlot ps ns => ps ++ ns
  | .arrayBoolAndSlot is k => is ++ [k]
  | .bool2intSlot i k => [i, k]
  | .boolEqSlot i j => [i, j]
  | .arrayIntElementSlot _ i k => [i, k]
  | .arrayVarIntElementSlot is i k => is ++ [i, k]
  | .arrayVarBoolElementSlot is i k => is ++ [i, k]
  | .eqReifSlot i j r => [i, j, r]
  | .leReifSlot i j r => [i, j, r]
  | .neReifSlot i j r => [i, j, r]
  | .linEqReif _ is _ r => is ++ [r]
  | .linLeReif _ is _ r => is ++ [r]
  | .linNeReif _ is _ r => is ++ [r]
  | .maxGen os r => (os.flatMap DomIntArg.slots) ++ r.slots
  | .minGen os r => (os.flatMap DomIntArg.slots) ++ r.slots
  | .divGen o₁ o₂ r => o₁.slots ++ o₂.slots ++ r.slots
  | .modGen o₁ o₂ r => o₁.slots ++ o₂.slots ++ r.slots
  | .minPair o₀ o₁ r => o₀.slots ++ o₁.slots ++ r.slots
  | .maxPair o₀ o₁ r => o₀.slots ++ o₁.slots ++ r.slots
  | .setInSlot i _ => [i]
  | .setInReifSlot i _ r => [i, r]

/-! ## 2. The forced frame assignment -/

/-- The singleton value at slot `s` of a domain list, if any. -/
def frameSingleton (doms : List Domain) (s : Nat) : Option Value :=
  match Dom.enum (doms.getD s Dom.empty) with
  | [v] => some v
  | _ => none

/-- Every slot of `dcSlotsFull dc` has a singleton frame domain. -/
def propCheckReady (dc : DomConstraint) (doms : List Domain) : Bool :=
  (dcSlotsFull dc).all (fun s => (frameSingleton doms s).isSome)

/-- The forced assignment: the singleton value at every slot where one
exists, an arbitrary placeholder otherwise (irrelevant off `dcSlotsFull dc`
under `propCheckReady`, see `satisfiedB_dcSlotsFull_congr`). -/
def propCheckAssign (doms : List Domain) : List Value :=
  doms.map (fun d => match Dom.enum d with | [v] => v | _ => Value.int 0)

/-- The conflict literal contributed by a singleton slot: `posNe s c` for
an integer singleton, `posBool s (!b)` for a Boolean singleton — the only
falsified normal forms `FixExpl`/`AbsentExpl` certify. -/
def singletonLit (s : Nat) (v : Value) : Option Literal :=
  match v with
  | .int c => some (posNe s c)
  | .bool b => some (posBool s (!b))
  | .setOfInt _ | .array _ => none

/-- `propCheck`'s conflict clause: the disjunction of the singleton
falsified literals over every slot the constraint reads. -/
def propCheckConflict (dc : DomConstraint) (doms : List Domain) : Clause :=
  (dcSlotsFull dc).filterMap (fun s => (frameSingleton doms s).bind (singletonLit s))

/-! ## 3. The propagator -/

/-- **The generic checking propagator** (PLAN L0a): watches nothing; when
every slot `dc` reads is pinned to a singleton frame domain, it evaluates
`dc.satisfiedB` on the forced assignment and reports a conflict clause over
the singleton facts on failure; it never implies. -/
def propCheck (dc : DomConstraint) : Propagator :=
  { watches := []
    run := fun st =>
      if propCheckReady dc st.domains = true then
        if dc.satisfiedB (propCheckAssign st.domains) = true then .stable
        else .conflict (propCheckConflict dc st.domains)
      else .stable }

/-- `propCheck` never implies. -/
theorem propCheck_implied_elim {dc : DomConstraint} {st : State} {l : Literal} {r : Reason}
    (h : (propCheck dc).run st = .implied l r) : False := by
  simp only [propCheck] at h
  split at h
  · split at h
    · cases h
    · cases h
  · cases h

/-- A conflict from `propCheck` always pins down the gate and the forced
check, and its clause is exactly `propCheckConflict`. -/
theorem propCheck_conflict_inv {dc : DomConstraint} {st : State} {c : Clause}
    (h : (propCheck dc).run st = .conflict c) :
    propCheckReady dc st.domains = true ∧
      dc.satisfiedB (propCheckAssign st.domains) = false ∧
      c = propCheckConflict dc st.domains := by
  simp only [propCheck] at h
  split at h
  · rename_i hready
    split at h
    · cases h
    · rename_i hsat
      refine ⟨hready, ?_, ?_⟩
      · revert hsat
        cases dc.satisfiedB (propCheckAssign st.domains) <;> simp
      · injection h with h'; exact h'.symm
  · cases h

/-! ## 4. The singleton-value agreement lemma -/

theorem frameSingleton_iff {doms : List Domain} {s : Nat} {v : Value} :
    frameSingleton doms s = some v ↔
      (doms.getD s Dom.empty).enum = [v] := by
  unfold frameSingleton
  rcases hd : (doms.getD s Dom.empty).enum with _ | ⟨x, xs⟩
  · simp
  · rcases xs with _ | ⟨y, ys⟩
    · simp
    · simp

/-- The forced assignment reads exactly the singleton value at every
slot with one: `propCheckAssign doms` agrees with `frameSingleton doms`
wherever the latter is defined. -/
theorem propCheckAssign_getElem? {doms : List Domain} {s : Nat} {v : Value}
    (h : frameSingleton doms s = some v) : (propCheckAssign doms)[s]? = some v := by
  have hd := frameSingleton_iff.mp h
  unfold propCheckAssign
  rw [List.getElem?_map]
  cases hget : doms[s]? with
  | none =>
      rw [List.getD_eq_getElem?_getD, hget] at hd
      simp only [Option.getD_none, Dom.enum_empty] at hd
      simp at hd ⊢
  | some d =>
      have hd' : d.enum = [v] := by
        rw [List.getD_eq_getElem?_getD, hget] at hd
        simpa using hd
      simp [hd']

/-! ## 5. The `satisfiedB` congruence lemma -/

private theorem bang_congr {a1 a2 : List Value} {i : Nat} (h : a1[i]? = a2[i]?) :
    a1[i]! = a2[i]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD, h]

private theorem map_bang_congr {a1 a2 : List Value} {is : List Nat}
    (h : ∀ i ∈ is, a1[i]? = a2[i]?) :
    is.map (fun i => a1[i]!) = is.map (fun i => a2[i]!) :=
  List.map_congr_left (fun i hi => bang_congr (h i hi))

private theorem all_congr_mem {α : Type} {l : List α} {p q : α → Bool}
    (h : ∀ a ∈ l, p a = q a) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
      simp only [List.all_cons]
      rw [h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

private theorem any_congr_mem {α : Type} {l : List α} {p q : α → Bool}
    (h : ∀ a ∈ l, p a = q a) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
      simp only [List.any_cons]
      rw [h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

private theorem isSome_congr {a1 a2 : List Value} {i : Nat} (h : a1[i]? = a2[i]?) :
    (a1[i]?).isSome = (a2[i]?).isSome := by rw [h]

private theorem slotIsBoolB_congr {a1 a2 : List Value} {i : Nat} {b : Bool}
    (h : a1[i]? = a2[i]?) : slotIsBoolB a1 i b = slotIsBoolB a2 i b := by
  unfold slotIsBoolB
  rw [h]

private theorem read_congr {a1 a2 : List Value} {o : DomIntArg}
    (h : ∀ i ∈ o.slots, a1[i]? = a2[i]?) :
    DomIntArg.read a1 o = DomIntArg.read a2 o := by
  cases o with
  | slot i => exact bang_congr (h i (by simp [DomIntArg.slots]))
  | lit k => rfl

private theorem map_read_congr {a1 a2 : List Value} {os : List DomIntArg}
    (h : ∀ i ∈ os.flatMap DomIntArg.slots, a1[i]? = a2[i]?) :
    os.map (DomIntArg.read a1) = os.map (DomIntArg.read a2) :=
  List.map_congr_left (fun _o ho => read_congr (fun i hi => h i (List.mem_flatMap_of_mem ho hi)))

/-- **`satisfiedB` depends only on `dcSlotsFull` lookups**: two
assignments agreeing on every slot `dc` reads agree on `dc.satisfiedB`. -/
theorem satisfiedB_dcSlotsFull_congr (dc : DomConstraint) {a1 a2 : List Value}
    (h : ∀ s ∈ dcSlotsFull dc, a1[s]? = a2[s]?) :
    dc.satisfiedB a1 = dc.satisfiedB a2 := by
  cases dc with
  | eqSlot i j | neSlot i j | leSlot i j | ltSlot i j
  | boolNotSlot i j | boolEqSlot i j | absSlot i j | bool2intSlot i j =>
      simp only [DomConstraint.satisfiedB]
      rw [h i (by simp [dcSlotsFull]), h j (by simp [dcSlotsFull])]
  | constEq i _ | leConstHi i _ | leConstLo i _ | ltConstHi i _ | ltConstLo i _ =>
      simp only [DomConstraint.satisfiedB]
      rw [h i (by simp [dcSlotsFull])]
  | plusSlot i j k | timesSlot i j k | minSlot i j k | maxSlot i j k
  | boolAndSlot i j k | boolOrSlot i j k
  | eqReifSlot i j k | leReifSlot i j k | neReifSlot i j k =>
      simp only [DomConstraint.satisfiedB]
      rw [h i (by simp [dcSlotsFull]), h j (by simp [dcSlotsFull]), h k (by simp [dcSlotsFull])]
  | arrayIntElementSlot xs i j =>
      simp only [DomConstraint.satisfiedB]
      rw [h i (by simp [dcSlotsFull]), h j (by simp [dcSlotsFull])]
  | allDiff is =>
      simp only [DomConstraint.satisfiedB]
      have h' : ∀ i ∈ is, a1[i]? = a2[i]? := h
      rw [map_bang_congr h']
  | linEq coeffs is b | linLe coeffs is b | linNe coeffs is b =>
      simp only [DomConstraint.satisfiedB]
      have h' : ∀ i ∈ is, a1[i]? = a2[i]? := h
      rw [map_bang_congr h']
  | boolClauseSlot ps ns =>
      simp only [DomConstraint.satisfiedB]
      have hps : ∀ i ∈ ps, a1[i]? = a2[i]? := fun i hi => h i (List.mem_append_left _ hi)
      have hns : ∀ j ∈ ns, a1[j]? = a2[j]? := fun j hj => h j (List.mem_append_right _ hj)
      rw [any_congr_mem (fun i hi => slotIsBoolB_congr (hps i hi)),
          any_congr_mem (fun j hj => slotIsBoolB_congr (hns j hj))]
  | arrayBoolAndSlot is k =>
      simp only [DomConstraint.satisfiedB]
      have hris : ∀ i ∈ is, a1[i]? = a2[i]? := fun i hi => h i (List.mem_append_left _ hi)
      have hk : a1[k]? = a2[k]? := h k (List.mem_append_right _ (List.mem_singleton_self k))
      rw [hk, all_congr_mem (fun i hi => slotIsBoolB_congr (hris i hi))]
  | arrayVarIntElementSlot is i k | arrayVarBoolElementSlot is i k =>
      simp only [DomConstraint.satisfiedB]
      have hris : ∀ j ∈ is, a1[j]? = a2[j]? := fun j hj => h j (List.mem_append_left _ hj)
      have hi : a1[i]? = a2[i]? :=
        h i (List.mem_append_right _ List.mem_cons_self)
      have hk : a1[k]? = a2[k]? :=
        h k (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self k)))
      rw [hi, hk, map_bang_congr hris, all_congr_mem (fun j hj => isSome_congr (hris j hj))]
  | linEqReif coeffs is b r | linLeReif coeffs is b r | linNeReif coeffs is b r =>
      simp only [DomConstraint.satisfiedB]
      have hris : ∀ i ∈ is, a1[i]? = a2[i]? := fun i hi => h i (List.mem_append_left _ hi)
      have hr : a1[r]? = a2[r]? := h r (List.mem_append_right _ (List.mem_singleton_self r))
      rw [hr, map_bang_congr hris]
  | maxGen os r | minGen os r =>
      simp only [DomConstraint.satisfiedB]
      have hos : ∀ i ∈ os.flatMap DomIntArg.slots, a1[i]? = a2[i]? :=
        fun i hi => h i (List.mem_append_left _ hi)
      have hr : ∀ i ∈ r.slots, a1[i]? = a2[i]? :=
        fun i hi => h i (List.mem_append_right _ hi)
      rw [read_congr hr, map_read_congr hos]
  | divGen o1 o2 r | modGen o1 o2 r =>
      simp only [DomConstraint.satisfiedB]
      have h1 : ∀ i ∈ o1.slots, a1[i]? = a2[i]? :=
        fun i hi => h i (List.mem_append_left _ (List.mem_append_left _ hi))
      have h2 : ∀ i ∈ o2.slots, a1[i]? = a2[i]? :=
        fun i hi => h i (List.mem_append_left _ (List.mem_append_right _ hi))
      have h3 : ∀ i ∈ r.slots, a1[i]? = a2[i]? :=
        fun i hi => h i (List.mem_append_right _ hi)
      rw [read_congr h1, read_congr h2, read_congr h3]
  | minPair o0 o1 r | maxPair o0 o1 r =>
      simp only [DomConstraint.satisfiedB]
      have h1 : ∀ i ∈ o0.slots, a1[i]? = a2[i]? :=
        fun i hi => h i (List.mem_append_left _ (List.mem_append_left _ hi))
      have h2 : ∀ i ∈ o1.slots, a1[i]? = a2[i]? :=
        fun i hi => h i (List.mem_append_left _ (List.mem_append_right _ hi))
      have h3 : ∀ i ∈ r.slots, a1[i]? = a2[i]? :=
        fun i hi => h i (List.mem_append_right _ hi)
      rw [read_congr h1, read_congr h2, read_congr h3]
  | setInSlot i s =>
      simp only [DomConstraint.satisfiedB]
      rw [h i (by simp [dcSlotsFull])]
  | setInReifSlot i s r =>
      simp only [DomConstraint.satisfiedB]
      rw [h i (by simp [dcSlotsFull]), h r (by simp [dcSlotsFull])]

/-! ## 6. Conflict-clause entailment -/

theorem mem_propCheckConflict_iff {dc : DomConstraint} {doms : List Domain} {q : Literal} :
    q ∈ propCheckConflict dc doms ↔
      ∃ s ∈ dcSlotsFull dc, (frameSingleton doms s).bind (singletonLit s) = some q := by
  unfold propCheckConflict
  exact List.mem_filterMap

/-- Every literal `propCheckConflict` reports sits on a slot the
constraint reads. -/
theorem propCheckConflict_atomSlot_mem {dc : DomConstraint} {doms : List Domain}
    {q : Literal} (hq : q ∈ propCheckConflict dc doms) :
    q.atom.slot ∈ dcSlotsFull dc := by
  obtain ⟨s, hs, hbind⟩ := mem_propCheckConflict_iff.mp hq
  obtain ⟨v, -, hv2⟩ := Option.bind_eq_some_iff.mp hbind
  cases v with
  | int c =>
      simp only [singletonLit] at hv2
      injection hv2 with hv2
      rw [← hv2]; simpa [posNe, Atom.slot] using hs
  | bool b =>
      simp only [singletonLit] at hv2
      injection hv2 with hv2
      rw [← hv2]; simpa [posBool, Atom.slot] using hs
  | setOfInt w => simp [singletonLit] at hv2
  | array w => simp [singletonLit] at hv2

/-- Every literal `propCheckConflict` reports is already in canonical
(normalized) form. -/
theorem propCheckConflict_literal_norm {dc : DomConstraint} {doms : List Domain}
    {q : Literal} (hq : q ∈ propCheckConflict dc doms) : q.norm = q := by
  obtain ⟨s, -, hbind⟩ := mem_propCheckConflict_iff.mp hq
  obtain ⟨v, -, hv2⟩ := Option.bind_eq_some_iff.mp hbind
  cases v with
  | int c =>
      simp only [singletonLit] at hv2
      injection hv2 with hv2
      rw [← hv2]
      rfl
  | bool b =>
      simp only [singletonLit] at hv2
      injection hv2 with hv2
      rw [← hv2]
      rfl
  | setOfInt w => simp [singletonLit] at hv2
  | array w => simp [singletonLit] at hv2

/-- **Conflict impossibility** (PLAN L0b1): when `propCheck` reports a
conflict, no assignment fitting the frame domains satisfies `dc`. -/
theorem propCheck_conflict_false {dc : DomConstraint} {st : State} {c : Clause}
    (hrun : (propCheck dc).run st = .conflict c) {a : Assignment}
    (hfits : a.Fits st.domains) (hsat : dc.SatisfiedBy a) : False := by
  obtain ⟨hready, hcheck, -⟩ := propCheck_conflict_inv hrun
  have hagree : ∀ s ∈ dcSlotsFull dc, a[s]? = (propCheckAssign st.domains)[s]? := by
    intro s hs
    have hsome : (frameSingleton st.domains s).isSome = true := List.all_eq_true.mp hready s hs
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    have hd : (st.domains.getD s Dom.empty).enum = [v] := frameSingleton_iff.mp hv
    have hslt : s < st.domains.length := by
      rcases Nat.lt_or_ge s st.domains.length with hlt | hge
      · exact hlt
      · exfalso
        have h0 : (st.domains.getD s Dom.empty).enum = [] := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr hge]
          rfl
        rw [hd] at h0
        simp at h0
    have hsa : s < a.length := by rw [hfits.1]; exact hslt
    have haget : a[s]? = some a[s] := List.getElem?_eq_getElem hsa
    have hmemw : a[s] ∈ Dom.enum (st.domains.getD s Dom.empty) := by
      have h := hfits.2 s a[s] haget
      rwa [DomainLike.mem_iff, domElems_eq_enum] at h
    rw [hd] at hmemw
    have hav : a[s]? = some v := by rw [haget]; congr 1; exact List.mem_singleton.mp hmemw
    rw [hav, propCheckAssign_getElem? hv]
  have hcong := satisfiedB_dcSlotsFull_congr dc hagree
  have hsat' : dc.satisfiedB a = true := (DomConstraint.satisfiedB_iff dc a).mpr hsat
  rw [hsat', hcheck] at hcong
  exact absurd hcong (by simp)

/-- **Conflict entailment** (PLAN L0a): no leaf solution faithful to the
frame contradicts `propCheck`'s conflict clause — equivalently, under the
gate's forced check failing, no assignment fitting the frame domains can
satisfy `dc` (the clause is vacuously entailed by that impossibility). -/
theorem propCheck_conflict_entailed {dc : DomConstraint} {st : State} {c : Clause}
    (hrun : (propCheck dc).run st = .conflict c) {a : Assignment}
    (hfits : a.Fits st.domains) (hsat : dc.SatisfiedBy a) :
    Clause.SatisfiedBy c a :=
  (propCheck_conflict_false hrun hfits hsat).elim

/-- **Faithful conflict entailment** (PLAN L0b1): every solution `a` of `dc`
faithful to the frame carries a true literal of `propCheck`'s conflict clause
(`a` need not fit the narrowed frame: it differs from the forced assignment
on some read slot, and that slot's singleton literal is then true). -/
theorem propCheck_conflict_faithful {dc : DomConstraint} {st : State} {c : Clause}
    (hrun : (propCheck dc).run st = .conflict c) {a : Assignment}
    (hfaith : FrameFaithful st.domains a) (hsat : dc.SatisfiedBy a) :
    Clause.SatisfiedBy c a := by
  refine Classical.byContradiction fun hno => ?_
  obtain ⟨hready, hcheck, hceq⟩ := propCheck_conflict_inv hrun
  have hagree : ∀ s ∈ dcSlotsFull dc, a[s]? = (propCheckAssign st.domains)[s]? := by
    intro s hs
    have hsome : (frameSingleton st.domains s).isSome = true := List.all_eq_true.mp hready s hs
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    have hd : (st.domains.getD s Dom.empty).enum = [v] := frameSingleton_iff.mp hv
    have hslt : s < st.domains.length := by
      rcases Nat.lt_or_ge s st.domains.length with hlt | hge
      · exact hlt
      · exfalso
        have h0 : (st.domains.getD s Dom.empty).enum = [] := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr hge]
          rfl
        rw [hd] at h0
        simp at h0
    obtain ⟨y, hay, -, hsort⟩ := hfaith s hslt
    have hsv : SortAgree v y := hsort v (by
      rw [DomainLike.mem_iff, domElems_eq_enum, hd]
      exact List.mem_singleton_self v)
    rw [propCheckAssign_getElem? hv, hay]
    have hmem : ∀ q, (frameSingleton st.domains s).bind (singletonLit s) = some q →
        q ∈ c := fun q hq => by
      rw [hceq]; exact mem_propCheckConflict_iff.mpr ⟨s, hs, hq⟩
    cases v with
    | int k =>
        rcases hsv with ⟨-, k', rfl⟩ | ⟨⟨b, hb⟩, -⟩
        · have hlit := hmem (posNe s k) (by rw [hv]; rfl)
          refine congrArg some (congrArg Value.int ?_)
          refine Classical.byContradiction fun hne => hno ⟨posNe s k, hlit, ?_⟩
          rw [eval_posNe_iff]
          exact ⟨k', by simp [slotInt, hay, Value.intView], fun h => hne h⟩
        · cases hb
    | bool b =>
        rcases hsv with ⟨⟨k, hk⟩, -⟩ | ⟨-, b', rfl⟩
        · cases hk
        · have hlit := hmem (posBool s (!b)) (by rw [hv]; rfl)
          refine congrArg some (congrArg Value.bool ?_)
          refine Classical.byContradiction fun hne => hno ⟨posBool s (!b), hlit, ?_⟩
          rw [eval_posBool_iff, hay]
          cases b <;> cases b' <;> simp_all
    | setOfInt w =>
        rcases hsv with ⟨⟨k, hk⟩, -⟩ | ⟨⟨b, hb⟩, -⟩
        · cases hk
        · cases hb
    | array w =>
        rcases hsv with ⟨⟨k, hk⟩, -⟩ | ⟨⟨b, hb⟩, -⟩
        · cases hk
        · cases hb
  have hcong := satisfiedB_dcSlotsFull_congr dc hagree
  have hsat' : dc.satisfiedB a = true := (DomConstraint.satisfiedB_iff dc a).mpr hsat
  rw [hsat', hcheck] at hcong
  exact absurd hcong (by simp)

end LeanFzn.Solver.Propagation.DomainFiltering

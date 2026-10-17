/-
File: LeanFzn/Solver/UIP/Proofs/LcgEmissionTyped.lean

Typed emissions of the `lcgFamB` constraint families: every literal that a
raw propagator `dcs.filterMap propagatorOfProved` emits (implied literals,
implied reasons, conflict clauses) is well-slotted, `EmissionTyped orig raw`
(see `Proofs/ClampPool.lean`).

Premises of the main theorem `emissionTyped_of_families`:
* `hfam`  : every constraint of `dcs` lies in the gate `lcgFamB`;
* `hsh`   : `ShapeTypedDomains orig` (each box domain is int-shaped or
            bool-shaped, so a nonempty domain has an integer view);
* `hslot` : every slot index a constraint of `dcs` names (`dcSlots`) is
            in range of `orig` with a nonempty domain (`SlotOK`).

Why these premises suffice: `LitWF orig l` only inspects the box `orig`
(never the state `st`) at the literal's slot, so the emitted literals are
typed as soon as their slot is `SlotOK`. A Boolean literal `boolEq s _`
needs only `s < orig.length`; an order/removal literal `intLe s _` or
`intNe s _` needs an integer view of `orig[s]`, which `SlotOK` plus
`ShapeTypedDomains` provides.

No placeholder proofs and no custom axioms.
-/
import LeanFzn.Solver.UIP.Proofs.LcgFamiliesRun
import LeanFzn.Solver.UIP.Proofs.ClampPool
import LeanFzn.Solver.UIP.Proofs.SchedulerDecision

namespace LeanFzn.Solver.UIP.LcgEmissionTyped
open LeanFzn LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP LeanFzn.Solver.UIP.ClampPool LeanFzn.Solver.UIP.LcgFamilies

/-! ## 1. Slot discipline -/

/-- A box slot is usable: in range, with a nonempty domain. Under
`ShapeTypedDomains` every value of such a domain has an integer view. -/
def SlotOK (orig : List Domain) (s : Nat) : Prop :=
  ∃ d, orig[s]? = some d ∧ d ≠ []

/-- The slots a constraint names (the slots its propagator may emit on). -/
def dcSlots : DomConstraint → List Nat
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

/-- PLAN L0b1: the slot list now covers every constructor and IS the
propagation layer's `dcSlotsFull`. -/
theorem dcSlots_eq_full : dcSlots = dcSlotsFull := by
  funext dc
  cases dc <;> rfl

/-- Result-level typing: every implied literal and its reason, and every
conflict clause, is well-slotted. -/
def ResTyped (orig : List Domain) (res : PropagationResult) : Prop :=
  (∀ l r, res = .implied l r → LitWF orig l ∧ ∀ q ∈ r.clause, LitWF orig q) ∧
  (∀ c, res = .conflict c → ∀ q ∈ c, LitWF orig q)

theorem resTyped_stable (orig : List Domain) : ResTyped orig .stable :=
  ⟨fun _ _ h => (by cases h), fun _ h => (by cases h)⟩

theorem resTyped_implied {orig : List Domain} {l : Literal} {r : Reason}
    (hl : LitWF orig l) (hr : ∀ q ∈ r.clause, LitWF orig q) :
    ResTyped orig (.implied l r) :=
  ⟨fun l' r' h => by
      injection h with h1 h2
      subst h1; subst h2
      exact ⟨hl, hr⟩,
    fun _ h => (by cases h)⟩

theorem resTyped_conflict {orig : List Domain} {c : Clause}
    (hc : ∀ q ∈ c, LitWF orig q) : ResTyped orig (.conflict c) :=
  ⟨fun _ _ h => (by cases h), fun c' h => by
      injection h with h1
      subst h1
      exact hc⟩

/-- A literal over an `SlotOK` slot is well-slotted. -/
theorem litWF_of_slotOK {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {l : Literal} (h : SlotOK orig l.atom.slot) : LitWF orig l := by
  obtain ⟨atom, pos⟩ := l
  obtain ⟨d, hd, hne⟩ := h
  have hmem : d ∈ orig := List.mem_of_getElem? hd
  have hlen : ∀ s, orig[s]? = some d → s < orig.length := fun s hs =>
    (List.getElem?_eq_some_iff.mp hs).1 |> fun h => by simpa using h
  cases atom with
  | boolEq s b => exact hlen s hd
  | intLe s k =>
      refine ⟨d, hd, ?_⟩
      obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil d hne
      have hint : ∃ x, Value.intView v = some x := by
        rcases hsh d hmem with h | h
        · obtain ⟨k', hk'⟩ := h v hv
          exact ⟨k', by rw [hk']; rfl⟩
        · obtain ⟨b', hb'⟩ := h v hv
          exact ⟨if b' then 1 else 0, by rw [hb']; cases b' <;> rfl⟩
      obtain ⟨x, hx⟩ := hint
      intro hnil
      have : x ∈ clampInts d := List.mem_filterMap.mpr ⟨v, hv, hx⟩
      rw [hnil] at this
      cases this
  | intNe s k =>
      refine ⟨d, hd, ?_⟩
      obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil d hne
      have hint : ∃ x, Value.intView v = some x := by
        rcases hsh d hmem with h | h
        · obtain ⟨k', hk'⟩ := h v hv
          exact ⟨k', by rw [hk']; rfl⟩
        · obtain ⟨b', hb'⟩ := h v hv
          exact ⟨if b' then 1 else 0, by rw [hb']; cases b' <;> rfl⟩
      obtain ⟨x, hx⟩ := hint
      intro hnil
      have : x ∈ clampInts d := List.mem_filterMap.mpr ⟨v, hv, hx⟩
      rw [hnil] at this
      cases this

/-! ## 2. Bound narrowings and their combinators -/

theorem narrowHi_typed {orig : List Domain} (hsh : ShapeTypedDomains orig)
    (st : State) {s : Nat} {hi : Int} {ng : Clause}
    (hs : SlotOK orig s) (hng : ∀ q ∈ ng, SlotOK orig q.atom.slot) :
    ResTyped orig (narrowHi st s hi ng) := by
  constructor
  · intro l r h
    obtain ⟨rfl, rfl⟩ := narrowHi_implied_inv h
    exact ⟨litWF_of_slotOK hsh hs, fun q hq => litWF_of_slotOK hsh (hng q hq)⟩
  · intro c h
    obtain ⟨-, -, -, -, -, rfl⟩ := narrowHi_conflict_inv h
    exact fun q hq => litWF_of_slotOK hsh (hng q hq)

theorem narrowLo_typed {orig : List Domain} (hsh : ShapeTypedDomains orig)
    (st : State) {s : Nat} {lo : Int} {ng : Clause}
    (hs : SlotOK orig s) (hng : ∀ q ∈ ng, SlotOK orig q.atom.slot) :
    ResTyped orig (narrowLo st s lo ng) := by
  constructor
  · intro l r h
    obtain ⟨rfl, rfl⟩ := narrowLo_implied_inv h
    exact ⟨litWF_of_slotOK hsh hs, fun q hq => litWF_of_slotOK hsh (hng q hq)⟩
  · intro c h
    obtain ⟨-, -, -, -, -, rfl⟩ := narrowLo_conflict_inv h
    exact fun q hq => litWF_of_slotOK hsh (hng q hq)

theorem resTyped_firstEvent {orig : List Domain} (rs : List PropagationResult)
    (h : ∀ r ∈ rs, ResTyped orig r) : ResTyped orig (firstEvent rs) := by
  rcases firstEvent_mem rs _ rfl with hs | hm
  · rw [hs]; exact resTyped_stable orig
  · exact h _ hm

/-- Membership helper: a slot of a singleton-or-append clause. -/
theorem slotOK_of_mem_single {orig : List Domain} {s : Nat} {q : Literal}
    (hs : SlotOK orig s) (hq : q ∈ [posLe s hi] ) : SlotOK orig q.atom.slot := by
  simp only [List.mem_singleton] at hq
  subst hq
  exact hs

/-! ## 3. Bound families (`leConstHi`, `leConstLo`, `ltConstHi`, `ltConstLo`) -/

theorem typed_leConstHi {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {i : Nat} {c : Int} (hi : SlotOK orig i) (st : State) :
    ResTyped orig (propLeConstHi st i c) :=
  narrowHi_typed hsh st hi (fun q hq => by
    simp only [List.mem_singleton] at hq
    subst hq; exact hi)

theorem typed_ltConstHi {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {i : Nat} {c : Int} (hi : SlotOK orig i) (st : State) :
    ResTyped orig (propLtConstHi st i c) :=
  narrowHi_typed hsh st hi (fun q hq => by
    simp only [List.mem_singleton] at hq
    subst hq; exact hi)

theorem typed_leConstLo {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {i : Nat} {c : Int} (hi : SlotOK orig i) (st : State) :
    ResTyped orig (propLeConstLo st i c) :=
  narrowLo_typed hsh st hi (fun q hq => by
    simp only [List.mem_singleton] at hq
    subst hq; exact hi)

theorem typed_ltConstLo {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {i : Nat} {c : Int} (hi : SlotOK orig i) (st : State) :
    ResTyped orig (propLtConstLo st i c) :=
  narrowLo_typed hsh st hi (fun q hq => by
    simp only [List.mem_singleton] at hq
    subst hq; exact hi)

/-! ## 4. `constEq` -/

theorem typed_constEq {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {i : Nat} (hi : SlotOK orig i) (v : Value) (st : State) :
    ResTyped orig (LeanFzn.Solver.Propagation.propConstEq st i v) := by
  match v with
  | .int k =>
      simp only [LeanFzn.Solver.Propagation.propConstEq]
      refine resTyped_firstEvent _ ?_
      intro r hr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl
      · exact narrowHi_typed hsh st hi (fun q hq => by
          simp only [List.mem_singleton] at hq
          subst hq; exact hi)
      · exact narrowLo_typed hsh st hi (fun q hq => by
          simp only [List.mem_singleton] at hq
          subst hq; exact hi)
  | .bool b =>
      simp only [LeanFzn.Solver.Propagation.propConstEq]
      by_cases h1 : valueMemB (Value.bool b) (st.domains.getD i []) = true
      · rw [if_pos h1]
        by_cases h2 : valuesEqB (st.domains.getD i []) [Value.bool b] = true
        · rw [if_pos h2]; exact resTyped_stable orig
        · rw [if_neg h2]
          exact resTyped_implied (litWF_of_slotOK hsh hi)
            (fun q hq => by
              simp only [List.mem_singleton] at hq
              subst hq; exact litWF_of_slotOK hsh hi)
      · rw [if_neg h1]
        exact resTyped_conflict (fun q hq => by
          simp only [List.mem_singleton] at hq
          subst hq; exact litWF_of_slotOK hsh hi)
  | .setOfInt _ => simp only [LeanFzn.Solver.Propagation.propConstEq]; exact resTyped_stable orig
  | .array _ => simp only [LeanFzn.Solver.Propagation.propConstEq]; exact resTyped_stable orig

/-! ## 5. Boolean families -/

theorem implyBool_typed {orig : List Domain} (hsh : ShapeTypedDomains orig)
    (st : State) {s : Nat} {b : Bool} {ng : Clause}
    (hs : SlotOK orig s) (hng : ∀ q ∈ ng, SlotOK orig q.atom.slot) :
    ResTyped orig (implyBool st s b ng) := by
  constructor
  · intro l r h
    obtain ⟨rfl, rfl⟩ := implyBool_implied_inv h
    exact ⟨litWF_of_slotOK hsh hs, fun q hq => litWF_of_slotOK hsh (hng q hq)⟩
  · intro c h
    obtain ⟨rfl, -⟩ := implyBool_conflict_inv h
    exact fun q hq => litWF_of_slotOK hsh (hng q hq)

theorem typed_boolNot {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {i j : Nat} (hi : SlotOK orig i) (hj : SlotOK orig j) (st : State) :
    ResTyped orig (propBoolNot st i j) := by
  rcases propBoolNot_emit (res := propBoolNot st i j) rfl with
    ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | h
  · rw [← h]
    exact implyBool_typed hsh st hi (fun q hq => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl <;> first | exact hi | exact hj)
  · rw [← h]
    exact implyBool_typed hsh st hi (fun q hq => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl <;> first | exact hi | exact hj)
  · rw [← h]
    exact implyBool_typed hsh st hj (fun q hq => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl <;> first | exact hi | exact hj)
  · rw [← h]
    exact implyBool_typed hsh st hj (fun q hq => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl <;> first | exact hi | exact hj)
  · rw [h]; exact resTyped_stable orig

/-! ## 6. Order families: `le`, `lt`, `eq`, `plus` (narrowings over two or three slots) -/

/-- Clause-slot discharge: every literal of an explicit clause list is
`SlotOK` once its slots are in context (by assumption). -/
macro "ng_ok" : tactic =>
  `(tactic| (simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, false_implies, implies_true]; and_intros <;> assumption))

theorem neBoolLit_slotOK {orig : List Domain} (p s : Nat) (c : Int)
    (hp : SlotOK orig p) (hs : SlotOK orig s) :
    SlotOK orig (neBoolLit p s c).atom.slot := by
  unfold neBoolLit
  split
  · exact hs
  · exact hp

theorem typed_le {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {i j : Nat} (hi : SlotOK orig i) (hj : SlotOK orig j) (st : State) :
    ResTyped orig (propLe st i j) := by
  unfold propLe
  split
  · refine resTyped_firstEvent _ ?_
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl
    · exact narrowHi_typed hsh _ (by assumption) (by ng_ok)
    · exact narrowLo_typed hsh _ (by assumption) (by ng_ok)
  · exact resTyped_stable orig

theorem typed_lt {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {i j : Nat} (hi : SlotOK orig i) (hj : SlotOK orig j) (st : State) :
    ResTyped orig (propLt st i j) := by
  unfold propLt
  split
  · refine resTyped_firstEvent _ ?_
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl
    · exact narrowHi_typed hsh _ (by assumption) (by ng_ok)
    · exact narrowLo_typed hsh _ (by assumption) (by ng_ok)
  · exact resTyped_stable orig

theorem typed_eq {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {i j : Nat} (hi : SlotOK orig i) (hj : SlotOK orig j) (st : State) :
    ResTyped orig (propEq st i j) := by
  unfold propEq
  split
  · refine resTyped_firstEvent _ ?_
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact narrowLo_typed hsh _ (by assumption) (by ng_ok)
    · exact narrowHi_typed hsh _ (by assumption) (by ng_ok)
    · exact narrowLo_typed hsh _ (by assumption) (by ng_ok)
    · exact narrowHi_typed hsh _ (by assumption) (by ng_ok)
  · exact resTyped_stable orig

theorem typed_plus {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {i j k : Nat} (hi : SlotOK orig i) (hj : SlotOK orig j) (hk : SlotOK orig k)
    (st : State) : ResTyped orig (propPlus st i j k) := by
  unfold propPlus
  split
  · refine resTyped_firstEvent _ ?_
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact narrowLo_typed hsh _ (by assumption) (by ng_ok)
    · exact narrowHi_typed hsh _ (by assumption) (by ng_ok)
    · exact narrowLo_typed hsh _ (by assumption) (by ng_ok)
    · exact narrowHi_typed hsh _ (by assumption) (by ng_ok)
    · exact narrowLo_typed hsh _ (by assumption) (by ng_ok)
    · exact narrowHi_typed hsh _ (by assumption) (by ng_ok)
  · exact resTyped_stable orig

/-- PLAN L3: the `minSlot` bound propagator `propMin` emits four narrowings
    (two on `k` from the `i`/`j` bounds, one each on `i`/`j` from `k`'s
    lower bound), all on `SlotOK` slots with `SlotOK` clause literals. -/
theorem typed_min {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {i j k : Nat} (hi : SlotOK orig i) (hj : SlotOK orig j) (hk : SlotOK orig k)
    (st : State) : ResTyped orig (propMin st i j k) := by
  unfold propMin
  split
  · refine resTyped_firstEvent _ ?_
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact narrowLo_typed hsh _ (by assumption) (by ng_ok)
    · exact narrowHi_typed hsh _ (by assumption) (by ng_ok)
    · exact narrowLo_typed hsh _ (by assumption) (by ng_ok)
    · exact narrowLo_typed hsh _ (by assumption) (by ng_ok)
  · exact resTyped_stable orig

/-- PLAN L3: the `maxSlot` twin of `typed_min`: two narrowings on `k` from
    the `i`/`j` bounds, two on `i`/`j` from `k`'s upper bound. -/
theorem typed_max {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {i j k : Nat} (hi : SlotOK orig i) (hj : SlotOK orig j) (hk : SlotOK orig k)
    (st : State) : ResTyped orig (propMax st i j k) := by
  unfold propMax
  split
  · refine resTyped_firstEvent _ ?_
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact narrowLo_typed hsh _ (by assumption) (by ng_ok)
    · exact narrowHi_typed hsh _ (by assumption) (by ng_ok)
    · exact narrowHi_typed hsh _ (by assumption) (by ng_ok)
    · exact narrowHi_typed hsh _ (by assumption) (by ng_ok)
  · exact resTyped_stable orig

/-- PLAN L7: the `absSlot` bound propagator `propAbs` emits five
    narrowings (one `k ≥ 0` unit, two on `k` from the `i` bounds and
    `r = |x|`, and two on `i` from `r`'s upper bound), all on `SlotOK`
    slots with `SlotOK` clause literals. -/
theorem typed_abs {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {i k : Nat} (hi : SlotOK orig i) (hk : SlotOK orig k)
    (st : State) : ResTyped orig (propAbs st i k) := by
  unfold propAbs
  split
  · refine resTyped_firstEvent _ ?_
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact narrowLo_typed hsh _ (by assumption) (by ng_ok)
    · exact narrowLo_typed hsh _ (by assumption) (by ng_ok)
    · exact narrowHi_typed hsh _ (by assumption) (by ng_ok)
    · exact narrowHi_typed hsh _ (by assumption) (by ng_ok)
    · exact narrowLo_typed hsh _ (by assumption) (by ng_ok)
  · exact resTyped_stable orig

/-- PLAN L7: the general `int_div` bound propagator `propDiv` emits only
    narrowings on the result slot `k` (pivot `k`, causes on the dividend
    slot `i` and — for a slot divisor — the divisor slot `j`), plus the
    zero-divisor conflict clause (`[]` on a literal `0`, `[o_j ≠ 0]` on a
    slot). All literals are `SlotOK`-slotted. -/
theorem typed_div {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {o₁ o₂ r : DomIntArg}
    (h₁ : ∀ s, o₁ = .slot s → SlotOK orig s)
    (h₂ : ∀ s, o₂ = .slot s → SlotOK orig s)
    (hr : ∀ s, r = .slot s → SlotOK orig s)
    (st : State) : ResTyped orig (propDiv st o₁ o₂ r) := by
  unfold propDiv
  split
  · rename_i x d hpin
    split
    · -- the zero-divisor conflict
      rename_i hd0
      cases o₂ with
      | lit d' =>
          refine resTyped_conflict ?_
          intro q hq
          simp [divZeroClause] at hq
      | slot j =>
          refine resTyped_conflict ?_
          intro q hq
          simp only [divZeroClause, List.mem_cons, List.not_mem_nil,
            or_false] at hq
          subst hq
          exact litWF_of_slotOK hsh (h₂ j rfl)
    · split
      · rename_i i k
        split
        · rename_i pl ph hpl hph
          refine resTyped_firstEvent _ ?_
          intro r' hr'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
          rcases hr' with rfl | rfl
          · -- narrowLo
            cases o₂ with
            | lit d' =>
                refine narrowLo_typed hsh _ (hr k rfl) ?_
                intro q hq
                simp only [divReasonLo] at hq
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
                rcases hq with rfl | rfl | rfl
                all_goals first
                  | exact hr k rfl
                  | exact h₂ j rfl
                  | exact h₁ i rfl
            | slot j =>
                refine narrowLo_typed hsh _ (hr k rfl) ?_
                intro q hq
                simp only [divReasonLo] at hq
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
                rcases hq with rfl | rfl | rfl | rfl | rfl
                all_goals first
                  | exact hr k rfl
                  | exact h₂ j rfl
                  | exact h₁ i rfl
          · -- narrowHi
            cases o₂ with
            | lit d' =>
                refine narrowHi_typed hsh _ (hr k rfl) ?_
                intro q hq
                simp only [divReasonHi] at hq
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
                rcases hq with rfl | rfl | rfl
                all_goals first
                  | exact hr k rfl
                  | exact h₂ j rfl
                  | exact h₁ i rfl
            | slot j =>
                refine narrowHi_typed hsh _ (hr k rfl) ?_
                intro q hq
                simp only [divReasonHi] at hq
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
                rcases hq with rfl | rfl | rfl | rfl | rfl
                all_goals first
                  | exact hr k rfl
                  | exact h₂ j rfl
                  | exact h₁ i rfl
        · exact resTyped_stable orig
      · exact resTyped_stable orig
  · exact resTyped_stable orig

/-- PLAN L7: the general `int_mod` bound propagator `propMod`, the
    `modGen` twin of `typed_div`. -/
theorem typed_mod {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {o₁ o₂ r : DomIntArg}
    (h₁ : ∀ s, o₁ = .slot s → SlotOK orig s)
    (h₂ : ∀ s, o₂ = .slot s → SlotOK orig s)
    (hr : ∀ s, r = .slot s → SlotOK orig s)
    (st : State) : ResTyped orig (propMod st o₁ o₂ r) := by
  unfold propMod
  split
  · rename_i x d hpin
    split
    · -- the zero-divisor conflict
      rename_i hd0
      cases o₂ with
      | lit d' =>
          refine resTyped_conflict ?_
          intro q hq
          simp [divZeroClause] at hq
      | slot j =>
          refine resTyped_conflict ?_
          intro q hq
          simp only [divZeroClause, List.mem_cons, List.not_mem_nil,
            or_false] at hq
          subst hq
          exact litWF_of_slotOK hsh (h₂ j rfl)
    · split
      · rename_i i k
        split
        · rename_i pl ph hpl hph
          refine resTyped_firstEvent _ ?_
          intro r' hr'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
          rcases hr' with rfl | rfl
          · -- narrowLo
            cases o₂ with
            | lit d' =>
                refine narrowLo_typed hsh _ (hr k rfl) ?_
                intro q hq
                simp only [modReasonLo] at hq
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
                rcases hq with rfl | rfl | rfl
                all_goals first
                  | exact hr k rfl
                  | exact h₂ j rfl
                  | exact h₁ i rfl
            | slot j =>
                refine narrowLo_typed hsh _ (hr k rfl) ?_
                intro q hq
                simp only [modReasonLo] at hq
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
                rcases hq with rfl | rfl | rfl | rfl | rfl
                all_goals first
                  | exact hr k rfl
                  | exact h₂ j rfl
                  | exact h₁ i rfl
          · -- narrowHi
            cases o₂ with
            | lit d' =>
                refine narrowHi_typed hsh _ (hr k rfl) ?_
                intro q hq
                simp only [modReasonHi] at hq
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
                rcases hq with rfl | rfl | rfl
                all_goals first
                  | exact hr k rfl
                  | exact h₂ j rfl
                  | exact h₁ i rfl
            | slot j =>
                refine narrowHi_typed hsh _ (hr k rfl) ?_
                intro q hq
                simp only [modReasonHi] at hq
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
                rcases hq with rfl | rfl | rfl | rfl | rfl
                all_goals first
                  | exact hr k rfl
                  | exact h₂ j rfl
                  | exact h₁ i rfl
        · exact resTyped_stable orig
      · exact resTyped_stable orig
  · exact resTyped_stable orig

theorem argLoCause_slotOK {orig : List Domain} {st : State} (os : List DomIntArg)
    (hslots : ∀ o ∈ os, ∀ i ∈ DomIntArg.slots o, SlotOK orig i) :
    ∀ q ∈ os.flatMap (argLoCause st), SlotOK orig q.atom.slot := by
  intro q hq
  obtain ⟨o, ho, hq2⟩ := List.mem_flatMap.mp hq
  cases o with
  | lit k => cases hq2
  | slot i =>
      cases hl : domMinI (st.domains.getD i []) with
      | none =>
          rw [argLoCause_slot_none hl] at hq2
          cases hq2
      | some l =>
          rw [argLoCause_slot_some hl] at hq2
          rw [List.mem_singleton] at hq2
          rw [hq2]
          exact hslots (.slot i) ho i (by simp [DomIntArg.slots])

/-- PLAN C9c: the upper-bound causes of an operand list name only `SlotOK`
    slots. -/
theorem argHiCause_slotOK {orig : List Domain} {st : State} (os : List DomIntArg)
    (hslots : ∀ o ∈ os, ∀ i ∈ DomIntArg.slots o, SlotOK orig i) :
    ∀ q ∈ os.flatMap (argHiCause st), SlotOK orig q.atom.slot := by
  intro q hq
  obtain ⟨o, ho, hq2⟩ := List.mem_flatMap.mp hq
  cases o with
  | lit k => cases hq2
  | slot i =>
      cases hh : domMaxI (st.domains.getD i []) with
      | none =>
          rw [argHiCause_slot_none hh] at hq2
          cases hq2
      | some h =>
          rw [argHiCause_slot_some hh] at hq2
          rw [List.mem_singleton] at hq2
          rw [hq2]
          exact hslots (.slot i) ho i (by simp [DomIntArg.slots])

/-- PLAN C9c: a clause whose head and tail literals name `SlotOK` slots. -/
theorem clauseSlotOK_cons {orig : List Domain} {q : Literal} {c : Clause}
    (hq : SlotOK orig q.atom.slot) (hc : ∀ q' ∈ c, SlotOK orig q'.atom.slot) :
    ∀ q' ∈ q :: c, SlotOK orig q'.atom.slot := by
  intro q' hq'
  rcases List.mem_cons.mp hq' with rfl | hq'
  · exact hq
  · exact hc q' hq'

/-- PLAN C9c: the `minGen` result propagator is slot-typed: its emitted
    literals are order literals over the result slot and the operand
    slots. -/
theorem typed_minGen {orig : List Domain} (hsh : ShapeTypedDomains orig)
    (os : List DomIntArg) (r : DomIntArg)
    (hr : ∀ i ∈ r.slots, SlotOK orig i)
    (hslots : ∀ o ∈ os, ∀ i ∈ DomIntArg.slots o, SlotOK orig i)
    (st : State) : ResTyped orig (propMinGen st os r) := by
  unfold propMinGen
  split
  case h_1 => exact resTyped_stable orig
  case h_2 =>
    rename_i r' k
    split
    case h_1 =>
      rename_i m_lo m_hi hlo hhi
      refine resTyped_firstEvent _ ?_
      intro rr hrr
      rcases List.mem_cons.mp hrr with rfl | hrr
      · exact narrowLo_typed hsh st
          (by simpa [DomIntArg.slots] using hr k (by simp [DomIntArg.slots]))
          (clauseSlotOK_cons
            (by simpa [negLe, Atom.slot] using hr k (by simp [DomIntArg.slots]))
            (argLoCause_slotOK os hslots))
      · rw [List.mem_singleton] at hrr
        rw [hrr]
        exact narrowHi_typed hsh st
          (by simpa [DomIntArg.slots] using hr k (by simp [DomIntArg.slots]))
          (clauseSlotOK_cons
            (by simpa [posLe, Atom.slot] using hr k (by simp [DomIntArg.slots]))
            (argHiCause_slotOK os hslots))
    case h_2 => exact resTyped_stable orig

/-- PLAN C9c: the `maxGen` twin of `typed_minGen`. -/
theorem typed_maxGen {orig : List Domain} (hsh : ShapeTypedDomains orig)
    (os : List DomIntArg) (r : DomIntArg)
    (hr : ∀ i ∈ r.slots, SlotOK orig i)
    (hslots : ∀ o ∈ os, ∀ i ∈ DomIntArg.slots o, SlotOK orig i)
    (st : State) : ResTyped orig (propMaxGen st os r) := by
  unfold propMaxGen
  split
  case h_1 => exact resTyped_stable orig
  case h_2 =>
    rename_i r' k
    split
    case h_1 =>
      rename_i m_lo m_hi hlo hhi
      refine resTyped_firstEvent _ ?_
      intro rr hrr
      rcases List.mem_cons.mp hrr with rfl | hrr
      · exact narrowLo_typed hsh st
          (by simpa [DomIntArg.slots] using hr k (by simp [DomIntArg.slots]))
          (clauseSlotOK_cons
            (by simpa [negLe, Atom.slot] using hr k (by simp [DomIntArg.slots]))
            (argLoCause_slotOK os hslots))
      · rw [List.mem_singleton] at hrr
        rw [hrr]
        exact narrowHi_typed hsh st
          (by simpa [DomIntArg.slots] using hr k (by simp [DomIntArg.slots]))
          (clauseSlotOK_cons
            (by simpa [posLe, Atom.slot] using hr k (by simp [DomIntArg.slots]))
            (argHiCause_slotOK os hslots))
    case h_2 => exact resTyped_stable orig

/-- PLAN L6: the `timesSlot` bound propagator `propTimes` emits two corner
    narrowings on `k` and eight guarded sign narrowings on `i`/`j`, all on
    `SlotOK` slots with `SlotOK` clause literals. -/
theorem typed_times {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {i j k : Nat} (hi : SlotOK orig i) (hj : SlotOK orig j) (hk : SlotOK orig k)
    (st : State) : ResTyped orig (propTimes st i j k) := by
  unfold propTimes
  split
  · refine resTyped_firstEvent _ ?_
    intro r hr
    rcases times_sign_arm hr with hcorner | hcorner |
      ⟨-, -, hr⟩ | ⟨-, -, hr⟩ | ⟨-, -, hr⟩ | ⟨-, -, hr⟩ |
      ⟨-, -, hr⟩ | ⟨-, -, hr⟩ | ⟨-, -, hr⟩ | ⟨-, -, hr⟩
    · rw [hcorner]
      exact narrowLo_typed hsh st hk (by ng_ok)
    · rw [hcorner]
      exact narrowHi_typed hsh st hk (by ng_ok)
    · rw [hr]
      exact narrowLo_typed hsh st hi (by ng_ok)
    · rw [hr]
      exact narrowHi_typed hsh st hi (by ng_ok)
    · rw [hr]
      exact narrowHi_typed hsh st hi (by ng_ok)
    · rw [hr]
      exact narrowLo_typed hsh st hi (by ng_ok)
    · rw [hr]
      exact narrowLo_typed hsh st hj (by ng_ok)
    · rw [hr]
      exact narrowHi_typed hsh st hj (by ng_ok)
    · rw [hr]
      exact narrowHi_typed hsh st hj (by ng_ok)
    · rw [hr]
      exact narrowLo_typed hsh st hj (by ng_ok)
  · exact resTyped_stable orig

/-! ## 7. `ne` (value removal) -/

theorem typed_ne {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {i j : Nat} (hi : SlotOK orig i) (hj : SlotOK orig j) (st : State) :
    ResTyped orig (propNe st i j) := by
  constructor
  · intro l r h
    rcases propNe_implied_inv h with
      ⟨x, c, -, rfl, rfl, -, -, -, -⟩ | ⟨y, c, -, rfl, rfl, -, -, -, -⟩
    · refine ⟨litWF_of_slotOK hsh hj, fun q hq => litWF_of_slotOK hsh ?_⟩
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl
      · exact hj
      · exact hi
      · exact hi
      · exact neBoolLit_slotOK _ _ _ hi hi
      · exact neBoolLit_slotOK _ _ _ hi hj
    · refine ⟨litWF_of_slotOK hsh hi, fun q hq => litWF_of_slotOK hsh ?_⟩
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl
      · exact hi
      · exact hj
      · exact hj
      · exact neBoolLit_slotOK _ _ _ hj hj
      · exact neBoolLit_slotOK _ _ _ hj hi
  · intro c h
    obtain ⟨x, y, -, -, -, rfl⟩ := propNe_conflict_inv h
    intro q hq
    apply litWF_of_slotOK hsh
    cases x <;> simp only [neConflictClause, List.mem_cons, List.mem_nil_iff, or_false] at hq <;>
      rcases hq with rfl | rfl <;> first | exact hi | exact hj

/-! ## 8. `allDiff` (only the pigeonhole Hall conflict is ever emitted) -/

theorem slotHall_slot {s : Nat} {d : Domain} {cl : Clause}
    (h : slotHall s d = some cl) : ∀ q ∈ cl, q.atom.slot = s := by
  unfold slotHall at h
  split at h
  · cases h
  · split at h
    · cases h
    · dsimp only at h
      split at h
      · cases h
      · injection h with h1
        subst h1
        intro q hq
        simp only [List.mem_cons, List.mem_map] at hq
        rcases hq with rfl | rfl | ⟨a, -, rfl⟩
        · rfl
        · rfl
        · rfl

theorem hallClauses_slot : ∀ (doms : List Domain) (ss : List Nat) (c : Clause),
    hallClauses doms ss = some c → ∀ q ∈ c, q.atom.slot ∈ ss := by
  intro doms ss
  induction ss with
  | nil =>
      intro c h q hq
      simp only [hallClauses, Option.some.injEq] at h
      subst h
      cases hq
  | cons s ss ih =>
      intro c h q hq
      unfold hallClauses at h
      split at h
      · rename_i c1 c2 h1 h2
        injection h with h3
        subst h3
        rcases List.mem_append.mp hq with hq1 | hq2
        · rw [slotHall_slot h1 q hq1]
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih c2 h2 q hq2)
      · cases h

theorem hallClause_slot_mem (doms : List Domain) (is : List Nat) (q : Literal)
    (hq : q ∈ hallClause doms is) : q.atom.slot ∈ is := by
  unfold hallClause at hq
  split at hq
  · rename_i c hc
    have := hallClauses_slot doms _ c hc q hq
    exact (List.mem_filter.mp this).1
  · cases hq

theorem typed_allDiff {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {is : List Nat} (hslot : ∀ s ∈ is, SlotOK orig s) (st : State) :
    ResTyped orig (propAllDiffLCG st is) := by
  constructor
  · intro l r h
    obtain ⟨i, j, c, hf, hl, hr⟩ := propAllDiffLCG_implied_inv h
    obtain ⟨hi, -, hj, -⟩ := allDiffElimFirst_spec hf
    subst hl
    subst hr
    refine ⟨litWF_of_slotOK hsh (hslot j hj), fun q hq => ?_⟩
    rcases allDiffElimClause_slot hq with hq' | hq'
    · exact litWF_of_slotOK hsh (by rw [hq']; exact hslot i hi)
    · exact litWF_of_slotOK hsh (by rw [hq']; exact hslot j hj)
  · intro c h
    obtain ⟨-, rfl⟩ := propAllDiffLCG_conflict_inv h
    intro q hq
    exact litWF_of_slotOK hsh (hslot _ (hallClause_slot_mem st.domains is q hq))

/-! ## 9. Boolean `and` / `or` (the pin-branch implications) -/

theorem typed_boolAnd {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {i j k : Nat} (hi : SlotOK orig i) (hj : SlotOK orig j) (hk : SlotOK orig k)
    (st : State) : ResTyped orig (propBoolAnd st i j k) := by
  rcases propBoolAnd_emit (res := propBoolAnd st i j k) rfl with
    ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | h
  · rw [← h]; exact implyBool_typed hsh st (by assumption) (by ng_ok)
  · rw [← h]; exact implyBool_typed hsh st (by assumption) (by ng_ok)
  · rw [← h]; exact implyBool_typed hsh st (by assumption) (by ng_ok)
  · rw [← h]; exact implyBool_typed hsh st (by assumption) (by ng_ok)
  · rw [← h]; exact implyBool_typed hsh st (by assumption) (by ng_ok)
  · rw [h]; exact resTyped_stable orig

theorem typed_boolOr {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {i j k : Nat} (hi : SlotOK orig i) (hj : SlotOK orig j) (hk : SlotOK orig k)
    (st : State) : ResTyped orig (propBoolOr st i j k) := by
  rcases propBoolOr_emit (res := propBoolOr st i j k) rfl with
    ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | h
  · rw [← h]; exact implyBool_typed hsh st (by assumption) (by ng_ok)
  · rw [← h]; exact implyBool_typed hsh st (by assumption) (by ng_ok)
  · rw [← h]; exact implyBool_typed hsh st (by assumption) (by ng_ok)
  · rw [← h]; exact implyBool_typed hsh st (by assumption) (by ng_ok)
  · rw [← h]; exact implyBool_typed hsh st (by assumption) (by ng_ok)
  · rw [h]; exact resTyped_stable orig

/-! ## 10. Linear families (`linLe`, `linEq`) -/

theorem linCauseMinPair_slot {st : State} {p : Int × Nat} {q : Literal}
    (h : linCauseMinPair st p = some q) : q.atom.slot = p.2 := by
  unfold linCauseMinPair at h
  split at h
  · cases hd : domMinI (st.domains.getD p.2 []) with
    | none => rw [hd] at h; simp at h
    | some mn => rw [hd] at h; simp at h; subst h; rfl
  · split at h
    · cases hd : domMaxI (st.domains.getD p.2 []) with
      | none => rw [hd] at h; simp at h
      | some mx => rw [hd] at h; simp at h; subst h; rfl
    · cases h

theorem linCauseMaxPair_slot {st : State} {p : Int × Nat} {q : Literal}
    (h : linCauseMaxPair st p = some q) : q.atom.slot = p.2 := by
  unfold linCauseMaxPair at h
  split at h
  · cases hd : domMaxI (st.domains.getD p.2 []) with
    | none => rw [hd] at h; simp at h
    | some mx => rw [hd] at h; simp at h; subst h; rfl
  · split at h
    · cases hd : domMinI (st.domains.getD p.2 []) with
      | none => rw [hd] at h; simp at h
      | some mn => rw [hd] at h; simp at h; subst h; rfl
    · cases h

theorem linCausesMin_slotOK {orig : List Domain} (st : State)
    {rest : List (Int × Nat)} (hrest : ∀ p ∈ rest, SlotOK orig p.2) :
    ∀ q ∈ linCausesMin st rest, SlotOK orig q.atom.slot := by
  intro q hq
  unfold linCausesMin at hq
  obtain ⟨p, hp, hpq⟩ := List.mem_filterMap.mp hq
  rw [linCauseMinPair_slot hpq]
  exact hrest p hp

theorem linCausesMax_slotOK {orig : List Domain} (st : State)
    {rest : List (Int × Nat)} (hrest : ∀ p ∈ rest, SlotOK orig p.2) :
    ∀ q ∈ linCausesMax st rest, SlotOK orig q.atom.slot := by
  intro q hq
  unfold linCausesMax at hq
  obtain ⟨p, hp, hpq⟩ := List.mem_filterMap.mp hq
  rw [linCauseMaxPair_slot hpq]
  exact hrest p hp

theorem narrowHi_cause_typed {orig : List Domain} (hsh : ShapeTypedDomains orig)
    (st : State) {s : Nat} {v : Int} {cs : Clause} (hs : SlotOK orig s)
    (hcs : ∀ q ∈ cs, SlotOK orig q.atom.slot) :
    ResTyped orig (narrowHi st s v ([posLe s v] ++ cs)) :=
  narrowHi_typed hsh st hs (fun q hq => by
    rcases List.mem_append.mp hq with h | h
    · rw [List.mem_singleton.mp h]; exact hs
    · exact hcs q h)

theorem narrowLo_cause_typed {orig : List Domain} (hsh : ShapeTypedDomains orig)
    (st : State) {s : Nat} {v : Int} {cs : Clause} (hs : SlotOK orig s)
    (hcs : ∀ q ∈ cs, SlotOK orig q.atom.slot) :
    ResTyped orig (narrowLo st s v ([negLe s (v - 1)] ++ cs)) :=
  narrowLo_typed hsh st hs (fun q hq => by
    rcases List.mem_append.mp hq with h | h
    · rw [List.mem_singleton.mp h]; exact hs
    · exact hcs q h)

/-- The solver-side slot of a linear term's rest list: every rest entry's
slot is one of `is`. -/
theorem rest_slot_ok {orig : List Domain} {coeffs : List Int} {is : List Nat}
    {i : Nat} (hslot : ∀ s ∈ is, SlotOK orig s)
    {rest : List (Int × Nat)}
    (hrest : rest = (((coeffs.zip is).zipIdx.filter
      (fun q => q.2 != i)).map (·.1))) :
    ∀ p ∈ rest, SlotOK orig p.2 := by
  subst hrest
  intro p hp
  obtain ⟨a, b⟩ := p
  exact hslot _ (List.of_mem_zip (lin2_others_mem_zip hp)).2

theorem arm_hi_min {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {coeffs : List Int} {is : List Nat} {i m : Nat} {c : Int}
    {rest : List (Int × Nat)} {st : State} {res : PropagationResult} {v : Int}
    (hslot : ∀ s ∈ is, SlotOK orig s)
    (hmem : ((c, m), i) ∈ (coeffs.zip is).zipIdx)
    (hrest : rest = (((coeffs.zip is).zipIdx.filter
      (fun q => q.2 != i)).map (·.1)))
    (hres : res = narrowHi st m v ([posLe m v] ++ linCausesMin st rest)) :
    ResTyped orig res := by
  subst hres
  exact narrowHi_cause_typed hsh st
    (hslot m (List.of_mem_zip (lin2_mem_zip_of_zipIdx _ 0 _ hmem)).2)
    (linCausesMin_slotOK st (rest_slot_ok hslot hrest))

theorem arm_hi_max {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {coeffs : List Int} {is : List Nat} {i m : Nat} {c : Int}
    {rest : List (Int × Nat)} {st : State} {res : PropagationResult} {v : Int}
    (hslot : ∀ s ∈ is, SlotOK orig s)
    (hmem : ((c, m), i) ∈ (coeffs.zip is).zipIdx)
    (hrest : rest = (((coeffs.zip is).zipIdx.filter
      (fun q => q.2 != i)).map (·.1)))
    (hres : res = narrowHi st m v ([posLe m v] ++ linCausesMax st rest)) :
    ResTyped orig res := by
  subst hres
  exact narrowHi_cause_typed hsh st
    (hslot m (List.of_mem_zip (lin2_mem_zip_of_zipIdx _ 0 _ hmem)).2)
    (linCausesMax_slotOK st (rest_slot_ok hslot hrest))

theorem arm_lo_min {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {coeffs : List Int} {is : List Nat} {i m : Nat} {c : Int}
    {rest : List (Int × Nat)} {st : State} {res : PropagationResult} {v : Int}
    (hslot : ∀ s ∈ is, SlotOK orig s)
    (hmem : ((c, m), i) ∈ (coeffs.zip is).zipIdx)
    (hrest : rest = (((coeffs.zip is).zipIdx.filter
      (fun q => q.2 != i)).map (·.1)))
    (hres : res = narrowLo st m v ([negLe m (v - 1)] ++ linCausesMin st rest)) :
    ResTyped orig res := by
  subst hres
  exact narrowLo_cause_typed hsh st
    (hslot m (List.of_mem_zip (lin2_mem_zip_of_zipIdx _ 0 _ hmem)).2)
    (linCausesMin_slotOK st (rest_slot_ok hslot hrest))

theorem arm_lo_max {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {coeffs : List Int} {is : List Nat} {i m : Nat} {c : Int}
    {rest : List (Int × Nat)} {st : State} {res : PropagationResult} {v : Int}
    (hslot : ∀ s ∈ is, SlotOK orig s)
    (hmem : ((c, m), i) ∈ (coeffs.zip is).zipIdx)
    (hrest : rest = (((coeffs.zip is).zipIdx.filter
      (fun q => q.2 != i)).map (·.1)))
    (hres : res = narrowLo st m v ([negLe m (v - 1)] ++ linCausesMax st rest)) :
    ResTyped orig res := by
  subst hres
  exact narrowLo_cause_typed hsh st
    (hslot m (List.of_mem_zip (lin2_mem_zip_of_zipIdx _ 0 _ hmem)).2)
    (linCausesMax_slotOK st (rest_slot_ok hslot hrest))

theorem typed_linLe {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {coeffs : List Int} {is : List Nat} {b : Int}
    (hslot : ∀ s ∈ is, SlotOK orig s) (st : State) :
    ResTyped orig (propLinLe2 st coeffs is b) := by
  rcases propLinLe2_emission_inv (res := propLinLe2 st coeffs is b) rfl with
    hs | ⟨m, i, rest, lr, hmem, hrest, -, -, hres⟩ | ⟨m, i, rest, lr, hmem, hrest, -, -, hres⟩ |
    ⟨m, i, rest, lr, c, hmem, -, hrest, -, -, hres⟩ | ⟨m, i, rest, lr, c, hmem, -, hrest, -, -, hres⟩
  · rw [hs]; exact resTyped_stable orig
  · exact arm_hi_min hsh hslot hmem hrest hres
  · exact arm_lo_min hsh hslot hmem hrest hres
  · exact arm_hi_min hsh hslot hmem hrest hres
  · exact arm_lo_min hsh hslot hmem hrest hres

/-- PLAN L2: `propLinNe` emits value-removal literals over operand slots. -/
theorem typed_linNe {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {coeffs : List Int} {is : List Nat} {b : Int}
    (hslot : ∀ s ∈ is, SlotOK orig s) (st : State) :
    ResTyped orig (propLinNe st coeffs is b) := by
  have hcauses : ∀ q ∈ linNeCauses st.domains (coeffs.zip is), LitWF orig q := by
    intro q hq
    obtain ⟨c, s, v, hm, -, rfl⟩ := linNeCauses_mem.mp hq
    exact litWF_of_slotOK hsh (hslot s (List.of_mem_zip hm).2)
  cases hres : propLinNe st coeffs is b with
  | stable => exact resTyped_stable orig
  | implied l rs =>
      obtain ⟨-, c, m, hfree, -, -, -, hl, hrs⟩ := propLinNe_implied_inv hres
      have hm : m ∈ is := by
        have := (linNeFree_mem (by rw [hfree]; exact List.mem_singleton_self (c, m))).1
        exact (List.of_mem_zip this).2
      subst hl
      subst hrs
      refine resTyped_implied (litWF_of_slotOK hsh (hslot m hm)) ?_
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact litWF_of_slotOK hsh (hslot m hm)
      · exact hcauses q hq
  | conflict cc =>
      obtain ⟨-, -, -, hcl⟩ := propLinNe_conflict_inv hres
      subst hcl
      exact resTyped_conflict hcauses

theorem typed_linLeReif {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {coeffs : List Int} {is : List Nat} {b : Int} {r : Nat}
    (hslot : ∀ s ∈ is, SlotOK orig s) (hslotR : SlotOK orig r) (st : State) :
    ResTyped orig (propLinLeReif st coeffs is b r) := by
  by_cases hlenB : (coeffs.length == is.length) = true
  · by_cases h1 : domBoolPin st.domains r true = true
    · rw [propLinLeReif_run_true hlenB h1]
      refine ⟨?_, ?_⟩
      · intro l rs hrun
        obtain ⟨rs0, hres, hcl⟩ := augmentRes_implied_inv hrun
        obtain ⟨hl, hr⟩ := (typed_linLe hsh hslot st).1 l rs0 hres
        refine ⟨hl, ?_⟩
        intro q hq
        rw [hcl] at hq
        rcases mem_insertAfterHead hq with hq | hq
        · exact hr q hq
        · simp only [linLeReifEscTrue, List.mem_singleton] at hq
          rw [hq]
          exact litWF_of_slotOK hsh hslotR
      · intro c hrun q hq
        obtain ⟨c0, hres, hcl⟩ := augmentRes_conflict_inv hrun
        rw [hcl] at hq
        rcases mem_insertAfterHead hq with hq | hq
        · exact (typed_linLe hsh hslot st).2 c0 hres q hq
        · simp only [linLeReifEscTrue, List.mem_singleton] at hq
          rw [hq]
          exact litWF_of_slotOK hsh hslotR
    · by_cases h2 : (domBoolPin st.domains r false
          && domsIntOnlyB st.domains is) = true
      · rw [propLinLeReif_run_false hlenB h1 h2]
        refine ⟨fun l rs hrun => (conflictsOnly_implied_elim hrun).elim, ?_⟩
        intro c hrun q hq
        obtain ⟨c0, hres, hcl⟩ :=
          augmentRes_conflict_inv (conflictsOnly_conflict_inv hrun)
        rw [hcl] at hq
        rcases mem_insertAfterHead hq with hq | hq
        · exact (typed_linLe hsh hslot st).2 c0 hres q hq
        · rw [linLeReifEscFalse] at hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact litWF_of_slotOK hsh hslotR
          · obtain ⟨i, hi, hq2⟩ := List.mem_flatMap.mp hq
            rcases List.mem_cons.mp hq2 with rfl | hq2
            · exact litWF_of_slotOK hsh (hslot i hi)
            · rw [List.mem_singleton.mp hq2]
              exact litWF_of_slotOK hsh (hslot i hi)
      · -- PLAN L1b: the bounds arm's implied pin, operand escapes and
        -- max-causes
        rw [propLinLeReif_run_b hlenB h1 h2]
        rcases propLinLeReifB_emission_inv
            (res := propLinLeReifB st coeffs is b r) rfl with
          hstable | ⟨-, -, -, -, -, -, -, -, hres⟩
        · rw [hstable]
          exact resTyped_stable orig
        · rw [hres]
          refine resTyped_implied (litWF_of_slotOK hsh hslotR) ?_
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact litWF_of_slotOK hsh hslotR
          · rcases List.mem_append.mp hq with hq | hq
            · rw [linLeReifEscB] at hq
              obtain ⟨i, hi, hq2⟩ := List.mem_flatMap.mp hq
              rcases List.mem_cons.mp hq2 with rfl | hq2
              · exact litWF_of_slotOK hsh (hslot i hi)
              · rw [List.mem_singleton.mp hq2]
                exact litWF_of_slotOK hsh (hslot i hi)
            · exact litWF_of_slotOK hsh
                (linCausesMax_slotOK st (fun p hp => hslot p.2 (mem_zip_snd hp))
                  q hq)
  · rw [propLinLeReif_run_arity (Bool.eq_false_iff.mpr hlenB)]
    exact resTyped_stable orig

theorem resTyped_augment {orig : List Domain} {res : PropagationResult}
    {extras : Clause} (h : ResTyped orig res) (he : ∀ q ∈ extras, LitWF orig q) :
    ResTyped orig (augmentRes extras res) := by
  refine ⟨?_, ?_⟩
  · intro l rs hrun
    obtain ⟨rs0, hres, hcl⟩ := augmentRes_implied_inv hrun
    obtain ⟨hl, hr⟩ := h.1 l rs0 hres
    refine ⟨hl, ?_⟩
    intro q hq
    rw [hcl] at hq
    rcases mem_insertAfterHead hq with hq | hq
    · exact hr q hq
    · exact he q hq
  · intro c hrun q hq
    obtain ⟨c0, hres, hcl⟩ := augmentRes_conflict_inv hrun
    rw [hcl] at hq
    rcases mem_insertAfterHead hq with hq | hq
    · exact h.2 c0 hres q hq
    · exact he q hq

/-- PLAN L4: `propLeReifSlot` emits well-slotted literals. -/
theorem typed_leReifSlot {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {i j r : Nat} (hi : SlotOK orig i) (hj : SlotOK orig j) (hr : SlotOK orig r)
    (st : State) : ResTyped orig (propLeReifSlot st i j r) := by
  rcases propLeReifSlot_cases st i j r with ⟨h1, he⟩ | ⟨h1, h2, he⟩ | he
  · rw [he]
    exact resTyped_augment (typed_le hsh hi hj st) (fun q hq => by
      rw [List.mem_singleton.mp hq]; exact litWF_of_slotOK hsh hr)
  · rw [he]
    exact resTyped_augment (typed_lt hsh hj hi st) (fun q hq => by
      rw [List.mem_singleton.mp hq]; exact litWF_of_slotOK hsh hr)
  · rw [he]; exact resTyped_stable orig

/-- PLAN L4: `propEqReifSlot` emits well-slotted literals. -/
theorem typed_eqReifSlot {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {i j r : Nat} (hi : SlotOK orig i) (hj : SlotOK orig j) (hr : SlotOK orig r)
    (st : State) : ResTyped orig (propEqReifSlot st i j r) := by
  rcases propEqReifSlot_cases st i j r with ⟨h1, he⟩ | ⟨h1, h2, he⟩ | he
  · rw [he]
    exact resTyped_augment (typed_eq hsh hi hj st) (fun q hq => by
      rw [List.mem_singleton.mp hq]; exact litWF_of_slotOK hsh hr)
  · rw [he]
    exact resTyped_augment (typed_ne hsh hi hj st) (fun q hq => by
      rw [List.mem_singleton.mp hq]; exact litWF_of_slotOK hsh hr)
  · rw [he]; exact resTyped_stable orig

/-- PLAN L4: `propNeReifSlot` emits well-slotted literals. -/
theorem typed_neReifSlot {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {i j r : Nat} (hi : SlotOK orig i) (hj : SlotOK orig j) (hr : SlotOK orig r)
    (st : State) : ResTyped orig (propNeReifSlot st i j r) := by
  rcases propNeReifSlot_cases st i j r with ⟨h1, he⟩ | ⟨h1, h2, he⟩ | he
  · rw [he]
    exact resTyped_augment (typed_ne hsh hi hj st) (fun q hq => by
      rw [List.mem_singleton.mp hq]; exact litWF_of_slotOK hsh hr)
  · rw [he]
    exact resTyped_augment (typed_eq hsh hi hj st) (fun q hq => by
      rw [List.mem_singleton.mp hq]; exact litWF_of_slotOK hsh hr)
  · rw [he]; exact resTyped_stable orig

theorem typed_linEq {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {coeffs : List Int} {is : List Nat} {b : Int}
    (hslot : ∀ s ∈ is, SlotOK orig s) (st : State) :
    ResTyped orig (propLinEq2 st coeffs is b) := by
  rcases propLinEq2_emission_inv (res := propLinEq2 st coeffs is b) rfl with
    hs | ⟨m, i, rest, lr, hmem, hrest, -, -, hres⟩ | ⟨m, i, rest, hr, hmem, hrest, -, -, hres⟩ |
    ⟨m, i, rest, lr, hmem, hrest, -, -, hres⟩ | ⟨m, i, rest, hr, hmem, hrest, -, -, hres⟩ |
    ⟨m, i, rest, lr, c, hmem, -, hrest, -, -, hres⟩ | ⟨m, i, rest, hr, c, hmem, -, hrest, -, -, hres⟩ |
    ⟨m, i, rest, lr, c, hmem, -, hrest, -, -, hres⟩ | ⟨m, i, rest, hr, c, hmem, -, hrest, -, -, hres⟩
  · rw [hs]; exact resTyped_stable orig
  · exact arm_hi_min hsh hslot hmem hrest hres
  · exact arm_lo_max hsh hslot hmem hrest hres
  · exact arm_lo_min hsh hslot hmem hrest hres
  · exact arm_hi_max hsh hslot hmem hrest hres
  · exact arm_hi_min hsh hslot hmem hrest hres
  · exact arm_lo_max hsh hslot hmem hrest hres
  · exact arm_lo_min hsh hslot hmem hrest hres
  · exact arm_hi_max hsh hslot hmem hrest hres

/-- PLAN L5: `propLinEqReif` emits well-slotted literals (the delegated
    `propLinEq2`/`propLinNe` clauses plus the L1a pin/typing escapes). -/
theorem typed_linEqReif {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {coeffs : List Int} {is : List Nat} {b : Int} {r : Nat}
    (hslot : ∀ s ∈ is, SlotOK orig s) (hslotR : SlotOK orig r) (st : State) :
    ResTyped orig (propLinEqReif st coeffs is b r) := by
  by_cases hlenB : (coeffs.length == is.length) = true
  · by_cases h1 : domBoolPin st.domains r true = true
    · rw [propLinEqReif_run_true hlenB h1]
      refine ⟨?_, ?_⟩
      · intro l rs hrun
        obtain ⟨rs0, hres, hcl⟩ := augmentRes_implied_inv hrun
        obtain ⟨hl, hr⟩ := (typed_linEq hsh hslot st).1 l rs0 hres
        refine ⟨hl, ?_⟩
        intro q hq
        rw [hcl] at hq
        rcases mem_insertAfterHead hq with hq | hq
        · exact hr q hq
        · simp only [linLeReifEscTrue, List.mem_singleton] at hq
          rw [hq]
          exact litWF_of_slotOK hsh hslotR
      · intro c hrun q hq
        obtain ⟨c0, hres, hcl⟩ := augmentRes_conflict_inv hrun
        rw [hcl] at hq
        rcases mem_insertAfterHead hq with hq | hq
        · exact (typed_linEq hsh hslot st).2 c0 hres q hq
        · simp only [linLeReifEscTrue, List.mem_singleton] at hq
          rw [hq]
          exact litWF_of_slotOK hsh hslotR
    · by_cases h2 : (domBoolPin st.domains r false
          && domsIntOnlyB st.domains is) = true
      · rw [propLinEqReif_run_false hlenB h1 h2]
        refine ⟨fun l rs hrun => (conflictsOnly_implied_elim hrun).elim, ?_⟩
        intro c hrun q hq
        obtain ⟨c0, hres, hcl⟩ :=
          augmentRes_conflict_inv (conflictsOnly_conflict_inv hrun)
        rw [hcl] at hq
        rcases mem_insertAfterHead hq with hq | hq
        · exact (typed_linNe hsh hslot st).2 c0 hres q hq
        · rw [linLeReifEscFalse] at hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact litWF_of_slotOK hsh hslotR
          · obtain ⟨i, hi, hq2⟩ := List.mem_flatMap.mp hq
            rcases List.mem_cons.mp hq2 with rfl | hq2
            · exact litWF_of_slotOK hsh (hslot i hi)
            · rw [List.mem_singleton.mp hq2]
              exact litWF_of_slotOK hsh (hslot i hi)
      · rw [propLinEqReif_run_stable hlenB h1 h2]
        exact resTyped_stable orig
  · rw [propLinEqReif_run_arity (Bool.eq_false_iff.mpr hlenB)]
    exact resTyped_stable orig

/-- PLAN L5: `propLinNeReif` emits well-slotted literals (the delegated
    `propLinNe`/`propLinEq2` clauses plus the L1a pin/typing escapes). -/
theorem typed_linNeReif {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {coeffs : List Int} {is : List Nat} {b : Int} {r : Nat}
    (hslot : ∀ s ∈ is, SlotOK orig s) (hslotR : SlotOK orig r) (st : State) :
    ResTyped orig (propLinNeReif st coeffs is b r) := by
  by_cases hlenB : (coeffs.length == is.length) = true
  · by_cases h1 : domBoolPin st.domains r true = true
    · rw [propLinNeReif_run_true hlenB h1]
      refine ⟨?_, ?_⟩
      · intro l rs hrun
        obtain ⟨rs0, hres, hcl⟩ := augmentRes_implied_inv hrun
        obtain ⟨hl, hr⟩ := (typed_linNe hsh hslot st).1 l rs0 hres
        refine ⟨hl, ?_⟩
        intro q hq
        rw [hcl] at hq
        rcases mem_insertAfterHead hq with hq | hq
        · exact hr q hq
        · simp only [linLeReifEscTrue, List.mem_singleton] at hq
          rw [hq]
          exact litWF_of_slotOK hsh hslotR
      · intro c hrun q hq
        obtain ⟨c0, hres, hcl⟩ := augmentRes_conflict_inv hrun
        rw [hcl] at hq
        rcases mem_insertAfterHead hq with hq | hq
        · exact (typed_linNe hsh hslot st).2 c0 hres q hq
        · simp only [linLeReifEscTrue, List.mem_singleton] at hq
          rw [hq]
          exact litWF_of_slotOK hsh hslotR
    · by_cases h2 : (domBoolPin st.domains r false
          && domsIntOnlyB st.domains is) = true
      · rw [propLinNeReif_run_false hlenB h1 h2]
        refine ⟨fun l rs hrun => (conflictsOnly_implied_elim hrun).elim, ?_⟩
        intro c hrun q hq
        obtain ⟨c0, hres, hcl⟩ :=
          augmentRes_conflict_inv (conflictsOnly_conflict_inv hrun)
        rw [hcl] at hq
        rcases mem_insertAfterHead hq with hq | hq
        · exact (typed_linEq hsh hslot st).2 c0 hres q hq
        · rw [linLeReifEscFalse] at hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact litWF_of_slotOK hsh hslotR
          · obtain ⟨i, hi, hq2⟩ := List.mem_flatMap.mp hq
            rcases List.mem_cons.mp hq2 with rfl | hq2
            · exact litWF_of_slotOK hsh (hslot i hi)
            · rw [List.mem_singleton.mp hq2]
              exact litWF_of_slotOK hsh (hslot i hi)
      · rw [propLinNeReif_run_stable hlenB h1 h2]
        exact resTyped_stable orig
  · rw [propLinNeReif_run_arity (Bool.eq_false_iff.mpr hlenB)]
    exact resTyped_stable orig

/-! ## 11. The assembled theorem -/

/-- **Typed emissions of the `lcgFamB` raw kit.** For a constraint list in
the gate `lcgFamB`, with the box `orig` shape-typed and every slot a
constraint names being `SlotOK` (in range, nonempty domain), the raw
propagators `dcs.filterMap propagatorOfProved` emit only well-slotted
literals (`EmissionTyped orig`). -/
theorem emissionTyped_of_families {orig : List Domain} {dcs : List DomConstraint}
    (hfam : ∀ dc ∈ dcs, LeanFzn.Solver.UIP.LcgFamilies.lcgFamB dc = true)
    (hsh : ShapeTypedDomains orig)
    (hslot : ∀ dc ∈ dcs, ∀ s ∈ dcSlots dc, SlotOK orig s) :
    EmissionTyped orig (dcs.filterMap propagatorOfProved) := by
  have hall : ∀ p ∈ dcs.filterMap propagatorOfProved, ∀ st, ResTyped orig (p.run st) := by
    intro p hp st
    obtain ⟨dc, hdc, hprop⟩ := LeanFzn.Solver.Propagation.propagatorsOfProved_mem hp
    have hf := hfam dc hdc
    have hs : ∀ s ∈ dcSlots dc, SlotOK orig s := hslot dc hdc
    cases dc with
    | eqSlot i j =>
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact typed_eq hsh (hs i (by simp [dcSlots])) (hs j (by simp [dcSlots])) st
    | neSlot i j =>
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact typed_ne hsh (hs i (by simp [dcSlots])) (hs j (by simp [dcSlots])) st
    | leSlot i j =>
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact typed_le hsh (hs i (by simp [dcSlots])) (hs j (by simp [dcSlots])) st
    | ltSlot i j =>
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact typed_lt hsh (hs i (by simp [dcSlots])) (hs j (by simp [dcSlots])) st
    | constEq i v =>
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact typed_constEq hsh (hs i (by simp [dcSlots])) v st
    | plusSlot i j k =>
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact typed_plus hsh (hs i (by simp [dcSlots])) (hs j (by simp [dcSlots]))
          (hs k (by simp [dcSlots])) st
    | leConstHi i c =>
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact typed_leConstHi hsh (hs i (by simp [dcSlots])) st
    | leConstLo i c =>
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact typed_leConstLo hsh (hs i (by simp [dcSlots])) st
    | ltConstHi i c =>
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact typed_ltConstHi hsh (hs i (by simp [dcSlots])) st
    | ltConstLo i c =>
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact typed_ltConstLo hsh (hs i (by simp [dcSlots])) st
    | allDiff is =>
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact typed_allDiff hsh (fun s hsm => hs s (by simp [dcSlots, hsm])) st
    | linLe coeffs is b =>
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact typed_linLe hsh (fun s hsm => hs s (by simp [dcSlots, hsm])) st
    | linEq coeffs is b =>
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact typed_linEq hsh (fun s hsm => hs s (by simp [dcSlots, hsm])) st
    | boolNotSlot i j =>
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact typed_boolNot hsh (hs i (by simp [dcSlots])) (hs j (by simp [dcSlots])) st
    | boolAndSlot i j k =>
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact typed_boolAnd hsh (hs i (by simp [dcSlots])) (hs j (by simp [dcSlots]))
          (hs k (by simp [dcSlots])) st
    | boolOrSlot i j k =>
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact typed_boolOr hsh (hs i (by simp [dcSlots])) (hs j (by simp [dcSlots]))
          (hs k (by simp [dcSlots])) st
    | minSlot i j k =>
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact typed_min hsh (hs i (by simp [dcSlots])) (hs j (by simp [dcSlots]))
          (hs k (by simp [dcSlots])) st
    | maxSlot i j k =>
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact typed_max hsh (hs i (by simp [dcSlots])) (hs j (by simp [dcSlots]))
          (hs k (by simp [dcSlots])) st
    | linNe coeffs is b =>
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact typed_linNe hsh (fun s hsm => hs s (by simp [dcSlots, hsm])) st
    | absSlot i k =>
        -- PLAN L7: the registered propagator is the bound propagator
        -- `propAbs`.
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact typed_abs hsh (hs i (by simp [dcSlots])) (hs k (by simp [dcSlots])) st
    | timesSlot i j k =>
        -- PLAN L6: the registered propagator is the bound propagator
        -- `propTimes`.
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact typed_times hsh (hs i (by simp [dcSlots])) (hs j (by simp [dcSlots]))
          (hs k (by simp [dcSlots])) st
    | boolClauseSlot ps ns =>
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved] at hprop
        exact absurd hprop (by intro hc; cases hc)
    | arrayBoolAndSlot is k =>
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved] at hprop
        exact absurd hprop (by intro hc; cases hc)
    | bool2intSlot i k =>
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved] at hprop
        exact absurd hprop (by intro hc; cases hc)
    | boolEqSlot i j =>
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved] at hprop
        exact absurd hprop (by intro hc; cases hc)
    | arrayIntElementSlot xs i k =>
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved] at hprop
        exact absurd hprop (by intro hc; cases hc)
    | arrayVarIntElementSlot is i k =>
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved] at hprop
        exact absurd hprop (by intro hc; cases hc)
    | arrayVarBoolElementSlot is i k =>
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved] at hprop
        exact absurd hprop (by intro hc; cases hc)
    | leReifSlot i j r =>
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact typed_leReifSlot hsh (hs i (by simp [dcSlots])) (hs j (by simp [dcSlots]))
          (hs r (by simp [dcSlots])) st
    | eqReifSlot i j r =>
        -- PLAN L4: the registered propagator is the pinned-direction
        -- `propEqReifSlot` delegation.
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact typed_eqReifSlot hsh (hs i (by simp [dcSlots])) (hs j (by simp [dcSlots]))
          (hs r (by simp [dcSlots])) st
    | neReifSlot i j r =>
        -- PLAN L4: the registered propagator is the pinned-direction
        -- `propNeReifSlot` delegation.
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact typed_neReifSlot hsh (hs i (by simp [dcSlots])) (hs j (by simp [dcSlots]))
          (hs r (by simp [dcSlots])) st
    | linLeReif coeffs is b r =>
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        refine typed_linLeReif hsh ?_ ?_ st
        · intro s hs'
          exact hs s (by simpa [dcSlots] using List.mem_append_left [r] hs')
        · exact hs r (by simp [dcSlots])
    | linEqReif coeffs is b r =>
        -- PLAN L5: the registered propagator is the pinned-direction
        -- `propLinEqReif` delegation.
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        refine typed_linEqReif hsh ?_ ?_ st
        · intro s hs'
          exact hs s (by simpa [dcSlots] using List.mem_append_left [r] hs')
        · exact hs r (by simp [dcSlots])
    | linNeReif coeffs is b r =>
        -- PLAN L5: the registered propagator is the pinned-direction
        -- `propLinNeReif` delegation.
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        refine typed_linNeReif hsh ?_ ?_ st
        · intro s hs'
          exact hs s (by simpa [dcSlots] using List.mem_append_left [r] hs')
        · exact hs r (by simp [dcSlots])
    | minPair o₀ o₁ r =>
        cases o₀ <;> cases o₁ <;> cases r <;>
          first
          | (simp only [LeanFzn.Solver.Propagation.propagatorOfProved,
               Option.some.injEq] at hprop
             subst hprop
             refine typed_min hsh (hs _ ?_) (hs _ ?_) (hs _ ?_) st <;>
               simp [dcSlots, DomIntArg.slots])
          | (simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
             subst hprop
             rw [dcSlots_eq_full] at hs
             cases hres :
             ((LeanFzn.Solver.Propagation.DomainFiltering.propCheck _) : Propagator).run st with
             | stable => exact resTyped_stable orig
             | implied l r => exact (propCheck_implied_elim hres).elim
             | conflict c =>
                 obtain ⟨hready, hall, hc⟩ := propCheck_conflict_inv hres
                 refine resTyped_conflict ?_
                 intro q hq
                 rw [hc] at hq
                 exact litWF_of_slotOK hsh (hs _ (propCheckConflict_atomSlot_mem hq))
             )
    | maxPair o₀ o₁ r =>
        cases o₀ <;> cases o₁ <;> cases r <;>
          first
          | (simp only [LeanFzn.Solver.Propagation.propagatorOfProved,
               Option.some.injEq] at hprop
             subst hprop
             refine typed_max hsh (hs _ ?_) (hs _ ?_) (hs _ ?_) st <;>
               simp [dcSlots, DomIntArg.slots])
          | (simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
             subst hprop
             rw [dcSlots_eq_full] at hs
             cases hres :
             ((LeanFzn.Solver.Propagation.DomainFiltering.propCheck _) : Propagator).run st with
             | stable => exact resTyped_stable orig
             | implied l r => exact (propCheck_implied_elim hres).elim
             | conflict c =>
                 obtain ⟨hready, hall, hc⟩ := propCheck_conflict_inv hres
                 refine resTyped_conflict ?_
                 intro q hq
                 rw [hc] at hq
                 exact litWF_of_slotOK hsh (hs _ (propCheckConflict_atomSlot_mem hq))
             )
    | divGen o₁ o₂ r =>
        -- PLAN L7: the registered propagator is the bound propagator
        -- `propDiv`.
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        refine typed_div hsh ?_ ?_ ?_ st <;>
          (intro s hs'
           exact hs s (by simp [dcSlots, DomIntArg.slots, hs']))
    | modGen o₁ o₂ r =>
        -- PLAN L7: the registered propagator is the bound propagator
        -- `propMod`.
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        refine typed_mod hsh ?_ ?_ ?_ st <;>
          (intro s hs'
           exact hs s (by simp [dcSlots, DomIntArg.slots, hs']))
    | maxGen os r =>
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact typed_maxGen hsh os r
          (fun i hi => hs i (by
            simp only [dcSlots]
            exact List.mem_append_right _ hi))
          (fun o ho i hi => hs i (by
            simp only [dcSlots]
            exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨o, ho, hi⟩))) st
    | minGen os r =>
        simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
        subst hprop
        exact typed_minGen hsh os r
          (fun i hi => hs i (by
            simp only [dcSlots]
            exact List.mem_append_right _ hi))
          (fun o ho i hi => hs i (by
            simp only [dcSlots]
            exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨o, ho, hi⟩))) st
  unfold EmissionTyped
  exact ⟨fun p hp st l r h => (hall p hp st).1 l r h,
    fun p hp st c h => (hall p hp st).2 c h⟩

end LeanFzn.Solver.UIP.LcgEmissionTyped

import LeanFzn.Semantics.Evaluation
open LeanFzn.Semantics


/-!
# Shared helpers for the global-constraint formalization

Common list/set helpers used by several `fzn_*` global-constraint
families, each Boolean twin paired with an iff theorem, following the
`wellFormedB_iff` pattern of `FznSemantics.lean`.

All FlatZinc arrays are 1-based; the helpers here work on Lean `List`s
with 0-based indices, with conversion lemmas where needed.
-/

open LeanFzn.Semantics

open LeanFzn.Semantics.Evaluation

namespace LeanFzn.Semantics.Globals

open LeanFzn LeanFzn.Semantics.Evaluation

/-! ## Set membership bridge -/

/-- Boolean twin of `IntSetValue.Contains`. -/
def setMemB (s : IntSetValue) (i : Int) : Bool := decide (s.Contains i)

theorem setMemB_iff {s : IntSetValue} {i : Int} :
    setMemB s i = true ↔ s.Contains i := by
  exact decide_eq_true_iff

/-- Boolean twin of extensional set equality (both directions checked
    through the finite element lists). -/
def setEqB (a b : IntSetValue) : Bool :=
  (setElems a).all (fun x => setMemB b x) && (setElems b).all (fun x => setMemB a x)

theorem setEqB_iff {a b : IntSetValue} :
    setEqB a b = true ↔ ∀ i, a.Contains i ↔ b.Contains i := by
  unfold setEqB
  rw [Bool.and_eq_true]
  have h1 : ((setElems a).all fun x => setMemB b x) = true ↔
      ∀ i, a.Contains i → b.Contains i := by
    constructor
    · intro h i hi
      have himem : i ∈ setElems a := setElems_mem_iff.mp hi
      exact setMemB_iff.mp ((List.all_eq_true.mp h) i himem)
    · intro h
      refine List.all_eq_true.mpr ?_
      intro x hx
      exact setMemB_iff.mpr (h x (setElems_mem_iff.mpr hx))
  have h2 : ((setElems b).all fun x => setMemB a x) = true ↔
      ∀ i, b.Contains i → a.Contains i := by
    constructor
    · intro h i hi
      have himem : i ∈ setElems b := setElems_mem_iff.mp hi
      exact setMemB_iff.mp ((List.all_eq_true.mp h) i himem)
    · intro h
      refine List.all_eq_true.mpr ?_
      intro x hx
      exact setMemB_iff.mpr (h x (setElems_mem_iff.mpr hx))
  rw [h1, h2]
  constructor
  · rintro ⟨hsub, hsup⟩ i
    exact ⟨hsub i, hsup i⟩
  · intro h
    exact ⟨fun i => (h i).mp, fun i => (h i).mpr⟩

/-- Boolean twin of extensional set inclusion. -/
def setSubB (a b : IntSetValue) : Bool :=
  (setElems a).all (fun x => setMemB b x)

theorem setSubB_iff {a b : IntSetValue} :
    setSubB a b = true ↔ ∀ i, a.Contains i → b.Contains i := by
  constructor
  · intro h i hi
    have himem : i ∈ setElems a := setElems_mem_iff.mp hi
    exact setMemB_iff.mp ((List.all_eq_true.mp h) i himem)
  · intro h
    refine List.all_eq_true.mpr ?_
    intro x hx
    exact setMemB_iff.mpr (h x (setElems_mem_iff.mpr hx))

/-! ## Typed views of value lists -/

/-- The integers of a value list; `none` if any element is not an integer. -/
def valueInts : List Value → Option (List Int)
  | [] => some []
  | .int x :: rest => (valueInts rest).map (x :: ·)
  | _ => none

/-- The booleans of a value list; `none` if any element is not a boolean. -/
def valueBools : List Value → Option (List Bool)
  | [] => some []
  | .bool x :: rest => (valueBools rest).map (x :: ·)
  | _ => none

/-- The sets of a value list; `none` if any element is not a set. -/
def valueSets : List Value → Option (List IntSetValue)
  | [] => some []
  | .setOfInt x :: rest => (valueSets rest).map (x :: ·)
  | _ => none

/-- The integer of a single value; `none` if it is not an integer. -/
def valueInt : Value → Option Int
  | .int x => some x
  | _ => none

/-- The set of a single value; `none` if it is not a set. -/
def valueSet : Value → Option IntSetValue
  | .setOfInt s => some s
  | _ => none

/-- The boolean of a single value; `none` if it is not a boolean. -/
def valueBool : Value → Option Bool
  | .bool b => some b
  | _ => none

/-! ## Occurrence counting -/

/-- Number of occurrences of integer `v` in an integer list. -/
def intCount (xs : List Int) (v : Int) : Nat := xs.count v

/-- Number of elements of a value list equal to `v` (by `Value.eqB`). -/
def valueCount (xs : List Value) (v : Value) : Nat :=
  (xs.filter (fun x => x.eqB v)).length

theorem valueCount_le_length {xs : List Value} {v : Value} :
    valueCount xs v ≤ xs.length := List.length_filter_le _ _

theorem valueCount_pos_iff {xs : List Value} {v : Value} :
    0 < valueCount xs v ↔ ∃ x ∈ xs, x.eqB v = true := by
  unfold valueCount
  induction xs with
  | nil => simp
  | cons y ys ih =>
    by_cases hy : y.eqB v = true
    · simp only [List.filter, hy, List.length_cons]
      exact ⟨fun _ => ⟨y, by simp, hy⟩, fun _ => by omega⟩
    · simp only [List.filter, hy, ih]
      constructor
      · intro h
        rcases h with ⟨x, hx, hxeq⟩
        exact ⟨x, by simp [hx], hxeq⟩
      · rintro ⟨x, hx, hxeq⟩
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact absurd hxeq hy
        · exact ⟨x, hx', hxeq⟩

theorem valueCount_zero_iff {xs : List Value} {v : Value} :
    valueCount xs v = 0 ↔ ∀ x ∈ xs, x.eqB v ≠ true := by
  constructor
  · intro h x hx hxeq
    have : 0 < valueCount xs v := valueCount_pos_iff.mpr ⟨x, hx, hxeq⟩
    omega
  · intro h
    match hc : valueCount xs v with
    | 0 => rfl
    | (n+1) =>
        have h0 : 0 < valueCount xs v := by rw [hc]; omega
        obtain ⟨x, hx, hxeq⟩ := valueCount_pos_iff.mp h0
        exact absurd hxeq (h x hx)

/-! ## Membership -/

/-- Boolean twin of value-list membership. -/
def valueMemB (xs : List Value) (v : Value) : Bool := xs.any (fun x => x.eqB v)

theorem valueMemB_iff {xs : List Value} {v : Value} :
    valueMemB xs v = true ↔ ∃ x ∈ xs, x.eqB v = true := by
  exact List.any_eq_true

end LeanFzn.Semantics.Globals

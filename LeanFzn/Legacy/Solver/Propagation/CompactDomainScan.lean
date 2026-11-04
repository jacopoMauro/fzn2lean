/-
File: LeanFzn/Solver/Propagation/CompactDomainScan.lean

Purpose (D2 stage 3, UNWIRED): the S4 bridge between the wave-2 scan
summary `SlotSum` (`DbScanIndex.lean`) and the `Dom` query summary
(`CompactDomain.lean`).

`slotSumOfDomain` folds `SlotSum.step` over a legacy `List Value`
domain and collects the integer extremes of the `Value.intView` image
plus the two Boolean memberships; `Dom.summary` answers the same four
fields directly.  This module proves

  `slotSumOfDomain (Dom.enum d) = SlotSum.ofSummary (Dom.summary d)`

so the scan's `sumsOfArray` can be computed from `Dom` summaries
without enumerating the domain (S4 of the D0 §5.3 migration).

Why a companion module: `CompactDomain` must stay importable by
`DbScanIndex` (S4 replaces the scan's summary construction by
`Dom.summary`), so `DbScanIndex` cannot be imported there.  This file
is a leaf — nothing imports it — and can be inlined into
`DbScanIndex` (or deleted) when S4 is integrated.

DAG:
  LeanFzn.Solver.Propagation.DbScanIndex +
  LeanFzn.Solver.Propagation.CompactDomain
    -> LeanFzn.Solver.Propagation.CompactDomainScan
    -> (S4 integration: scan summaries)
-/

import LeanFzn.Legacy.Solver.Propagation.DbScanIndex
import LeanFzn.Solver.Propagation.CompactDomain

namespace LeanFzn.Solver.Propagation

open LeanFzn.Semantics LeanFzn.Solver.Core Dom

/-- The `SlotSum` of a `Dom` query summary: the S4 swap. -/
def SlotSum.ofSummary (s : Dom.Summary) : SlotSum :=
  ⟨s.minInt, s.maxInt, s.hasTrue, s.hasFalse⟩

/-! ## One-step projections of the `SlotSum.step` fold -/

private def stepMin (acc : Option Int) (v : Value) : Option Int :=
  match Value.intView v with
  | some i => some (match acc with | some a => min a i | none => i)
  | none => acc

private def stepMax (acc : Option Int) (v : Value) : Option Int :=
  match Value.intView v with
  | some i => some (match acc with | some a => max a i | none => i)
  | none => acc

private def stepTrue (acc : Bool) (v : Value) : Bool :=
  acc || (match v with | .bool true => true | _ => false)

private def stepFalse (acc : Bool) (v : Value) : Bool :=
  acc || (match v with | .bool false => true | _ => false)

private theorem foldl_step_minInt (l : List Value) (s : SlotSum) :
    (l.foldl SlotSum.step s).minInt = l.foldl stepMin s.minInt := by
  induction l generalizing s with
  | nil => rfl
  | cons v rest ih =>
    show (rest.foldl SlotSum.step (SlotSum.step s v)).minInt =
      rest.foldl stepMin (stepMin s.minInt v)
    rw [ih (SlotSum.step s v)]
    congr 1
    cases v <;> rfl

private theorem foldl_step_maxInt (l : List Value) (s : SlotSum) :
    (l.foldl SlotSum.step s).maxInt = l.foldl stepMax s.maxInt := by
  induction l generalizing s with
  | nil => rfl
  | cons v rest ih =>
    show (rest.foldl SlotSum.step (SlotSum.step s v)).maxInt =
      rest.foldl stepMax (stepMax s.maxInt v)
    rw [ih (SlotSum.step s v)]
    congr 1
    cases v <;> rfl

private theorem foldl_step_hasTrue (l : List Value) (s : SlotSum) :
    (l.foldl SlotSum.step s).hasTrue = l.foldl stepTrue s.hasTrue := by
  induction l generalizing s with
  | nil => rfl
  | cons v rest ih =>
    show (rest.foldl SlotSum.step (SlotSum.step s v)).hasTrue =
      rest.foldl stepTrue (stepTrue s.hasTrue v)
    rw [ih (SlotSum.step s v)]
    congr 1
    cases v with
    | bool b => cases b <;> simp [stepTrue, SlotSum.step, Value.intView]
    | int i => simp [stepTrue, SlotSum.step, Value.intView]
    | setOfInt s => simp [stepTrue, SlotSum.step, Value.intView]
    | array a => simp [stepTrue, SlotSum.step, Value.intView]

private theorem foldl_step_hasFalse (l : List Value) (s : SlotSum) :
    (l.foldl SlotSum.step s).hasFalse = l.foldl stepFalse s.hasFalse := by
  induction l generalizing s with
  | nil => rfl
  | cons v rest ih =>
    show (rest.foldl SlotSum.step (SlotSum.step s v)).hasFalse =
      rest.foldl stepFalse (stepFalse s.hasFalse v)
    rw [ih (SlotSum.step s v)]
    congr 1
    cases v with
    | bool b => cases b <;> simp [stepFalse, SlotSum.step, Value.intView]
    | int i => simp [stepFalse, SlotSum.step, Value.intView]
    | setOfInt s => simp [stepFalse, SlotSum.step, Value.intView]
    | array a => simp [stepFalse, SlotSum.step, Value.intView]

/-! ## Folds over the view image -/

private theorem foldl_min_eq (l : List Int) (a : Int) :
    l.foldl min a = l.min?.elim a (min a) := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, List.min?_cons, ih (min a x)]
    cases hm : xs.min? with
    | none => rfl
    | some m => simp only [Option.elim_some]; rw [Int.min_assoc]

private theorem foldl_max_eq (l : List Int) (a : Int) :
    l.foldl max a = l.max?.elim a (max a) := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, List.max?_cons, ih (max a x)]
    cases hm : xs.max? with
    | none => rfl
    | some m => simp only [Option.elim_some]; rw [Int.max_assoc]

private theorem foldl_stepMin_some (l : List Value) (a : Int) :
    l.foldl stepMin (some a) = some ((l.filterMap Value.intView).foldl min a) := by
  induction l generalizing a with
  | nil => rfl
  | cons v rest ih =>
    show rest.foldl stepMin (stepMin (some a) v) =
      some ((v :: rest).filterMap Value.intView |>.foldl min a)
    cases hv : Value.intView v with
    | none =>
      rw [show stepMin (some a) v = some a from by simp [stepMin, hv], ih a]
      simp [hv]
    | some i =>
      rw [show stepMin (some a) v = some (min a i) from by simp [stepMin, hv], ih (min a i)]
      simp only [List.filterMap_cons, hv, List.foldl_cons]

private theorem foldl_stepMax_some (l : List Value) (a : Int) :
    l.foldl stepMax (some a) = some ((l.filterMap Value.intView).foldl max a) := by
  induction l generalizing a with
  | nil => rfl
  | cons v rest ih =>
    show rest.foldl stepMax (stepMax (some a) v) =
      some ((v :: rest).filterMap Value.intView |>.foldl max a)
    cases hv : Value.intView v with
    | none =>
      rw [show stepMax (some a) v = some a from by simp [stepMax, hv], ih a]
      simp [hv]
    | some i =>
      rw [show stepMax (some a) v = some (max a i) from by simp [stepMax, hv], ih (max a i)]
      simp only [List.filterMap_cons, hv, List.foldl_cons]

private theorem foldl_stepMin_none (l : List Value) :
    l.foldl stepMin none = (l.filterMap Value.intView).min? := by
  induction l with
  | nil => rfl
  | cons v rest ih =>
    show rest.foldl stepMin (stepMin none v) = ((v :: rest).filterMap Value.intView).min?
    cases hv : Value.intView v with
    | none =>
      rw [show stepMin none v = none from by simp [stepMin, hv], ih]
      simp [hv]
    | some i =>
      rw [show stepMin none v = some i from by simp [stepMin, hv],
        foldl_stepMin_some rest i, List.filterMap_cons, hv, List.min?_cons]
      exact congrArg some (foldl_min_eq (rest.filterMap Value.intView) i)

private theorem foldl_stepMax_none (l : List Value) :
    l.foldl stepMax none = (l.filterMap Value.intView).max? := by
  induction l with
  | nil => rfl
  | cons v rest ih =>
    show rest.foldl stepMax (stepMax none v) = ((v :: rest).filterMap Value.intView).max?
    cases hv : Value.intView v with
    | none =>
      rw [show stepMax none v = none from by simp [stepMax, hv], ih]
      simp [hv]
    | some i =>
      rw [show stepMax none v = some i from by simp [stepMax, hv],
        foldl_stepMax_some rest i, List.filterMap_cons, hv, List.max?_cons]
      exact congrArg some (foldl_max_eq (rest.filterMap Value.intView) i)

/-! ## Boolean membership flags -/

private theorem foldl_stepTrue_true (l : List Value) : l.foldl stepTrue true = true := by
  induction l with
  | nil => rfl
  | cons v rest ih => exact ih

private theorem foldl_stepFalse_true (l : List Value) : l.foldl stepFalse true = true := by
  induction l with
  | nil => rfl
  | cons v rest ih => exact ih

private theorem foldl_stepTrue_false_iff (l : List Value) :
    l.foldl stepTrue false = true ↔ Value.bool true ∈ l := by
  induction l with
  | nil => simp
  | cons v rest ih =>
    show rest.foldl stepTrue (stepTrue false v) = true ↔ Value.bool true ∈ v :: rest
    cases v with
    | bool b =>
      cases b with
      | true => simp [stepTrue, foldl_stepTrue_true]
      | false => simpa [stepTrue] using ih
    | int i => simpa [stepTrue] using ih
    | setOfInt s => simpa [stepTrue] using ih
    | array a => simpa [stepTrue] using ih

private theorem foldl_stepFalse_false_iff (l : List Value) :
    l.foldl stepFalse false = true ↔ Value.bool false ∈ l := by
  induction l with
  | nil => simp
  | cons v rest ih =>
    show rest.foldl stepFalse (stepFalse false v) = true ↔ Value.bool false ∈ v :: rest
    cases v with
    | bool b =>
      cases b with
      | true => simpa [stepFalse] using ih
      | false => simp [stepFalse, foldl_stepFalse_true]
    | int i => simpa [stepFalse] using ih
    | setOfInt s => simpa [stepFalse] using ih
    | array a => simpa [stepFalse] using ih

/-! ## The S4 bridge -/

/-- The scan's min over the enumeration is the direct `Dom` query. -/
theorem slotSumOfDomain_enum_minInt (d : Dom) :
    (slotSumOfDomain d).minInt = (summary d).minInt := by
  unfold slotSumOfDomain
  rw [foldl_step_minInt]
  dsimp only [emptySum]
  rw [foldl_stepMin_none]
  show ((enum d).filterMap Value.intView).min? = minInt? d
  rw [← domInts_eq_intView, ← minInt?_eq_domInts_min]

/-- The scan's max over the enumeration is the direct `Dom` query. -/
theorem slotSumOfDomain_enum_maxInt (d : Dom) :
    (slotSumOfDomain d).maxInt = (summary d).maxInt := by
  unfold slotSumOfDomain
  rw [foldl_step_maxInt]
  dsimp only [emptySum]
  rw [foldl_stepMax_none]
  show ((enum d).filterMap Value.intView).max? = maxInt? d
  rw [← domInts_eq_intView, ← maxInt?_eq_domInts_max]

/-- The scan's `.bool true` membership over the enumeration is the
    direct `Dom` query. -/
theorem slotSumOfDomain_enum_hasTrue (d : Dom) :
    (slotSumOfDomain d).hasTrue = (summary d).hasTrue := by
  unfold slotSumOfDomain
  rw [foldl_step_hasTrue]
  dsimp only [emptySum]
  rw [Bool.eq_iff_iff]
  exact Iff.trans (foldl_stepTrue_false_iff (enum d)) (hasTrueB_iff d).symm

/-- The scan's `.bool false` membership over the enumeration is the
    direct `Dom` query. -/
theorem slotSumOfDomain_enum_hasFalse (d : Dom) :
    (slotSumOfDomain d).hasFalse = (summary d).hasFalse := by
  unfold slotSumOfDomain
  rw [foldl_step_hasFalse]
  dsimp only [emptySum]
  rw [Bool.eq_iff_iff]
  exact Iff.trans (foldl_stepFalse_false_iff (enum d)) (hasFalseB_iff d).symm

/-- **The S4 bridge (per slot)**: the legacy scan summary of a `Dom`'s
    enumeration is the direct `Dom` query summary; replacing
    `slotSumOfDomain` by `SlotSum.ofSummary ∘ Dom.summary` on `Dom`
    domains is denotation-exact. -/
theorem slotSumOfDomain_enum (d : Dom) :
    slotSumOfDomain d = SlotSum.ofSummary (summary d) := by
  rw [show SlotSum.ofSummary (summary d) =
      ⟨(slotSumOfDomain d).minInt, (slotSumOfDomain d).maxInt,
        (slotSumOfDomain d).hasTrue,
        (slotSumOfDomain d).hasFalse⟩ from by
    rw [show SlotSum.ofSummary (summary d) =
        ⟨(summary d).minInt, (summary d).maxInt, (summary d).hasTrue,
          (summary d).hasFalse⟩ from rfl]
    rw [← slotSumOfDomain_enum_minInt d, ← slotSumOfDomain_enum_maxInt d,
      ← slotSumOfDomain_enum_hasTrue d, ← slotSumOfDomain_enum_hasFalse d]]

/-- **The S4 bridge (per scan)**: `sumsOfArray` over an array of
    enumerations equals the array of direct summaries, so the scan's
    slot summaries can be computed from `Dom` values without
    enumerating (the `frameDomainArray` swap of D0 §5.3 S4). -/
theorem sumsOfArray_enum (ds : Array Dom) :
    sumsOfArray ds =
      ds.map fun d => SlotSum.ofSummary (summary d) := by
  unfold sumsOfArray
  congr 1
  funext d
  exact slotSumOfDomain_enum d

end LeanFzn.Solver.Propagation

import LeanFzn.Semantics.Evaluation
import Lean

namespace LeanFzn.Semantics.Evaluation
open LeanFzn LeanFzn.Semantics

/-- Reflexivity of pointwise value equality, by induction on the
    list of array elements (all nested arrays recurse through the
    element list). -/
theorem value_eqB_refl : ∀ (v : Value), v.eqB v = true := by
  intro v
  cases v with
  | bool b => simp [Value.eqB]
  | int i => simp [Value.eqB]
  | setOfInt sv =>
      cases sv with
      | enumeration xs =>
          have hzip : (xs.zip xs).all (fun x => x.1 == x.2) = true := by
            induction xs with
            | nil => rfl
            | cons x xt ih =>
                show ((decide (x = x)) &&
                  ((xt.zip xt).all (fun x => x.1 == x.2))) = true
                rw [decide_eq_true rfl, ih]
                rfl
          simp only [Value.eqB, IntSetValue.eqB, Bool.and_eq_true, beq_iff_eq]
          exact ⟨trivial, hzip⟩
      | interval lo hi => simp [Value.eqB, IntSetValue.eqB]
  | array vs =>
      have hrec : ∀ (ws : List Value), (∀ w ∈ ws, w.eqB w = true) →
          valuesEqB ws ws = true := by
        intro ws
        induction ws with
        | nil => intro _; rfl
        | cons w wt ih =>
            intro hall
            simp only [valuesEqB, Bool.and_eq_true]
            exact ⟨hall w (by simp), ih (fun h hin => hall h (by simp [hin]))⟩
      simp only [Value.eqB, hrec vs (fun w _ => value_eqB_refl w)]

/-- Two integer lists of equal length whose zipped pairs are all
    equal are equal. -/
private theorem int_list_eq_of_zip : ∀ (xs ys : List Int),
    xs.length = ys.length →
    (xs.zip ys).all (fun (a, b) => decide (a = b)) = true → xs = ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys h1 h2
      cases ys with
      | nil => rfl
      | cons y yt => simp at h1
  | cons x xt ih =>
      intro ys h1 h2
      cases ys with
      | nil => simp at h1
      | cons y yt =>
          have hzp : (decide (x = y) &&
              (xt.zip yt).all (fun (a, b) => decide (a = b))) = true := by
            simpa [List.zip_cons_cons, List.all_cons] using h2
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hzp
          have hlen : xt.length = yt.length := by
            simp only [List.length_cons] at h1; omega
          rw [ih yt hlen hzp.2]
          exact congrArg (fun h' => h' :: yt) hzp.1

/-- The fold-max of a list is at least its starting accumulator. -/
private theorem List.foldl_le_foldl_max_start (l : List Nat) (n : Nat) :
    n ≤ List.foldl max n l := by
  induction l generalizing n with
  | nil => exact Nat.le_refl _
  | cons a tl ih =>
      show n ≤ List.foldl max (max n a) tl
      exact Nat.le_trans (by omega) (ih (max n a))

/-- The fold-max is monotone in the starting accumulator. -/
private theorem List.foldl_mono_start (l : List Nat) (m n : Nat) (h : m ≤ n) :
    List.foldl max m l ≤ List.foldl max n l := by
  induction l generalizing m n with
  | nil => exact h
  | cons a tl ih => exact ih (max m a) (max n a) (by omega)

/-- Every element's measure is bounded by the fold-max of the
    list's measures. -/
private theorem listMeasure_le_foldl {α : Type} (f : α → Nat) :
    ∀ (l : List α) (v : α), v ∈ l → f v ≤ (l.map f).foldl max 0 := by
  intro l
  induction l with
  | nil => intro v hv; cases hv
  | cons w wt ih =>
      intro v hv
      simp only [List.mem_cons] at hv
      simp only [List.map_cons, List.foldl_cons]
      rcases hv with rfl | hv'
      · have h0 : f v ≤ max 0 (f v) := by omega
        have hfold : (List.map f wt).foldl max (max 0 (f v)) ≥ max 0 (f v) := by
          exact List.foldl_le_foldl_max_start (List.map f wt) (max 0 (f v))
        omega
      · have h1 := ih v hv'
        have h2 : (wt.map f).foldl max 0 ≤
            List.foldl max (max 0 (f w)) (wt.map f) :=
          List.foldl_mono_start (wt.map f) 0 (max 0 (f w)) (by omega)
        exact Nat.le_trans h1 h2

/-- Nesting depth of a value. -/
private def valueDepth : Value → Nat
  | .array vs => (vs.map valueDepth).foldl max 0 + 1
  | _ => 0

/-- List equality from `valuesEqB`, with the recursive leaf
    obligation discharged by a depth-bounded induction on the
    elements. -/
private theorem valuesEqB_bounded : ∀ (len fuel : Nat)
    (_ih : ∀ (a b : Value), valueDepth a ≤ fuel → a.eqB b = true → a = b)
    (xs ys : List Value)
    (_hxs : (xs.map valueDepth).foldl max 0 ≤ fuel)
    (_hlen : xs.length ≤ len)
    (_h : valuesEqB xs ys = true), xs = ys := by
  intro len
  induction len with
  | zero =>
      intro fuel ih xs ys hxs hlen h
      cases xs with
      | nil =>
          cases ys with
          | nil => rfl
          | cons y yt => simp [valuesEqB] at h
      | cons x xt =>
          exfalso
          simp only [List.length_cons] at hlen
          omega
  | succ len ihh =>
      intro fuel ih xs ys hxs hlen h
      cases xs with
      | nil =>
          cases ys with
          | nil => rfl
          | cons y yt => simp [valuesEqB] at h
      | cons x xt =>
          cases ys with
          | nil => simp [valuesEqB] at h
          | cons y yt =>
              simp only [valuesEqB, Bool.and_eq_true] at h
              have hhead : x = y := by
                refine ih x y ?_ h.1
                have hxb := listMeasure_le_foldl valueDepth (x :: xt) x (by simp)
                -- normalize hxs to the same foldl form as hxb
                rw [show List.foldl max 0 (List.map valueDepth (x :: xt)) =
                  List.foldl max 0 (List.map valueDepth (x :: xt)) from rfl]
                  at hxs
                omega
              rw [hhead]
              have htail : xt = yt :=
                ihh fuel ih xt yt
                  (by
                    have h1 : List.foldl max 0
                          (List.map valueDepth (x :: xt)) =
                        List.foldl max (max 0 (valueDepth x))
                          (xt.map valueDepth) := by
                      rfl
                    rw [h1] at hxs
                    have hmono : List.foldl max 0 (List.map valueDepth xt) ≤
                        List.foldl max (max 0 (valueDepth x))
                          (List.map valueDepth xt) :=
                      List.foldl_mono_start (List.map valueDepth xt)
                        0 (max 0 (valueDepth x)) (by omega)
                    omega)
                  (by
                    simp only [List.length_cons] at hlen
                    omega)
                  h.2
              rw [htail]

/-- Pointwise equality of values: proved by recursion on the depth
    fuel of the first argument. -/
theorem value_eqB_leaf_fueled : ∀ (fuel : Nat) (a b : Value),
    valueDepth a ≤ fuel → a.eqB b = true → a = b := by
  intro fuel
  induction fuel with
  | zero =>
      intro a b hle0 h
      cases a with
      | bool x =>
        cases b with
        | bool y =>
          simp only [Value.eqB, beq_iff_eq] at h
          rw [h]
        | _ => simp [Value.eqB] at h
      | int x =>
        cases b with
        | int y => simp [Value.eqB] at h; rw [h]
        | _ => simp [Value.eqB] at h
      | setOfInt x =>
        cases b with
        | setOfInt y =>
          cases x with
          | enumeration xs =>
            cases y with
            | enumeration ys =>
              simp only [Value.eqB, IntSetValue.eqB, Bool.and_eq_true] at h
              have h1 : xs.length = ys.length := by simpa using h.1
              have h2 : (xs.zip ys).all (fun (a, b) => decide (a = b)) = true :=
                h.2
              exact congrArg (fun l =>
                Value.setOfInt (IntSetValue.enumeration l))
                (int_list_eq_of_zip xs ys h1 h2)
            | interval lo hi => simp [Value.eqB, IntSetValue.eqB] at h
          | interval lo hi =>
            cases y with
            | enumeration ys => simp [Value.eqB, IntSetValue.eqB] at h
            | interval lo' hi' =>
              simp only [Value.eqB, IntSetValue.eqB, Bool.and_eq_true,
                beq_iff_eq] at h
              rw [h.1, h.2]
        | _ => simp [Value.eqB] at h
      | array xs =>
        exfalso
        have heq : valueDepth (Value.array xs) =
            (xs.map valueDepth).foldl max 0 + 1 := by
          simp only [valueDepth]
        rw [heq] at hle0
        omega
  | succ fuel ih =>
    intro a b hle h
    cases a with
    | bool x =>
      cases b with
      | bool y =>
        simp only [Value.eqB, beq_iff_eq] at h
        rw [h]
      | _ => simp [Value.eqB] at h
    | int x =>
      cases b with
      | int y => simp [Value.eqB] at h; rw [h]
      | _ => simp [Value.eqB] at h
    | setOfInt x =>
      cases b with
      | setOfInt y =>
        cases x with
        | enumeration xs =>
          cases y with
          | enumeration ys =>
            simp only [Value.eqB, IntSetValue.eqB, Bool.and_eq_true] at h
            have h1 : xs.length = ys.length := by simpa using h.1
            have h2 : (xs.zip ys).all (fun (a, b) => decide (a = b)) = true :=
              h.2
            exact congrArg (fun l =>
              Value.setOfInt (IntSetValue.enumeration l))
              (int_list_eq_of_zip xs ys h1 h2)
          | interval lo hi => simp [Value.eqB, IntSetValue.eqB] at h
        | interval lo hi =>
          cases y with
          | enumeration ys => simp [Value.eqB, IntSetValue.eqB] at h
          | interval lo' hi' =>
            simp only [Value.eqB, IntSetValue.eqB, Bool.and_eq_true,
              beq_iff_eq] at h
            rw [h.1, h.2]
      | _ => simp [Value.eqB] at h
    | array xs =>
      cases b with
      | array ys =>
        simp only [Value.eqB] at h
        rw [valuesEqB_bounded xs.length fuel ih xs ys
          (by
            have heq : valueDepth (Value.array xs) =
                (xs.map valueDepth).foldl max 0 + 1 := by
              simp only [valueDepth]
            rw [heq] at hle
            omega)
          (Nat.le_refl _) h]
      | _ => simp [Value.eqB] at h

/-- Unfueled entry point: the depth of `a` itself is a sufficient
    fuel. -/
theorem value_eqB_leaf' (a b : Value) (h : a.eqB b = true) : a = b :=
  value_eqB_leaf_fueled (valueDepth a) a b (Nat.le_refl _) h

/-- `Value.eqB` decides value equality. -/
theorem value_eqB_iff {a b : Value} : a.eqB b = true ↔ a = b :=
  ⟨fun h => value_eqB_leaf' a b h, fun h => by rw [h]; exact value_eqB_refl b⟩

/-- The executable `Value.eqB` gives the structural `DecidableEq` instance.
    Keeping the decision on the fast path avoids a second recursive
    equality implementation. -/
instance : DecidableEq Value := fun a b =>
  decidable_of_iff (a.eqB b = true) value_eqB_iff




end LeanFzn.Semantics.Evaluation

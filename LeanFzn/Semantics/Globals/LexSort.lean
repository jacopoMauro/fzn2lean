import LeanFzn.Semantics.Globals.Common
open LeanFzn.Semantics


/-!
# Lexicographic, sorting, and value-precedence global constraints

Mathematical interpretations (`lexSortInterp`) and executable Boolean
twins (`lexSortInterpB`) for the lex, sort, argsort, maximum/minimum-arg,
and value-precedence global-constraint predicates of the pinned MiniZinc
2.10.1 FlatZinc tree.  Each predicate name gets a per-name agreement
theorem `<name>_iff` proving that the Boolean twin is `true` exactly
when the mathematical interpretation holds.

Semantics per the MiniZinc 2.10.1 handbook, Section 4.2.2.3
("Lexicographic constraints") and 4.2.2.12 ("Sorting constraints"),
cross-checked against the pinned stdlib decompositions.  The
interpretive decisions specific to this family (prefix order for lex,
sortedness plus sub-multiset containment for `sort` — the pinned
decomposition's injective index array `p : index_set(xs) → index_set(ys)`
admits a longer `ys` — *stability* plus the "permutation of the positions
of `xs`" gate for `arg_sort_int`, least-index tie-breaking for
`maximum_arg`/`minimum_arg`, and the vacuous no-`after` case of
value precedence) are recorded in
`specification/flatzinc_specification_assumptions.md`, G12–G13.
-/

open LeanFzn.Semantics

open LeanFzn.Semantics.Evaluation

namespace LeanFzn.Semantics.Globals.LexSort

open LeanFzn LeanFzn.Semantics.Globals

/-! ## Small bridges -/

private theorem optBne_iff (a b : Option Int) : (a != b) = true ↔ a ≠ b := by
  cases a <;> cases b <;> simp_all

private theorem optBeq_iff (a b : Option Int) : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> simp_all

private theorem getElemBang_eq_getElem?getD {l : List Int} {i : Nat} :
    l[i]! = (l[i]?.getD 0) := by
  cases h : l[i]? with
  | none =>
    have hlen : l.length ≤ i := List.getElem?_eq_none_iff.mp h
    have hneg : ¬ (i < l.length) := by omega
    simp [show l[i]! = 0 from getElem!_neg l i hneg]
  | some a =>
    have hle : i < l.length := List.getElem?_eq_some_iff.mp h |>.1
    have hget : l[i] = a := List.getElem?_eq_some_iff.mp h |>.2
    simp [show l[i]! = l[i] from getElem!_pos l i hle, hget]

/-! ## Lex family -/

/-- Strict lexicographic order on integer lists (first to last; a
    proper prefix is smaller; `[] < []` is false). -/
def lexLess : List Int → List Int → Prop
  | [], [] => False
  | [], _ :: _ => True
  | _ :: _, [] => False
  | x :: xs, y :: ys => x < y ∨ (x = y ∧ lexLess xs ys)

/-- Boolean twin of `lexLess`. -/
def lexLessB : List Int → List Int → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => decide (x < y) || (decide (x = y) && lexLessB xs ys)

theorem lexLessB_iff (a b : List Int) : lexLessB a b = true ↔ lexLess a b := by
  induction a generalizing b with
  | nil => cases b <;> simp [lexLess, lexLessB]
  | cons x xs ih =>
    cases b with
    | nil => simp [lexLess, lexLessB]
    | cons y ys =>
      simp only [lexLess, lexLessB, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_iff, ih]

/-- Non-strict lexicographic order on integer lists. -/
def lexLesseq : List Int → List Int → Prop
  | [], _ => True
  | _ :: _, [] => False
  | x :: xs, y :: ys => x < y ∨ (x = y ∧ lexLesseq xs ys)

/-- Boolean twin of `lexLesseq`. -/
def lexLesseqB : List Int → List Int → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => decide (x < y) || (decide (x = y) && lexLesseqB xs ys)

theorem lexLesseqB_iff (a b : List Int) : lexLesseqB a b = true ↔ lexLesseq a b := by
  induction a generalizing b with
  | nil => cases b <;> simp [lexLesseq, lexLesseqB]
  | cons x xs ih =>
    cases b with
    | nil => simp [lexLesseq, lexLesseqB]
    | cons y ys =>
      simp only [lexLesseq, lexLesseqB, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_iff, ih]

/-! ## Increasing -/

/-- Non-decreasing consecutive elements (vacuously true for length ≤ 1). -/
def increasing : List Int → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => x ≤ y ∧ increasing (y :: rest)

/-- Boolean twin of `increasing`. -/
def increasingB : List Int → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => decide (x ≤ y) && increasingB (y :: rest)

theorem increasingB_iff (l : List Int) : increasingB l = true ↔ increasing l := by
  induction l with
  | nil => simp [increasingB, increasing]
  | cons x xs ih =>
    cases xs with
    | nil => simp [increasingB, increasing]
    | cons y ys =>
      simp only [increasingB, increasing, Bool.and_eq_true, decide_eq_true_iff, ih]

theorem increasing_tail : ∀ {xs : List Int}, increasing xs → increasing xs.tail
  | [], _ => trivial
  | [_], _ => trivial
  | _ :: _ :: _, h => h.2

theorem increasing_iff_pairwise {l : List Int} :
    increasing l ↔ List.Pairwise (· ≤ ·) l := by
  induction l with
  | nil => simp [increasing]
  | cons x xs ih =>
    cases xs with
    | nil => simp [increasing]
    | cons y ys =>
      simp only [increasing, ih]
      constructor
      · rintro ⟨hxy, hrest⟩
        exact List.Pairwise.cons (fun y' hy' => by
          rcases List.mem_cons.mp hy' with rfl | hy'
          · exact hxy
          · exact Int.le_trans hxy (List.rel_of_pairwise_cons hrest hy')) hrest
      · intro h
        exact ⟨List.rel_of_pairwise_cons h (by simp), h.tail⟩

/-- Non-decreasing consecutive booleans (`false ≤ true`). -/
def boolLe (a b : Bool) : Prop := a = true → b = true

def increasingBool : List Bool → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => boolLe x y ∧ increasingBool (y :: rest)

def increasingBoolB : List Bool → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => (!x || y) && increasingBoolB (y :: rest)

theorem increasingBoolB_iff (l : List Bool) :
    increasingBoolB l = true ↔ increasingBool l := by
  induction l with
  | nil => simp [increasingBoolB, increasingBool]
  | cons x xs ih =>
    cases xs with
    | nil => simp [increasingBoolB, increasingBool]
    | cons y ys =>
      simp only [increasingBoolB, increasingBool, Bool.and_eq_true, ih]
      cases x <;> cases y <;> simp [boolLe]

/-- Strictly increasing consecutive elements (vacuously true for length ≤ 1). -/
def strictlyIncreasing : List Int → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => x < y ∧ strictlyIncreasing (y :: rest)

def strictlyIncreasingB : List Int → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => decide (x < y) && strictlyIncreasingB (y :: rest)

theorem strictlyIncreasingB_iff (l : List Int) :
    strictlyIncreasingB l = true ↔ strictlyIncreasing l := by
  induction l with
  | nil => simp [strictlyIncreasingB, strictlyIncreasing]
  | cons x xs ih =>
    cases xs with
    | nil => simp [strictlyIncreasingB, strictlyIncreasing]
    | cons y ys =>
      simp only [strictlyIncreasingB, strictlyIncreasing, Bool.and_eq_true,
        decide_eq_true_iff, ih]

set_option maxHeartbeats 1000000 in
private theorem mergeSort_increasing (xs : List Int) :
    increasing (List.mergeSort xs (fun a b => decide (a ≤ b))) := by
  have hp := List.pairwise_mergeSort
    (le := fun a b => decide (a ≤ b))
    (fun (a b c : Int) hab hbc => by
      simp only [decide_eq_true_iff] at hab hbc ⊢
      exact Int.le_trans hab hbc)
    (fun (a b : Int) => by
      simp only [Bool.or_eq_true, decide_eq_true_iff]
      omega)
    xs
  refine increasing_iff_pairwise.mpr ?_
  exact List.Pairwise.imp (fun h => decide_eq_true_iff.mp h) hp

set_option maxHeartbeats 1000000 in
/-- Two increasing lists that are permutations of each other are equal. -/
theorem sorted_perm_unique : ∀ {l l' : List Int}, l.Perm l' →
    increasing l → increasing l' → l = l' := by
  intro l
  induction l with
  | nil =>
    intro l' hp _ _
    cases l' with
    | nil => rfl
    | cons y ys =>
      have hmem : y ∈ ([] : List Int) :=
        List.Perm.mem_iff (List.Perm.symm hp) |>.mp List.mem_cons_self
      simp at hmem
  | cons x xs ih =>
    intro l' hp h1 h2
    cases l' with
    | nil =>
      have hmem : x ∈ ([] : List Int) :=
        List.Perm.mem_iff hp |>.mp List.mem_cons_self
      simp at hmem
    | cons y ys =>
      have hyx : y ∈ x :: xs :=
        List.Perm.mem_iff (List.Perm.symm hp) |>.mp List.mem_cons_self
      have hxy : x ∈ y :: ys :=
        List.Perm.mem_iff hp |>.mp List.mem_cons_self
      have hxle : x ≤ y := by
        rcases List.mem_cons.mp hyx with rfl | hyx
        · exact Int.le_refl _
        · exact List.rel_of_pairwise_cons (increasing_iff_pairwise.mp h1) hyx
      have hyle : y ≤ x := by
        rcases List.mem_cons.mp hxy with rfl | hxy
        · exact Int.le_refl _
        · exact List.rel_of_pairwise_cons (increasing_iff_pairwise.mp h2) hxy
      have hxyeq : x = y := Int.le_antisymm hxle hyle
      subst hxyeq
      have hperm : xs.Perm ys := List.Perm.cons_inv hp
      congr 1
      exact ih hperm (increasing_tail h1) (increasing_tail h2)

/-! ## First index of a predicate -/

/-- The least index `i` with `p xs[i]! = true`; `none` if there is none. -/
private def firstIdx (p : Int → Bool) : List Int → Option Nat
  | [] => none
  | x :: xs => if p x then some 0 else (firstIdx p xs).map (· + 1)

private theorem firstIdx_spec (p : Int → Bool) : ∀ (xs : List Int) (i : Nat),
    firstIdx p xs = some i ↔
      ((xs[i]?.map p) = some true ∧ ∀ j, j < i → (xs[j]?.map p) = some false) := by
  intro xs
  induction xs with
  | nil => intro i; simp [firstIdx]
  | cons x xs ih =>
    intro i
    by_cases hpx : p x = true
    · rw [show firstIdx p (x :: xs) = some 0 from by
        rw [firstIdx, if_pos hpx]]
      simp only [Option.some.injEq]
      constructor
      · rintro rfl
        refine ⟨by simp [hpx], ?_⟩
        intro j hjlt
        exact absurd hjlt (Nat.not_lt_zero j)
      · rintro ⟨h2, h3⟩
        rcases Nat.eq_zero_or_pos i with rfl | hipos
        · rfl
        · exfalso
          have h0 : (x :: xs)[0]?.map p = some false := h3 0 hipos
          simp only [List.getElem?_cons_zero, hpx, Option.map_some] at h0
          simp at h0
    · rw [show firstIdx p (x :: xs) = (firstIdx p xs).map (· + 1) from by
        rw [firstIdx, if_neg hpx]]
      rw [Option.map_eq_some_iff]
      constructor
      · rintro ⟨i', hiss, rfl⟩
        have hrec := (ih i').mp hiss
        refine ⟨?_, ?_⟩
        · rw [List.getElem?_cons_succ]
          exact hrec.1
        · intro j hjlt
          rcases Nat.eq_zero_or_pos j with rfl | hjpos
          · simp only [List.getElem?_cons_zero, hpx, Option.map_some]
          · rw [show (x :: xs)[j]? = xs[j-1]? from by
              have := List.getElem?_cons_succ (i := j - 1) (a := x) (l := xs)
              rw [show j - 1 + 1 = j from by omega] at this
              exact this]
            exact hrec.2 (j-1) (by omega)
      · rintro ⟨h2, h3⟩
        rcases Nat.eq_zero_or_pos i with rfl | hipos
        · exfalso
          simp only [List.getElem?_cons_zero, Option.map_some] at h2
          simp_all
        · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
          refine ⟨i', (ih i').mpr ⟨?_, ?_⟩, rfl⟩
          · rw [List.getElem?_cons_succ] at h2
            exact h2
          · intro j hjlt
            have hj := h3 (j+1) (by omega)
            rw [List.getElem?_cons_succ] at hj
            exact hj

/-! ## Maximum / minimum argument -/

/-- Fold computing the maximum of a list. -/
private def maxAux : Option Int → List Int → Option Int
  | acc, [] => acc
  | none, x :: xs => maxAux (some x) xs
  | some m, x :: xs => maxAux (some (max m x)) xs

private def maxOf (xs : List Int) : Option Int := maxAux none xs

private def minAux : Option Int → List Int → Option Int
  | acc, [] => acc
  | none, x :: xs => minAux (some x) xs
  | some m, x :: xs => minAux (some (min m x)) xs

private def minOf (xs : List Int) : Option Int := minAux none xs

private theorem maxAux_spec : ∀ (xs : List Int) (acc : Option Int) (m : Int),
    maxAux acc xs = some m →
      (∀ v, acc = some v → v ≤ m) ∧ (∀ x ∈ xs, x ≤ m) ∧
      (acc = some m ∨ m ∈ xs) := by
  intro xs
  induction xs with
  | nil =>
    intro acc m h
    cases acc with
    | none => simp only [maxAux] at h; simp at h
    | some v =>
      simp only [maxAux, Option.some.injEq] at h
      subst h
      refine ⟨fun w hw => ?_, ?_, Or.inl rfl⟩
      · simp only [Option.some.injEq] at hw
        subst hw
        exact Int.le_refl v
      · intro x hx; simp at hx
  | cons y ys ih =>
    intro acc m h
    cases acc with
    | none =>
      rw [show maxAux none (y :: ys) = maxAux (some y) ys from rfl] at h
      obtain ⟨h1, h2, h3⟩ := ih (some y) m h
      have hyle : y ≤ m := h1 y rfl
      refine ⟨fun v hv => by simp at hv, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hyle
        · exact h2 x hx
      · rcases h3 with hys | hys
        · rw [Option.some.injEq] at hys
          exact Or.inr (by rw [← hys]; simp)
        · exact Or.inr (List.mem_cons.mpr (Or.inr hys))
    | some v =>
      rw [show maxAux (some v) (y :: ys) = maxAux (some (max v y)) ys from rfl] at h
      obtain ⟨h1, h2, h3⟩ := ih (some (max v y)) m h
      have hmle : max v y ≤ m := h1 (max v y) rfl
      refine ⟨fun w hw => Int.le_trans (by
          simp only [Option.some.injEq] at hw; subst hw; exact Int.le_max_left v y) hmle,
        ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Int.le_trans (Int.le_max_right v x) hmle
        · exact h2 x hx
      · rcases h3 with hys | hys
        · rw [Option.some.injEq] at hys
          by_cases hvy : v ≤ y
          · have hmax : max v y = y := Int.max_eq_right hvy
            have hmy : m = y := hys.symm.trans hmax
            exact Or.inr (by rw [← hmy]; simp)
          · have hmax : max v y = v := Int.max_eq_left (by omega)
            have hmv : m = v := hys.symm.trans hmax
            exact Or.inl (by rw [hmv])
        · exact Or.inr (List.mem_cons.mpr (Or.inr hys))

private theorem minAux_spec : ∀ (xs : List Int) (acc : Option Int) (m : Int),
    minAux acc xs = some m →
      (∀ v, acc = some v → m ≤ v) ∧ (∀ x ∈ xs, m ≤ x) ∧
      (acc = some m ∨ m ∈ xs) := by
  intro xs
  induction xs with
  | nil =>
    intro acc m h
    cases acc with
    | none => simp only [minAux] at h; simp at h
    | some v =>
      simp only [minAux, Option.some.injEq] at h
      subst h
      refine ⟨fun w hw => ?_, ?_, Or.inl rfl⟩
      · simp only [Option.some.injEq] at hw
        subst hw
        exact Int.le_refl v
      · intro x hx; simp at hx
  | cons y ys ih =>
    intro acc m h
    cases acc with
    | none =>
      rw [show minAux none (y :: ys) = minAux (some y) ys from rfl] at h
      obtain ⟨h1, h2, h3⟩ := ih (some y) m h
      have hyle : m ≤ y := h1 y rfl
      refine ⟨fun v hv => by simp at hv, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hyle
        · exact h2 x hx
      · rcases h3 with hys | hys
        · rw [Option.some.injEq] at hys
          exact Or.inr (by rw [← hys]; simp)
        · exact Or.inr (List.mem_cons.mpr (Or.inr hys))
    | some v =>
      rw [show minAux (some v) (y :: ys) = minAux (some (min v y)) ys from rfl] at h
      obtain ⟨h1, h2, h3⟩ := ih (some (min v y)) m h
      have hmle : m ≤ min v y := h1 (min v y) rfl
      refine ⟨fun w hw => Int.le_trans hmle (by
          simp only [Option.some.injEq] at hw; subst hw; exact Int.min_le_left v y),
        ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Int.le_trans hmle (Int.min_le_right v x)
        · exact h2 x hx
      · rcases h3 with hys | hys
        · rw [Option.some.injEq] at hys
          by_cases hvy : v ≤ y
          · have hmin : min v y = v := Int.min_eq_left hvy
            have hmv : m = v := hys.symm.trans hmin
            exact Or.inl (by rw [hmv])
          · have hmin : min v y = y := Int.min_eq_right (by omega)
            have hmy : m = y := hys.symm.trans hmin
            exact Or.inr (by rw [← hmy]; simp)
        · exact Or.inr (List.mem_cons.mpr (Or.inr hys))

/-- Maximum and least index attaining it. -/
private def maximumArg (xs : List Int) : Option Nat :=
  match maxOf xs with
  | none => none
  | some m => firstIdx (fun x => decide (x = m)) xs

/-- Minimum and least index attaining it. -/
private def minimumArg (xs : List Int) : Option Nat :=
  match minOf xs with
  | none => none
  | some m => firstIdx (fun x => decide (x = m)) xs

/-! ## Value precedence -/

/-- Every occurrence of `after` is strictly preceded by `before`. -/
def valuePrecedeProp (before after : Int) (xs : List Int) : Prop :=
  ∀ j : Nat, xs[j]? = some after → ∃ i : Nat, i < j ∧ xs[i]? = some before

/-- Boolean twin of `valuePrecedeProp`. -/
def valuePrecedeB (before after : Int) (xs : List Int) : Bool :=
  (List.range xs.length).all (fun i =>
    (xs[i]? != some after) ||
    (List.range i).any (fun k => xs[k]? == some before))

theorem valuePrecedeB_iff (before after : Int) (xs : List Int) :
    valuePrecedeB before after xs = true ↔ valuePrecedeProp before after xs := by
  unfold valuePrecedeB valuePrecedeProp
  rw [List.all_eq_true]
  constructor
  · intro h j hj
    by_cases hjlt : j < xs.length
    · have hj2 := h j (by simp only [List.mem_range]; omega)
      simp only [Bool.or_eq_true] at hj2
      rcases hj2 with h1 | h1
      · rw [hj] at h1
        simp_all
      · rw [List.any_eq_true] at h1
        obtain ⟨k, hkmem, hk⟩ := h1
        rw [optBeq_iff] at hk
        exact ⟨k, by simpa using hkmem, hk⟩
    · exfalso
      have hnone : xs[j]? = none := List.getElem?_eq_none_iff.mpr (by omega)
      rw [hnone] at hj
      simp at hj
  · intro h j hjmem
    simp only [List.mem_range] at hjmem
    by_cases hjeq : xs[j]? = some after
    · obtain ⟨k, hklt, hk⟩ := h j hjeq
      simp only [Bool.or_eq_true]
      refine Or.inr ?_
      rw [List.any_eq_true]
      exact ⟨k, by simp only [List.mem_range]; omega, by rw [optBeq_iff]; exact hk⟩
    · simp only [Bool.or_eq_true]
      exact Or.inl (by rw [optBne_iff]; exact hjeq)

/-- For consecutive pairs of `order`, each value precedes the next. -/
def valuePrecedeChainProp (order : List Int) (xs : List Int) : Prop :=
  match order with
  | [] => True
  | [_] => True
  | a :: b :: rest => valuePrecedeProp a b xs ∧ valuePrecedeChainProp (b :: rest) xs

def valuePrecedeChainB (order : List Int) (xs : List Int) : Bool :=
  match order with
  | [] => true
  | [_] => true
  | a :: b :: rest => valuePrecedeB a b xs && valuePrecedeChainB (b :: rest) xs

theorem valuePrecedeChainB_iff (order xs : List Int) :
    valuePrecedeChainB order xs = true ↔ valuePrecedeChainProp order xs := by
  induction order with
  | nil => simp [valuePrecedeChainB, valuePrecedeChainProp]
  | cons a order ih =>
    cases order with
    | nil => simp [valuePrecedeChainB, valuePrecedeChainProp]
    | cons b rest =>
      simp only [valuePrecedeChainB, valuePrecedeChainProp, Bool.and_eq_true,
        valuePrecedeB_iff, ih]

/-- Sequential value precedence: every element `v ≥ 2` is preceded by an
    occurrence of `v - 1` (the documented meaning of
    `fzn_seq_precede_chain_int`). -/
def seqPrecedeChainProp (xs : List Int) : Prop :=
  ∀ (j : Nat) (v : Int), xs[j]? = some v → 2 ≤ v →
    ∃ i : Nat, i < j ∧ xs[i]? = some (v - 1)

def seqPrecedeChainB (xs : List Int) : Bool :=
  (List.range xs.length).all (fun i =>
    match xs[i]? with
    | some v => !(2 ≤ v) || (List.range i).any (fun k => xs[k]? == some (v - 1))
    | none => true)

theorem seqPrecedeChainB_iff (xs : List Int) :
    seqPrecedeChainB xs = true ↔ seqPrecedeChainProp xs := by
  unfold seqPrecedeChainB seqPrecedeChainProp
  rw [List.all_eq_true]
  constructor
  · intro h j v hjv hv2
    by_cases hjlt : j < xs.length
    · have hj2 := h j (by simp only [List.mem_range]; omega)
      rw [hjv] at hj2
      simp only [Bool.or_eq_true] at hj2
      rcases hj2 with h1 | h1
      · simp only [Bool.not_eq_true'] at h1
        exact absurd hv2 (decide_eq_false_iff_not.mp h1)
      · rw [List.any_eq_true] at h1
        obtain ⟨k, hkmem, hk⟩ := h1
        rw [optBeq_iff] at hk
        exact ⟨k, by simpa using hkmem, hk⟩
    · exfalso
      have hnone : xs[j]? = none := List.getElem?_eq_none_iff.mpr (by omega)
      rw [hnone] at hjv
      simp at hjv
  · intro h j hjmem
    simp only [List.mem_range] at hjmem
    cases hx : xs[j]? with
    | none => rfl
    | some v =>
      simp only [Bool.or_eq_true, Bool.not_eq_true']
      by_cases hv2 : 2 ≤ v
      · obtain ⟨k, hklt, hk⟩ := h j v hx hv2
        refine Or.inr ?_
        rw [List.any_eq_true]
        exact ⟨k, by simp only [List.mem_range]; omega, by rw [optBeq_iff]; exact hk⟩
      · exact Or.inl (decide_eq_false_iff_not.mpr hv2)

/-! ## Stable argument sort -/

/-- The upstream loop `forall (j in 1..length(xs)-1)` reads the 1-based
    positions `permutation[j]` and `permutation[j+1]`, and evaluates
    `xs[permutation[j]]` and `xs[permutation[j+1]]`.  This predicate states
    exactly that loop: both positions of `perm` must exist and be valid
    1-based indices of `xs`, the values of `xs` there are nondecreasing, and
    equal values force the earlier position to have the smaller index
    (stability). -/
private def idxSortedStable (xs : List Int) (perm : List Int) : Prop :=
  ∀ j, j + 1 < xs.length →
    -- The conjunct `j + 1 < perm.length` proves both `perm[j]!` and
    -- `perm[j+1]!` in bounds; the two range conjuncts prove the
    -- `xs[...]!` accesses in bounds.
    j + 1 < perm.length ∧
    1 ≤ perm[j]! ∧ perm[j]! ≤ (xs.length : Int) ∧
    1 ≤ perm[j+1]! ∧ perm[j+1]! ≤ (xs.length : Int) ∧
    xs[(perm[j]!).toNat - 1]! ≤ xs[(perm[j+1]!).toNat - 1]! ∧
    (xs[(perm[j]!).toNat - 1]! = xs[(perm[j+1]!).toNat - 1]! →
      perm[j]! < perm[j+1]!)

/-- Boolean twin of `idxSortedStable`.  The `decide (j + 1 < perm.length ∧
    ...)` conjunct inside the body carries the same in-bounds premises as the
    Prop version. -/
private def idxSortedStableB (xs : List Int) (perm : List Int) : Bool :=
  (List.range (xs.length - 1)).all (fun j =>
    decide (j + 1 < perm.length ∧
      1 ≤ perm[j]! ∧ perm[j]! ≤ (xs.length : Int) ∧
      1 ≤ perm[j+1]! ∧ perm[j+1]! ≤ (xs.length : Int) ∧
      xs[(perm[j]!).toNat - 1]! ≤ xs[(perm[j+1]!).toNat - 1]! ∧
      (xs[(perm[j]!).toNat - 1]! = xs[(perm[j+1]!).toNat - 1]! →
        perm[j]! < perm[j+1]!)))

private theorem idxSortedStableB_iff (xs : List Int) (perm : List Int) :
    idxSortedStableB xs perm = true ↔ idxSortedStable xs perm := by
  unfold idxSortedStableB idxSortedStable
  rw [List.all_eq_true]
  constructor
  · intro h j hj
    have hdec := h j (by simp only [List.mem_range]; omega)
    exact of_decide_eq_true hdec
  · intro h j hjmem
    simp only [List.mem_range] at hjmem
    exact decide_eq_true (h j (by omega))

/-- Full arg-sort specification: `perm` is globally duplicate-free and the
    upstream loop, read literally, holds.

    The upstream decomposition `fzn_arg_sort_int.mzn` is
    `all_different(permutation) /\
     forall (j in 1..length(xs)-1)
       (xs[permutation[j]] <= xs[permutation[j+1]] /\
        (xs[permutation[j]] == xs[permutation[j+1]] ->
         permutation[j] < permutation[j+1]))`.
    For `length(xs) ≥ 2` the loop reads `permutation[1..length(xs)]`; a
    shorter `perm` or a loop entry outside `1..xs.length` leaves an access
    undefined, and `idxSortedStable` rejects such a call.  For
    `length(xs) ≤ 1` the range `1..length(xs)-1` is empty, so the loop is
    vacuous: only `all_different(permutation)` remains, and an empty or
    arbitrary-position `perm` is accepted when duplicate-free.  There is
    therefore no unconditional `xs.length ≤ perm.length` gate and no
    prefix range gate beyond the per-iteration premises in
    `idxSortedStable`. -/
def argSortProp (xs perm : List Int) : Prop :=
  perm.Nodup ∧
  idxSortedStable xs perm

/-- Boolean twin of `argSortProp`. -/
def argSortB (xs perm : List Int) : Bool :=
  decide perm.Nodup &&
  idxSortedStableB xs perm

theorem argSortB_iff (xs perm : List Int) :
    argSortB xs perm = true ↔ argSortProp xs perm := by
  simp only [argSortB, argSortProp, Bool.and_eq_true, decide_eq_true_iff,
    idxSortedStableB_iff]

/-! ## Sort -/

/-- `fzn_sort(xs, ys)`: the pinned decomposition
    `let { array [index_set(xs)] of var index_set(ys): p; }
     in forall (i in index_set(xs)) (ys[p[i]] == xs[i]) /\
        alldifferent(p) /\ increasing(ys)`
    existentially quantifies the index array `p`: it is injective and takes
    values in `index_set(ys)`.  Picking a distinct position of `ys` for every
    occurrence of `xs` is possible exactly when every value occurs in `ys` at
    least as often as in `xs`, so the relation is: `ys` is nondecreasing and
    `xs` is a sub-multiset of `ys`.  A longer `ys` is therefore permitted by
    the raw decomposition (its extra entries only have to respect
    `increasing`); equality of the two lengths is not an upstream premise.
    For equal lengths the relation is the usual "`ys` is a sorted permutation
    of `xs`". -/
def sortProp (xs ys : List Int) : Prop :=
  increasing ys ∧ ∀ v, v ∈ xs → xs.count v ≤ ys.count v

/-- Boolean twin of `sortProp`. -/
def sortB (xs ys : List Int) : Bool :=
  increasingB ys && xs.all (fun v => decide (xs.count v ≤ ys.count v))

theorem sortB_iff (xs ys : List Int) :
    sortB xs ys = true ↔ sortProp xs ys := by
  simp only [sortB, sortProp, Bool.and_eq_true, List.all_eq_true,
    increasingB_iff, decide_eq_true_iff]

/-! ## Argument decoders -/

/-- Decode two integer-array arguments. -/
def twoIntArrays' (args : List Value) : Option (List Int × List Int) :=
  match args with
  | [.array xs, .array ys] =>
    match valueInts xs, valueInts ys with
    | some a, some b => some (a, b)
    | _, _ => none
  | _ => none

private def twoIntArrays (args : List Value) : Option (List Int × List Int) :=
  twoIntArrays' args

/-- Decode a single integer-array argument. -/
private def oneIntArray (args : List Value) : Option (List Int) :=
  match args with
  | [.array xs] => valueInts xs
  | _ => none

/-- Decode a single boolean-array argument. -/
private def oneBoolArray (args : List Value) : Option (List Bool) :=
  match args with
  | [.array xs] => valueBools xs
  | _ => none

/-- Decode (array of int, int) arguments. -/
private def arrayAndInt (args : List Value) : Option (List Int × Int) :=
  match args with
  | [.array xs, .int y] => (valueInts xs).map (fun a => (a, y))
  | _ => none

/-- Decode (int, int, array of int) arguments. -/
private def twoIntsAndArray (args : List Value) : Option (Int × Int × List Int) :=
  match args with
  | [.int x, .int y, .array xs] => (valueInts xs).map (fun a => (x, y, a))
  | _ => none

/-! ## The interpretations -/

/-- Mathematical interpretations of the lex/sort/value-precedence
    global-constraint predicates.  A wrong argument shape yields
    `False`. -/
def lexSortInterp : LeanFzn.Semantics.PredicateInterpretation := fun x =>
  match x.name with
  | "fzn_lex_less_int" => fun args =>
    match twoIntArrays args with
    | some (a, b) => lexLess a b
    | none => False
  | "fzn_lex_lesseq_int" => fun args =>
    match twoIntArrays args with
    | some (a, b) => lexLesseq a b
    | none => False
  | "fzn_increasing_int" => fun args =>
    match oneIntArray args with
    | some a => increasing a
    | none => False
  | "fzn_increasing_bool" => fun args =>
    match oneBoolArray args with
    | some a => increasingBool a
    | none => False
  | "fzn_strictly_increasing_int" => fun args =>
    match oneIntArray args with
    | some a => strictlyIncreasing a
    | none => False
  | "fzn_sort" => fun args =>
    match twoIntArrays args with
    | some (a, b) => sortProp a b
    | none => False
  | "fzn_arg_sort_int" => fun args =>
    match twoIntArrays args with
    | some (a, b) => argSortProp a b
    | none => False
  | "fzn_maximum_arg_int" => fun args =>
    match arrayAndInt args with
    | some (a, i) =>
      match maximumArg a with
      | none => False
      | some k => i = (k : Int) + 1
    | none => False
  | "fzn_minimum_arg_int" => fun args =>
    match arrayAndInt args with
    | some (a, i) =>
      match minimumArg a with
      | none => False
      | some k => i = (k : Int) + 1
    | none => False
  | "fzn_value_precede_int" => fun args =>
    match twoIntsAndArray args with
    | some (b, a, xs) => valuePrecedeProp b a xs
    | none => False
  | "fzn_value_precede_chain_int" => fun args =>
    match twoIntArrays args with
    | some (o, a) => valuePrecedeChainProp o a
    | none => False
  | "fzn_seq_precede_chain_int" => fun args =>
    match oneIntArray args with
    | some a => seqPrecedeChainProp a
    | none => False
  | _ => fun _ => False

/-- **Executable twin of `lexSortInterp`**: computes the truth of the
    lex/sort/value-precedence interpretations; `false` on a wrong
    shape. -/
def lexSortInterpB : LeanFzn.Ident → List Value → Bool := fun x =>
  match x.name with
  | "fzn_lex_less_int" => fun args =>
    match twoIntArrays args with
    | some (a, b) => lexLessB a b
    | none => false
  | "fzn_lex_lesseq_int" => fun args =>
    match twoIntArrays args with
    | some (a, b) => lexLesseqB a b
    | none => false
  | "fzn_increasing_int" => fun args =>
    match oneIntArray args with
    | some a => increasingB a
    | none => false
  | "fzn_increasing_bool" => fun args =>
    match oneBoolArray args with
    | some a => increasingBoolB a
    | none => false
  | "fzn_strictly_increasing_int" => fun args =>
    match oneIntArray args with
    | some a => strictlyIncreasingB a
    | none => false
  | "fzn_sort" => fun args =>
    match twoIntArrays args with
    | some (a, b) => sortB a b
    | none => false
  | "fzn_arg_sort_int" => fun args =>
    match twoIntArrays args with
    | some (a, b) => argSortB a b
    | none => false
  | "fzn_maximum_arg_int" => fun args =>
    match arrayAndInt args with
    | some (a, i) =>
      match maximumArg a with
      | none => false
      | some k => decide (i = (k : Int) + 1)
    | none => false
  | "fzn_minimum_arg_int" => fun args =>
    match arrayAndInt args with
    | some (a, i) =>
      match minimumArg a with
      | none => false
      | some k => decide (i = (k : Int) + 1)
    | none => false
  | "fzn_value_precede_int" => fun args =>
    match twoIntsAndArray args with
    | some (b, a, xs) => valuePrecedeB b a xs
    | none => false
  | "fzn_value_precede_chain_int" => fun args =>
    match twoIntArrays args with
    | some (o, a) => valuePrecedeChainB o a
    | none => false
  | "fzn_seq_precede_chain_int" => fun args =>
    match oneIntArray args with
    | some a => seqPrecedeChainB a
    | none => false
  | _ => fun _ => false

/-! ## Per-name agreement theorems -/

theorem fzn_lex_less_int_iff (args : List Value) :
    lexSortInterpB (Ident.mk "fzn_lex_less_int") args = true ↔
      lexSortInterp (Ident.mk "fzn_lex_less_int") args := by
  have hB : ∀ args, lexSortInterpB (Ident.mk "fzn_lex_less_int") args
      = match twoIntArrays args with
      | some (a, b) => lexLessB a b
      | none => false
      := fun _ => rfl
  have hI : ∀ args, lexSortInterp (Ident.mk "fzn_lex_less_int") args
      = match twoIntArrays args with
      | some (a, b) => lexLess a b
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : twoIntArrays args with
  | none => simp
  | some p =>
    obtain ⟨a, b⟩ := p
    simp only
    exact lexLessB_iff a b

theorem fzn_lex_lesseq_int_iff (args : List Value) :
    lexSortInterpB (Ident.mk "fzn_lex_lesseq_int") args = true ↔
      lexSortInterp (Ident.mk "fzn_lex_lesseq_int") args := by
  have hB : ∀ args, lexSortInterpB (Ident.mk "fzn_lex_lesseq_int") args
      = match twoIntArrays args with
      | some (a, b) => lexLesseqB a b
      | none => false
      := fun _ => rfl
  have hI : ∀ args, lexSortInterp (Ident.mk "fzn_lex_lesseq_int") args
      = match twoIntArrays args with
      | some (a, b) => lexLesseq a b
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : twoIntArrays args with
  | none => simp
  | some p =>
    obtain ⟨a, b⟩ := p
    simp only
    exact lexLesseqB_iff a b

theorem fzn_increasing_int_iff (args : List Value) :
    lexSortInterpB (Ident.mk "fzn_increasing_int") args = true ↔
      lexSortInterp (Ident.mk "fzn_increasing_int") args := by
  have hB : ∀ args, lexSortInterpB (Ident.mk "fzn_increasing_int") args
      = match oneIntArray args with
      | some a => increasingB a
      | none => false
      := fun _ => rfl
  have hI : ∀ args, lexSortInterp (Ident.mk "fzn_increasing_int") args
      = match oneIntArray args with
      | some a => increasing a
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : oneIntArray args with
  | none => simp
  | some a =>
    simp only
    exact increasingB_iff a

theorem fzn_increasing_bool_iff (args : List Value) :
    lexSortInterpB (Ident.mk "fzn_increasing_bool") args = true ↔
      lexSortInterp (Ident.mk "fzn_increasing_bool") args := by
  have hB : ∀ args, lexSortInterpB (Ident.mk "fzn_increasing_bool") args
      = match oneBoolArray args with
      | some a => increasingBoolB a
      | none => false
      := fun _ => rfl
  have hI : ∀ args, lexSortInterp (Ident.mk "fzn_increasing_bool") args
      = match oneBoolArray args with
      | some a => increasingBool a
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : oneBoolArray args with
  | none => simp
  | some a =>
    simp only
    exact increasingBoolB_iff a

theorem fzn_strictly_increasing_int_iff (args : List Value) :
    lexSortInterpB (Ident.mk "fzn_strictly_increasing_int") args = true ↔
      lexSortInterp (Ident.mk "fzn_strictly_increasing_int") args := by
  have hB : ∀ args, lexSortInterpB (Ident.mk "fzn_strictly_increasing_int") args
      = match oneIntArray args with
      | some a => strictlyIncreasingB a
      | none => false
      := fun _ => rfl
  have hI : ∀ args, lexSortInterp (Ident.mk "fzn_strictly_increasing_int") args
      = match oneIntArray args with
      | some a => strictlyIncreasing a
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : oneIntArray args with
  | none => simp
  | some a =>
    simp only
    exact strictlyIncreasingB_iff a

set_option maxHeartbeats 1000000 in
theorem fzn_sort_iff (args : List Value) :
    lexSortInterpB (Ident.mk "fzn_sort") args = true ↔
      lexSortInterp (Ident.mk "fzn_sort") args := by
  have hB : ∀ args, lexSortInterpB (Ident.mk "fzn_sort") args
      = match twoIntArrays args with
      | some (a, b) => sortB a b
      | none => false
      := fun _ => rfl
  have hI : ∀ args, lexSortInterp (Ident.mk "fzn_sort") args
      = match twoIntArrays args with
      | some (a, b) => sortProp a b
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : twoIntArrays args with
  | none => simp
  | some p =>
    obtain ⟨a, b⟩ := p
    simp only
    exact sortB_iff a b

theorem fzn_arg_sort_int_iff (args : List Value) :
    lexSortInterpB (Ident.mk "fzn_arg_sort_int") args = true ↔
      lexSortInterp (Ident.mk "fzn_arg_sort_int") args := by
  have hB : ∀ args, lexSortInterpB (Ident.mk "fzn_arg_sort_int") args
      = match twoIntArrays args with
      | some (a, b) => argSortB a b
      | none => false
      := fun _ => rfl
  have hI : ∀ args, lexSortInterp (Ident.mk "fzn_arg_sort_int") args
      = match twoIntArrays args with
      | some (a, b) => argSortProp a b
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : twoIntArrays args with
  | none => simp
  | some p =>
    obtain ⟨a, b⟩ := p
    simp only
    exact argSortB_iff a b

set_option maxHeartbeats 1000000 in
theorem fzn_maximum_arg_int_iff (args : List Value) :
    lexSortInterpB (Ident.mk "fzn_maximum_arg_int") args = true ↔
      lexSortInterp (Ident.mk "fzn_maximum_arg_int") args := by
  have hB : ∀ args, lexSortInterpB (Ident.mk "fzn_maximum_arg_int") args
      = match arrayAndInt args with
      | some (a, i) =>
        match maximumArg a with
        | none => false
        | some k => decide (i = (k : Int) + 1)
      | none => false
      := fun _ => rfl
  have hI : ∀ args, lexSortInterp (Ident.mk "fzn_maximum_arg_int") args
      = match arrayAndInt args with
      | some (a, i) =>
        match maximumArg a with
        | none => False
        | some k => i = (k : Int) + 1
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : arrayAndInt args with
  | none => simp
  | some p =>
    obtain ⟨a, i⟩ := p
    simp only
    unfold maximumArg
    cases hm : maxOf a with
    | none => simp
    | some m =>
      simp only
      cases hf : firstIdx (fun x => decide (x = m)) a with
      | none => simp
      | some k => simp only [decide_eq_true_iff]

set_option maxHeartbeats 1000000 in
theorem fzn_minimum_arg_int_iff (args : List Value) :
    lexSortInterpB (Ident.mk "fzn_minimum_arg_int") args = true ↔
      lexSortInterp (Ident.mk "fzn_minimum_arg_int") args := by
  have hB : ∀ args, lexSortInterpB (Ident.mk "fzn_minimum_arg_int") args
      = match arrayAndInt args with
      | some (a, i) =>
        match minimumArg a with
        | none => false
        | some k => decide (i = (k : Int) + 1)
      | none => false
      := fun _ => rfl
  have hI : ∀ args, lexSortInterp (Ident.mk "fzn_minimum_arg_int") args
      = match arrayAndInt args with
      | some (a, i) =>
        match minimumArg a with
        | none => False
        | some k => i = (k : Int) + 1
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : arrayAndInt args with
  | none => simp
  | some p =>
    obtain ⟨a, i⟩ := p
    simp only
    unfold minimumArg
    cases hm : minOf a with
    | none => simp
    | some m =>
      simp only
      cases hf : firstIdx (fun x => decide (x = m)) a with
      | none => simp
      | some k => simp only [decide_eq_true_iff]

theorem fzn_value_precede_int_iff (args : List Value) :
    lexSortInterpB (Ident.mk "fzn_value_precede_int") args = true ↔
      lexSortInterp (Ident.mk "fzn_value_precede_int") args := by
  have hB : ∀ args, lexSortInterpB (Ident.mk "fzn_value_precede_int") args
      = match twoIntsAndArray args with
      | some (b, a, xs) => valuePrecedeB b a xs
      | none => false
      := fun _ => rfl
  have hI : ∀ args, lexSortInterp (Ident.mk "fzn_value_precede_int") args
      = match twoIntsAndArray args with
      | some (b, a, xs) => valuePrecedeProp b a xs
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : twoIntsAndArray args with
  | none => simp
  | some p =>
    obtain ⟨b, a, xs⟩ := p
    simp only
    exact valuePrecedeB_iff b a xs

theorem fzn_value_precede_chain_int_iff (args : List Value) :
    lexSortInterpB (Ident.mk "fzn_value_precede_chain_int") args = true ↔
      lexSortInterp (Ident.mk "fzn_value_precede_chain_int") args := by
  have hB : ∀ args, lexSortInterpB (Ident.mk "fzn_value_precede_chain_int") args
      = match twoIntArrays args with
      | some (o, a) => valuePrecedeChainB o a
      | none => false
      := fun _ => rfl
  have hI : ∀ args, lexSortInterp (Ident.mk "fzn_value_precede_chain_int") args
      = match twoIntArrays args with
      | some (o, a) => valuePrecedeChainProp o a
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : twoIntArrays args with
  | none => simp
  | some p =>
    obtain ⟨o, a⟩ := p
    simp only
    exact valuePrecedeChainB_iff o a

theorem fzn_seq_precede_chain_int_iff (args : List Value) :
    lexSortInterpB (Ident.mk "fzn_seq_precede_chain_int") args = true ↔
      lexSortInterp (Ident.mk "fzn_seq_precede_chain_int") args := by
  have hB : ∀ args, lexSortInterpB (Ident.mk "fzn_seq_precede_chain_int") args
      = match oneIntArray args with
      | some a => seqPrecedeChainB a
      | none => false
      := fun _ => rfl
  have hI : ∀ args, lexSortInterp (Ident.mk "fzn_seq_precede_chain_int") args
      = match oneIntArray args with
      | some a => seqPrecedeChainProp a
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : oneIntArray args with
  | none => simp
  | some a =>
    simp only
    exact seqPrecedeChainB_iff a

/-! ## Decodability gates

`lexSortDecodes` is the Boolean decodability gate of the family: the `isSome`
of the very decoder `lexSortInterp` uses, and `true` outside the family.
`lexSortDecodes_agree` states that the gate cannot distinguish two argument
lists which agree on the shape information that is statically known from a
well-typed call (`ArgsAgree`).  Every decoder in this family inspects the
arguments through `valueInts`/`valueBools`, which see only constructor tags
and array lengths, so the plain `ArgsAgree` hypothesis suffices. -/

/-- Pairing two integer-list decodings preserves `isSome` agreement. -/
private theorem optionPair_isSome_agree {a a' b b' : Option (List Int)}
    (ha : a.isSome = a'.isSome) (hb : b.isSome = b'.isSome) :
    (match a, b with
      | some x, some y => some (x, y)
      | _, _ => none).isSome =
    (match a', b' with
      | some x, some y => some (x, y)
      | _, _ => none).isSome := by
  cases a <;> cases b <;> cases a' <;> cases b' <;> simp_all

/-- The two-integer-array decoder accepts exactly the same argument shapes. -/
theorem twoIntArrays'_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (twoIntArrays' vs).isSome = (twoIntArrays' ws).isSome := by
  have hshape : Value.SameShapeList vs ws := ArgsAgree.sameShape h
  rcases vs with _ | ⟨v0, vs1⟩ <;> rcases ws with _ | ⟨w0, ws1⟩
  · rfl
  · cases hshape
  · cases hshape
  · cases hshape with
    | cons hhead htail =>
      cases htail with
      | nil =>
        cases hhead with
        | bool _ _ => simp [twoIntArrays']
        | int _ _ => simp [twoIntArrays']
        | setOfInt _ _ => simp [twoIntArrays']
        | @array _ _ _ => simp [twoIntArrays']
      | cons hhead2 htail2 =>
        cases htail2 with
        | nil =>
          cases hhead with
          | bool _ _ => simp [twoIntArrays']
          | int _ _ => simp [twoIntArrays']
          | setOfInt _ _ => simp [twoIntArrays']
          | @array xs ys harr =>
            cases hhead2 with
            | bool _ _ => simp [twoIntArrays']
            | int _ _ => simp [twoIntArrays']
            | setOfInt _ _ => simp [twoIntArrays']
            | @array xs2 ys2 harr2 =>
              simp only [twoIntArrays']
              exact optionPair_isSome_agree
                (valueInts_isSome_sameShape harr)
                (valueInts_isSome_sameShape harr2)
        | cons _ _ => simp [twoIntArrays']

/-- The private alias `twoIntArrays` accepts exactly the same argument
    shapes. -/
theorem twoIntArrays_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (twoIntArrays vs).isSome = (twoIntArrays ws).isSome :=
  twoIntArrays'_isSome_agree h

/-- The single-integer-array decoder accepts exactly the same argument
    shapes. -/
theorem oneIntArray_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (oneIntArray vs).isSome = (oneIntArray ws).isSome := by
  have hshape : Value.SameShapeList vs ws := ArgsAgree.sameShape h
  rcases vs with _ | ⟨v0, vs1⟩ <;> rcases ws with _ | ⟨w0, ws1⟩
  · rfl
  · cases hshape
  · cases hshape
  · cases hshape with
    | cons hhead htail =>
      cases htail with
      | nil =>
        cases hhead with
        | bool _ _ => simp [oneIntArray]
        | int _ _ => simp [oneIntArray]
        | setOfInt _ _ => simp [oneIntArray]
        | @array xs ys harr =>
          simp only [oneIntArray]
          exact valueInts_isSome_sameShape harr
      | cons _ _ => simp [oneIntArray]

/-- The single-boolean-array decoder accepts exactly the same argument
    shapes. -/
theorem oneBoolArray_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (oneBoolArray vs).isSome = (oneBoolArray ws).isSome := by
  have hshape : Value.SameShapeList vs ws := ArgsAgree.sameShape h
  rcases vs with _ | ⟨v0, vs1⟩ <;> rcases ws with _ | ⟨w0, ws1⟩
  · rfl
  · cases hshape
  · cases hshape
  · cases hshape with
    | cons hhead htail =>
      cases htail with
      | nil =>
        cases hhead with
        | bool _ _ => simp [oneBoolArray]
        | int _ _ => simp [oneBoolArray]
        | setOfInt _ _ => simp [oneBoolArray]
        | @array xs ys harr =>
          simp only [oneBoolArray]
          exact valueBools_isSome_sameShape harr
      | cons _ _ => simp [oneBoolArray]

/-- The (array, int) decoder accepts exactly the same argument shapes. -/
theorem arrayAndInt_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (arrayAndInt vs).isSome = (arrayAndInt ws).isSome := by
  have hshape : Value.SameShapeList vs ws := ArgsAgree.sameShape h
  rcases vs with _ | ⟨v0, vs1⟩ <;> rcases ws with _ | ⟨w0, ws1⟩
  · rfl
  · cases hshape
  · cases hshape
  · cases hshape with
    | cons hhead htail =>
      cases htail with
      | nil =>
        cases hhead with
        | bool _ _ => simp [arrayAndInt]
        | int _ _ => simp [arrayAndInt]
        | setOfInt _ _ => simp [arrayAndInt]
        | @array _ _ _ => simp [arrayAndInt]
      | cons hhead2 htail2 =>
        cases htail2 with
        | nil =>
          cases hhead with
          | bool _ _ => simp [arrayAndInt]
          | int _ _ => simp [arrayAndInt]
          | setOfInt _ _ => simp [arrayAndInt]
          | @array xs ys harr =>
            cases hhead2 with
            | bool _ _ => simp [arrayAndInt]
            | int y y' =>
              simp only [arrayAndInt, Option.isSome_map]
              exact valueInts_isSome_sameShape harr
            | setOfInt _ _ => simp [arrayAndInt]
            | @array _ _ _ => simp [arrayAndInt]
        | cons _ _ => simp [arrayAndInt]

/-- The (int, int, array) decoder accepts exactly the same argument shapes. -/
theorem twoIntsAndArray_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (twoIntsAndArray vs).isSome = (twoIntsAndArray ws).isSome := by
  have hshape : Value.SameShapeList vs ws := ArgsAgree.sameShape h
  rcases vs with _ | ⟨v0, vs1⟩ <;> rcases ws with _ | ⟨w0, ws1⟩
  · rfl
  · cases hshape
  · cases hshape
  · cases hshape with
    | cons hhead htail =>
      cases htail with
      | nil =>
        cases hhead with
        | bool _ _ => simp [twoIntsAndArray]
        | int _ _ => simp [twoIntsAndArray]
        | setOfInt _ _ => simp [twoIntsAndArray]
        | @array _ _ _ => simp [twoIntsAndArray]
      | cons hhead2 htail2 =>
        cases htail2 with
        | nil =>
          cases hhead with
          | bool _ _ => simp [twoIntsAndArray]
          | int _ _ => simp [twoIntsAndArray]
          | setOfInt _ _ => simp [twoIntsAndArray]
          | @array _ _ _ => simp [twoIntsAndArray]
        | cons hhead3 htail3 =>
          cases htail3 with
          | nil =>
            cases hhead with
            | bool _ _ => simp [twoIntsAndArray]
            | int _ _ =>
              cases hhead2 with
              | bool _ _ => simp [twoIntsAndArray]
              | int _ _ =>
                cases hhead3 with
                | bool _ _ => simp [twoIntsAndArray]
                | int _ _ => simp [twoIntsAndArray]
                | setOfInt _ _ => simp [twoIntsAndArray]
                | @array xs ys harr =>
                  simp only [twoIntsAndArray, Option.isSome_map]
                  exact valueInts_isSome_sameShape harr
              | setOfInt _ _ => simp [twoIntsAndArray]
              | @array _ _ _ => simp [twoIntsAndArray]
            | setOfInt _ _ => simp [twoIntsAndArray]
            | @array _ _ _ => simp [twoIntsAndArray]
          | cons _ _ => simp [twoIntsAndArray]

/-- Boolean decodability gate of the lex/sort/value-precedence family.
    Neutral (`true`) outside the family. -/
def lexSortDecodes (n : String) (args : List Value) : Bool :=
  match n with
  | "fzn_lex_less_int" => (twoIntArrays args).isSome
  | "fzn_lex_lesseq_int" => (twoIntArrays args).isSome
  | "fzn_increasing_int" => (oneIntArray args).isSome
  | "fzn_increasing_bool" => (oneBoolArray args).isSome
  | "fzn_strictly_increasing_int" => (oneIntArray args).isSome
  | "fzn_sort" => (twoIntArrays args).isSome
  | "fzn_arg_sort_int" => (twoIntArrays args).isSome
  | "fzn_maximum_arg_int" => (arrayAndInt args).isSome
  | "fzn_minimum_arg_int" => (arrayAndInt args).isSome
  | "fzn_value_precede_int" => (twoIntsAndArray args).isSome
  | "fzn_value_precede_chain_int" => (twoIntArrays args).isSome
  | "fzn_seq_precede_chain_int" => (oneIntArray args).isSome
  | _ => true

/-- The decodability gate is invariant under `ArgsAgree`. -/
theorem lexSortDecodes_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) (n : String) :
    lexSortDecodes n vs = lexSortDecodes n ws := by
  unfold lexSortDecodes
  split
  · exact twoIntArrays_isSome_agree h
  · exact twoIntArrays_isSome_agree h
  · exact oneIntArray_isSome_agree h
  · exact oneBoolArray_isSome_agree h
  · exact oneIntArray_isSome_agree h
  · exact twoIntArrays_isSome_agree h
  · exact twoIntArrays_isSome_agree h
  · exact arrayAndInt_isSome_agree h
  · exact arrayAndInt_isSome_agree h
  · exact twoIntsAndArray_isSome_agree h
  · exact twoIntArrays_isSome_agree h
  · exact oneIntArray_isSome_agree h
  · rfl

end LeanFzn.Semantics.Globals.LexSort

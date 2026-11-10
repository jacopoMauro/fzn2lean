/-
File: LeanFzn/Compiler/Proofs/SetExpand.lean

Purpose:
  Correctness of the verified set-expansion pass
  (`Compiler/SetExpand.lean`): the expansion is sound (a store of the
  expanded model reconstructs a store of the source model through
  `setStore`) and complete (every source store extends to a store of the
  expanded model through `encodeStore`), and the expansion preserves
  static well-formedness.

Dependencies:
  - LeanFzn.Compiler.SetExpand, LeanFzn.Compiler.Proofs.SetIn,
    LeanFzn.Compiler.Proofs.CompileAux1.
-/

import LeanFzn.Compiler.SetExpand
import LeanFzn.Compiler.Proofs.SetIn
import LeanFzn.Compiler.Proofs.CompileAux1
import LeanFzn.Compiler.Proofs.Fragment
import LeanFzn.Compiler.Proofs.LiteralFold

namespace LeanFzn.Compiler
open LeanFzn LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Semantics.Globals

/-! ## List helpers -/

/-- `eraseDups` removes all duplicates (proved with fuel, because the
    recursive call is on a filtered list). -/
theorem nodup_eraseDups_int_aux : ∀ (n : Nat) (l : List Int), l.length ≤ n → l.eraseDups.Nodup
  | 0, [], _ => by simp
  | 0, _ :: _, h => by simp at h
  | n + 1, [], _ => by simp
  | n + 1, a :: as, h => by
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · intro hmem
        simp only [List.mem_eraseDups, List.mem_filter] at hmem
        simp at hmem
      · apply nodup_eraseDups_int_aux n (as.filter (fun b => !b == a))
        have hle := List.length_filter_le (fun b => !b == a) as
        simp at h
        omega

/-- `eraseDups` removes all duplicates. -/
theorem nodup_eraseDups_int (l : List Int) : l.eraseDups.Nodup :=
  nodup_eraseDups_int_aux l.length l (Nat.le_refl _)

/-- A merge sort does not change duplicateness. -/
theorem nodup_mergeSort_int {l : List Int} (h : l.Nodup) :
    (l.mergeSort (fun a b => decide (a ≤ b))).Nodup :=
  h.perm (List.mergeSort_perm l _).symm

/-- The sorted enumeration of a set literal is duplicate-free. -/
theorem nodup_sortElems_enum (xs : List Int) :
    ((IntSetValue.enumeration xs).sortElems).Nodup := by
  show (xs.eraseDups.mergeSort (fun a b => decide (a ≤ b))).Nodup
  exact nodup_mergeSort_int (nodup_eraseDups_int xs)

/-- Membership in the sorted enumeration is membership in the literal. -/
theorem mem_sortElems_enum {xs : List Int} {x : Int} :
    x ∈ (IntSetValue.enumeration xs).sortElems ↔ x ∈ xs := by
  show x ∈ xs.eraseDups.mergeSort (fun a b => decide (a ≤ b)) ↔ x ∈ xs
  rw [List.mem_mergeSort, List.mem_eraseDups]

/-- The element list of an interval is duplicate-free. -/
theorem nodup_setElems_interval (lo hi : Int) :
    (setElems (.interval lo hi)).Nodup := by
  by_cases h : hi < lo
  · simp [setElems, h]
  · rw [show setElems (.interval lo hi) =
      List.map (fun k : Nat => lo + (k : Int))
        (List.range ((hi - lo + 1).toNat)) from by
      simp [setElems, h]]
    refine List.Pairwise.map _ ?_ List.nodup_range
    intro a b hab heq
    apply hab
    omega

/-- Membership in the element list of an interval. -/
theorem mem_setElems_interval' {lo hi x : Int} :
    x ∈ setElems (.interval lo hi) ↔ lo ≤ x ∧ x ≤ hi := by
  rw [← setElems_mem_iff]
  rfl

/-! ## Universe properties -/

/-- The universe of a declared set type is duplicate-free. -/
theorem setUniverse?_nodup {ty : BasicVarType} {us : List Int}
    (h : setUniverse? ty = some us) : us.Nodup := by
  cases ty with
  | par t => simp [setUniverse?] at h
  | intRange lo hi => simp [setUniverse?] at h
  | intSet xs => simp [setUniverse?] at h
  | setOfIntRange lo hi =>
      simp only [setUniverse?, Option.some.injEq] at h
      subst h
      exact nodup_setElems_interval lo hi
  | setOfIntSet xs =>
      simp only [setUniverse?, Option.some.injEq] at h
      subst h
      exact nodup_sortElems_enum xs

/-- Membership in the universe is exactly membership in the declared
    set type's admitted value set. -/
theorem setUniverse?_mem {ty : BasicVarType} {us : List Int}
    (h : setUniverse? ty = some us) {v : Int} :
    v ∈ us ↔ ∃ sv : IntSetValue, ty.contains (.setOfInt sv) ∧ sv.Contains v := by
  cases ty with
  | par t => simp [setUniverse?] at h
  | intRange lo hi => simp [setUniverse?] at h
  | intSet xs => simp [setUniverse?] at h
  | setOfIntRange lo hi =>
      simp only [setUniverse?, Option.some.injEq] at h
      subst h
      rw [mem_setElems_interval']
      constructor
      · intro hv
        exact ⟨.interval lo hi, fun x hx => hx, hv⟩
      · rintro ⟨sv, hsv, hmem⟩
        have := hsv v hmem
        simpa using this
  | setOfIntSet xs =>
      simp only [setUniverse?, Option.some.injEq] at h
      subst h
      rw [mem_sortElems_enum]
      constructor
      · intro hv
        exact ⟨.enumeration xs, fun x hx => hx, hv⟩
      · rintro ⟨sv, hsv, hmem⟩
        -- `hsv` holds for every contained element
        exact hsv v hmem

/-! ## Fresh Boolean pairs -/

/-- The names allocated by `freshPairs`, as a range of auxiliary names. -/
theorem freshPairs_names (taken : List String) (start : Nat) :
    ∀ us : List Int,
      (freshPairs taken start us).map Prod.fst =
        (List.range us.length).map (fun j => auxName taken (start + j))
  | [] => rfl
  | v :: vs => by
      simp only [freshPairs, List.map_cons, List.length_cons]
      rw [freshPairs_names taken (start + 1) vs]
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map]
      congr 1
      rw [List.map_congr_left]
      intro j _
      simp only [Function.comp_apply]
      congr 1
      omega

/-- The count after a `freshPairs` run is its start plus its length. -/
theorem freshPairs_length (taken : List String) (start : Nat) (us : List Int) :
    (freshPairs taken start us).length = us.length := by
  induction us generalizing start with
  | nil => rfl
  | cons v vs ih => simp [freshPairs, ih]

/-- Distinct positions give distinct fresh names. -/
theorem freshPairs_names_nodup (taken : List String) (start : Nat) (us : List Int) :
    ((freshPairs taken start us).map Prod.fst).Nodup := by
  rw [freshPairs_names]
  refine List.Pairwise.map _ ?_ List.nodup_range
  intro j k hjk heq
  apply hjk
  have h := auxName_inj (taken := taken) heq
  omega

/-- The values of a `freshPairs` run are the universe values. -/
theorem freshPairs_values (taken : List String) (start : Nat) (us : List Int) :
    (freshPairs taken start us).map Prod.snd = us := by
  induction us generalizing start with
  | nil => rfl
  | cons v vs ih => simp [freshPairs, ih]

/-- The values of a `freshPairs` run are duplicate-free when the
    universe is. -/
theorem freshPairs_values_nodup (taken : List String) (start : Nat)
    {us : List Int} (h : us.Nodup) :
    ((freshPairs taken start us).map Prod.snd).Nodup := by
  rw [freshPairs_values]
  exact h

/-- A fresh name is outside the taken list. -/
theorem freshPairs_name_not_mem (taken : List String) (start : Nat)
    (us : List Int) {b : String} (hb : b ∈ (freshPairs taken start us).map Prod.fst) :
    b ∉ taken := by
  rw [freshPairs_names] at hb
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hb
  exact auxName_not_mem

/-! ## Pair lists with distinct keys -/

/-- A map is injective on a list whose images are duplicate-free. -/
theorem inj_of_nodup_map' {α β : Type} (f : α → β) :
    ∀ {l : List α}, (l.map f).Nodup → ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y := by
  intro l
  induction l with
  | nil => intro _ x hx; cases hx
  | cons a rest ih =>
      intro hnu x hx y hy hxy
      rw [List.map_cons, List.nodup_cons] at hnu
      rcases List.mem_cons.mp hx with rfl | hx'
      · rcases List.mem_cons.mp hy with rfl | hy'
        · rfl
        · exfalso; exact hnu.1 (List.mem_map.mpr ⟨y, hy', hxy.symm⟩)
      · rcases List.mem_cons.mp hy with rfl | hy'
        · exfalso; exact hnu.1 (List.mem_map.mpr ⟨x, hx', hxy⟩)
        · exact ih hnu.2 x hx' y hy' hxy

/-- In a pair list with duplicate-free first components, the found
    pair at a key is the unique pair with that key. -/
theorem find?_fst_eq_some_of_mem {l : List (String × Int)}
    (hnd : (l.map Prod.fst).Nodup) {x : String} {p : String × Int}
    (hp : p ∈ l) (hx : p.1 = x) :
    l.find? (fun q => q.1 = x) = some p := by
  induction l with
  | nil => cases hp
  | cons a rest ih =>
      rw [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨hnot, hndr⟩ := hnd
      by_cases hax : a.1 = x
      · have hpa : p = a := by
          rcases List.mem_cons.mp hp with rfl | hpr
          · rfl
          · exfalso
            apply hnot
            exact List.mem_map.mpr ⟨p, hpr, by rw [hx, hax]⟩
        subst hpa
        rw [List.find?_cons_of_pos]
        simpa using hax
      · have hpr : p ∈ rest := by
          rcases List.mem_cons.mp hp with hpa | hpr
          · exfalso
            subst hpa
            exact hax hx
          · exact hpr
        rw [List.find?_cons_of_neg]
        · exact ih hndr hpr
        · simpa using hax

/-- In a pair list with duplicate-free second components, the found
    pair at a value is the unique pair with that value. -/
theorem find?_snd_eq_some_of_mem {l : List (String × Int)}
    (hnd : (l.map Prod.snd).Nodup) {v : Int} {p : String × Int}
    (hp : p ∈ l) (hv : p.2 = v) :
    l.find? (fun q => q.2 = v) = some p := by
  induction l with
  | nil => cases hp
  | cons a rest ih =>
      rw [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨hnot, hndr⟩ := hnd
      by_cases hav : a.2 = v
      · have hpa : p = a := by
          rcases List.mem_cons.mp hp with rfl | hpr
          · rfl
          · exfalso
            apply hnot
            exact List.mem_map.mpr ⟨p, hpr, by rw [hv, hav]⟩
        subst hpa
        rw [List.find?_cons_of_pos]
        simpa using hav
      · have hpr : p ∈ rest := by
          rcases List.mem_cons.mp hp with hpa | hpr
          · exfalso
            subst hpa
            exact hav hv
          · exact hpr
        rw [List.find?_cons_of_neg]
        · exact ih hndr hpr
        · simpa using hav

/-! ## Fresh Boolean lookups -/

/-- The Boolean name attached to a value is the unique pair's name. -/
theorem SetInfo.boolAt_eq_some_of_mem {i : SetInfo} {v : Int} {p : String × Int}
    (hnd : (i.bools.map Prod.snd).Nodup) (hp : p ∈ i.bools) (hv : p.2 = v) :
    i.boolAt v = some p.1 := by
  unfold SetInfo.boolAt
  rw [find?_snd_eq_some_of_mem hnd hp hv]
  rfl

/-- A `boolAt` lookup yields a pair of the table. -/
theorem SetInfo.boolAt_some {i : SetInfo} {v : Int} {b : String}
    (h : i.boolAt v = some b) :
    ∃ p, p ∈ i.bools ∧ p.1 = b ∧ p.2 = v := by
  unfold SetInfo.boolAt at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨p, hfind, hpb⟩ := h
  have hmem := List.mem_of_find?_eq_some hfind
  have hpred := List.find?_some hfind
  exact ⟨p, hmem, hpb, by simpa using hpred⟩

/-- A value outside the universe has no Boolean slot. -/
theorem SetInfo.boolAt_eq_none_of_not_mem_values {i : SetInfo} {v : Int}
    (hv : v ∉ i.values) : i.boolAt v = none := by
  unfold SetInfo.boolAt
  rw [Option.map_eq_none_iff, List.find?_eq_none]
  intro p hp hpred
  apply hv
  rw [SetInfo.values, List.mem_map]
  exact ⟨p, hp, by simpa using hpred⟩

/-- The Boolean attached to a name is the unique pair's value. -/
theorem SetInfo.boolValueOf_eq_some_of_mem {i : SetInfo} {x : Ident}
    {p : String × Int} (hnd : (i.bools.map Prod.fst).Nodup)
    (hp : p ∈ i.bools) (hx : p.1 = x.name) :
    i.boolValueOf x = some p.2 := by
  unfold SetInfo.boolValueOf
  rw [find?_fst_eq_some_of_mem hnd hp hx]
  rfl

/-- A `boolValueOf` lookup yields a pair of the table. -/
theorem SetInfo.boolValueOf_some {i : SetInfo} {x : Ident} {v : Int}
    (h : i.boolValueOf x = some v) :
    ∃ p, p ∈ i.bools ∧ p.1 = x.name ∧ p.2 = v := by
  unfold SetInfo.boolValueOf at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨p, hfind, hpv⟩ := h
  have hmem := List.mem_of_find?_eq_some hfind
  have hpred := List.find?_some hfind
  exact ⟨p, hmem, by simpa using hpred, hpv⟩

/-! ## The rebuilt set -/

/-- Membership in the rebuilt set is a true Boolean in the table. -/
theorem SetInfo.mem_rebuilt {i : SetInfo} {s : Store} {v : Int} :
    (i.rebuilt s).Contains v ↔
      ∃ p, p ∈ i.bools ∧ p.2 = v ∧ s (Ident.mk p.1) = some (.bool true) := by
  unfold SetInfo.rebuilt
  change v ∈ (i.bools.filterMap fun p =>
      match s (Ident.mk p.1) with
      | some (.bool true) => some p.2
      | _ => none) ↔ _
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨p, hp, hsome⟩
    cases hs : s (Ident.mk p.1) with
    | none => rw [hs] at hsome; cases hsome
    | some val =>
        cases val with
        | bool b =>
            cases b with
            | false => rw [hs] at hsome; cases hsome
            | true =>
                have hpv : p.2 = v := by
                  have h' : some p.2 = some v := by simpa [hs] using hsome
                  exact Option.some.inj h'
                exact ⟨p, hp, hpv, by rw [hs]⟩
        | int _ => rw [hs] at hsome; cases hsome
        | setOfInt _ => rw [hs] at hsome; cases hsome
        | array _ => rw [hs] at hsome; cases hsome
  · rintro ⟨p, hp, hpv, hstrue⟩
    exact ⟨p, hp, by simp [hstrue, hpv]⟩

/-- Rebuilt membership depends only on the Boolean slots' values. -/
theorem SetInfo.rebuilt_congr_contains {i : SetInfo} {s t : Store}
    (h : ∀ p ∈ i.bools, s (Ident.mk p.1) = t (Ident.mk p.1)) {v : Int} :
    (i.rebuilt s).Contains v ↔ (i.rebuilt t).Contains v := by
  rw [SetInfo.mem_rebuilt, SetInfo.mem_rebuilt]
  constructor
  · rintro ⟨p, hp, hpv, htrue⟩
    exact ⟨p, hp, hpv, by rw [← h p hp]; exact htrue⟩
  · rintro ⟨p, hp, hpv, htrue⟩
    exact ⟨p, hp, hpv, by rw [h p hp]; exact htrue⟩

/-- With a duplicate-free universe, membership in the rebuilt set is
    exactly the truth of the value's Boolean slot. -/
theorem SetInfo.rebuilt_contains_iff_boolAt {i : SetInfo} {s : Store} {v : Int}
    (hnd : (i.bools.map Prod.snd).Nodup) {b : String} (hb : i.boolAt v = some b) :
    (i.rebuilt s).Contains v ↔ s (Ident.mk b) = some (.bool true) := by
  constructor
  · intro h
    obtain ⟨p, hp, hpv, hstrue⟩ := SetInfo.mem_rebuilt.mp h
    obtain ⟨q, hq, hqb, hqv⟩ := SetInfo.boolAt_some hb
    have hpq : p = q := by
      exact inj_of_nodup_map' Prod.snd hnd p hp q hq (by rw [hpv, hqv])
    subst hpq
    rw [hqb] at hstrue
    exact hstrue
  · intro h
    obtain ⟨q, hq, hqb, hqv⟩ := SetInfo.boolAt_some hb
    refine SetInfo.mem_rebuilt.mpr ⟨q, hq, hqv, ?_⟩
    rw [← hqb] at h
    exact h

/-- A value outside the universe is not in the rebuilt set. -/
theorem SetInfo.not_contains_rebuilt {i : SetInfo} {s : Store} {v : Int}
    (hv : v ∉ i.values) : ¬ (i.rebuilt s).Contains v := by
  intro h
  obtain ⟨p, hp, hpv, _⟩ := SetInfo.mem_rebuilt.mp h
  apply hv
  rw [SetInfo.values, List.mem_map]
  exact ⟨p, hp, hpv⟩

/-! ## Expansion-table lookups -/

/-- A member of the set table is found by its name. -/
theorem find_infoOf_eq_some_of_mem {sets : List SetInfo} (hnd : (sets.map (fun i => i.name)).Nodup)
    {i : SetInfo} (hi : i ∈ sets) :
    sets.find? (fun j => j.name = i.name) = some i := by
  induction sets with
  | nil => cases hi
  | cons a rest ih =>
      rw [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨hnot, hndr⟩ := hnd
      by_cases ha : a.name = i.name
      · have hia : i = a := by
          rcases List.mem_cons.mp hi with rfl | hir
          · rfl
          · exfalso
            apply hnot
            exact List.mem_map.mpr ⟨i, hir, by rw [ha]⟩
        subst hia
        rw [List.find?_cons_of_pos]
        simp
      · have hir : i ∈ rest := by
          rcases List.mem_cons.mp hi with rfl | hir
          · exact absurd rfl ha
          · exact hir
        rw [List.find?_cons_of_neg]
        · exact ih hndr hir
        · simpa using ha

/-- A member of the set table is found by `infoOf`. -/
theorem SetExpansion.infoOf_eq_some_of_mem {se : SetExpansion} {i : SetInfo}
    (hnd : se.setNames.Nodup) (hi : i ∈ se.sets) :
    se.infoOf (Ident.mk i.name) = some i := by
  unfold SetExpansion.infoOf
  apply find_infoOf_eq_some_of_mem
  · simpa [SetExpansion.setNames] using hnd
  · exact hi

/-- A name outside the table has no info. -/
theorem SetExpansion.infoOf_eq_none_of_not_mem {se : SetExpansion} {x : Ident}
    (hx : x.name ∉ se.setNames) : se.infoOf x = none := by
  unfold SetExpansion.infoOf
  rw [List.find?_eq_none]
  intro i hi hname
  apply hx
  rw [SetExpansion.setNames, List.mem_map]
  exact ⟨i, hi, by simpa using hname⟩

/-! ### Fast lookup-table twins -/

/-- Membership in the precomputed set-name table. -/
theorem insertSetNames_contains (is : List SetInfo) (s : Std.HashSet String)
    (x : String) :
    (insertSetNames is s).contains x =
      (s.contains x || is.any (fun i => i.name == x)) := by
  induction is generalizing s with
  | nil => simp [insertSetNames]
  | cons i is ih =>
      simp only [insertSetNames, List.foldl_cons] at ih ⊢
      rw [ih, Std.HashSet.contains_insert]
      simp [Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

/-- Membership in `setNameSet` is exactly being a removed set name. -/
theorem setNameSet_contains (se : SetExpansion) (x : String) :
    se.setNameSet.contains x = se.sets.any (fun i => i.name == x) := by
  simp [SetExpansion.setNameSet, insertSetNames_contains]

/-- The scanning set-name test is the `any` test. -/
theorem isSetName_any (se : SetExpansion) (x : Ident) :
    se.isSetName x = se.sets.any (fun i => i.name == x.name) := by
  unfold SetExpansion.isSetName SetExpansion.infoOf
  rw [Bool.eq_iff_iff, List.find?_isSome, List.any_eq_true]
  constructor
  · rintro ⟨i, hi, hp⟩
    exact ⟨i, hi, by simpa using hp⟩
  · rintro ⟨i, hi, hp⟩
    exact ⟨i, hi, by simpa using hp⟩

/-- The precomputed set-name test equals the scanning one. -/
theorem setNameSet_contains_isSetName (se : SetExpansion) (x : Ident) :
    se.setNameSet.contains x.name = se.isSetName x := by
  rw [setNameSet_contains, isSetName_any]

/-- The fast basic-expression test equals the scanning test. -/
theorem basicMentionsSetFast_eq (se : SetExpansion) (b : BasicExpr) :
    basicMentionsSetFast se.setNameSet b = basicMentionsSet se b := by
  cases b with
  | lit l => rfl
  | ident x => exact setNameSet_contains_isSetName se x

/-- The fast expression test equals the scanning test. -/
theorem exprMentionsSetFast_eq (se : SetExpansion) (e : Expr) :
    exprMentionsSetFast se.setNameSet e = exprMentionsSet se e := by
  cases e with
  | basic b => exact basicMentionsSetFast_eq se b
  | array es =>
      exact List.any_congr rfl (fun b => basicMentionsSetFast_eq se b)

/-- The fast constraint test equals the scanning test. -/
theorem constraintMentionsSetFast_eq (se : SetExpansion) (c : ConstraintItem) :
    constraintMentionsSetFast se.setNameSet c = constraintMentionsSet se c := by
  exact List.any_congr rfl (fun e => exprMentionsSetFast_eq se e)

/-- Pointwise congruence for `List.mapM`. -/
theorem mapM_congr_set {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.mapM f = l.mapM g := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a rest ih =>
      intro h
      rw [List.mapM_cons, List.mapM_cons, h a List.mem_cons_self,
        ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- **The fast rewrite equals the scanning specification.**  This is what
    lets the executable pass use the hash table while the correctness
    theorems keep talking about `rewriteConstraint`. -/
theorem rewriteConstraintFast_eq (se : SetExpansion) (c : ConstraintItem) :
    rewriteConstraintFast se.setNameSet se c = rewriteConstraint se c := by
  simp only [rewriteConstraintFast, rewriteConstraint,
    constraintMentionsSetFast_eq, setNameSet_contains_isSetName]

/-- Distinct members of a `flatMap` have disjoint fibres. -/
theorem nodup_flatMap_disjoint {α β : Type} {f : α → List β} :
    ∀ {l : List α}, (l.flatMap f).Nodup →
      ∀ a ∈ l, ∀ b ∈ l, a ≠ b → ∀ x, x ∈ f a → x ∈ f b → False
  | [], h, a, ha, b, hb, hne, x, hxa, hxb => by cases ha
  | a0 :: rest, h, a, ha, b, hb, hne, x, hxa, hxb => by
      rw [List.flatMap_cons, List.nodup_append] at h
      obtain ⟨_, hrest, hdisj⟩ := h
      rcases List.mem_cons.mp ha with rfl | ha'
      · have hb' : b ∈ rest := by
          rcases List.mem_cons.mp hb with rfl | hb'
          · exact absurd rfl hne
          · exact hb'
        exact hdisj x hxa x (List.mem_flatMap.mpr ⟨b, hb', hxb⟩) rfl
      · rcases List.mem_cons.mp hb with rfl | hb'
        · exact hdisj x hxb x (List.mem_flatMap.mpr ⟨a, ha', hxa⟩) rfl
        · exact nodup_flatMap_disjoint (l := rest) hrest a ha' b hb' hne x hxa hxb

/-- A fibre of a duplicate-free `flatMap` is duplicate-free. -/
theorem nodup_flatMap_fiber {α β : Type} {f : α → List β} :
    ∀ {l : List α}, (l.flatMap f).Nodup → ∀ a ∈ l, (f a).Nodup := by
  intro l
  induction l with
  | nil => intro _ a ha; cases ha
  | cons a0 rest ih =>
      intro h a ha
      rw [List.flatMap_cons, List.nodup_append] at h
      obtain ⟨hhead, hrest, _⟩ := h
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact hhead
      · exact ih hrest a ha'

/-- A fresh Boolean name is found in its own set's table entry. -/
theorem SetExpansion.boolInfoOf_eq_some_of_mem {se : SetExpansion} {i : SetInfo}
    {p : String × Int} (hnd : se.boolNames.Nodup) (hi : i ∈ se.sets)
    (hp : p ∈ i.bools) :
    se.boolInfoOf (Ident.mk p.1) = some i := by
  unfold SetExpansion.boolInfoOf
  by_cases hf : se.sets.find? (fun j => j.bools.any fun q => q.1 = p.1) = none
  · rw [hf]
    rw [List.find?_eq_none] at hf
    have hany : (i.bools.any fun q => decide (q.1 = p.1)) = true := by
      rw [List.any_eq_true]
      exact ⟨p, hp, by simp⟩
    have hfalse := hf i hi
    rw [hany] at hfalse
    exact absurd rfl hfalse
  · cases hsome : se.sets.find? (fun j => j.bools.any fun q => q.1 = p.1) with
    | none => exact absurd hsome hf
    | some j =>
        have hj : j ∈ se.sets := List.mem_of_find?_eq_some hsome
        have hanyj := List.find?_some hsome
        obtain ⟨q, hq, hqname⟩ : ∃ q : String × Int,
            q ∈ j.bools ∧ decide (q.1 = p.1) = true := by
          simpa using (List.any_eq_true.mp hanyj)
        have hji : j = i := by
          by_cases h_eq : j = i
          · exact h_eq
          · exfalso
            exact nodup_flatMap_disjoint
              (f := fun k : SetInfo => k.bools.map Prod.fst) (l := se.sets) (by
                simpa [SetExpansion.boolNames] using hnd)
              i hi j hj (fun h => h_eq h.symm) p.1
              (List.mem_map.mpr ⟨p, hp, rfl⟩)
              (List.mem_map.mpr ⟨q, hq, by simpa using hqname⟩)
        subst hji
        rfl

/-- A name outside the fresh-Boolean table has no Boolean info. -/
theorem SetExpansion.boolInfoOf_eq_none_of_not_mem {se : SetExpansion} {x : Ident}
    (hx : x.name ∉ se.boolNames) : se.boolInfoOf x = none := by
  unfold SetExpansion.boolInfoOf
  rw [List.find?_eq_none]
  intro i hi hany
  obtain ⟨p, hp, hname⟩ := List.any_eq_true.mp hany
  apply hx
  rw [SetExpansion.boolNames, List.mem_flatMap]
  refine ⟨i, hi, ?_⟩
  rw [List.mem_map]
  exact ⟨p, hp, by simpa using hname⟩

/-- The completeness store reads a fresh Boolean from its source set. -/
theorem SetExpansion.encodeStore_bool {se : SetExpansion} {s : Store}
    {i : SetInfo} {p : String × Int} (hnames : se.boolNames.Nodup)
    (hfib : (i.bools.map Prod.fst).Nodup) (hi : i ∈ se.sets) (hp : p ∈ i.bools) :
    encodeStore se s (Ident.mk p.1) =
      some (.bool (i.sourceContainsB s p.2)) := by
  unfold encodeStore
  rw [SetExpansion.boolInfoOf_eq_some_of_mem hnames hi hp]
  dsimp only
  rw [SetInfo.boolValueOf_eq_some_of_mem hfib hp rfl]

/-- The completeness store leaves non-Boolean names unchanged. -/
theorem SetExpansion.encodeStore_of_not_bool {se : SetExpansion} {s : Store}
    {x : Ident} (hx : x.name ∉ se.boolNames) : encodeStore se s x = s x := by
  unfold encodeStore
  rw [SetExpansion.boolInfoOf_eq_none_of_not_mem hx]

/-! ## Declaration expansion -/

/-- The total number of fresh Boolean slots in an expansion table. -/
def totalValues (infos : List SetInfo) : Nat :=
  (infos.map (fun i => i.values.length)).sum

/-- Mapping a shifted range of auxiliary names splits at an offset. -/
theorem map_range_add_aux (taken : List String) (n a b : Nat) :
    (List.range (a + b)).map (fun j => auxName taken (n + j)) =
      (List.range a).map (fun j => auxName taken (n + j)) ++
        (List.range b).map (fun j => auxName taken ((n + a) + j)) := by
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply]
  congr 1
  omega

/-- Concatenating two fresh runs is one fresh run over the appended
    universe. -/
theorem freshPairs_names_append (taken : List String) (n : Nat)
    (us vs : List Int) :
    (freshPairs taken n us).map Prod.fst ++
        (freshPairs taken (n + us.length) vs).map Prod.fst =
      (freshPairs taken n (us ++ vs)).map Prod.fst := by
  rw [freshPairs_names, freshPairs_names, freshPairs_names,
    List.length_append, map_range_add_aux]

/-! ## The declaration-expansion specification -/

/-- The declared base type of a variable declaration. -/
def declBase : VarDeclItem → BaseType
  | .basic ty _ _ _ => ty.base
  | .array ty _ _ _ => ty.elem.base

/-- A declaration whose declared type is not set-typed. -/
def nonSetDecl (d : VarDeclItem) : Prop := declBase d ≠ .setOfInt

/-- Everything the expansion pass records about one run of
    `expandVarDecls`: the fresh-name ranges, the table invariants, and
    the source/expanded declaration correspondence. -/
structure DeclExpansion (taken : List String) (ds : List VarDeclItem)
    (n : Nat) (infos : List SetInfo) (n' : Nat) (vars : List VarDeclItem) : Prop where
  /-- The counter advances by exactly the number of fresh slots. -/
  counter : n' = n + totalValues infos
  /-- The fresh names are the consecutive auxiliary names from `n`. -/
  bool_eq : infos.flatMap (fun i => i.bools.map Prod.fst) =
    (List.range (totalValues infos)).map (fun j => auxName taken (n + j))
  /-- Set-variable names are unique. -/
  infos_nodup : (infos.map (fun i => i.name)).Nodup
  /-- Each set's universe values are unique. -/
  values_nodup : ∀ i ∈ infos, i.values.Nodup
  /-- A set's Boolean names are unique. -/
  bools_nodup : ∀ i ∈ infos, (i.bools.map Prod.fst).Nodup
  /-- The values of a set's Booleans are its universe. -/
  values_eq : ∀ i ∈ infos, i.bools.map Prod.snd = i.values
  /-- Fresh names avoid the taken names. -/
  fresh : ∀ i ∈ infos, ∀ b ∈ i.bools.map Prod.fst, b ∉ taken
  /-- Every set info comes from a matching initializer-free source
      declaration with the recorded universe. -/
  info_source : ∀ i ∈ infos, ∃ (ty : BasicVarType) (x : Ident)
      (anns : List Annotation),
        (.basic ty x anns none : VarDeclItem) ∈ ds ∧
          i.name = x.name ∧ i.ty = ty ∧ setUniverse? ty = some i.values
  /-- The expanded declarations have unique names. -/
  vars_nodup : (vars.map (fun d => d.name.name)).Nodup
  /-- Removed set-variable names are not kept in the expanded declarations. -/
  names_not_vars : ∀ i ∈ infos, i.name ∉ vars.map (fun d => d.name.name)
  /-- Kept declarations are never set-typed: every declared set variable
      shape is either expanded or rejected. -/
  vars_not_set : ∀ d ∈ vars, nonSetDecl d
  /-- Every fresh Boolean declaration is present in the expanded list. -/
  fresh_vars : ∀ i ∈ infos, ∀ p ∈ i.bools,
    (.basic (.par .bool) (Ident.mk p.1) [] none : VarDeclItem) ∈ vars
  /-- Every source declaration is either kept or recorded as a set. -/
  source : ∀ d ∈ ds, d ∈ vars ∨ ∃ i ∈ infos, ∃ (ty : BasicVarType)
      (anns : List Annotation),
        d = .basic ty (Ident.mk i.name) anns none ∧ i.ty = ty ∧
          setUniverse? ty = some i.values
  /-- Every expanded declaration is either a source declaration or a
      fresh Boolean. -/
  expanded : ∀ d ∈ vars, d ∈ ds ∨ ∃ i ∈ infos, ∃ p ∈ i.bools,
      d = .basic (.par .bool) (Ident.mk p.1) [] none

/-- Keeping a non-set declaration in front of an expansion. -/
theorem DeclExpansion.keep {taken : List String} {ds : List VarDeclItem}
    {n : Nat} {infos : List SetInfo} {n' : Nat} {rest : List VarDeclItem}
    (d : VarDeclItem) (ihs : DeclExpansion taken ds n infos n' rest)
    (hnd : d.name.name ∉ ds.map (fun e => e.name.name))
    (htk : d.name.name ∈ taken)
    (hset : ∀ i ∈ infos, i.name ≠ d.name.name)
    (hns : nonSetDecl d) :
    DeclExpansion taken (d :: ds) n infos n' (d :: rest) := by
  refine
    { counter := ihs.counter
      bool_eq := ihs.bool_eq
      infos_nodup := ihs.infos_nodup
      values_nodup := ihs.values_nodup
      bools_nodup := ihs.bools_nodup
      values_eq := ihs.values_eq
      fresh := ihs.fresh
      info_source := ?_
      vars_nodup := ?_
      names_not_vars := ?_
      vars_not_set := ?_
      fresh_vars := ?_
      source := ?_
      expanded := ?_ }
  · intro i hi
    obtain ⟨ty, x, anns, hd, hname, hty, huniv⟩ := ihs.info_source i hi
    exact ⟨ty, x, anns, List.mem_cons_of_mem _ hd, hname, hty, huniv⟩
  · rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ihs.vars_nodup⟩
    intro hmem
    obtain ⟨e, he, hen⟩ := List.mem_map.mp hmem
    rcases ihs.expanded e he with hsrc | ⟨i, hi, p, hp, hde⟩
    · apply hnd
      exact List.mem_map.mpr ⟨e, hsrc, hen⟩
    · have hfresh := ihs.fresh i hi p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)
      have hpe : e.name.name = p.1 := by rw [hde]; rfl
      apply hfresh
      rw [← hpe, hen]
      exact htk
  · intro i hi
    rw [List.map_cons]
    intro hmem
    rcases List.mem_cons.mp hmem with heq | hmem'
    · exact hset i hi heq
    · exact ihs.names_not_vars i hi hmem'
  · intro e he
    rcases List.mem_cons.mp he with rfl | he'
    · exact hns
    · exact ihs.vars_not_set e he'
  · intro i hi p hp
    exact List.mem_cons_of_mem _ (ihs.fresh_vars i hi p hp)
  · intro e he
    rcases List.mem_cons.mp he with rfl | he'
    · exact Or.inl (List.mem_cons_self ..)
    · rcases ihs.source e he' with hmem | hset
      · exact Or.inl (List.mem_cons_of_mem _ hmem)
      · exact Or.inr hset
  · intro e he
    rcases List.mem_cons.mp he with rfl | he'
    · exact Or.inl (List.mem_cons_self ..)
    · rcases ihs.expanded e he' with hmem | hfresh
      · exact Or.inl (List.mem_cons_of_mem _ hmem)
      · exact Or.inr hfresh

/-- The width-bounded declaration expansion equals the scanning one at
    the bound `maxStrLength taken`; the executable pass uses the former so
    the bound is computed once instead of once per fresh slot. -/
theorem expandVarDeclsAt_eq (taken : List String) :
    ∀ (ds : List VarDeclItem) (n : Nat),
      expandVarDeclsAt (maxStrLength taken) n ds = expandVarDecls taken n ds := by
  intro ds
  induction ds with
  | nil => intro n; rfl
  | cons d ds ih =>
      intro n
      cases d with
      | basic ty x anns init =>
          cases init with
          | some e =>
              by_cases hbase : ty.base = .setOfInt
              · simp [expandVarDeclsAt, expandVarDecls, hbase]
              · simp [expandVarDeclsAt, expandVarDecls, hbase, ih]
          | none =>
              cases hu : setUniverse? ty with
              | some us =>
                  simp only [expandVarDeclsAt, expandVarDecls, hu,
                    freshPairsAt_eq, ih]
              | none =>
                  by_cases hbase : ty.base = .setOfInt
                  · simp [expandVarDeclsAt, expandVarDecls, hu, hbase]
                  · simp [expandVarDeclsAt, expandVarDecls, hu, hbase, ih]
      | array ty x anns es =>
          by_cases hbase : ty.elem.base = .setOfInt
          · simp [expandVarDeclsAt, expandVarDecls, hbase]
          · simp [expandVarDeclsAt, expandVarDecls, hbase, ih]

/-- **Declaration-expansion specification**: a successful `expandVarDecls`
    run has unique source/expanded names, records each removed set
    declaration in the table, and allocates exactly the consecutive
    fresh Boolean names. -/
theorem expandVarDecls_spec (taken : List String) :
    ∀ (ds : List VarDeclItem) (n : Nat) (infos : List SetInfo) (n' : Nat)
      (vars : List VarDeclItem),
      (ds.map (fun d => d.name.name)).Nodup →
      (∀ d ∈ ds, d.name.name ∈ taken) →
      expandVarDecls taken n ds = some (infos, n', vars) →
      DeclExpansion taken ds n infos n' vars := by
  intro ds
  induction ds with
  | nil =>
      intro n infos n' vars _ _ h
      simp only [expandVarDecls, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine
        { counter := by simp [totalValues]
          bool_eq := by simp [totalValues]
          infos_nodup := by simp
          values_nodup := by simp
          bools_nodup := by simp
          values_eq := by simp
          fresh := by simp
          info_source := by simp
          vars_nodup := by simp
          names_not_vars := by simp
          vars_not_set := by simp
          fresh_vars := by simp
          source := by simp
          expanded := by simp }
  | cons d ds ih =>
      intro n infos n' vars hnd htk h
      rw [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨hnd_head, hnd_tail⟩ := hnd
      have htk_head : d.name.name ∈ taken := htk d (List.mem_cons_self ..)
      have htk_tail : ∀ e ∈ ds, e.name.name ∈ taken :=
        fun e he => htk e (List.mem_cons_of_mem _ he)
      cases d with
      | basic ty x anns init =>
          cases init with
          | none =>
              simp only [expandVarDecls] at h
              cases hu : setUniverse? ty with
              | none =>
                  rw [hu] at h
                  by_cases hbase : ty.base = .setOfInt
                  · rw [if_pos hbase] at h
                    cases h
                  · rw [if_neg hbase] at h
                    cases hrec : expandVarDecls taken n ds with
                    | none => rw [hrec] at h; cases h
                    | some res =>
                        obtain ⟨infos', n'', rest⟩ := res
                        rw [hrec] at h
                        simp only [Option.some.injEq, Prod.mk.injEq] at h
                        obtain ⟨rfl, rfl, rfl⟩ := h
                        have ihs := ih n infos' n'' rest hnd_tail htk_tail hrec
                        exact DeclExpansion.keep (.basic ty x anns none) ihs
                          (by simpa using hnd_head) (by simpa using htk_head)
                          (by
                            intro i hi hname
                            obtain ⟨ty', x', anns', he', hname', _, _⟩ := ihs.info_source i hi
                            apply hnd_head
                            refine List.mem_map.mpr ⟨.basic ty' x' anns' none, he', ?_⟩
                            exact hname'.symm.trans hname)
                          (by simpa [nonSetDecl, declBase] using hbase)
              | some us =>
                  rw [hu] at h
                  dsimp only at h
                  cases hrec : expandVarDecls taken (n + us.length) ds with
                  | none => rw [hrec] at h; cases h
                  | some res =>
                      obtain ⟨infos', n'', rest⟩ := res
                      rw [hrec] at h
                      simp only [Option.some.injEq, Prod.mk.injEq] at h
                      obtain ⟨rfl, rfl, rfl⟩ := h
                      let info : SetInfo :=
                        { name := x.name, ty := ty, bools := freshPairs taken n us }
                      let bds : List VarDeclItem :=
                        (freshPairs taken n us).map fun p =>
                          .basic (.par .bool) (Ident.mk p.1) [] none
                      change DeclExpansion taken (.basic ty x anns none :: ds) n
                        (info :: infos') n'' (bds ++ rest)
                      have ihs := ih (n + us.length) infos' n'' rest hnd_tail htk_tail hrec
                      have hvals : info.values = us := by
                        simp [info, SetInfo.values, freshPairs_values]
                      have hbds : bds.map (fun d => d.name.name) =
                            (freshPairs taken n us).map Prod.fst := by
                        rw [show bds = (freshPairs taken n us).map
                            (fun p => .basic (.par .bool) (Ident.mk p.1) [] none)
                            from rfl, List.map_map]
                        rfl
                      refine
                        { counter := ?_
                          bool_eq := ?_
                          infos_nodup := ?_
                          values_nodup := ?_
                          bools_nodup := ?_
                          values_eq := ?_
                          fresh := ?_
                          info_source := ?_
                          vars_nodup := ?_
                          names_not_vars := ?_
                          vars_not_set := ?_
                          fresh_vars := ?_
                          source := ?_
                          expanded := ?_ }
                      · have hc := ihs.counter
                        simp only [totalValues, List.map_cons, List.sum_cons] at hc ⊢
                        rw [hvals] at ⊢
                        omega
                      · have hhead : info.bools.map Prod.fst =
                            (List.range us.length).map
                              (fun j => auxName taken (n + j)) := by
                          rw [show info.bools = freshPairs taken n us from rfl,
                            freshPairs_names]
                        calc
                          (info :: infos').flatMap (fun i => i.bools.map Prod.fst)
                              = info.bools.map Prod.fst ++
                                  infos'.flatMap (fun i => i.bools.map Prod.fst) := rfl
                          _ = (List.range us.length).map
                                  (fun j => auxName taken (n + j)) ++
                                (List.range (totalValues infos')).map
                                  (fun j => auxName taken ((n + us.length) + j)) := by
                                rw [hhead, ihs.bool_eq]
                          _ = (List.range (us.length + totalValues infos')).map
                                  (fun j => auxName taken (n + j)) := by
                                rw [← map_range_add_aux]
                          _ = (List.range (totalValues (info :: infos'))).map
                                  (fun j => auxName taken (n + j)) := by
                                rw [show us.length + totalValues infos' =
                                  totalValues (info :: infos') by
                                    simp [totalValues, hvals]]
                      · rw [List.map_cons, List.nodup_cons]
                        refine ⟨?_, ihs.infos_nodup⟩
                        intro hmem
                        obtain ⟨j, hj, hjn⟩ := List.mem_map.mp hmem
                        obtain ⟨tyj, xj, annsj, hdj, hnamej, _, _⟩ :=
                          ihs.info_source j hj
                        apply hnd_head
                        refine List.mem_map.mpr ⟨.basic tyj xj annsj none, hdj, ?_⟩
                        show xj.name = x.name
                        rw [← hnamej]
                        exact hjn.trans (by simp [info])
                      · intro i hi
                        rcases List.mem_cons.mp hi with rfl | hi'
                        · rw [hvals]
                          exact setUniverse?_nodup hu
                        · exact ihs.values_nodup i hi'
                      · intro i hi
                        rcases List.mem_cons.mp hi with rfl | hi'
                        · rw [show info.bools = freshPairs taken n us from rfl]
                          exact freshPairs_names_nodup taken n us
                        · exact ihs.bools_nodup i hi'
                      · intro i hi
                        rcases List.mem_cons.mp hi with rfl | hi'
                        · rfl
                        · exact ihs.values_eq i hi'
                      · intro i hi b hb
                        rcases List.mem_cons.mp hi with rfl | hi'
                        · rw [show info.bools = freshPairs taken n us from rfl] at hb
                          exact freshPairs_name_not_mem taken n us hb
                        · exact ihs.fresh i hi' b hb
                      · intro i hi
                        rcases List.mem_cons.mp hi with rfl | hi'
                        · refine ⟨ty, x, anns, List.mem_cons_self .., rfl, rfl, ?_⟩
                          rw [hvals]
                          exact hu
                        · obtain ⟨ty', x', anns', hd', hname', hty', huniv'⟩ :=
                            ihs.info_source i hi'
                          exact ⟨ty', x', anns', List.mem_cons_of_mem _ hd',
                            hname', hty', huniv'⟩
                      · rw [List.map_append]
                        refine List.nodup_append.mpr
                          ⟨?_, ihs.vars_nodup, ?_⟩
                        · rw [hbds]
                          exact freshPairs_names_nodup taken n us
                        · intro a ha b hb hab
                          have ha' : a ∈ (freshPairs taken n us).map Prod.fst :=
                            hbds ▸ ha
                          rw [freshPairs_names] at ha'
                          obtain ⟨j, hj, hja⟩ := List.mem_map.mp ha'
                          have hjlt : j < us.length := List.mem_range.mp hj
                          obtain ⟨e, he, heb⟩ := List.mem_map.mp hb
                          rcases ihs.expanded e he with hsrc | ⟨i, hi, p, hp, hde⟩
                          · have hb_taken : b ∈ taken := by
                              rw [← heb]
                              exact htk_tail e hsrc
                            have ha_not : a ∉ taken := by
                              rw [← hja]
                              exact auxName_not_mem
                            exact ha_not (by rw [hab]; exact hb_taken)
                          · have hbmem : p.1 ∈
                                infos'.flatMap (fun i => i.bools.map Prod.fst) :=
                              List.mem_flatMap.mpr
                                ⟨i, hi, List.mem_map.mpr ⟨p, hp, rfl⟩⟩
                            rw [ihs.bool_eq] at hbmem
                            obtain ⟨k, hk, hkeq⟩ := List.mem_map.mp hbmem
                            have hb_eq : b = auxName taken ((n + us.length) + k) := by
                              rw [← heb, hde]
                              exact hkeq.symm
                            have ha_eq : a = auxName taken (n + j) := hja.symm
                            have heqaux : auxName taken (n + j) =
                                auxName taken ((n + us.length) + k) := by
                              rw [← ha_eq, hab, hb_eq]
                            have hidx := auxName_inj heqaux
                            omega
                      · -- removed set names are not kept
                        intro i hi
                        rw [List.map_append]
                        intro hmem
                        rcases List.mem_append.mp hmem with hb | hr
                        · rw [hbds] at hb
                          obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hb
                          have hpnot : p.1 ∉ taken :=
                            freshPairs_name_not_mem taken n us
                              (List.mem_map.mpr ⟨p, hp, rfl⟩)
                          rcases List.mem_cons.mp hi with rfl | hi'
                          · exact hpnot (by rw [hpn]; simpa [info, VarDeclItem.name] using htk_head)
                          · obtain ⟨ty', x', anns', he', hname', _, _⟩ :=
                              ihs.info_source i hi'
                            have hit : i.name ∈ taken := by
                              have := htk_tail (.basic ty' x' anns' none) he'
                              simpa [VarDeclItem.name, hname'] using this
                            exact hpnot (by rw [hpn]; exact hit)
                        · rcases List.mem_cons.mp hi with rfl | hi'
                          · obtain ⟨e, he, hen⟩ := List.mem_map.mp hr
                            rcases ihs.expanded e he with hsrc | ⟨j, hj, p, hp, hde⟩
                            · apply hnd_head
                              refine List.mem_map.mpr ⟨e, hsrc, ?_⟩
                              simpa [info, VarDeclItem.name] using hen
                            · have hpe : e.name.name = p.1 := by rw [hde]; rfl
                              exact (ihs.fresh j hj p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩))
                                (by rw [← hpe, hen]; simpa [info, VarDeclItem.name] using htk_head)
                          · exact ihs.names_not_vars i hi' hr
                      · intro e he
                        rcases List.mem_append.mp he with hbds | hrest
                        · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hbds
                          simp [nonSetDecl, declBase, BasicVarType.base, BasicParType.base]
                        · exact ihs.vars_not_set e hrest
                      · intro i hi p hp
                        rcases List.mem_cons.mp hi with rfl | hi'
                        · exact List.mem_append_left _
                            (List.mem_map.mpr ⟨p, hp, rfl⟩)
                        · exact List.mem_append_right _
                            (ihs.fresh_vars i hi' p hp)
                      · intro e he
                        rcases List.mem_cons.mp he with rfl | he'
                        · exact Or.inr ⟨info, List.mem_cons_self .., ty, anns, rfl, rfl,
                            by rw [hvals]; exact hu⟩
                        · rcases ihs.source e he' with hmem | hset
                          · exact Or.inl (List.mem_append_right bds hmem)
                          · obtain ⟨i, hi, ty', anns', heq, hty', huniv'⟩ := hset
                            exact Or.inr ⟨i, List.mem_cons_of_mem _ hi, ty', anns', heq,
                              hty', huniv'⟩
                      · intro e he
                        rcases List.mem_append.mp he with hbds | hrest
                        · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hbds
                          exact Or.inr ⟨info, List.mem_cons_self .., p, hp, rfl⟩
                        · rcases ihs.expanded e hrest with hmem | hfresh
                          · exact Or.inl (List.mem_cons_of_mem _ hmem)
                          · obtain ⟨i, hi, p, hp, heq⟩ := hfresh
                            exact Or.inr ⟨i, List.mem_cons_of_mem _ hi, p, hp, heq⟩
          | some e =>
              simp only [expandVarDecls] at h
              by_cases hbase : ty.base = .setOfInt
              · rw [if_pos hbase] at h
                cases h
              · rw [if_neg hbase] at h
                cases hrec : expandVarDecls taken n ds with
                | none => rw [hrec] at h; cases h
                | some res =>
                    obtain ⟨infos', n'', rest⟩ := res
                    rw [hrec] at h
                    simp only [Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl, rfl⟩ := h
                    have ihs := ih n infos' n'' rest hnd_tail htk_tail hrec
                    exact DeclExpansion.keep (.basic ty x anns (some e)) ihs
                      (by simpa using hnd_head) (by simpa using htk_head)
                      (by
                        intro i hi hname
                        obtain ⟨ty', x', anns', he', hname', _, _⟩ := ihs.info_source i hi
                        apply hnd_head
                        refine List.mem_map.mpr ⟨.basic ty' x' anns' none, he', ?_⟩
                        exact hname'.symm.trans hname)
                      (by simpa [nonSetDecl, declBase] using hbase)
      | array ty x anns es =>
          simp only [expandVarDecls] at h
          by_cases hbase : ty.elem.base = .setOfInt
          · rw [if_pos hbase] at h
            cases h
          · rw [if_neg hbase] at h
            cases hrec : expandVarDecls taken n ds with
            | none => rw [hrec] at h; cases h
            | some res =>
                obtain ⟨infos', n'', rest⟩ := res
                rw [hrec] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                have ihs := ih n infos' n'' rest hnd_tail htk_tail hrec
                exact DeclExpansion.keep (.array ty x anns es) ihs
                  (by simpa using hnd_head) (by simpa using htk_head)
                  (by
                    intro i hi hname
                    obtain ⟨ty', x', anns', he', hname', _, _⟩ := ihs.info_source i hi
                    apply hnd_head
                    refine List.mem_map.mpr ⟨.basic ty' x' anns' none, he', ?_⟩
                    exact hname'.symm.trans hname)
                  (by simpa [nonSetDecl, declBase] using hbase)

/-- **Inversion of the set-expansion pass.** -/
theorem setExpandModel_spec {taken : List String} {m : Model} {se : SetExpansion}
    (hnd : (m.variables.map (fun d => d.name.name)).Nodup)
    (htk : ∀ d ∈ m.variables, d.name.name ∈ taken)
    (h : setExpandModelWith taken m = some se) :
    (∃ n', DeclExpansion taken m.variables 0 se.sets n'
        se.model.variables) ∧
      se.model.parameters = m.parameters ∧
      se.model.predicates = m.predicates ∧
      se.model.solve = m.solve ∧
      (∃ css, m.constraints.mapM (rewriteConstraint se) = some css ∧
        se.model.constraints = css.flatten) := by
  unfold setExpandModelWith at h
  split at h
  · cases h
  · rename_i infos n' vars hdecl
    dsimp only at h
    split at h
    · cases h
    · rename_i css hmap
      let model' : Model := { m with variables := vars, constraints := css.flatten }
      let se' : SetExpansion := { model := model', sets := infos }
      have hse : se = se' := (Option.some.inj h).symm
      subst hse
      dsimp only [se', model']
      have hdeclS : expandVarDecls taken 0 m.variables = some (infos, n', vars) := by
        rw [← expandVarDeclsAt_eq taken]
        exact hdecl
      have hdecl' := expandVarDecls_spec taken m.variables 0 infos n' vars
        hnd htk hdeclS
      refine ⟨⟨n', hdecl'⟩, rfl, rfl, rfl, css, ?_, rfl⟩
      let se0 : SetExpansion :=
        { model := { m with variables := vars }, sets := infos }
      change m.constraints.mapM (rewriteConstraintFast se0.setNameSet se0) = some css at hmap
      show m.constraints.mapM (rewriteConstraint se0) = some css
      rw [mapM_congr_set (f := rewriteConstraint se0)
        (g := rewriteConstraintFast se0.setNameSet se0)
        (fun c _ => (rewriteConstraintFast_eq se0 c).symm)]
      exact hmap

/-- The set expansion leaves parameters, predicates and the solve item
    untouched. -/
theorem setExpandModelWith_fields {taken : List String} {m : Model}
    {se : SetExpansion} (h : setExpandModelWith taken m = some se) :
    se.model.parameters = m.parameters ∧
      se.model.predicates = m.predicates ∧
      se.model.solve = m.solve := by
  unfold setExpandModelWith at h
  split at h
  · cases h
  · rename_i infos n' vars hdecl
    dsimp only at h
    split at h
    · cases h
    · rename_i css hmap
      have hse : se = { model := { m with
            variables := vars, constraints := css.flatten }, sets := infos } :=
        (Option.some.inj h).symm
      subst hse
      exact ⟨rfl, rfl, rfl⟩

/-- The set expansion leaves parameters, predicates and the solve item
    untouched (unnamed variant). -/
theorem setExpandModel_fields {m : Model} {se : SetExpansion}
    (h : setExpandModel m = some se) :
    se.model.parameters = m.parameters ∧
      se.model.predicates = m.predicates ∧
      se.model.solve = m.solve :=
  setExpandModelWith_fields h

/-- The fresh names of a declaration expansion are unique. -/
theorem DeclExpansion.boolNames_nodup {taken : List String} {ds : List VarDeclItem}
    {n n' : Nat} {infos : List SetInfo} {vars : List VarDeclItem}
    (d : DeclExpansion taken ds n infos n' vars) :
    (infos.flatMap (fun i => i.bools.map Prod.fst)).Nodup := by
  rw [d.bool_eq]
  refine List.Pairwise.map _ ?_ List.nodup_range
  intro j k hjk heq
  apply hjk
  have := auxName_inj heq
  omega

/-- The invariants of a successful set-expansion pass. -/
structure SetExpansion.Inv (taken : List String) (m : Model)
    (se : SetExpansion) : Prop where
  parameters : se.model.parameters = m.parameters
  predicates : se.model.predicates = m.predicates
  solve : se.model.solve = m.solve
  /-- The expansion's taken list contains every name of the expanded model. -/
  superset : ∀ x ∈ setTaken m, x ∈ taken
  decls : ∃ n', DeclExpansion taken m.variables 0 se.sets n'
    se.model.variables
  constraints : ∃ css, m.constraints.mapM (rewriteConstraint se) = some css ∧
    se.model.constraints = css.flatten

theorem setExpandModel_inv {taken : List String} {m : Model} {se : SetExpansion}
    (hnd : (m.variables.map (fun d => d.name.name)).Nodup)
    (htk : ∀ d ∈ m.variables, d.name.name ∈ taken)
    (hsup : ∀ x ∈ setTaken m, x ∈ taken)
    (h : setExpandModelWith taken m = some se) : se.Inv taken m := by
  obtain ⟨hd, hp, hpr, hs, hc⟩ := setExpandModel_spec hnd htk h
  exact ⟨hp, hpr, hs, hsup, hd, hc⟩

theorem SetExpansion.Inv.setNames_nodup {m : Model} {se : SetExpansion}
    {taken : List String} (inv : se.Inv taken m) : se.setNames.Nodup := by
  obtain ⟨n', d⟩ := inv.decls
  simpa [SetExpansion.setNames] using d.infos_nodup

theorem SetExpansion.Inv.boolNames_nodup {m : Model} {se : SetExpansion}
    {taken : List String} (inv : se.Inv taken m) : se.boolNames.Nodup := by
  obtain ⟨n', d⟩ := inv.decls
  simpa [SetExpansion.boolNames] using d.boolNames_nodup

theorem SetExpansion.Inv.values_nodup {m : Model} {se : SetExpansion}
    {taken : List String} (inv : se.Inv taken m) : ∀ i ∈ se.sets, i.values.Nodup := by
  obtain ⟨n', d⟩ := inv.decls
  exact d.values_nodup

theorem SetExpansion.Inv.bools_nodup {m : Model} {se : SetExpansion}
    {taken : List String} (inv : se.Inv taken m) : ∀ i ∈ se.sets, (i.bools.map Prod.fst).Nodup := by
  obtain ⟨n', d⟩ := inv.decls
  exact d.bools_nodup

theorem SetExpansion.Inv.values_eq {m : Model} {se : SetExpansion}
    {taken : List String} (inv : se.Inv taken m) : ∀ i ∈ se.sets, i.bools.map Prod.snd = i.values := by
  obtain ⟨n', d⟩ := inv.decls
  exact d.values_eq

theorem SetExpansion.Inv.fresh {m : Model} {se : SetExpansion}
    {taken : List String} (inv : se.Inv taken m) :
    ∀ i ∈ se.sets, ∀ b ∈ i.bools.map Prod.fst, b ∉ taken := by
  obtain ⟨n', d⟩ := inv.decls
  exact d.fresh

theorem SetExpansion.Inv.vars_nodup {m : Model} {se : SetExpansion}
    {taken : List String} (inv : se.Inv taken m) : (se.model.variables.map (fun d => d.name.name)).Nodup := by
  obtain ⟨n', d⟩ := inv.decls
  exact d.vars_nodup

theorem SetExpansion.Inv.source {m : Model} {se : SetExpansion}
    {taken : List String} (inv : se.Inv taken m) :
    ∀ d ∈ m.variables, d ∈ se.model.variables ∨
      ∃ i ∈ se.sets, ∃ (ty : BasicVarType) (anns : List Annotation),
        d = .basic ty (Ident.mk i.name) anns none ∧ i.ty = ty ∧
          setUniverse? ty = some i.values := by
  obtain ⟨n', d⟩ := inv.decls
  exact d.source

theorem SetExpansion.Inv.expanded {m : Model} {se : SetExpansion}
    {taken : List String} (inv : se.Inv taken m) :
    ∀ d ∈ se.model.variables, d ∈ m.variables ∨
      ∃ i ∈ se.sets, ∃ p ∈ i.bools,
        d = .basic (.par .bool) (Ident.mk p.1) [] none := by
  obtain ⟨n', d⟩ := inv.decls
  exact d.expanded

/-- A member of a flattened `mapM` result comes from one input's output. -/
theorem mem_flatten_of_mapM_some {α β : Type} {f : α → Option (List β)}
    {xs : List α} {ys : List (List β)} (h : xs.mapM f = some ys) :
    ∀ b ∈ ys.flatten, ∃ a ∈ xs, ∃ l, f a = some l ∧ b ∈ l := by
  induction xs generalizing ys with
  | nil =>
      have h' : some ([] : List (List β)) = some ys := h
      simp only [Option.some.injEq] at h'
      subst h'
      intro b hb
      simp at hb
  | cons a rest ih =>
      simp only [List.mapM_cons] at h
      cases ha : f a with
      | none => rw [ha] at h; cases h
      | some l =>
          rw [ha] at h
          cases hrest : rest.mapM f with
          | none => rw [hrest] at h; cases h
          | some ls =>
              rw [hrest] at h
              simp at h
              subst h
              intro b hb
              rw [List.flatten_cons, List.mem_append] at hb
              rcases hb with hb | hb
              · exact ⟨a, List.mem_cons_self .., l, ha, hb⟩
              · obtain ⟨a', ha', l', hf', hb'⟩ := ih hrest b hb
                exact ⟨a', List.mem_cons_of_mem _ ha', l', hf', hb'⟩


/-! ## Store reconstruction and set-free evaluation -/



/-- The reconstructed store reads a removed set variable as the set of
    universe values whose fresh Boolean is true. -/
theorem SetExpansion.setStore_setName {se : SetExpansion} {i : SetInfo}
    (hnd : se.setNames.Nodup) (hi : i ∈ se.sets) (s : Store) :
    setStore se s (Ident.mk i.name) = some (.setOfInt (i.rebuilt s)) := by
  unfold setStore
  rw [SetExpansion.infoOf_eq_some_of_mem hnd hi]

/-- The reconstructed store leaves every name that is not a removed set
    variable unchanged. -/
theorem SetExpansion.setStore_of_none {se : SetExpansion} {s : Store}
    {x : Ident} (h : se.infoOf x = none) : setStore se s x = s x := by
  simp [setStore, h]

/-- A basic expression that does not mention a removed set name evaluates
    the same in the reconstructed and in the expanded store. -/
theorem basicMentionsSet_eval {se : SetExpansion} {s : Store} {b : BasicExpr}
    (h : basicMentionsSet se b = false) :
    b.eval (setStore se s) = b.eval s := by
  cases b with
  | lit l => rfl
  | ident x =>
      have hx : se.infoOf x = none := by
        have h' : (se.isSetName x) = false := by simpa [basicMentionsSet] using h
        simpa [SetExpansion.isSetName] using h'
      simp [BasicExpr.eval, SetExpansion.setStore_of_none hx]

/-- An expression that does not mention a removed set name evaluates the
    same in the reconstructed and in the expanded store. -/
theorem exprMentionsSet_eval {se : SetExpansion} {s : Store} {e : Expr}
    (h : exprMentionsSet se e = false) :
    e.eval (setStore se s) = e.eval s := by
  cases e with
  | basic b => exact basicMentionsSet_eval h
  | array es =>
      show (es.mapM (BasicExpr.eval (setStore se s))).map Value.array =
        (es.mapM (BasicExpr.eval s)).map Value.array
      have hall : ∀ b ∈ es, BasicExpr.eval (setStore se s) b = BasicExpr.eval s b := by
        intro b hb
        exact basicMentionsSet_eval (by
          have := (List.any_eq_false.mp (by simpa [exprMentionsSet] using h)) b hb
          simpa using this)
      rw [mapM_congr_set hall]

/-- A constraint whose arguments do not mention a removed set name holds
    in the reconstructed store exactly when it holds in the expanded
    store. -/
theorem holds_setFree {se : SetExpansion} {s : Store}
    {pred : PredicateInterpretation} {c : ConstraintItem}
    (h : constraintMentionsSet se c = false) :
    c.Holds pred (setStore se s) ↔ c.Holds pred s := by
  have hargs : c.args.mapM (Expr.eval (setStore se s)) =
      c.args.mapM (Expr.eval s) := by
    apply mapM_congr_set
    intro e he
    exact exprMentionsSet_eval (by
      have := (List.any_eq_false.mp (by simpa [constraintMentionsSet] using h)) e he
      simpa using this)
  unfold ConstraintItem.Holds
  rw [hargs]


/-- The full interpretation is the standard interpretation on names
    outside the global-constraint set. -/
theorem fullInterp_std_set {n : String} (hn : ¬ n ∈ globalsNames) :
    fullInterp (Ident.mk n) = stdInterp (Ident.mk n) := by
  simp only [fullInterp, if_neg hn]

/-- A Boolean pin `bool_not(b, !v)` holds exactly when `b` is `v`. -/
theorem pinBool_holds {b : String} {v : Bool} {s : Store} :
    (pinBoolConstraint b v).Holds fullInterp s ↔ s (Ident.mk b) = some (.bool v) := by
  unfold pinBoolConstraint ConstraintItem.Holds
  rw [show fullInterp (Ident.mk "bool_not") = stdInterp (Ident.mk "bool_not") from
    fullInterp_std_set (by decide)]
  constructor
  · rintro ⟨args, hmap, hinterp⟩
    simp only [List.mapM_cons, List.mapM_nil, Expr.eval, BasicExpr.eval] at hmap
    cases hb : s (Ident.mk b) with
    | none => simp [hb] at hmap
    | some val =>
      rw [hb] at hmap
      simp [BasicLiteral.denote] at hmap
      subst hmap
      simp only [stdInterp] at hinterp
      cases val with
      | bool bb =>
        simp at hinterp
        have : bb = v := by simpa using hinterp.symm
        rw [this]
      | int i => simp at hinterp
      | setOfInt x => simp at hinterp
      | array x => simp at hinterp
  · intro h
    refine ⟨[.bool v, .bool (!v)], ?_, ?_⟩
    · simp [Expr.eval, BasicExpr.eval, BasicLiteral.denote, h]
    · simp [stdInterp]

/-- A Boolean equality `bool_eq(b, r)` holds exactly when both are
    Boolean values and they are equal. -/
theorem boolEq_holds {b r : String} {s : Store} :
    (boolEqConstraint b r).Holds fullInterp s ↔
      ∃ vb vr, s (Ident.mk b) = some (.bool vb) ∧
        s (Ident.mk r) = some (.bool vr) ∧ vb = vr := by
  unfold boolEqConstraint ConstraintItem.Holds
  rw [show fullInterp (Ident.mk "bool_eq") = stdInterp (Ident.mk "bool_eq") from
    fullInterp_std_set (by decide)]
  constructor
  · rintro ⟨args, hmap, hinterp⟩
    simp only [List.mapM_cons, List.mapM_nil, Expr.eval, BasicExpr.eval] at hmap
    cases hb : s (Ident.mk b) with
    | none => simp [hb] at hmap
    | some vb =>
      cases hr : s (Ident.mk r) with
      | none => simp [hb, hr] at hmap
      | some vr =>
        rw [hb, hr] at hmap
        simp [BasicLiteral.denote] at hmap
        subst hmap
        simp only [stdInterp] at hinterp
        cases vb <;> cases vr <;> simp_all
  · rintro ⟨vb, vr, hb, hr, heq⟩
    refine ⟨[.bool vb, .bool vr], ?_, ?_⟩
    · simp [Expr.eval, BasicExpr.eval, BasicLiteral.denote, hb, hr]
    · simp [stdInterp, heq]


/-- The source set value of an info entry reads the declared set variable. -/
theorem SetInfo.sourceSet?_some {i : SetInfo} {s : Store} {sv : IntSetValue}
    (h : i.sourceSet? s = some sv) :
    s (Ident.mk i.name) = some (.setOfInt sv) := by
  unfold SetInfo.sourceSet? at h
  cases hs : s (Ident.mk i.name) with
  | none => rw [hs] at h; cases h
  | some val =>
      rw [hs] at h
      cases val with
      | bool b => cases h
      | int i => cases h
      | setOfInt sv' =>
          rw [Option.some.injEq] at h
          subst h
          rfl
      | array l => cases h

/-- The source-membership Boolean is true exactly when the source set
    value contains the value. -/
theorem SetInfo.sourceContainsB_true_iff {i : SetInfo} {s : Store} {sv : IntSetValue}
    (h : i.sourceSet? s = some sv) {v : Int} :
    i.sourceContainsB s v = true ↔ sv.Contains v := by
  unfold SetInfo.sourceContainsB
  rw [h]
  simp

/-- After encoding and rebuilding, a set variable's reconstructed value
    has exactly the source value's members, provided the source value is
    inside the declared type. -/
theorem SetInfo.rebuilt_encodeStore_contains_iff {se : SetExpansion} {i : SetInfo}
    {s : Store} {sv : IntSetValue}
    (hnames : se.boolNames.Nodup)
    (hbools : (i.bools.map Prod.fst).Nodup)
    (hvals : (i.bools.map Prod.snd).Nodup)
    (hi : i ∈ se.sets) (hsrc : i.sourceSet? s = some sv)
    (huniv : setUniverse? i.ty = some i.values)
    (hty : i.ty.contains (.setOfInt sv)) :
    ∀ v, (i.rebuilt (encodeStore se s)).Contains v ↔ sv.Contains v := by
  intro v
  have hsrcB : i.sourceContainsB s v = true ↔ sv.Contains v :=
    SetInfo.sourceContainsB_true_iff hsrc
  cases hb : i.boolAt v with
  | none =>
      have hvnot : v ∉ i.values := by
        intro hv
        change v ∈ i.bools.map Prod.snd at hv
        obtain ⟨p, hp, hpv⟩ := List.mem_map.mp hv
        have hsome : i.boolAt p.2 = some p.1 :=
          SetInfo.boolAt_eq_some_of_mem hvals hp rfl
        rw [hpv] at hsome
        rw [hb] at hsome
        cases hsome
      constructor
      · intro h
        exact absurd h (SetInfo.not_contains_rebuilt hvnot)
      · intro hc
        have hv : v ∈ i.values := by
          have := (setUniverse?_mem huniv).mpr ⟨sv, hty, hc⟩
          exact this
        exact absurd hv hvnot
  | some b =>
      have hb' : i.boolAt v = some b := hb
      have hreb := SetInfo.rebuilt_contains_iff_boolAt
        (s := encodeStore se s) hvals hb'
      rw [hreb]
      obtain ⟨p, hp, hpb, hpv⟩ := SetInfo.boolAt_some hb'
      have henc : encodeStore se s (Ident.mk b) =
          some (.bool (i.sourceContainsB s v)) := by
        have h := SetExpansion.encodeStore_bool (s := s) hnames hbools hi hp
        rw [hpb, hpv] at h
        exact h
      constructor
      · intro htrue
        rw [henc] at htrue
        have : i.sourceContainsB s v = true := by simpa using htrue
        exact hsrcB.mp this
      · intro hc
        have : i.sourceContainsB s v = true := hsrcB.mpr hc
        rw [henc, this]

/-- The reconstructed value of a set variable after encoding is
    semantically equal to its source value. -/
theorem SetInfo.setStore_encodeStore_semEq {se : SetExpansion} {i : SetInfo}
    {s : Store} {sv : IntSetValue}
    (hset : se.setNames.Nodup)
    (hnames : se.boolNames.Nodup)
    (hbools : (i.bools.map Prod.fst).Nodup)
    (hvals : (i.bools.map Prod.snd).Nodup)
    (hi : i ∈ se.sets) (hsrc : i.sourceSet? s = some sv)
    (huniv : setUniverse? i.ty = some i.values)
    (hty : i.ty.contains (.setOfInt sv)) :
    ∃ v w, setStore se (encodeStore se s) (Ident.mk i.name) = some v ∧
      s (Ident.mk i.name) = some w ∧ Value.SemEq v w := by
  refine ⟨.setOfInt (i.rebuilt (encodeStore se s)), .setOfInt sv, ?_,
    SetInfo.sourceSet?_some hsrc, ?_⟩
  · exact SetExpansion.setStore_setName hset hi _
  · exact SetInfo.rebuilt_encodeStore_contains_iff hnames hbools hvals hi hsrc huniv hty

/-- A set-info lookup yields a table entry. -/
theorem SetExpansion.mem_sets_of_infoOf {se : SetExpansion} {x : Ident} {i : SetInfo}
    (h : se.infoOf x = some i) : i ∈ se.sets := by
  unfold SetExpansion.infoOf at h
  exact List.mem_of_find?_eq_some h

/-- A set-info lookup preserves the name. -/
theorem SetExpansion.infoOf_name {se : SetExpansion} {x : Ident} {i : SetInfo}
    (h : se.infoOf x = some i) : i.name = x.name := by
  unfold SetExpansion.infoOf at h
  simpa using (List.find?_some h)

/-- A fresh Boolean value after encoding reads the source membership. -/
theorem SetExpansion.encodeStore_boolAt {se : SetExpansion} {s : Store}
    {i : SetInfo} {v : Int} {b : String}
    (hnames : se.boolNames.Nodup) (hi : i ∈ se.sets)
    (hb : i.boolAt v = some b) :
    encodeStore se s (Ident.mk b) = some (.bool (i.sourceContainsB s v)) := by
  obtain ⟨p, hp, hpb, hpv⟩ := SetInfo.boolAt_some hb
  have hfib : (i.bools.map Prod.fst).Nodup :=
    nodup_flatMap_fiber (by simpa [SetExpansion.boolNames] using hnames) i hi
  have henc := SetExpansion.encodeStore_bool (s := s) hnames hfib hi hp
  rwa [hpb, hpv] at henc

/-- A name that is not a set name has no set-info entry. -/
theorem SetExpansion.infoOf_eq_none_of_isSetName_false {se : SetExpansion} {x : Ident}
    (h : se.isSetName x = false) : se.infoOf x = none := by
  unfold SetExpansion.isSetName at h
  cases hh : se.infoOf x with
  | none => rfl
  | some i => rw [hh] at h; cases h

/-- A value with no Boolean slot is outside the universe. -/
theorem SetInfo.not_mem_values_of_boolAt_none {i : SetInfo} {v : Int}
    (h : i.boolAt v = none) : v ∉ i.values := by
  intro hv
  have hfind : i.bools.find? (fun p => p.2 = v) = none := by
    unfold SetInfo.boolAt at h
    rwa [Option.map_eq_none_iff] at h
  obtain ⟨p, hp, hpv⟩ := List.mem_map.mp (show v ∈ i.bools.map Prod.snd from hv)
  exact (List.find?_eq_none.mp hfind) p hp (by simpa using hpv)

/-- A value with no Boolean slot is not in the rebuilt set. -/
theorem SetInfo.not_contains_rebuilt_of_boolAt_none {i : SetInfo} {s : Store}
    {v : Int} (h : i.boolAt v = none) : ¬ (i.rebuilt s).Contains v := by
  intro hc
  obtain ⟨p, hp, hpv, _⟩ := SetInfo.mem_rebuilt.mp hc
  exact SetInfo.not_mem_values_of_boolAt_none h (by
    rw [SetInfo.values]
    exact List.mem_map.mpr ⟨p, hp, hpv⟩)

/-- The reconstructed store at a set name is the rebuilt set. -/
theorem SetExpansion.setStore_at {se : SetExpansion} {s : Store} {x : Ident}
    {i : SetInfo} (h : se.infoOf x = some i) :
    setStore se s x = some (.setOfInt (i.rebuilt s)) := by
  unfold setStore
  rw [h]

/-- Two basic-expression arguments evaluate through `mapM` to a pair. -/
theorem holds_basic_two {name : String} (hn : ¬ name ∈ globalsNames)
    {b₁ b₂ : BasicExpr} {s : Store} {anns : List Annotation} :
    (ConstraintItem.mk (Ident.mk name) [.basic b₁, .basic b₂] anns).Holds
        fullInterp s ↔
      ∃ v₁ v₂, BasicExpr.eval s b₁ = some v₁ ∧
        BasicExpr.eval s b₂ = some v₂ ∧
        stdInterp (Ident.mk name) [v₁, v₂] := by
  unfold ConstraintItem.Holds
  rw [fullInterp_std_set hn]
  constructor
  · rintro ⟨args, hmap, hinterp⟩
    simp only [List.mapM_cons, List.mapM_nil, Expr.eval] at hmap
    cases h₁ : BasicExpr.eval s b₁ with
    | none => rw [h₁] at hmap; simp at hmap
    | some v₁ =>
        cases h₂ : BasicExpr.eval s b₂ with
        | none => rw [h₁, h₂] at hmap; simp at hmap
        | some v₂ =>
            rw [h₁, h₂] at hmap
            simp at hmap
            subst hmap
            exact ⟨v₁, v₂, rfl, rfl, hinterp⟩
  · rintro ⟨v₁, v₂, h₁, h₂, hinterp⟩
    refine ⟨[v₁, v₂], ?_, hinterp⟩
    simp [Expr.eval, h₁, h₂]

/-- Three basic-expression arguments evaluate through `mapM` to a triple. -/
theorem holds_basic_three {name : String} (hn : ¬ name ∈ globalsNames)
    {b₁ b₂ b₃ : BasicExpr} {s : Store} {anns : List Annotation} :
    (ConstraintItem.mk (Ident.mk name) [.basic b₁, .basic b₂, .basic b₃] anns).Holds
        fullInterp s ↔
      ∃ v₁ v₂ v₃, BasicExpr.eval s b₁ = some v₁ ∧
        BasicExpr.eval s b₂ = some v₂ ∧
        BasicExpr.eval s b₃ = some v₃ ∧
        stdInterp (Ident.mk name) [v₁, v₂, v₃] := by
  unfold ConstraintItem.Holds
  rw [fullInterp_std_set hn]
  constructor
  · rintro ⟨args, hmap, hinterp⟩
    simp only [List.mapM_cons, List.mapM_nil, Expr.eval] at hmap
    cases h₁ : BasicExpr.eval s b₁ with
    | none => rw [h₁] at hmap; simp at hmap
    | some v₁ =>
        cases h₂ : BasicExpr.eval s b₂ with
        | none => rw [h₁, h₂] at hmap; simp at hmap
        | some v₂ =>
            cases h₃ : BasicExpr.eval s b₃ with
            | none => rw [h₁, h₂, h₃] at hmap; simp at hmap
            | some v₃ =>
                rw [h₁, h₂, h₃] at hmap
                simp at hmap
                subst hmap
                exact ⟨v₁, v₂, v₃, rfl, rfl, rfl, hinterp⟩
  · rintro ⟨v₁, v₂, v₃, h₁, h₂, h₃, hinterp⟩
    refine ⟨[v₁, v₂, v₃], ?_, hinterp⟩
    simp [Expr.eval, h₁, h₂, h₃]

/-- The truth of `set_in(k, S)` in terms of the evaluated set value. -/
theorem setIn_holds_iff {k : Int} {S : BasicExpr} {s : Store}
    {anns : List Annotation} :
    (ConstraintItem.mk (Ident.mk "set_in")
        [.basic (.lit (.int k)), .basic S] anns).Holds fullInterp s ↔
      ∃ sv, BasicExpr.eval s S = some (.setOfInt sv) ∧ sv.Contains k := by
  rw [holds_basic_two (by decide)]
  constructor
  · rintro ⟨v₁, v₂, h₁, h₂, hP⟩
    simp only [BasicExpr.eval, BasicLiteral.denote, Option.some.injEq] at h₁
    subst h₁
    cases v₂ with
    | setOfInt sv => exact ⟨sv, h₂, by simpa [stdInterp] using hP⟩
    | bool b => simp [stdInterp] at hP
    | int i => simp [stdInterp] at hP
    | array l => simp [stdInterp] at hP
  · rintro ⟨sv, h₂, hmem⟩
    exact ⟨.int k, .setOfInt sv, rfl, h₂, by simpa [stdInterp] using hmem⟩

/-- The truth of `set_in_reif(k, S, R)` for a Boolean result value. -/
theorem setInReif_holds_iff {k : Int} {S R : BasicExpr} {s : Store}
    {anns : List Annotation} :
    (ConstraintItem.mk (Ident.mk "set_in_reif")
        [.basic (.lit (.int k)), .basic S, .basic R] anns).Holds fullInterp s ↔
      ∃ sv r, BasicExpr.eval s S = some (.setOfInt sv) ∧
        BasicExpr.eval s R = some (.bool r) ∧
        ((r = true ∧ sv.Contains k) ∨ (r = false ∧ ¬ sv.Contains k)) := by
  rw [holds_basic_three (by decide)]
  constructor
  · rintro ⟨v₁, v₂, v₃, h₁, h₂, h₃, hP⟩
    simp only [BasicExpr.eval, BasicLiteral.denote, Option.some.injEq] at h₁
    subst h₁
    revert hP
    cases v₂ with
    | setOfInt sv =>
        intro hP
        cases v₃ with
        | bool r =>
            exact ⟨sv, r, h₂, h₃, by simpa [stdInterp] using hP⟩
        | int i => simp [stdInterp] at hP
        | setOfInt x => simp [stdInterp] at hP
        | array x => simp [stdInterp] at hP
    | bool b => intro hP; simp [stdInterp] at hP
    | int i => intro hP; simp [stdInterp] at hP
    | array l => intro hP; simp [stdInterp] at hP
  · rintro ⟨sv, r, h₂, h₃, hP⟩
    exact ⟨.int k, .setOfInt sv, .bool r, rfl, h₂, h₃,
      by simpa [stdInterp] using hP⟩


/-! ## Per-constraint semantic preservation -/

/-- **Soundness of the per-constraint rewrite**: if the expanded rows of
    `c` hold at `s`, the source constraint holds at the reconstructed
    store. -/
theorem rewriteConstraint_sound {se : SetExpansion} {s : Store}
    {c : ConstraintItem} {cs : List ConstraintItem}
    (hvals : ∀ i ∈ se.sets, i.values.Nodup)
    (h : rewriteConstraint se c = some cs)
    (hs : ∀ d ∈ cs, d.Holds fullInterp s) :
    c.Holds fullInterp (setStore se s) := by
  rcases c with ⟨nm, args, anns⟩
  unfold rewriteConstraint at h
  split at h
  case h_1 =>
    rename_i k S hname hargs
    dsimp only at hname hargs
    have hnm : nm = Ident.mk "set_in" := ident_eq_of_name hname
    subst hnm
    subst hargs
    split at h
    case h_1 =>
      rename_i i hinfo
      split at h
      case h_1 =>
        rename_i b hb
        have hcs : cs = [pinBoolConstraint b true] := (Option.some.inj h).symm
        rw [hcs] at hs
        have hpin : (pinBoolConstraint b true).Holds fullInterp s :=
          hs _ List.mem_cons_self
        have hbval : s (Ident.mk b) = some (.bool true) := pinBool_holds.mp hpin
        obtain ⟨p, hp, hpb, hpv⟩ := SetInfo.boolAt_some hb
        have hmem : (i.rebuilt s).Contains k := by
          rw [SetInfo.mem_rebuilt]
          exact ⟨p, hp, hpv, by rw [hpb]; exact hbval⟩
        rw [setIn_holds_iff]
        exact ⟨i.rebuilt s, SetExpansion.setStore_at hinfo, hmem⟩
      case h_2 =>
        rename_i hbnone
        have hcs : cs = [falseConstraint] := (Option.some.inj h).symm
        rw [hcs] at hs
        exact absurd (hs _ List.mem_cons_self) (falseConstraint_holds_false s)
    case h_2 =>
      rename_i hinone
      split at h
      case isTrue => cases h
      case isFalse =>
        rename_i hno
        have hcs : cs =
            [{ name := Ident.mk "set_in",
               args := [.basic (.lit (.int k)), .basic (.ident S)],
               anns := anns }] := (Option.some.inj h).symm
        rw [hcs] at hs
        exact (holds_setFree (by simpa using hno)).mpr (hs _ List.mem_cons_self)
  case h_2 =>
    rename_i k S r hname hargs
    dsimp only at hname hargs
    have hnm : nm = Ident.mk "set_in_reif" := ident_eq_of_name hname
    subst hnm
    subst hargs
    split at h
    case h_1 =>
      rename_i i hinfo
      split at h
      case h_1 =>
        rename_i b hb
        split at h
        case h_1 =>
          rename_i z hz
          split at h
          case isTrue => cases h
          case isFalse =>
            rename_i hznot
            have hcs : cs = [boolEqConstraint b hz.name] :=
              (Option.some.inj h).symm
            rw [hcs] at hs
            obtain ⟨vb, vr, hbval, hzval, hveq⟩ :=
              boolEq_holds.mp (hs _ List.mem_cons_self)
            have hzn : se.infoOf hz = none :=
              SetExpansion.infoOf_eq_none_of_isSetName_false (by simpa using hznot)
            have hzstore : setStore se s hz = some (.bool vr) := by
              rw [SetExpansion.setStore_of_none hzn]
              exact hzval
            have hi : i ∈ se.sets := SetExpansion.mem_sets_of_infoOf hinfo
            have hcont := SetInfo.rebuilt_contains_iff_boolAt
              (s := s) (hvals i hi) hb
            subst hveq
            rw [setInReif_holds_iff]
            refine ⟨i.rebuilt s, vb, SetExpansion.setStore_at hinfo,
              hzstore, ?_⟩
            cases vb with
            | true =>
                exact Or.inl ⟨rfl, hcont.mpr (by rw [hbval])⟩
            | false =>
                exact Or.inr ⟨rfl, fun hc => by
                  have := hcont.mp hc
                  rw [hbval] at this
                  cases this⟩
        case h_2 =>
          rename_i r' hr'
          have hcs : cs = [pinBoolConstraint b true] :=
            (Option.some.inj h).symm
          rw [hcs] at hs
          have hbval : s (Ident.mk b) = some (.bool true) :=
            pinBool_holds.mp (hs _ List.mem_cons_self)
          have hi : i ∈ se.sets := SetExpansion.mem_sets_of_infoOf hinfo
          have hcont := SetInfo.rebuilt_contains_iff_boolAt (s := s) (hvals i hi) hb
          rw [setInReif_holds_iff]
          exact ⟨i.rebuilt s, true, SetExpansion.setStore_at hinfo, rfl,
            Or.inl ⟨rfl, hcont.mpr hbval⟩⟩
        case h_3 =>
          rename_i r' hr'
          have hcs : cs = [pinBoolConstraint b false] :=
            (Option.some.inj h).symm
          rw [hcs] at hs
          have hbval : s (Ident.mk b) = some (.bool false) :=
            pinBool_holds.mp (hs _ List.mem_cons_self)
          have hi : i ∈ se.sets := SetExpansion.mem_sets_of_infoOf hinfo
          have hcont := SetInfo.rebuilt_contains_iff_boolAt (s := s) (hvals i hi) hb
          rw [setInReif_holds_iff]
          exact ⟨i.rebuilt s, false, SetExpansion.setStore_at hinfo, rfl,
            Or.inr ⟨rfl, fun hc => by
              have := hcont.mp hc
              rw [hbval] at this
              cases this⟩⟩
        case h_4 => cases h
      case h_2 =>
        rename_i hbnone
        split at h
        case h_1 =>
          rename_i z hz
          split at h
          case isTrue => cases h
          case isFalse =>
            rename_i hznot
            have hcs : cs = [pinBoolConstraint hz.name false] :=
              (Option.some.inj h).symm
            rw [hcs] at hs
            have hzval : s (Ident.mk hz.name) = some (.bool false) :=
              pinBool_holds.mp (hs _ List.mem_cons_self)
            have hzn : se.infoOf hz = none :=
              SetExpansion.infoOf_eq_none_of_isSetName_false (by simpa using hznot)
            have hzstore : setStore se s hz = some (.bool false) := by
              rw [SetExpansion.setStore_of_none hzn]
              exact hzval
            rw [setInReif_holds_iff]
            exact ⟨i.rebuilt s, false, SetExpansion.setStore_at hinfo,
              hzstore, Or.inr ⟨rfl,
                SetInfo.not_contains_rebuilt_of_boolAt_none hbnone⟩⟩
        case h_2 =>
          rename_i r' hr'
          have hcs : cs = [falseConstraint] := (Option.some.inj h).symm
          rw [hcs] at hs
          exact absurd (hs _ List.mem_cons_self) (falseConstraint_holds_false s)
        case h_3 =>
          rename_i r' hr'
          have hcs : cs = [] := (Option.some.inj h).symm
          rw [setInReif_holds_iff]
          exact ⟨i.rebuilt s, false, SetExpansion.setStore_at hinfo, rfl,
            Or.inr ⟨rfl, SetInfo.not_contains_rebuilt_of_boolAt_none hbnone⟩⟩
        case h_4 => cases h
    case h_2 =>
      rename_i hinone
      split at h
      case isTrue => cases h
      case isFalse =>
        rename_i hno
        have hcs : cs =
            [{ name := Ident.mk "set_in_reif",
               args := [.basic (.lit (.int k)), .basic (.ident S), r],
               anns := anns }] := (Option.some.inj h).symm
        rw [hcs] at hs
        exact (holds_setFree (by simpa using hno)).mpr (hs _ List.mem_cons_self)
  case h_3 =>
    split at h
    case isTrue => cases h
    case isFalse =>
      rename_i hno
      have hcs : cs = [{ name := nm, args := args, anns := anns }] :=
        (Option.some.inj h).symm
      rw [hcs] at hs
      exact (holds_setFree (by
        have hc : constraintMentionsSet se
            { name := nm, args := args, anns := anns } = true → False := by
          simpa using hno
        simpa using hc)).mpr (hs _ List.mem_cons_self)


/-! ## Names mentioned by expressions and the completeness store -/

/-- The identifier names of a basic expression. -/
def basicNames : BasicExpr → List String
  | .lit _ => []
  | .ident x => [x.name]

/-- The identifier names of an expression. -/
def exprNames : Expr → List String
  | .basic b => basicNames b
  | .array es => es.flatMap basicNames

/-- The identifier names a constraint mentions. -/
def constraintNames (c : ConstraintItem) : List String :=
  c.args.flatMap exprNames

/-- The identifier names a variable declaration's initializer mentions. -/
def varDeclNames : VarDeclItem → List String
  | .basic _ _ _ none => []
  | .basic _ _ _ (some e) => basicNames e
  | .array _ _ _ es => es.flatMap basicNames

/-- A basic expression whose names are not fresh Booleans evaluates the
    same in the completeness store. -/
theorem basicNames_eval_encodeStore {se : SetExpansion} {s : Store}
    {b : BasicExpr} (h : ∀ x ∈ basicNames b, x ∉ se.boolNames) :
    b.eval (encodeStore se s) = b.eval s := by
  cases b with
  | lit l => rfl
  | ident y =>
      have hy : y.name ∉ se.boolNames := h y.name (by simp [basicNames])
      simp [BasicExpr.eval, SetExpansion.encodeStore_of_not_bool hy]

/-- An expression whose names are not fresh Booleans evaluates the same
    in the completeness store. -/
theorem exprNames_eval_encodeStore {se : SetExpansion} {s : Store}
    {e : Expr} (h : ∀ x ∈ exprNames e, x ∉ se.boolNames) :
    e.eval (encodeStore se s) = e.eval s := by
  cases e with
  | basic b =>
      exact basicNames_eval_encodeStore (by
        intro x hx
        exact h x (by simpa [exprNames] using hx))
  | array es =>
      show (es.mapM (BasicExpr.eval (encodeStore se s))).map Value.array =
        (es.mapM (BasicExpr.eval s)).map Value.array
      have hall : ∀ b ∈ es,
          BasicExpr.eval (encodeStore se s) b = BasicExpr.eval s b := by
        intro b hb
        exact basicNames_eval_encodeStore (by
          intro x hx
          exact h x (by
            simp only [exprNames, List.mem_flatMap]
            exact ⟨b, hb, hx⟩))
      rw [mapM_congr_set hall]

/-- A constraint whose names are not fresh Booleans holds in the
    completeness store exactly when it holds in the source store. -/
theorem holds_encodeStore_free {se : SetExpansion} {s : Store}
    {pred : PredicateInterpretation} {c : ConstraintItem}
    (h : ∀ x ∈ constraintNames c, x ∉ se.boolNames) :
    c.Holds pred (encodeStore se s) ↔ c.Holds pred s := by
  have hargs : c.args.mapM (Expr.eval (encodeStore se s)) =
      c.args.mapM (Expr.eval s) := by
    apply mapM_congr_set
    intro e he
    exact exprNames_eval_encodeStore (by
      intro x hx
      exact h x (by
        simp only [constraintNames, List.mem_flatMap]
        exact ⟨e, he, hx⟩))
  unfold ConstraintItem.Holds
  rw [hargs]

/-- The completeness store leaves every declared source name unchanged. -/
theorem SetExpansion.encodeStore_of_mem_taken {se : SetExpansion} {m : Model}
    {s : Store} {x : Ident} {taken : List String} (inv : se.Inv taken m) (hx : x.name ∈ setTaken m) :
    encodeStore se s x = s x := by
  apply SetExpansion.encodeStore_of_not_bool
  intro hb
  obtain ⟨n', d⟩ := inv.decls
  rw [SetExpansion.boolNames] at hb
  obtain ⟨i, hi, hmem⟩ := List.mem_flatMap.mp hb
  rw [List.mem_map] at hmem
  obtain ⟨p, hp, hpn⟩ := hmem
  have hfresh := d.fresh i hi p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)
  exact hfresh (by simpa [hpn] using inv.superset _ hx)

/-! ## Declared names and well-formedness -/

/-- A name in the static environment is declared in the model. -/
theorem staticEnv_mem_setTaken {m : Model} {x : Ident} {info : FznType × Bool}
    (h : m.staticEnv x = some info) : x.name ∈ setTaken m := by
  unfold Model.staticEnv at h
  cases hp : lookupIdent x (m.parameters.map
      (fun d => (d.name, (d.type, false)))) with
  | some info' =>
      obtain ⟨y, hy, hyn⟩ := lookupIdent_inv_mem x _ info' hp
      obtain ⟨d, hd, hdy⟩ := List.mem_map.mp hy
      have hdy' : d.name = y := ((Prod.mk.injEq ..).mp hdy).1
      rw [setTaken]
      exact List.mem_append_left _ (List.mem_map.mpr
        ⟨d, hd, by rw [hdy']; exact hyn⟩)
  | none =>
      rw [hp] at h
      obtain ⟨y, hy, hyn⟩ := lookupIdent_inv_mem x _ info h
      obtain ⟨d, hd, hdy⟩ := List.mem_map.mp hy
      have hdy' : d.name = y := ((Prod.mk.injEq ..).mp hdy).1
      rw [setTaken]
      exact List.mem_append_right _ (List.mem_map.mpr
        ⟨d, hd, by rw [hdy']; exact hyn⟩)

/-- The names of a checked basic expression are declared. -/
theorem checkBase_names {env : StaticEnv} {b : BasicExpr}
    {bt : BasicPredParamType} (h : b.checkBase env bt) :
    ∀ x ∈ basicNames b, ∃ info, env (Ident.mk x) = some info := by
  cases b with
  | lit l =>
      intro x hx
      simp [basicNames] at hx
  | ident y =>
      intro x hx
      simp only [basicNames, List.mem_singleton] at hx
      dsimp only [BasicExpr.checkBase] at h
      cases hv : env y with
      | none => rw [hv] at h; cases h
      | some info => exact ⟨info, by subst hx; simpa using hv⟩

/-- The names of a checked argument expression are declared. -/
theorem checkArg_names {env : StaticEnv} {e : Expr} {pt : PredParamType}
    (h : e.checkArg env pt) :
    ∀ x ∈ exprNames e, ∃ info, env (Ident.mk x) = some info := by
  cases pt with
  | basic bt =>
      cases e with
      | basic b =>
          dsimp only [Expr.checkArg] at h
          intro x hx
          exact checkBase_names h x (by simpa [exprNames] using hx)
      | array es =>
          dsimp only [Expr.checkArg] at h
  | array idx bt =>
      cases e with
      | basic b =>
          cases b with
          | lit l =>
              intro x hx
              simp [exprNames, basicNames] at hx
          | ident y =>
              intro x hx
              simp only [exprNames, basicNames, List.mem_singleton] at hx
              dsimp only [Expr.checkArg] at h
              cases hv : env y with
              | none => rw [hv] at h; cases h
              | some info => exact ⟨info, by subst hx; simpa using hv⟩
      | array es =>
          dsimp only [Expr.checkArg] at h
          intro x hx
          simp only [exprNames, List.mem_flatMap] at hx
          obtain ⟨b, hb, hxb⟩ := hx
          exact checkBase_names (h.2 b hb) x hxb

/-- The names of a checked initializer are declared. -/
theorem hasBaseType_names {env : StaticEnv} {b : BasicExpr} {t : BaseType}
    (h : b.hasBaseType env t) :
    ∀ x ∈ basicNames b, ∃ info, env (Ident.mk x) = some info := by
  cases b with
  | lit l =>
      intro x hx
      simp [basicNames] at hx
  | ident y =>
      intro x hx
      simp only [basicNames, List.mem_singleton] at hx
      dsimp only [BasicExpr.hasBaseType] at h
      cases hv : env y with
      | none => rw [hv] at h; cases h
      | some info => exact ⟨info, by subst hx; simpa using hv⟩

/-- In a well-formed model, every name a constraint mentions is declared. -/
theorem wf_constraint_names_taken {m : Model} (hwf : WellFormed fullSig m) :
    ∀ c ∈ m.constraints, ∀ x ∈ constraintNames c, x ∈ setTaken m := by
  intro c hc x hx
  obtain ⟨params, hs, hfor⟩ := hwf.constraintsChecked c hc
  simp only [constraintNames, List.mem_flatMap] at hx
  obtain ⟨e, he, hxe⟩ := hx
  obtain ⟨pt, hpt, harg⟩ := forall2_mem (Expr.checkArg m.staticEnv) c.args
    params hfor e he
  obtain ⟨info, hinv⟩ := checkArg_names harg x hxe
  exact staticEnv_mem_setTaken hinv

/-- In a well-formed model, every name an initializer mentions is
    declared. -/
theorem wf_init_names_taken {m : Model} (hwf : WellFormed fullSig m) :
    ∀ d ∈ m.variables, ∀ x ∈ varDeclNames d, x ∈ setTaken m := by
  intro d hd x hx
  have hinit := hwf.variableInitializers d hd
  cases d with
  | basic ty n anns init =>
      cases init with
      | none => simp [varDeclNames] at hx
      | some e =>
          simp only [varDeclNames] at hx
          obtain ⟨info, hinv⟩ := hasBaseType_names hinit x hx
          exact staticEnv_mem_setTaken hinv
  | array ty n anns es =>
      simp only [varDeclNames, List.mem_flatMap] at hx
      obtain ⟨b, hb, hxb⟩ := hx
      obtain ⟨info, hinv⟩ := hasBaseType_names (hinit b hb) x hxb
      exact staticEnv_mem_setTaken hinv


/-- **Completeness of the per-constraint rewrite**: every source
    constraint's expanded rows hold in the completeness store. -/
theorem rewriteConstraint_complete {se : SetExpansion} {s : Store}
    {c : ConstraintItem} {cs : List ConstraintItem}
    (hnames : se.boolNames.Nodup)
    (huni : ∀ i ∈ se.sets, setUniverse? i.ty = some i.values)
    (hdom : ∀ i ∈ se.sets, ∀ sv,
      s (Ident.mk i.name) = some (.setOfInt sv) →
        i.ty.contains (.setOfInt sv))
    (hfree : ∀ x ∈ constraintNames c, x ∉ se.boolNames)
    (h : rewriteConstraint se c = some cs)
    (hc : c.Holds fullInterp s) :
    ∀ d ∈ cs, d.Holds fullInterp (encodeStore se s) := by
  rcases c with ⟨nm, args, anns⟩
  unfold rewriteConstraint at h
  split at h
  case h_1 =>
    rename_i k S hname hargs
    dsimp only at hname hargs
    have hnm : nm = Ident.mk "set_in" := ident_eq_of_name hname
    subst hnm
    subst hargs
    split at h
    case h_1 =>
      rename_i i hinfo
      split at h
      case h_1 =>
        rename_i b hb
        have hcs : cs = [pinBoolConstraint b true] := (Option.some.inj h).symm
        rw [hcs]
        intro d hd
        rw [List.mem_singleton] at hd
        subst hd
        obtain ⟨sv, hsv, hmem⟩ := setIn_holds_iff.mp hc
        have hi : i ∈ se.sets := SetExpansion.mem_sets_of_infoOf hinfo
        have hS : Ident.mk i.name = S :=
          ident_eq_of_name (SetExpansion.infoOf_name hinfo)
        have hread : s (Ident.mk i.name) = some (.setOfInt sv) := by
          rw [hS]
          exact hsv
        have hsource : i.sourceSet? s = some sv := by
          unfold SetInfo.sourceSet?
          rw [hread]
        have hcontain : i.sourceContainsB s k = true :=
          (SetInfo.sourceContainsB_true_iff hsource).mpr hmem
        rw [pinBool_holds, SetExpansion.encodeStore_boolAt hnames hi hb,
          hcontain]
      case h_2 =>
        rename_i hbnone
        have hcs : cs = [falseConstraint] := (Option.some.inj h).symm
        rw [hcs]
        intro d hd
        rw [List.mem_singleton] at hd
        subst hd
        obtain ⟨sv, hsv, hmem⟩ := setIn_holds_iff.mp hc
        have hi : i ∈ se.sets := SetExpansion.mem_sets_of_infoOf hinfo
        have hS : Ident.mk i.name = S :=
          ident_eq_of_name (SetExpansion.infoOf_name hinfo)
        have hread : s (Ident.mk i.name) = some (.setOfInt sv) := by
          rw [hS]
          exact hsv
        have hcont := hdom i hi sv hread
        have hmemv : k ∈ i.values :=
          (setUniverse?_mem (huni i hi)).mpr ⟨sv, hcont, hmem⟩
        exact absurd hmemv (SetInfo.not_mem_values_of_boolAt_none hbnone)
    case h_2 =>
      rename_i hinone
      split at h
      case isTrue => cases h
      case isFalse =>
        rename_i hno
        have hcs : cs =
            [{ name := Ident.mk "set_in",
               args := [.basic (.lit (.int k)), .basic (.ident S)],
               anns := anns }] := (Option.some.inj h).symm
        rw [hcs]
        intro d hd
        rw [List.mem_singleton] at hd
        subst hd
        exact (holds_encodeStore_free (by
          intro x hx
          exact hfree x (by simpa [constraintNames] using hx))).mpr hc
  case h_2 =>
    rename_i k S r hname hargs
    dsimp only at hname hargs
    have hnm : nm = Ident.mk "set_in_reif" := ident_eq_of_name hname
    subst hnm
    subst hargs
    split at h
    case h_1 =>
      rename_i i hinfo
      split at h
      case h_1 =>
        rename_i b hb
        split at h
        case h_1 =>
          rename_i z hz
          split at h
          case isTrue => cases h
          case isFalse =>
            rename_i hznot
            have hcs : cs = [boolEqConstraint b hz.name] :=
              (Option.some.inj h).symm
            rw [hcs]
            intro d hd
            rw [List.mem_singleton] at hd
            subst hd
            obtain ⟨sv, rv, hsv, hrv, hdisj⟩ := setInReif_holds_iff.mp hc
            have hi : i ∈ se.sets := SetExpansion.mem_sets_of_infoOf hinfo
            have hS : Ident.mk i.name = S :=
              ident_eq_of_name (SetExpansion.infoOf_name hinfo)
            have hread : s (Ident.mk i.name) = some (.setOfInt sv) := by
              rw [hS]
              exact hsv
            have hsource : i.sourceSet? s = some sv := by
              unfold SetInfo.sourceSet?
              rw [hread]
            have hsrcB : i.sourceContainsB s k = true ↔ sv.Contains k :=
              SetInfo.sourceContainsB_true_iff hsource
            have hzbool : hz.name ∉ se.boolNames := by
              apply hfree hz.name
              simp [constraintNames, exprNames, basicNames]
            have hzstore : encodeStore se s hz = some (.bool rv) := by
              rw [SetExpansion.encodeStore_of_not_bool hzbool]
              exact hrv
            have hsrcval : i.sourceContainsB s k = rv := by
              rcases hdisj with ⟨rfl, hmem⟩ | ⟨rfl, hnot⟩
              · rw [show i.sourceContainsB s k = true from hsrcB.mpr hmem]
              · have hf : i.sourceContainsB s k = false := by
                  cases hbv : i.sourceContainsB s k with
                  | false => rfl
                  | true => exact absurd (hsrcB.mp hbv) hnot
                rw [hf]
            rw [boolEq_holds]
            exact ⟨i.sourceContainsB s k, rv,
              SetExpansion.encodeStore_boolAt hnames hi hb, hzstore,
              hsrcval⟩
        case h_2 =>
          rename_i r' hr'
          have hcs : cs = [pinBoolConstraint b true] :=
            (Option.some.inj h).symm
          rw [hcs]
          intro d hd
          rw [List.mem_singleton] at hd
          subst hd
          obtain ⟨sv, rv, hsv, hrv, hdisj⟩ := setInReif_holds_iff.mp hc
          have hi : i ∈ se.sets := SetExpansion.mem_sets_of_infoOf hinfo
          have hS : Ident.mk i.name = S :=
            ident_eq_of_name (SetExpansion.infoOf_name hinfo)
          have hread : s (Ident.mk i.name) = some (.setOfInt sv) := by
            rw [hS]
            exact hsv
          have hsource : i.sourceSet? s = some sv := by
            unfold SetInfo.sourceSet?
            rw [hread]
          have hsrcB : i.sourceContainsB s k = true ↔ sv.Contains k :=
            SetInfo.sourceContainsB_true_iff hsource
          have hrv' : rv = true := by
            simpa [BasicExpr.eval, BasicLiteral.denote] using hrv
          subst hrv'
          have hmem : sv.Contains k := by
            rcases hdisj with ⟨_, hmem⟩ | ⟨hfalse, _⟩
            · exact hmem
            · exact absurd hfalse (by simp)
          have hcontain : i.sourceContainsB s k = true := hsrcB.mpr hmem
          rw [pinBool_holds, SetExpansion.encodeStore_boolAt hnames hi hb,
            hcontain]
        case h_3 =>
          rename_i r' hr'
          have hcs : cs = [pinBoolConstraint b false] :=
            (Option.some.inj h).symm
          rw [hcs]
          intro d hd
          rw [List.mem_singleton] at hd
          subst hd
          obtain ⟨sv, rv, hsv, hrv, hdisj⟩ := setInReif_holds_iff.mp hc
          have hi : i ∈ se.sets := SetExpansion.mem_sets_of_infoOf hinfo
          have hS : Ident.mk i.name = S :=
            ident_eq_of_name (SetExpansion.infoOf_name hinfo)
          have hread : s (Ident.mk i.name) = some (.setOfInt sv) := by
            rw [hS]
            exact hsv
          have hsource : i.sourceSet? s = some sv := by
            unfold SetInfo.sourceSet?
            rw [hread]
          have hsrcB : i.sourceContainsB s k = true ↔ sv.Contains k :=
            SetInfo.sourceContainsB_true_iff hsource
          have hrv' : rv = false := by
            simpa [BasicExpr.eval, BasicLiteral.denote] using hrv
          subst hrv'
          have hnot : ¬ sv.Contains k := by
            rcases hdisj with ⟨htrue, _⟩ | ⟨_, hnot⟩
            · exact absurd htrue (by simp)
            · exact hnot
          have hf : i.sourceContainsB s k = false := by
            cases hbv : i.sourceContainsB s k with
            | false => rfl
            | true => exact absurd (hsrcB.mp hbv) hnot
          rw [pinBool_holds, SetExpansion.encodeStore_boolAt hnames hi hb,
            hf]
        case h_4 => cases h
      case h_2 =>
        rename_i hbnone
        split at h
        case h_1 =>
          rename_i z hz
          split at h
          case isTrue => cases h
          case isFalse =>
            rename_i hznot
            have hcs : cs = [pinBoolConstraint hz.name false] :=
              (Option.some.inj h).symm
            rw [hcs]
            intro d hd
            rw [List.mem_singleton] at hd
            subst hd
            obtain ⟨sv, rv, hsv, hrv, hdisj⟩ := setInReif_holds_iff.mp hc
            have hi : i ∈ se.sets := SetExpansion.mem_sets_of_infoOf hinfo
            have hS : Ident.mk i.name = S :=
              ident_eq_of_name (SetExpansion.infoOf_name hinfo)
            have hread : s (Ident.mk i.name) = some (.setOfInt sv) := by
              rw [hS]
              exact hsv
            have hcont := hdom i hi sv hread
            have hnot : ¬ sv.Contains k := by
              intro hmem
              have hmemv : k ∈ i.values :=
                (setUniverse?_mem (huni i hi)).mpr ⟨sv, hcont, hmem⟩
              exact SetInfo.not_mem_values_of_boolAt_none hbnone hmemv
            have hrvf : rv = false := by
              rcases hdisj with ⟨htrue, hmem⟩ | ⟨hfalse, _⟩
              · exact absurd hmem hnot
              · exact hfalse
            have hzbool : hz.name ∉ se.boolNames := by
              apply hfree hz.name
              simp [constraintNames, exprNames, basicNames]
            rw [pinBool_holds]
            rw [SetExpansion.encodeStore_of_not_bool hzbool]
            rw [show s hz = some (.bool rv) from hrv, hrvf]
        case h_2 =>
          rename_i r' hr'
          have hcs : cs = [falseConstraint] := (Option.some.inj h).symm
          rw [hcs]
          intro d hd
          rw [List.mem_singleton] at hd
          subst hd
          obtain ⟨sv, rv, hsv, hrv, hdisj⟩ := setInReif_holds_iff.mp hc
          have hi : i ∈ se.sets := SetExpansion.mem_sets_of_infoOf hinfo
          have hS : Ident.mk i.name = S :=
            ident_eq_of_name (SetExpansion.infoOf_name hinfo)
          have hread : s (Ident.mk i.name) = some (.setOfInt sv) := by
            rw [hS]
            exact hsv
          have hcont := hdom i hi sv hread
          have hrv' : rv = true := by
            simpa [BasicExpr.eval, BasicLiteral.denote] using hrv
          subst hrv'
          have hmem : sv.Contains k := by
            rcases hdisj with ⟨_, hmem⟩ | ⟨hfalse, _⟩
            · exact hmem
            · exact absurd hfalse (by simp)
          have hmemv : k ∈ i.values :=
            (setUniverse?_mem (huni i hi)).mpr ⟨sv, hcont, hmem⟩
          exact absurd hmemv (SetInfo.not_mem_values_of_boolAt_none hbnone)
        case h_3 =>
          rename_i r' hr'
          have hcs : cs = [] := (Option.some.inj h).symm
          rw [hcs]
          intro d hd
          cases hd
        case h_4 => cases h
    case h_2 =>
      rename_i hinone
      split at h
      case isTrue => cases h
      case isFalse =>
        rename_i hno
        have hcs : cs =
            [{ name := Ident.mk "set_in_reif",
               args := [.basic (.lit (.int k)), .basic (.ident S), r],
               anns := anns }] := (Option.some.inj h).symm
        rw [hcs]
        intro d hd
        rw [List.mem_singleton] at hd
        subst hd
        exact (holds_encodeStore_free (by
          intro x hx
          exact hfree x (by simpa [constraintNames] using hx))).mpr hc
  case h_3 =>
    split at h
    case isTrue => cases h
    case isFalse =>
      rename_i hno
      have hcs : cs = [{ name := nm, args := args, anns := anns }] :=
        (Option.some.inj h).symm
      rw [hcs]
      intro d hd
      rw [List.mem_singleton] at hd
      subst hd
      exact (holds_encodeStore_free (by
        intro x hx
        exact hfree x (by simpa [constraintNames] using hx))).mpr hc

/-! ## Blocks of a `mapM` result and name-set facts -/

/-- Each input of a successful `mapM` has an output block in the result. -/
theorem mapM_mem_block {α β : Type} {f : α → Option (List β)}
    {xs : List α} {ys : List (List β)} (h : xs.mapM f = some ys) :
    ∀ a ∈ xs, ∃ l, f a = some l ∧ l ∈ ys := by
  induction xs generalizing ys with
  | nil => intro a ha; cases ha
  | cons x rest ih =>
      intro a ha
      simp only [List.mapM_cons] at h
      cases hx : f x with
      | none => rw [hx] at h; simp at h
      | some l =>
          rw [hx] at h
          cases hr : rest.mapM f with
          | none => rw [hr] at h; simp at h
          | some ls =>
              rw [hr] at h
              have hys : ys = l :: ls := (Option.some.inj h).symm
              subst hys
              rcases List.mem_cons.mp ha with rfl | ha'
              · exact ⟨l, hx, List.mem_cons_self ..⟩
              · obtain ⟨l', hl', hmem⟩ := ih hr a ha'
                exact ⟨l', hl', List.mem_cons_of_mem _ hmem⟩

/-- A block of a flattened `mapM` result contributes each member. -/
theorem mem_flatten_of_block {β : Type} {l : List β} {ls : List (List β)}
    (hl : l ∈ ls) : ∀ b ∈ l, b ∈ ls.flatten := by
  intro b hb
  exact List.mem_flatten.mpr ⟨l, hl, hb⟩

/-- A set-info lookup is `none` exactly for names outside the set table. -/
theorem SetExpansion.infoOf_eq_none_of_not_mem_setNames {se : SetExpansion} {x : Ident}
    (hx : x.name ∉ se.setNames) : se.infoOf x = none := by
  cases h : se.infoOf x with
  | none => rfl
  | some i =>
      exfalso
      have hi : i ∈ se.sets := SetExpansion.mem_sets_of_infoOf h
      have hn : i.name = x.name := SetExpansion.infoOf_name h
      apply hx
      rw [← hn]
      exact List.mem_map.mpr ⟨i, hi, rfl⟩

theorem SetExpansion.setStore_of_not_mem {se : SetExpansion} {s : Store} {x : Ident}
    (hx : x.name ∉ se.setNames) : setStore se s x = s x :=
  SetExpansion.setStore_of_none (SetExpansion.infoOf_eq_none_of_not_mem_setNames hx)

/-- Is-set-name membership. -/
theorem SetExpansion.isSetName_iff {se : SetExpansion} {x : Ident} :
    se.isSetName x = true ↔ x.name ∈ se.setNames := by
  unfold SetExpansion.isSetName SetExpansion.infoOf
  cases hfind : se.sets.find? (fun i => i.name = x.name) with
  | none =>
      constructor
      · intro h; cases h
      · intro hmem
        obtain ⟨i, hi, hname⟩ := List.mem_map.mp hmem
        have hfalse := List.find?_eq_none.mp hfind i hi
        exact absurd hname (by simpa using hfalse)
  | some i =>
      constructor
      · intro _
        have hname : i.name = x.name := by simpa using List.find?_some hfind
        exact List.mem_map.mpr ⟨i, List.mem_of_find?_eq_some hfind, hname⟩
      · intro _
        rfl

theorem basicMentionsSet_true_of_mem {se : SetExpansion} {b : BasicExpr} {x : String}
    (hx : x ∈ basicNames b) (his : se.isSetName (Ident.mk x) = true) :
    basicMentionsSet se b = true := by
  cases b with
  | lit l => simp [basicNames] at hx
  | ident y =>
      simp only [basicNames, List.mem_singleton] at hx
      subst hx
      simpa [basicMentionsSet] using his

theorem exprMentionsSet_true_of_mem {se : SetExpansion} {e : Expr} {x : String}
    (hx : x ∈ exprNames e) (his : se.isSetName (Ident.mk x) = true) :
    exprMentionsSet se e = true := by
  cases e with
  | basic b => exact basicMentionsSet_true_of_mem (by simpa [exprNames] using hx) his
  | array es =>
      simp only [exprNames, List.mem_flatMap] at hx
      obtain ⟨b, hb, hxb⟩ := hx
      exact List.any_eq_true.mpr ⟨b, hb, basicMentionsSet_true_of_mem hxb his⟩

/-- A constraint that does not mention a removed set name mentions no
    removed set name at all. -/
theorem constraintNames_not_set_of_mentions_false {se : SetExpansion}
    {c : ConstraintItem} (h : constraintMentionsSet se c = false) :
    ∀ x ∈ constraintNames c, x ∉ se.setNames := by
  intro x hx hxset
  have his : se.isSetName (Ident.mk x) = true :=
    SetExpansion.isSetName_iff.mpr hxset
  simp only [constraintNames, List.mem_flatMap] at hx
  obtain ⟨e, he, hxe⟩ := hx
  have hany : c.args.any (exprMentionsSet se) = false := by
    simpa [constraintMentionsSet] using h
  have hfalse : ¬ exprMentionsSet se e = true := (List.any_eq_false.mp hany) e he
  exact hfalse (exprMentionsSet_true_of_mem hxe his)

/-! ## Universe facts -/

theorem setUniverse?_base {ty : BasicVarType} {us : List Int}
    (h : setUniverse? ty = some us) : ty.base = .setOfInt := by
  cases ty with
  | par t => simp [setUniverse?] at h
  | intRange lo hi => simp [setUniverse?] at h
  | intSet xs => simp [setUniverse?] at h
  | setOfIntRange lo hi => rfl
  | setOfIntSet xs => rfl

/-- A set all of whose elements lie in the declared universe is admitted
    by the declared set type. -/
theorem setUniverse?_contains {ty : BasicVarType} {us : List Int}
    (h : setUniverse? ty = some us) {sv : IntSetValue}
    (hmem : ∀ v, sv.Contains v → v ∈ us) :
    ty.contains (.setOfInt sv) := by
  cases ty with
  | par t => simp [setUniverse?] at h
  | intRange lo hi => simp [setUniverse?] at h
  | intSet xs => simp [setUniverse?] at h
  | setOfIntRange lo hi =>
      simp only [setUniverse?, Option.some.injEq] at h
      subst h
      intro x hx
      have := hmem x hx
      rwa [mem_setElems_interval'] at this
  | setOfIntSet xs =>
      simp only [setUniverse?, Option.some.injEq] at h
      subst h
      intro x hx
      have := hmem x hx
      rwa [mem_sortElems_enum] at this

/-- A set-typed `contains` forces a set value. -/
theorem setOfInt_of_contains_set {ty : BasicVarType} {v : Value}
    (hb : ty.base = .setOfInt) (h : ty.contains v) : ∃ sv, v = .setOfInt sv := by
  cases ty <;> cases v <;>
    simp_all [BasicVarType.contains, BasicVarType.base, BasicParType.base]
  all_goals (split at h <;> simp_all)

/-- Every element of a rebuilt set is a universe value. -/
theorem SetInfo.rebuilt_contains_mem_values {i : SetInfo} {s : Store} {v : Int}
    (hv : (i.rebuilt s).Contains v) : v ∈ i.values := by
  obtain ⟨p, hp, hpv, _⟩ := SetInfo.mem_rebuilt.mp hv
  rw [SetInfo.values]
  exact List.mem_map.mpr ⟨p, hp, hpv⟩

/-! ## Reconstructed-store invariance for name-free expressions -/

/-- A basic expression whose names are not removed set names evaluates
    the same in the reconstructed store. -/
theorem basicNames_eval_setStore {se : SetExpansion} {s : Store} {b : BasicExpr}
    (h : ∀ x ∈ basicNames b, x ∉ se.setNames) :
    b.eval (setStore se s) = b.eval s := by
  cases b with
  | lit l => rfl
  | ident y =>
      have hy : y.name ∉ se.setNames := h y.name (by simp [basicNames])
      simp only [BasicExpr.eval]
      rw [SetExpansion.setStore_of_not_mem hy]

/-- An expression whose names are not removed set names evaluates the
    same in the reconstructed store. -/
theorem exprNames_eval_setStore {se : SetExpansion} {s : Store} {e : Expr}
    (h : ∀ x ∈ exprNames e, x ∉ se.setNames) :
    e.eval (setStore se s) = e.eval s := by
  cases e with
  | basic b =>
      exact basicNames_eval_setStore (by
        intro x hx
        exact h x (by simpa [exprNames] using hx))
  | array es =>
      show (es.mapM (BasicExpr.eval (setStore se s))).map Value.array =
        (es.mapM (BasicExpr.eval s)).map Value.array
      have hall : ∀ b ∈ es,
          BasicExpr.eval (setStore se s) b = BasicExpr.eval s b := by
        intro b hb
        exact basicNames_eval_setStore (by
          intro x hx
          exact h x (by
            simp only [exprNames, List.mem_flatMap]
            exact ⟨b, hb, hx⟩))
      rw [mapM_congr_set hall]

/-- An initializer whose names are not removed set names has the same
    `initializerHolds` value in the reconstructed store, provided its
    declared name is not removed either. -/
theorem initializerHolds_setStore_iff {se : SetExpansion} {s : Store}
    {d : VarDeclItem} (hn : d.name.name ∉ se.setNames)
    (h : ∀ x ∈ varDeclNames d, x ∉ se.setNames) :
    d.initializerHolds (setStore se s) ↔ d.initializerHolds s := by
  cases d with
  | basic ty n anns init =>
      cases init with
      | none => simp [VarDeclItem.initializerHolds]
      | some e =>
          have he : e.eval (setStore se s) = e.eval s :=
            basicNames_eval_setStore (by
              intro x hx
              exact h x (by simpa [varDeclNames] using hx))
          have hn' : setStore se s n = s n :=
            SetExpansion.setStore_of_not_mem (by simpa [VarDeclItem.name] using hn)
          simp only [VarDeclItem.initializerHolds]
          rw [he, hn']
  | array ty n anns es =>
      have hall : ∀ b ∈ es,
          BasicExpr.eval (setStore se s) b = BasicExpr.eval s b := by
        intro b hb
        exact basicNames_eval_setStore (by
          intro x hx
          exact h x (by
            simp only [varDeclNames, List.mem_flatMap]
            exact ⟨b, hb, hx⟩))
      have hmap : es.mapM (BasicExpr.eval (setStore se s)) =
          es.mapM (BasicExpr.eval s) := by
        rw [mapM_congr_set hall]
      have hn' : setStore se s n = s n :=
        SetExpansion.setStore_of_not_mem (by simpa [VarDeclItem.name] using hn)
      simp only [VarDeclItem.initializerHolds]
      rw [hmap, hn']

/-- An initializer whose names are not fresh Booleans has the same
    `initializerHolds` value in the completeness store, provided its
    declared name is not fresh either. -/
theorem initializerHolds_encodeStore_iff {se : SetExpansion} {s : Store}
    {d : VarDeclItem} (hn : d.name.name ∉ se.boolNames)
    (h : ∀ x ∈ varDeclNames d, x ∉ se.boolNames) :
    d.initializerHolds (encodeStore se s) ↔ d.initializerHolds s := by
  cases d with
  | basic ty n anns init =>
      cases init with
      | none => simp [VarDeclItem.initializerHolds]
      | some e =>
          have he : e.eval (encodeStore se s) = e.eval s :=
            basicNames_eval_encodeStore (by
              intro x hx
              exact h x (by simpa [varDeclNames] using hx))
          have hn' : encodeStore se s n = s n :=
            SetExpansion.encodeStore_of_not_bool (by simpa [VarDeclItem.name] using hn)
          simp only [VarDeclItem.initializerHolds]
          rw [he, hn']
  | array ty n anns es =>
      have hall : ∀ b ∈ es,
          BasicExpr.eval (encodeStore se s) b = BasicExpr.eval s b := by
        intro b hb
        exact basicNames_eval_encodeStore (by
          intro x hx
          exact h x (by
            simp only [varDeclNames, List.mem_flatMap]
            exact ⟨b, hb, hx⟩))
      have hmap : es.mapM (BasicExpr.eval (encodeStore se s)) =
          es.mapM (BasicExpr.eval s) := by
        rw [mapM_congr_set hall]
      have hn' : encodeStore se s n = s n :=
        SetExpansion.encodeStore_of_not_bool (by simpa [VarDeclItem.name] using hn)
      simp only [VarDeclItem.initializerHolds]
      rw [hmap, hn']

/-! ## Inversion-table facts -/

theorem SetExpansion.Inv.universe {m : Model} {se : SetExpansion}
    {taken : List String} (inv : se.Inv taken m) : ∀ i ∈ se.sets, setUniverse? i.ty = some i.values := by
  obtain ⟨n', d⟩ := inv.decls
  intro i hi
  obtain ⟨ty, x, anns, hmem, hname, hty, huniv⟩ := d.info_source i hi
  rw [hty]
  exact huniv

theorem SetExpansion.Inv.vars_not_set {m : Model} {se : SetExpansion}
    {taken : List String} (inv : se.Inv taken m) : ∀ d ∈ se.model.variables, nonSetDecl d := by
  obtain ⟨n', d⟩ := inv.decls
  exact d.vars_not_set

theorem SetExpansion.Inv.fresh_vars {m : Model} {se : SetExpansion}
    {taken : List String} (inv : se.Inv taken m) :
    ∀ i ∈ se.sets, ∀ p ∈ i.bools,
      (.basic (.par .bool) (Ident.mk p.1) [] none : VarDeclItem) ∈
        se.model.variables := by
  obtain ⟨n', d⟩ := inv.decls
  exact d.fresh_vars

/-- A kept declaration is not a removed set variable. -/
theorem SetExpansion.Inv.kept_not_setName {m : Model} {se : SetExpansion}
    {taken : List String} (inv : se.Inv taken m) {d : VarDeclItem} (hd : d ∈ se.model.variables)
    {i : SetInfo} (hi : i ∈ se.sets) : d.name.name ≠ i.name := by
  obtain ⟨n', D⟩ := inv.decls
  intro h
  apply D.names_not_vars i hi
  rw [← h]
  exact List.mem_map.mpr ⟨d, hd, rfl⟩

/-- A kept declaration's name is not a removed set name. -/
theorem SetExpansion.Inv.kept_name_not_set {m : Model} {se : SetExpansion}
    {taken : List String} (inv : se.Inv taken m) {d : VarDeclItem} (hd : d ∈ se.model.variables) :
    d.name.name ∉ se.setNames := by
  intro hmem
  obtain ⟨i, hi, hiname⟩ := List.mem_map.mp hmem
  exact inv.kept_not_setName hd hi hiname.symm

/-- A kept declaration has no set-info entry. -/
theorem SetExpansion.Inv.infoOf_eq_none_of_kept {m : Model} {se : SetExpansion}
    {taken : List String} (inv : se.Inv taken m) {d : VarDeclItem} (hd : d ∈ se.model.variables) :
    se.infoOf d.name = none :=
  SetExpansion.infoOf_eq_none_of_not_mem_setNames (inv.kept_name_not_set hd)

/-- Name-level duplicate-freeness implies identifier-level
    duplicate-freeness. -/
theorem nodup_ident_of_nodup_name {l : List VarDeclItem} :
    (l.map (fun d => d.name.name)).Nodup → (l.map (fun d => d.name)).Nodup := by
  induction l with
  | nil => simp
  | cons d ds ih =>
      intro h
      rw [List.map_cons] at h
      rw [List.map_cons]
      rw [List.nodup_cons] at h ⊢
      refine ⟨?_, ih h.2⟩
      intro hmem
      obtain ⟨e, he, hen⟩ := List.mem_map.mp hmem
      exact h.1 (List.mem_map.mpr ⟨e, he, congrArg Ident.name hen⟩)

/-- A basic expression of base type `t` mentions only identifiers whose
    static entry has base type `t`. -/
theorem hasBaseType_staticEnv {env : StaticEnv} {b : BasicExpr} {t : BaseType}
    (h : b.hasBaseType env t) :
    ∀ x ∈ basicNames b, ∃ isVar, env (Ident.mk x) = some (.base t, isVar) := by
  cases b with
  | lit l =>
      intro x hx
      simp [basicNames] at hx
  | ident y =>
      intro x hx
      simp only [basicNames, List.mem_singleton] at hx
      subst hx
      dsimp only [BasicExpr.hasBaseType] at h
      cases hv : env y with
      | none => rw [hv] at h; exact h.elim
      | some info =>
          rw [hv] at h
          obtain ⟨ft, isVar⟩ := info
          cases ft with
          | base t' =>
              dsimp only at h
              subst t'
              exact ⟨isVar, by simpa using hv⟩
          | array n t' => simp at h

/-- `hasBaseType` is invariant under pointwise-equal static environments
    on the expression's names. -/
theorem hasBaseType_staticEnv_eq {env env' : StaticEnv} {b : BasicExpr}
    {t : BaseType} (h : b.hasBaseType env t)
    (hx : ∀ x ∈ basicNames b, env' (Ident.mk x) = env (Ident.mk x)) :
    b.hasBaseType env' t := by
  cases b with
  | lit l => exact h
  | ident y =>
      have hy : env' y = env y := by
        simpa [basicNames] using hx y.name (by simp [basicNames])
      dsimp only [BasicExpr.hasBaseType] at h ⊢
      rw [hy]
      exact h

/-- `checkBase` is invariant under pointwise-equal static environments on
    the expression's names. -/
theorem checkBase_staticEnv_eq {env env' : StaticEnv} {b : BasicExpr}
    {bt : BasicPredParamType} (h : b.checkBase env bt)
    (hx : ∀ x ∈ basicNames b, env' (Ident.mk x) = env (Ident.mk x)) :
    b.checkBase env' bt := by
  cases b with
  | lit l => exact h
  | ident y =>
      have hy : env' y = env y := by
        simpa [basicNames] using hx y.name (by simp [basicNames])
      dsimp only [BasicExpr.checkBase] at h ⊢
      rw [hy]
      exact h

/-- `checkArg` is invariant under pointwise-equal static environments on
    the expression's names. -/
theorem checkArg_staticEnv_eq {env env' : StaticEnv} {e : Expr}
    {pt : PredParamType} (h : e.checkArg env pt)
    (hx : ∀ x ∈ exprNames e, env' (Ident.mk x) = env (Ident.mk x)) :
    e.checkArg env' pt := by
  cases pt with
  | basic bt =>
      cases e with
      | basic b =>
          exact checkBase_staticEnv_eq h (by
            intro x hxx
            exact hx x (by simpa [exprNames] using hxx))
      | array es => exact h
  | array idx bt =>
      cases e with
      | basic b =>
          cases b with
          | lit l => exact h
          | ident y =>
              have hy : env' y = env y := by
                simpa [exprNames, basicNames] using
                  hx y.name (by simp [exprNames, basicNames])
              dsimp only [Expr.checkArg] at h ⊢
              rw [hy]
              exact h
      | array es =>
          obtain ⟨hlen, hall⟩ := h
          refine ⟨hlen, ?_⟩
          intro b hb
          exact checkBase_staticEnv_eq (hall b hb) (by
            intro x hxx
            exact hx x (by
              simp only [exprNames, List.mem_flatMap]
              exact ⟨b, hb, hxx⟩))

/-- A removed set variable has the declared set base type in the static
    environment of the source model. -/
theorem SetExpansion.Inv.setName_staticEnv {m : Model} {se : SetExpansion}
    {taken : List String} (inv : se.Inv taken m) (hwf : WellFormed fullSig m) {i : SetInfo} (hi : i ∈ se.sets) :
    m.staticEnv (Ident.mk i.name) = some (.base i.ty.base, true) := by
  obtain ⟨n', d⟩ := inv.decls
  obtain ⟨ty, x, anns, hmem, hname, hty, huniv⟩ := d.info_source i hi
  have hx : x = Ident.mk i.name := ident_eq_of_name hname.symm
  subst hx
  have hs := staticEnv_var_of_mem hwf hmem
  simpa [VarDeclItem.name, VarDeclItem.type, hty] using hs

/-- A basic expression whose declared base type is not a set type cannot
    mention a removed set variable. -/
theorem SetExpansion.Inv.basicNames_not_set {m : Model} {se : SetExpansion}
    {taken : List String} (inv : se.Inv taken m) (hwf : WellFormed fullSig m)
    {b : BasicExpr} {t : BaseType}
    (hb : b.hasBaseType m.staticEnv t) (ht : t ≠ .setOfInt) :
    ∀ x ∈ basicNames b, x ∉ se.setNames := by
  intro x hx hxset
  obtain ⟨i, hi, hiname⟩ := List.mem_map.mp hxset
  obtain ⟨isVar, hstat⟩ := hasBaseType_staticEnv hb x hx
  have hset := SetExpansion.Inv.setName_staticEnv inv hwf hi
  have hchain : some (FznType.base t, isVar) =
      some (FznType.base i.ty.base, true) := by
    rw [← hstat]
    rw [← hiname]
    exact hset
  have hfty : (FznType.base t) = FznType.base i.ty.base :=
    congrArg Prod.fst (Option.some.inj hchain)
  have hft : t = i.ty.base := by
    cases hfty
    rfl
  exact ht (hft.trans (setUniverse?_base (inv.universe i hi)))

/-- The initializer names of a kept source declaration are not removed set
    names. -/
theorem SetExpansion.Inv.init_names_not_set {m : Model} {se : SetExpansion}
    {taken : List String} (inv : se.Inv taken m) (hwf : WellFormed fullSig m)
    {d : VarDeclItem} (hdm : d ∈ m.variables) (hdv : d ∈ se.model.variables) :
    ∀ x ∈ varDeclNames d, x ∉ se.setNames := by
  obtain ⟨n', D⟩ := inv.decls
  have hns : nonSetDecl d := D.vars_not_set d hdv
  cases d with
  | basic ty n anns init =>
      cases init with
      | none => intro x hx; simp [varDeclNames] at hx
      | some e =>
          intro x hx
          exact inv.basicNames_not_set hwf (hwf.variableInitializers _ hdm)
            (by simpa [nonSetDecl, declBase] using hns)
            x (by simpa [varDeclNames] using hx)
  | array ty n anns es =>
      intro x hx
      simp only [varDeclNames, List.mem_flatMap] at hx
      obtain ⟨b, hb, hxb⟩ := hx
      exact inv.basicNames_not_set hwf (hwf.variableInitializers _ hdm b hb)
        (by simpa [nonSetDecl, declBase] using hns) x hxb

/-- The static environments of the source and expanded models agree on
    every declared source name that is not a removed set variable. -/
theorem SetExpansion.Inv.staticEnv_eq {m : Model} {se : SetExpansion}
    {taken : List String} (inv : se.Inv taken m) (hwf : WellFormed fullSig m) {x : Ident}
    (htaken : x.name ∈ setTaken m) (hnot : x.name ∉ se.setNames) :
    se.model.staticEnv x = m.staticEnv x := by
  obtain ⟨n', D⟩ := inv.decls
  have hnuVar : ((se.model.variables.map (fun d => (d.name, (d.type, true)))).map
      Prod.fst).Nodup := by
    rw [show ((se.model.variables.map (fun d => (d.name, (d.type, true)))).map Prod.fst) =
        se.model.variables.map (fun d => d.name) from by simp [List.map_map]]
    exact nodup_ident_of_nodup_name D.vars_nodup
  have hnuM : ((m.variables.map (fun d => (d.name, (d.type, true)))).map
      Prod.fst).Nodup := by
    rw [show ((m.variables.map (fun d => (d.name, (d.type, true)))).map Prod.fst) =
        m.variables.map (fun d => d.name) from by simp [List.map_map]]
    exact (List.nodup_append.mp hwf.valueNamesUnique).2.1
  have hleft : ∀ {info : FznType × Bool},
      lookupIdent x (se.model.variables.map (fun d => (d.name, (d.type, true)))) =
        some info →
      lookupIdent x (m.variables.map (fun d => (d.name, (d.type, true)))) =
        some info := by
    intro info hlk
    obtain ⟨y, hy, hyn⟩ := lookupIdent_inv_mem x _ info hlk
    obtain ⟨d, hd, hde⟩ := List.mem_map.mp hy
    have hdn : d.name.name = x.name := by
      have h1 : d.name = y := (Prod.mk.injEq ..).mp hde |>.1
      rw [h1]
      exact hyn
    have hinfo : info = (d.type, true) := by
      exact ((Prod.mk.injEq ..).mp hde |>.2).symm
    rcases D.expanded d hd with hsrc | ⟨i, hi, p, hp, hdeq⟩
    · have hmem : (d.name, (d.type, true)) ∈
          m.variables.map (fun d => (d.name, (d.type, true))) :=
        List.mem_map.mpr ⟨d, hsrc, rfl⟩
      have hlook := lookupIdent_of_mem hnuM hmem
      rw [ident_eq_of_name hdn] at hlook
      rw [hlook, hinfo]
    · have hpd : p.1 = d.name.name := by
        rw [hdeq]
        simp [VarDeclItem.name]
      have hfresh := D.fresh i hi p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)
      exact absurd (by rw [hpd, hdn]; exact inv.superset _ htaken) hfresh
  have hright : ∀ {info : FznType × Bool},
      lookupIdent x (m.variables.map (fun d => (d.name, (d.type, true)))) =
        some info →
      lookupIdent x (se.model.variables.map (fun d => (d.name, (d.type, true)))) =
        some info := by
    intro info hlk
    obtain ⟨y, hy, hyn⟩ := lookupIdent_inv_mem x _ info hlk
    obtain ⟨d, hd, hde⟩ := List.mem_map.mp hy
    have hdn : d.name.name = x.name := by
      have h1 : d.name = y := (Prod.mk.injEq ..).mp hde |>.1
      rw [h1]
      exact hyn
    have hinfo : info = (d.type, true) := by
      exact ((Prod.mk.injEq ..).mp hde |>.2).symm
    rcases D.source d hd with hsrc | ⟨i, hi, ty, anns, heq, hty, huniv⟩
    · have hmem : (d.name, (d.type, true)) ∈
          se.model.variables.map (fun d => (d.name, (d.type, true))) :=
        List.mem_map.mpr ⟨d, hsrc, rfl⟩
      have hlook := lookupIdent_of_mem hnuVar hmem
      rw [ident_eq_of_name hdn] at hlook
      rw [hlook, hinfo]
    · have hdname : d.name.name = i.name := by
        rw [heq]
        simp [VarDeclItem.name]
      have hix : i.name = x.name := hdname.symm.trans hdn
      apply absurd ?_ hnot
      rw [← hix]
      exact List.mem_map.mpr ⟨i, hi, rfl⟩
  unfold Model.staticEnv
  rw [inv.parameters]
  cases hp : lookupIdent x (m.parameters.map (fun d => (d.name, (d.type, false)))) with
  | some info => rfl
  | none =>
      show lookupIdent x (se.model.variables.map (fun d => (d.name, (d.type, true)))) =
        lookupIdent x (m.variables.map (fun d => (d.name, (d.type, true))))
      cases hr : lookupIdent x (m.variables.map (fun d => (d.name, (d.type, true)))) with
      | none =>
          cases hl : lookupIdent x (se.model.variables.map
              (fun d => (d.name, (d.type, true)))) with
          | none => rfl
          | some info => exact absurd (hleft hl) (by rw [hr]; simp)
      | some info => exact hright hr

/-- A fresh Boolean name has Boolean variable type in the expanded static
    environment. -/
theorem SetExpansion.Inv.fresh_staticEnv {m : Model} {se : SetExpansion}
    {taken : List String} (inv : se.Inv taken m) {i : SetInfo} (hi : i ∈ se.sets) {p : String × Int}
    (hp : p ∈ i.bools) :
    se.model.staticEnv (Ident.mk p.1) = some (.base .bool, true) := by
  obtain ⟨n', D⟩ := inv.decls
  have hfresh : p.1 ∉ taken :=
    D.fresh i hi p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)
  have hdecl : (.basic (.par .bool) (Ident.mk p.1) [] none : VarDeclItem) ∈
      se.model.variables := D.fresh_vars i hi p hp
  have hnuVar : ((se.model.variables.map (fun d => (d.name, (d.type, true)))).map
      Prod.fst).Nodup := by
    rw [show ((se.model.variables.map (fun d => (d.name, (d.type, true)))).map Prod.fst) =
        se.model.variables.map (fun d => d.name) from by simp [List.map_map]]
    exact nodup_ident_of_nodup_name D.vars_nodup
  have hlookVar : lookupIdent (Ident.mk p.1)
      (se.model.variables.map (fun d => (d.name, (d.type, true)))) =
        some ((.base .bool : FznType), true) := by
    have := lookupIdent_of_mem hnuVar
      (List.mem_map.mpr ⟨_, hdecl, rfl⟩)
    simpa [VarDeclItem.name, VarDeclItem.type, BasicVarType.base,
      BasicParType.base] using this
  have hlookPar : lookupIdent (Ident.mk p.1)
      (se.model.parameters.map (fun d => (d.name, (d.type, false)))) = none := by
    apply lookupIdent_none_of_forall
    intro q hq hqn
    rw [inv.parameters] at hq
    obtain ⟨d, hd, hde⟩ := List.mem_map.mp hq
    have hpn : d.name.name = p.1 := by
      have h1 : q.1 = d.name := (congrArg Prod.fst hde).symm
      rw [h1] at hqn
      exact hqn
    exact hfresh (by
      rw [← hpn]
      exact inv.superset _
        (List.mem_append_left _ (List.mem_map.mpr ⟨d, hd, rfl⟩)))
  unfold Model.staticEnv
  rw [hlookPar]
  exact hlookVar

/-! ## Model-level correctness -/

/-- Identifier-level duplicate-freeness implies name-level
    duplicate-freeness. -/
theorem nodup_name_of_nodup_ident {l : List VarDeclItem} :
    (l.map (fun d => d.name)).Nodup → (l.map (fun d => d.name.name)).Nodup := by
  induction l with
  | nil => simp
  | cons d ds ih =>
      intro h
      rw [List.map_cons] at h
      rw [List.map_cons]
      rw [List.nodup_cons] at h ⊢
      refine ⟨?_, ih h.2⟩
      intro hmem
      obtain ⟨e, he, hen⟩ := List.mem_map.mp hmem
      exact h.1 (List.mem_map.mpr ⟨e, he, ident_eq_of_name hen⟩)

/-- The expansion invariant, derived from static well-formedness and the
    fact that the taken list contains every declared name. -/
theorem SetExpansion.Inv.of_wellFormed {taken : List String} {m : Model}
    {se : SetExpansion}
    (hwf : WellFormed fullSig m) (hsup : ∀ x ∈ setTaken m, x ∈ taken)
    (h : setExpandModelWith taken m = some se) :
    se.Inv taken m :=
  setExpandModel_inv
    (nodup_name_of_nodup_ident
      (List.nodup_append.mp hwf.valueNamesUnique).2.1)
    (by
      intro d hd
      exact hsup d.name.name (List.mem_append_right _
        (List.mem_map.mpr ⟨d, hd, rfl⟩)))
    hsup h

/-- Fresh Boolean names avoid every taken name. -/
theorem DeclExpansion.boolNames_not_mem_taken {taken : List String}
    {ds : List VarDeclItem} {n n' : Nat} {infos : List SetInfo}
    {vars : List VarDeclItem} (D : DeclExpansion taken ds n infos n' vars) :
    ∀ x ∈ infos.flatMap (fun i => i.bools.map Prod.fst), x ∉ taken := by
  intro x hx
  simp only [List.mem_flatMap] at hx
  obtain ⟨i, hi, hxi⟩ := hx
  exact D.fresh i hi x hxi

theorem SetExpansion.Inv.constraintNames_not_bool {m : Model} {se : SetExpansion}
    {taken : List String} (inv : se.Inv taken m) (hwf : WellFormed fullSig m) {c : ConstraintItem}
    (hc : c ∈ m.constraints) :
    ∀ x ∈ constraintNames c, x ∉ se.boolNames := by
  obtain ⟨n', D⟩ := inv.decls
  intro x hx hxb
  exact D.boolNames_not_mem_taken x (by simpa [SetExpansion.boolNames] using hxb)
    (inv.superset x (wf_constraint_names_taken hwf c hc x hx))

theorem SetExpansion.Inv.varDeclNames_not_bool {m : Model} {se : SetExpansion}
    {taken : List String} (inv : se.Inv taken m) (hwf : WellFormed fullSig m) {d : VarDeclItem}
    (hd : d ∈ m.variables) :
    ∀ x ∈ varDeclNames d, x ∉ se.boolNames := by
  obtain ⟨n', D⟩ := inv.decls
  intro x hx hxb
  exact D.boolNames_not_mem_taken x (by simpa [SetExpansion.boolNames] using hxb)
    (inv.superset x (wf_init_names_taken hwf d hd x hx))

/-- A declared source name is not a fresh Boolean name. -/
theorem SetExpansion.Inv.varName_not_bool {m : Model} {se : SetExpansion}
    {taken : List String} (inv : se.Inv taken m) {d : VarDeclItem} (hd : d ∈ m.variables) :
    d.name.name ∉ se.boolNames := by
  obtain ⟨n', D⟩ := inv.decls
  intro hxb
  exact D.boolNames_not_mem_taken d.name.name
    (by simpa [SetExpansion.boolNames] using hxb)
    (inv.superset _ (List.mem_append_right _
      (List.mem_map.mpr ⟨d, hd, rfl⟩)))

/-- **Soundness of the set expansion**: a store of the expanded model
    reconstructs a store of the source model through `setStore`. -/
theorem setExpand_sound {taken : List String} {m : Model} {se : SetExpansion}
    {s : Store}
    (hwf : WellFormed fullSig m) (hsup : ∀ x ∈ setTaken m, x ∈ taken)
    (h : setExpandModelWith taken m = some se)
    (hs : SatisfiesDyn fullInterp se.model s) :
    SatisfiesDyn fullInterp m (setStore se s) := by
  have inv := SetExpansion.Inv.of_wellFormed hwf hsup h
  obtain ⟨n', D⟩ := inv.decls
  obtain ⟨css, hmap, hcons⟩ := inv.constraints
  obtain ⟨hconsSat, hdomSat, hinitSat⟩ := hs
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨cs, hcs, hcsMem⟩ := mapM_mem_block hmap c hc
    exact rewriteConstraint_sound inv.values_nodup hcs (by
      intro d hd
      exact hconsSat d (by
        rw [hcons]
        exact mem_flatten_of_block hcsMem d hd))
  · intro d hd
    rcases D.source d hd with hkept | ⟨i, hi, ty, anns, heq, hty, huniv⟩
    · cases d with
      | basic ty n anns init =>
          obtain ⟨v, hv, hcont⟩ := hdomSat (.basic ty n anns init) hkept
          exact ⟨v, by
            rw [SetExpansion.setStore_of_not_mem (by
              simpa [VarDeclItem.name] using inv.kept_name_not_set hkept)]
            exact hv, hcont⟩
      | array ty n anns es =>
          obtain ⟨vs, hv, hlen, hcont⟩ := hdomSat (.array ty n anns es) hkept
          exact ⟨vs, by
            rw [SetExpansion.setStore_of_not_mem (by
              simpa [VarDeclItem.name] using inv.kept_name_not_set hkept)]
            exact hv, hlen, hcont⟩
    · subst heq
      refine ⟨.setOfInt (i.rebuilt s), ?_, ?_⟩
      · simpa [VarDeclItem.name] using
          SetExpansion.setStore_setName inv.setNames_nodup hi s
      · exact setUniverse?_contains (ty := ty) (us := i.values) huniv
          (fun v hv => SetInfo.rebuilt_contains_mem_values hv)
  · intro d hd
    rcases D.source d hd with hkept | ⟨i, hi, ty, anns, heq, hty, huniv⟩
    · exact (initializerHolds_setStore_iff (inv.kept_name_not_set hkept)
        (inv.init_names_not_set hwf hd hkept)).mpr (hinitSat d hkept)
    · subst heq
      simp [VarDeclItem.initializerHolds]

/-- **Completeness of the set expansion**: every source store extends to
    the store `encodeStore`, which reads every fresh Boolean as the source
    set value's membership at its universe value. -/
theorem setExpand_complete {taken : List String} {m : Model} {se : SetExpansion}
    {s : Store}
    (hwf : WellFormed fullSig m) (hsup : ∀ x ∈ setTaken m, x ∈ taken)
    (h : setExpandModelWith taken m = some se)
    (hs : SatisfiesDyn fullInterp m s) :
    SatisfiesDyn fullInterp se.model (encodeStore se s) ∧
      (∀ i ∈ se.sets, ∀ p ∈ i.bools,
        encodeStore se s (Ident.mk p.1) = some (.bool (i.sourceContainsB s p.2))) := by
  have inv := SetExpansion.Inv.of_wellFormed hwf hsup h
  obtain ⟨n', D⟩ := inv.decls
  obtain ⟨css, hmap, hcons⟩ := inv.constraints
  obtain ⟨hconsSat, hdomSat, hinitSat⟩ := hs
  have hnames := inv.boolNames_nodup
  have huni := inv.universe
  have hdom : ∀ i ∈ se.sets, ∀ sv,
      s (Ident.mk i.name) = some (.setOfInt sv) →
        i.ty.contains (.setOfInt sv) := by
    intro i hi sv hsv
    obtain ⟨ty, x, anns, hmem, hname, hty, huniv⟩ := D.info_source i hi
    obtain ⟨v, hv, hcont⟩ := hdomSat (.basic ty x anns none) hmem
    have hv' : s x = some v := by simpa [VarDeclItem.name] using hv
    have hxy : x = Ident.mk i.name := ident_eq_of_name hname.symm
    rw [hxy] at hv'
    have hveq : v = .setOfInt sv :=
      Option.some.inj (hv'.symm.trans hsv)
    subst hveq
    rwa [hty]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro c' hc'
    rw [hcons] at hc'
    obtain ⟨c, hc, cs, hcs, hc'cs⟩ := mem_flatten_of_mapM_some hmap c' hc'
    exact rewriteConstraint_complete hnames huni hdom
      (inv.constraintNames_not_bool hwf hc) hcs (hconsSat c hc) c' hc'cs
  · intro d hd
    rcases D.expanded d hd with hsrc | ⟨i, hi, p, hp, heq⟩
    · cases d with
      | basic ty n anns init =>
          obtain ⟨v, hv, hcont⟩ := hdomSat (.basic ty n anns init) hsrc
          exact ⟨v, by
            rw [SetExpansion.encodeStore_of_not_bool (by
              simpa [VarDeclItem.name] using inv.varName_not_bool hsrc)]
            exact hv, hcont⟩
      | array ty n anns es =>
          obtain ⟨vs, hv, hlen, hcont⟩ := hdomSat (.array ty n anns es) hsrc
          exact ⟨vs, by
            rw [SetExpansion.encodeStore_of_not_bool (by
              simpa [VarDeclItem.name] using inv.varName_not_bool hsrc)]
            exact hv, hlen, hcont⟩
    · subst heq
      refine ⟨.bool (i.sourceContainsB s p.2), ?_, trivial⟩
      simpa [VarDeclItem.name] using
        SetExpansion.encodeStore_bool hnames (inv.bools_nodup i hi) hi hp
  · intro d hd
    rcases D.expanded d hd with hsrc | ⟨i, hi, p, hp, heq⟩
    · exact (initializerHolds_encodeStore_iff (inv.varName_not_bool hsrc)
        (inv.varDeclNames_not_bool hwf hsrc)).mpr (hinitSat d hsrc)
    · subst heq
      simp [VarDeclItem.initializerHolds]
  · intro i hi p hp
    exact SetExpansion.encodeStore_bool hnames (inv.bools_nodup i hi) hi hp

/-! ## Well-formedness preservation -/

/-- A model without predicate items has the external signature
    environment as its signature environment. -/
theorem Model.sigEnv_eq_of_predicates_nil {m : Model} (hpred : m.predicates = []) :
    m.sigEnv fullSig = fullSig := by
  funext x
  simp [Model.sigEnv, Model.declaredSigs, lookupIdent, hpred]

/-- The standard `bool_not` signature. -/
theorem fullSig_bool_not :
    fullSig (Ident.mk "bool_not") =
      some [.basic (.var (.par .bool)), .basic (.var (.par .bool))] := by
  simp [fullSig, globalsSig, stdSig]

/-- The standard `bool_eq` signature. -/
theorem fullSig_bool_eq :
    fullSig (Ident.mk "bool_eq") =
      some [.basic (.var (.par .bool)), .basic (.var (.par .bool))] := by
  simp [fullSig, globalsSig, stdSig]

/-- The standard `int_lin_le` signature. -/
theorem fullSig_int_lin_le :
    fullSig (Ident.mk "int_lin_le") =
      some [.array .int (.par .int), .array .int (.var (.par .int)),
        .basic (.var (.par .int))] :=
  falseConstraint_sig

/-- A name in the set table is a set name. -/
theorem SetExpansion.isSetName_eq_true_of_mem {se : SetExpansion} {x : Ident}
    (h : x.name ∈ se.setNames) : se.isSetName x = true := by
  unfold SetExpansion.setNames at h
  obtain ⟨i, hi, hin⟩ := List.mem_map.mp h
  unfold SetExpansion.isSetName SetExpansion.infoOf
  rw [List.find?_isSome]
  exact ⟨i, hi, by simp [hin]⟩

/-- A name with no set-info entry is not a removed set name. -/
theorem SetExpansion.not_mem_setNames_of_infoOf_eq_none {se : SetExpansion}
    (_hnd : se.setNames.Nodup) {x : Ident} (h : se.infoOf x = none) :
    x.name ∉ se.setNames := by
  intro hmem
  have his := SetExpansion.isSetName_eq_true_of_mem (x := x) hmem
  unfold SetExpansion.isSetName at his
  rw [h] at his
  cases his

/-- A basic expression that does not mention a removed set name has no
    removed set name among its names. -/
theorem basicMentionsSet_eq_false {se : SetExpansion} {b : BasicExpr}
    (h : basicMentionsSet se b = false) {x : String} (hx : x ∈ basicNames b) :
    x ∉ se.setNames := by
  cases b with
  | lit l => simp [basicNames] at hx
  | ident y =>
      simp only [basicNames, List.mem_singleton] at hx
      subst hx
      intro hmem
      have his := SetExpansion.isSetName_eq_true_of_mem (x := y) hmem
      have h' : se.isSetName y = false := by simpa [basicMentionsSet] using h
      rw [his] at h'
      cases h'

/-- An expression that does not mention a removed set name has no
    removed set name among its names. -/
theorem exprMentionsSet_eq_false {se : SetExpansion} {e : Expr}
    (h : exprMentionsSet se e = false) {x : String} (hx : x ∈ exprNames e) :
    x ∉ se.setNames := by
  cases e with
  | basic b =>
      exact basicMentionsSet_eq_false (by simpa [exprMentionsSet] using h)
        (by simpa [exprNames] using hx)
  | array es =>
      simp only [exprNames, List.mem_flatMap] at hx
      obtain ⟨b, hb, hxb⟩ := hx
      have hbf : basicMentionsSet se b = false := by
        have := (List.any_eq_false.mp (by simpa [exprMentionsSet] using h)) b hb
        simpa using this
      exact basicMentionsSet_eq_false hbf hxb

/-- A constraint that does not mention a removed set name has no
    removed set name among its names. -/
theorem constraintMentionsSet_eq_false {se : SetExpansion} {c : ConstraintItem}
    (h : constraintMentionsSet se c = false) {x : String}
    (hx : x ∈ constraintNames c) : x ∉ se.setNames := by
  simp only [constraintNames, List.mem_flatMap] at hx
  obtain ⟨e, he, hxe⟩ := hx
  have hef : exprMentionsSet se e = false := by
    have := (List.any_eq_false.mp (by simpa [constraintMentionsSet] using h)) e he
    simpa using this
  exact exprMentionsSet_eq_false hef hxe

/-- The signature check for a Boolean pin. -/
theorem pinBool_check {env : StaticEnv} {b : String} {v : Bool}
    (hb : ∃ isVar, env (Ident.mk b) = some (.base .bool, isVar)) :
    Forall2 (Expr.checkArg env) (pinBoolConstraint b v).args
      [.basic (.var (.par .bool)), .basic (.var (.par .bool))] := by
  obtain ⟨isVar, hb⟩ := hb
  simp [pinBoolConstraint, Forall2, Expr.checkArg, BasicExpr.checkBase,
    hb, BasicPredParamType.accepts, BasicPredParamType.isPar,
    BasicPredParamType.baseType,
    BasicLiteral.type, BasicParType.base, BasicVarType.base]

/-- The signature check for a Boolean equality. -/
theorem boolEq_check {env : StaticEnv} {b r : String}
    (hb : ∃ isVar, env (Ident.mk b) = some (.base .bool, isVar))
    (hr : ∃ isVar, env (Ident.mk r) = some (.base .bool, isVar)) :
    Forall2 (Expr.checkArg env) (boolEqConstraint b r).args
      [.basic (.var (.par .bool)), .basic (.var (.par .bool))] := by
  obtain ⟨isVar, hb⟩ := hb
  obtain ⟨isVar', hr⟩ := hr
  simp [boolEqConstraint, Forall2, Expr.checkArg, BasicExpr.checkBase,
    hb, hr, BasicPredParamType.accepts, BasicPredParamType.isPar,
    BasicPredParamType.baseType,
    BasicLiteral.type, BasicParType.base, BasicVarType.base]

/-- `Forall2 checkArg` is invariant under pointwise-equal static
    environments on the argument names. -/
theorem forall2_checkArg_staticEnv_eq {env env' : StaticEnv} :
    ∀ {args : List Expr} {params : List PredParamType},
      Forall2 (Expr.checkArg env) args params →
      (∀ e ∈ args, ∀ x ∈ exprNames e, env' (Ident.mk x) = env (Ident.mk x)) →
      Forall2 (Expr.checkArg env') args params := by
  intro args
  induction args with
  | nil =>
      intro params h _
      cases params with
      | nil => exact trivial
      | cons p ps => exact h.elim
  | cons e es ih =>
      intro params h hx
      cases params with
      | nil => exact h.elim
      | cons p ps =>
          obtain ⟨h1, h2⟩ := h
          exact ⟨checkArg_staticEnv_eq h1 (hx e List.mem_cons_self),
            ih h2 (fun e' he' x hxx =>
              hx e' (List.mem_cons_of_mem _ he') x hxx)⟩

/-! ## Static well-formedness of the rewrite -/

/-- The third component of a checked three-argument constraint. -/
theorem checkArg_third {env : StaticEnv} {a b c : Expr}
    {x y z : PredParamType}
    (h : Forall2 (Expr.checkArg env) [a, b, c] [x, y, z]) :
    Expr.checkArg env c z := by
  have h' := h
  simp only [Forall2, and_true] at h'
  exact h'.2.2

/-- **Static well-formedness of the per-constraint rewrite**: every row
    produced by `rewriteConstraint` is a signature-checked standard
    constraint in the expanded static environment. -/
theorem rewriteConstraint_wf {m : Model} {se : SetExpansion}
    {taken : List String} (inv : se.Inv taken m) (hwf : WellFormed fullSig m) (hpred : m.predicates = [])
    {c : ConstraintItem} (hc : c ∈ m.constraints) {cs : List ConstraintItem}
    (h : rewriteConstraint se c = some cs) :
    ∀ c' ∈ cs, ∃ params,
      se.model.sigEnv fullSig c'.name = some params ∧
      Forall2 (Expr.checkArg se.model.staticEnv) c'.args params := by
  have hpredse : se.model.predicates = [] := by rw [inv.predicates, hpred]
  have hsig : se.model.sigEnv fullSig = fullSig :=
    Model.sigEnv_eq_of_predicates_nil hpredse
  have hsig_src : m.sigEnv fullSig = fullSig :=
    Model.sigEnv_eq_of_predicates_nil hpred
  have kept : ∀ {c0 : ConstraintItem}, c0 ∈ m.constraints →
      constraintMentionsSet se c0 = false →
      ∀ c' ∈ [c0], ∃ params,
        se.model.sigEnv fullSig c'.name = some params ∧
        Forall2 (Expr.checkArg se.model.staticEnv) c'.args params := by
    intro c0 hc0 hfree c' hc'
    rw [List.mem_singleton] at hc'
    subst c'
    obtain ⟨params, hsigc, hF⟩ := hwf.constraintsChecked c0 hc0
    refine ⟨params, ?_, ?_⟩
    · rw [hsig, ← hsig_src]
      exact hsigc
    · apply forall2_checkArg_staticEnv_eq hF
      intro e he x hx
      have hcx : x ∈ constraintNames c0 := by
        simp only [constraintNames, List.mem_flatMap]
        exact ⟨e, he, hx⟩
      exact inv.staticEnv_eq hwf (wf_constraint_names_taken hwf c0 hc0 x hcx)
        (constraintMentionsSet_eq_false hfree hcx)
  rcases c with ⟨nm, args, anns⟩
  unfold rewriteConstraint at h
  split at h
  case h_1 =>
    rename_i k S hname hargs
    dsimp only at hname hargs
    have hnm : nm = Ident.mk "set_in" := ident_eq_of_name hname
    subst hnm
    subst hargs
    split at h
    case h_1 =>
      rename_i i hinfo
      split at h
      case h_1 =>
        rename_i b hb
        have hcs : cs = [pinBoolConstraint b true] := (Option.some.inj h).symm
        rw [hcs]
        intro c' hc'
        rw [List.mem_singleton] at hc'
        subst hc'
        obtain ⟨p, hp, hpb, hpv⟩ := SetInfo.boolAt_some hb
        have hi : i ∈ se.sets := SetExpansion.mem_sets_of_infoOf hinfo
        have hbstat : se.model.staticEnv (Ident.mk b) =
            some (.base .bool, true) := by
          rw [← hpb]
          exact inv.fresh_staticEnv hi hp
        exact ⟨[.basic (.var (.par .bool)), .basic (.var (.par .bool))],
          by rw [hsig]; exact fullSig_bool_not,
          pinBool_check ⟨true, hbstat⟩⟩
      case h_2 =>
        rename_i hbnone
        have hcs : cs = [falseConstraint] := (Option.some.inj h).symm
        rw [hcs]
        intro c' hc'
        rw [List.mem_singleton] at hc'
        subst hc'
        exact ⟨[.array .int (.par .int), .array .int (.var (.par .int)),
          .basic (.var (.par .int))],
          by rw [hsig]; exact fullSig_int_lin_le,
          falseConstraint_check _⟩
    case h_2 =>
      rename_i hinone
      split at h
      case isTrue => cases h
      case isFalse =>
        rename_i hno
        have hcs : cs =
            [{ name := Ident.mk "set_in",
               args := [.basic (.lit (.int k)), .basic (.ident S)],
               anns := anns }] := (Option.some.inj h).symm
        rw [hcs]
        exact kept hc (by simpa using hno)
  case h_2 =>
    rename_i k S r hname hargs
    dsimp only at hname hargs
    have hnm : nm = Ident.mk "set_in_reif" := ident_eq_of_name hname
    subst hnm
    subst hargs
    split at h
    case h_1 =>
      rename_i i hinfo
      split at h
      case h_1 =>
        rename_i b hb
        split at h
        case h_1 =>
          rename_i z hz
          split at h
          case isTrue => cases h
          case isFalse =>
            rename_i hznot
            have hcs : cs = [boolEqConstraint b hz.name] :=
              (Option.some.inj h).symm
            rw [hcs]
            intro c' hc'
            rw [List.mem_singleton] at hc'
            subst hc'
            obtain ⟨p, hp, hpb, hpv⟩ := SetInfo.boolAt_some hb
            have hi : i ∈ se.sets := SetExpansion.mem_sets_of_infoOf hinfo
            have hbstat : se.model.staticEnv (Ident.mk b) =
                some (.base .bool, true) := by
              rw [← hpb]
              exact inv.fresh_staticEnv hi hp
            obtain ⟨params, hsigc, hF⟩ := hwf.constraintsChecked _ hc
            have hsigc' : m.sigEnv fullSig (Ident.mk "set_in_reif") =
                some [.basic (.var (.par .int)),
                  .basic (.var (.par .setOfInt)),
                  .basic (.var (.par .bool))] := by
              rw [hsig_src]
              simp [fullSig, globalsSig, stdSig]
            have hparams : params =
                [.basic (.var (.par .int)),
                  .basic (.var (.par .setOfInt)),
                  .basic (.var (.par .bool))] :=
              Option.some.inj (hsigc.symm.trans hsigc')
            subst hparams
            have hFz : Expr.checkArg m.staticEnv (.basic (.ident hz))
                (.basic (.var (.par .bool))) :=
              checkArg_third hF
            have hzstat0 := staticEnv_bool_of_checkArg hFz
            have hznotmem : hz.name ∉ se.setNames := by
              have hfalse : se.isSetName hz = false := by simpa using hznot
              exact SetExpansion.not_mem_setNames_of_infoOf_eq_none
                inv.setNames_nodup
                (SetExpansion.infoOf_eq_none_of_isSetName_false hfalse)
            have hzstat : ∃ isVar, se.model.staticEnv (Ident.mk hz.name) =
                some (.base .bool, isVar) := by
              obtain ⟨isVar, hzstat0⟩ := hzstat0
              refine ⟨isVar, ?_⟩
              rw [inv.staticEnv_eq hwf ?_ hznotmem]
              · simpa using hzstat0
              · obtain ⟨info, hinv⟩ := checkArg_names hFz hz.name (by
                  simp [exprNames, basicNames])
                exact staticEnv_mem_setTaken hinv
            exact ⟨[.basic (.var (.par .bool)), .basic (.var (.par .bool))],
              by rw [hsig]; exact fullSig_bool_eq,
              boolEq_check ⟨true, hbstat⟩ hzstat⟩
        case h_2 =>
          rename_i r' hr'
          have hcs : cs = [pinBoolConstraint b true] := (Option.some.inj h).symm
          rw [hcs]
          intro c' hc'
          rw [List.mem_singleton] at hc'
          subst hc'
          obtain ⟨p, hp, hpb, hpv⟩ := SetInfo.boolAt_some hb
          have hi : i ∈ se.sets := SetExpansion.mem_sets_of_infoOf hinfo
          have hbstat : se.model.staticEnv (Ident.mk b) =
              some (.base .bool, true) := by
            rw [← hpb]
            exact inv.fresh_staticEnv hi hp
          exact ⟨[.basic (.var (.par .bool)), .basic (.var (.par .bool))],
            by rw [hsig]; exact fullSig_bool_not,
            pinBool_check ⟨true, hbstat⟩⟩
        case h_3 =>
          rename_i r' hr'
          have hcs : cs = [pinBoolConstraint b false] := (Option.some.inj h).symm
          rw [hcs]
          intro c' hc'
          rw [List.mem_singleton] at hc'
          subst hc'
          obtain ⟨p, hp, hpb, hpv⟩ := SetInfo.boolAt_some hb
          have hi : i ∈ se.sets := SetExpansion.mem_sets_of_infoOf hinfo
          have hbstat : se.model.staticEnv (Ident.mk b) =
              some (.base .bool, true) := by
            rw [← hpb]
            exact inv.fresh_staticEnv hi hp
          exact ⟨[.basic (.var (.par .bool)), .basic (.var (.par .bool))],
            by rw [hsig]; exact fullSig_bool_not,
            pinBool_check ⟨true, hbstat⟩⟩
        case h_4 => cases h
      case h_2 =>
        rename_i hbnone
        split at h
        case h_1 =>
          rename_i z hz
          split at h
          case isTrue => cases h
          case isFalse =>
            rename_i hznot
            have hcs : cs = [pinBoolConstraint hz.name false] :=
              (Option.some.inj h).symm
            rw [hcs]
            intro c' hc'
            rw [List.mem_singleton] at hc'
            subst hc'
            obtain ⟨params, hsigc, hF⟩ := hwf.constraintsChecked _ hc
            have hsigc' : m.sigEnv fullSig (Ident.mk "set_in_reif") =
                some [.basic (.var (.par .int)),
                  .basic (.var (.par .setOfInt)),
                  .basic (.var (.par .bool))] := by
              rw [hsig_src]
              simp [fullSig, globalsSig, stdSig]
            have hparams : params =
                [.basic (.var (.par .int)),
                  .basic (.var (.par .setOfInt)),
                  .basic (.var (.par .bool))] :=
              Option.some.inj (hsigc.symm.trans hsigc')
            subst hparams
            have hFz : Expr.checkArg m.staticEnv (.basic (.ident hz))
                (.basic (.var (.par .bool))) :=
              checkArg_third hF
            have hzstat0 := staticEnv_bool_of_checkArg hFz
            have hznotmem : hz.name ∉ se.setNames := by
              have hfalse : se.isSetName hz = false := by simpa using hznot
              exact SetExpansion.not_mem_setNames_of_infoOf_eq_none
                inv.setNames_nodup
                (SetExpansion.infoOf_eq_none_of_isSetName_false hfalse)
            have hzstat : ∃ isVar, se.model.staticEnv (Ident.mk hz.name) =
                some (.base .bool, isVar) := by
              obtain ⟨isVar, hzstat0⟩ := hzstat0
              refine ⟨isVar, ?_⟩
              rw [inv.staticEnv_eq hwf ?_ hznotmem]
              · simpa using hzstat0
              · obtain ⟨info, hinv⟩ := checkArg_names hFz hz.name (by
                  simp [exprNames, basicNames])
                exact staticEnv_mem_setTaken hinv
            exact ⟨[.basic (.var (.par .bool)), .basic (.var (.par .bool))],
              by rw [hsig]; exact fullSig_bool_not,
              pinBool_check hzstat⟩
        case h_2 =>
          rename_i r' hr'
          have hcs : cs = [falseConstraint] := (Option.some.inj h).symm
          rw [hcs]
          intro c' hc'
          rw [List.mem_singleton] at hc'
          subst hc'
          exact ⟨[.array .int (.par .int), .array .int (.var (.par .int)),
            .basic (.var (.par .int))],
            by rw [hsig]; exact fullSig_int_lin_le,
            falseConstraint_check _⟩
        case h_3 =>
          rename_i r' hr'
          have hcs : cs = [] := (Option.some.inj h).symm
          rw [hcs]
          intro c' hc'
          simp at hc'
        case h_4 => cases h
    case h_2 =>
      rename_i hinone
      split at h
      case isTrue => cases h
      case isFalse =>
        rename_i hno
        have hcs : cs =
            [{ name := Ident.mk "set_in_reif",
               args := [.basic (.lit (.int k)), .basic (.ident S), r],
               anns := anns }] := (Option.some.inj h).symm
        rw [hcs]
        exact kept hc (by simpa using hno)
  case h_3 =>
    split at h
    case isTrue => cases h
    case isFalse =>
      rename_i hno
      have hcs : cs = [{ name := nm, args := args, anns := anns }] :=
        (Option.some.inj h).symm
      rw [hcs]
      exact kept hc (by simpa using hno)

/-- A checked initializer or objective stays checked after the
    expansion. -/
theorem SetExpansion.Inv.hasBaseType_staticEnv {m : Model} {se : SetExpansion}
    {taken : List String} (inv : se.Inv taken m) (hwf : WellFormed fullSig m)
    {b : BasicExpr} {t : BaseType}
    (hb : b.hasBaseType m.staticEnv t) (ht : t ≠ .setOfInt) :
    b.hasBaseType se.model.staticEnv t := by
  apply hasBaseType_staticEnv_eq hb
  intro x hx
  have hnot : x ∉ se.setNames :=
    inv.basicNames_not_set hwf hb ht x hx
  have htak : x ∈ setTaken m := by
    obtain ⟨info, hinv⟩ := hasBaseType_names hb x hx
    exact staticEnv_mem_setTaken hinv
  exact inv.staticEnv_eq hwf htak hnot

/-- **Static well-formedness is preserved by the set expansion.** -/
theorem wf_setExpand {taken : List String} {m : Model} {se : SetExpansion}
    (hwf : WellFormed fullSig m) (hpred : m.predicates = [])
    (hsup : ∀ x ∈ setTaken m, x ∈ taken)
    (h : setExpandModelWith taken m = some se) :
    WellFormed fullSig se.model := by
  have inv := SetExpansion.Inv.of_wellFormed hwf hsup h
  obtain ⟨n', D⟩ := inv.decls
  refine
    { predNamesUnique := ?_
      valueNamesUnique := ?_
      predParamsUnique := ?_
      parameterTypes := ?_
      variableArrayLengths := ?_
      variableInitializers := ?_
      objectiveType := ?_
      constraintsChecked := ?_ }
  · rw [inv.predicates]
    exact hwf.predNamesUnique
  · rw [inv.parameters, List.nodup_append]
    have hsrc := hwf.valueNamesUnique
    rw [List.nodup_append] at hsrc
    obtain ⟨hpnd, _, hdisj⟩ := hsrc
    refine ⟨hpnd, nodup_ident_of_nodup_name D.vars_nodup, ?_⟩
    intro a ha b hb hab
    obtain ⟨d, hd, hdn⟩ := List.mem_map.mp hb
    rcases D.expanded d hd with hsrc | ⟨i, hi, p, hp, heq⟩
    · have hbv : b ∈ m.variables.map VarDeclItem.name :=
        List.mem_map.mpr ⟨d, hsrc, hdn⟩
      exact hdisj a ha b hbv hab
    · have hpd : d.name.name = p.1 := by rw [heq]; rfl
      have hbn : b.name = p.1 := (congrArg Ident.name hdn).symm.trans hpd
      have hpa : p.1 = a.name := ((congrArg Ident.name hab).trans hbn).symm
      have hfresh := D.fresh i hi p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)
      have hat : a.name ∈ setTaken m := by
        obtain ⟨d0, hd0, hd0n⟩ := List.mem_map.mp ha
        exact List.mem_append_left _
          (List.mem_map.mpr ⟨d0, hd0, congrArg Ident.name hd0n⟩)
      exact hfresh (by rw [hpa]; exact inv.superset _ hat)
  · rw [inv.predicates]
    exact hwf.predParamsUnique
  · rw [inv.parameters]
    exact hwf.parameterTypes
  · intro d hd
    rcases D.expanded d hd with hsrc | ⟨i, hi, p, hp, heq⟩
    · exact hwf.variableArrayLengths d hsrc
    · subst heq
      simp
  · intro d hd
    rcases D.expanded d hd with hsrc | ⟨i, hi, p, hp, heq⟩
    · cases d with
      | basic ty n anns init =>
          cases init with
          | none => trivial
          | some e =>
              have hns : ty.base ≠ .setOfInt := by
                have := D.vars_not_set (.basic ty n anns (some e)) hd
                simpa [nonSetDecl, declBase] using this
              exact inv.hasBaseType_staticEnv hwf
                (hwf.variableInitializers _ hsrc) hns
      | array ty n anns es =>
          have hns : ty.elem.base ≠ .setOfInt := by
            have := D.vars_not_set (.array ty n anns es) hd
            simpa [nonSetDecl, declBase] using this
          intro v hv
          exact inv.hasBaseType_staticEnv hwf
            (hwf.variableInitializers _ hsrc v hv) hns
    · subst heq
      simp [VarDeclItem.initializerHolds]
  · rw [inv.solve]
    cases hs : m.solve with
    | satisfy anns => exact trivial
    | minimize anns e =>
        exact inv.hasBaseType_staticEnv hwf
          (by simpa [hs] using hwf.objectiveType) (by decide)
    | maximize anns e =>
        exact inv.hasBaseType_staticEnv hwf
          (by simpa [hs] using hwf.objectiveType) (by decide)
  · intro c' hc'
    obtain ⟨css, hmap, hcons⟩ := inv.constraints
    rw [hcons] at hc'
    obtain ⟨c, hc, cs, hcs, hc'cs⟩ := mem_flatten_of_mapM_some hmap c' hc'
    exact rewriteConstraint_wf inv hwf hpred hc hcs c' hc'cs

end LeanFzn.Compiler



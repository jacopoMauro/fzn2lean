/-
File: LeanFzn/Engine/Props/AllDiff.lean

Dedicated Core `all_different` propagator.

Task P1.1: register a real propagator for `.allDiff is` instead of falling
back to the generic fixed-assignment checker.  The propagator

* rejects a repeated slot identifier immediately (`is` not `Nodup`), because
  then the constraint is unsatisfiable on every assignment;
* detects two distinct fixed slots with the same value and emits the
  entailed conflict clause `x_i ≠ v ∨ x_j ≠ v`;
* removes a fixed value `v` from every other distinct slot that still
  contains `v`, using the same two-literal reason.

The reason is exactly the `int_ne` reason, but entailed by `all_different`
rather than by a binary disequality: if both literals were false, both
slots would carry `v`, contradicting pairwise distinctness.  The
kind-homogeneity guard of `Ne` is reused: `v` must be a member of both
initial converted domains so that `neLit` is exact across value
constructors.

Only `.fix` events are subscribed: fixed-value propagation needs no other
event, and every successful pruning that changes a domain to a singleton
fires `.fix` again.

Dependencies:
  - LeanFzn.Engine.Props.Ne: `neLit` and its evaluation bridge.

DAG: LeanFzn.Engine.Prop -> LeanFzn.Engine.Props.Ne ->
     LeanFzn.Engine.Props.AllDiff
-/
import LeanFzn.Engine.Props.Ne

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

/-! ## Slot bookkeeping -/

/-- A fixed slot together with the proof that it is one of the constraint's
slots.  The proof field is erased at runtime. -/
structure AllDiffFixed (is : List Nat) where
  slot : Nat
  mem : slot ∈ is
  value : Value

/-- The fixed slots of `is` in the current view. -/
def allDiffFixedSlots (is : List Nat) (doms : Array DomC) : List (AllDiffFixed is) :=
  is.attach.filterMap fun x =>
    match (doms.getD x.1 DomC.empty).fixedValue with
    | some v => some ⟨x.1, x.2, v⟩
    | none => none

/-- An initial converted domain is present only at an in-range slot. -/
theorem slot_lt_of_ofDom? {p : CompiledProblem DomConstraint} {s : Nat} {c : DomC}
    (h : DomC.ofDom? (p.domains.getD s Dom.empty) = some c) :
    s < p.domains.length := by
  apply Classical.byContradiction
  intro hlt
  have hnone : p.domains.getD s Dom.empty = Dom.empty := by
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_none_iff.mpr (Nat.le_of_not_lt hlt)]
    rfl
  rw [hnone, DomC.ofDom?_empty] at h
  simp at h

/-! ## Entailment of the two-literal reason -/

/-- **Pair reason.**  If two distinct slots of an `all_different` both carry
`v`, pairwise distinctness fails.  Hence the clause `x_i ≠ v ∨ x_j ≠ v` is
entailed by membership in the constraint, the initial-domain conversion, and
membership of `v` in both initial domains (the kind-homogeneity guard). -/
theorem allDiff_ne_pair_entailed (p : CompiledProblem DomConstraint)
    (is : List Nat) (init : Array DomC)
    (hinit : ∀ s ∈ is,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.allDiff is ∈ p.constraints)
    (i j : Nat) (hi : i ∈ is) (hj : j ∈ is) (hij : i ≠ j)
    (v : Value)
    (hgi : (init.getD i DomC.empty).mem v = true)
    (hgj : (init.getD j DomC.empty).mem v = true) :
    Entailed p [neLit i v, neLit j v] := by
  intro b hb hacc
  have hfit := allAssigns_fits_dom p.domains b hb
  have hsat : (is.map (fun t => b[t]!)).Nodup := by
    have h := List.all_eq_true.mp hacc _ hmem
    rw [DomConstraint.satisfiedB_iff] at h
    exact h
  apply Classical.byContradiction
  intro hno
  have hfalsei : (neLit i v).eval b ≠ some true := by
    intro ht
    exact hno ⟨neLit i v, by simp, ht⟩
  have hfalsej : (neLit j v).eval b ≠ some true := by
    intro ht
    exact hno ⟨neLit j v, by simp, ht⟩
  have hbiLen : i < b.length := by
    have hiDom : i < p.domains.length := slot_lt_of_ofDom? (hinit i hi)
    rw [hfit.1]
    exact hiDom
  have hbjLen : j < b.length := by
    have hjDom : j < p.domains.length := slot_lt_of_ofDom? (hinit j hj)
    rw [hfit.1]
    exact hjDom
  have hbi : b[i]? = some b[i] := List.getElem?_eq_getElem hbiLen
  have hbj : b[j]? = some b[j] := List.getElem?_eq_getElem hbjLen
  have hbiBang : b[i]! = b[i] := by
    simp [List.getElem!_eq_getElem?_getD, hbi]
  have hbjBang : b[j]! = b[j] := by
    simp [List.getElem!_eq_getElem?_getD, hbj]
  have hwi : (init.getD i DomC.empty).mem b[i] = true :=
    (DomC.mem_iff _ _ (hinit i hi) b[i]).mpr (hfit.2 i b[i] hbi)
  have hwj : (init.getD j DomC.empty).mem b[j] = true :=
    (DomC.mem_iff _ _ (hinit j hj) b[j]).mpr (hfit.2 j b[j] hbj)
  have hiffi := neLit_eval_true_iff_of_mem (init := (init.getD i DomC.empty))
    (vi := v) (w := b[i]) hgi hwi hbi
  have hiffj := neLit_eval_true_iff_of_mem (init := (init.getD j DomC.empty))
    (vi := v) (w := b[j]) hgj hwj hbj
  have hbiv : b[i] = v := by
    apply Classical.byContradiction
    intro hne
    exact hfalsei (hiffi.mpr hne)
  have hbjv : b[j] = v := by
    apply Classical.byContradiction
    intro hne
    exact hfalsej (hiffj.mpr hne)
  obtain ⟨k, hk, hik⟩ := List.getElem_of_mem hi
  obtain ⟨l, hl, hjl⟩ := List.getElem_of_mem hj
  have hk' : k < (is.map (fun t => b[t]!)).length := by simpa using hk
  have hisk : is[k]? = some i := by
    rw [List.getElem?_eq_getElem hk, hik]
  have hisl : is[l]? = some j := by
    rw [List.getElem?_eq_getElem hl, hjl]
  have hmapk : (is.map (fun t => b[t]!))[k]? = some v := by
    rw [List.getElem?_map, hisk]
    simp [hbi, hbiv]
  have hmapl : (is.map (fun t => b[t]!))[l]? = some v := by
    rw [List.getElem?_map, hisl]
    simp [hbj, hbjv]
  have hkl : k = l :=
    (List.Nodup.getElem?_inj hk' hsat).mp (by rw [hmapk, hmapl])
  apply hij
  subst hkl
  exact hik.symm.trans hjl

/-! ## Repeated slot identifiers -/

/-- A repeated slot identifier makes `all_different` unsatisfiable. -/
theorem allDiff_unsat_of_not_nodup (p : CompiledProblem DomConstraint)
    (is : List Nat) (hmem : DomConstraint.allDiff is ∈ p.constraints)
    (hdup : ¬ is.Nodup) : Entailed p [] := by
  intro b hb hacc
  have hsat : (is.map (fun t => b[t]!)).Nodup := by
    have h := List.all_eq_true.mp hacc _ hmem
    rw [DomConstraint.satisfiedB_iff] at h
    exact h
  rw [List.nodup_iff_eq_of_getElem_eq] at hdup
  have hex : ∃ (i j : Nat) (hi : i < is.length) (hj : j < is.length),
      is[i] = is[j] ∧ i ≠ j := by
    apply Classical.byContradiction
    intro h
    apply hdup
    intro i j hi hj heq
    apply Classical.byContradiction
    intro hne
    exact h ⟨i, j, hi, hj, heq, hne⟩
  obtain ⟨k, l, hk, hl, hklEq, hkl⟩ := hex
  exfalso
  have hk' : k < (is.map (fun t => b[t]!)).length := by simpa using hk
  have hisk : is[k]? = some is[k] := List.getElem?_eq_getElem hk
  have hisl : is[l]? = some is[l] := List.getElem?_eq_getElem hl
  have hmapk : (is.map (fun t => b[t]!))[k]? =
      some (b[is[k]]!) := by
    rw [List.getElem?_map, hisk]
    rfl
  have hmapl : (is.map (fun t => b[t]!))[l]? =
      some (b[is[l]]!) := by
    rw [List.getElem?_map, hisl]
    rfl
  have hvals : (is.map (fun t => b[t]!))[k]? =
      (is.map (fun t => b[t]!))[l]? := by
    rw [hmapk, hmapl, hklEq]
  exact hkl ((List.Nodup.getElem?_inj hk' hsat).mp hvals)

/-! ## Hall intervals -/

/-- The escape literals of a Hall set: each listed slot must leave the
interval `[a,b]` either below `a` (its `posLe s (a-1)` literal) or above
`b` (its `negLe s b` literal).  On a view whose domains sit inside
`[a,b]` every one of these literals is false. -/
def hallEscapeLits (S : List Nat) (a b : Int) : List Literal :=
  S.flatMap fun s => [posLe s (a - 1), negLe s b]

/-- The reason of an exact-fill bound pruning: the escape literals of the
Hall set together with the two literals pinning the pruned slot `j` to
`[a,b]`.  The target is one of the latter two; the other is a currently
false context literal. -/
def hallExactLits (j : Nat) (S : List Nat) (a b : Int) : List Literal :=
  posLe j (a - 1) :: negLe j b :: hallEscapeLits S a b

theorem mem_hallEscapeLits_pos {S : List Nat} {a b : Int} {s : Nat}
    (hs : s ∈ S) : posLe s (a - 1) ∈ hallEscapeLits S a b := by
  simp [hallEscapeLits]
  exact ⟨s, hs, Or.inl rfl⟩

theorem mem_hallEscapeLits_neg {S : List Nat} {a b : Int} {s : Nat}
    (hs : s ∈ S) : negLe s b ∈ hallEscapeLits S a b := by
  simp [hallEscapeLits]
  exact ⟨s, hs, Or.inr rfl⟩

theorem mem_hallExactLits_pos {S : List Nat} {a b : Int} {j : Nat} :
    posLe j (a - 1) ∈ hallExactLits j S a b := by
  simp [hallExactLits]

theorem mem_hallExactLits_neg {S : List Nat} {a b : Int} {j : Nat} :
    negLe j b ∈ hallExactLits j S a b := by
  simp [hallExactLits]

theorem mem_hallExactLits_escape_pos {S : List Nat} {a b : Int} {j s : Nat}
    (hs : s ∈ S) : posLe s (a - 1) ∈ hallExactLits j S a b := by
  simp [hallExactLits, hallEscapeLits]
  exact Or.inr (Or.inr ⟨s, hs, Or.inl rfl⟩)

theorem mem_hallExactLits_escape_neg {S : List Nat} {a b : Int} {j s : Nat}
    (hs : s ∈ S) : negLe s b ∈ hallExactLits j S a b := by
  simp [hallExactLits, hallEscapeLits]
  exact Or.inr (Or.inr ⟨s, hs, Or.inr rfl⟩)

/-- Mapping through an injective-on-members function preserves
duplicate-freedom. -/
theorem allDiff_nodup_map_of_inj_on {α β : Type} :
    ∀ {l : List α}, l.Nodup → ∀ (f : α → β),
      (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → (l.map f).Nodup := by
  intro l
  induction l with
  | nil => intro _ f _; simp
  | cons x xs ih =>
      intro h f hinj
      rw [List.nodup_cons] at h
      obtain ⟨hx, hxs⟩ := h
      rw [List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        obtain ⟨y, hy, hyeq⟩ := List.mem_map.mp hmem
        have hxy : x = y := hinj x (by simp) y (by simp [hy]) hyeq.symm
        exact hx (by simpa [hxy] using hy)
      · exact ih hxs f (fun y hy z hz => hinj y (by simp [hy]) z (by simp [hz]))

/-- **Integer pigeonhole.**  A duplicate-free list of integers contained in
`[a,b]` has at most `b-a+1` elements. -/
theorem allDiff_nodup_int_interval_length_le {l : List Int} {a b : Int}
    (hnd : l.Nodup) (hbound : ∀ x ∈ l, a ≤ x ∧ x ≤ b) :
    l.length ≤ (b - a + 1).toNat := by
  by_cases hba : b < a
  · have hl : l = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro x hx
      have hx' := hbound x hx
      omega
    rw [hl]
    simp
  · have hle : a ≤ b := by omega
    let n := (b - a + 1).toNat
    have hn : (n : Int) = b - a + 1 := Int.toNat_of_nonneg (by omega)
    let f : Int → Nat := fun x => (x - a).toNat
    have hf_inj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y := by
      intro x hx y hy hxy
      have hx' := hbound x hx
      have hy' := hbound y hy
      have hxnonneg : 0 ≤ x - a := by omega
      have hynonneg : 0 ≤ y - a := by omega
      have hxeq : (f x : Int) = x - a := Int.toNat_of_nonneg hxnonneg
      have hyeq : (f y : Int) = y - a := Int.toNat_of_nonneg hynonneg
      have : x - a = y - a := by
        rw [← hxeq, ← hyeq, hxy]
      omega
    have hndf : (l.map f).Nodup := allDiff_nodup_map_of_inj_on hnd f hf_inj
    have hsub : ∀ y ∈ l.map f, y ∈ List.range n := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      rw [List.mem_range]
      have hx' := hbound x hx
      have hxnonneg : 0 ≤ x - a := by omega
      have hxlt : x - a < (n : Int) := by omega
      exact (Int.toNat_lt hxnonneg).mpr hxlt
    have hle' := List.Nodup.length_le_of_subset hndf hsub
    simpa [List.length_map, List.length_range, n] using hle'

/-- Elimination of a symmetric `List.Pairwise` relation at arbitrary
members. -/
theorem allDiff_pairwise_rel_of_mem_of_symm {α : Type} {R : α → α → Prop}
    (hsymm : ∀ a b, R a b → R b a)
    {l : List α} (h : List.Pairwise R l)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) : R a b := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
      cases h with
      | cons hhead htail =>
          rcases List.mem_cons.mp ha with rfl | ha'
          · rcases List.mem_cons.mp hb with rfl | hb'
            · exact absurd rfl hne
            · exact hhead b hb'
          · rcases List.mem_cons.mp hb with rfl | hb'
            · exact hsymm _ _ (hhead a ha')
            · exact ih htail ha' hb'

/-- A false positive and a false negative order literal pin the slot's
integer view inside `[a,b]`. -/
theorem hall_escape_bounds {asg : Assignment} {s : Nat} {a b x : Int}
    (hslot : slotInt asg s = some x)
    (hpos : (posLe s (a - 1)).eval asg ≠ some true)
    (hneg : (negLe s b).eval asg ≠ some true) :
    a ≤ x ∧ x ≤ b := by
  constructor
  · apply Classical.byContradiction
    intro hlt
    apply hpos
    exact (eval_posLe_iff asg s (a - 1)).mpr ⟨x, hslot, by omega⟩
  · apply Classical.byContradiction
    intro hgt
    apply hneg
    exact (eval_negLe_iff asg s b).mpr ⟨x, hslot, by omega⟩

/-- **Hall conflict.**  If more slots than the `b-a+1` values of `[a,b]`
have all their values inside `[a,b]`, `all_different` is violated, so the
disjunction of the escape literals is entailed. -/
theorem allDiff_hall_conflict_entailed (p : CompiledProblem DomConstraint)
    (is : List Nat) (init : Array DomC)
    (hinit : ∀ s ∈ is,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.allDiff is ∈ p.constraints)
    (hint : ∀ s ∈ is, (init.getD s DomC.empty).intKindB = true)
    (S : List Nat) (a b : Int)
    (hSsub : ∀ s ∈ S, s ∈ is)
    (hSnd : S.Nodup)
    (hlen : (b - a + 1).toNat < S.length) :
    Entailed p (hallEscapeLits S a b) := by
  intro asg hasg hacc
  apply Classical.byContradiction
  intro hno
  have hsat : (is.map (fun t => asg[t]!)).Nodup := by
    have h := List.all_eq_true.mp hacc _ hmem
    rw [DomConstraint.satisfiedB_iff] at h
    exact h
  have hpair : List.Pairwise (fun s t => asg[s]! ≠ asg[t]!) is := by
    have h := (List.pairwise_map (l := is) (f := fun t => asg[t]!)
      (R := fun x y : Value => x ≠ y)).mp hsat
    simpa using h
  have hfit := allAssigns_fits_dom p.domains asg hasg
  have hslotInt : ∀ s ∈ S, ∃ v, asg[s]! = .int v ∧ slotInt asg s = some v := by
    intro s hs
    have hs' := hSsub s hs
    have hltDom : s < p.domains.length := slot_lt_of_ofDom? (hinit s hs')
    have hltAsg : s < asg.length := by
      rw [hfit.1]
      exact hltDom
    have has : asg[s]? = some asg[s] := List.getElem?_eq_getElem hltAsg
    have hmemInit : (init.getD s DomC.empty).mem asg[s] = true :=
      (DomC.mem_iff _ _ (hinit s hs') asg[s]).mpr (hfit.2 s asg[s] has)
    obtain ⟨v, hv⟩ := DomC.mem_int_of_intKindB (hint s hs') hmemInit
    have hsome : asg[s]? = some (.int v) := by rw [has]; simp [hv]
    exact ⟨v, by simp [List.getElem!_eq_getElem?_getD, hsome],
      by simp [slotInt, hsome, Value.intView]⟩
  let x : Nat → Int := fun s => (slotInt asg s).getD 0
  have hx : ∀ s ∈ S, slotInt asg s = some (x s) := by
    intro s hs
    obtain ⟨v, _, hslot⟩ := hslotInt s hs
    simp [x, hslot]
  have hval : ∀ s ∈ S, asg[s]! = .int (x s) := by
    intro s hs
    obtain ⟨v, hbang, hslot⟩ := hslotInt s hs
    have h := hx s hs
    rw [hslot] at h
    have hvx : v = x s := Option.some.inj h
    rw [hbang, hvx]
  have hvalPair : ∀ s ∈ is, ∀ t ∈ is, s ≠ t → asg[s]! ≠ asg[t]! :=
    fun s hs t ht hne =>
      allDiff_pairwise_rel_of_mem_of_symm (R := fun u v => asg[u]! ≠ asg[v]!)
        (fun _ _ h => Ne.symm h) hpair hs ht hne
  rw [List.nodup_iff_pairwise_ne] at hSnd
  have hnd' : List.Pairwise (fun s t => x s ≠ x t) S := by
    apply List.Pairwise.imp_of_mem (l := S) ?_ hSnd
    intro s t hs ht hst hxy
    apply hvalPair s (hSsub s hs) t (hSsub t ht) hst
    rw [hval s hs, hval t ht, hxy]
  have hndx : (S.map x).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact hnd'
  have hbndx : ∀ y ∈ S.map x, a ≤ y ∧ y ≤ b := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hy
    have hpos : (posLe s (a - 1)).eval asg ≠ some true := by
      intro ht
      exact hno ⟨posLe s (a - 1), mem_hallEscapeLits_pos hs, ht⟩
    have hneg : (negLe s b).eval asg ≠ some true := by
      intro ht
      exact hno ⟨negLe s b, mem_hallEscapeLits_neg hs, ht⟩
    exact hall_escape_bounds (hx s hs) hpos hneg
  have hle := allDiff_nodup_int_interval_length_le hndx hbndx
  have hle' : S.length ≤ (b - a + 1).toNat := by
    simpa [List.length_map] using hle
  exact (Nat.not_lt_of_ge hle') hlen

/-- **Exact-fill bound pruning.**  If the Hall set `S` fills `[a,b]`
exactly and `j` is another slot, then `j` cannot take any value of
`[a,b]`; the clause pinning `j` to `[a,b]` together with the Hall escapes
is entailed.  Both bound prunings use this one reason. -/
theorem allDiff_hall_exact_entailed (p : CompiledProblem DomConstraint)
    (is : List Nat) (init : Array DomC)
    (hinit : ∀ s ∈ is,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.allDiff is ∈ p.constraints)
    (hint : ∀ s ∈ is, (init.getD s DomC.empty).intKindB = true)
    (S : List Nat) (j : Nat) (a b : Int)
    (hSsub : ∀ s ∈ S, s ∈ is)
    (hSnd : S.Nodup)
    (hlen : S.length = (b - a + 1).toNat)
    (hj : j ∈ is) (hjS : j ∉ S) :
    Entailed p (hallExactLits j S a b) := by
  intro asg hasg hacc
  apply Classical.byContradiction
  intro hno
  have hsat : (is.map (fun t => asg[t]!)).Nodup := by
    have h := List.all_eq_true.mp hacc _ hmem
    rw [DomConstraint.satisfiedB_iff] at h
    exact h
  have hpair : List.Pairwise (fun s t => asg[s]! ≠ asg[t]!) is := by
    have h := (List.pairwise_map (l := is) (f := fun t => asg[t]!)
      (R := fun x y : Value => x ≠ y)).mp hsat
    simpa using h
  have hvalPair : ∀ s ∈ is, ∀ t ∈ is, s ≠ t → asg[s]! ≠ asg[t]! :=
    fun s hs t ht hne =>
      allDiff_pairwise_rel_of_mem_of_symm (R := fun u v => asg[u]! ≠ asg[v]!)
        (fun _ _ h => Ne.symm h) hpair hs ht hne
  have hfit := allAssigns_fits_dom p.domains asg hasg
  have hslotInt : ∀ s ∈ is, ∃ v, asg[s]! = .int v ∧ slotInt asg s = some v := by
    intro s hs
    have hltDom : s < p.domains.length := slot_lt_of_ofDom? (hinit s hs)
    have hltAsg : s < asg.length := by
      rw [hfit.1]
      exact hltDom
    have has : asg[s]? = some asg[s] := List.getElem?_eq_getElem hltAsg
    have hmemInit : (init.getD s DomC.empty).mem asg[s] = true :=
      (DomC.mem_iff _ _ (hinit s hs) asg[s]).mpr (hfit.2 s asg[s] has)
    obtain ⟨v, hv⟩ := DomC.mem_int_of_intKindB (hint s hs) hmemInit
    have hsome : asg[s]? = some (.int v) := by rw [has]; simp [hv]
    exact ⟨v, by simp [List.getElem!_eq_getElem?_getD, hsome],
      by simp [slotInt, hsome, Value.intView]⟩
  let x : Nat → Int := fun s => (slotInt asg s).getD 0
  have hxOf : ∀ s ∈ is, slotInt asg s = some (x s) := by
    intro s hs
    obtain ⟨v, _, hslot⟩ := hslotInt s hs
    simp [x, hslot]
  have hvalOf : ∀ s ∈ is, asg[s]! = .int (x s) := by
    intro s hs
    obtain ⟨v, hbang, hslot⟩ := hslotInt s hs
    have h := hxOf s hs
    rw [hslot] at h
    have hvx : v = x s := Option.some.inj h
    rw [hbang, hvx]
  have hnot : ∀ l ∈ hallExactLits j S a b, l.eval asg ≠ some true := by
    intro l hl ht
    exact hno ⟨l, hl, ht⟩
  have hxj : a ≤ x j ∧ x j ≤ b := by
    have hpos : (posLe j (a - 1)).eval asg ≠ some true :=
      hnot _ mem_hallExactLits_pos
    have hneg : (negLe j b).eval asg ≠ some true :=
      hnot _ mem_hallExactLits_neg
    exact hall_escape_bounds (hxOf j hj) hpos hneg
  rw [List.nodup_iff_pairwise_ne] at hSnd
  have hnd' : List.Pairwise (fun s t => x s ≠ x t) S := by
    apply List.Pairwise.imp_of_mem (l := S) ?_ hSnd
    intro s t hs ht hst hxy
    apply hvalPair s (hSsub s hs) t (hSsub t ht) hst
    rw [hvalOf s (hSsub s hs), hvalOf t (hSsub t ht), hxy]
  have hndx : (S.map x).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact hnd'
  have hxS : x j ∉ S.map x := by
    intro hmem
    obtain ⟨s, hs, heq⟩ := List.mem_map.mp hmem
    have hjs : j ≠ s := by
      intro h
      subst h
      exact hjS hs
    apply hvalPair j hj s (hSsub s hs) hjs
    rw [hvalOf j hj, hvalOf s (hSsub s hs), heq]
  have hndT : ((j :: S).map x).Nodup := by
    rw [List.map_cons, List.nodup_cons]
    exact ⟨hxS, hndx⟩
  have hbndT : ∀ y ∈ (j :: S).map x, a ≤ y ∧ y ≤ b := by
    intro y hy
    rw [List.map_cons] at hy
    rcases List.mem_cons.mp hy with rfl | hyS
    · exact hxj
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hyS
      have hpos : (posLe s (a - 1)).eval asg ≠ some true :=
        hnot _ (mem_hallExactLits_escape_pos hs)
      have hneg : (negLe s b).eval asg ≠ some true :=
        hnot _ (mem_hallExactLits_escape_neg hs)
      exact hall_escape_bounds (hxOf s (hSsub s hs)) hpos hneg
  have hle := allDiff_nodup_int_interval_length_le hndT hbndT
  have hlenT : ((j :: S).map x).length = S.length + 1 := by simp
  omega

/-! ## Conflict detection -/

/-- Return the first entailed conflict among the fixed slots: two distinct
slots with the same value, both values present in the respective initial
domains. -/
def allDiffFindConflict (p : CompiledProblem DomConstraint) (T : LitTable)
    (is : List Nat) (init : Array DomC)
    (hinit : ∀ s ∈ is,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.allDiff is ∈ p.constraints)
    (fs : List (AllDiffFixed is)) : Option (EClause p T) :=
  fs.foldl (fun acc a =>
    match acc with
    | some _ => acc
    | none =>
        fs.foldl (fun acc b =>
          match acc with
          | some _ => acc
          | none =>
              if hne : a.slot ≠ b.slot then
                if heq : a.value == b.value then
                  if hgi : (init.getD a.slot DomC.empty).mem a.value = true then
                    if hgj : (init.getD b.slot DomC.empty).mem a.value = true then
                      some (EClause.ofLiterals p T
                        [neLit a.slot a.value, neLit b.slot a.value]
                        (allDiff_ne_pair_entailed p is init hinit hmem
                          a.slot b.slot a.mem b.mem hne a.value hgi
                          (by simpa [eq_of_beq heq] using hgj)))
                    else none
                  else none
                else none
              else none) none) none

/-! ## Fixed-value pruning -/

/-- All distinct non-fixed slots containing `v`, pruned by the fixed slot
`a` with value `v`. -/
def allDiffPrunesFor (p : CompiledProblem DomConstraint) (T : LitTable)
    (is : List Nat) (init : Array DomC)
    (hinit : ∀ s ∈ is,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.allDiff is ∈ p.constraints)
    (doms : Array DomC) (a : AllDiffFixed is)
    (hgi : (init.getD a.slot DomC.empty).mem a.value = true) :
    Array (PLit × EClause p T) :=
  is.attach.foldl (fun acc b =>
    if hne : b.1 ≠ a.slot then
      let db := doms.getD b.1 DomC.empty
      if _hfix : db.fixedValue = none then
        if _hm : db.mem a.value = true then
          if hgj : (init.getD b.1 DomC.empty).mem a.value = true then
            acc.push (pLit (neLit b.1 a.value),
              EClause.ofLiterals p T [neLit a.slot a.value, neLit b.1 a.value]
                (allDiff_ne_pair_entailed p is init hinit hmem
                  a.slot b.1 a.mem b.2 (Ne.symm hne) a.value hgi hgj))
          else acc
        else acc
      else acc
    else acc) #[]

/-- Batch all fixed-value prunings of the current view. -/
def allDiffCollectPrunes (p : CompiledProblem DomConstraint) (T : LitTable)
    (is : List Nat) (init : Array DomC)
    (hinit : ∀ s ∈ is,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.allDiff is ∈ p.constraints)
    (doms : Array DomC) (fs : List (AllDiffFixed is)) :
    Array (PLit × EClause p T) :=
  fs.foldl (fun acc a =>
    if hgi : (init.getD a.slot DomC.empty).mem a.value = true then
      acc ++ allDiffPrunesFor p T is init hinit hmem doms a hgi
    else acc) #[]

/-! ## Hall interval runtime support -/

/-- A slot together with its current integer bounds. -/
structure AllDiffItem where
  slot : Nat
  lo : Int
  hi : Int
  deriving Repr, Inhabited

/-- Current integer bounds of a slot, when the compact domain is
nonempty and integer-kind. -/
def allDiffBounds? (doms : Array DomC) (s : Nat) : Option (Int × Int) :=
  let d := doms.getD s DomC.empty
  if d.intKindB = true then
    match d.lo?, d.hi? with
    | some lo, some hi => some (lo, hi)
    | _, _ => none
  else none

/-- Item extraction for one slot. -/
def allDiffItemOfDom? (doms : Array DomC) (s : Nat) : Option AllDiffItem :=
  (allDiffBounds? doms s).map fun p => ⟨s, p.1, p.2⟩

/-- All slots with current integer bounds, sorted by upper bound.  Sorting
once lets the interval sweep below run in time quadratic in the number of
slots instead of cubic: per left endpoint it only walks the already
filtered list, and every prefix is a candidate Hall set. -/
def allDiffHallItems (is : List Nat) (doms : Array DomC) : List AllDiffItem :=
  (is.filterMap (allDiffItemOfDom? doms)).mergeSort
    (fun x y => decide (x.hi ≤ y.hi))

theorem allDiffItemOfDom?_slot {doms : Array DomC} {s : Nat} {x : AllDiffItem}
    (h : allDiffItemOfDom? doms s = some x) : x.slot = s := by
  unfold allDiffItemOfDom? at h
  cases hb : allDiffBounds? doms s with
  | none => simp [hb] at h
  | some p =>
      simp [hb] at h
      rw [← h]

theorem allDiffItem_slot_mem_filterMap {is : List Nat} {doms : Array DomC}
    {x : AllDiffItem} (hx : x ∈ is.filterMap (allDiffItemOfDom? doms)) :
    x.slot ∈ is := by
  obtain ⟨s, hs, hf⟩ := List.mem_filterMap.mp hx
  rw [allDiffItemOfDom?_slot hf]
  exact hs

theorem allDiffItem_slot_mem {is : List Nat} {doms : Array DomC}
    {x : AllDiffItem} (hx : x ∈ allDiffHallItems is doms) : x.slot ∈ is := by
  unfold allDiffHallItems at hx
  exact allDiffItem_slot_mem_filterMap (List.mem_mergeSort.mp hx)

/-- Mapping the slot projection turns the item filter into a sublist of
the original slot list. -/
theorem allDiffFilterMap_slots_sublist (is : List Nat) (doms : Array DomC) :
    ((is.filterMap (allDiffItemOfDom? doms)).map AllDiffItem.slot).Sublist is := by
  induction is with
  | nil => simp
  | cons s ss ih =>
      rw [List.filterMap_cons]
      cases hb : allDiffItemOfDom? doms s with
      | none =>
          simp
          exact List.Sublist.cons s ih
      | some x =>
          simp
          have hxs : x.slot = s := allDiffItemOfDom?_slot hb
          rw [hxs]
          exact List.Sublist.cons_cons s ih

theorem allDiffHallFilter_slots_nodup {is : List Nat} {doms : Array DomC}
    (hnd : is.Nodup) :
    ((is.filterMap (allDiffItemOfDom? doms)).map AllDiffItem.slot).Nodup :=
  List.Nodup.sublist (allDiffFilterMap_slots_sublist is doms) hnd

/-- The item list carries each slot at most once. -/
theorem allDiffHallItems_slots_nodup {is : List Nat} {doms : Array DomC}
    (hnd : is.Nodup) :
    ((allDiffHallItems is doms).map AllDiffItem.slot).Nodup := by
  unfold allDiffHallItems
  have hperm :
      ((is.filterMap (allDiffItemOfDom? doms)).map AllDiffItem.slot).Perm
        (((is.filterMap (allDiffItemOfDom? doms)).mergeSort
          (fun x y => decide (x.hi ≤ y.hi))).map AllDiffItem.slot) :=
    (List.Perm.map _ (List.mergeSort_perm _ _)).symm
  exact List.Perm.nodup hperm (allDiffHallFilter_slots_nodup hnd)

/-- Distinct current lower bounds.  Checking these as left interval
endpoints is complete: a Hall interval can be tightened to one whose left
endpoint is the lower bound of one of its slots. -/
def allDiffHallLowers (items : List AllDiffItem) : List Int :=
  (items.foldl (fun acc x =>
    if acc.contains x.lo then acc else acc.push x.lo) #[]).toList

/-- All exact-fill bound prunings of one interval.  A slot whose lower
bound lies inside `[a,b]` while its upper bound exceeds `b` gets
`x > b`; symmetrically a slot whose upper bound lies inside `[a,b]`
while its lower bound is below `a` gets `x < a`. -/
def allDiffHallPrunesFor (p : CompiledProblem DomConstraint) (T : LitTable)
    (init : Array DomC) (is : List Nat)
    (hinit : ∀ s ∈ is,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.allDiff is ∈ p.constraints)
    (hint : ∀ s ∈ is, (init.getD s DomC.empty).intKindB = true)
    (items : List AllDiffItem)
    (hitems : ∀ x ∈ items, x.slot ∈ is)
    (S : List Nat) (a b : Int)
    (hSsub : ∀ s ∈ S, s ∈ is) (hSnd : S.Nodup)
    (hlen : S.length = (b - a + 1).toNat) :
    Array (PLit × EClause p T) :=
  items.attach.foldl (fun acc x =>
    let j := x.1.slot
    if hjS : j ∈ S then acc
    else
      if decide (a ≤ x.1.lo) && decide (x.1.lo ≤ b) && decide (b < x.1.hi) then
        acc.push (pLit (negLe j b),
          EClause.ofLiterals p T (hallExactLits j S a b)
            (allDiff_hall_exact_entailed p is init hinit hmem hint S j a b
              hSsub hSnd hlen (hitems x.1 x.2) hjS))
      else if decide (a ≤ x.1.hi) && decide (x.1.lo < a) && decide (x.1.hi ≤ b) then
        acc.push (pLit (posLe j (a - 1)),
          EClause.ofLiterals p T (hallExactLits j S a b)
            (allDiff_hall_exact_entailed p is init hinit hmem hint S j a b
              hSsub hSnd hlen (hitems x.1 x.2) hjS))
      else acc) #[]

/-- Sorted-prefix Hall sweep.  For each candidate left endpoint `a` walk
the slots with `lo ≥ a` in increasing upper-bound order.  The prefix
ending at `b` is a Hall set: all its slots lie in `[a,b]`.  A prefix
longer than `b-a+1` is a conflict; a prefix of exactly that length pins
every other slot away from `[a,b]`, which yields the two bound prunings
of `allDiffHallPrunesFor`. -/
def allDiffHallSweep (p : CompiledProblem DomConstraint) (T : LitTable)
    (init : Array DomC) (is : List Nat)
    (hinit : ∀ s ∈ is,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.allDiff is ∈ p.constraints)
    (hint : ∀ s ∈ is, (init.getD s DomC.empty).intKindB = true)
    (items : List AllDiffItem)
    (hitems : ∀ x ∈ items, x.slot ∈ is)
    (hndItems : (items.map AllDiffItem.slot).Nodup) :
    Option (EClause p T) × Array (PLit × EClause p T) :=
  let lowers := allDiffHallLowers items
  let rec goA (as : List Int) (conflict : Option (EClause p T))
      (acc : Array (PLit × EClause p T)) :
      Option (EClause p T) × Array (PLit × EClause p T) :=
    match as with
    | [] => (conflict, acc)
    | a :: as' =>
        match conflict with
        | some c => (some c, acc)
        | none =>
            let cand := items.filter fun x => decide (a ≤ x.lo)
            let rec go (rest : List AllDiffItem)
                (hRest : ∀ y ∈ rest, y ∈ cand)
                (k : Nat)
                (hRestLen : k + rest.length = cand.length)
                (conflict : Option (EClause p T))
                (acc : Array (PLit × EClause p T)) :
                Option (EClause p T) × Array (PLit × EClause p T) :=
              match rest with
              | [] => (conflict, acc)
              | x :: xs =>
                  match conflict with
                  | some c => (some c, acc)
                  | none =>
                      let k' := k + 1
                      let b := x.hi
                      let cap := (b - a + 1).toNat
                      have hxCand : x ∈ cand := hRest x (by simp)
                      have hxItems : x ∈ items := (List.mem_filter.mp hxCand).1
                      have hk'le : k' ≤ cand.length := by
                        have hlen : k + (xs.length + 1) = cand.length := by
                          simpa using hRestLen
                        omega
                      have hRestLen' : k' + xs.length = cand.length := by
                        have hlen : k + (xs.length + 1) = cand.length := by
                          simpa using hRestLen
                        simp [k']
                        omega
                      if hlt : cap < k' then
                        let S := (cand.take k').map AllDiffItem.slot
                        have hSsub : ∀ s ∈ S, s ∈ is := by
                          intro s hs
                          obtain ⟨y, hyTake, rfl⟩ := List.mem_map.mp hs
                          have hyCand : y ∈ cand :=
                            List.Sublist.subset (List.take_sublist k' cand) hyTake
                          exact hitems y (List.mem_filter.mp hyCand).1
                        have hSnd : S.Nodup := by
                          have htake : (cand.take k').Sublist cand :=
                            List.take_sublist k' cand
                          have hsub : S.Sublist (items.map AllDiffItem.slot) :=
                            List.Sublist.trans (List.Sublist.map _ htake)
                              (List.Sublist.map _ List.filter_sublist)
                          exact List.Nodup.sublist hsub hndItems
                        have hSlen : S.length = k' := by
                          simp [S, List.length_take, Nat.min_eq_left hk'le]
                        (some (EClause.ofLiterals p T (hallEscapeLits S a b)
                          (allDiff_hall_conflict_entailed p is init hinit hmem hint
                            S a b hSsub hSnd (by
                              show (b - a + 1).toNat < S.length
                              rw [hSlen]
                              exact hlt))), acc)
                      else if hEq : k' = cap then
                        let S := (cand.take k').map AllDiffItem.slot
                        have hSsub : ∀ s ∈ S, s ∈ is := by
                          intro s hs
                          obtain ⟨y, hyTake, rfl⟩ := List.mem_map.mp hs
                          have hyCand : y ∈ cand :=
                            List.Sublist.subset (List.take_sublist k' cand) hyTake
                          exact hitems y (List.mem_filter.mp hyCand).1
                        have hSnd : S.Nodup := by
                          have htake : (cand.take k').Sublist cand :=
                            List.take_sublist k' cand
                          have hsub : S.Sublist (items.map AllDiffItem.slot) :=
                            List.Sublist.trans (List.Sublist.map _ htake)
                              (List.Sublist.map _ List.filter_sublist)
                          exact List.Nodup.sublist hsub hndItems
                        have hSlen : S.length = k' := by
                          simp [S, List.length_take, Nat.min_eq_left hk'le]
                        let acc' := acc ++
                          allDiffHallPrunesFor p T init is hinit hmem hint items hitems
                            S a b hSsub hSnd (by rw [hSlen]; exact hEq)
                        go xs (fun y hy => hRest y (List.mem_cons_of_mem x hy))
                          k' hRestLen' conflict acc'
                      else
                        go xs (fun y hy => hRest y (List.mem_cons_of_mem x hy))
                          k' hRestLen' conflict acc
            match go cand (fun _ h => h) 0 (by simp) none acc with
            | (some c, acc') => (some c, acc')
            | (none, acc') => goA as' none acc'
  goA lowers none #[]

/-! ## The propagator -/

/-- Dedicated `all_different` propagation. -/
def allDiffPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (init : Array DomC) (is : List Nat)
    (hinit : ∀ s ∈ is,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.allDiff is ∈ p.constraints) : PropV2 p T :=
  { vars := is.toArray
    events := is.eraseDups.toArray.flatMap fun s => #[(s, .fix), (s, .bounds)]
    run := fun view =>
      if hdup : is.Nodup then
        let fs := allDiffFixedSlots is view.doms
        match allDiffFindConflict p T is init hinit hmem fs with
        | some ec => .conflict ec
        | none =>
            let fixedPs := allDiffCollectPrunes p T is init hinit hmem view.doms fs
            if hkind : is.all (fun s => (init.getD s DomC.empty).intKindB) = true then
              let hint : ∀ s ∈ is, (init.getD s DomC.empty).intKindB = true :=
                fun s hs => List.all_eq_true.mp hkind s hs
              let items := allDiffHallItems is view.doms
              let hall := allDiffHallSweep p T init is hinit hmem hint items
                (fun _ hx => allDiffItem_slot_mem hx)
                (allDiffHallItems_slots_nodup hdup)
              match hall.1 with
              | some ec => .conflict ec
              | none =>
                  -- Different left endpoints can derive the same target
                  -- pruning.  Keep one reason per target: every reason is
                  -- entailed on its own, so dropping duplicates is sound.
                  let ps := (fixedPs ++ hall.2).foldl
                    (fun acc pe =>
                      if acc.any (fun q => q.1 == pe.1) then acc else acc.push pe) #[]
                  if ps.isEmpty then .fix else .prune ps
            else
              if fixedPs.isEmpty then .fix else .prune fixedPs
      else
        .conflict (EClause.ofLiterals p T []
          (allDiff_unsat_of_not_nodup p is hmem hdup)) }

/-! ## Runtime contracts used by the tests -/

/-- The conflict literals emitted for two fixed slots are false on the
current view. -/
theorem allDiff_fixed_pair_lits_false {d₁ d₂ : DomC} {i j : Nat} {v : Value}
    (h₁ : d₁.WF) (h₂ : d₂.WF)
    (hf₁ : d₁.fixedValue = some v) (hf₂ : d₂.fixedValue = some v) :
    d₁.evalLit (neLit i v) = some false ∧ d₂.evalLit (neLit j v) = some false :=
  ⟨DomC.evalLit_neLit_fixed_false h₁ hf₁,
   DomC.evalLit_neLit_fixed_false h₂ hf₂⟩

/-- A fixed source and an unfixed target containing `v` make the source
literal false and the target literal unassigned. -/
theorem allDiff_prune_lits {d₁ d₂ : DomC} {i j : Nat} {v : Value}
    (h₁ : d₁.WF) (hf₁ : d₁.fixedValue = some v)
    (hf₂ : d₂.fixedValue = none) (hm₂ : d₂.mem v = true) :
    d₁.evalLit (neLit i v) = some false ∧ d₂.evalLit (neLit j v) = none :=
  ⟨DomC.evalLit_neLit_fixed_false h₁ hf₁,
   DomC.evalLit_neLit_none_of_not_fixed hf₂ hm₂⟩

end LeanFzn.Engine

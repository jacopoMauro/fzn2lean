/-
File: LeanFzn/Engine/Props/Linear.lean

Dedicated bounded linear inequality (`int_lin_le`) propagator.  It mirrors
the bounds propagation of `propLinLe`: each term is bounded by the other
terms' minimum contribution.  Explanations are the propagated bound plus
the current bound-negation literals of the other variables, which linear
arithmetic entails.
-/
import LeanFzn.Engine.Prop

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

def linTermMin (c lo hi : Int) : Int := if 0 ≤ c then c * lo else c * hi

def linMinNegLit (s : Nat) (c lo hi : Int) : Literal :=
  if 0 ≤ c then posLe s (lo - 1) else negLe s hi

structure LinTerm where
  c : Int
  s : Nat
  lo : Int
  hi : Int
  deriving Repr, DecidableEq

def LinTerm.min (t : LinTerm) : Int := linTermMin t.c t.lo t.hi

def linBoundAt (doms : Array DomC) (s : Nat) : Option (Int × Int) :=
  match (doms.getD s DomC.empty).lo?, (doms.getD s DomC.empty).hi? with
  | some lo, some hi => some (lo, hi)
  | _, _ => none

theorem linBoundAt_spec {doms : Array DomC} {s : Nat} {lo hi : Int}
    (h : linBoundAt doms s = some (lo, hi)) :
    (doms.getD s DomC.empty).lo? = some lo ∧
      (doms.getD s DomC.empty).hi? = some hi := by
  unfold linBoundAt at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by assumption, by assumption⟩
  · simp at h

def linExtractBoundsAux (doms : Array DomC) : List Nat → Option (List (Int × Int))
  | [] => some []
  | s :: ss =>
      (linBoundAt doms s).bind fun p =>
        (linExtractBoundsAux doms ss).map fun rest => p :: rest

def linExtractBounds (doms : Array DomC) (is : Array Nat) : Option (Array (Int × Int)) :=
  (linExtractBoundsAux doms is.toList).map fun bds => bds.toArray

theorem linExtractBoundsAux_spec {doms : Array DomC} {slots : List Nat}
    {bds : List (Int × Int)} (h : linExtractBoundsAux doms slots = some bds) :
    bds.length = slots.length ∧
      ∀ i (hi : i < slots.length), ∃ lo hi,
        (doms.getD slots[i] DomC.empty).lo? = some lo ∧
        (doms.getD slots[i] DomC.empty).hi? = some hi ∧
        bds[i]? = some (lo, hi) := by
  induction slots generalizing bds with
  | nil =>
      simp [linExtractBoundsAux] at h
      subst bds
      simp
  | cons s ss ih =>
      simp only [linExtractBoundsAux] at h
      cases hb : linBoundAt doms s with
      | none =>
          rw [hb] at h
          simp at h
      | some p =>
          rw [hb] at h
          simp only [Option.bind_some] at h
          cases hrec : linExtractBoundsAux doms ss with
          | none =>
              rw [hrec] at h
              simp at h
          | some rest =>
              rw [hrec] at h
              simp only [Option.map_some, Option.some.injEq] at h
              subst bds
              obtain ⟨lo, hi⟩ := p
              have hspec := linBoundAt_spec (doms := doms) (s := s) hb
              have ih' := ih hrec
              refine ⟨by simp [ih'.1], ?_⟩
              intro i hiLen
              cases i with
              | zero =>
                  simp only [List.getElem_cons_zero, List.getElem?_cons_zero]
                  exact ⟨lo, hi, hspec.1, hspec.2, rfl⟩
              | succ k =>
                  simp only [List.getElem_cons_succ, List.getElem?_cons_succ]
                  exact ih'.2 k (by simpa using hiLen)

theorem linExtractBounds_spec {doms : Array DomC} {is : Array Nat}
    {bds : Array (Int × Int)} (h : linExtractBounds doms is = some bds) :
    bds.size = is.size ∧
      ∀ i (hi : i < is.size), ∃ lo hi,
        (doms.getD is[i] DomC.empty).lo? = some lo ∧
        (doms.getD is[i] DomC.empty).hi? = some hi ∧
        bds[i]? = some (lo, hi) := by
  unfold linExtractBounds at h
  cases ha : linExtractBoundsAux doms is.toList with
  | none =>
      rw [ha] at h
      simp at h
  | some rest =>
      rw [ha] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst bds
      have hs := linExtractBoundsAux_spec ha
      refine ⟨by simpa using hs.1, ?_⟩
      intro i hi
      have hi' : i < is.toList.length := by simpa using hi
      obtain ⟨lo, hi, hl, hh, hb⟩ := hs.2 i hi'
      refine ⟨lo, hi, hl, hh, ?_⟩
      rw [← Array.getElem?_toList]
      exact hb

def linTermsAux : List Int → List Nat → List (Int × Int) → List LinTerm
  | c :: cs, s :: ss, (lo, hi) :: bds => ⟨c, s, lo, hi⟩ :: linTermsAux cs ss bds
  | _, _, _ => []

def linTerms (cs : Array Int) (slots : Array Nat) (bds : Array (Int × Int)) : List LinTerm :=
  linTermsAux cs.toList slots.toList bds.toList

theorem linTermsAux_getElem?_some {cs : List Int} {slots : List Nat}
    {bds : List (Int × Int)} :
    ∀ {i : Nat}, cs.length = slots.length → bds.length = slots.length →
      i < slots.length →
      ∃ c s lo hi, cs[i]? = some c ∧ slots[i]? = some s ∧
        bds[i]? = some (lo, hi) ∧
        (linTermsAux cs slots bds)[i]? = some ⟨c, s, lo, hi⟩
  | 0, h1, h2, hiLen => by
      cases cs with
      | nil => simp at h1; omega
      | cons c cs' =>
          cases slots with
          | nil => simp at hiLen
          | cons s ss =>
              cases bds with
              | nil => simp at h2
              | cons p bs =>
                  obtain ⟨lo, hi⟩ := p
                  exact ⟨c, s, lo, hi, by simp, by simp, by simp, by simp [linTermsAux]⟩
  | i + 1, h1, h2, hiLen => by
      cases cs with
      | nil => simp at h1; omega
      | cons c cs' =>
          cases slots with
          | nil => simp at hiLen
          | cons s ss =>
              cases bds with
              | nil => simp at h2
              | cons p bs =>
                  obtain ⟨lo, hi⟩ := p
                  have h1' : cs'.length = ss.length := by simpa using h1
                  have h2' : bs.length = ss.length := by simpa using h2
                  have hi' : i < ss.length := by simpa using hiLen
                  obtain ⟨c', s', lo', hi', hc, hs, hb, hterm⟩ :=
                    linTermsAux_getElem?_some h1' h2' hi'
                  exact ⟨c', s', lo', hi', by simp [hc], by simp [hs],
                    by simp [hb], by simp [linTermsAux, hterm]⟩

theorem linTermsAux_length {cs : List Int} {slots : List Nat}
    {bds : List (Int × Int)} (h1 : cs.length = slots.length)
    (h2 : bds.length = slots.length) :
    (linTermsAux cs slots bds).length = slots.length := by
  induction cs generalizing slots bds with
  | nil =>
      cases slots with
      | nil =>
          cases bds with
          | nil => rfl
          | cons p ps => simp at h2
      | cons s ss => simp at h1
  | cons c cs ih =>
      cases slots with
      | nil => simp at h1
      | cons s ss =>
          cases bds with
          | nil => simp at h2
          | cons p ps =>
              obtain ⟨lo, hi⟩ := p
              simp only [linTermsAux, List.length_cons]
              rw [ih (by simpa using h1) (by simpa using h2)]

theorem linTerms_length {cs : Array Int} {slots : Array Nat}
    {bds : Array (Int × Int)} (h1 : cs.size = slots.size) (h2 : bds.size = slots.size) :
    (linTerms cs slots bds).length = slots.size := by
  unfold linTerms
  rw [linTermsAux_length (by simpa using h1) (by simpa using h2)]
  simp

theorem linTerms_getElem?_some {cs : Array Int} {slots : Array Nat}
    {bds : Array (Int × Int)} (h1 : cs.size = slots.size) (h2 : bds.size = slots.size)
    {i : Nat} (hi : i < slots.size) :
    ∃ c s lo hi, cs[i]? = some c ∧ slots[i]? = some s ∧
      bds[i]? = some (lo, hi) ∧
      (linTerms cs slots bds)[i]? = some ⟨c, s, lo, hi⟩ := by
  have h1' : cs.toList.length = slots.toList.length := by simpa using h1
  have h2' : bds.toList.length = slots.toList.length := by simpa using h2
  have hi' : i < slots.toList.length := by simpa using hi
  obtain ⟨c, s, lo, hi, hc, hs, hb, ht⟩ :=
    linTermsAux_getElem?_some (cs := cs.toList) (slots := slots.toList)
      (bds := bds.toList) h1' h2' hi'
  refine ⟨c, s, lo, hi, ?_, ?_, ?_, ?_⟩
  · rw [← Array.getElem?_toList]; exact hc
  · rw [← Array.getElem?_toList]; exact hs
  · rw [← Array.getElem?_toList]; exact hb
  · unfold linTerms; exact ht

def linTotalMin : List LinTerm → Int
  | [] => 0
  | t :: ts => linTotalMin ts + t.min

def linDotSum : List LinTerm → Assignment → Int
  | [], _ => 0
  | t :: ts, a => linDotSum ts a + t.c * (slotInt a t.s).getD 0

def linConflictLits (terms : List LinTerm) : List Literal :=
  terms.map fun t => linMinNegLit t.s t.c t.lo t.hi

def linOtherLits (terms : List LinTerm) (i : Nat) : List Literal :=
  linConflictLits (terms.eraseIdx i)

def linOtherMin (terms : List LinTerm) (i : Nat) : Int :=
  linTotalMin (terms.eraseIdx i)

theorem linTotalMin_eq_eraseIdx_add {terms : List LinTerm} {i : Nat} {t : LinTerm}
    (h : terms[i]? = some t) :
    linTotalMin terms = linTotalMin (terms.eraseIdx i) + t.min := by
  induction terms generalizing i with
  | nil => simp at h
  | cons u us ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h
          subst t
          simp [linTotalMin]
      | succ k =>
          have hk : us[k]? = some t := by simpa using h
          have ih' := ih hk
          simp only [List.eraseIdx_cons_succ]
          rw [linTotalMin, linTotalMin, ih']
          omega

theorem linDotSum_eq_eraseIdx_add {terms : List LinTerm} {i : Nat} {t : LinTerm}
    {a : Assignment} {x : Int} (h : terms[i]? = some t)
    (hx : slotInt a t.s = some x) :
    linDotSum terms a = linDotSum (terms.eraseIdx i) a + t.c * x := by
  induction terms generalizing i with
  | nil => simp at h
  | cons u us ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h
          subst t
          simp [linDotSum, hx]
      | succ k =>
          have hk : us[k]? = some t := by simpa using h
          have ih' := ih hk
          simp only [List.eraseIdx_cons_succ]
          rw [linDotSum, linDotSum, ih']
          ac_rfl

theorem linMinNegLit_false_bound {t : LinTerm} {a : Assignment}
    (h : (linMinNegLit t.s t.c t.lo t.hi).eval a = some false) :
    ∃ x, slotInt a t.s = some x ∧ t.min ≤ t.c * x := by
  by_cases hc : 0 ≤ t.c
  · rw [linMinNegLit, if_pos hc] at h
    rw [eval_posLe_false_iff] at h
    obtain ⟨x, hx, hlt⟩ := h
    refine ⟨x, hx, ?_⟩
    have hle : t.lo ≤ x := by omega
    simp only [LinTerm.min, linTermMin, if_pos hc]
    exact Int.mul_le_mul_of_nonneg_left hle hc
  · have hc' : t.c ≤ 0 := by omega
    rw [linMinNegLit, if_neg hc] at h
    rw [eval_negLe_false_iff] at h
    obtain ⟨x, hx, hle⟩ := h
    refine ⟨x, hx, ?_⟩
    simp only [LinTerm.min, linTermMin, if_neg hc]
    exact Int.mul_le_mul_of_nonpos_left hc' hle

theorem linTotalMin_le_linDotSum (terms : List LinTerm) (a : Assignment)
    (hfalse : ∀ l ∈ linConflictLits terms, l.eval a = some false) :
    linTotalMin terms ≤ linDotSum terms a := by
  induction terms with
  | nil => simp [linTotalMin, linDotSum]
  | cons t ts ih =>
      have hhead : (linMinNegLit t.s t.c t.lo t.hi).eval a = some false :=
        hfalse _ (by simp [linConflictLits])
      have htail : ∀ l ∈ linConflictLits ts, l.eval a = some false := by
        intro l hl
        have hl' : l ∈ linConflictLits (t :: ts) := by
          simp only [linConflictLits, List.map_cons, List.mem_cons]
          exact Or.inr hl
        exact hfalse l hl'
      obtain ⟨x, hx, hbound⟩ := linMinNegLit_false_bound hhead
      have iht := ih htail
      have hsum : linTotalMin ts + t.min ≤ linDotSum ts a + t.c * x :=
        Int.add_le_add iht hbound
      simpa [linTotalMin, linDotSum, hx] using hsum

theorem goHoleHi_some_spec3 {lo hi : Int} {holes : Array Int} {v : Int}
    (hlo : ∀ h ∈ holes.toList, lo ≤ h)
    (hhi : ∀ h ∈ holes.toList, h ≤ hi)
    (hpair : holes.toList.Pairwise (fun a b => a < b))
    (h : DomC.hi?.goHoleHi lo holes hi 0 = some v) :
    lo ≤ v ∧ v ≤ hi ∧ v ∉ holes.toList := by
  have key : ∀ (m k : Nat) (v w : Int), holes.size - k = m → k ≤ holes.size →
      v = hi - (k : Int) →
      (∀ j, j < k → holes[holes.size - 1 - j]? = some (hi - (j : Int))) →
      DomC.hi?.goHoleHi lo holes v k = some w →
      lo ≤ w ∧ w ≤ hi ∧ w ∉ holes.toList := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro k v w hm hkle hv hinv hgo
      rw [DomC.hi?.goHoleHi.eq_1] at hgo
      by_cases hk : k < holes.size
      · rw [dif_pos hk] at hgo
        cases hget : holes[holes.size - 1 - k]? with
        | none =>
            rw [Array.getElem?_eq_none_iff] at hget
            omega
        | some h =>
            rw [hget] at hgo
            change (if (h == v) = true then
              DomC.hi?.goHoleHi lo holes (v - 1) (k + 1) else some v) = some w at hgo
            by_cases heq : (h == v) = true
            · rw [if_pos heq] at hgo
              have hv' : v - 1 = hi - ((k + 1 : Nat) : Int) := by omega
              have hinv' : ∀ j, j < k + 1 →
                  holes[holes.size - 1 - j]? = some (hi - (j : Int)) := by
                intro j hj
                by_cases hjk : j < k
                · exact hinv j hjk
                · have hjeq : j = k := by omega
                  subst hjeq
                  rw [hget]
                  have hhv : h = v := beq_iff_eq.mp heq
                  rw [hhv, hv]
              have hm' : holes.size - (k + 1) < m := by omega
              exact ih (holes.size - (k + 1)) hm' (k + 1) (v - 1) w (by omega)
                (by omega) hv' hinv' hgo
            · rw [if_neg heq] at hgo
              have hwv : w = v := (Option.some.inj hgo).symm
              subst w
              have hmemh : h ∈ holes.toList :=
                Array.mem_toList_iff.mpr (Array.mem_of_getElem? hget)
              have hvhi : v ≤ hi := by omega
              have hleh : h ≤ v := by
                by_cases hk0 : k = 0
                · subst hk0
                  have := hhi h hmemh
                  omega
                · have hidx : holes.size - 1 - (k - 1) = holes.size - k := by omega
                  have hprev := hinv (k - 1) (by omega)
                  rw [hidx] at hprev
                  have hprev' : holes[holes.size - k]? = some (v + 1) := by
                    rw [hprev]
                    congr 1
                    omega
                  have hgetprev : holes[holes.size - k] = v + 1 := by
                    rw [Array.getElem?_eq_getElem (by omega)] at hprev'
                    exact Option.some.inj hprev'
                  have hgetcur : holes[holes.size - 1 - k] = h := by
                    rw [Array.getElem?_eq_getElem (by omega)] at hget
                    exact Option.some.inj hget
                  have hlt := array_lt_of_pairwise (a := holes) hpair
                    (i := holes.size - 1 - k) (j := holes.size - k)
                    (by omega) (by omega) (by omega)
                  rw [hgetcur, hgetprev] at hlt
                  omega
              have hlov : lo ≤ v := by
                have := hlo h hmemh
                omega
              refine ⟨hlov, hvhi, ?_⟩
              intro hvmem
              obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.mp hvmem
              have hjsize : j < holes.size := by simpa using hj
              have hval : holes[j] = v := by simpa using hjv
              have hgetcur : holes[holes.size - 1 - k] = h := by
                rw [Array.getElem?_eq_getElem (by omega)] at hget
                exact Option.some.inj hget
              by_cases hjk : j < holes.size - 1 - k
              · have hlt := array_lt_of_pairwise (a := holes) hpair hjsize (by omega) hjk
                rw [hval, hgetcur] at hlt
                omega
              · by_cases hjeq : j = holes.size - 1 - k
                · have hveq : v = h := by
                    have hvj : holes[j]? = some v := by
                      rw [Array.getElem?_eq_getElem hjsize]
                      exact congrArg some hval
                    have hsome : some v = some h := by
                      rw [← hvj, hjeq]
                      exact hget
                    exact Option.some.inj hsome
                  exact heq (by rw [beq_iff_eq]; exact hveq.symm)
                · have hjg : holes.size - 1 - k < j := by omega
                  have hidx : holes.size - 1 - j < k := by omega
                  have hproc := hinv (holes.size - 1 - j) hidx
                  have hidx2 : holes.size - 1 - (holes.size - 1 - j) = j := by omega
                  rw [hidx2] at hproc
                  have hvalproc : holes[j] = hi - ((holes.size - 1 - j : Nat) : Int) := by
                    rw [Array.getElem?_eq_getElem hjsize] at hproc
                    exact Option.some.inj hproc
                  rw [hval] at hvalproc
                  omega
      · rw [dif_neg hk] at hgo
        have hkeq : k = holes.size := by omega
        subst hkeq
        by_cases hlv : lo ≤ v
        · rw [if_pos hlv] at hgo
          have hwv : w = v := (Option.some.inj hgo).symm
          subst w
          refine ⟨hlv, by omega, ?_⟩
          intro hvmem
          obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.mp hvmem
          have hjsize : j < holes.size := by simpa using hj
          have hval : holes[j] = v := by simpa using hjv
          have hidx : holes.size - 1 - j < holes.size := by omega
          have hproc := hinv (holes.size - 1 - j) hidx
          have hidx2 : holes.size - 1 - (holes.size - 1 - j) = j := by omega
          rw [hidx2] at hproc
          have hvalproc : holes[j] = hi - ((holes.size - 1 - j : Nat) : Int) := by
            rw [Array.getElem?_eq_getElem hjsize] at hproc
            exact Option.some.inj hproc
          rw [hval] at hvalproc
          omega
        · rw [if_neg hlv] at hgo
          cases hgo
  exact key holes.size 0 hi v (by omega) (by omega) (by simp) (by intro j hj; omega) h

theorem DomC.lo?_le_hi? (d : DomC) (hWF : d.WF) {lo hi : Int}
    (hlo : d.lo? = some lo) (hhi : d.hi? = some hi) : lo ≤ hi := by
  cases d with
  | bool bits =>
      rw [DomC.lo?.eq_1] at hlo
      rw [DomC.hi?.eq_1] at hhi
      split at hlo <;> split at hhi <;> simp_all <;> omega
  | bounds blo bhi =>
      rw [DomC.lo?.eq_2] at hlo
      rw [DomC.hi?.eq_2] at hhi
      split at hlo <;> split at hhi <;> simp_all <;> omega
  | bitset blo words =>
      rw [DomC.lo?.eq_3] at hlo
      rw [DomC.hi?.eq_3] at hhi
      have hm : (DomC.bitset blo words).mem (.int lo) = true :=
        bitset_mem_int_of_lo?_eq hlo
      have hle := DomC.le_hi? (.bitset blo words) hWF hhi hm
      simpa [iv, Value.intView] using hle
  | boundsHoles blo bhi holes =>
      rw [DomC.lo?.eq_4] at hlo
      rw [DomC.hi?.eq_4] at hhi
      by_cases hlt : decide (bhi < blo) = true
      · rw [if_pos hlt] at hlo
        cases hlo
      · rw [if_neg hlt] at hlo
        rw [if_neg hlt] at hhi
        have hpair := hWF.1
        have hrange_lo : ∀ h ∈ holes.toList, blo ≤ h := fun h hh => (hWF.2 h hh).1
        have hrange_hi : ∀ h ∈ holes.toList, h ≤ bhi := fun h hh => (hWF.2 h hh).2
        have hspec := goHoleHi_some_spec3 (lo := blo) (hi := bhi) hrange_lo hrange_hi hpair hhi
        by_cases hle : lo ≤ hi
        · exact hle
        · exfalso
          have hhiLt : hi < lo := by omega
          have hspecLo := goHoleLo_some_spec bhi holes holes.size 0 blo lo (by omega) hlo
          have hmem : hi ∈ holes.toList := hspecLo.2 hi hspec.1 (by omega)
          exact hspec.2.2 hmem

theorem slotInt_eq_some_of_getElem!_int {a : Assignment} {s : Nat} {x : Int}
    (h : a[s]! = .int x) : slotInt a s = some x := by
  rw [List.getElem!_eq_getElem?_getD] at h
  cases hs : a[s]? with
  | none =>
      simp only [hs, Option.getD_none] at h
      change (Value.bool false) = Value.int x at h
      cases h
  | some v =>
      simp only [hs, Option.getD_some] at h
      simp [slotInt, hs, h, Value.intView]

theorem dotProduct_reads_int_local {vals : List Value} {is : List Nat} {d : Int}
    {a : Assignment}
    (hd : dotProduct vals (is.map (fun i => a[i]!)) = some d) :
    ∀ s ∈ is, ∃ x, a[s]! = .int x := by
  induction vals generalizing is d with
  | nil =>
      intro s hs
      cases is with
      | nil => simp at hs
      | cons u us =>
          simp [dotProduct] at hd
  | cons v vs ih =>
      intro s hs
      cases is with
      | nil => simp at hs
      | cons u us =>
          cases v with
          | int c =>
              rw [List.map_cons] at hd
              cases hu : a[u]! with
              | int x =>
                  rw [hu] at hd
                  rw [dotProduct.eq_1] at hd
                  cases hrest : dotProduct vs (us.map (fun i => a[i]!)) with
                  | none => rw [hrest] at hd; cases hd
                  | some e =>
                      have hdrest : dotProduct vs (us.map (fun i => a[i]!)) = some e := hrest
                      rcases List.mem_cons.mp hs with rfl | hs'
                      · exact ⟨x, hu⟩
                      · exact ih hdrest s hs'
              | bool b =>
                  rw [hu] at hd
                  rw [show dotProduct (Value.int c :: vs)
                    (Value.bool b :: us.map (fun i => a[i]!)) = none from rfl] at hd
                  cases hd
              | setOfInt t =>
                  rw [hu] at hd
                  rw [show dotProduct (Value.int c :: vs)
                    (Value.setOfInt t :: us.map (fun i => a[i]!)) = none from rfl] at hd
                  cases hd
              | array t =>
                  rw [hu] at hd
                  rw [show dotProduct (Value.int c :: vs)
                    (Value.array t :: us.map (fun i => a[i]!)) = none from rfl] at hd
                  cases hd
          | bool b =>
              rw [List.map_cons] at hd
              rw [show dotProduct (Value.bool b :: vs)
                (a[u]! :: us.map (fun i => a[i]!)) = none from rfl] at hd
              cases hd
          | setOfInt t =>
              rw [List.map_cons] at hd
              rw [show dotProduct (Value.setOfInt t :: vs)
                (a[u]! :: us.map (fun i => a[i]!)) = none from rfl] at hd
              cases hd
          | array t =>
              rw [List.map_cons] at hd
              rw [show dotProduct (Value.array t :: vs)
                (a[u]! :: us.map (fun i => a[i]!)) = none from rfl] at hd
              cases hd

theorem dotProduct_linTermsAux (cs : List Int) (slots : List Nat)
    (bds : List (Int × Int)) (h1 : cs.length = slots.length)
    (h2 : bds.length = slots.length) (a : Assignment)
    (hx : ∀ s ∈ slots, ∃ x, a[s]! = .int x) :
    dotProduct (intVals cs) (slots.map (fun s => a[s]!)) =
      some (linDotSum (linTermsAux cs slots bds) a) := by
  induction cs generalizing slots bds with
  | nil =>
      cases slots with
      | nil =>
          cases bds with
          | nil => rw [List.map_nil, intVals, dotProduct.eq_2]; simp [linTermsAux, linDotSum]
          | cons p ps => simp at h2
      | cons s ss => simp at h1
  | cons c cs ih =>
      cases slots with
      | nil => simp at h1
      | cons s ss =>
          cases bds with
          | nil => simp at h2
          | cons p bs =>
              obtain ⟨lo, hi⟩ := p
              have h1' : cs.length = ss.length := by simpa using h1
              have h2' : bs.length = ss.length := by simpa using h2
              obtain ⟨x, hx0⟩ := hx s (by simp)
              have hget : a[s]! = .int x := hx0
              have hsx : slotInt a s = some x := slotInt_eq_some_of_getElem!_int hget
              have hx' : ∀ t ∈ ss, ∃ y, a[t]! = .int y := by
                intro t ht
                exact hx t (List.mem_cons_of_mem s ht)
              have hrec := ih ss bs h1' h2' hx'
              rw [List.map_cons, hget]
              simp only [intVals]
              rw [dotProduct.eq_1, hrec]
              simp only [Option.some.injEq]
              simp [linTermsAux, linDotSum, hsx]
              omega

theorem dotProduct_eq_linDotSum {cs : Array Int} {slots : Array Nat}
    {bds : Array (Int × Int)} (h1 : cs.size = slots.size) (h2 : bds.size = slots.size)
    (a : Assignment) (hx : ∀ s ∈ slots.toList, ∃ x, a[s]! = .int x) :
    dotProduct (intVals cs.toList) (slots.toList.map (fun s => a[s]!)) =
      some (linDotSum (linTerms cs slots bds) a) := by
  unfold linTerms
  exact dotProduct_linTermsAux cs.toList slots.toList bds.toList
    (by simpa using h1) (by simpa using h2) a hx

theorem linTerms_slot_mem {cs : Array Int} {slots : Array Nat}
    {bds : Array (Int × Int)} {t : LinTerm} (h1 : cs.size = slots.size)
    (h2 : bds.size = slots.size) (ht : t ∈ linTerms cs slots bds) :
    t.s ∈ slots.toList := by
  unfold linTerms at ht
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp ht
  have hlen : (linTermsAux cs.toList slots.toList bds.toList).length =
      slots.toList.length :=
    linTermsAux_length (by simpa using h1) (by simpa using h2)
  have hi' : i < slots.toList.length := by rw [← hlen]; exact hi
  have hterm : (linTermsAux cs.toList slots.toList bds.toList)[i]? = some t := by
    rw [List.getElem?_eq_getElem hi]
    exact congrArg some hget
  obtain ⟨c, s, lo, hi2, hc, hs, hb, hteq⟩ :=
    linTermsAux_getElem?_some (cs := cs.toList) (slots := slots.toList)
      (bds := bds.toList) (by simpa using h1) (by simpa using h2) hi'
  have ht_eq : t = ⟨c, s, lo, hi2⟩ := Option.some.inj (hterm.symm.trans hteq)
  rw [ht_eq]
  obtain ⟨hilt, hgetslot⟩ := List.getElem?_eq_some_iff.mp hs
  rw [← hgetslot]
  exact List.getElem_mem hilt

theorem linTermMin_le_value {d : DomC} (hWF : d.WF) {c lo hi : Int}
    (hlo : d.lo? = some lo) (hhi : d.hi? = some hi)
    {v : Value} (hm : d.mem v = true) {x : Int} (hx : Value.intView v = some x) :
    linTermMin c lo hi ≤ c * x := by
  have hvx : iv v = x := iv_of_intView hx
  by_cases hc : 0 ≤ c
  · have hle : lo ≤ x := by
      have := DomC.lo?_le d hWF hlo hm
      simpa [hvx] using this
    simp [linTermMin, hc]
    exact Int.mul_le_mul_of_nonneg_left hle hc
  · have hc' : c ≤ 0 := by omega
    have hle : x ≤ hi := by
      have := DomC.le_hi? d hWF hhi hm
      simpa [hvx] using this
    simp [linTermMin, hc]
    exact Int.mul_le_mul_of_nonpos_left hc' hle

theorem linPrunePos_lo_le {terms : List LinTerm} {i : Nat} {t : LinTerm} {b : Int}
    (hterm : terms[i]? = some t) (hpos : 0 < t.c)
    (hb : linTotalMin terms ≤ b) :
    t.lo ≤ (b - linOtherMin terms i) / t.c := by
  have hsplit := linTotalMin_eq_eraseIdx_add hterm
  have hmin : t.min = t.c * t.lo := by
    have hc : 0 ≤ t.c := Int.le_of_lt hpos
    simp [LinTerm.min, linTermMin, hc]
  have hle : t.c * t.lo ≤ b - linOtherMin terms i := by
    unfold linOtherMin
    omega
  rw [Int.le_ediv_iff_mul_le hpos, Int.mul_comm]
  exact hle

theorem negMulNegSubOne (q m : Int) : (-m) * (-q - 1) = (q + 1) * m := by
  have h : -q - 1 = -(q + 1) := by omega
  rw [h, Int.neg_mul_neg, Int.mul_comm]

theorem linPruneNeg_newLo_le_hi {terms : List LinTerm} {i : Nat} {t : LinTerm}
    {b : Int} (hterm : terms[i]? = some t) (hneg : t.c < 0)
    (hb : linTotalMin terms ≤ b) :
    -((b - linOtherMin terms i) / (-t.c)) ≤ t.hi := by
  have hm : 0 < -t.c := by omega
  have hsplit := linTotalMin_eq_eraseIdx_add hterm
  have hmin : t.min = t.c * t.hi := by
    have hc : ¬ 0 ≤ t.c := by omega
    simp [LinTerm.min, linTermMin, hc]
  have hle : t.c * t.hi ≤ b - linOtherMin terms i := by
    unfold linOtherMin
    omega
  have hceil : -t.hi ≤ (b - linOtherMin terms i) / (-t.c) := by
    rw [Int.le_ediv_iff_mul_le hm]
    have hmul : -t.hi * (-t.c) = t.c * t.hi := by
      rw [Int.neg_mul_neg, Int.mul_comm t.hi t.c]
    rwa [hmul]
  omega

theorem linPrunePos_newHi_lt_mul {c newHi x b other : Int}
    (hpos : 0 < c) (hnew : newHi = (b - other) / c) (hx : newHi < x) :
    b - other < c * x := by
  have hx1 : newHi + 1 ≤ x := by omega
  have hstep : (newHi + 1) * c ≤ x * c :=
    Int.mul_le_mul_of_nonneg_right hx1 (Int.le_of_lt hpos)
  rw [Int.mul_comm x c] at hstep
  have hlt := Int.lt_ediv_add_one_mul_self (b - other) hpos
  rw [← hnew] at hlt
  exact Int.lt_of_lt_of_le hlt hstep

theorem linPruneNeg_mul_lt {c newLo x b other : Int}
    (hneg : c < 0) (hnew : newLo = -((b - other) / (-c)))
    (hx : x ≤ newLo - 1) :
    b - other < c * x := by
  have hm : 0 < -c := by omega
  have hstep : c * (newLo - 1) ≤ c * x :=
    Int.mul_le_mul_of_nonpos_left (Int.le_of_lt hneg) hx
  have heq : c * (newLo - 1) = (((b - other) / (-c)) + 1) * (-c) := by
    calc
      c * (newLo - 1) = (-(-c)) * (-((b - other) / (-c)) - 1) := by
        rw [hnew]
        congr 1
        omega
      _ = (((b - other) / (-c)) + 1) * (-c) :=
        negMulNegSubOne ((b - other) / (-c)) (-c)
  have hlt := Int.lt_ediv_add_one_mul_self (b - other) hm
  rw [← heq] at hlt
  exact Int.lt_of_lt_of_le hlt hstep

def linPrunes (terms : List LinTerm) (b : Int) : List (Literal × Clause) :=
  (List.range terms.length).filterMap fun i =>
    match terms[i]? with
    | none => none
    | some t =>
        let otherMin := linOtherMin terms i
        if 0 < t.c then
          let newHi := (b - otherMin) / t.c
          if newHi < t.hi then
            some (posLe t.s newHi, linOtherLits terms i ++ [posLe t.s newHi])
          else none
        else if t.c < 0 then
          let newLo := -((b - otherMin) / (-t.c))
          if t.lo < newLo then
            some (negLe t.s (newLo - 1), linOtherLits terms i ++ [negLe t.s (newLo - 1)])
          else none
        else none

/-- Runtime twin of `linPrunes`: one total instead of a per-term
`linOtherMin` sum and O(1) term lookups, so a run is linear in the number
of terms (plus the reasons it emits).  `@[csimp]` swaps it in for the
compiled code only. -/
def linPrunesFast (terms : List LinTerm) (b : Int) : List (Literal × Clause) :=
  let arr := terms.toArray
  let total := linTotalMin terms
  (List.range terms.length).filterMap fun i =>
    match arr[i]? with
    | none => none
    | some t =>
        let otherMin := total - t.min
        if 0 < t.c then
          let newHi := (b - otherMin) / t.c
          if newHi < t.hi then
            some (posLe t.s newHi, linOtherLits terms i ++ [posLe t.s newHi])
          else none
        else if t.c < 0 then
          let newLo := -((b - otherMin) / (-t.c))
          if t.lo < newLo then
            some (negLe t.s (newLo - 1), linOtherLits terms i ++ [negLe t.s (newLo - 1)])
          else none
        else none

@[csimp] theorem linPrunes_eq_fast : @linPrunes = @linPrunesFast := by
  funext terms b
  unfold linPrunes linPrunesFast
  congr 1
  funext i
  simp only [List.getElem?_toArray]
  cases h : terms[i]? with
  | none => rfl
  | some t =>
      have hsum := linTotalMin_eq_eraseIdx_add h
      have ho : linOtherMin terms i = linTotalMin terms - t.min := by
        unfold linOtherMin; omega
      simp only [ho]

theorem linPrunes_mem {terms : List LinTerm} {b : Int} {l : Literal} {reason : Clause}
    (h : (l, reason) ∈ linPrunes terms b) :
    ∃ i t, terms[i]? = some t ∧
      ((0 < t.c ∧
          l = posLe t.s ((b - linOtherMin terms i) / t.c) ∧
          ((b - linOtherMin terms i) / t.c) < t.hi ∧
          reason = linOtherLits terms i ++ [l]) ∨
        (¬ 0 < t.c ∧ t.c < 0 ∧
          l = negLe t.s (-((b - linOtherMin terms i) / (-t.c)) - 1) ∧
          t.lo < -((b - linOtherMin terms i) / (-t.c)) ∧
          reason = linOtherLits terms i ++ [l])) := by
  unfold linPrunes at h
  rw [List.mem_filterMap] at h
  obtain ⟨i, hi, hf⟩ := h
  rw [List.mem_range] at hi
  cases hterm : terms[i]? with
  | none => simp [hterm] at hf
  | some t =>
      simp only [hterm] at hf
      split at hf
      · rename_i hpos
        split at hf
        · rename_i hlt
          have hpair : (posLe t.s ((b - linOtherMin terms i) / t.c),
              linOtherLits terms i ++ [posLe t.s ((b - linOtherMin terms i) / t.c)]) =
              (l, reason) := Option.some.inj hf
          have hl : l = posLe t.s ((b - linOtherMin terms i) / t.c) :=
            (congrArg Prod.fst hpair).symm
          have hr : reason = linOtherLits terms i ++
              [posLe t.s ((b - linOtherMin terms i) / t.c)] :=
            (congrArg Prod.snd hpair).symm
          rw [← hl] at hr
          exact ⟨i, t, hterm, Or.inl ⟨hpos, hl, hlt, hr⟩⟩
        · simp at hf
      · rename_i hnotpos
        split at hf
        · rename_i hneg
          split at hf
          · rename_i hlt
            have hpair : (negLe t.s (-((b - linOtherMin terms i) / (-t.c)) - 1),
                linOtherLits terms i ++ [negLe t.s (-((b - linOtherMin terms i) / (-t.c)) - 1)]) =
                (l, reason) := Option.some.inj hf
            have hl : l = negLe t.s (-((b - linOtherMin terms i) / (-t.c)) - 1) :=
              (congrArg Prod.fst hpair).symm
            have hr : reason = linOtherLits terms i ++
                [negLe t.s (-((b - linOtherMin terms i) / (-t.c)) - 1)] :=
              (congrArg Prod.snd hpair).symm
            rw [← hl] at hr
            exact ⟨i, t, hterm, Or.inr ⟨hnotpos, hneg, hl, hlt, hr⟩⟩
          · simp at hf
        · simp at hf

end LeanFzn.Engine

namespace LeanFzn.Engine

theorem accepts_satisfiedB {p : CompiledProblem DomConstraint} {a : Assignment}
    {dc : DomConstraint} (hacc : accepts p a = true) (hmem : dc ∈ p.constraints) :
    dc.satisfiedB a = true :=
  List.all_eq_true.mp hacc dc hmem

theorem eval_posLe_some {a : Assignment} {s : Nat} {k : Int} {x : Int}
    (hx : slotInt a s = some x) :
    ∃ z, (posLe s k).eval a = some z := by
  refine ⟨decide (x ≤ k), ?_⟩
  simp [posLe, Literal.eval, Atom.eval, hx]

theorem eval_negLe_some {a : Assignment} {s : Nat} {k : Int} {x : Int}
    (hx : slotInt a s = some x) :
    ∃ z, (negLe s k).eval a = some z := by
  refine ⟨!decide (x ≤ k), ?_⟩
  simp [negLe, Literal.eval, Atom.eval, hx]

theorem posLe_eval_false_of_not_true {a : Assignment} {s : Nat} {k : Int} {x : Int}
    (hx : slotInt a s = some x) (h : (posLe s k).eval a ≠ some true) :
    (posLe s k).eval a = some false := by
  obtain ⟨z, hz⟩ := eval_posLe_some (k := k) hx
  cases z with
  | false => exact hz
  | true => exact absurd hz h

theorem negLe_eval_false_of_not_true {a : Assignment} {s : Nat} {k : Int} {x : Int}
    (hx : slotInt a s = some x) (h : (negLe s k).eval a ≠ some true) :
    (negLe s k).eval a = some false := by
  obtain ⟨z, hz⟩ := eval_negLe_some (k := k) hx
  cases z with
  | false => exact hz
  | true => exact absurd hz h

theorem linMinNegLit_eval_false_of_not_true {t : LinTerm} {a : Assignment} {x : Int}
    (hx : slotInt a t.s = some x)
    (h : (linMinNegLit t.s t.c t.lo t.hi).eval a ≠ some true) :
    (linMinNegLit t.s t.c t.lo t.hi).eval a = some false := by
  by_cases hc : 0 ≤ t.c
  · rw [linMinNegLit, if_pos hc]
    exact posLe_eval_false_of_not_true hx (by rwa [linMinNegLit, if_pos hc] at h)
  · rw [linMinNegLit, if_neg hc]
    exact negLe_eval_false_of_not_true hx (by rwa [linMinNegLit, if_neg hc] at h)

theorem linMinNegLit_evalLit_false {d : DomC} (hWF : d.WF)
    {s : Nat} {c lo hi : Int} (hlo : d.lo? = some lo) (hhi : d.hi? = some hi) :
    d.evalLit (linMinNegLit s c lo hi) = some false := by
  have hle := DomC.lo?_le_hi? d hWF hlo hhi
  by_cases hc : 0 ≤ c
  · rw [linMinNegLit, if_pos hc]
    simp only [DomC.evalLit, posLe, hlo, hhi, ↓reduceIte]
    rw [if_neg (by omega), if_pos (by omega)]
  · rw [linMinNegLit, if_neg hc]
    simp only [DomC.evalLit, negLe, hlo, hhi, Bool.false_eq_true, ↓reduceIte]
    rw [if_neg (by omega), if_pos (by omega)]

theorem evalLit_posLe_none {d : DomC} {s : Nat} {k lo hi : Int}
    (hlo : d.lo? = some lo) (hhi : d.hi? = some hi)
    (hlok : lo ≤ k) (hhik : k < hi) : d.evalLit (posLe s k) = none := by
  simp only [DomC.evalLit, posLe, hlo, hhi, ↓reduceIte]
  rw [if_neg (by omega), if_neg (by omega)]

theorem evalLit_negLe_none {d : DomC} {s : Nat} {k lo hi : Int}
    (hlo : d.lo? = some lo) (hhi : d.hi? = some hi)
    (hlok : lo ≤ k) (hhik : k < hi) : d.evalLit (negLe s k) = none := by
  simp only [DomC.evalLit, negLe, hlo, hhi, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg (by omega), if_neg (by omega)]

def ViewWF (view : EngineView) (slots : Array Nat) : Prop :=
  ∀ (i : Nat) (h : i < slots.size), (view.doms.getD slots[i] DomC.empty).WF

theorem ViewWF.dom_wf {view : EngineView} {slots : Array Nat} (h : ViewWF view slots)
    {s : Nat} (hs : s ∈ slots.toList) :
    (view.doms.getD s DomC.empty).WF := by
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hs
  have hlt : i < slots.size := by simpa using hi
  have hsi : slots[i] = s := by
    have hq : slots[i]? = some s := by
      rw [Array.getElem?_eq_getElem hlt]
      exact congrArg some hget
    rw [Array.getElem?_eq_getElem hlt] at hq
    exact Option.some.inj hq
  have hwf := h i hlt
  simpa [hsi] using hwf

theorem linTerms_mem_bounds {cs : Array Int} {slots : Array Nat}
    {bds : Array (Int × Int)} {doms : Array DomC}
    (h1 : cs.size = slots.size) (hbds : linExtractBounds doms slots = some bds)
    {t : LinTerm} (ht : t ∈ linTerms cs slots bds) :
    (doms.getD t.s DomC.empty).lo? = some t.lo ∧
      (doms.getD t.s DomC.empty).hi? = some t.hi := by
  have hsize := (linExtractBounds_spec hbds).1
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp ht
  have hlen : (linTerms cs slots bds).length = slots.size := linTerms_length h1 hsize
  have hi' : i < slots.size := by rw [← hlen]; exact hi
  have hterm : (linTerms cs slots bds)[i]? = some t := by
    rw [List.getElem?_eq_getElem hi]
    exact congrArg some hget
  obtain ⟨c, s, lo, hi2, hc, hs, hb, hte⟩ := linTerms_getElem?_some h1 hsize hi'
  have ht_eq : t = ⟨c, s, lo, hi2⟩ := Option.some.inj (hterm.symm.trans hte)
  subst ht_eq
  obtain ⟨lo', hi', hlo, hhi, hbd⟩ := (linExtractBounds_spec hbds).2 i hi'
  have hp : (lo, hi2) = (lo', hi') := Option.some.inj (hb.symm.trans hbd)
  injection hp with h1' h2'
  subst h1'
  subst h2'
  have hsi : slots[i] = s := by
    rw [Array.getElem?_eq_getElem hi'] at hs
    exact Option.some.inj hs
  simpa [hsi] using And.intro hlo hhi

end LeanFzn.Engine

namespace LeanFzn.Engine

/-- Any accepted assignment satisfies the linear budget, expressed on the
extracted term list.  This is the arithmetic bridge used by the conflict
proof (`linConflict_entailed`) and by N9. -/
theorem dot_ge_totalMin (p : CompiledProblem DomConstraint)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linLe coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (a : Assignment) (hacc : accepts p a = true) :
    linDotSum (linTerms coeffs.toArray is.toArray bds) a ≤ b := by
  have hbdsize : bds.size = is.toArray.size := (linExtractBounds_spec hbds).1
  have hdc : (DomConstraint.linLe coeffs is b).satisfiedB a = true :=
    accepts_satisfiedB hacc hmem
  have hdotle : dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b = true := by
    simpa [DomConstraint.satisfiedB] using hdc
  obtain ⟨d, hd, hdle⟩ := (dotLe_eq _ _ _).mp hdotle
  have hint : ∀ s ∈ is, ∃ x, a[s]! = .int x := dotProduct_reads_int_local hd
  have hxall : ∀ s ∈ is.toArray.toList, ∃ x, a[s]! = .int x := by
    intro s hs
    exact hint s (by simpa using hs)
  have hbridge := dotProduct_eq_linDotSum (cs := coeffs.toArray) (slots := is.toArray)
    (bds := bds) hsize hbdsize a hxall
  rw [hd] at hbridge
  have hd_eq : d = linDotSum (linTerms coeffs.toArray is.toArray bds) a :=
    Option.some.inj hbridge
  omega

theorem linConflict_entailed (p : CompiledProblem DomConstraint)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linLe coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hconf : b < linTotalMin (linTerms coeffs.toArray is.toArray bds)) :
    Entailed p (linConflictLits (linTerms coeffs.toArray is.toArray bds)) := by
  intro a ha hacc
  have hbdsize : bds.size = is.toArray.size := (linExtractBounds_spec hbds).1
  have hdc : (DomConstraint.linLe coeffs is b).satisfiedB a = true :=
    accepts_satisfiedB hacc hmem
  have hdotle : dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b = true := by
    simpa [DomConstraint.satisfiedB] using hdc
  obtain ⟨d, hd, hdle⟩ := (dotLe_eq _ _ _).mp hdotle
  have hint : ∀ s ∈ is, ∃ x, a[s]! = .int x := dotProduct_reads_int_local hd
  apply Classical.byContradiction
  intro hno
  have hnotTrue : ∀ l ∈ linConflictLits (linTerms coeffs.toArray is.toArray bds),
      l.eval a ≠ some true := by
    intro l hl htrue
    exact hno ⟨l, hl, htrue⟩
  have hfalse : ∀ l ∈ linConflictLits (linTerms coeffs.toArray is.toArray bds),
      l.eval a = some false := by
    intro l hl
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hl
    have htmem : t.s ∈ is := by
      have := linTerms_slot_mem (cs := coeffs.toArray) (slots := is.toArray)
        (bds := bds) hsize hbdsize ht
      simpa using this
    obtain ⟨x, hxint⟩ := hint t.s htmem
    exact linMinNegLit_eval_false_of_not_true (slotInt_eq_some_of_getElem!_int hxint)
      (hnotTrue _ hl)
  have hle1 := linTotalMin_le_linDotSum (linTerms coeffs.toArray is.toArray bds) a hfalse
  have hxall : ∀ s ∈ is.toArray.toList, ∃ x, a[s]! = .int x := by
    intro s hs
    exact hint s (by simpa using hs)
  have hbridge := dotProduct_eq_linDotSum (cs := coeffs.toArray) (slots := is.toArray)
    (bds := bds) hsize hbdsize a hxall
  rw [hd] at hbridge
  have hd_eq : d = linDotSum (linTerms coeffs.toArray is.toArray bds) a :=
    Option.some.inj hbridge
  have htot : linTotalMin (linTerms coeffs.toArray is.toArray bds) ≤ b := by
    calc
      linTotalMin (linTerms coeffs.toArray is.toArray bds)
          ≤ linDotSum (linTerms coeffs.toArray is.toArray bds) a := hle1
      _ = d := hd_eq.symm
      _ ≤ b := hdle
  omega

end LeanFzn.Engine

namespace LeanFzn.Engine

theorem linPrunes_sound (p : CompiledProblem DomConstraint)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linLe coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds) :
    ∀ (l : Literal) (reason : Clause),
      (l, reason) ∈ linPrunes (linTerms coeffs.toArray is.toArray bds) b →
      Entailed p reason := by
  intro l reason hprune a ha hacc
  let terms := linTerms coeffs.toArray is.toArray bds
  have hbdsize : bds.size = is.toArray.size := (linExtractBounds_spec hbds).1
  have hdc : (DomConstraint.linLe coeffs is b).satisfiedB a = true :=
    accepts_satisfiedB hacc hmem
  have hdotle : dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b = true := by
    simpa [DomConstraint.satisfiedB] using hdc
  obtain ⟨d, hd, hdle⟩ := (dotLe_eq _ _ _).mp hdotle
  have hint : ∀ s ∈ is, ∃ x, a[s]! = .int x := dotProduct_reads_int_local hd
  have hxall : ∀ s ∈ is.toArray.toList, ∃ x, a[s]! = .int x := by
    intro s hs
    exact hint s (by simpa using hs)
  have hbridge := dotProduct_eq_linDotSum (cs := coeffs.toArray) (slots := is.toArray)
    (bds := bds) hsize hbdsize a hxall
  rw [hd] at hbridge
  have hd_eq : d = linDotSum terms a := Option.some.inj hbridge
  have hslot_mem : ∀ u ∈ terms, u.s ∈ is := by
    intro u hu
    have := linTerms_slot_mem (cs := coeffs.toArray) (slots := is.toArray)
      (bds := bds) hsize hbdsize hu
    simpa using this
  have hall_int : ∀ u ∈ terms, ∃ x, slotInt a u.s = some x := by
    intro u hu
    obtain ⟨x, hx⟩ := hint u.s (hslot_mem u hu)
    exact ⟨x, slotInt_eq_some_of_getElem!_int hx⟩
  obtain ⟨i, t, hterm, hbranch⟩ := linPrunes_mem hprune
  have ht : t ∈ terms := by
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hterm
    exact List.mem_iff_getElem.mpr ⟨i, hlt, hget⟩
  apply Classical.byContradiction
  intro hno
  have hnotTrue : ∀ q ∈ reason, q.eval a ≠ some true := by
    intro q hq htrue
    exact hno ⟨q, hq, htrue⟩
  have hotherFalse : ∀ q ∈ linOtherLits terms i, q.eval a = some false := by
    intro q hq
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (by
      simpa [linOtherLits, linConflictLits] using hq)
    have hu' : u ∈ terms := List.mem_of_mem_eraseIdx hu
    obtain ⟨x, hx⟩ := hall_int u hu'
    have hqOther : linMinNegLit u.s u.c u.lo u.hi ∈ linOtherLits terms i :=
      List.mem_map.mpr ⟨u, hu, rfl⟩
    have hqReason : linMinNegLit u.s u.c u.lo u.hi ∈ reason := by
      rcases hbranch with ⟨_, _, _, hreason⟩ | ⟨_, _, _, _, hreason⟩
      · rw [hreason]
        exact List.mem_append_left _ hqOther
      · rw [hreason]
        exact List.mem_append_left _ hqOther
    exact linMinNegLit_eval_false_of_not_true hx (hnotTrue _ hqReason)
  have hother := linTotalMin_le_linDotSum (terms.eraseIdx i) a (by
    intro q hq
    exact hotherFalse q (by simpa [linOtherLits] using hq))
  have hx : ∃ x, slotInt a t.s = some x := hall_int t ht
  obtain ⟨xt, hxt⟩ := hx
  have hsplit := linDotSum_eq_eraseIdx_add (terms := terms) (i := i) (t := t) hterm hxt
  rcases hbranch with ⟨hpos, hl, hlt, hreason⟩ | ⟨hnotpos, hneg, hl, hlt, hreason⟩
  · have hqReason : l ∈ reason := by
      rw [hreason]
      exact List.mem_append_right _ (by simp)
    have hpl : (posLe t.s ((b - linOtherMin terms i) / t.c)).eval a = some false :=
      posLe_eval_false_of_not_true (k := (b - linOtherMin terms i) / t.c) hxt (by
        rw [← hl]
        exact hnotTrue _ hqReason)
    have hqFalse : l.eval a = some false := by rwa [hl]
    obtain ⟨x, hx, hnle⟩ := (eval_posLe_false_iff a t.s
      ((b - linOtherMin terms i) / t.c)).mp hpl
    have hxle : (b - linOtherMin terms i) / t.c < x := by omega
    have hmul := linPrunePos_newHi_lt_mul (c := t.c)
      (newHi := (b - linOtherMin terms i) / t.c) (x := x)
      (b := b) (other := linOtherMin terms i) hpos rfl hxle
    have hxxt : x = xt := by
      rw [hxt] at hx
      exact Option.some.inj hx.symm
    have hbig : b < linDotSum (terms.eraseIdx i) a + t.c * x := by
      unfold linOtherMin at hmul
      omega
    have hsum : linDotSum terms a = linDotSum (terms.eraseIdx i) a + t.c * x := by
      rw [hxxt]
      exact hsplit
    have hfinal : linDotSum terms a ≤ b := by
      rw [hd_eq] at hdle
      exact hdle
    rw [hsum] at hfinal
    omega
  · have hqReason : l ∈ reason := by
      rw [hreason]
      exact List.mem_append_right _ (by simp)
    have hnl : (negLe t.s (-((b - linOtherMin terms i) / (-t.c)) - 1)).eval a = some false :=
      negLe_eval_false_of_not_true
        (k := -((b - linOtherMin terms i) / (-t.c)) - 1) hxt (by
          rw [← hl]
          exact hnotTrue _ hqReason)
    have hqFalse : l.eval a = some false := by rwa [hl]
    obtain ⟨x, hx, hxle⟩ := (eval_negLe_false_iff a t.s
      (-((b - linOtherMin terms i) / (-t.c)) - 1)).mp hnl
    have hmul := linPruneNeg_mul_lt (c := t.c)
      (newLo := -((b - linOtherMin terms i) / (-t.c))) (x := x)
      (b := b) (other := linOtherMin terms i) hneg rfl hxle
    have hxxt : x = xt := by
      rw [hxt] at hx
      exact Option.some.inj hx.symm
    have hbig : b < linDotSum (terms.eraseIdx i) a + t.c * x := by
      unfold linOtherMin at hmul
      omega
    have hsum : linDotSum terms a = linDotSum (terms.eraseIdx i) a + t.c * x := by
      rw [hxxt]
      exact hsplit
    have hfinal : linDotSum terms a ≤ b := by
      rw [hd_eq] at hdle
      exact hdle
    rw [hsum] at hfinal
    omega

end LeanFzn.Engine

namespace LeanFzn.Engine

theorem linConflict_lits_evalLit_false (_p : CompiledProblem DomConstraint)
    (coeffs : List Int) (is : List Nat) (_b : Int) (view : EngineView)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hWF : ViewWF view is.toArray) :
    ∀ t ∈ linTerms coeffs.toArray is.toArray bds,
      (view.doms.getD t.s DomC.empty).evalLit
        (linMinNegLit t.s t.c t.lo t.hi) = some false := by
  intro t ht
  have hbdsize : bds.size = is.toArray.size := (linExtractBounds_spec hbds).1
  have htmem : t.s ∈ is.toArray.toList :=
    linTerms_slot_mem (cs := coeffs.toArray) (slots := is.toArray)
      (bds := bds) hsize hbdsize ht
  have hwf : (view.doms.getD t.s DomC.empty).WF := hWF.dom_wf htmem
  obtain ⟨hlo, hhi⟩ := linTerms_mem_bounds hsize hbds ht
  exact linMinNegLit_evalLit_false hwf hlo hhi

theorem linPrune_lit_evalLit_none (_p : CompiledProblem DomConstraint)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hWF : ViewWF view is.toArray)
    (hb : linTotalMin (linTerms coeffs.toArray is.toArray bds) ≤ b)
    {l : Literal} {reason : Clause}
    (hprune : (l, reason) ∈ linPrunes (linTerms coeffs.toArray is.toArray bds) b) :
    (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = none := by
  let terms := linTerms coeffs.toArray is.toArray bds
  have hbdsize : bds.size = is.toArray.size := (linExtractBounds_spec hbds).1
  obtain ⟨i, t, hterm, hbranch⟩ := linPrunes_mem hprune
  have ht : t ∈ terms := by
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hterm
    exact List.mem_iff_getElem.mpr ⟨i, hlt, hget⟩
  have htmem : t.s ∈ is.toArray.toList :=
    linTerms_slot_mem (cs := coeffs.toArray) (slots := is.toArray)
      (bds := bds) hsize hbdsize ht
  have hwf : (view.doms.getD t.s DomC.empty).WF := hWF.dom_wf htmem
  obtain ⟨hlo, hhi⟩ := linTerms_mem_bounds hsize hbds ht
  rcases hbranch with ⟨hpos, hl, hlt, _⟩ | ⟨_, hneg, hl, hlt, _⟩
  · subst hl
    have hlok := linPrunePos_lo_le (terms := terms) (i := i) (t := t)
      (b := b) hterm hpos hb
    have hnew : (b - linOtherMin terms i) / t.c < t.hi := hlt
    simpa [atomSlot, posLe] using
      (evalLit_posLe_none (d := view.doms.getD t.s DomC.empty) hlo hhi hlok hnew)
  · subst hl
    have hhiNew := linPruneNeg_newLo_le_hi (terms := terms) (i := i) (t := t)
      (b := b) hterm hneg hb
    have hhiNew' : -((b - linOtherMin (linTerms coeffs.toArray is.toArray bds) i) /
        (-t.c)) ≤ t.hi := by
      simpa only [terms] using hhiNew
    have hlt' : t.lo < -((b - linOtherMin (linTerms coeffs.toArray is.toArray bds) i) /
        (-t.c)) := by
      simpa only [terms] using hlt
    have hlok : t.lo ≤ -((b - linOtherMin (linTerms coeffs.toArray is.toArray bds) i) /
        (-t.c)) - 1 := by omega
    have hhik : -((b - linOtherMin (linTerms coeffs.toArray is.toArray bds) i) /
        (-t.c)) - 1 < t.hi := by omega
    simpa [atomSlot, negLe] using
      (evalLit_negLe_none (d := view.doms.getD t.s DomC.empty) hlo hhi hlok hhik)

theorem atomSlot_linMinNegLit (s : Nat) (c lo hi : Int) :
    atomSlot (linMinNegLit s c lo hi).atom = s := by
  unfold linMinNegLit
  split <;> rfl

theorem linPrune_other_lits_evalLit_false (_p : CompiledProblem DomConstraint)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hWF : ViewWF view is.toArray)
    {l : Literal} {reason : Clause}
    (hprune : (l, reason) ∈ linPrunes (linTerms coeffs.toArray is.toArray bds) b) :
    ∀ q ∈ reason, q ≠ l →
      (view.doms.getD (atomSlot q.atom) DomC.empty).evalLit q = some false := by
  let terms := linTerms coeffs.toArray is.toArray bds
  have hbdsize : bds.size = is.toArray.size := (linExtractBounds_spec hbds).1
  obtain ⟨i, t, hterm, hbranch⟩ := linPrunes_mem hprune
  have hreason : reason = linOtherLits terms i ++ [l] := by
    rcases hbranch with ⟨_, _, _, hr⟩ | ⟨_, _, _, _, hr⟩ <;> exact hr
  intro q hq hne
  have hqOther : q ∈ linOtherLits terms i := by
    rw [hreason] at hq
    rcases List.mem_append.mp hq with h | h
    · exact h
    · exact absurd (List.mem_singleton.mp h) hne
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (by
    simpa [linOtherLits, linConflictLits] using hqOther)
  have hu' : u ∈ terms := List.mem_of_mem_eraseIdx hu
  have htmem : u.s ∈ is.toArray.toList :=
    linTerms_slot_mem (cs := coeffs.toArray) (slots := is.toArray)
      (bds := bds) hsize hbdsize hu'
  have hwf : (view.doms.getD u.s DomC.empty).WF := hWF.dom_wf htmem
  obtain ⟨hlo, hhi⟩ := linTerms_mem_bounds hsize hbds hu'
  simpa [atomSlot_linMinNegLit] using linMinNegLit_evalLit_false hwf hlo hhi

def linPrunesWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linLe coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds) :
    Array (PLit × EClause p T) :=
  ((linPrunes (linTerms coeffs.toArray is.toArray bds) b).attach.map fun q =>
    (pLit q.1.1, EClause.ofLiterals p T q.1.2
      (linPrunes_sound p coeffs is b view hmem hsize bds hbds q.1.1 q.1.2 q.2))).toArray

theorem linPrunesWith_mem (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linLe coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    {q : PLit × EClause p T}
    (hq : q ∈ (linPrunesWith p T coeffs is b view hmem hsize bds hbds).toList) :
    ∃ (l : Literal) (reason : Clause),
      (l, reason) ∈ linPrunes (linTerms coeffs.toArray is.toArray bds) b ∧
        q.1.lit = l ∧ T.decodeClause q.2.lits = reason ∧
        Entailed p reason := by
  unfold linPrunesWith at hq
  rw [Array.mem_toList_iff, List.mem_toArray, List.mem_map] at hq
  obtain ⟨x, hx, rfl⟩ := hq
  refine ⟨x.1.1, x.1.2, x.2, rfl, ?_, ?_⟩
  · change T.decodeClause (x.1.2.toArray.map pLit) = x.1.2
    exact LitTable.decodeClause_map_pLit T x.1.2
  · change Entailed p x.1.2
    rw [← LitTable.decodeClause_map_pLit T x.1.2]
    exact (EClause.ofLiterals p T x.1.2
      (linPrunes_sound p coeffs is b view hmem hsize bds hbds x.1.1 x.1.2 x.2)).ent

def linLeOutWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linLe coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds) : PropOut p T :=
  let terms := linTerms coeffs.toArray is.toArray bds
  if hconf : b < linTotalMin terms then
    .conflict (EClause.ofLiterals p T (linConflictLits terms)
      (linConflict_entailed p coeffs is b view hmem hsize bds hbds hconf))
  else
    let ps := linPrunesWith p T coeffs is b view hmem hsize bds hbds
    if ps.isEmpty then .fix else .prune ps

/-- Computable test for the constraint this propagator was built from. -/
def linLeMatches (coeffs : List Int) (is : List Nat) (b : Int)
    (dc : DomConstraint) : Bool :=
  match dc with
  | .linLe cs js b' => cs == coeffs && js == is && b' == b
  | _ => false

theorem linLeMatches_spec {coeffs : List Int} {is : List Nat} {b : Int}
    {dc : DomConstraint} (h : linLeMatches coeffs is b dc = true) :
    dc = .linLe coeffs is b := by
  unfold linLeMatches at h
  split at h
  · rename_i cs js b'
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    rfl
  · simp at h

theorem linLeHmemOfFind (p : CompiledProblem DomConstraint)
    (coeffs : List Int) (is : List Nat) (b : Int) {dc : DomConstraint}
    (hfind : p.constraints.find? (linLeMatches coeffs is b) = some dc) :
    DomConstraint.linLe coeffs is b ∈ p.constraints := by
  have hmem := List.mem_of_find?_eq_some hfind
  have heq := linLeMatches_spec (List.find?_some hfind)
  rw [heq] at hmem
  exact hmem

def linLeProp (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) : PropV2 p T :=
  let cs := coeffs.toArray
  let slots := is.toArray
  { vars := slots
    events := slots.map fun s => (s, .bounds)
    run := fun view =>
      if hsize : cs.size = slots.size then
        match hbds : linExtractBounds view.doms slots with
        | none => .fix
        | some bds =>
            match hfind : p.constraints.find? (linLeMatches coeffs is b) with
            | none => .fix
            | some _ =>
                linLeOutWith p T coeffs is b view
                  (linLeHmemOfFind p coeffs is b hfind) hsize bds hbds
      else
        -- §A: a compiled `linLe` always has equal coefficient/variable
        -- lengths, so this defensive branch is unreachable in practice.
        -- Returning `.fix` (rather than an unprovable empty conflict)
        -- keeps `linLeProp` sound for an arbitrary `PropV2` input.
        .fix }

/-- Membership-explicit linear inequality propagator for N9.  Unlike
`linLeProp`, this wrapper does not search the constraint list: the caller
supplies the proof that the corresponding `linLe` is present. -/
def linLePropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int)
    (hmem : DomConstraint.linLe coeffs is b ∈ p.constraints) : PropV2 p T :=
  let cs := coeffs.toArray
  let slots := is.toArray
  { vars := slots
    events := slots.map fun s => (s, .bounds)
    run := fun view =>
      if hsize : cs.size = slots.size then
        match hbds : linExtractBounds view.doms slots with
        | none => .fix
        | some bds =>
            linLeOutWith p T coeffs is b view hmem hsize bds hbds
      else
        -- Same §A defensive branch as `linLeProp`: malformed arity is a
        -- sound no-op, and compiled `linLe` constraints never hit it.
        .fix }

theorem linLeProp_run_conflict (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (_hmem : DomConstraint.linLe coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    {ec : EClause p T}
    (h : (linLeProp p T coeffs is b).run view = .conflict ec) :
    ∃ bds terms, linExtractBounds view.doms is.toArray = some bds ∧
      terms = linTerms coeffs.toArray is.toArray bds ∧
      b < linTotalMin terms ∧
      T.decodeClause ec.lits = linConflictLits terms ∧
      Entailed p (linConflictLits terms) ∧
      (∀ t ∈ terms,
        (view.doms.getD t.s DomC.empty).evalLit
          (linMinNegLit t.s t.c t.lo t.hi) = some false) := by
  unfold linLeProp at h
  dsimp only at h
  by_cases hsize' : coeffs.toArray.size = is.toArray.size
  · rw [dif_pos hsize'] at h
    split at h
    · cases h
    · rename_i bds hbds
      split at h
      · cases h
      · rename_i dc hfind
        unfold linLeOutWith at h
        dsimp only at h
        split at h
        · rename_i hconf
          injection h with hec
          subst hec
          refine ⟨bds, linTerms coeffs.toArray is.toArray bds, hbds, rfl, hconf, ?_, ?_, ?_⟩
          · change T.decodeClause
              (linConflictLits (linTerms coeffs.toArray is.toArray bds) |>.toArray.map pLit) =
              linConflictLits (linTerms coeffs.toArray is.toArray bds)
            exact LitTable.decodeClause_map_pLit T _
          · exact linConflict_entailed p coeffs is b view
              (linLeHmemOfFind p coeffs is b hfind) hsize bds hbds hconf
          · exact linConflict_lits_evalLit_false p coeffs is b view hsize bds hbds hWF
        · split at h <;> cases h
  · rw [dif_neg hsize'] at h
    cases h

theorem linLeProp_run_prune (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (_hmem : DomConstraint.linLe coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    {ps : Array (PLit × EClause p T)}
    (h : (linLeProp p T coeffs is b).run view = .prune ps) :
    ∃ bds terms, linExtractBounds view.doms is.toArray = some bds ∧
      terms = linTerms coeffs.toArray is.toArray bds ∧
      ¬ b < linTotalMin terms ∧
      (∀ q ∈ ps.toList, ∃ (l : Literal) (reason : Clause),
        (l, reason) ∈ linPrunes terms b ∧
          q.1.lit = l ∧ T.decodeClause q.2.lits = reason ∧
          Entailed p reason ∧
          (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = none ∧
          (∀ q' ∈ reason, q' ≠ l →
            (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false)) := by
  unfold linLeProp at h
  dsimp only at h
  by_cases hsize' : coeffs.toArray.size = is.toArray.size
  · rw [dif_pos hsize'] at h
    split at h
    · cases h
    · rename_i bds hbds
      split at h
      · cases h
      · rename_i dc hfind
        unfold linLeOutWith at h
        dsimp only at h
        split at h
        · cases h
        · rename_i hconf
          split at h
          · cases h
          · rename_i hne
            injection h with hps
            subst hps
            refine ⟨bds, linTerms coeffs.toArray is.toArray bds, hbds, rfl, hconf, ?_⟩
            intro q hq
            obtain ⟨l, reason, hprune, hlit, hdec, hent⟩ :=
              linPrunesWith_mem p T coeffs is b view
                (linLeHmemOfFind p coeffs is b hfind) hsize bds hbds hq
            have hb' : linTotalMin (linTerms coeffs.toArray is.toArray bds) ≤ b := by
              omega
            refine ⟨l, reason, hprune, hlit, hdec, hent, ?_, ?_⟩
            · exact linPrune_lit_evalLit_none p coeffs is b view hsize bds hbds
                hWF hb' hprune
            · exact linPrune_other_lits_evalLit_false p coeffs is b view hsize bds hbds
                hWF hprune
  · rw [dif_neg hsize'] at h
    cases h

/-- Public conflict contract for the exact `PropOut` returned by `run`. -/
theorem linLeProp_conflict_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linLe coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    {ec : EClause p T}
    (h : (linLeProp p T coeffs is b).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  obtain ⟨bds, terms, hbds, hterms, hconf, hdec, hent, hfalse⟩ :=
    linLeProp_run_conflict p T coeffs is b view hmem hsize hWF h
  rwa [hdec]

/-- Every literal of the emitted conflict evaluates to `some false` on the
current view. -/
theorem linLeProp_conflict_lits_false (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linLe coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    {ec : EClause p T}
    (h : (linLeProp p T coeffs is b).run view = .conflict ec) :
    ∀ l ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false := by
  obtain ⟨bds, terms, hbds, hterms, hconf, hdec, hent, hfalse⟩ :=
    linLeProp_run_conflict p T coeffs is b view hmem hsize hWF h
  intro l hl
  rw [hdec] at hl
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hl
  simpa [atomSlot_linMinNegLit] using hfalse t ht

/-- Public prune-reason contract for the exact `PropOut` returned by `run`. -/
theorem linLeProp_prune_reason_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linLe coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    {ps : Array (PLit × EClause p T)}
    (h : (linLeProp p T coeffs is b).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  obtain ⟨bds, terms, hbds, hterms, hnotconf, hqfacts⟩ :=
    linLeProp_run_prune p T coeffs is b view hmem hsize hWF h
  obtain ⟨l, reason, hprune, hlit, hdec, hent, hnone, hother⟩ := hqfacts q hq
  rwa [hdec]

/-- In a prune branch the propagated literal is unassigned and every other
literal of its decoded reason is false on the current view. -/
theorem linLeProp_prune_lit_none (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linLe coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    {ps : Array (PLit × EClause p T)}
    (h : (linLeProp p T coeffs is b).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false := by
  obtain ⟨bds, terms, hbds, hterms, hnotconf, hqfacts⟩ :=
    linLeProp_run_prune p T coeffs is b view hmem hsize hWF h
  obtain ⟨l, reason, hprune, hlit, hdec, hent, hnone, hother⟩ := hqfacts q hq
  refine ⟨?_, ?_⟩
  · rwa [hlit]
  · intro q' hq' hne
    rw [hdec] at hq'
    exact hother q' hq' (by rwa [hlit] at hne)

/-- The §A defensive branch: malformed coefficient/variable arity is a
no-op, never an empty-clause conflict. -/
theorem linLeProp_run_fix_of_size_ne (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hsize : coeffs.length ≠ is.length) :
    (linLeProp p T coeffs is b).run view = .fix := by
  unfold linLeProp
  dsimp only
  have hne : coeffs.toArray.size ≠ is.toArray.size := by
    simpa using hsize
  rw [dif_neg hne]

/-! ## Membership-explicit contracts for `linLePropWith` -/

theorem linLePropWith_run_conflict (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linLe coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    {ec : EClause p T}
    (h : (linLePropWith p T coeffs is b hmem).run view = .conflict ec) :
    ∃ bds terms, linExtractBounds view.doms is.toArray = some bds ∧
      terms = linTerms coeffs.toArray is.toArray bds ∧
      b < linTotalMin terms ∧
      T.decodeClause ec.lits = linConflictLits terms ∧
      Entailed p (linConflictLits terms) ∧
      (∀ t ∈ terms,
        (view.doms.getD t.s DomC.empty).evalLit
          (linMinNegLit t.s t.c t.lo t.hi) = some false) := by
  unfold linLePropWith at h
  dsimp only at h
  by_cases hsize' : coeffs.toArray.size = is.toArray.size
  · rw [dif_pos hsize'] at h
    split at h
    · cases h
    · rename_i bds hbds
      unfold linLeOutWith at h
      dsimp only at h
      split at h
      · rename_i hconf
        injection h with hec
        subst hec
        refine ⟨bds, linTerms coeffs.toArray is.toArray bds, hbds, rfl, hconf, ?_, ?_, ?_⟩
        · change T.decodeClause
            (linConflictLits (linTerms coeffs.toArray is.toArray bds) |>.toArray.map pLit) =
            linConflictLits (linTerms coeffs.toArray is.toArray bds)
          exact LitTable.decodeClause_map_pLit T _
        · exact linConflict_entailed p coeffs is b view hmem hsize bds hbds hconf
        · exact linConflict_lits_evalLit_false p coeffs is b view hsize bds hbds hWF
      · split at h <;> cases h
  · rw [dif_neg hsize'] at h
    cases h

theorem linLePropWith_run_prune (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linLe coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    {ps : Array (PLit × EClause p T)}
    (h : (linLePropWith p T coeffs is b hmem).run view = .prune ps) :
    ∃ bds terms, linExtractBounds view.doms is.toArray = some bds ∧
      terms = linTerms coeffs.toArray is.toArray bds ∧
      ¬ b < linTotalMin terms ∧
      (∀ q ∈ ps.toList, ∃ (l : Literal) (reason : Clause),
        (l, reason) ∈ linPrunes terms b ∧
          q.1.lit = l ∧ T.decodeClause q.2.lits = reason ∧
          Entailed p reason ∧
          (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = none ∧
          (∀ q' ∈ reason, q' ≠ l →
            (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false)) := by
  unfold linLePropWith at h
  dsimp only at h
  by_cases hsize' : coeffs.toArray.size = is.toArray.size
  · rw [dif_pos hsize'] at h
    split at h
    · cases h
    · rename_i bds hbds
      unfold linLeOutWith at h
      dsimp only at h
      split at h
      · cases h
      · rename_i hconf
        split at h
        · cases h
        · rename_i hne
          injection h with hps
          subst hps
          refine ⟨bds, linTerms coeffs.toArray is.toArray bds, hbds, rfl, hconf, ?_⟩
          intro q hq
          obtain ⟨l, reason, hprune, hlit, hdec, hent⟩ :=
            linPrunesWith_mem p T coeffs is b view hmem hsize bds hbds hq
          have hb' : linTotalMin (linTerms coeffs.toArray is.toArray bds) ≤ b := by
            omega
          refine ⟨l, reason, hprune, hlit, hdec, hent, ?_, ?_⟩
          · exact linPrune_lit_evalLit_none p coeffs is b view hsize bds hbds
              hWF hb' hprune
          · exact linPrune_other_lits_evalLit_false p coeffs is b view hsize bds hbds
              hWF hprune
  · rw [dif_neg hsize'] at h
    cases h

/-- Public conflict contract for the exact `PropOut` returned by the
membership-explicit `linLePropWith`. -/
theorem linLePropWith_conflict_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linLe coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    {ec : EClause p T}
    (h : (linLePropWith p T coeffs is b hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  obtain ⟨bds, terms, hbds, hterms, hconf, hdec, hent, hfalse⟩ :=
    linLePropWith_run_conflict p T coeffs is b view hmem hsize hWF h
  rwa [hdec]

/-- Every literal of the `linLePropWith` conflict evaluates to `some false`
on the current view. -/
theorem linLePropWith_conflict_lits_false (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linLe coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    {ec : EClause p T}
    (h : (linLePropWith p T coeffs is b hmem).run view = .conflict ec) :
    ∀ l ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false := by
  obtain ⟨bds, terms, hbds, hterms, hconf, hdec, hent, hfalse⟩ :=
    linLePropWith_run_conflict p T coeffs is b view hmem hsize hWF h
  intro l hl
  rw [hdec] at hl
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hl
  simpa [atomSlot_linMinNegLit] using hfalse t ht

/-- Public prune-reason contract for the exact `PropOut` returned by
`linLePropWith`. -/
theorem linLePropWith_prune_reason_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linLe coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    {ps : Array (PLit × EClause p T)}
    (h : (linLePropWith p T coeffs is b hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  obtain ⟨bds, terms, hbds, hterms, hnotconf, hqfacts⟩ :=
    linLePropWith_run_prune p T coeffs is b view hmem hsize hWF h
  obtain ⟨l, reason, hprune, hlit, hdec, hent, hnone, hother⟩ := hqfacts q hq
  rwa [hdec]

/-- In a `linLePropWith` prune branch the propagated literal is unassigned
and every other literal of its decoded reason is false on the view. -/
theorem linLePropWith_prune_lit_none (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linLe coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    {ps : Array (PLit × EClause p T)}
    (h : (linLePropWith p T coeffs is b hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false := by
  obtain ⟨bds, terms, hbds, hterms, hnotconf, hqfacts⟩ :=
    linLePropWith_run_prune p T coeffs is b view hmem hsize hWF h
  obtain ⟨l, reason, hprune, hlit, hdec, hent, hnone, hother⟩ := hqfacts q hq
  refine ⟨?_, ?_⟩
  · rwa [hlit]
  · intro q' hq' hne
    rw [hdec] at hq'
    exact hother q' hq' (by rwa [hlit] at hne)

/-- The §A defensive branch for `linLePropWith`: malformed arity is a
no-op, never an empty-clause conflict. -/
theorem linLePropWith_run_fix_of_size_ne (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (_hmem : DomConstraint.linLe coeffs is b ∈ p.constraints)
    (hsize : coeffs.length ≠ is.length) :
    (linLePropWith p T coeffs is b _hmem).run view = .fix := by
  unfold linLePropWith
  dsimp only
  have hne : coeffs.toArray.size ≠ is.toArray.size := by
    simpa using hsize
  rw [dif_neg hne]

end LeanFzn.Engine

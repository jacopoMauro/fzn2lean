import LeanFzn.Solver.Propagation.DomainConstraints.Repr
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation
open LeanFzn.Solver.Core
open LeanFzn LeanFzn.Semantics.Evaluation LeanFzn.Solver.Core List
open LeanFzn.Solver.Propagation.DomainFiltering.Internal

namespace LeanFzn.Solver.Propagation.DomainFiltering

/-! ## The strict-order propagators (`int_lt` style) -/

/-- The strict upper-bound propagator (`int_lt(x, c)` style, slot vs
    constant): slot `i`'s domain keeps its integer values `< c`;
    `contradiction` when that empties. -/
def propLtConstHi (i : Nat) (c : Int) (doms : List (List Value)) : PropResult :=
  let d' := atMostVals (c - 1) (getSlot doms i)
  if d'.isEmpty = true then .contradiction
  else .narrowed (setSlot doms i d')

/-- **Preservation for `propLtConstHi`**: on `narrowed doms'`, every
    assignment of the input domains whose slot `i` value is an
    integer `p < c` is still an assignment of `doms'`, and `doms'`
    is pointwise-subset the input domains; on `contradiction`, no
    assignment of the input domains bounds slot `i` strictly below
    `c`. -/
theorem propLtConstHi_preserves (i : Nat) (c : Int) :
    Preserves (DomConstraint.ltConstHi i c) (propLtConstHi i c) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propLtConstHi] at h
    obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, hx, hpc⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    by_cases hc : (atMostVals (c - 1) (getSlot doms i)).isEmpty = true
    · rw [if_pos hc] at h
      exact absurd h (by simp)
    · rw [if_neg hc] at h
      have hd : setSlot doms i (atMostVals (c - 1) (getSlot doms i)) = doms' :=
        PropResult.narrowed.inj h
      subst hd
      apply allAssigns_intro
      · rw [setSlot_length]
        exact hlen
      · intro m v hv
        by_cases hmi : m = i
        · rw [hmi] at hv
          have hvp : v = Value.int p := Option.some.inj (hv.symm.trans hx)
          subst hvp
          rw [hmi, getSlot_setSlot_eq doms (atMostVals (c - 1) (getSlot doms i)) i
            (lt_length_of_mem_getSlot doms i _ hxi)]
          exact mem_atMostVals.mpr ⟨hxi, p, rfl, by omega⟩
        · rw [getSlot_setSlot_of_ne doms (atMostVals (c - 1) (getSlot doms i)) i m hmi]
          exact hget m v hv
  · intro doms doms' h
    simp only [propLtConstHi] at h
    by_cases hc : (atMostVals (c - 1) (getSlot doms i)).isEmpty = true
    · rw [if_pos hc] at h
      exact absurd h (by simp)
    · rw [if_neg hc] at h
      have hd : setSlot doms i (atMostVals (c - 1) (getSlot doms i)) = doms' :=
        PropResult.narrowed.inj h
      subst hd
      exact DomPointwiseSub.setSlot (DomPointwiseSub.refl doms)
        (fun _ hv => (mem_atMostVals.mp hv).1)
  · intro doms h a ha hsat
    simp only [propLtConstHi] at h
    obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, hx, hpc⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    by_cases hc : (atMostVals (c - 1) (getSlot doms i)).isEmpty = true
    · rw [if_pos hc] at h
      have hmem : Value.int p ∈ atMostVals (c - 1) (getSlot doms i) :=
        mem_atMostVals.mpr ⟨hxi, p, rfl, by omega⟩
      rw [List.isEmpty_iff.mp hc] at hmem
      exact absurd hmem (by simp)
    · rw [if_neg hc] at h
      exact absurd h (by simp)

/-- The strict lower-bound propagator (`int_lt(c, x)` style, constant
    vs slot): slot `i`'s domain keeps its integer values `> c`;
    `contradiction` when that empties. -/
def propLtConstLo (i : Nat) (c : Int) (doms : List (List Value)) : PropResult :=
  let d' := atLeastVals (c + 1) (getSlot doms i)
  if d'.isEmpty = true then .contradiction
  else .narrowed (setSlot doms i d')

/-- **Preservation for `propLtConstLo`** (the symmetric local
    preservation theorem, strict lower-bound case). -/
theorem propLtConstLo_preserves (i : Nat) (c : Int) :
    Preserves (DomConstraint.ltConstLo i c) (propLtConstLo i c) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propLtConstLo] at h
    obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, hx, hcp⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    by_cases hc : (atLeastVals (c + 1) (getSlot doms i)).isEmpty = true
    · rw [if_pos hc] at h
      exact absurd h (by simp)
    · rw [if_neg hc] at h
      have hd : setSlot doms i (atLeastVals (c + 1) (getSlot doms i)) = doms' :=
        PropResult.narrowed.inj h
      subst hd
      apply allAssigns_intro
      · rw [setSlot_length]
        exact hlen
      · intro m v hv
        by_cases hmi : m = i
        · rw [hmi] at hv
          have hvp : v = Value.int p := Option.some.inj (hv.symm.trans hx)
          subst hvp
          rw [hmi, getSlot_setSlot_eq doms (atLeastVals (c + 1) (getSlot doms i)) i
            (lt_length_of_mem_getSlot doms i _ hxi)]
          exact mem_atLeastVals.mpr ⟨hxi, p, rfl, by omega⟩
        · rw [getSlot_setSlot_of_ne doms (atLeastVals (c + 1) (getSlot doms i)) i m hmi]
          exact hget m v hv
  · intro doms doms' h
    simp only [propLtConstLo] at h
    by_cases hc : (atLeastVals (c + 1) (getSlot doms i)).isEmpty = true
    · rw [if_pos hc] at h
      exact absurd h (by simp)
    · rw [if_neg hc] at h
      have hd : setSlot doms i (atLeastVals (c + 1) (getSlot doms i)) = doms' :=
        PropResult.narrowed.inj h
      subst hd
      exact DomPointwiseSub.setSlot (DomPointwiseSub.refl doms)
        (fun _ hv => (mem_atLeastVals.mp hv).1)
  · intro doms h a ha hsat
    simp only [propLtConstLo] at h
    obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, hx, hcp⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    by_cases hc : (atLeastVals (c + 1) (getSlot doms i)).isEmpty = true
    · rw [if_pos hc] at h
      have hmem : Value.int p ∈ atLeastVals (c + 1) (getSlot doms i) :=
        mem_atLeastVals.mpr ⟨hxi, p, rfl, by omega⟩
      rw [List.isEmpty_iff.mp hc] at hmem
      exact absurd hmem (by simp)
    · rw [if_neg hc] at h
      exact absurd h (by simp)

/-- The `int_lt` narrowing: slot `i` keeps values `≤ b` (the max of
    `j`'s domain: `p < q ≤ b` gives `p ≤ b`), slot `j` keeps values
    `≥ m` (the min of `i`'s domain: `m ≤ p < q` gives `q ≥ m`). -/
private def ltNarrow (b m : Int) (i j : Nat) (doms : List (List Value)) :
    List (List Value) :=
  let hi := atMostVals b (getSlot doms i)
  let hj := atLeastVals m (getSlot doms j)
  setSlot (setSlot doms i hi) j hj

/-- The strict-order propagator (`int_lt` style on two slots): slot
    `i` keeps values strictly below one plus the maximum integer of
    slot `j`'s domain, slot `j` keeps values strictly above one less
    than the minimum integer of slot `i`'s domain;
    `contradiction` when either side empties. -/
def propLtSlot (i j : Nat) (doms : List (List Value)) : PropResult :=
  match domMax (getSlot doms j) with
  | none => .contradiction
  | some b =>
      match domMin (getSlot doms i) with
      | none => .contradiction
      | some m =>
          let hi := atMostVals b (getSlot doms i)
          let hj := atLeastVals m (getSlot doms j)
          if hi.isEmpty = true ∨ hj.isEmpty = true then
            .contradiction
          else
            .narrowed (ltNarrow b m i j doms)

private theorem getSlot_ltNarrow_left {i j : Nat} {b m : Int}
    {doms : List (List Value)}
    (hi : i < doms.length) (hij : i ≠ j) :
    getSlot (ltNarrow b m i j doms) i = atMostVals b (getSlot doms i) := by
  simp only [ltNarrow]
  rw [getSlot_setSlot_of_ne (setSlot doms i (atMostVals b (getSlot doms i)))
    (atLeastVals m (getSlot doms j)) j i hij,
    getSlot_setSlot_eq doms _ i hi]

private theorem getSlot_ltNarrow_right {i j : Nat} {b m : Int}
    {doms : List (List Value)} (hj : j < doms.length) :
    getSlot (ltNarrow b m i j doms) j = atLeastVals m (getSlot doms j) := by
  simp only [ltNarrow]
  rw [getSlot_setSlot_eq (setSlot doms i (atMostVals b (getSlot doms i)))
    (atLeastVals m (getSlot doms j)) j (by rw [setSlot_length]; exact hj)]

private theorem getSlot_ltNarrow_other {i j k : Nat} {b m : Int}
    {doms : List (List Value)}
    (hki : k ≠ i) (hkj : k ≠ j) :
    getSlot (ltNarrow b m i j doms) k = getSlot doms k := by
  simp only [ltNarrow]
  rw [getSlot_setSlot_of_ne (setSlot doms i (atMostVals b (getSlot doms i)))
    (atLeastVals m (getSlot doms j)) j k hkj,
    getSlot_setSlot_of_ne doms (atMostVals b (getSlot doms i)) i k hki]

/-- **Preservation for `propLtSlot`**: on `narrowed doms'`, every
    assignment of the input domains whose slots `i` and `j` carry
    integers `p < q` is still an assignment of `doms'`, and `doms'`
    is pointwise-subset the input domains; on `contradiction`, no
    assignment of the input domains puts slot `i`'s value strictly
    below slot `j`'s. -/
theorem propLtSlot_preserves (i j : Nat) :
    Preserves (DomConstraint.ltSlot i j) (propLtSlot i j) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propLtSlot] at h
    obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, q, hx, hy, hlt⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    have hyj : Value.int q ∈ getSlot doms j := hget j _ hy
    have hilen : i < doms.length := lt_length_of_mem_getSlot doms i _ hxi
    have hjlen : j < doms.length := lt_length_of_mem_getSlot doms j _ hyj
    have hij : i ≠ j := by
      intro hij'
      subst hij'
      have : (Value.int p) = (Value.int q) := Option.some.inj (hx.symm.trans hy)
      injection this with hpq
      omega
    cases hb : domMax (getSlot doms j) with
    | none =>
        rw [hb] at h
        exact absurd h (by simp)
    | some b =>
        simp only [hb] at h
        obtain ⟨b', hbb, hqb⟩ := domMax_of_mem hyj
        rw [hb] at hbb
        injection hbb with hbqb
        cases hm : domMin (getSlot doms i) with
        | none =>
            rw [hm] at h
            exact absurd h (by simp)
        | some m =>
            simp only [hm] at h
            obtain ⟨m', hmm, hpm⟩ := domMin_of_mem hxi
            rw [hm] at hmm
            injection hmm with hmmm
            by_cases hc : (atMostVals b (getSlot doms i)).isEmpty = true ∨
              (atLeastVals m (getSlot doms j)).isEmpty = true
            · rw [if_pos hc] at h
              exact absurd h (by simp)
            · rw [if_neg hc] at h
              have hd : ltNarrow b m i j doms = doms' := PropResult.narrowed.inj h
              subst hd
              rw [hbqb, hmmm]
              apply allAssigns_intro
              · rw [ltNarrow, setSlot_length, setSlot_length]
                exact hlen
              · intro k v hv
                by_cases hki : k = i
                · rw [hki] at hv
                  have hvp : v = Value.int p := Option.some.inj (hv.symm.trans hx)
                  subst hvp
                  rw [hki, getSlot_ltNarrow_left hilen hij]
                  exact mem_atMostVals.mpr ⟨hxi, p, rfl, by omega⟩
                · by_cases hkj : k = j
                  · rw [hkj] at hv
                    have hvq : v = Value.int q := Option.some.inj (hv.symm.trans hy)
                    subst hvq
                    rw [hkj, getSlot_ltNarrow_right hjlen]
                    exact mem_atLeastVals.mpr ⟨hyj, q, rfl, by omega⟩
                  · rw [getSlot_ltNarrow_other (fun h => hki h) (fun h => hkj h)]
                    exact hget k v hv
  · intro doms doms' h
    simp only [propLtSlot] at h
    cases hb : domMax (getSlot doms j) with
    | none => rw [hb] at h; exact absurd h (by simp)
    | some b =>
        simp only [hb] at h
        cases hm : domMin (getSlot doms i) with
        | none => rw [hm] at h; exact absurd h (by simp)
        | some m =>
            simp only [hm] at h
            by_cases hc : (atMostVals b (getSlot doms i)).isEmpty = true ∨
              (atLeastVals m (getSlot doms j)).isEmpty = true
            · rw [if_pos hc] at h
              exact absurd h (by simp)
            · rw [if_neg hc] at h
              have hd : ltNarrow b m i j doms = doms' := PropResult.narrowed.inj h
              subst hd
              simp only [ltNarrow]
              exact DomPointwiseSub.setSlot
                (DomPointwiseSub.setSlot (DomPointwiseSub.refl doms)
                  (fun _ hv => (mem_atMostVals.mp hv).1))
                (fun _ hv => (mem_atLeastVals.mp hv).1)
  · intro doms h a ha hsat
    simp only [propLtSlot] at h
    obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, q, hx, hy, hlt⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    have hyj : Value.int q ∈ getSlot doms j := hget j _ hy
    cases hb : domMax (getSlot doms j) with
    | none =>
        have := domMax_of_mem hyj
        rw [hb] at this
        exact absurd this (by simp)
    | some b =>
        simp only [hb] at h
        obtain ⟨b', hbb, hqb⟩ := domMax_of_mem hyj
        rw [hb] at hbb
        injection hbb with hbqb
        cases hm : domMin (getSlot doms i) with
        | none =>
            have := domMin_of_mem hxi
            rw [hm] at this
            exact absurd this (by simp)
        | some m =>
            simp only [hm] at h
            obtain ⟨m', hmm, hpm⟩ := domMin_of_mem hxi
            rw [hm] at hmm
            injection hmm with hmmm
            by_cases hc : (atMostVals b (getSlot doms i)).isEmpty = true ∨
              (atLeastVals m (getSlot doms j)).isEmpty = true
            · rw [if_pos hc] at h
              rcases hc with hc | hc
              · have hmem : Value.int p ∈ atMostVals b (getSlot doms i) :=
                  mem_atMostVals.mpr ⟨hxi, p, rfl, by omega⟩
                rw [List.isEmpty_iff.mp hc] at hmem
                exact absurd hmem (by simp)
              · have hmem : Value.int q ∈ atLeastVals m (getSlot doms j) :=
                  mem_atLeastVals.mpr ⟨hyj, q, rfl, by omega⟩
                rw [List.isEmpty_iff.mp hc] at hmem
                exact absurd hmem (by simp)
            · rw [if_neg hc] at h
              exact absurd h (by simp)


end LeanFzn.Solver.Propagation.DomainFiltering

import LeanFzn.Solver.Propagation.DomainConstraints.Repr
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation
open LeanFzn.Solver.Core
open LeanFzn LeanFzn.Semantics.Evaluation LeanFzn.Solver.Core List
open LeanFzn.Solver.Propagation.DomainFiltering.Internal

namespace LeanFzn.Solver.Propagation.DomainFiltering

/-! ## The equality propagator -/

/-- The equality narrowing: both slots take the intersection of their
    domains (each in its own order), each intersection computed once. -/
private def eqNarrow (i j : Nat) (doms : List (List Value)) :
    List (List Value) :=
  let di := getSlot doms i
  let dj := getSlot doms j
  setSlot (setSlot doms i (interVals di dj)) j (interVals dj di)

/-- **The equality propagator** (`int_eq` style on two slots): both
    domains narrow to their intersection; `contradiction` when the
    intersection is empty.  Each intersection is computed once. -/
def propEqSlot (i j : Nat) (doms : List (List Value)) : PropResult :=
  let xi := interVals (getSlot doms i) (getSlot doms j)
  let xj := interVals (getSlot doms j) (getSlot doms i)
  if xi.isEmpty = true ∨ xj.isEmpty = true then
    .contradiction
  else
    .narrowed (eqNarrow i j doms)

private theorem getSlot_eqNarrow_left {i j : Nat} {doms : List (List Value)}
    (hi : i < doms.length) (hij : i ≠ j) :
    getSlot (eqNarrow i j doms) i =
      interVals (getSlot doms i) (getSlot doms j) := by
  simp only [eqNarrow]
  rw [getSlot_setSlot_of_ne (setSlot doms i (interVals (getSlot doms i) (getSlot doms j)))
    (interVals (getSlot doms j) (getSlot doms i)) j i hij,
    getSlot_setSlot_eq doms _ i hi]

private theorem getSlot_eqNarrow_right {i j : Nat} {doms : List (List Value)}
    (hj : j < doms.length) :
    getSlot (eqNarrow i j doms) j =
      interVals (getSlot doms j) (getSlot doms i) := by
  simp only [eqNarrow]
  rw [getSlot_setSlot_eq (setSlot doms i (interVals (getSlot doms i) (getSlot doms j)))
    (interVals (getSlot doms j) (getSlot doms i)) j
    (by rw [setSlot_length]; exact hj)]

private theorem getSlot_eqNarrow_other {i j k : Nat} {doms : List (List Value)}
    (hki : k ≠ i) (hkj : k ≠ j) :
    getSlot (eqNarrow i j doms) k = getSlot doms k := by
  simp only [eqNarrow]
  rw [getSlot_setSlot_of_ne (setSlot doms i (interVals (getSlot doms i) (getSlot doms j)))
    (interVals (getSlot doms j) (getSlot doms i)) j k hkj,
    getSlot_setSlot_of_ne doms (interVals (getSlot doms i) (getSlot doms j)) i k hki]

/-- **Preservation for `propEqSlot`** (PLAN 6.3's local preservation
    theorem, equality case): on `narrowed doms'`, every assignment of
    the input domains whose two slots carry equal values is still an
    assignment of `doms'`, and `doms'` is pointwise-subset the input
    domains; on `contradiction`, no assignment of the input domains
    makes the two slots equal. -/
theorem propEqSlot_preserves (i j : Nat) :
    Preserves (DomConstraint.eqSlot i j) (propEqSlot i j) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propEqSlot] at h
    by_cases hc : (interVals (getSlot doms i) (getSlot doms j)).isEmpty = true ∨
      (interVals (getSlot doms j) (getSlot doms i)).isEmpty = true
    · rw [if_pos hc] at h
      exact absurd h (by simp)
    · rw [if_neg hc] at h
      have hd : eqNarrow i j doms = doms' := PropResult.narrowed.inj h
      subst hd
      obtain ⟨x, y, hx, hy, heq⟩ := hsat
      obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
      have hxi : x ∈ getSlot doms i := hget i x hx
      have hyj : y ∈ getSlot doms j := hget j y hy
      have hyi : y ∈ getSlot doms i := by rw [← heq]; exact hxi
      have hxj : x ∈ getSlot doms j := by rw [heq]; exact hyj
      apply allAssigns_intro
      · have hlen2 : (eqNarrow i j doms).length = doms.length := by
          simp only [eqNarrow, setSlot_length]
        rw [hlen2]
        exact hlen
      · intro k v hv
        by_cases hkj : k = j
        · rw [hkj] at hv
          have hvy : v = y := Option.some.inj (hv.symm.trans hy)
          subst hvy
          have hlenj : j < doms.length :=
            lt_length_of_mem_getSlot doms j v (hget j v hv)
          rw [hkj, getSlot_eqNarrow_right hlenj]
          refine mem_interVals_of (hget j v hv) ?_
          rw [← heq]
          exact hxi
        · by_cases hki : k = i
          · rw [hki] at hv
            have hvx : v = x := Option.some.inj (hv.symm.trans hx)
            subst hvx
            have hleni : i < doms.length :=
              lt_length_of_mem_getSlot doms i v (hget i v hv)
            rw [hki, getSlot_eqNarrow_left hleni (fun hij => hkj (hki.trans hij))]
            refine mem_interVals_of (hget i v hv) ?_
            rw [heq]
            exact hyj
          · rw [getSlot_eqNarrow_other (fun h => hki h) (fun h => hkj h)]
            exact hget k v hv
  · intro doms doms' h
    simp only [propEqSlot] at h
    by_cases hc : (interVals (getSlot doms i) (getSlot doms j)).isEmpty = true ∨
      (interVals (getSlot doms j) (getSlot doms i)).isEmpty = true
    · rw [if_pos hc] at h
      exact absurd h (by simp)
    · rw [if_neg hc] at h
      have hd : eqNarrow i j doms = doms' := PropResult.narrowed.inj h
      subst hd
      simp only [eqNarrow]
      exact DomPointwiseSub.setSlot
        (DomPointwiseSub.setSlot (DomPointwiseSub.refl doms)
          (fun _ hv => mem_interVals_left hv))
        (fun _ hv => mem_interVals_left hv)
  · intro doms _h a ha hsat
    simp only [propEqSlot] at _h
    by_cases hc : (interVals (getSlot doms i) (getSlot doms j)).isEmpty = true ∨
      (interVals (getSlot doms j) (getSlot doms i)).isEmpty = true
    · rcases hc with hle | hre
      · obtain ⟨x, y, hx, hy, heq⟩ := hsat
        obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
        have hxj : x ∈ getSlot doms j := by rw [heq]; exact hget j y hy
        have hmem : x ∈ interVals (getSlot doms i) (getSlot doms j) :=
          mem_interVals_of (hget i x hx) hxj
        rw [List.isEmpty_iff.mp hle] at hmem
        exact absurd hmem (by simp)
      · obtain ⟨x, y, hx, hy, heq⟩ := hsat
        obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
        have hyi : y ∈ getSlot doms i := by rw [← heq]; exact hget i x hx
        have hmem : y ∈ interVals (getSlot doms j) (getSlot doms i) :=
          mem_interVals_of (hget j y hy) hyi
        rw [List.isEmpty_iff.mp hre] at hmem
        exact absurd hmem (by simp)
    · rw [if_neg hc] at _h
      exact absurd _h (by simp)

/-! ## The disequality propagator -/

/-- **The disequality propagator** (`int_ne` style on two slots): if
    one slot's domain is a singleton, its value is removed from the
    other slot's domain; `contradiction` when the other domain becomes
    empty.  When neither domain is a singleton, nothing is narrowed. -/
def propNeSlot (i j : Nat) (doms : List (List Value)) : PropResult :=
  match single? (getSlot doms i) with
  | some x =>
      if (removeVal x (getSlot doms j)).isEmpty = true then .contradiction
      else .narrowed (setSlot doms j (removeVal x (getSlot doms j)))
  | none =>
      match single? (getSlot doms j) with
      | some y =>
          if (removeVal y (getSlot doms i)).isEmpty = true then .contradiction
          else .narrowed (setSlot doms i (removeVal y (getSlot doms i)))
      | none => .narrowed doms

private theorem propNe_narrowed {s r : Nat} {w : Value}
    {doms : List (List Value)}
    (hw : single? (getSlot doms s) = some w) {a : List Value}
    (ha : a ∈ allAssigns doms) (hsat : DomConstraint.SatisfiedBy (DomConstraint.neSlot s r) a) :
    a ∈ allAssigns (setSlot doms r (removeVal w (getSlot doms r))) := by
  obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
  obtain ⟨x, y, hx, hy, hne⟩ := hsat
  have hxs : x = w := by
    have hxmem : x ∈ getSlot doms s := hget s x hx
    rw [single?_eq_some_iff.mp hw] at hxmem
    exact List.mem_singleton.mp hxmem
  apply allAssigns_intro
  · rw [setSlot_length]
    exact hlen
  · intro k v hv
    by_cases hkr : k = r
    · rw [hkr] at hv
      have hvy : v = y := Option.some.inj (hv.symm.trans hy)
      subst hvy
      have hlenr : r < doms.length :=
        lt_length_of_mem_getSlot doms r v (hget r v hv)
      rw [hkr, getSlot_setSlot_eq doms (removeVal w (getSlot doms r)) r hlenr]
      exact mem_removeVal_of (hget r v hv)
        (eqB_false_of_ne (by rw [← hxs]; exact hne))
    · rw [getSlot_setSlot_of_ne doms (removeVal w (getSlot doms r)) r k hkr]
      exact hget k v hv

private theorem propNe_contradicts {s r : Nat} {w : Value}
    {doms : List (List Value)}
    (hw : single? (getSlot doms s) = some w)
    (hempty : (removeVal w (getSlot doms r)).isEmpty = true)
    {a : List Value} (ha : a ∈ allAssigns doms)
    (hsat : DomConstraint.SatisfiedBy (DomConstraint.neSlot s r) a) : False := by
  obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
  obtain ⟨x, y, hx, hy, hne⟩ := hsat
  have hxs : x = w := by
    have hxmem : x ∈ getSlot doms s := hget s x hx
    rw [single?_eq_some_iff.mp hw] at hxmem
    exact List.mem_singleton.mp hxmem
  have hmem : y ∈ removeVal w (getSlot doms r) :=
    mem_removeVal_of (hget r y hy) (eqB_false_of_ne (by rw [← hxs]; exact hne))
  rw [List.isEmpty_iff.mp hempty] at hmem
  exact absurd hmem (by simp)

/-- **Preservation for `propNeSlot`** (PLAN 6.3's local preservation
    theorem, disequality case): on `narrowed doms'`, every assignment
    of the input domains whose two slots carry different values is
    still an assignment of `doms'`, and `doms'` is pointwise-subset
    the input domains; on `contradiction`, no assignment of the input
    domains makes the two slots differ. -/
theorem propNeSlot_preserves (i j : Nat) :
    Preserves (DomConstraint.neSlot i j) (propNeSlot i j) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propNeSlot] at h
    cases hi : single? (getSlot doms i) with
    | none =>
        simp only [hi] at h
        cases hj : single? (getSlot doms j) with
        | none =>
            simp only [hj] at h
            have hd : doms' = doms := (PropResult.narrowed.inj h).symm
            subst hd
            exact ha
        | some y =>
            simp only [hj] at h
            by_cases hc : (removeVal y (getSlot doms i)).isEmpty = true
            · rw [if_pos hc] at h
              exact absurd h (by simp)
            · rw [if_neg hc] at h
              have hd : setSlot doms i (removeVal y (getSlot doms i)) = doms' :=
                PropResult.narrowed.inj h
              subst hd
              exact propNe_narrowed hj ha
                ((DomConstraint.satisfiedBy_neSlot_comm i j a).mp hsat)
    | some x =>
        simp only [hi] at h
        by_cases hc : (removeVal x (getSlot doms j)).isEmpty = true
        · rw [if_pos hc] at h
          exact absurd h (by simp)
        · rw [if_neg hc] at h
          have hd : setSlot doms j (removeVal x (getSlot doms j)) = doms' :=
            PropResult.narrowed.inj h
          subst hd
          exact propNe_narrowed hi ha hsat
  · intro doms doms' _h
    simp only [propNeSlot] at _h
    cases hi : single? (getSlot doms i) with
    | none =>
        simp only [hi] at _h
        cases hj : single? (getSlot doms j) with
        | none =>
            simp only [hj] at _h
            have hd : doms' = doms := (PropResult.narrowed.inj _h).symm
            rw [hd]
            exact DomPointwiseSub.refl doms
        | some y =>
            simp only [hj] at _h
            by_cases hc : (removeVal y (getSlot doms i)).isEmpty = true
            · rw [if_pos hc] at _h
              exact absurd _h (by simp)
            · rw [if_neg hc] at _h
              have hd : setSlot doms i (removeVal y (getSlot doms i)) = doms' :=
                PropResult.narrowed.inj _h
              rw [← hd]
              exact DomPointwiseSub.setSlot (DomPointwiseSub.refl doms)
                (fun _ hv => mem_removeVal hv)
    | some x =>
        simp only [hi] at _h
        by_cases hc : (removeVal x (getSlot doms j)).isEmpty = true
        · rw [if_pos hc] at _h
          exact absurd _h (by simp)
        · rw [if_neg hc] at _h
          have hd : setSlot doms j (removeVal x (getSlot doms j)) = doms' :=
            PropResult.narrowed.inj _h
          rw [← hd]
          exact DomPointwiseSub.setSlot (DomPointwiseSub.refl doms)
            (fun _ hv => mem_removeVal hv)
  · intro doms h a ha hsat
    simp only [propNeSlot] at h
    cases hi : single? (getSlot doms i) with
    | none =>
        simp only [hi] at h
        cases hj : single? (getSlot doms j) with
        | none =>
            simp only [hj] at h
            exact absurd h (by simp)
        | some y =>
            simp only [hj] at h
            by_cases hc : (removeVal y (getSlot doms i)).isEmpty = true
            · rw [if_pos hc] at h
              exact propNe_contradicts hj hc ha
                ((DomConstraint.satisfiedBy_neSlot_comm i j a).mp hsat)
            · rw [if_neg hc] at h
              exact absurd h (by simp)
    | some x =>
        simp only [hi] at h
        by_cases hc : (removeVal x (getSlot doms j)).isEmpty = true
        · rw [if_pos hc] at h
          exact propNe_contradicts hi hc ha hsat
        · rw [if_neg hc] at h
          exact absurd h (by simp)

/-! ## The order propagator -/

/-- The order narrowing: slot `i` keeps values at most `b`, slot `j`
    keeps values at least `m`. -/
private def leNarrow (b m : Int) (i j : Nat) (doms : List (List Value)) :
    List (List Value) :=
  let hi := atMostVals b (getSlot doms i)
  let hj := atLeastVals m (getSlot doms j)
  setSlot (setSlot doms i hi) j hj

/-- **The order propagator** (`int_le` style on two slots): slot `i`
    keeps values at most the maximum integer of slot `j`'s domain,
    slot `j` keeps values at least the minimum integer of slot `i`'s
    domain; `contradiction` when either side becomes empty (or a
    domain has no integers to order). -/
def propLeSlot (i j : Nat) (doms : List (List Value)) : PropResult :=
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
            .narrowed (leNarrow b m i j doms)

private theorem getSlot_leNarrow_left {i j : Nat} {b m : Int}
    {doms : List (List Value)}
    (hi : i < doms.length) (hij : i ≠ j) :
    getSlot (leNarrow b m i j doms) i = atMostVals b (getSlot doms i) := by
  simp only [leNarrow]
  rw [getSlot_setSlot_of_ne (setSlot doms i (atMostVals b (getSlot doms i)))
    (atLeastVals m (getSlot doms j)) j i hij,
    getSlot_setSlot_eq doms _ i hi]

private theorem getSlot_leNarrow_right {i j : Nat} {b m : Int}
    {doms : List (List Value)} (hj : j < doms.length) :
    getSlot (leNarrow b m i j doms) j = atLeastVals m (getSlot doms j) := by
  simp only [leNarrow]
  rw [getSlot_setSlot_eq (setSlot doms i (atMostVals b (getSlot doms i)))
    (atLeastVals m (getSlot doms j)) j (by rw [setSlot_length]; exact hj)]

private theorem getSlot_leNarrow_other {i j k : Nat} {b m : Int}
    {doms : List (List Value)} (hki : k ≠ i) (hkj : k ≠ j) :
    getSlot (leNarrow b m i j doms) k = getSlot doms k := by
  simp only [leNarrow]
  rw [getSlot_setSlot_of_ne (setSlot doms i (atMostVals b (getSlot doms i)))
    (atLeastVals m (getSlot doms j)) j k hkj,
    getSlot_setSlot_of_ne doms (atMostVals b (getSlot doms i)) i k hki]

/-- **Preservation for `propLeSlot`** (PLAN 6.3's local preservation
    theorem, order case): on `narrowed doms'`, every assignment of the
    input domains whose slot values are ordered integers `p ≤ q` is
    still an assignment of `doms'`, and `doms'` is pointwise-subset
    the input domains; on `contradiction`, no assignment of the input
    domains orders the two slots. -/
theorem propLeSlot_preserves (i j : Nat) :
    Preserves (DomConstraint.leSlot i j) (propLeSlot i j) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propLeSlot] at h
    obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, q, hx, hy, hpq⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    have hyj : Value.int q ∈ getSlot doms j := hget j _ hy
    cases hb : domMax (getSlot doms j) with
    | none =>
        obtain ⟨b', hb', _⟩ := domMax_of_mem hyj
        rw [hb] at hb'
        exact absurd hb' (by simp)
    | some b =>
        simp only [hb] at h
        cases hm : domMin (getSlot doms i) with
        | none =>
            obtain ⟨m', hm', _⟩ := domMin_of_mem hxi
            rw [hm] at hm'
            exact absurd hm' (by simp)
        | some m =>
            simp only [hm] at h
            obtain ⟨b', hb', hqb'⟩ := domMax_of_mem hyj
            rw [hb] at hb'
            have hbb : b' = b := (Option.some.inj hb').symm
            rw [hbb] at hqb'
            obtain ⟨m', hm', hmp'⟩ := domMin_of_mem hxi
            rw [hm] at hm'
            have hmm : m' = m := (Option.some.inj hm').symm
            rw [hmm] at hmp'
            by_cases hc : (atMostVals b (getSlot doms i)).isEmpty = true ∨
              (atLeastVals m (getSlot doms j)).isEmpty = true
            · rw [if_pos hc] at h
              exact absurd h (by simp)
            · rw [if_neg hc] at h
              have hd : leNarrow b m i j doms = doms' := PropResult.narrowed.inj h
              subst hd
              apply allAssigns_intro
              · have hlen2 : (leNarrow b m i j doms).length = doms.length := by
                  simp only [leNarrow, setSlot_length]
                rw [hlen2]
                exact hlen
              · intro k v hv
                by_cases hkj : k = j
                · rw [hkj] at hv
                  have hvq : v = Value.int q := Option.some.inj (hv.symm.trans hy)
                  subst hvq
                  rw [hkj, getSlot_leNarrow_right (lt_length_of_mem_getSlot doms j _ hyj)]
                  exact mem_atLeastVals.mpr ⟨hyj, q, rfl, by omega⟩
                · by_cases hki : k = i
                  · rw [hki] at hv
                    have hvp : v = Value.int p := Option.some.inj (hv.symm.trans hx)
                    subst hvp
                    rw [hki, getSlot_leNarrow_left (lt_length_of_mem_getSlot doms i _ hxi)
                      (fun hij => hkj (hki.trans hij))]
                    exact mem_atMostVals.mpr ⟨hxi, p, rfl, by omega⟩
                  · rw [getSlot_leNarrow_other (fun h => hki h) (fun h => hkj h)]
                    exact hget k v hv
  · intro doms doms' h
    simp only [propLeSlot] at h
    cases hb : domMax (getSlot doms j) with
    | none => simp only [hb] at h; exact absurd h (by simp)
    | some b =>
        simp only [hb] at h
        cases hm : domMin (getSlot doms i) with
        | none => simp only [hm] at h; exact absurd h (by simp)
        | some m =>
            simp only [hm] at h
            by_cases hc : (atMostVals b (getSlot doms i)).isEmpty = true ∨
              (atLeastVals m (getSlot doms j)).isEmpty = true
            · rw [if_pos hc] at h
              exact absurd h (by simp)
            · rw [if_neg hc] at h
              have hd : leNarrow b m i j doms = doms' := PropResult.narrowed.inj h
              subst hd
              simp only [leNarrow]
              exact DomPointwiseSub.setSlot
                (DomPointwiseSub.setSlot (DomPointwiseSub.refl doms)
                  (fun _ hv => (mem_atMostVals.mp hv).1))
                (fun _ hv => (mem_atLeastVals.mp hv).1)
  · intro doms h a ha hsat
    simp only [propLeSlot] at h
    obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, q, hx, hy, hpq⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    have hyj : Value.int q ∈ getSlot doms j := hget j _ hy
    cases hb : domMax (getSlot doms j) with
    | none =>
        obtain ⟨b', hb', _⟩ := domMax_of_mem hyj
        rw [hb] at hb'
        exact absurd hb' (by simp)
    | some b =>
        simp only [hb] at h
        cases hm : domMin (getSlot doms i) with
        | none =>
            obtain ⟨m', hm', _⟩ := domMin_of_mem hxi
            rw [hm] at hm'
            exact absurd hm' (by simp)
        | some m =>
            simp only [hm] at h
            obtain ⟨b', hb', hqb'⟩ := domMax_of_mem hyj
            rw [hb] at hb'
            have hbb : b' = b := (Option.some.inj hb').symm
            rw [hbb] at hqb'
            obtain ⟨m', hm', hmp'⟩ := domMin_of_mem hxi
            rw [hm] at hm'
            have hmm : m' = m := (Option.some.inj hm').symm
            rw [hmm] at hmp'
            by_cases hc : (atMostVals b (getSlot doms i)).isEmpty = true ∨
              (atLeastVals m (getSlot doms j)).isEmpty = true
            · rw [if_pos hc] at h
              rcases hc with hcl | hcr
              · have hmem : Value.int p ∈ atMostVals b (getSlot doms i) :=
                  mem_atMostVals.mpr ⟨hxi, p, rfl, by omega⟩
                rw [List.isEmpty_iff.mp hcl] at hmem
                exact absurd hmem (by simp)
              · have hmem : Value.int q ∈ atLeastVals m (getSlot doms j) :=
                  mem_atLeastVals.mpr ⟨hyj, q, rfl, by omega⟩
                rw [List.isEmpty_iff.mp hcr] at hmem
                exact absurd hmem (by simp)
            · rw [if_neg hc] at h
              exact absurd h (by simp)

/-! ## The constant-equality propagator -/

/-- **The constant-equality propagator** (`int_eq` style, slot vs
    constant): slot `i`'s domain narrows to the constant when the
    constant is present; `contradiction` when it is absent. -/
def propConstEq (i : Nat) (v : Value) (doms : List (List Value)) : PropResult :=
  if valueMemB v (getSlot doms i) = true then
    .narrowed (setSlot doms i [v])
  else
    .contradiction

/-- **Preservation for `propConstEq`** (PLAN 6.3's local preservation
    theorem, constant case): on `narrowed doms'`, every assignment of
    the input domains whose slot `i` carries the constant is still an
    assignment of `doms'`, and `doms'` is pointwise-subset the input
    domains; on `contradiction`, no assignment of the input domains
    carries the constant at slot `i`. -/
theorem propConstEq_preserves (i : Nat) (v : Value) :
    Preserves (DomConstraint.constEq i v) (propConstEq i v) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propConstEq] at h
    by_cases hc : valueMemB v (getSlot doms i) = true
    · rw [if_pos hc] at h
      have hd : setSlot doms i [v] = doms' := PropResult.narrowed.inj h
      subst hd
      obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
      apply allAssigns_intro
      · rw [setSlot_length]
        exact hlen
      · intro k v' hv'
        by_cases hki : k = i
        · rw [hki] at hv'
          have hvv : v' = v := Option.some.inj (hv'.symm.trans hsat)
          rw [hki, getSlot_setSlot_eq doms [v] i
            (lt_length_of_mem_getSlot doms i v (valueMemB_iff.mp hc))]
          exact List.mem_singleton.mpr hvv
        · rw [getSlot_setSlot_of_ne doms [v] i k hki]
          exact hget k v' hv'
    · rw [if_neg hc] at h
      exact absurd h (by simp)
  · intro doms doms' h
    simp only [propConstEq] at h
    by_cases hc : valueMemB v (getSlot doms i) = true
    · rw [if_pos hc] at h
      have hd : setSlot doms i [v] = doms' := PropResult.narrowed.inj h
      subst hd
      exact DomPointwiseSub.setSlot (DomPointwiseSub.refl doms)
        (fun w hw => by
          have hwv : w = v := List.mem_singleton.mp hw
          subst hwv
          exact valueMemB_iff.mp hc)
    · rw [if_neg hc] at h
      exact absurd h (by simp)
  · intro doms _h a ha hsat
    simp only [propConstEq] at _h
    by_cases hc : valueMemB v (getSlot doms i) = true
    · rw [if_pos hc] at _h
      exact absurd _h (by simp)
    · obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
      exact absurd (valueMemB_iff.mpr (hget i v hsat)) hc

/-! ## The plus propagator (bounds propagation) -/

/-- The plus narrowing: each of the three slots takes its implied
    interval, each filter computed once (on the *input* domains — the
    bounds are sound independently, so coinciding slot positions are
    harmless: whichever write lands last keeps a sound domain). -/
private def plusNarrow (di' dj' dk' : List Value) (i j k : Nat)
    (doms : List (List Value)) : List (List Value) :=
  setSlot (setSlot (setSlot doms i di') j dj') k dk'

/-- The bounded plus propagation: given all three domains' integer
    extrema, narrow each slot to its implied interval;
    `contradiction` when any side empties. -/
private def propPlusBounded (ilo ihi jlo jhi klo khi : Int) (i j k : Nat)
    (doms : List (List Value)) : PropResult :=
  let di' := atLeastVals (klo - jhi) (atMostVals (khi - jlo) (getSlot doms i))
  let dj' := atLeastVals (klo - ihi) (atMostVals (khi - ilo) (getSlot doms j))
  let dk' := atLeastVals (ilo + jlo) (atMostVals (ihi + jhi) (getSlot doms k))
  if di'.isEmpty = true ∨ dj'.isEmpty = true ∨ dk'.isEmpty = true then
    .contradiction
  else
    .narrowed (plusNarrow di' dj' dk' i j k doms)

/-- **The plus propagator** (`int_plus` style on three slots): bounds
    propagation for `x + y = z` — slot `i` keeps values `p` with
    `zmin - ymax ≤ p ≤ zmax - ymin`, slot `j` symmetrically, slot `k`
    keeps values in `[xmin + ymin, xmax + ymax]`.  `contradiction`
    when any side empties or any of the three domains has no
    integers (a satisfying assignment needs an integer in each). -/
def propPlusSlot (i j k : Nat) (doms : List (List Value)) : PropResult :=
  match domMin (getSlot doms i) with
  | none => .contradiction
  | some ilo =>
      match domMax (getSlot doms i) with
      | none => .contradiction
      | some ihi =>
          match domMin (getSlot doms j) with
          | none => .contradiction
          | some jlo =>
              match domMax (getSlot doms j) with
              | none => .contradiction
              | some jhi =>
                  match domMin (getSlot doms k) with
                  | none => .contradiction
                  | some klo =>
                      match domMax (getSlot doms k) with
                      | none => .contradiction
                      | some khi => propPlusBounded ilo ihi jlo jhi klo khi i j k doms

/-- Reading back the three written slots of a `plusNarrow` (the
    `k`-write is outermost, then `j`, then `i`). -/
private theorem getSlot_plusNarrow_k {di' dj' dk' : List Value} {i j k : Nat}
    {doms : List (List Value)} (hk : k < doms.length) :
    getSlot (plusNarrow di' dj' dk' i j k doms) k = dk' := by
  simp only [plusNarrow]
  rw [getSlot_setSlot_eq (setSlot (setSlot doms i di') j dj') dk' k
    (by rw [setSlot_length, setSlot_length]; exact hk)]

private theorem getSlot_plusNarrow_j {di' dj' dk' : List Value} {i j k : Nat}
    {doms : List (List Value)} (hj : j < doms.length) (hjk : j ≠ k) :
    getSlot (plusNarrow di' dj' dk' i j k doms) j = dj' := by
  simp only [plusNarrow]
  rw [getSlot_setSlot_of_ne (setSlot (setSlot doms i di') j dj') dk' k j hjk,
    getSlot_setSlot_eq (setSlot doms i di') dj' j
    (by rw [setSlot_length]; exact hj)]

private theorem getSlot_plusNarrow_i {di' dj' dk' : List Value} {i j k : Nat}
    {doms : List (List Value)} (hi : i < doms.length) (hij : i ≠ j) (hik : i ≠ k) :
    getSlot (plusNarrow di' dj' dk' i j k doms) i = di' := by
  simp only [plusNarrow]
  rw [getSlot_setSlot_of_ne (setSlot (setSlot doms i di') j dj') dk' k i hik,
    getSlot_setSlot_of_ne (setSlot doms i di') dj' j i hij,
    getSlot_setSlot_eq doms di' i hi]

private theorem getSlot_plusNarrow_other {di' dj' dk' : List Value} {i j k m : Nat}
    {doms : List (List Value)} (hmi : m ≠ i) (hmj : m ≠ j) (hmk : m ≠ k) :
    getSlot (plusNarrow di' dj' dk' i j k doms) m = getSlot doms m := by
  simp only [plusNarrow]
  rw [getSlot_setSlot_of_ne (setSlot (setSlot doms i di') j dj') dk' k m hmk,
    getSlot_setSlot_of_ne (setSlot doms i di') dj' j m hmj,
    getSlot_setSlot_of_ne doms di' i m hmi]

/-- **Preservation for `propPlusSlot`** (PLAN 6.3's local preservation
    theorem, plus case): on `narrowed doms'`, every assignment of the
    input domains whose slot values are integers `p + q = r` is still
    an assignment of `doms'` (each slot's narrowed interval contains
    its satisfying value — `p ≥ zmin - ymax` etc. follow from the
    domain-extrema bounds and the equation), and `doms'` is
    pointwise-subset the input domains; on `contradiction`, no
    assignment of the input domains solves the equation. -/
theorem propPlusSlot_preserves (i j k : Nat) :
    Preserves (DomConstraint.plusSlot i j k) (propPlusSlot i j k) := by
  constructor
  · -- narrowing soundness
    intro doms doms' h a ha hsat
    simp only [propPlusSlot] at h
    obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, q, r, hx, hy, hz, hpqr⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    have hyj : Value.int q ∈ getSlot doms j := hget j _ hy
    have hzk : Value.int r ∈ getSlot doms k := hget k _ hz
    cases h1 : domMin (getSlot doms i) with
    | none => rw [h1] at h; exact absurd h (by simp)
    | some ilo =>
        simp only [h1] at h
        cases h2 : domMax (getSlot doms i) with
        | none => rw [h2] at h; exact absurd h (by simp)
        | some ihi =>
            simp only [h2] at h
            cases h3 : domMin (getSlot doms j) with
            | none => rw [h3] at h; exact absurd h (by simp)
            | some jlo =>
                simp only [h3] at h
                cases h4 : domMax (getSlot doms j) with
                | none => rw [h4] at h; exact absurd h (by simp)
                | some jhi =>
                    simp only [h4] at h
                    cases h5 : domMin (getSlot doms k) with
                    | none => rw [h5] at h; exact absurd h (by simp)
                    | some klo =>
                        simp only [h5] at h
                        cases h6 : domMax (getSlot doms k) with
                        | none => rw [h6] at h; exact absurd h (by simp)
                        | some khi =>
                            simp only [h6, propPlusBounded] at h
                            -- pin the extrema to the satisfying values' bounds
                            obtain ⟨m1, hm1, hplo⟩ := domMin_of_mem hxi
                            rw [h1] at hm1
                            have hilo : m1 = ilo := (Option.some.inj hm1).symm
                            rw [hilo] at hplo
                            obtain ⟨m2, hm2, hphi⟩ := domMax_of_mem hxi
                            rw [h2] at hm2
                            have hihi : m2 = ihi := (Option.some.inj hm2).symm
                            rw [hihi] at hphi
                            obtain ⟨m3, hm3, hqlo⟩ := domMin_of_mem hyj
                            rw [h3] at hm3
                            have hjlo : m3 = jlo := (Option.some.inj hm3).symm
                            rw [hjlo] at hqlo
                            obtain ⟨m4, hm4, hqhi⟩ := domMax_of_mem hyj
                            rw [h4] at hm4
                            have hjhi : m4 = jhi := (Option.some.inj hm4).symm
                            rw [hjhi] at hqhi
                            obtain ⟨m5, hm5, hrlo⟩ := domMin_of_mem hzk
                            rw [h5] at hm5
                            have hklo : m5 = klo := (Option.some.inj hm5).symm
                            rw [hklo] at hrlo
                            obtain ⟨m6, hm6, hrhi⟩ := domMax_of_mem hzk
                            rw [h6] at hm6
                            have hkhi : m6 = khi := (Option.some.inj hm6).symm
                            rw [hkhi] at hrhi
                            by_cases hc : (atLeastVals (klo - jhi)
                                (atMostVals (khi - jlo) (getSlot doms i))).isEmpty = true ∨
                              (atLeastVals (klo - ihi)
                                (atMostVals (khi - ilo) (getSlot doms j))).isEmpty = true ∨
                              (atLeastVals (ilo + jlo)
                                (atMostVals (ihi + jhi) (getSlot doms k))).isEmpty = true
                            · rw [if_pos hc] at h
                              exact absurd h (by simp)
                            · rw [if_neg hc] at h
                              have hd : plusNarrow
                                  (atLeastVals (klo - jhi)
                                    (atMostVals (khi - jlo) (getSlot doms i)))
                                  (atLeastVals (klo - ihi)
                                    (atMostVals (khi - ilo) (getSlot doms j)))
                                  (atLeastVals (ilo + jlo)
                                    (atMostVals (ihi + jhi) (getSlot doms k)))
                                  i j k doms = doms' := PropResult.narrowed.inj h
                              subst hd
                              apply allAssigns_intro
                              · have hlen2 : (plusNarrow
                                  (atLeastVals (klo - jhi)
                                    (atMostVals (khi - jlo) (getSlot doms i)))
                                  (atLeastVals (klo - ihi)
                                    (atMostVals (khi - ilo) (getSlot doms j)))
                                  (atLeastVals (ilo + jlo)
                                    (atMostVals (ihi + jhi) (getSlot doms k)))
                                  i j k doms).length = doms.length := by
                                  simp only [plusNarrow, setSlot_length]
                                rw [hlen2]
                                exact hlen
                              · intro m v hv
                                by_cases hmk : m = k
                                · rw [hmk] at hv
                                  have hvr : v = Value.int r :=
                                    Option.some.inj (hv.symm.trans hz)
                                  subst hvr
                                  rw [hmk, getSlot_plusNarrow_k
                                    (lt_length_of_mem_getSlot doms k _ hzk)]
                                  exact mem_atLeastVals_atMostVals.mpr
                                    ⟨hzk, r, rfl, by omega, by omega⟩
                                · by_cases hmj : m = j
                                  · rw [hmj] at hv
                                    have hvq : v = Value.int q :=
                                      Option.some.inj (hv.symm.trans hy)
                                    subst hvq
                                    rw [hmj, getSlot_plusNarrow_j
                                      (lt_length_of_mem_getSlot doms j _ hyj)
                                      (fun hjk => hmk (hmj.trans hjk))]
                                    exact mem_atLeastVals_atMostVals.mpr
                                      ⟨hyj, q, rfl, by omega, by omega⟩
                                  · by_cases hmi : m = i
                                    · rw [hmi] at hv
                                      have hvp : v = Value.int p :=
                                        Option.some.inj (hv.symm.trans hx)
                                      subst hvp
                                      rw [hmi, getSlot_plusNarrow_i
                                        (lt_length_of_mem_getSlot doms i _ hxi)
                                        (fun hij => hmj (hmi.trans hij))
                                        (fun hik => hmk (hmi.trans hik))]
                                      exact mem_atLeastVals_atMostVals.mpr
                                        ⟨hxi, p, rfl, by omega, by omega⟩
                                    · rw [getSlot_plusNarrow_other
                                        (fun h => hmi h) (fun h => hmj h)
                                        (fun h => hmk h)]
                                      exact hget m v hv
  · -- subset
    intro doms doms' h
    simp only [propPlusSlot] at h
    cases h1 : domMin (getSlot doms i) with
    | none => rw [h1] at h; exact absurd h (by simp)
    | some ilo =>
        simp only [h1] at h
        cases h2 : domMax (getSlot doms i) with
        | none => rw [h2] at h; exact absurd h (by simp)
        | some ihi =>
            simp only [h2] at h
            cases h3 : domMin (getSlot doms j) with
            | none => rw [h3] at h; exact absurd h (by simp)
            | some jlo =>
                simp only [h3] at h
                cases h4 : domMax (getSlot doms j) with
                | none => rw [h4] at h; exact absurd h (by simp)
                | some jhi =>
                    simp only [h4] at h
                    cases h5 : domMin (getSlot doms k) with
                    | none => rw [h5] at h; exact absurd h (by simp)
                    | some klo =>
                        simp only [h5] at h
                        cases h6 : domMax (getSlot doms k) with
                        | none => rw [h6] at h; exact absurd h (by simp)
                        | some khi =>
                            simp only [h6, propPlusBounded] at h
                            by_cases hc : (atLeastVals (klo - jhi)
                                (atMostVals (khi - jlo) (getSlot doms i))).isEmpty = true ∨
                              (atLeastVals (klo - ihi)
                                (atMostVals (khi - ilo) (getSlot doms j))).isEmpty = true ∨
                              (atLeastVals (ilo + jlo)
                                (atMostVals (ihi + jhi) (getSlot doms k))).isEmpty = true
                            · rw [if_pos hc] at h
                              exact absurd h (by simp)
                            · rw [if_neg hc] at h
                              have hd : plusNarrow
                                  (atLeastVals (klo - jhi)
                                    (atMostVals (khi - jlo) (getSlot doms i)))
                                  (atLeastVals (klo - ihi)
                                    (atMostVals (khi - ilo) (getSlot doms j)))
                                  (atLeastVals (ilo + jlo)
                                    (atMostVals (ihi + jhi) (getSlot doms k)))
                                  i j k doms = doms' := PropResult.narrowed.inj h
                              subst hd
                              simp only [plusNarrow]
                              exact DomPointwiseSub.setSlot
                                (DomPointwiseSub.setSlot
                                  (DomPointwiseSub.setSlot (DomPointwiseSub.refl doms)
                                    (fun _ hv => (mem_atLeastVals_atMostVals.mp hv).1))
                                  (fun _ hv => (mem_atLeastVals_atMostVals.mp hv).1))
                                (fun _ hv => (mem_atLeastVals_atMostVals.mp hv).1)
  · -- contradiction soundness
    intro doms h a ha hsat
    simp only [propPlusSlot] at h
    obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, q, r, hx, hy, hz, hpqr⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    have hyj : Value.int q ∈ getSlot doms j := hget j _ hy
    have hzk : Value.int r ∈ getSlot doms k := hget k _ hz
    cases h1 : domMin (getSlot doms i) with
    | none =>
        obtain ⟨m, hm, _⟩ := domMin_of_mem hxi
        rw [h1] at hm
        exact absurd hm (by simp)
    | some ilo =>
        simp only [h1] at h
        cases h2 : domMax (getSlot doms i) with
        | none =>
            obtain ⟨m, hm, _⟩ := domMax_of_mem hxi
            rw [h2] at hm
            exact absurd hm (by simp)
        | some ihi =>
            simp only [h2] at h
            cases h3 : domMin (getSlot doms j) with
            | none =>
                obtain ⟨m, hm, _⟩ := domMin_of_mem hyj
                rw [h3] at hm
                exact absurd hm (by simp)
            | some jlo =>
                simp only [h3] at h
                cases h4 : domMax (getSlot doms j) with
                | none =>
                    obtain ⟨m, hm, _⟩ := domMax_of_mem hyj
                    rw [h4] at hm
                    exact absurd hm (by simp)
                | some jhi =>
                    simp only [h4] at h
                    cases h5 : domMin (getSlot doms k) with
                    | none =>
                        obtain ⟨m, hm, _⟩ := domMin_of_mem hzk
                        rw [h5] at hm
                        exact absurd hm (by simp)
                    | some klo =>
                        simp only [h5] at h
                        cases h6 : domMax (getSlot doms k) with
                        | none =>
                            obtain ⟨m, hm, _⟩ := domMax_of_mem hzk
                            rw [h6] at hm
                            exact absurd hm (by simp)
                        | some khi =>
                            simp only [h6, propPlusBounded] at h
                            -- pin the extrema to the satisfying values' bounds
                            obtain ⟨m1, hm1, hplo⟩ := domMin_of_mem hxi
                            rw [h1] at hm1
                            have hilo : m1 = ilo := (Option.some.inj hm1).symm
                            rw [hilo] at hplo
                            obtain ⟨m2, hm2, hphi⟩ := domMax_of_mem hxi
                            rw [h2] at hm2
                            have hihi : m2 = ihi := (Option.some.inj hm2).symm
                            rw [hihi] at hphi
                            obtain ⟨m3, hm3, hqlo⟩ := domMin_of_mem hyj
                            rw [h3] at hm3
                            have hjlo : m3 = jlo := (Option.some.inj hm3).symm
                            rw [hjlo] at hqlo
                            obtain ⟨m4, hm4, hqhi⟩ := domMax_of_mem hyj
                            rw [h4] at hm4
                            have hjhi : m4 = jhi := (Option.some.inj hm4).symm
                            rw [hjhi] at hqhi
                            obtain ⟨m5, hm5, hrlo⟩ := domMin_of_mem hzk
                            rw [h5] at hm5
                            have hklo : m5 = klo := (Option.some.inj hm5).symm
                            rw [hklo] at hrlo
                            obtain ⟨m6, hm6, hrhi⟩ := domMax_of_mem hzk
                            rw [h6] at hm6
                            have hkhi : m6 = khi := (Option.some.inj hm6).symm
                            rw [hkhi] at hrhi
                            by_cases hc : (atLeastVals (klo - jhi)
                                (atMostVals (khi - jlo) (getSlot doms i))).isEmpty = true ∨
                              (atLeastVals (klo - ihi)
                                (atMostVals (khi - ilo) (getSlot doms j))).isEmpty = true ∨
                              (atLeastVals (ilo + jlo)
                                (atMostVals (ihi + jhi) (getSlot doms k))).isEmpty = true
                            · rw [if_pos hc] at h
                              rcases hc with hci | hcj | hck
                              · have hmem : Value.int p ∈ atLeastVals (klo - jhi)
                                    (atMostVals (khi - jlo) (getSlot doms i)) :=
                                  mem_atLeastVals_atMostVals.mpr
                                    ⟨hxi, p, rfl, by omega, by omega⟩
                                rw [List.isEmpty_iff.mp hci] at hmem
                                exact absurd hmem (by simp)
                              · have hmem : Value.int q ∈ atLeastVals (klo - ihi)
                                    (atMostVals (khi - ilo) (getSlot doms j)) :=
                                  mem_atLeastVals_atMostVals.mpr
                                    ⟨hyj, q, rfl, by omega, by omega⟩
                                rw [List.isEmpty_iff.mp hcj] at hmem
                                exact absurd hmem (by simp)
                              · have hmem : Value.int r ∈ atLeastVals (ilo + jlo)
                                    (atMostVals (ihi + jhi) (getSlot doms k)) :=
                                  mem_atLeastVals_atMostVals.mpr
                                    ⟨hzk, r, rfl, by omega, by omega⟩
                                rw [List.isEmpty_iff.mp hck] at hmem
                                exact absurd hmem (by simp)
                            · rw [if_neg hc] at h
                              exact absurd h (by simp)

/-! ## The constant-bound order propagators -/

/-- **The upper-bound propagator** (`int_le(x, c)` style, slot vs
    constant): slot `i`'s domain keeps its integer values `≤ c`;
    `contradiction` when that empties (no integer in the domain can
    satisfy `p ≤ c`). -/
def propLeConstHi (i : Nat) (c : Int) (doms : List (List Value)) : PropResult :=
  let d' := atMostVals c (getSlot doms i)
  if d'.isEmpty = true then .contradiction
  else .narrowed (setSlot doms i d')

/-- **Preservation for `propLeConstHi`** (PLAN 6.3's local
    preservation theorem, upper-bound case): on `narrowed doms'`,
    every assignment of the input domains whose slot `i` value is an
    integer `p ≤ c` is still an assignment of `doms'`, and `doms'`
    is pointwise-subset the input domains; on `contradiction`, no
    assignment of the input domains bounds slot `i` by `c`. -/
theorem propLeConstHi_preserves (i : Nat) (c : Int) :
    Preserves (DomConstraint.leConstHi i c) (propLeConstHi i c) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propLeConstHi] at h
    obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, hx, hpc⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    by_cases hc : (atMostVals c (getSlot doms i)).isEmpty = true
    · rw [if_pos hc] at h
      exact absurd h (by simp)
    · rw [if_neg hc] at h
      have hd : setSlot doms i (atMostVals c (getSlot doms i)) = doms' :=
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
          rw [hmi, getSlot_setSlot_eq doms (atMostVals c (getSlot doms i)) i
            (lt_length_of_mem_getSlot doms i _ hxi)]
          exact mem_atMostVals.mpr ⟨hxi, p, rfl, hpc⟩
        · rw [getSlot_setSlot_of_ne doms (atMostVals c (getSlot doms i)) i m hmi]
          exact hget m v hv
  · intro doms doms' h
    simp only [propLeConstHi] at h
    by_cases hc : (atMostVals c (getSlot doms i)).isEmpty = true
    · rw [if_pos hc] at h
      exact absurd h (by simp)
    · rw [if_neg hc] at h
      have hd : setSlot doms i (atMostVals c (getSlot doms i)) = doms' :=
        PropResult.narrowed.inj h
      subst hd
      exact DomPointwiseSub.setSlot (DomPointwiseSub.refl doms)
        (fun _ hv => (mem_atMostVals.mp hv).1)
  · intro doms h a ha hsat
    simp only [propLeConstHi] at h
    obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, hx, hpc⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    by_cases hc : (atMostVals c (getSlot doms i)).isEmpty = true
    · rw [if_pos hc] at h
      have hmem : Value.int p ∈ atMostVals c (getSlot doms i) :=
        mem_atMostVals.mpr ⟨hxi, p, rfl, hpc⟩
      rw [List.isEmpty_iff.mp hc] at hmem
      exact absurd hmem (by simp)
    · rw [if_neg hc] at h
      exact absurd h (by simp)

/-- **The lower-bound propagator** (`int_le(c, x)` style, constant vs
    slot): slot `i`'s domain keeps its integer values `≥ c`;
    `contradiction` when that empties. -/
def propLeConstLo (i : Nat) (c : Int) (doms : List (List Value)) : PropResult :=
  let d' := atLeastVals c (getSlot doms i)
  if d'.isEmpty = true then .contradiction
  else .narrowed (setSlot doms i d')

/-- **Preservation for `propLeConstLo`** (the symmetric local
    preservation theorem, lower-bound case). -/
theorem propLeConstLo_preserves (i : Nat) (c : Int) :
    Preserves (DomConstraint.leConstLo i c) (propLeConstLo i c) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propLeConstLo] at h
    obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, hx, hcp⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    by_cases hc : (atLeastVals c (getSlot doms i)).isEmpty = true
    · rw [if_pos hc] at h
      exact absurd h (by simp)
    · rw [if_neg hc] at h
      have hd : setSlot doms i (atLeastVals c (getSlot doms i)) = doms' :=
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
          rw [hmi, getSlot_setSlot_eq doms (atLeastVals c (getSlot doms i)) i
            (lt_length_of_mem_getSlot doms i _ hxi)]
          exact mem_atLeastVals.mpr ⟨hxi, p, rfl, hcp⟩
        · rw [getSlot_setSlot_of_ne doms (atLeastVals c (getSlot doms i)) i m hmi]
          exact hget m v hv
  · intro doms doms' h
    simp only [propLeConstLo] at h
    by_cases hc : (atLeastVals c (getSlot doms i)).isEmpty = true
    · rw [if_pos hc] at h
      exact absurd h (by simp)
    · rw [if_neg hc] at h
      have hd : setSlot doms i (atLeastVals c (getSlot doms i)) = doms' :=
        PropResult.narrowed.inj h
      subst hd
      exact DomPointwiseSub.setSlot (DomPointwiseSub.refl doms)
        (fun _ hv => (mem_atLeastVals.mp hv).1)
  · intro doms h a ha hsat
    simp only [propLeConstLo] at h
    obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, hx, hcp⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    by_cases hc : (atLeastVals c (getSlot doms i)).isEmpty = true
    · rw [if_pos hc] at h
      have hmem : Value.int p ∈ atLeastVals c (getSlot doms i) :=
        mem_atLeastVals.mpr ⟨hxi, p, rfl, hcp⟩
      rw [List.isEmpty_iff.mp hc] at hmem
      exact absurd hmem (by simp)
    · rw [if_neg hc] at h
      exact absurd h (by simp)


end LeanFzn.Solver.Propagation.DomainFiltering

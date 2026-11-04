import LeanFzn.Solver.Propagation.DomainConstraints.Repr
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation
open LeanFzn.Solver.Core
open LeanFzn LeanFzn.Semantics.Evaluation LeanFzn.Solver.Core List
open LeanFzn.Solver.Propagation.DomainFiltering.Internal

namespace LeanFzn.Solver.Propagation.DomainFiltering

/-! ## The arithmetic propagators (`times`, `min`, `max`, `abs`)

Each of the four new constraint kinds mirrors the bounds-propagation
pattern of `propPlusSlot`: from the integer extrema of the involved
slot domains, each slot keeps exactly the values that can still
participate in a satisfying assignment:

* `propTimesSlot i j k` — `p * q = r`: slot `i` keeps `p` when the
  (necessary) interval condition `min (p·jlo) (p·jhi) ≤ khi` and
  `klo ≤ max (p·jlo) (p·jhi)` holds — the product `p·q` with `q`
  between `jlo` and `jhi` stays within the two corner products, so a
  result in `[klo, khi]` is impossible outside; slot `j` symmetrically
  (against the extrema of slot `i`); slot `k` keeps only the corner
  interval `[cornerMin ilo ihi jlo jhi, cornerMax ilo ihi jlo jhi]`;
* `propMinSlot i j k` — `min p q = r`: slot `i` keeps `p` when
  `min p jlo ≤ khi` and `klo ≤ min p jhi` (`min` is monotone in both
  arguments, so these are necessary), slot `j` symmetrically, slot `k`
  keeps `[min ilo jlo, min ihi jhi]`; `propMaxSlot` mirrors it with
  `max`, whose monotonicity gives the identical necessary conditions;
* `propAbsSlot i k` — `absValue p = r`: slot `i` keeps `p` with
  `klo ≤ absValue p ≤ khi` (exact — `absValue` is defined), slot `k`
  keeps the nonneg interval `[0, max (absValue ilo) (absValue ihi)]`.

Each propagator returns `contradiction` when a slot domain carries no
integers (a satisfying assignment needs an integer in each involved
slot) or when any narrowed side empties. -/

/-- The three-slot narrowing: each of the three slots takes its
    narrowed list, each filter computed once (on the *input* domains —
    every bound argument holds for any satisfying assignment
    independently, so coinciding slot positions are harmless). -/
private def threeNarrow (di' dj' dk' : List Value) (i j k : Nat)
    (doms : List (List Value)) : List (List Value) :=
  setSlot (setSlot (setSlot doms i di') j dj') k dk'

/-- Reading back the three written slots of a `threeNarrow` (the
    `k`-write is outermost, then `j`, then `i`). -/
private theorem getSlot_threeNarrow_k {di' dj' dk' : List Value} {i j k : Nat}
    {doms : List (List Value)} (hk : k < doms.length) :
    getSlot (threeNarrow di' dj' dk' i j k doms) k = dk' := by
  simp only [threeNarrow]
  rw [getSlot_setSlot_eq (setSlot (setSlot doms i di') j dj') dk' k
    (by rw [setSlot_length, setSlot_length]; exact hk)]

private theorem getSlot_threeNarrow_j {di' dj' dk' : List Value} {i j k : Nat}
    {doms : List (List Value)} (hj : j < doms.length) (hjk : j ≠ k) :
    getSlot (threeNarrow di' dj' dk' i j k doms) j = dj' := by
  simp only [threeNarrow]
  rw [getSlot_setSlot_of_ne (setSlot (setSlot doms i di') j dj') dk' k j hjk,
    getSlot_setSlot_eq (setSlot doms i di') dj' j
    (by rw [setSlot_length]; exact hj)]

private theorem getSlot_threeNarrow_i {di' dj' dk' : List Value} {i j k : Nat}
    {doms : List (List Value)} (hi : i < doms.length) (hij : i ≠ j) (hik : i ≠ k) :
    getSlot (threeNarrow di' dj' dk' i j k doms) i = di' := by
  simp only [threeNarrow]
  rw [getSlot_setSlot_of_ne (setSlot (setSlot doms i di') j dj') dk' k i hik,
    getSlot_setSlot_of_ne (setSlot doms i di') dj' j i hij,
    getSlot_setSlot_eq doms di' i hi]

private theorem getSlot_threeNarrow_other {di' dj' dk' : List Value} {i j k m : Nat}
    {doms : List (List Value)} (hmi : m ≠ i) (hmj : m ≠ j) (hmk : m ≠ k) :
    getSlot (threeNarrow di' dj' dk' i j k doms) m = getSlot doms m := by
  simp only [threeNarrow]
  rw [getSlot_setSlot_of_ne (setSlot (setSlot doms i di') j dj') dk' k m hmk,
    getSlot_setSlot_of_ne (setSlot doms i di') dj' j m hmj,
    getSlot_setSlot_of_ne doms di' i m hmi]

/-! ### The min propagator -/

/-- The keep test for a `min` operand: an integer value `v = .int p`
    can participate in a satisfying `min p q = r` with `q ∈ [jlo, jhi]`
    and `r ∈ [klo, khi]` only when both necessary interval conditions
    hold (monotonicity of `min` in each argument). Non-integer values
    are rejected. -/
private def minKeepB (v : Value) (jlo jhi klo khi : Int) : Bool :=
  match v with
  | .int p => decide (min p jlo ≤ khi) && decide (klo ≤ min p jhi)
  | _ => false

private theorem mem_minKeepB_iff {v : Value} {jlo jhi klo khi : Int} :
    minKeepB v jlo jhi klo khi = true ↔
      ∃ p, v = .int p ∧ min p jlo ≤ khi ∧ klo ≤ min p jhi := by
  constructor
  · intro h
    cases v with
    | int p =>
      simp only [minKeepB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨p, rfl, h.1, h.2⟩
    | _ => contradiction
  · rintro ⟨p, rfl, h1, h2⟩
    simp only [minKeepB, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h1, h2⟩

/-- A satisfying triple keeps both `min` operands. -/
private theorem minKeepB_of_satisfying {p q r jlo jhi klo khi : Int}
    (hq1 : jlo ≤ q) (hq2 : q ≤ jhi) (hr1 : klo ≤ r) (hr2 : r ≤ khi)
    (hmin : min p q = r) :
    minKeepB (.int p) jlo jhi klo khi = true := by
  simp only [minKeepB, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨le_trans (min_le_min (le_refl p) hq1) (hmin ▸ hr2),
    le_trans (hmin ▸ hr1) (min_le_min (le_refl p) hq2)⟩

/-- The bounded min propagation: given all three domains' integer
    extrema, narrow each slot; `contradiction` when any side empties. -/
private def propMinBounded (ilo ihi jlo jhi klo khi : Int) (i j k : Nat)
    (doms : List (List Value)) : PropResult :=
  let di' := (getSlot doms i).filter (fun p => minKeepB p jlo jhi klo khi)
  let dj' := (getSlot doms j).filter (fun q => minKeepB q ilo ihi klo khi)
  let dk' := atLeastVals (min ilo jlo) (atMostVals (min ihi jhi) (getSlot doms k))
  if di'.isEmpty = true ∨ dj'.isEmpty = true ∨ dk'.isEmpty = true then
    .contradiction
  else
    .narrowed (threeNarrow di' dj' dk' i j k doms)

/-- **The min propagator** (`int_min` style on three slots): bounds
    propagation for `min p q = r` — slot `i` keeps exactly the values
    passing the necessary `min` interval conditions, slot `j`
    symmetrically, slot `k` keeps `[min ilo jlo, min ihi jhi]`.
    `contradiction` when any side empties or any domain has no
    integers. -/
def propMinSlot (i j k : Nat) (doms : List (List Value)) : PropResult :=
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
                      | some khi => propMinBounded ilo ihi jlo jhi klo khi i j k doms

/-- **Preservation for `propMinSlot`** (PLAN 6.3's local preservation
    theorem, min case): on `narrowed doms'`, every assignment of the
    input domains whose slot values are integers `min p q = r` is still
    an assignment of `doms'`, and `doms'` is pointwise-subset the input
    domains; on `contradiction`, no assignment of the input domains
    solves the equation. -/
theorem propMinSlot_preserves (i j k : Nat) :
    Preserves (DomConstraint.minSlot i j k) (propMinSlot i j k) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propMinSlot] at h
    obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, q, r, hx, hy, hz, hmin⟩ := hsat
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
                            simp only [h6, propMinBounded] at h
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
                            have hlo_bounds : min ilo jlo ≤ r := by
                              have h1 : min ilo jlo ≤ p := le_trans (min_le_left ilo jlo) hplo
                              have h2 : min ilo jlo ≤ q := le_trans (min_le_right ilo jlo) hqlo
                              have h3 : min ilo jlo ≤ min p q := le_min_iff.mpr ⟨h1, h2⟩
                              rw [hmin] at h3
                              exact h3
                            have hhi_bounds : r ≤ min ihi jhi := by
                              have h3 : min p q ≤ min ihi jhi := min_le_min hphi hqhi
                              rw [hmin] at h3
                              exact h3
                            by_cases hc : ((getSlot doms i).filter
                                (fun p => minKeepB p jlo jhi klo khi)).isEmpty = true ∨
                              ((getSlot doms j).filter
                                (fun q => minKeepB q ilo ihi klo khi)).isEmpty = true ∨
                              (atLeastVals (min ilo jlo)
                                (atMostVals (min ihi jhi) (getSlot doms k))).isEmpty = true
                            · rw [if_pos hc] at h
                              exact absurd h (by simp)
                            · rw [if_neg hc] at h
                              have hd : threeNarrow
                                  ((getSlot doms i).filter
                                    (fun p => minKeepB p jlo jhi klo khi))
                                  ((getSlot doms j).filter
                                    (fun q => minKeepB q ilo ihi klo khi))
                                  (atLeastVals (min ilo jlo)
                                    (atMostVals (min ihi jhi) (getSlot doms k)))
                                  i j k doms = doms' := PropResult.narrowed.inj h
                              subst hd
                              apply allAssigns_intro
                              · have hlen2 : (threeNarrow
                                  ((getSlot doms i).filter
                                    (fun p => minKeepB p jlo jhi klo khi))
                                  ((getSlot doms j).filter
                                    (fun q => minKeepB q ilo ihi klo khi))
                                  (atLeastVals (min ilo jlo)
                                    (atMostVals (min ihi jhi) (getSlot doms k)))
                                  i j k doms).length = doms.length := by
                                  simp only [threeNarrow, setSlot_length]
                                rw [hlen2]
                                exact hlen
                              · intro m v hv
                                by_cases hmk : m = k
                                · rw [hmk] at hv
                                  have hvr : v = Value.int r :=
                                    Option.some.inj (hv.symm.trans hz)
                                  subst hvr
                                  rw [hmk, getSlot_threeNarrow_k
                                    (lt_length_of_mem_getSlot doms k _ hzk)]
                                  exact mem_atLeastVals_atMostVals.mpr
                                    ⟨hzk, r, rfl, hlo_bounds, hhi_bounds⟩
                                · by_cases hmj : m = j
                                  · rw [hmj] at hv
                                    have hvq : v = Value.int q :=
                                      Option.some.inj (hv.symm.trans hy)
                                    subst hvq
                                    rw [hmj, getSlot_threeNarrow_j
                                      (lt_length_of_mem_getSlot doms j _ hyj)
                                      (fun hjk => hmk (hmj.trans hjk))]
                                    exact List.mem_filter.mpr ⟨hyj,
                                      minKeepB_of_satisfying (p := q) (q := p)
                                        (jlo := ilo) (jhi := ihi)
                                        (klo := klo) (khi := khi)
                                        hplo hphi hrlo hrhi
                                        (by simpa [min_comm] using hmin)⟩
                                  · by_cases hmi : m = i
                                    · rw [hmi] at hv
                                      have hvp : v = Value.int p :=
                                        Option.some.inj (hv.symm.trans hx)
                                      subst hvp
                                      rw [hmi, getSlot_threeNarrow_i
                                        (lt_length_of_mem_getSlot doms i _ hxi)
                                        (fun hij => hmj (hmi.trans hij))
                                        (fun hik => hmk (hmi.trans hik))]
                                      exact List.mem_filter.mpr ⟨hxi,
                                        minKeepB_of_satisfying
                                          (jlo := jlo) (jhi := jhi)
                                          (klo := klo) (khi := khi)
                                          hqlo hqhi hrlo hrhi hmin⟩
                                    · rw [getSlot_threeNarrow_other
                                        (fun h => hmi h) (fun h => hmj h)
                                        (fun h => hmk h)]
                                      exact hget m v hv
  · intro doms doms' h
    simp only [propMinSlot] at h
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
                            simp only [h6, propMinBounded] at h
                            by_cases hc : ((getSlot doms i).filter
                                (fun p => minKeepB p jlo jhi klo khi)).isEmpty = true ∨
                              ((getSlot doms j).filter
                                (fun q => minKeepB q ilo ihi klo khi)).isEmpty = true ∨
                              (atLeastVals (min ilo jlo)
                                (atMostVals (min ihi jhi) (getSlot doms k))).isEmpty = true
                            · rw [if_pos hc] at h
                              exact absurd h (by simp)
                            · rw [if_neg hc] at h
                              have hd : threeNarrow
                                  ((getSlot doms i).filter
                                    (fun p => minKeepB p jlo jhi klo khi))
                                  ((getSlot doms j).filter
                                    (fun q => minKeepB q ilo ihi klo khi))
                                  (atLeastVals (min ilo jlo)
                                    (atMostVals (min ihi jhi) (getSlot doms k)))
                                  i j k doms = doms' := PropResult.narrowed.inj h
                              subst hd
                              simp only [threeNarrow]
                              exact DomPointwiseSub.setSlot
                                (DomPointwiseSub.setSlot
                                  (DomPointwiseSub.setSlot (DomPointwiseSub.refl doms)
                                    (fun _ hv => (List.mem_filter.mp hv).1))
                                  (fun _ hv => (List.mem_filter.mp hv).1))
                                (fun _ hv => (mem_atLeastVals_atMostVals.mp hv).1)
  · intro doms h a ha hsat
    simp only [propMinSlot] at h
    obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, q, r, hx, hy, hz, hmin⟩ := hsat
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
                            simp only [h6, propMinBounded] at h
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
                            have hlo_bounds : min ilo jlo ≤ r := by
                              have h1 : min ilo jlo ≤ p := le_trans (min_le_left ilo jlo) hplo
                              have h2 : min ilo jlo ≤ q := le_trans (min_le_right ilo jlo) hqlo
                              have h3 : min ilo jlo ≤ min p q := le_min_iff.mpr ⟨h1, h2⟩
                              rw [hmin] at h3
                              exact h3
                            have hhi_bounds : r ≤ min ihi jhi := by
                              have h3 : min p q ≤ min ihi jhi := min_le_min hphi hqhi
                              rw [hmin] at h3
                              exact h3
                            by_cases hc : ((getSlot doms i).filter
                                (fun p => minKeepB p jlo jhi klo khi)).isEmpty = true ∨
                              ((getSlot doms j).filter
                                (fun q => minKeepB q ilo ihi klo khi)).isEmpty = true ∨
                              (atLeastVals (min ilo jlo)
                                (atMostVals (min ihi jhi) (getSlot doms k))).isEmpty = true
                            · rw [if_pos hc] at h
                              rcases hc with hci | hcj | hck
                              · have hmem : Value.int p ∈ (getSlot doms i).filter
                                    (fun p => minKeepB p jlo jhi klo khi) :=
                                  List.mem_filter.mpr ⟨hxi,
                                    minKeepB_of_satisfying
                                      (jlo := jlo) (jhi := jhi)
                                      (klo := klo) (khi := khi)
                                      hqlo hqhi hrlo hrhi hmin⟩
                                rw [List.isEmpty_iff.mp hci] at hmem
                                exact absurd hmem (by simp)
                              · have hmem : Value.int q ∈ (getSlot doms j).filter
                                    (fun q => minKeepB q ilo ihi klo khi) :=
                                  List.mem_filter.mpr ⟨hyj,
                                    minKeepB_of_satisfying (p := q) (q := p)
                                      (jlo := ilo) (jhi := ihi)
                                      (klo := klo) (khi := khi)
                                      hplo hphi hrlo hrhi
                                      (by simpa [min_comm] using hmin)⟩
                                rw [List.isEmpty_iff.mp hcj] at hmem
                                exact absurd hmem (by simp)
                              · have hmem : Value.int r ∈ atLeastVals (min ilo jlo)
                                    (atMostVals (min ihi jhi) (getSlot doms k)) :=
                                  mem_atLeastVals_atMostVals.mpr
                                    ⟨hzk, r, rfl, hlo_bounds, hhi_bounds⟩
                                rw [List.isEmpty_iff.mp hck] at hmem
                                exact absurd hmem (by simp)
                            · rw [if_neg hc] at h
                              exact absurd h (by simp)

/-! ### The max propagator -/

/-- The keep test for a `max` operand: an integer value `v = .int p`
    can participate in a satisfying `max p q = r` with `q ∈ [jlo, jhi]`
    and `r ∈ [klo, khi]` only when both necessary interval conditions
    hold (monotonicity of `max` in each argument). Non-integer values
    are rejected. -/
private def maxKeepB (v : Value) (jlo jhi klo khi : Int) : Bool :=
  match v with
  | .int p => decide (max p jlo ≤ khi) && decide (klo ≤ max p jhi)
  | _ => false

private theorem mem_maxKeepB_iff {v : Value} {jlo jhi klo khi : Int} :
    maxKeepB v jlo jhi klo khi = true ↔
      ∃ p, v = .int p ∧ max p jlo ≤ khi ∧ klo ≤ max p jhi := by
  constructor
  · intro h
    cases v with
    | int p =>
      simp only [maxKeepB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨p, rfl, h.1, h.2⟩
    | _ => contradiction
  · rintro ⟨p, rfl, h1, h2⟩
    simp only [maxKeepB, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h1, h2⟩

/-- A satisfying triple keeps both `max` operands. -/
private theorem maxKeepB_of_satisfying {p q r jlo jhi klo khi : Int}
    (hq1 : jlo ≤ q) (hq2 : q ≤ jhi) (hr1 : klo ≤ r) (hr2 : r ≤ khi)
    (hmax : max p q = r) :
    maxKeepB (.int p) jlo jhi klo khi = true := by
  simp only [maxKeepB, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨le_trans (max_le_max (le_refl p) hq1) (hmax ▸ hr2),
    le_trans (hmax ▸ hr1) (max_le_max (le_refl p) hq2)⟩

/-- The bounded max propagation: given all three domains' integer
    extrema, narrow each slot; `contradiction` when any side empties. -/
private def propMaxBounded (ilo ihi jlo jhi klo khi : Int) (i j k : Nat)
    (doms : List (List Value)) : PropResult :=
  let di' := (getSlot doms i).filter (fun p => maxKeepB p jlo jhi klo khi)
  let dj' := (getSlot doms j).filter (fun q => maxKeepB q ilo ihi klo khi)
  let dk' := atLeastVals (max ilo jlo) (atMostVals (max ihi jhi) (getSlot doms k))
  if di'.isEmpty = true ∨ dj'.isEmpty = true ∨ dk'.isEmpty = true then
    .contradiction
  else
    .narrowed (threeNarrow di' dj' dk' i j k doms)

/-- **The max propagator** (`int_max` style on three slots): bounds
    propagation for `max p q = r` — slot `i` keeps exactly the values
    passing the necessary `max` interval conditions, slot `j`
    symmetrically, slot `k` keeps `[max ilo jlo, max ihi jhi]`.
    `contradiction` when any side empties or any domain has no
    integers. -/
def propMaxSlot (i j k : Nat) (doms : List (List Value)) : PropResult :=
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
                      | some khi => propMaxBounded ilo ihi jlo jhi klo khi i j k doms

/-- **Preservation for `propMaxSlot`** (PLAN 6.3's local preservation
    theorem, max case): on `narrowed doms'`, every assignment of the
    input domains whose slot values are integers `max p q = r` is still
    an assignment of `doms'`, and `doms'` is pointwise-subset the input
    domains; on `contradiction`, no assignment of the input domains
    solves the equation. -/
theorem propMaxSlot_preserves (i j k : Nat) :
    Preserves (DomConstraint.maxSlot i j k) (propMaxSlot i j k) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propMaxSlot] at h
    obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, q, r, hx, hy, hz, hmax⟩ := hsat
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
                            simp only [h6, propMaxBounded] at h
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
                            have hlo_bounds : max ilo jlo ≤ r := by
                              have h1 : ilo ≤ max p q := le_trans hplo (le_max_left p q)
                              have h2 : jlo ≤ max p q := le_trans hqlo (le_max_right p q)
                              have h3 : max ilo jlo ≤ max p q := max_le h1 h2
                              rw [hmax] at h3
                              exact h3
                            have hhi_bounds : r ≤ max ihi jhi := by
                              have h3 : max p q ≤ max ihi jhi := max_le_max hphi hqhi
                              rw [hmax] at h3
                              exact h3
                            by_cases hc : ((getSlot doms i).filter
                                (fun p => maxKeepB p jlo jhi klo khi)).isEmpty = true ∨
                              ((getSlot doms j).filter
                                (fun q => maxKeepB q ilo ihi klo khi)).isEmpty = true ∨
                              (atLeastVals (max ilo jlo)
                                (atMostVals (max ihi jhi) (getSlot doms k))).isEmpty = true
                            · rw [if_pos hc] at h
                              exact absurd h (by simp)
                            · rw [if_neg hc] at h
                              have hd : threeNarrow
                                  ((getSlot doms i).filter
                                    (fun p => maxKeepB p jlo jhi klo khi))
                                  ((getSlot doms j).filter
                                    (fun q => maxKeepB q ilo ihi klo khi))
                                  (atLeastVals (max ilo jlo)
                                    (atMostVals (max ihi jhi) (getSlot doms k)))
                                  i j k doms = doms' := PropResult.narrowed.inj h
                              subst hd
                              apply allAssigns_intro
                              · have hlen2 : (threeNarrow
                                  ((getSlot doms i).filter
                                    (fun p => maxKeepB p jlo jhi klo khi))
                                  ((getSlot doms j).filter
                                    (fun q => maxKeepB q ilo ihi klo khi))
                                  (atLeastVals (max ilo jlo)
                                    (atMostVals (max ihi jhi) (getSlot doms k)))
                                  i j k doms).length = doms.length := by
                                  simp only [threeNarrow, setSlot_length]
                                rw [hlen2]
                                exact hlen
                              · intro m v hv
                                by_cases hmk : m = k
                                · rw [hmk] at hv
                                  have hvr : v = Value.int r :=
                                    Option.some.inj (hv.symm.trans hz)
                                  subst hvr
                                  rw [hmk, getSlot_threeNarrow_k
                                    (lt_length_of_mem_getSlot doms k _ hzk)]
                                  exact mem_atLeastVals_atMostVals.mpr
                                    ⟨hzk, r, rfl, hlo_bounds, hhi_bounds⟩
                                · by_cases hmj : m = j
                                  · rw [hmj] at hv
                                    have hvq : v = Value.int q :=
                                      Option.some.inj (hv.symm.trans hy)
                                    subst hvq
                                    rw [hmj, getSlot_threeNarrow_j
                                      (lt_length_of_mem_getSlot doms j _ hyj)
                                      (fun hjk => hmk (hmj.trans hjk))]
                                    exact List.mem_filter.mpr ⟨hyj,
                                      maxKeepB_of_satisfying (p := q) (q := p)
                                        (jlo := ilo) (jhi := ihi)
                                        (klo := klo) (khi := khi)
                                        hplo hphi hrlo hrhi
                                        (by simpa [max_comm] using hmax)⟩
                                  · by_cases hmi : m = i
                                    · rw [hmi] at hv
                                      have hvp : v = Value.int p :=
                                        Option.some.inj (hv.symm.trans hx)
                                      subst hvp
                                      rw [hmi, getSlot_threeNarrow_i
                                        (lt_length_of_mem_getSlot doms i _ hxi)
                                        (fun hij => hmj (hmi.trans hij))
                                        (fun hik => hmk (hmi.trans hik))]
                                      exact List.mem_filter.mpr ⟨hxi,
                                        maxKeepB_of_satisfying
                                          (jlo := jlo) (jhi := jhi)
                                          (klo := klo) (khi := khi)
                                          hqlo hqhi hrlo hrhi hmax⟩
                                    · rw [getSlot_threeNarrow_other
                                        (fun h => hmi h) (fun h => hmj h)
                                        (fun h => hmk h)]
                                      exact hget m v hv
  · intro doms doms' h
    simp only [propMaxSlot] at h
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
                            simp only [h6, propMaxBounded] at h
                            by_cases hc : ((getSlot doms i).filter
                                (fun p => maxKeepB p jlo jhi klo khi)).isEmpty = true ∨
                              ((getSlot doms j).filter
                                (fun q => maxKeepB q ilo ihi klo khi)).isEmpty = true ∨
                              (atLeastVals (max ilo jlo)
                                (atMostVals (max ihi jhi) (getSlot doms k))).isEmpty = true
                            · rw [if_pos hc] at h
                              exact absurd h (by simp)
                            · rw [if_neg hc] at h
                              have hd : threeNarrow
                                  ((getSlot doms i).filter
                                    (fun p => maxKeepB p jlo jhi klo khi))
                                  ((getSlot doms j).filter
                                    (fun q => maxKeepB q ilo ihi klo khi))
                                  (atLeastVals (max ilo jlo)
                                    (atMostVals (max ihi jhi) (getSlot doms k)))
                                  i j k doms = doms' := PropResult.narrowed.inj h
                              subst hd
                              simp only [threeNarrow]
                              exact DomPointwiseSub.setSlot
                                (DomPointwiseSub.setSlot
                                  (DomPointwiseSub.setSlot (DomPointwiseSub.refl doms)
                                    (fun _ hv => (List.mem_filter.mp hv).1))
                                  (fun _ hv => (List.mem_filter.mp hv).1))
                                (fun _ hv => (mem_atLeastVals_atMostVals.mp hv).1)
  · intro doms h a ha hsat
    simp only [propMaxSlot] at h
    obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, q, r, hx, hy, hz, hmax⟩ := hsat
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
                            simp only [h6, propMaxBounded] at h
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
                            have hlo_bounds : max ilo jlo ≤ r := by
                              have h1 : ilo ≤ max p q := le_trans hplo (le_max_left p q)
                              have h2 : jlo ≤ max p q := le_trans hqlo (le_max_right p q)
                              have h3 : max ilo jlo ≤ max p q := max_le h1 h2
                              rw [hmax] at h3
                              exact h3
                            have hhi_bounds : r ≤ max ihi jhi := by
                              have h3 : max p q ≤ max ihi jhi := max_le_max hphi hqhi
                              rw [hmax] at h3
                              exact h3
                            by_cases hc : ((getSlot doms i).filter
                                (fun p => maxKeepB p jlo jhi klo khi)).isEmpty = true ∨
                              ((getSlot doms j).filter
                                (fun q => maxKeepB q ilo ihi klo khi)).isEmpty = true ∨
                              (atLeastVals (max ilo jlo)
                                (atMostVals (max ihi jhi) (getSlot doms k))).isEmpty = true
                            · rw [if_pos hc] at h
                              rcases hc with hci | hcj | hck
                              · have hmem : Value.int p ∈ (getSlot doms i).filter
                                    (fun p => maxKeepB p jlo jhi klo khi) :=
                                  List.mem_filter.mpr ⟨hxi,
                                    maxKeepB_of_satisfying
                                      (jlo := jlo) (jhi := jhi)
                                      (klo := klo) (khi := khi)
                                      hqlo hqhi hrlo hrhi hmax⟩
                                rw [List.isEmpty_iff.mp hci] at hmem
                                exact absurd hmem (by simp)
                              · have hmem : Value.int q ∈ (getSlot doms j).filter
                                    (fun q => maxKeepB q ilo ihi klo khi) :=
                                  List.mem_filter.mpr ⟨hyj,
                                    maxKeepB_of_satisfying (p := q) (q := p)
                                      (jlo := ilo) (jhi := ihi)
                                      (klo := klo) (khi := khi)
                                      hplo hphi hrlo hrhi
                                      (by simpa [max_comm] using hmax)⟩
                                rw [List.isEmpty_iff.mp hcj] at hmem
                                exact absurd hmem (by simp)
                              · have hmem : Value.int r ∈ atLeastVals (max ilo jlo)
                                    (atMostVals (max ihi jhi) (getSlot doms k)) :=
                                  mem_atLeastVals_atMostVals.mpr
                                    ⟨hzk, r, rfl, hlo_bounds, hhi_bounds⟩
                                rw [List.isEmpty_iff.mp hck] at hmem
                                exact absurd hmem (by simp)
                            · rw [if_neg hc] at h
                              exact absurd h (by simp)

/-! ### The times propagator -/

/-- The keep test for a `times` operand: an integer value `v = .int p`
    can participate in a satisfying `p * q = r` with `q ∈ [jlo, jhi]`
    and `r ∈ [klo, khi]` only when the necessary interval condition
    (the product `p * q` stays within the two corner products) holds.
    Non-integer values are rejected. -/
private def timesKeepB (v : Value) (jlo jhi klo khi : Int) : Bool :=
  match v with
  | .int p =>
    decide (min (p * jlo) (p * jhi) ≤ khi) &&
      decide (klo ≤ max (p * jlo) (p * jhi))
  | _ => false

private theorem mem_timesKeepB_iff {v : Value} {jlo jhi klo khi : Int} :
    timesKeepB v jlo jhi klo khi = true ↔
      ∃ p, v = .int p ∧ min (p * jlo) (p * jhi) ≤ khi ∧
        klo ≤ max (p * jlo) (p * jhi) := by
  constructor
  · intro h
    cases v with
    | int p =>
      simp only [timesKeepB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨p, rfl, h.1, h.2⟩
    | _ => contradiction
  · rintro ⟨p, rfl, h1, h2⟩
    simp only [timesKeepB, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h1, h2⟩

/-- A satisfying triple keeps both `times` operands. -/
private theorem timesKeepB_of_satisfying {p q r jlo jhi klo khi : Int}
    (hq1 : jlo ≤ q) (hq2 : q ≤ jhi) (hr1 : klo ≤ r) (hr2 : r ≤ khi)
    (hprod : p * q = r) :
    timesKeepB (.int p) jlo jhi klo khi = true := by
  simp only [timesKeepB, Bool.and_eq_true, decide_eq_true_eq]
  obtain ⟨hlo_pq, hhi_pq⟩ := mul_one_interval hq1 hq2
  exact ⟨le_trans hlo_pq (hprod ▸ hr2),
    le_trans hr1 (hprod ▸ hhi_pq)⟩

/-- The bounded times propagation: given all three domains' integer
    extrema, narrow each slot; `contradiction` when any side empties. -/
private def propTimesBounded (ilo ihi jlo jhi klo khi : Int) (i j k : Nat)
    (doms : List (List Value)) : PropResult :=
  let di' := (getSlot doms i).filter (fun p => timesKeepB p jlo jhi klo khi)
  let dj' := (getSlot doms j).filter (fun q => timesKeepB q ilo ihi klo khi)
  let dk' := atLeastVals (cornerMin ilo ihi jlo jhi)
    (atMostVals (cornerMax ilo ihi jlo jhi) (getSlot doms k))
  if di'.isEmpty = true ∨ dj'.isEmpty = true ∨ dk'.isEmpty = true then
    .contradiction
  else
    .narrowed (threeNarrow di' dj' dk' i j k doms)

/-- **The times propagator** (`int_times` style on three slots): bounds
    propagation for `p * q = r` — slot `i` keeps exactly the values
    passing the necessary product interval condition, slot `j`
    symmetrically, slot `k` keeps the four-corner product interval
    `[cornerMin ilo ihi jlo jhi, cornerMax ilo ihi jlo jhi]`.
    `contradiction` when any side empties or any domain has no
    integers. -/
def propTimesSlot (i j k : Nat) (doms : List (List Value)) : PropResult :=
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
                      | some khi => propTimesBounded ilo ihi jlo jhi klo khi i j k doms

/-- **Preservation for `propTimesSlot`** (PLAN 6.3's local preservation
    theorem, times case): on `narrowed doms'`, every assignment of the
    input domains whose slot values are integers `p * q = r` is still
    an assignment of `doms'`, and `doms'` is pointwise-subset the input
    domains; on `contradiction`, no assignment of the input domains
    solves the equation. -/
theorem propTimesSlot_preserves (i j k : Nat) :
    Preserves (DomConstraint.timesSlot i j k) (propTimesSlot i j k) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propTimesSlot] at h
    obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, q, r, hx, hy, hz, hprod⟩ := hsat
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
                            simp only [h6, propTimesBounded] at h
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
                            by_cases hc : ((getSlot doms i).filter
                                (fun p => timesKeepB p jlo jhi klo khi)).isEmpty = true ∨
                              ((getSlot doms j).filter
                                (fun q => timesKeepB q ilo ihi klo khi)).isEmpty = true ∨
                              (atLeastVals (cornerMin ilo ihi jlo jhi)
                                (atMostVals (cornerMax ilo ihi jlo jhi)
                                  (getSlot doms k))).isEmpty = true
                            · rw [if_pos hc] at h
                              exact absurd h (by simp)
                            · rw [if_neg hc] at h
                              have hd : threeNarrow
                                  ((getSlot doms i).filter
                                    (fun p => timesKeepB p jlo jhi klo khi))
                                  ((getSlot doms j).filter
                                    (fun q => timesKeepB q ilo ihi klo khi))
                                  (atLeastVals (cornerMin ilo ihi jlo jhi)
                                    (atMostVals (cornerMax ilo ihi jlo jhi)
                                      (getSlot doms k)))
                                  i j k doms = doms' := PropResult.narrowed.inj h
                              subst hd
                              apply allAssigns_intro
                              · have hlen2 : (threeNarrow
                                  ((getSlot doms i).filter
                                    (fun p => timesKeepB p jlo jhi klo khi))
                                  ((getSlot doms j).filter
                                    (fun q => timesKeepB q ilo ihi klo khi))
                                  (atLeastVals (cornerMin ilo ihi jlo jhi)
                                    (atMostVals (cornerMax ilo ihi jlo jhi)
                                      (getSlot doms k)))
                                  i j k doms).length = doms.length := by
                                  simp only [threeNarrow, setSlot_length]
                                rw [hlen2]
                                exact hlen
                              · intro m v hv
                                by_cases hmk : m = k
                                · rw [hmk] at hv
                                  have hvr : v = Value.int r :=
                                    Option.some.inj (hv.symm.trans hz)
                                  subst hvr
                                  rw [hmk, getSlot_threeNarrow_k
                                    (lt_length_of_mem_getSlot doms k _ hzk)]
                                  exact mem_atLeastVals_atMostVals.mpr
                                    ⟨hzk, r, rfl,
                                      (by simpa [← hprod] using
                                        cornerMin_le_mul hplo hphi hqlo hqhi),
                                      (by simpa [← hprod] using
                                        mul_le_cornerMax hplo hphi hqlo hqhi)⟩
                                · by_cases hmj : m = j
                                  · rw [hmj] at hv
                                    have hvq : v = Value.int q :=
                                      Option.some.inj (hv.symm.trans hy)
                                    subst hvq
                                    rw [hmj, getSlot_threeNarrow_j
                                      (lt_length_of_mem_getSlot doms j _ hyj)
                                      (fun hjk => hmk (hmj.trans hjk))]
                                    exact List.mem_filter.mpr ⟨hyj,
                                      timesKeepB_of_satisfying (p := q) (q := p)
                                        (jlo := ilo) (jhi := ihi)
                                        (klo := klo) (khi := khi)
                                        hplo hphi hrlo hrhi
                                        (by simpa [mul_comm] using hprod)⟩
                                  · by_cases hmi : m = i
                                    · rw [hmi] at hv
                                      have hvp : v = Value.int p :=
                                        Option.some.inj (hv.symm.trans hx)
                                      subst hvp
                                      rw [hmi, getSlot_threeNarrow_i
                                        (lt_length_of_mem_getSlot doms i _ hxi)
                                        (fun hij => hmj (hmi.trans hij))
                                        (fun hik => hmk (hmi.trans hik))]
                                      exact List.mem_filter.mpr ⟨hxi,
                                        timesKeepB_of_satisfying
                                          (jlo := jlo) (jhi := jhi)
                                          (klo := klo) (khi := khi)
                                          hqlo hqhi hrlo hrhi hprod⟩
                                    · rw [getSlot_threeNarrow_other
                                        (fun h => hmi h) (fun h => hmj h)
                                        (fun h => hmk h)]
                                      exact hget m v hv
  · intro doms doms' h
    simp only [propTimesSlot] at h
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
                            simp only [h6, propTimesBounded] at h
                            by_cases hc : ((getSlot doms i).filter
                                (fun p => timesKeepB p jlo jhi klo khi)).isEmpty = true ∨
                              ((getSlot doms j).filter
                                (fun q => timesKeepB q ilo ihi klo khi)).isEmpty = true ∨
                              (atLeastVals (cornerMin ilo ihi jlo jhi)
                                (atMostVals (cornerMax ilo ihi jlo jhi)
                                  (getSlot doms k))).isEmpty = true
                            · rw [if_pos hc] at h
                              exact absurd h (by simp)
                            · rw [if_neg hc] at h
                              have hd : threeNarrow
                                  ((getSlot doms i).filter
                                    (fun p => timesKeepB p jlo jhi klo khi))
                                  ((getSlot doms j).filter
                                    (fun q => timesKeepB q ilo ihi klo khi))
                                  (atLeastVals (cornerMin ilo ihi jlo jhi)
                                    (atMostVals (cornerMax ilo ihi jlo jhi)
                                      (getSlot doms k)))
                                  i j k doms = doms' := PropResult.narrowed.inj h
                              subst hd
                              simp only [threeNarrow]
                              exact DomPointwiseSub.setSlot
                                (DomPointwiseSub.setSlot
                                  (DomPointwiseSub.setSlot (DomPointwiseSub.refl doms)
                                    (fun _ hv => (List.mem_filter.mp hv).1))
                                  (fun _ hv => (List.mem_filter.mp hv).1))
                                (fun _ hv => (mem_atLeastVals_atMostVals.mp hv).1)
  · intro doms h a ha hsat
    simp only [propTimesSlot] at h
    obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, q, r, hx, hy, hz, hprod⟩ := hsat
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
                            simp only [h6, propTimesBounded] at h
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
                            by_cases hc : ((getSlot doms i).filter
                                (fun p => timesKeepB p jlo jhi klo khi)).isEmpty = true ∨
                              ((getSlot doms j).filter
                                (fun q => timesKeepB q ilo ihi klo khi)).isEmpty = true ∨
                              (atLeastVals (cornerMin ilo ihi jlo jhi)
                                (atMostVals (cornerMax ilo ihi jlo jhi)
                                  (getSlot doms k))).isEmpty = true
                            · rw [if_pos hc] at h
                              rcases hc with hci | hcj | hck
                              · have hmem : Value.int p ∈ (getSlot doms i).filter
                                    (fun p => timesKeepB p jlo jhi klo khi) :=
                                  List.mem_filter.mpr ⟨hxi,
                                    timesKeepB_of_satisfying
                                      (jlo := jlo) (jhi := jhi)
                                      (klo := klo) (khi := khi)
                                      hqlo hqhi hrlo hrhi hprod⟩
                                rw [List.isEmpty_iff.mp hci] at hmem
                                exact absurd hmem (by simp)
                              · have hmem : Value.int q ∈ (getSlot doms j).filter
                                    (fun q => timesKeepB q ilo ihi klo khi) :=
                                  List.mem_filter.mpr ⟨hyj,
                                    timesKeepB_of_satisfying (p := q) (q := p)
                                      (jlo := ilo) (jhi := ihi)
                                      (klo := klo) (khi := khi)
                                      hplo hphi hrlo hrhi
                                      (by simpa [mul_comm] using hprod)⟩
                                rw [List.isEmpty_iff.mp hcj] at hmem
                                exact absurd hmem (by simp)
                              · have hmem : Value.int r ∈
                                    atLeastVals (cornerMin ilo ihi jlo jhi)
                                      (atMostVals (cornerMax ilo ihi jlo jhi)
                                        (getSlot doms k)) :=
                                  mem_atLeastVals_atMostVals.mpr
                                    ⟨hzk, r, rfl,
                                      (by simpa [← hprod] using
                                        cornerMin_le_mul hplo hphi hqlo hqhi),
                                      (by simpa [← hprod] using
                                        mul_le_cornerMax hplo hphi hqlo hqhi)⟩
                                rw [List.isEmpty_iff.mp hck] at hmem
                                exact absurd hmem (by simp)
                            · rw [if_neg hc] at h
                              exact absurd h (by simp)

/-! ### The abs propagator -/

/-- The two-slot narrowing: each slot takes its narrowed list, each
    filter computed once (on the *input* domains — every bound argument
    holds for any satisfying assignment independently, so coinciding
    slot positions are harmless). -/
private def twoNarrow (di' dk' : List Value) (i k : Nat)
    (doms : List (List Value)) : List (List Value) :=
  setSlot (setSlot doms i di') k dk'

/-- Reading back the two written slots of a `twoNarrow` (the `k`-write
    is outermost, then `i`). -/
private theorem getSlot_twoNarrow_k {di' dk' : List Value} {i k : Nat}
    {doms : List (List Value)} (hk : k < doms.length) :
    getSlot (twoNarrow di' dk' i k doms) k = dk' := by
  simp only [twoNarrow]
  rw [getSlot_setSlot_eq (setSlot doms i di') dk' k
    (by rw [setSlot_length]; exact hk)]

private theorem getSlot_twoNarrow_i {di' dk' : List Value} {i k : Nat}
    {doms : List (List Value)} (hi : i < doms.length) (hik : i ≠ k) :
    getSlot (twoNarrow di' dk' i k doms) i = di' := by
  simp only [twoNarrow]
  rw [getSlot_setSlot_of_ne (setSlot doms i di') dk' k i hik,
    getSlot_setSlot_eq doms di' i hi]

private theorem getSlot_twoNarrow_other {di' dk' : List Value} {i k m : Nat}
    {doms : List (List Value)} (hmi : m ≠ i) (hmk : m ≠ k) :
    getSlot (twoNarrow di' dk' i k doms) m = getSlot doms m := by
  simp only [twoNarrow]
  rw [getSlot_setSlot_of_ne (setSlot doms i di') dk' k m hmk,
    getSlot_setSlot_of_ne doms di' i m hmi]

/-- The keep test for the `abs` operand: an integer value `v = .int p`
    participates in a satisfying `absValue p = r` with `r ∈ [klo, khi]`
    exactly when `klo ≤ absValue p ≤ khi`. Non-integer values are
    rejected. -/
private def absKeepB (v : Value) (klo khi : Int) : Bool :=
  match v with
  | .int p => decide (klo ≤ absValue p) && decide (absValue p ≤ khi)
  | _ => false

private theorem mem_absKeepB_iff {v : Value} {klo khi : Int} :
    absKeepB v klo khi = true ↔
      ∃ p, v = .int p ∧ klo ≤ absValue p ∧ absValue p ≤ khi := by
  constructor
  · intro h
    cases v with
    | int p =>
      simp only [absKeepB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨p, rfl, h.1, h.2⟩
    | _ => contradiction
  · rintro ⟨p, rfl, h1, h2⟩
    simp only [absKeepB, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h1, h2⟩

/-- A satisfying pair keeps the `abs` operand. -/
private theorem absKeepB_of_satisfying {p r klo khi : Int}
    (hr1 : klo ≤ r) (hr2 : r ≤ khi) (habs : absValue p = r) :
    absKeepB (.int p) klo khi = true := by
  simp only [absKeepB, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨habs ▸ hr1, habs ▸ hr2⟩

/-- The bounded abs propagation: given both domains' integer extrema,
    narrow each slot; `contradiction` when any side empties. -/
private def propAbsBounded (ilo ihi klo khi : Int) (i k : Nat)
    (doms : List (List Value)) : PropResult :=
  let M := max (absValue ilo) (absValue ihi)
  let di' := (getSlot doms i).filter (fun p => absKeepB p klo khi)
  let dk' := atLeastVals 0 (atMostVals M (getSlot doms k))
  if di'.isEmpty = true ∨ dk'.isEmpty = true then
    .contradiction
  else
    .narrowed (twoNarrow di' dk' i k doms)

/-- **The abs propagator** (`int_abs` style on two slots): bounds
    propagation for `absValue p = r` — slot `i` keeps exactly the
    values with `klo ≤ absValue p ≤ khi`, slot `k` keeps the nonneg
    interval `[0, max (absValue ilo) (absValue ihi)]`.
    `contradiction` when any side empties or any domain has no
    integers. -/
def propAbsSlot (i k : Nat) (doms : List (List Value)) : PropResult :=
  match domMin (getSlot doms i) with
  | none => .contradiction
  | some ilo =>
      match domMax (getSlot doms i) with
      | none => .contradiction
      | some ihi =>
          match domMin (getSlot doms k) with
          | none => .contradiction
          | some klo =>
              match domMax (getSlot doms k) with
              | none => .contradiction
              | some khi => propAbsBounded ilo ihi klo khi i k doms

/-- **Preservation for `propAbsSlot`** (PLAN 6.3's local preservation
    theorem, abs case): on `narrowed doms'`, every assignment of the
    input domains whose slot values are integers `absValue p = r` is
    still an assignment of `doms'`, and `doms'` is pointwise-subset the
    input domains; on `contradiction`, no assignment of the input
    domains solves the equation. -/
theorem propAbsSlot_preserves (i k : Nat) :
    Preserves (DomConstraint.absSlot i k) (propAbsSlot i k) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propAbsSlot] at h
    obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, r, hx, hz, habs⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    have hzk : Value.int r ∈ getSlot doms k := hget k _ hz
    cases h1 : domMin (getSlot doms i) with
    | none => rw [h1] at h; exact absurd h (by simp)
    | some ilo =>
        simp only [h1] at h
        cases h2 : domMax (getSlot doms i) with
        | none => rw [h2] at h; exact absurd h (by simp)
        | some ihi =>
            simp only [h2] at h
            cases h3 : domMin (getSlot doms k) with
            | none => rw [h3] at h; exact absurd h (by simp)
            | some klo =>
                simp only [h3] at h
                cases h4 : domMax (getSlot doms k) with
                | none => rw [h4] at h; exact absurd h (by simp)
                | some khi =>
                    simp only [h4, propAbsBounded] at h
                    -- pin the extrema to the satisfying values' bounds
                    obtain ⟨m1, hm1, hplo⟩ := domMin_of_mem hxi
                    rw [h1] at hm1
                    have hilo : m1 = ilo := (Option.some.inj hm1).symm
                    rw [hilo] at hplo
                    obtain ⟨m2, hm2, hphi⟩ := domMax_of_mem hxi
                    rw [h2] at hm2
                    have hihi : m2 = ihi := (Option.some.inj hm2).symm
                    rw [hihi] at hphi
                    obtain ⟨m3, hm3, hrlo⟩ := domMin_of_mem hzk
                    rw [h3] at hm3
                    have hklo : m3 = klo := (Option.some.inj hm3).symm
                    rw [hklo] at hrlo
                    obtain ⟨m4, hm4, hrhi⟩ := domMax_of_mem hzk
                    rw [h4] at hm4
                    have hkhi : m4 = khi := (Option.some.inj hm4).symm
                    rw [hkhi] at hrhi
                    by_cases hc : ((getSlot doms i).filter
                        (fun p => absKeepB p klo khi)).isEmpty = true ∨
                      (atLeastVals 0 (atMostVals (max (absValue ilo) (absValue ihi))
                        (getSlot doms k))).isEmpty = true
                    · rw [if_pos hc] at h
                      exact absurd h (by simp)
                    · rw [if_neg hc] at h
                      have hd : twoNarrow
                          ((getSlot doms i).filter (fun p => absKeepB p klo khi))
                          (atLeastVals 0 (atMostVals (max (absValue ilo) (absValue ihi))
                            (getSlot doms k)))
                          i k doms = doms' := PropResult.narrowed.inj h
                      subst hd
                      apply allAssigns_intro
                      · have hlen2 : (twoNarrow
                          ((getSlot doms i).filter (fun p => absKeepB p klo khi))
                          (atLeastVals 0 (atMostVals (max (absValue ilo) (absValue ihi))
                            (getSlot doms k)))
                          i k doms).length = doms.length := by
                          simp only [twoNarrow, setSlot_length]
                        rw [hlen2]
                        exact hlen
                      · intro m v hv
                        by_cases hmk : m = k
                        · rw [hmk] at hv
                          have hvr : v = Value.int r :=
                            Option.some.inj (hv.symm.trans hz)
                          subst hvr
                          rw [hmk, getSlot_twoNarrow_k
                            (lt_length_of_mem_getSlot doms k _ hzk)]
                          exact mem_atLeastVals_atMostVals.mpr
                            ⟨hzk, r, rfl,
                              (by rw [← habs]; exact absValue_nonneg p),
                              (by rw [← habs]; exact absValue_le_range hplo hphi)⟩
                        · by_cases hmi : m = i
                          · rw [hmi] at hv
                            have hvp : v = Value.int p :=
                              Option.some.inj (hv.symm.trans hx)
                            subst hvp
                            rw [hmi, getSlot_twoNarrow_i
                              (lt_length_of_mem_getSlot doms i _ hxi)
                              (fun hik => hmk (hmi.trans hik))]
                            exact List.mem_filter.mpr ⟨hxi,
                              absKeepB_of_satisfying hrlo hrhi habs⟩
                          · rw [getSlot_twoNarrow_other
                              (fun h => hmi h) (fun h => hmk h)]
                            exact hget m v hv
  · intro doms doms' h
    simp only [propAbsSlot] at h
    cases h1 : domMin (getSlot doms i) with
    | none => rw [h1] at h; exact absurd h (by simp)
    | some ilo =>
        simp only [h1] at h
        cases h2 : domMax (getSlot doms i) with
        | none => rw [h2] at h; exact absurd h (by simp)
        | some ihi =>
            simp only [h2] at h
            cases h3 : domMin (getSlot doms k) with
            | none => rw [h3] at h; exact absurd h (by simp)
            | some klo =>
                simp only [h3] at h
                cases h4 : domMax (getSlot doms k) with
                | none => rw [h4] at h; exact absurd h (by simp)
                | some khi =>
                    simp only [h4, propAbsBounded] at h
                    by_cases hc : ((getSlot doms i).filter
                        (fun p => absKeepB p klo khi)).isEmpty = true ∨
                      (atLeastVals 0 (atMostVals (max (absValue ilo) (absValue ihi))
                        (getSlot doms k))).isEmpty = true
                    · rw [if_pos hc] at h
                      exact absurd h (by simp)
                    · rw [if_neg hc] at h
                      have hd : twoNarrow
                          ((getSlot doms i).filter (fun p => absKeepB p klo khi))
                          (atLeastVals 0 (atMostVals (max (absValue ilo) (absValue ihi))
                            (getSlot doms k)))
                          i k doms = doms' := PropResult.narrowed.inj h
                      subst hd
                      simp only [twoNarrow]
                      exact DomPointwiseSub.setSlot
                        (DomPointwiseSub.setSlot (DomPointwiseSub.refl doms)
                          (fun _ hv => (List.mem_filter.mp hv).1))
                        (fun _ hv => (mem_atLeastVals_atMostVals.mp hv).1)
  · intro doms h a ha hsat
    simp only [propAbsSlot] at h
    obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, r, hx, hz, habs⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
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
            cases h3 : domMin (getSlot doms k) with
            | none =>
                obtain ⟨m, hm, _⟩ := domMin_of_mem hzk
                rw [h3] at hm
                exact absurd hm (by simp)
            | some klo =>
                simp only [h3] at h
                cases h4 : domMax (getSlot doms k) with
                | none =>
                    obtain ⟨m, hm, _⟩ := domMax_of_mem hzk
                    rw [h4] at hm
                    exact absurd hm (by simp)
                | some khi =>
                    simp only [h4, propAbsBounded] at h
                    -- pin the extrema to the satisfying values' bounds
                    obtain ⟨m1, hm1, hplo⟩ := domMin_of_mem hxi
                    rw [h1] at hm1
                    have hilo : m1 = ilo := (Option.some.inj hm1).symm
                    rw [hilo] at hplo
                    obtain ⟨m2, hm2, hphi⟩ := domMax_of_mem hxi
                    rw [h2] at hm2
                    have hihi : m2 = ihi := (Option.some.inj hm2).symm
                    rw [hihi] at hphi
                    obtain ⟨m3, hm3, hrlo⟩ := domMin_of_mem hzk
                    rw [h3] at hm3
                    have hklo : m3 = klo := (Option.some.inj hm3).symm
                    rw [hklo] at hrlo
                    obtain ⟨m4, hm4, hrhi⟩ := domMax_of_mem hzk
                    rw [h4] at hm4
                    have hkhi : m4 = khi := (Option.some.inj hm4).symm
                    rw [hkhi] at hrhi
                    by_cases hc : ((getSlot doms i).filter
                        (fun p => absKeepB p klo khi)).isEmpty = true ∨
                      (atLeastVals 0 (atMostVals (max (absValue ilo) (absValue ihi))
                        (getSlot doms k))).isEmpty = true
                    · rw [if_pos hc] at h
                      rcases hc with hci | hck
                      · have hmem : Value.int p ∈ (getSlot doms i).filter
                            (fun p => absKeepB p klo khi) :=
                          List.mem_filter.mpr ⟨hxi, absKeepB_of_satisfying hrlo hrhi habs⟩
                        rw [List.isEmpty_iff.mp hci] at hmem
                        exact absurd hmem (by simp)
                      · have hmem : Value.int r ∈
                            atLeastVals 0 (atMostVals (max (absValue ilo) (absValue ihi))
                              (getSlot doms k)) :=
                          mem_atLeastVals_atMostVals.mpr
                            ⟨hzk, r, rfl,
                              (by rw [← habs]; exact absValue_nonneg p),
                              (by rw [← habs]; exact absValue_le_range hplo hphi)⟩
                        rw [List.isEmpty_iff.mp hck] at hmem
                        exact absurd hmem (by simp)
                    · rw [if_neg hc] at h
                      exact absurd h (by simp)


end LeanFzn.Solver.Propagation.DomainFiltering

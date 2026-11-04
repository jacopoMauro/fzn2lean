import LeanFzn.Solver.Propagation.DomainConstraints.Repr
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation
open LeanFzn.Solver.Core
open LeanFzn LeanFzn.Semantics.Evaluation LeanFzn.Solver.Core List
open LeanFzn.Solver.Propagation.DomainFiltering.Internal

namespace LeanFzn.Solver.Propagation.DomainFiltering

/-! ## The Boolean propagators (`bool_not` / `bool_and` / `bool_or`) -/

/-- Keep only the Boolean values of a domain. -/
def boolVals (d : List Value) : List Value :=
  d.filter (fun v => match v with | .bool _ => true | _ => false)

/-- Membership characterization of `boolVals`. -/
theorem mem_boolVals {v : Value} {d : List Value} :
    v ∈ boolVals d ↔ v ∈ d ∧ ∃ p, v = .bool p := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := List.mem_filter.mp h
    cases v with
    | bool p => exact ⟨h1, p, rfl⟩
    | int w => simp at h2
    | setOfInt w => simp at h2
    | array w => simp at h2
  · rintro ⟨h1, p, rfl⟩
    exact List.mem_filter.mpr ⟨h1, rfl⟩

/-- Keep only the `true` Booleans of a domain. -/
def trueVals (d : List Value) : List Value :=
  d.filter (fun v => match v with | .bool true => true | _ => false)

/-- Membership characterization of `trueVals`. -/
theorem mem_trueVals {v : Value} {d : List Value} :
    v ∈ trueVals d ↔ v ∈ d ∧ v = .bool true := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := List.mem_filter.mp h
    cases v with
    | bool p => cases p with
      | true => exact ⟨h1, rfl⟩
      | false => simp at h2
    | int w => simp at h2
    | setOfInt w => simp at h2
    | array w => simp at h2
  · rintro ⟨h1, rfl⟩
    exact List.mem_filter.mpr ⟨h1, rfl⟩

/-- Keep only the `false` Booleans of a domain. -/
def falseVals (d : List Value) : List Value :=
  d.filter (fun v => match v with | .bool false => true | _ => false)

/-- Membership characterization of `falseVals`. -/
theorem mem_falseVals {v : Value} {d : List Value} :
    v ∈ falseVals d ↔ v ∈ d ∧ v = .bool false := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := List.mem_filter.mp h
    cases v with
    | bool p => cases p with
      | false => exact ⟨h1, rfl⟩
      | true => simp at h2
    | int w => simp at h2
    | setOfInt w => simp at h2
    | array w => simp at h2
  · rintro ⟨h1, rfl⟩
    exact List.mem_filter.mpr ⟨h1, rfl⟩

/-- A Boolean value of a slot read by an assignment lies in that
    slot's Boolean projection. -/
private theorem mem_boolVals_of {p : Bool} {i : Nat} {doms : List (List Value)}
    {a : List Value} (ha : a ∈ allAssigns doms)
    (hx : a[i]? = some (.bool p)) : .bool p ∈ boolVals (getSlot doms i) := by
  obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
  exact mem_boolVals.mpr ⟨hget i _ hx, p, rfl⟩

/-- The singleton Boolean of a domain's Boolean projection, if the
    projection is exactly one Boolean. -/
private def singleBool? (d : List Value) : Option Bool :=
  match single? (boolVals d) with
  | some (.bool p) => some p
  | _ => none

/-- `singleBool?` extracts the pin when the Boolean projection is a
    singleton, and the assignment's read matches it. -/
private theorem eq_of_singleBool? {i : Nat} {p p' : Bool}
    {doms : List (List Value)} {a : List Value}
    (ha : a ∈ allAssigns doms) (hx : a[i]? = some (.bool p))
    (hs : singleBool? (getSlot doms i) = some p') : p = p' := by
  have hxmem : Value.bool p ∈ boolVals (getSlot doms i) := mem_boolVals_of ha hx
  simp only [singleBool?] at hs
  cases hs2 : single? (boolVals (getSlot doms i)) with
  | none =>
      rw [hs2] at hs
      exact absurd hs (by simp)
  | some val =>
      cases val with
      | bool p'' =>
          have hsingle : boolVals (getSlot doms i) = [.bool p''] :=
            single?_eq_some_iff.mp hs2
          rw [hsingle] at hxmem
          have hpp'' : Value.bool p = Value.bool p'' :=
            List.mem_singleton.mp hxmem
          injection hpp'' with hpp'''
          rw [hs2] at hs
          -- the match now reduces definitionally to `some p'' = some p'`
          have hp'p : p'' = p' := Option.some.inj hs
          exact hpp''' ▸ hp'p
      | int w =>
          rw [hs2] at hs
          exact absurd hs (by simp)
      | setOfInt w =>
          rw [hs2] at hs
          exact absurd hs (by simp)
      | array w =>
          rw [hs2] at hs
          exact absurd hs (by simp)

/-- The Boolean negation propagator (`bool_not` style on two slots):
    if slot `i`'s Boolean values form a singleton, slot `j` narrows to
    the opposite Booleans (and symmetrically); otherwise the domains
    are unchanged (a sound no-op); `contradiction` when the opposite
    side empties. -/
def propBoolNotSlot (i j : Nat) (doms : List (List Value)) : PropResult :=
  match singleBool? (getSlot doms i) with
  | some p =>
      let dj' := if p then falseVals (getSlot doms j) else trueVals (getSlot doms j)
      if dj'.isEmpty = true then .contradiction
      else .narrowed (setSlot doms j dj')
  | none =>
      match singleBool? (getSlot doms j) with
      | some q =>
          let di' := if q then falseVals (getSlot doms i) else trueVals (getSlot doms i)
          if di'.isEmpty = true then .contradiction
          else .narrowed (setSlot doms i di')
      | none => .narrowed doms

/-- From `bool_not` satisfaction, the two slot values are opposite
    Booleans. -/
private theorem boolNot_opposite {i j : Nat} {a : List Value}
    (hsat : DomConstraint.SatisfiedBy (DomConstraint.boolNotSlot i j) a) :
    ∃ p q, a[i]? = some (.bool p) ∧ a[j]? = some (.bool q) ∧ q = !p := by
  obtain ⟨x, y, hx, hy, hxy⟩ := hsat
  have hxbool : ∃ p, x = .bool p := by
    cases x with
    | bool p => exact ⟨p, rfl⟩
    | int w => cases hxy with
      | inl h =>
          have h1 : Value.int w = Value.bool true := h.1
          exact absurd h1 (by simp)
      | inr h =>
          have h1 : Value.int w = Value.bool false := h.1
          exact absurd h1 (by simp)
    | setOfInt w => cases hxy with
      | inl h =>
          have h1 : Value.setOfInt w = Value.bool true := h.1
          exact absurd h1 (by simp)
      | inr h =>
          have h1 : Value.setOfInt w = Value.bool false := h.1
          exact absurd h1 (by simp)
    | array w => cases hxy with
      | inl h =>
          have h1 : Value.array w = Value.bool true := h.1
          exact absurd h1 (by simp)
      | inr h =>
          have h1 : Value.array w = Value.bool false := h.1
          exact absurd h1 (by simp)
  have hybool : ∃ q, y = .bool q := by
    cases y with
    | bool q => exact ⟨q, rfl⟩
    | int w => cases hxy with
      | inl h =>
          have h1 : Value.int w = Value.bool false := h.2
          exact absurd h1 (by simp)
      | inr h =>
          have h1 : Value.int w = Value.bool true := h.2
          exact absurd h1 (by simp)
    | setOfInt w => cases hxy with
      | inl h =>
          have h1 : Value.setOfInt w = Value.bool false := h.2
          exact absurd h1 (by simp)
      | inr h =>
          have h1 : Value.setOfInt w = Value.bool true := h.2
          exact absurd h1 (by simp)
    | array w => cases hxy with
      | inl h =>
          have h1 : Value.array w = Value.bool false := h.2
          exact absurd h1 (by simp)
      | inr h =>
          have h1 : Value.array w = Value.bool true := h.2
          exact absurd h1 (by simp)
  obtain ⟨p, rfl⟩ := hxbool
  obtain ⟨q, rfl⟩ := hybool
  refine ⟨p, q, hx, hy, ?_⟩
  cases p <;> cases q <;> simp_all

/-- The narrowed target for `bool_not`'s `i` side (when `j` is the
    pinned singleton `q` and the assignment reads `p` at `i`, with
    `q = !p`): the read value survives the narrowing. -/
private theorem boolNot_target_i {q p : Bool} {i : Nat}
    {doms : List (List Value)} {a : List Value}
    (ha : a ∈ allAssigns doms) (hx : a[i]? = some (.bool p))
    (hqp : q = !p) :
    .bool p ∈ (if q then falseVals (getSlot doms i)
      else trueVals (getSlot doms i)) := by
  obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
  cases p with
  | true =>
      have hq' : q = false := by rw [hqp]; rfl
      subst hq'
      exact mem_trueVals.mpr ⟨hget i _ hx, rfl⟩
  | false =>
      have hq' : q = true := by rw [hqp]; rfl
      subst hq'
      exact mem_falseVals.mpr ⟨hget i _ hx, rfl⟩

/-- The narrowed target for `bool_not`'s `j` side (when `i` is the
    pinned singleton `p` and the assignment reads `q` at `j`, with
    `q = !p`): the read value survives the narrowing. -/
private theorem boolNot_target_j {p q : Bool} {j : Nat}
    {doms : List (List Value)} {a : List Value}
    (ha : a ∈ allAssigns doms) (hy : a[j]? = some (.bool q))
    (hpq : q = !p) :
    .bool q ∈ (if p then falseVals (getSlot doms j)
      else trueVals (getSlot doms j)) := by
  obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
  cases p with
  | true =>
      have hq' : q = false := by rw [hpq]; rfl
      subst hq'
      exact mem_falseVals.mpr ⟨hget j _ hy, rfl⟩
  | false =>
      have hq' : q = true := by rw [hpq]; rfl
      subst hq'
      exact mem_trueVals.mpr ⟨hget j _ hy, rfl⟩

/-- **Preservation for `propBoolNotSlot`**: on `narrowed doms'`, every
    assignment of the input domains whose slots `i` and `j` carry
    opposite Booleans is still an assignment of `doms'`, and `doms'`
    is pointwise-subset the input domains; on `contradiction`, no
    assignment of the input domains makes them opposite. -/
theorem propBoolNotSlot_preserves (i j : Nat) :
    Preserves (DomConstraint.boolNotSlot i j) (propBoolNotSlot i j) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propBoolNotSlot] at h
    obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, q, hx, hy, hq⟩ := boolNot_opposite hsat
    have hxmem : .bool p ∈ boolVals (getSlot doms i) := mem_boolVals_of ha hx
    have hymem : .bool q ∈ boolVals (getSlot doms j) := mem_boolVals_of ha hy
    cases hs : singleBool? (getSlot doms i) with
    | none =>
        simp only [hs] at h
        cases hs2 : singleBool? (getSlot doms j) with
        | none =>
            simp only [hs2] at h
            have hd : doms' = doms := (PropResult.narrowed.inj h).symm
            subst hd
            exact ha
        | some q' =>
            simp only [hs2] at h
            have hqq' : q = q' := eq_of_singleBool? ha hy hs2
            -- the pin forces x = !q', so narrow slot i to the opposite
            have htarget : .bool p ∈ (if q' then falseVals (getSlot doms i)
              else trueVals (getSlot doms i)) :=
              boolNot_target_i ha hx (by rw [← hqq']; exact hq)
            by_cases hc : (if q' then falseVals (getSlot doms i)
                else trueVals (getSlot doms i)).isEmpty = true
            · rw [if_pos hc] at h
              rw [List.isEmpty_iff.mp hc] at htarget
              exact absurd htarget (by simp)
            · rw [if_neg hc] at h
              have hd : setSlot doms i
                  (if q' then falseVals (getSlot doms i)
                   else trueVals (getSlot doms i)) = doms' :=
                PropResult.narrowed.inj h
              subst hd
              have hilen : i < doms.length :=
                lt_length_of_mem_getSlot doms i _ (mem_boolVals.mp hxmem).1
              apply allAssigns_intro
              · rw [setSlot_length]
                exact hlen
              · intro m v hv
                by_cases hmi : m = i
                · rw [hmi] at hv
                  have hvp : v = .bool p := Option.some.inj (hv.symm.trans hx)
                  subst hvp
                  rw [hmi, getSlot_setSlot_eq doms _ i hilen]
                  exact htarget
                · rw [getSlot_setSlot_of_ne doms _ i m hmi]
                  exact hget m v hv
    | some p' =>
        simp only [hs] at h
        have hpp' : p = p' := eq_of_singleBool? ha hx hs
        have htarget : .bool q ∈ (if p' then falseVals (getSlot doms j)
          else trueVals (getSlot doms j)) :=
          boolNot_target_j ha hy (by rw [← hpp']; exact hq)
        by_cases hc : (if p' then falseVals (getSlot doms j)
            else trueVals (getSlot doms j)).isEmpty = true
        · rw [if_pos hc] at h
          rw [List.isEmpty_iff.mp hc] at htarget
          exact absurd htarget (by simp)
        · rw [if_neg hc] at h
          have hd : setSlot doms j
              (if p' then falseVals (getSlot doms j)
               else trueVals (getSlot doms j)) = doms' :=
            PropResult.narrowed.inj h
          subst hd
          have hjlen : j < doms.length :=
            lt_length_of_mem_getSlot doms j _ (mem_boolVals.mp hymem).1
          apply allAssigns_intro
          · rw [setSlot_length]
            exact hlen
          · intro m v hv
            by_cases hmj : m = j
            · rw [hmj] at hv
              have hvq : v = .bool q := Option.some.inj (hv.symm.trans hy)
              subst hvq
              rw [hmj, getSlot_setSlot_eq doms _ j hjlen]
              exact htarget
            · rw [getSlot_setSlot_of_ne doms _ j m hmj]
              exact hget m v hv
  · intro doms doms' h
    simp only [propBoolNotSlot] at h
    cases hs : singleBool? (getSlot doms i) with
    | none =>
        simp only [hs] at h
        cases hs2 : singleBool? (getSlot doms j) with
        | none =>
            simp only [hs2] at h
            have hd : doms' = doms := (PropResult.narrowed.inj h).symm
            subst hd
            exact DomPointwiseSub.refl _
        | some q' =>
            simp only [hs2] at h
            by_cases hc : (if q' then falseVals (getSlot doms i)
                else trueVals (getSlot doms i)).isEmpty = true
            · rw [if_pos hc] at h
              exact absurd h (by simp)
            · rw [if_neg hc] at h
              have hd : setSlot doms i
                  (if q' then falseVals (getSlot doms i)
                   else trueVals (getSlot doms i)) = doms' :=
                PropResult.narrowed.inj h
              subst hd
              refine DomPointwiseSub.setSlot (DomPointwiseSub.refl doms) ?_
              intro v hv
              cases q' with
              | true => exact (mem_falseVals.mp hv).1
              | false => exact (mem_trueVals.mp hv).1
    | some p' =>
        simp only [hs] at h
        by_cases hc : (if p' then falseVals (getSlot doms j)
            else trueVals (getSlot doms j)).isEmpty = true
        · rw [if_pos hc] at h
          exact absurd h (by simp)
        · rw [if_neg hc] at h
          have hd : setSlot doms j
              (if p' then falseVals (getSlot doms j)
               else trueVals (getSlot doms j)) = doms' :=
            PropResult.narrowed.inj h
          subst hd
          refine DomPointwiseSub.setSlot (DomPointwiseSub.refl doms) ?_
          intro v hv
          cases p' with
          | true => exact (mem_falseVals.mp hv).1
          | false => exact (mem_trueVals.mp hv).1
  · intro doms h a ha hsat
    simp only [propBoolNotSlot] at h
    obtain ⟨p, q, hx, hy, hq⟩ := boolNot_opposite hsat
    have hxmem : .bool p ∈ boolVals (getSlot doms i) := mem_boolVals_of ha hx
    have hymem : .bool q ∈ boolVals (getSlot doms j) := mem_boolVals_of ha hy
    cases hs : singleBool? (getSlot doms i) with
    | none =>
        simp only [hs] at h
        cases hs2 : singleBool? (getSlot doms j) with
        | none => rw [hs2] at h; exact absurd h (by simp)
        | some q' =>
            simp only [hs2] at h
            have hqq' : q = q' := eq_of_singleBool? ha hy hs2
            have htarget : .bool p ∈ (if q' then falseVals (getSlot doms i)
              else trueVals (getSlot doms i)) :=
              boolNot_target_i ha hx (by rw [← hqq']; exact hq)
            by_cases hc : (if q' then falseVals (getSlot doms i)
                else trueVals (getSlot doms i)).isEmpty = true
            · rw [if_pos hc] at h
              rw [List.isEmpty_iff.mp hc] at htarget
              exact absurd htarget (by simp)
            · rw [if_neg hc] at h
              exact absurd h (by simp)
    | some p' =>
        simp only [hs] at h
        have hpp' : p = p' := eq_of_singleBool? ha hx hs
        have htarget : .bool q ∈ (if p' then falseVals (getSlot doms j)
          else trueVals (getSlot doms j)) :=
          boolNot_target_j ha hy (by rw [← hpp']; exact hq)
        by_cases hc : (if p' then falseVals (getSlot doms j)
            else trueVals (getSlot doms j)).isEmpty = true
        · rw [if_pos hc] at h
          rw [List.isEmpty_iff.mp hc] at htarget
          exact absurd htarget (by simp)
        · rw [if_neg hc] at h
          exact absurd h (by simp)

/-- The Boolean conjunction propagator (`bool_and` style on three
    slots): when both input slots' Boolean values are singleton
    pinned, the output slot narrows to their conjunction; otherwise
    the domains are unchanged; `contradiction` when the narrowed
    output empties. -/
def propBoolAndSlot (i j k : Nat) (doms : List (List Value)) : PropResult :=
  match singleBool? (getSlot doms i), singleBool? (getSlot doms j) with
  | some p, some q =>
      let dk' := if (p && q) then trueVals (getSlot doms k) else falseVals (getSlot doms k)
      if dk'.isEmpty = true then .contradiction
      else .narrowed (setSlot doms k dk')
  | _, _ => .narrowed doms

/-- The narrowed output target for `bool_and`: the assignment's
    output value survives the conjunction narrowing. -/
private theorem boolAnd_target {r : Bool} {k : Nat} {p' q' : Bool}
    {doms : List (List Value)} {a : List Value}
    (ha : a ∈ allAssigns doms) (hz : a[k]? = some (.bool r))
    (hand : (p' && q') = r) :
    .bool r ∈ (if (p' && q') then trueVals (getSlot doms k)
      else falseVals (getSlot doms k)) := by
  obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
  subst hand
  cases p' <;> cases q' <;>
    first
      | exact mem_trueVals.mpr ⟨hget k _ hz, rfl⟩
      | exact mem_falseVals.mpr ⟨hget k _ hz, rfl⟩

/-- **Preservation for `propBoolAndSlot`**: on `narrowed doms'`, every
    assignment of the input domains whose slots `i`, `j`, `k` carry
    Booleans `p`, `q`, `r` with `p && q = r` is still an assignment of
    `doms'`, and `doms'` is pointwise-subset the input domains; on
    `contradiction`, no assignment of the input domains satisfies the
    conjunction. -/
theorem propBoolAndSlot_preserves (i j k : Nat) :
    Preserves (DomConstraint.boolAndSlot i j k) (propBoolAndSlot i j k) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propBoolAndSlot] at h
    obtain ⟨p, q, r, hx, hy, hz, hand⟩ := hsat
    have hxmem : .bool p ∈ boolVals (getSlot doms i) := mem_boolVals_of ha hx
    have hymem : .bool q ∈ boolVals (getSlot doms j) := mem_boolVals_of ha hy
    have hzmem : .bool r ∈ boolVals (getSlot doms k) := mem_boolVals_of ha hz
    cases hs : singleBool? (getSlot doms i) with
    | some p' =>
        simp only [hs] at h
        have hpp' : p = p' := eq_of_singleBool? ha hx hs
        cases hs2 : singleBool? (getSlot doms j) with
        | some q' =>
            simp only [hs2] at h
            have hqq' : q = q' := eq_of_singleBool? ha hy hs2
            have hand' : (p' && q') = r := by rw [← hpp', ← hqq']; exact hand
            have htarget : .bool r ∈
                (if (p' && q') then trueVals (getSlot doms k)
                 else falseVals (getSlot doms k)) :=
              boolAnd_target ha hz hand'
            by_cases hc : (if (p' && q') then trueVals (getSlot doms k)
                else falseVals (getSlot doms k)).isEmpty = true
            · rw [if_pos hc] at h
              rw [List.isEmpty_iff.mp hc] at htarget
              exact absurd htarget (by simp)
            · rw [if_neg hc] at h
              have hd : setSlot doms k
                  (if (p' && q') then trueVals (getSlot doms k)
                   else falseVals (getSlot doms k)) = doms' :=
                PropResult.narrowed.inj h
              subst hd
              obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
              have hklen : k < doms.length :=
                lt_length_of_mem_getSlot doms k _ (mem_boolVals.mp hzmem).1
              apply allAssigns_intro
              · rw [setSlot_length]
                exact hlen
              · intro m v hv
                by_cases hmk : m = k
                · rw [hmk] at hv
                  have hvr : v = .bool r := Option.some.inj (hv.symm.trans hz)
                  subst hvr
                  rw [hmk, getSlot_setSlot_eq doms _ k hklen]
                  exact htarget
                · rw [getSlot_setSlot_of_ne doms _ k m hmk]
                  exact hget m v hv
        | none =>
            simp only [hs2] at h
            have hd : doms' = doms := (PropResult.narrowed.inj h).symm
            subst hd
            exact ha
    | none =>
        simp only [hs] at h
        have hd : doms' = doms := (PropResult.narrowed.inj h).symm
        subst hd
        exact ha
  · intro doms doms' h
    simp only [propBoolAndSlot] at h
    cases hs : singleBool? (getSlot doms i) with
    | some p' =>
        simp only [hs] at h
        cases hs2 : singleBool? (getSlot doms j) with
        | some q' =>
            rw [hs2] at h
            simp only [] at h
            by_cases hc : (if (p' && q') then trueVals (getSlot doms k)
                else falseVals (getSlot doms k)).isEmpty = true
            · rw [if_pos hc] at h
              exact absurd h (by simp)
            · rw [if_neg hc] at h
              have hd : setSlot doms k
                  (if (p' && q') then trueVals (getSlot doms k)
                   else falseVals (getSlot doms k)) = doms' :=
                PropResult.narrowed.inj h
              subst hd
              refine DomPointwiseSub.setSlot (DomPointwiseSub.refl doms) ?_
              intro v hv
              cases p' <;> cases q' <;> simp at hv <;>
                first
                  | exact (mem_trueVals.mp hv).1
                  | exact (mem_falseVals.mp hv).1
        | none =>
            simp only [hs2] at h
            have hd : doms' = doms := (PropResult.narrowed.inj h).symm
            subst hd
            exact DomPointwiseSub.refl _
    | none =>
        simp only [hs] at h
        have hd : doms' = doms := (PropResult.narrowed.inj h).symm
        subst hd
        exact DomPointwiseSub.refl _
  · intro doms h a ha hsat
    simp only [propBoolAndSlot] at h
    obtain ⟨p, q, r, hx, hy, hz, hand⟩ := hsat
    have hxmem : .bool p ∈ boolVals (getSlot doms i) := mem_boolVals_of ha hx
    have hymem : .bool q ∈ boolVals (getSlot doms j) := mem_boolVals_of ha hy
    have hzmem : .bool r ∈ boolVals (getSlot doms k) := mem_boolVals_of ha hz
    cases hs : singleBool? (getSlot doms i) with
    | some p' =>
        simp only [hs] at h
        have hpp' : p = p' := eq_of_singleBool? ha hx hs
        cases hs2 : singleBool? (getSlot doms j) with
        | some q' =>
            simp only [hs2] at h
            have hqq' : q = q' := eq_of_singleBool? ha hy hs2
            have hand' : (p' && q') = r := by rw [← hpp', ← hqq']; exact hand
            have htarget : .bool r ∈
                (if (p' && q') then trueVals (getSlot doms k)
                 else falseVals (getSlot doms k)) :=
              boolAnd_target ha hz hand'
            by_cases hc : (if (p' && q') then trueVals (getSlot doms k)
                else falseVals (getSlot doms k)).isEmpty = true
            · rw [if_pos hc] at h
              rw [List.isEmpty_iff.mp hc] at htarget
              exact absurd htarget (by simp)
            · rw [if_neg hc] at h
              exact absurd h (by simp)
        | none => rw [hs2] at h; exact absurd h (by simp)
    | none => rw [hs] at h; exact absurd h (by simp)

/-- The Boolean disjunction propagator (`bool_or` style on three
    slots): when both input slots' Boolean values are singleton
    pinned, the output slot narrows to their disjunction; otherwise
    the domains are unchanged; `contradiction` when the narrowed
    output empties. -/
def propBoolOrSlot (i j k : Nat) (doms : List (List Value)) : PropResult :=
  match singleBool? (getSlot doms i), singleBool? (getSlot doms j) with
  | some p, some q =>
      let dk' := if (p || q) then trueVals (getSlot doms k) else falseVals (getSlot doms k)
      if dk'.isEmpty = true then .contradiction
      else .narrowed (setSlot doms k dk')
  | _, _ => .narrowed doms

/-- The narrowed output target for `bool_or`: the assignment's
    output value survives the disjunction narrowing. -/
private theorem boolOr_target {r : Bool} {k : Nat} {p' q' : Bool}
    {doms : List (List Value)} {a : List Value}
    (ha : a ∈ allAssigns doms) (hz : a[k]? = some (.bool r))
    (hor : (p' || q') = r) :
    .bool r ∈ (if (p' || q') then trueVals (getSlot doms k)
      else falseVals (getSlot doms k)) := by
  obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
  subst hor
  cases p' <;> cases q' <;>
    first
      | exact mem_trueVals.mpr ⟨hget k _ hz, rfl⟩
      | exact mem_falseVals.mpr ⟨hget k _ hz, rfl⟩

/-- **Preservation for `propBoolOrSlot`**: on `narrowed doms'`, every
    assignment of the input domains whose slots `i`, `j`, `k` carry
    Booleans `p`, `q`, `r` with `p || q = r` is still an assignment of
    `doms'`, and `doms'` is pointwise-subset the input domains; on
    `contradiction`, no assignment of the input domains satisfies the
    disjunction. -/
theorem propBoolOrSlot_preserves (i j k : Nat) :
    Preserves (DomConstraint.boolOrSlot i j k) (propBoolOrSlot i j k) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propBoolOrSlot] at h
    obtain ⟨p, q, r, hx, hy, hz, hor⟩ := hsat
    have hxmem : .bool p ∈ boolVals (getSlot doms i) := mem_boolVals_of ha hx
    have hymem : .bool q ∈ boolVals (getSlot doms j) := mem_boolVals_of ha hy
    have hzmem : .bool r ∈ boolVals (getSlot doms k) := mem_boolVals_of ha hz
    cases hs : singleBool? (getSlot doms i) with
    | some p' =>
        simp only [hs] at h
        have hpp' : p = p' := eq_of_singleBool? ha hx hs
        cases hs2 : singleBool? (getSlot doms j) with
        | some q' =>
            simp only [hs2] at h
            have hqq' : q = q' := eq_of_singleBool? ha hy hs2
            have hor' : (p' || q') = r := by rw [← hpp', ← hqq']; exact hor
            have htarget : .bool r ∈
                (if (p' || q') then trueVals (getSlot doms k)
                 else falseVals (getSlot doms k)) :=
              boolOr_target ha hz hor'
            by_cases hc : (if (p' || q') then trueVals (getSlot doms k)
                else falseVals (getSlot doms k)).isEmpty = true
            · rw [if_pos hc] at h
              rw [List.isEmpty_iff.mp hc] at htarget
              exact absurd htarget (by simp)
            · rw [if_neg hc] at h
              have hd : setSlot doms k
                  (if (p' || q') then trueVals (getSlot doms k)
                   else falseVals (getSlot doms k)) = doms' :=
                PropResult.narrowed.inj h
              subst hd
              obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
              have hklen : k < doms.length :=
                lt_length_of_mem_getSlot doms k _ (mem_boolVals.mp hzmem).1
              apply allAssigns_intro
              · rw [setSlot_length]
                exact hlen
              · intro m v hv
                by_cases hmk : m = k
                · rw [hmk] at hv
                  have hvr : v = .bool r := Option.some.inj (hv.symm.trans hz)
                  subst hvr
                  rw [hmk, getSlot_setSlot_eq doms _ k hklen]
                  exact htarget
                · rw [getSlot_setSlot_of_ne doms _ k m hmk]
                  exact hget m v hv
        | none =>
            simp only [hs2] at h
            have hd : doms' = doms := (PropResult.narrowed.inj h).symm
            subst hd
            exact ha
    | none =>
        simp only [hs] at h
        have hd : doms' = doms := (PropResult.narrowed.inj h).symm
        subst hd
        exact ha
  · intro doms doms' h
    simp only [propBoolOrSlot] at h
    cases hs : singleBool? (getSlot doms i) with
    | some p' =>
        simp only [hs] at h
        cases hs2 : singleBool? (getSlot doms j) with
        | some q' =>
            rw [hs2] at h
            simp only [] at h
            by_cases hc : (if (p' || q') then trueVals (getSlot doms k)
                else falseVals (getSlot doms k)).isEmpty = true
            · rw [if_pos hc] at h
              exact absurd h (by simp)
            · rw [if_neg hc] at h
              have hd : setSlot doms k
                  (if (p' || q') then trueVals (getSlot doms k)
                   else falseVals (getSlot doms k)) = doms' :=
                PropResult.narrowed.inj h
              subst hd
              refine DomPointwiseSub.setSlot (DomPointwiseSub.refl doms) ?_
              intro v hv
              cases p' <;> cases q' <;> simp at hv <;>
                first
                  | exact (mem_trueVals.mp hv).1
                  | exact (mem_falseVals.mp hv).1
        | none =>
            simp only [hs2] at h
            have hd : doms' = doms := (PropResult.narrowed.inj h).symm
            subst hd
            exact DomPointwiseSub.refl _
    | none =>
        simp only [hs] at h
        have hd : doms' = doms := (PropResult.narrowed.inj h).symm
        subst hd
        exact DomPointwiseSub.refl _
  · intro doms h a ha hsat
    simp only [propBoolOrSlot] at h
    obtain ⟨p, q, r, hx, hy, hz, hor⟩ := hsat
    have hxmem : .bool p ∈ boolVals (getSlot doms i) := mem_boolVals_of ha hx
    have hymem : .bool q ∈ boolVals (getSlot doms j) := mem_boolVals_of ha hy
    have hzmem : .bool r ∈ boolVals (getSlot doms k) := mem_boolVals_of ha hz
    cases hs : singleBool? (getSlot doms i) with
    | some p' =>
        simp only [hs] at h
        have hpp' : p = p' := eq_of_singleBool? ha hx hs
        cases hs2 : singleBool? (getSlot doms j) with
        | some q' =>
            simp only [hs2] at h
            have hqq' : q = q' := eq_of_singleBool? ha hy hs2
            have hor' : (p' || q') = r := by rw [← hpp', ← hqq']; exact hor
            have htarget : .bool r ∈
                (if (p' || q') then trueVals (getSlot doms k)
                 else falseVals (getSlot doms k)) :=
              boolOr_target ha hz hor'
            by_cases hc : (if (p' || q') then trueVals (getSlot doms k)
                else falseVals (getSlot doms k)).isEmpty = true
            · rw [if_pos hc] at h
              rw [List.isEmpty_iff.mp hc] at htarget
              exact absurd htarget (by simp)
            · rw [if_neg hc] at h
              exact absurd h (by simp)
        | none => rw [hs2] at h; exact absurd h (by simp)
    | none => rw [hs] at h; exact absurd h (by simp)


end LeanFzn.Solver.Propagation.DomainFiltering

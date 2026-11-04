/-
File: LeanFzn/Solver/Propagation/Proofs/Fam/MinGen.lean

PLAN C9c: the n-ary `array_int_minimum`/`array_int_maximum` result
propagators `propMinGen`/`propMaxGen` (the `minGen`/`maxGen` constraint
families, produced by the C6 extractor for the array extremes).

Both families force the result value to be ATTAINED by one of the
operands (`minValue`/`maxValue` always return the value of an operand's
integer read, even when a non-integer TAIL is present — the C9
`array_int_minimum_rewrite_gap` semantics), so the two bounds

* `result ≥ min` of the operands' state lower bounds,
* `result ≤ max` of the operands' state upper bounds,

are valid at every solution of the constraint, with reasons built from
the operands' own bound literals.  Every emitted literal is an order
literal over an operand or the result slot, so the emissions are
canonical, slot-typed (given the operand/result slot typing) and never
Boolean atoms.

The stronger interval `result ∈ [min lo, min hi]` (the `propMin`
corner bounds) is NOT sound for the array families without an
int-typing gate on the operand slots: `minValue` ignores a non-integer
element after the integer prefix, so a Boolean operand read can exceed
the operand's own upper bound while the constraint still holds (see
`minGen_hI_gap` below for the kernel-checked counterexample shape).

Dependencies:
  - LeanFzn.Solver.Propagation.Proofs.Fam.Lin (`domsIntOnlyB`,
    the narrow* machinery through ConstFamilies/Theory).

DAG:
  LeanFzn.Solver.Propagation.Proofs.Fam.Lin
    -> LeanFzn.Solver.Propagation.Proofs.Fam.MinGen (this file)
    -> consumers (Propagators, UIP obligation files).
-/
import LeanFzn.Solver.Propagation.Proofs.Fam.Lin

open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation
open LeanFzn.Solver.Reference

/-! ## 1. The fold-shaped extremum reading of an operand list -/

/-- The lower integer bound an operand has in the state: a slot's current
    integer minimum, or the literal's own value. -/
def argLoB (st : State) : DomIntArg → Option Int
  | .slot i => domMinI (st.domains.getD i Dom.empty)
  | .lit k => some k

/-- The upper integer bound an operand has in the state: a slot's current
    integer maximum, or the literal's own value. -/
def argHiB (st : State) : DomIntArg → Option Int
  | .slot i => domMaxI (st.domains.getD i Dom.empty)
  | .lit k => some k

/-- The fold-shaped minimum of the operands' lower bounds: `none` unless
    every operand has one (a literal always does). -/
def minArgLo (st : State) : List DomIntArg → Option Int
  | [] => none
  | [o] => argLoB st o
  | o :: o' :: os =>
      match argLoB st o, minArgLo st (o' :: os) with
      | some l, some m => some (minI l m)
      | _, _ => none

/-- The fold-shaped maximum of the operands' upper bounds. -/
def maxArgHi (st : State) : List DomIntArg → Option Int
  | [] => none
  | [o] => argHiB st o
  | o :: o' :: os =>
      match argHiB st o, maxArgHi st (o' :: os) with
      | some h, some m => some (maxI h m)
      | _, _ => none

/-- `minArgLo` bounds every operand's lower bound from below. -/
theorem minArgLo_spec {st : State} {os : List DomIntArg} {m : Int}
    (h : minArgLo st os = some m) :
    ∀ o ∈ os, ∃ l, argLoB st o = some l ∧ m ≤ l := by
  cases os with
  | nil => simp [minArgLo] at h
  | cons o rest =>
      cases rest with
      | nil =>
          intro o' ho'
          rw [List.mem_singleton] at ho'
          subst ho'
          exact ⟨m, h, Int.le_refl m⟩
      | cons o' os =>
          simp only [minArgLo] at h
          cases hl : argLoB st o with
          | none => rw [hl] at h; cases h
          | some l =>
              cases hr : minArgLo st (o' :: os) with
              | none => rw [hl, hr] at h; cases h
              | some m' =>
                  rw [hl, hr] at h
                  have hm : m = minI l m' := (Option.some.inj h).symm
                  have ih := minArgLo_spec (st := st) hr
                  intro o'' ho''
                  rcases List.mem_cons.mp ho'' with rfl | ho''
                  · exact ⟨l, hl, by rw [hm]; exact minI_le_left l m'⟩
                  · obtain ⟨l', hl', hle⟩ := ih o'' ho''
                    exact ⟨l', hl', by
                      rw [hm]
                      exact Int.le_trans (minI_le_right l m') hle⟩

/-- `maxArgHi` bounds every operand's upper bound from above. -/
theorem maxArgHi_spec {st : State} {os : List DomIntArg} {m : Int}
    (h : maxArgHi st os = some m) :
    ∀ o ∈ os, ∃ h', argHiB st o = some h' ∧ h' ≤ m := by
  cases os with
  | nil => simp [maxArgHi] at h
  | cons o rest =>
      cases rest with
      | nil =>
          intro o' ho'
          rw [List.mem_singleton] at ho'
          subst ho'
          exact ⟨m, h, Int.le_refl m⟩
      | cons o' os =>
          simp only [maxArgHi] at h
          cases hl : argHiB st o with
          | none => rw [hl] at h; cases h
          | some h' =>
              cases hr : maxArgHi st (o' :: os) with
              | none => rw [hl, hr] at h; cases h
              | some m' =>
                  rw [hl, hr] at h
                  have hm : m = maxI h' m' := (Option.some.inj h).symm
                  have ih := maxArgHi_spec (st := st) hr
                  intro o'' ho''
                  rcases List.mem_cons.mp ho'' with rfl | ho''
                  · exact ⟨h', hl, by rw [hm]; exact maxI_ge_left h' m'⟩
                  · obtain ⟨h'', hh'', hle⟩ := ih o'' ho''
                    exact ⟨h'', hh'', by
                      rw [hm]
                      exact Int.le_trans hle (maxI_ge_right h' m')⟩

/-! ## 2. The cause literals of the arms -/

/-- The lower-bound cause of one operand: for a slot operand whose
    domain has an integer minimum `l`, the literal "slot ≤ l − 1". -/
def argLoCause (st : State) : DomIntArg → Clause
  | .slot i =>
      match domMinI (st.domains.getD i Dom.empty) with
      | some l => [posLe i (l - 1)]
      | none => []
  | .lit _ => []

/-- The upper-bound cause of one operand: for a slot operand whose
    domain has an integer maximum `h`, the literal "slot > h". -/
def argHiCause (st : State) : DomIntArg → Clause
  | .slot i =>
      match domMaxI (st.domains.getD i Dom.empty) with
      | some h => [negLe i h]
      | none => []
  | .lit _ => []

/-- The lower-bound cause of a slot operand is in the flat-mapped list. -/
theorem argLoCause_mem {st : State} {os : List DomIntArg} {i : Nat} {l : Int}
    (hmem : DomIntArg.slot i ∈ os)
    (hl : domMinI (st.domains.getD i Dom.empty) = some l) :
    posLe i (l - 1) ∈ os.flatMap (argLoCause st) :=
  List.mem_flatMap.mpr ⟨.slot i, hmem, by
    simp only [argLoCause, hl, List.mem_singleton_self]⟩

/-- The upper-bound cause of a slot operand is in the flat-mapped list. -/
theorem argHiCause_mem {st : State} {os : List DomIntArg} {i : Nat} {h : Int}
    (hmem : DomIntArg.slot i ∈ os)
    (hh : domMaxI (st.domains.getD i Dom.empty) = some h) :
    negLe i h ∈ os.flatMap (argHiCause st) :=
  List.mem_flatMap.mpr ⟨.slot i, hmem, by
    simp only [argHiCause, hh, List.mem_singleton_self]⟩

/-- The lower-bound cause of a slot operand with no integer minimum. -/
theorem argLoCause_slot_none {st : State} {i : Nat}
    (hl : domMinI (st.domains.getD i Dom.empty) = none) :
    argLoCause st (.slot i) = [] := by
  simp only [argLoCause, hl]

/-- The lower-bound cause of a slot operand with integer minimum `l`. -/
theorem argLoCause_slot_some {st : State} {i : Nat} {l : Int}
    (hl : domMinI (st.domains.getD i Dom.empty) = some l) :
    argLoCause st (.slot i) = [posLe i (l - 1)] := by
  simp only [argLoCause, hl]

/-- The upper-bound cause of a slot operand with no integer maximum. -/
theorem argHiCause_slot_none {st : State} {i : Nat}
    (hh : domMaxI (st.domains.getD i Dom.empty) = none) :
    argHiCause st (.slot i) = [] := by
  simp only [argHiCause, hh]

/-- The upper-bound cause of a slot operand with integer maximum `h`. -/
theorem argHiCause_slot_some {st : State} {i : Nat} {h : Int}
    (hh : domMaxI (st.domains.getD i Dom.empty) = some h) :
    argHiCause st (.slot i) = [negLe i h] := by
  simp only [argHiCause, hh]

/-- Every lower-bound cause is a normalized order literal. -/
theorem argLoCause_canonical (st : State) (o : DomIntArg) :
    ∀ q ∈ argLoCause st o, q = q.norm := by
  intro q hq
  cases o with
  | lit k => simp [argLoCause] at hq
  | slot i =>
      cases hl : domMinI (st.domains.getD i Dom.empty) with
      | none =>
          rw [argLoCause_slot_none hl] at hq
          cases hq
      | some l =>
          rw [argLoCause_slot_some hl] at hq
          rw [List.mem_singleton] at hq
          rw [hq]
          exact posLe_norm _ _

/-- Every upper-bound cause is a normalized order literal. -/
theorem argHiCause_canonical (st : State) (o : DomIntArg) :
    ∀ q ∈ argHiCause st o, q = q.norm := by
  intro q hq
  cases o with
  | lit k => simp [argHiCause] at hq
  | slot i =>
      cases hh : domMaxI (st.domains.getD i Dom.empty) with
      | none =>
          rw [argHiCause_slot_none hh] at hq
          cases hq
      | some h =>
          rw [argHiCause_slot_some hh] at hq
          rw [List.mem_singleton] at hq
          rw [hq]
          exact negLe_norm _ _

/-- Flat-mapped cause lists are canonical when each entry is. -/
theorem clauseCanonical_flatMap {os : List DomIntArg} {f : DomIntArg → Clause}
    (hf : ∀ o ∈ os, ∀ q ∈ f o, q = q.norm) :
    ∀ q ∈ os.flatMap f, q = q.norm := by
  induction os with
  | nil => intro q hq; cases hq
  | cons o rest ih =>
      intro q hq
      rw [List.flatMap_cons] at hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hf o List.mem_cons_self q hq
      · exact ih (fun o' ho' => hf o' (List.mem_cons_of_mem _ ho')) q hq

/-! ## 3. The attained-value semantics of `minValue`/`maxValue` -/

/-- The minimum of a value list is the integer value of one of its
    elements (the semantics that makes the array extremes
    `minGen`-representable at all — a non-integer TAIL does not destroy
    the attained element). -/
theorem minValue_mem : ∀ (vs : List Value) (m : Int), minValue vs = some m →
    ∃ v ∈ vs, v = .int m := by
  intro vs
  induction vs with
  | nil => intro m h; simp [minValue] at h
  | cons v vs ih =>
      intro m h
      cases v with
      | int x =>
          simp only [minValue] at h
          cases hr : minValue vs with
          | none =>
              rw [hr] at h
              have hm : m = x := (Option.some.inj h).symm
              rw [hm]
              exact ⟨.int x, List.mem_cons_self, rfl⟩
          | some m' =>
              rw [hr] at h
              have hm : m = min x m' := (Option.some.inj h).symm
              by_cases hx : x ≤ m'
              · rw [hm, Int.min_eq_left hx]
                exact ⟨.int x, List.mem_cons_self, rfl⟩
              · rw [hm, Int.min_eq_right (by omega : m' ≤ x)]
                obtain ⟨v', hv', hveq⟩ := ih m' hr
                exact ⟨v', List.mem_cons_of_mem _ hv', hveq⟩
      | bool b => simp [minValue] at h
      | setOfInt w => simp [minValue] at h
      | array w => simp [minValue] at h

/-- The maximum of a value list is the integer value of one of its
    elements. -/
theorem maxValue_mem : ∀ (vs : List Value) (m : Int), maxValue vs = some m →
    ∃ v ∈ vs, v = .int m := by
  intro vs
  induction vs with
  | nil => intro m h; simp [maxValue] at h
  | cons v vs ih =>
      intro m h
      cases v with
      | int x =>
          simp only [maxValue] at h
          cases hr : maxValue vs with
          | none =>
              rw [hr] at h
              have hm : m = x := (Option.some.inj h).symm
              rw [hm]
              exact ⟨.int x, List.mem_cons_self, rfl⟩
          | some m' =>
              rw [hr] at h
              have hm : m = max x m' := (Option.some.inj h).symm
              by_cases hx : m' ≤ x
              · rw [hm, Int.max_eq_left hx]
                exact ⟨.int x, List.mem_cons_self, rfl⟩
              · rw [hm, Int.max_eq_right (by omega : x ≤ m')]
                obtain ⟨v', hv', hveq⟩ := ih m' hr
                exact ⟨v', List.mem_cons_of_mem _ hv', hveq⟩
      | bool b => simp [maxValue] at h
      | setOfInt w => simp [maxValue] at h
      | array w => simp [maxValue] at h

/-- The attained value of `minValue` over the operand reads is the
    integer read of one of the operands. -/
theorem minGen_attained {os : List DomIntArg} {a : Assignment} {mv : Int}
    (h : minValue (os.map (DomIntArg.read a)) = some mv) :
    ∃ o ∈ os, DomIntArg.read a o = .int mv := by
  obtain ⟨v, hv, hveq⟩ := minValue_mem _ mv h
  obtain ⟨o, ho, hro⟩ := List.mem_map.mp hv
  exact ⟨o, ho, hro.trans hveq⟩

/-- The attained value of `maxValue` over the operand reads is the
    integer read of one of the operands. -/
theorem maxGen_attained {os : List DomIntArg} {a : Assignment} {mv : Int}
    (h : maxValue (os.map (DomIntArg.read a)) = some mv) :
    ∃ o ∈ os, DomIntArg.read a o = .int mv := by
  obtain ⟨v, hv, hveq⟩ := maxValue_mem _ mv h
  obtain ⟨o, ho, hro⟩ := List.mem_map.mp hv
  exact ⟨o, ho, hro.trans hveq⟩

/-- A raw `.int` read of a slot operand determines the slot's integer
    view (the bang read of an absent slot is the default value, which is
    not an `.int`). -/
theorem read_slot_int {a : Assignment} {i : Nat} {m : Int}
    (h : DomIntArg.read a (.slot i) = .int m) : slotInt a i = some m := by
  have hb : a[i]! = Value.int m := h
  cases hi : a[i]? with
  | none =>
      rw [List.getElem!_eq_getElem?_getD, hi] at hb
      exact absurd hb (by intro hc; cases hc)
  | some v =>
      rw [List.getElem!_eq_getElem?_getD, hi] at hb
      simp only [Option.getD_some] at hb
      rw [hb] at hi
      exact slotInt_of_int_read hi

/-- A raw `.int` read of a LITERAL operand fixes the read value. -/
theorem read_lit_int {a : Assignment} {k' mv : Int}
    (h : DomIntArg.read a (.lit k') = .int mv) : mv = k' := by
  have h' : (Value.int k' : Value) = .int mv := h
  injection h' with h''
  omega

/-! ## 4. The propagators -/

/-- PLAN C9c: the n-ary `array_int_minimum` result propagator over a
    slot result `k` and the operand list `os`.

    Arms (each with the operands' state-bound causes):
    * `r ≥ min` of the operands' lower bounds — the attained operand's
      own read is at or above its lower bound;
    * `r ≤ max` of the operands' upper bounds — the attained operand's
      own read is at or below its upper bound.

    Both arms are justifiable at every solution (the constraint forces
    the result to equal an operand's integer read), so no int-typing
    gate is needed.  Non-firing shapes (literal result, a missing
    operand bound) return `.stable`. -/
def propMinGen (st : State) (os : List DomIntArg) (r : DomIntArg) : PropagationResult :=
  match r with
  | .lit _ => .stable
  | .slot k =>
      match minArgLo st os, maxArgHi st os with
      | some m_lo, some m_hi =>
          firstEvent
            [ narrowLo st k m_lo
                (negLe k (m_lo - 1) :: os.flatMap (argLoCause st))
            , narrowHi st k m_hi
                (posLe k m_hi :: os.flatMap (argHiCause st)) ]
      | _, _ => .stable

/-- PLAN C9c: the n-ary `array_int_maximum` result propagator — the same
    two attained-operand arms as `propMinGen` (the result is attained by
    an operand read in both families). -/
def propMaxGen (st : State) (os : List DomIntArg) (r : DomIntArg) : PropagationResult :=
  match r with
  | .lit _ => .stable
  | .slot k =>
      match minArgLo st os, maxArgHi st os with
      | some m_lo, some m_hi =>
          firstEvent
            [ narrowLo st k m_lo
                (negLe k (m_lo - 1) :: os.flatMap (argLoCause st))
            , narrowHi st k m_hi
                (posLe k m_hi :: os.flatMap (argHiCause st)) ]
      | _, _ => .stable

/-- The attained-value bound core: a satisfied extreme constraint whose
    result value `mv` is attained by an operand read lies within the
    operands' state bounds. -/
theorem genValue_bounds {st : State} {a : Assignment} {os : List DomIntArg}
    {k : Nat} {mv m_lo m_hi : Int}
    (hfit : a.Fits st.domains)
    (homem : ∃ o ∈ os, DomIntArg.read a o = .int mv)
    (hrread : DomIntArg.read a (.slot k) = .int mv)
    (hlo : minArgLo st os = some m_lo)
    (hhi : maxArgHi st os = some m_hi) :
    slotInt a k = some mv ∧ m_lo ≤ mv ∧ mv ≤ m_hi := by
  obtain ⟨o, ho, hoatt⟩ := homem
  obtain ⟨l, hl, hmle⟩ := minArgLo_spec hlo o ho
  obtain ⟨h, hh, hle⟩ := maxArgHi_spec hhi o ho
  refine ⟨read_slot_int hrread, ?_, ?_⟩
  · cases o with
    | lit k' =>
        have h1 : k' = l := by simpa [argLoB] using hl
        have h2 : mv = k' := read_lit_int hoatt
        omega
    | slot i =>
        have hl' : domMinI (st.domains.getD i Dom.empty) = some l := hl
        have hslot : slotInt a i = some mv := read_slot_int hoatt
        have := fits_min_bound hfit hl' hslot
        omega
  · cases o with
    | lit k' =>
        have h1 : k' = h := by simpa [argHiB] using hh
        have h2 : mv = k' := read_lit_int hoatt
        omega
    | slot i =>
        have hh' : domMaxI (st.domains.getD i Dom.empty) = some h := hh
        have hslot : slotInt a i = some mv := read_slot_int hoatt
        have := fits_max_bound hfit hh' hslot
        omega


/-! ## 5. The solution-side nogoods of the arms -/

/-- The lower-bound nogood of the min arm has a true literal at every
    solution whose result value is attained by an operand: the pivot
    when the attained operand respects its own lower bound, the
    operand's cause literal otherwise. -/
theorem propGen_lo_nogood_true {st : State} {a : Assignment}
    {os : List DomIntArg} {k : Nat} {mv m_lo : Int}
    (homem : ∃ o ∈ os, DomIntArg.read a o = .int mv)
    (hrread : DomIntArg.read a (.slot k) = .int mv)
    (hlo : minArgLo st os = some m_lo) :
    ∃ q ∈ (negLe k (m_lo - 1) :: os.flatMap (argLoCause st)),
      q.eval a = some true := by
  obtain ⟨o, ho, hoatt⟩ := homem
  obtain ⟨l, hl, hmle⟩ := minArgLo_spec hlo o ho
  have hslotk : slotInt a k = some mv := read_slot_int hrread
  cases o with
  | lit k' =>
      have h1 : k' = l := by simpa [argLoB] using hl
      have h2 : mv = k' := read_lit_int hoatt
      exact ⟨negLe k (m_lo - 1), List.mem_cons_self,
        by rw [eval_negLe_iff]; exact ⟨mv, hslotk, by omega⟩⟩
  | slot i =>
      have hl' : domMinI (st.domains.getD i Dom.empty) = some l := hl
      have hslot : slotInt a i = some mv := read_slot_int hoatt
      by_cases hcase : mv < l
      · exact ⟨posLe i (l - 1), List.mem_cons_of_mem _ (argLoCause_mem ho hl'),
          by rw [eval_posLe_iff]; exact ⟨mv, hslot, by omega⟩⟩
      · exact ⟨negLe k (m_lo - 1), List.mem_cons_self,
          by rw [eval_negLe_iff]; exact ⟨mv, hslotk, by omega⟩⟩

/-- The upper-bound nogood of the max arm has a true literal at every
    solution whose result value is attained by an operand. -/
theorem propGen_hi_nogood_true {st : State} {a : Assignment}
    {os : List DomIntArg} {k : Nat} {mv m_hi : Int}
    (homem : ∃ o ∈ os, DomIntArg.read a o = .int mv)
    (hrread : DomIntArg.read a (.slot k) = .int mv)
    (hhi : maxArgHi st os = some m_hi) :
    ∃ q ∈ (posLe k m_hi :: os.flatMap (argHiCause st)),
      q.eval a = some true := by
  obtain ⟨o, ho, hoatt⟩ := homem
  obtain ⟨h, hh, hle⟩ := maxArgHi_spec hhi o ho
  have hslotk : slotInt a k = some mv := read_slot_int hrread
  cases o with
  | lit k' =>
      have h1 : k' = h := by simpa [argHiB] using hh
      have h2 : mv = k' := read_lit_int hoatt
      exact ⟨posLe k m_hi, List.mem_cons_self,
        by rw [eval_posLe_iff]; exact ⟨mv, hslotk, by omega⟩⟩
  | slot i =>
      have hh' : domMaxI (st.domains.getD i Dom.empty) = some h := hh
      have hslot : slotInt a i = some mv := read_slot_int hoatt
      by_cases hcase : h < mv
      · exact ⟨negLe i h, List.mem_cons_of_mem _ (argHiCause_mem ho hh'),
          by rw [eval_negLe_iff]; exact ⟨mv, hslot, by omega⟩⟩
      · exact ⟨posLe k m_hi, List.mem_cons_self,
          by rw [eval_posLe_iff]; exact ⟨mv, hslotk, by omega⟩⟩

/-! ## 6. The obligation packages -/

/-- PLAN C9c: the `minGen` result propagator `propMinGen` is sound:
    implied literals hold at every fitting solution of the constraint, a
    reported conflict admits no fitting solution, and every conflict
    clause carries a literal true at every fitting solution. -/
theorem propMinGen_safe (st : State) (os : List DomIntArg) (r : DomIntArg) :
    (∀ l rr, propMinGen st os r = .implied l rr →
      ∀ a, Assignment.Fits st.domains a →
        (DomConstraint.minGen os r).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ c, propMinGen st os r = .conflict c →
      ∀ a, Assignment.Fits st.domains a →
        (DomConstraint.minGen os r).SatisfiedBy a →
        False) ∧
    (∀ c, propMinGen st os r = .conflict c →
      ∀ a, Assignment.Fits st.domains a →
        (DomConstraint.minGen os r).SatisfiedBy a →
        ∃ l ∈ c, l.eval a = some true) := by
  refine ⟨?_, ?_, ?_⟩
  · intro l rr hrun a hfit hcons
    obtain ⟨mv, hrest⟩ := hcons
    obtain ⟨hrread, hval⟩ := hrest
    obtain ⟨o, ho, hoatt⟩ := minGen_attained hval
    unfold propMinGen at hrun
    split at hrun
    case h_1 => exact absurd hrun (by intro hc; cases hc)
    case h_2 =>
      rename_i r' k
      split at hrun
      case h_1 =>
        rename_i m_lo m_hi hlo hhi
        obtain ⟨hslotk, hmle, hmhe⟩ :=
          genValue_bounds hfit ⟨o, ho, hoatt⟩ hrread hlo hhi
        rcases firstEvent_mem
            [ narrowLo st k m_lo (negLe k (m_lo - 1) :: os.flatMap (argLoCause st))
            , narrowHi st k m_hi (posLe k m_hi :: os.flatMap (argHiCause st)) ]
            (.implied l rr) hrun with hstable | hmem
        · exact absurd hstable (by intro hc; cases hc)
        · rcases List.mem_cons.mp hmem with h1 | hrest
          · obtain ⟨hl, -⟩ := narrowLo_implied_inv (Eq.symm h1)
            subst hl
            rw [eval_negLe_iff]
            exact ⟨mv, hslotk, by omega⟩
          · rw [List.mem_singleton] at hrest
            obtain ⟨hl, -⟩ := narrowHi_implied_inv (Eq.symm hrest)
            subst hl
            rw [eval_posLe_iff]
            exact ⟨mv, hslotk, by omega⟩
      case h_2 => exact absurd hrun (by intro hc; cases hc)

  · intro c hrun a hfit hcons
    obtain ⟨mv, hrest⟩ := hcons
    obtain ⟨hrread, hval⟩ := hrest
    obtain ⟨o, ho, hoatt⟩ := minGen_attained hval
    unfold propMinGen at hrun
    split at hrun
    case h_1 => exact absurd hrun (by intro hc; cases hc)
    case h_2 =>
      rename_i r' k
      split at hrun
      case h_1 =>
        rename_i m_lo m_hi hlo hhi
        obtain ⟨hslotk, hmle, hmhe⟩ :=
          genValue_bounds hfit ⟨o, ho, hoatt⟩ hrread hlo hhi
        rcases firstEvent_mem
            [ narrowLo st k m_lo (negLe k (m_lo - 1) :: os.flatMap (argLoCause st))
            , narrowHi st k m_hi (posLe k m_hi :: os.flatMap (argHiCause st)) ]
            (.conflict c) hrun with hstable | hmem
        · exact absurd hstable (by intro hc; cases hc)
        · rcases List.mem_cons.mp hmem with h1 | hrest
          · obtain ⟨mn, mx, -, hmx, hlt, -⟩ := narrowLo_conflict_inv (Eq.symm h1)
            have := fits_max_bound hfit hmx hslotk
            omega
          · rw [List.mem_singleton] at hrest
            obtain ⟨mn, -, hmn, -, hgt, -⟩ := narrowHi_conflict_inv (Eq.symm hrest)
            have := fits_min_bound hfit hmn hslotk
            omega
      case h_2 => exact absurd hrun (by intro hc; cases hc)

  · intro c hrun a hfit hcons
    obtain ⟨mv, hrest⟩ := hcons
    obtain ⟨hrread, hval⟩ := hrest
    obtain ⟨o, ho, hoatt⟩ := minGen_attained hval
    unfold propMinGen at hrun
    split at hrun
    case h_1 => exact absurd hrun (by intro hc; cases hc)
    case h_2 =>
      rename_i r' k
      split at hrun
      case h_1 =>
        rename_i m_lo m_hi hlo hhi
        obtain ⟨hslotk, hmle, hmhe⟩ :=
          genValue_bounds hfit ⟨o, ho, hoatt⟩ hrread hlo hhi
        rcases firstEvent_mem
            [ narrowLo st k m_lo (negLe k (m_lo - 1) :: os.flatMap (argLoCause st))
            , narrowHi st k m_hi (posLe k m_hi :: os.flatMap (argHiCause st)) ]
            (.conflict c) hrun with hstable | hmem
        · exact absurd hstable (by intro hc; cases hc)
        · rcases List.mem_cons.mp hmem with h1 | hrest
          · obtain ⟨-, -, -, -, -, hcc⟩ := narrowLo_conflict_inv (Eq.symm h1)
            rw [hcc]
            exact ⟨negLe k (m_lo - 1), List.mem_cons_self,
              by rw [eval_negLe_iff]; exact ⟨mv, hslotk, by omega⟩⟩
          · rw [List.mem_singleton] at hrest
            obtain ⟨-, -, -, -, -, hcc⟩ := narrowHi_conflict_inv (Eq.symm hrest)
            rw [hcc]
            exact ⟨posLe k m_hi, List.mem_cons_self,
              by rw [eval_posLe_iff]; exact ⟨mv, hslotk, by omega⟩⟩
      case h_2 => exact absurd hrun (by intro hc; cases hc)

/-- PLAN C9c: the `maxGen` result propagator `propMaxGen` is sound:
    implied literals hold at every fitting solution of the constraint, a
    reported conflict admits no fitting solution, and every conflict
    clause carries a literal true at every fitting solution. -/
theorem propMaxGen_safe (st : State) (os : List DomIntArg) (r : DomIntArg) :
    (∀ l rr, propMaxGen st os r = .implied l rr →
      ∀ a, Assignment.Fits st.domains a →
        (DomConstraint.maxGen os r).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ c, propMaxGen st os r = .conflict c →
      ∀ a, Assignment.Fits st.domains a →
        (DomConstraint.maxGen os r).SatisfiedBy a →
        False) ∧
    (∀ c, propMaxGen st os r = .conflict c →
      ∀ a, Assignment.Fits st.domains a →
        (DomConstraint.maxGen os r).SatisfiedBy a →
        ∃ l ∈ c, l.eval a = some true) := by
  refine ⟨?_, ?_, ?_⟩
  · intro l rr hrun a hfit hcons
    obtain ⟨mv, hrest⟩ := hcons
    obtain ⟨hrread, hval⟩ := hrest
    obtain ⟨o, ho, hoatt⟩ := maxGen_attained hval
    unfold propMaxGen at hrun
    split at hrun
    case h_1 => exact absurd hrun (by intro hc; cases hc)
    case h_2 =>
      rename_i r' k
      split at hrun
      case h_1 =>
        rename_i m_lo m_hi hlo hhi
        obtain ⟨hslotk, hmle, hmhe⟩ :=
          genValue_bounds hfit ⟨o, ho, hoatt⟩ hrread hlo hhi
        rcases firstEvent_mem
            [ narrowLo st k m_lo (negLe k (m_lo - 1) :: os.flatMap (argLoCause st))
            , narrowHi st k m_hi (posLe k m_hi :: os.flatMap (argHiCause st)) ]
            (.implied l rr) hrun with hstable | hmem
        · exact absurd hstable (by intro hc; cases hc)
        · rcases List.mem_cons.mp hmem with h1 | hrest
          · obtain ⟨hl, -⟩ := narrowLo_implied_inv (Eq.symm h1)
            subst hl
            rw [eval_negLe_iff]
            exact ⟨mv, hslotk, by omega⟩
          · rw [List.mem_singleton] at hrest
            obtain ⟨hl, -⟩ := narrowHi_implied_inv (Eq.symm hrest)
            subst hl
            rw [eval_posLe_iff]
            exact ⟨mv, hslotk, by omega⟩
      case h_2 => exact absurd hrun (by intro hc; cases hc)

  · intro c hrun a hfit hcons
    obtain ⟨mv, hrest⟩ := hcons
    obtain ⟨hrread, hval⟩ := hrest
    obtain ⟨o, ho, hoatt⟩ := maxGen_attained hval
    unfold propMaxGen at hrun
    split at hrun
    case h_1 => exact absurd hrun (by intro hc; cases hc)
    case h_2 =>
      rename_i r' k
      split at hrun
      case h_1 =>
        rename_i m_lo m_hi hlo hhi
        obtain ⟨hslotk, hmle, hmhe⟩ :=
          genValue_bounds hfit ⟨o, ho, hoatt⟩ hrread hlo hhi
        rcases firstEvent_mem
            [ narrowLo st k m_lo (negLe k (m_lo - 1) :: os.flatMap (argLoCause st))
            , narrowHi st k m_hi (posLe k m_hi :: os.flatMap (argHiCause st)) ]
            (.conflict c) hrun with hstable | hmem
        · exact absurd hstable (by intro hc; cases hc)
        · rcases List.mem_cons.mp hmem with h1 | hrest
          · obtain ⟨mn, mx, -, hmx, hlt, -⟩ := narrowLo_conflict_inv (Eq.symm h1)
            have := fits_max_bound hfit hmx hslotk
            omega
          · rw [List.mem_singleton] at hrest
            obtain ⟨mn, -, hmn, -, hgt, -⟩ := narrowHi_conflict_inv (Eq.symm hrest)
            have := fits_min_bound hfit hmn hslotk
            omega
      case h_2 => exact absurd hrun (by intro hc; cases hc)

  · intro c hrun a hfit hcons
    obtain ⟨mv, hrest⟩ := hcons
    obtain ⟨hrread, hval⟩ := hrest
    obtain ⟨o, ho, hoatt⟩ := maxGen_attained hval
    unfold propMaxGen at hrun
    split at hrun
    case h_1 => exact absurd hrun (by intro hc; cases hc)
    case h_2 =>
      rename_i r' k
      split at hrun
      case h_1 =>
        rename_i m_lo m_hi hlo hhi
        obtain ⟨hslotk, hmle, hmhe⟩ :=
          genValue_bounds hfit ⟨o, ho, hoatt⟩ hrread hlo hhi
        rcases firstEvent_mem
            [ narrowLo st k m_lo (negLe k (m_lo - 1) :: os.flatMap (argLoCause st))
            , narrowHi st k m_hi (posLe k m_hi :: os.flatMap (argHiCause st)) ]
            (.conflict c) hrun with hstable | hmem
        · exact absurd hstable (by intro hc; cases hc)
        · rcases List.mem_cons.mp hmem with h1 | hrest
          · obtain ⟨-, -, -, -, -, hcc⟩ := narrowLo_conflict_inv (Eq.symm h1)
            rw [hcc]
            exact ⟨negLe k (m_lo - 1), List.mem_cons_self,
              by rw [eval_negLe_iff]; exact ⟨mv, hslotk, by omega⟩⟩
          · rw [List.mem_singleton] at hrest
            obtain ⟨-, -, -, -, -, hcc⟩ := narrowHi_conflict_inv (Eq.symm hrest)
            rw [hcc]
            exact ⟨posLe k m_hi, List.mem_cons_self,
              by rw [eval_posLe_iff]; exact ⟨mv, hslotk, by omega⟩⟩
      case h_2 => exact absurd hrun (by intro hc; cases hc)

/-- PLAN C9c: the state-free reason validity of `propMinGen` — every
    emitted nogood is entailed by the constraint alone (the attained
    operand argument; no Fits premise). -/
theorem propMinGen_reason_valid
    {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {st : State} {os : List DomIntArg} {r : DomIntArg} {l : Literal} {rr : Reason}
    (hprob : ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
      (DomConstraint.minGen os r).SatisfiedBy a)
    (hrun : propMinGen st os r = .implied l rr) :
    Reason.Valid problem DomConstraint.SatisfiedBy rr l ∧
      (∀ q ∈ rr.clause, q = q.norm) := by
  unfold propMinGen at hrun
  split at hrun
  case h_1 => exact absurd hrun (by intro hc; cases hc)
  case h_2 =>
    rename_i r' k
    split at hrun
    case h_1 =>
      rename_i m_lo m_hi hlo hhi
      have hcausesLo : ∀ q ∈ os.flatMap (argLoCause st), q = q.norm :=
        clauseCanonical_flatMap (fun o _ => argLoCause_canonical st o)
      have hcausesHi : ∀ q ∈ os.flatMap (argHiCause st), q = q.norm :=
        clauseCanonical_flatMap (fun o _ => argHiCause_canonical st o)
      rcases firstEvent_mem
          [ narrowLo st k m_lo (negLe k (m_lo - 1) :: os.flatMap (argLoCause st))
          , narrowHi st k m_hi (posLe k m_hi :: os.flatMap (argHiCause st)) ]
          (.implied l rr) hrun with hstable | hmem
      · exact absurd hstable (by intro hc; cases hc)
      · rcases List.mem_cons.mp hmem with h1 | hrest
        · obtain ⟨hl, hrw⟩ := narrowLo_implied_inv (Eq.symm h1)
          subst hl
          subst hrw
          refine ⟨⟨?_, decide_eq_true_eq.mpr List.mem_cons_self⟩, ?_⟩
          · intro a hsol
            obtain ⟨mv, hrest2⟩ := hprob a hsol
            obtain ⟨hrread, hval⟩ := hrest2
            obtain ⟨o, ho, hoatt⟩ := minGen_attained hval
            exact propGen_lo_nogood_true ⟨o, ho, hoatt⟩ hrread hlo
          · intro q hq
            rcases List.mem_cons.mp hq with rfl | hq
            · exact negLe_norm _ _
            · exact hcausesLo q hq
        · rw [List.mem_singleton] at hrest
          obtain ⟨hl, hrw⟩ := narrowHi_implied_inv (Eq.symm hrest)
          subst hl
          subst hrw
          refine ⟨⟨?_, decide_eq_true_eq.mpr List.mem_cons_self⟩, ?_⟩
          · intro a hsol
            obtain ⟨mv, hrest2⟩ := hprob a hsol
            obtain ⟨hrread, hval⟩ := hrest2
            obtain ⟨o, ho, hoatt⟩ := minGen_attained hval
            exact propGen_hi_nogood_true ⟨o, ho, hoatt⟩ hrread hhi
          · intro q hq
            rcases List.mem_cons.mp hq with rfl | hq
            · exact posLe_norm _ _
            · exact hcausesHi q hq
    case h_2 => exact absurd hrun (by intro hc; cases hc)

/-- PLAN C9c: the state-free reason validity of `propMaxGen` — every
    emitted nogood is entailed by the constraint alone (the attained
    operand argument; no Fits premise). -/
theorem propMaxGen_reason_valid
    {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {st : State} {os : List DomIntArg} {r : DomIntArg} {l : Literal} {rr : Reason}
    (hprob : ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
      (DomConstraint.maxGen os r).SatisfiedBy a)
    (hrun : propMaxGen st os r = .implied l rr) :
    Reason.Valid problem DomConstraint.SatisfiedBy rr l ∧
      (∀ q ∈ rr.clause, q = q.norm) := by
  unfold propMaxGen at hrun
  split at hrun
  case h_1 => exact absurd hrun (by intro hc; cases hc)
  case h_2 =>
    rename_i r' k
    split at hrun
    case h_1 =>
      rename_i m_lo m_hi hlo hhi
      have hcausesLo : ∀ q ∈ os.flatMap (argLoCause st), q = q.norm :=
        clauseCanonical_flatMap (fun o _ => argLoCause_canonical st o)
      have hcausesHi : ∀ q ∈ os.flatMap (argHiCause st), q = q.norm :=
        clauseCanonical_flatMap (fun o _ => argHiCause_canonical st o)
      rcases firstEvent_mem
          [ narrowLo st k m_lo (negLe k (m_lo - 1) :: os.flatMap (argLoCause st))
          , narrowHi st k m_hi (posLe k m_hi :: os.flatMap (argHiCause st)) ]
          (.implied l rr) hrun with hstable | hmem
      · exact absurd hstable (by intro hc; cases hc)
      · rcases List.mem_cons.mp hmem with h1 | hrest
        · obtain ⟨hl, hrw⟩ := narrowLo_implied_inv (Eq.symm h1)
          subst hl
          subst hrw
          refine ⟨⟨?_, decide_eq_true_eq.mpr List.mem_cons_self⟩, ?_⟩
          · intro a hsol
            obtain ⟨mv, hrest2⟩ := hprob a hsol
            obtain ⟨hrread, hval⟩ := hrest2
            obtain ⟨o, ho, hoatt⟩ := maxGen_attained hval
            exact propGen_lo_nogood_true ⟨o, ho, hoatt⟩ hrread hlo
          · intro q hq
            rcases List.mem_cons.mp hq with rfl | hq
            · exact negLe_norm _ _
            · exact hcausesLo q hq
        · rw [List.mem_singleton] at hrest
          obtain ⟨hl, hrw⟩ := narrowHi_implied_inv (Eq.symm hrest)
          subst hl
          subst hrw
          refine ⟨⟨?_, decide_eq_true_eq.mpr List.mem_cons_self⟩, ?_⟩
          · intro a hsol
            obtain ⟨mv, hrest2⟩ := hprob a hsol
            obtain ⟨hrread, hval⟩ := hrest2
            obtain ⟨o, ho, hoatt⟩ := maxGen_attained hval
            exact propGen_hi_nogood_true ⟨o, ho, hoatt⟩ hrread hhi
          · intro q hq
            rcases List.mem_cons.mp hq with rfl | hq
            · exact posLe_norm _ _
            · exact hcausesHi q hq
    case h_2 => exact absurd hrun (by intro hc; cases hc)

/-- PLAN C9c: the conflict entitlement of `propMinGen` at a solution of
    the constraint. -/
theorem propMinGen_entitled
    {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {st : State} {os : List DomIntArg} {r : DomIntArg} {c : Clause}
    (hprob : ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
      (DomConstraint.minGen os r).SatisfiedBy a)
    (hrun : propMinGen st os r = .conflict c)
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ c, l.eval a = some true := by
  unfold propMinGen at hrun
  split at hrun
  case h_1 => exact absurd hrun (by intro hc; cases hc)
  case h_2 =>
    rename_i r' k
    split at hrun
    case h_1 =>
      rename_i m_lo m_hi hlo hhi
      rcases firstEvent_mem
          [ narrowLo st k m_lo (negLe k (m_lo - 1) :: os.flatMap (argLoCause st))
          , narrowHi st k m_hi (posLe k m_hi :: os.flatMap (argHiCause st)) ]
          (.conflict c) hrun with hstable | hmem
      · exact absurd hstable (by intro hc; cases hc)
      · obtain ⟨mv, hrest2⟩ := hprob a ha
        obtain ⟨hrread, hval⟩ := hrest2
        obtain ⟨o, ho, hoatt⟩ := minGen_attained hval
        rcases List.mem_cons.mp hmem with h1 | hrest
        · obtain ⟨-, -, -, -, -, hcc⟩ := narrowLo_conflict_inv (Eq.symm h1)
          rw [hcc]
          exact propGen_lo_nogood_true ⟨o, ho, hoatt⟩ hrread hlo
        · rw [List.mem_singleton] at hrest
          obtain ⟨-, -, -, -, -, hcc⟩ := narrowHi_conflict_inv (Eq.symm hrest)
          rw [hcc]
          exact propGen_hi_nogood_true ⟨o, ho, hoatt⟩ hrread hhi
    case h_2 => exact absurd hrun (by intro hc; cases hc)

/-- PLAN C9c: the conflict entitlement of `propMaxGen` at a solution of
    the constraint. -/
theorem propMaxGen_entitled
    {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {st : State} {os : List DomIntArg} {r : DomIntArg} {c : Clause}
    (hprob : ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
      (DomConstraint.maxGen os r).SatisfiedBy a)
    (hrun : propMaxGen st os r = .conflict c)
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ c, l.eval a = some true := by
  unfold propMaxGen at hrun
  split at hrun
  case h_1 => exact absurd hrun (by intro hc; cases hc)
  case h_2 =>
    rename_i r' k
    split at hrun
    case h_1 =>
      rename_i m_lo m_hi hlo hhi
      rcases firstEvent_mem
          [ narrowLo st k m_lo (negLe k (m_lo - 1) :: os.flatMap (argLoCause st))
          , narrowHi st k m_hi (posLe k m_hi :: os.flatMap (argHiCause st)) ]
          (.conflict c) hrun with hstable | hmem
      · exact absurd hstable (by intro hc; cases hc)
      · obtain ⟨mv, hrest2⟩ := hprob a ha
        obtain ⟨hrread, hval⟩ := hrest2
        obtain ⟨o, ho, hoatt⟩ := maxGen_attained hval
        rcases List.mem_cons.mp hmem with h1 | hrest
        · obtain ⟨-, -, -, -, -, hcc⟩ := narrowLo_conflict_inv (Eq.symm h1)
          rw [hcc]
          exact propGen_lo_nogood_true ⟨o, ho, hoatt⟩ hrread hlo
        · rw [List.mem_singleton] at hrest
          obtain ⟨-, -, -, -, -, hcc⟩ := narrowHi_conflict_inv (Eq.symm hrest)
          rw [hcc]
          exact propGen_hi_nogood_true ⟨o, ho, hoatt⟩ hrread hhi
    case h_2 => exact absurd hrun (by intro hc; cases hc)

end LeanFzn.Solver.Propagation

namespace LeanFzn.Solver.Propagation

/-! ## 7. The documented gap of the strong corner arm -/

/-- **THE INT-GUARD GAP (kernel-checked).** The strong corner bound
    `result ≤ min of the operands' STATE upper bounds` (the `propMin`
    arm shape) is NOT sound for the array families: `minValue` ignores
    a non-integer element after the integer prefix, so with the operand
    reads `[.int 5, .bool true]` the constraint holds with result `5`
    although the second operand's state upper bound is `1`.  Closing
    this gap needs an int-typing gate on the operand slots (every
    `.minGen`/`.maxGen` operand slot's problem domain holds only
    integers), which this development does not add; the registered
    `propMinGen`/`propMaxGen` therefore use only the two attained-value
    arms. -/
theorem minGen_hi_corner_gap :
    (DomConstraint.minGen [.slot 0, .slot 1] (.slot 2)).SatisfiedBy
        [Value.int 5, Value.bool true, Value.int 5] ∧
      domMaxI (Dom.ofList [Value.bool true] : Domain) = some 1 ∧
      slotInt [Value.int 5, Value.bool true, Value.int 5] 2 = some 5 ∧
      (1 : Int) < 5 :=
  ⟨⟨5, rfl, rfl⟩, rfl, rfl, by omega⟩

end LeanFzn.Solver.Propagation

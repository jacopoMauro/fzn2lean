/-
Purpose: LinearExt propagators: bounds definitions and their required entailment proofs.
Dependencies: LeanFzn.Engine.Props.Linear
DAG: shared propagator foundations -> LeanFzn.Engine.Props.LinearExt.Bounds.
-/
import LeanFzn.Engine.Props.Linear

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

/-! ## Maximum-side arithmetic

`linTermMin` bounds one term from below by its contribution at the lower
end.  The mirror image uses the upper end.  For a coefficient `c ≥ 0` the
maximum contribution is `c * hi`; for `c < 0` it is `c * lo`.
-/

def linTermMax (c lo hi : Int) : Int := if 0 ≤ c then c * hi else c * lo

def LinTerm.max (t : LinTerm) : Int := linTermMax t.c t.lo t.hi

def linTotalMax : List LinTerm → Int
  | [] => 0
  | t :: ts => linTotalMax ts + t.max

/-- Literal asserting that the term's contribution exceeds its maximum:
`x > hi` for `c ≥ 0` and `x < lo` for `c < 0`.  Its negation is false on
any value inside the term's bounds. -/
def linMaxNegLit (s : Nat) (c lo hi : Int) : Literal :=
  if 0 ≤ c then negLe s hi else posLe s (lo - 1)

def linMaxLits (terms : List LinTerm) : List Literal :=
  terms.map fun t => linMaxNegLit t.s t.c t.lo t.hi

def linOtherMaxLits (terms : List LinTerm) (i : Nat) : List Literal :=
  linMaxLits (terms.eraseIdx i)

def linOtherMax (terms : List LinTerm) (i : Nat) : Int :=
  linTotalMax (terms.eraseIdx i)

theorem linTotalMax_eq_eraseIdx_add {terms : List LinTerm} {i : Nat} {t : LinTerm}
    (h : terms[i]? = some t) :
    linTotalMax terms = linTotalMax (terms.eraseIdx i) + t.max := by
  induction terms generalizing i with
  | nil => simp at h
  | cons u us ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h
          subst t
          simp [linTotalMax]
      | succ k =>
          have hk : us[k]? = some t := by simpa using h
          have ih' := ih hk
          simp only [List.eraseIdx_cons_succ]
          rw [linTotalMax, linTotalMax, ih']
          omega

theorem linMaxNegLit_false_bound {t : LinTerm} {a : Assignment}
    (h : (linMaxNegLit t.s t.c t.lo t.hi).eval a = some false) :
    ∃ x, slotInt a t.s = some x ∧ t.c * x ≤ t.max := by
  by_cases hc : 0 ≤ t.c
  · rw [linMaxNegLit, if_pos hc] at h
    rw [eval_negLe_false_iff] at h
    obtain ⟨x, hx, hle⟩ := h
    refine ⟨x, hx, ?_⟩
    simp only [LinTerm.max, linTermMax, if_pos hc]
    exact Int.mul_le_mul_of_nonneg_left hle hc
  · have hc' : t.c ≤ 0 := by omega
    rw [linMaxNegLit, if_neg hc] at h
    rw [eval_posLe_false_iff] at h
    obtain ⟨x, hx, hlt⟩ := h
    refine ⟨x, hx, ?_⟩
    have hle : t.lo ≤ x := by omega
    simp only [LinTerm.max, linTermMax, if_neg hc]
    exact Int.mul_le_mul_of_nonpos_left hc' hle

theorem linDotSum_le_linTotalMax (terms : List LinTerm) (a : Assignment)
    (hfalse : ∀ l ∈ linMaxLits terms, l.eval a = some false) :
    linDotSum terms a ≤ linTotalMax terms := by
  induction terms with
  | nil => simp [linTotalMax, linDotSum]
  | cons t ts ih =>
      have hhead : (linMaxNegLit t.s t.c t.lo t.hi).eval a = some false :=
        hfalse _ (by simp [linMaxLits])
      have htail : ∀ l ∈ linMaxLits ts, l.eval a = some false := by
        intro l hl
        have hl' : l ∈ linMaxLits (t :: ts) := by
          simp only [linMaxLits, List.map_cons, List.mem_cons]
          exact Or.inr hl
        exact hfalse l hl'
      obtain ⟨x, hx, hbound⟩ := linMaxNegLit_false_bound hhead
      have iht := ih htail
      have hsum : linDotSum ts a + t.c * x ≤ linTotalMax ts + t.max :=
        Int.add_le_add iht hbound
      simpa [linTotalMax, linDotSum, hx] using hsum

theorem linMaxNegLit_eval_false_of_not_true {t : LinTerm} {a : Assignment} {x : Int}
    (hx : slotInt a t.s = some x)
    (h : (linMaxNegLit t.s t.c t.lo t.hi).eval a ≠ some true) :
    (linMaxNegLit t.s t.c t.lo t.hi).eval a = some false := by
  by_cases hc : 0 ≤ t.c
  · rw [linMaxNegLit, if_pos hc]
    exact negLe_eval_false_of_not_true hx (by rwa [linMaxNegLit, if_pos hc] at h)
  · rw [linMaxNegLit, if_neg hc]
    exact posLe_eval_false_of_not_true hx (by rwa [linMaxNegLit, if_neg hc] at h)

theorem linMaxNegLit_evalLit_false {d : DomC} (hWF : d.WF)
    {s : Nat} {c lo hi : Int} (hlo : d.lo? = some lo) (hhi : d.hi? = some hi) :
    d.evalLit (linMaxNegLit s c lo hi) = some false := by
  have hle := DomC.lo?_le_hi? d hWF hlo hhi
  by_cases hc : 0 ≤ c
  · rw [linMaxNegLit, if_pos hc]
    simp only [DomC.evalLit, negLe, hlo, hhi, Bool.false_eq_true, ↓reduceIte]
    rw [if_neg (by omega), if_pos (by omega)]
  · rw [linMaxNegLit, if_neg hc]
    simp only [DomC.evalLit, posLe, hlo, hhi, ↓reduceIte]
    rw [if_neg (by omega), if_pos (by omega)]

theorem atomSlot_linMaxNegLit (s : Nat) (c lo hi : Int) :
    atomSlot (linMaxNegLit s c lo hi).atom = s := by
  unfold linMaxNegLit
  split <;> rfl

/-! ## Lower-bound propagation for an equality

Given `dot ≥ b`, each term is bounded below by `b - otherMax`.
-/

/-- If `c > 0`, values below `ceil((b-other)/c)` make the term contribution
strictly smaller than `b - other`. -/
theorem linPruneGePos_mul_lt {c newLo x b other : Int}
    (hpos : 0 < c) (hnew : newLo = -((other - b) / c))
    (hx : x ≤ newLo - 1) :
    c * x < b - other := by
  have hstep : c * x ≤ c * (newLo - 1) :=
    Int.mul_le_mul_of_nonneg_left (by omega) (Int.le_of_lt hpos)
  have heq : c * (newLo - 1) = -(((other - b) / c + 1) * c) := by
    have h2 : newLo - 1 = -(((other - b) / c) + 1) := by
      rw [hnew]
      omega
    rw [h2, Int.mul_neg, Int.mul_comm c (((other - b) / c) + 1)]
  have hlt := Int.lt_ediv_add_one_mul_self (other - b) hpos
  rw [heq] at hstep
  have hneg : -(((other - b) / c + 1) * c) < -(other - b) := by omega
  have hfin : -(other - b) = b - other := by omega
  rw [hfin] at hneg
  exact Int.lt_of_le_of_lt hstep hneg

/-- If `c < 0`, values above `(b-other)/c` make the term contribution
strictly smaller than `b - other`. -/
theorem linPruneGeNeg_mul_lt {c newHi x b other : Int}
    (hneg : c < 0) (hnew : newHi = (b - other) / c)
    (hx : newHi < x) :
    c * x < b - other := by
  have hx1 : newHi + 1 ≤ x := by omega
  have hstep : c * x ≤ c * (newHi + 1) :=
    Int.mul_le_mul_of_nonpos_left (Int.le_of_lt hneg) hx1
  have heq : c * (newHi + 1) = (b - other) / c * c + c := by
    rw [hnew, Int.mul_add, Int.mul_one, Int.mul_comm]
  have hle : (b - other) / c * c ≤ b - other :=
    Int.ediv_mul_le (b - other) (by omega)
  have hle' : c * (newHi + 1) ≤ b - other + c := by
    rw [heq]
    exact Int.add_le_add_right hle c
  have hlt : b - other + c < b - other := by omega
  exact Int.lt_of_le_of_lt hstep (Int.lt_of_le_of_lt hle' hlt)

/-- For `c > 0`, the lower bound derived from `b ≤ totalMax` stays below
the current upper bound. -/
theorem linPruneGePos_newLo_le_hi {terms : List LinTerm} {i : Nat} {t : LinTerm}
    {b : Int} (hterm : terms[i]? = some t) (hpos : 0 < t.c)
    (hb : b ≤ linTotalMax terms) :
    -((linOtherMax terms i - b) / t.c) ≤ t.hi := by
  have hsplit := linTotalMax_eq_eraseIdx_add hterm
  have hmax : t.max = t.c * t.hi := by
    have hc : 0 ≤ t.c := Int.le_of_lt hpos
    simp [LinTerm.max, linTermMax, hc]
  have hmul : b - linOtherMax terms i ≤ t.c * t.hi := by
    unfold linOtherMax
    omega
  have hq : -(t.hi) ≤ (linOtherMax terms i - b) / t.c := by
    rw [Int.le_ediv_iff_mul_le hpos]
    have hm : -(t.hi) * t.c = -(t.c * t.hi) := by
      rw [Int.neg_mul, Int.mul_comm t.hi t.c]
    rw [hm]
    omega
  omega

/-- For `c < 0`, the upper bound derived from `b ≤ totalMax` stays above
the current lower bound. -/
theorem linPruneGeNeg_newHi_ge_lo {terms : List LinTerm} {i : Nat} {t : LinTerm}
    {b : Int} (hterm : terms[i]? = some t) (hneg : t.c < 0)
    (hb : b ≤ linTotalMax terms) :
    t.lo ≤ (b - linOtherMax terms i) / t.c := by
  have hsplit := linTotalMax_eq_eraseIdx_add hterm
  have hmax : t.max = t.c * t.lo := by
    have hc : ¬ 0 ≤ t.c := by omega
    simp [LinTerm.max, linTermMax, hc]
  have hmul : b - linOtherMax terms i ≤ t.c * t.lo := by
    unfold linOtherMax
    omega
  have hm : 0 < -t.c := by omega
  have hq : (b - linOtherMax terms i) / (-t.c) ≤ -t.lo := by
    rw [Int.ediv_le_iff_le_mul hm]
    have hmul' : b - linOtherMax terms i ≤ (-t.lo) * (-t.c) := by
      have heq : (-t.lo) * (-t.c) = t.c * t.lo := by
        rw [Int.neg_mul_neg, Int.mul_comm]
      rw [heq]
      exact hmul
    omega
  have hdiv : (b - linOtherMax terms i) / t.c =
      -((b - linOtherMax terms i) / (-t.c)) := by
    have h := Int.ediv_neg (b - linOtherMax terms i) (-t.c)
    have hnegneg : -(-t.c) = t.c := by omega
    rw [hnegneg] at h
    exact h
  rw [hdiv]
  omega

def linPrunesGe (terms : List LinTerm) (b : Int) : List (Literal × Clause) :=
  (List.range terms.length).filterMap fun i =>
    match terms[i]? with
    | none => none
    | some t =>
        let otherMax := linOtherMax terms i
        if 0 < t.c then
          let newLo := -((otherMax - b) / t.c)
          if t.lo < newLo then
            some (negLe t.s (newLo - 1), linOtherMaxLits terms i ++ [negLe t.s (newLo - 1)])
          else none
        else if t.c < 0 then
          let newHi := (b - otherMax) / t.c
          if newHi < t.hi then
            some (posLe t.s newHi, linOtherMaxLits terms i ++ [posLe t.s newHi])
          else none
        else none

/-- Runtime twin of `linPrunesGe` parameterised by a precomputed term array
and total, so callers can share both across several plans. -/
def linPrunesGeFastAt (terms : List LinTerm) (arr : Array LinTerm) (total : Int)
    (b : Int) : List (Literal × Clause) :=
  (List.range terms.length).filterMap fun i =>
    match arr[i]? with
    | none => none
    | some t =>
        let otherMax := total - t.max
        if 0 < t.c then
          let newLo := -((otherMax - b) / t.c)
          if t.lo < newLo then
            some (negLe t.s (newLo - 1), linOtherMaxLits terms i ++ [negLe t.s (newLo - 1)])
          else none
        else if t.c < 0 then
          let newHi := (b - otherMax) / t.c
          if newHi < t.hi then
            some (posLe t.s newHi, linOtherMaxLits terms i ++ [posLe t.s newHi])
          else none
        else none

/-- Runtime twin of `linPrunesGe` (see `linPrunesGeFastAt`). -/
def linPrunesGeFast (terms : List LinTerm) (b : Int) : List (Literal × Clause) :=
  linPrunesGeFastAt terms terms.toArray (linTotalMax terms) b

@[csimp] theorem linPrunesGe_eq_fast : @linPrunesGe = @linPrunesGeFast := by
  funext terms b
  unfold linPrunesGe linPrunesGeFast linPrunesGeFastAt
  congr 1
  funext i
  simp only [List.getElem?_toArray]
  cases h : terms[i]? with
  | none => rfl
  | some t =>
      have hsum := linTotalMax_eq_eraseIdx_add h
      have ho : linOtherMax terms i = linTotalMax terms - t.max := by
        unfold linOtherMax; omega
      simp only [ho]

theorem linPrunesGe_mem {terms : List LinTerm} {b : Int} {l : Literal} {reason : Clause}
    (h : (l, reason) ∈ linPrunesGe terms b) :
    ∃ i t, terms[i]? = some t ∧
      ((0 < t.c ∧
          l = negLe t.s (-((linOtherMax terms i - b) / t.c) - 1) ∧
          t.lo < -((linOtherMax terms i - b) / t.c) ∧
          reason = linOtherMaxLits terms i ++ [l]) ∨
        (¬ 0 < t.c ∧ t.c < 0 ∧
          l = posLe t.s ((b - linOtherMax terms i) / t.c) ∧
          ((b - linOtherMax terms i) / t.c) < t.hi ∧
          reason = linOtherMaxLits terms i ++ [l])) := by
  unfold linPrunesGe at h
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
          have hpair : (negLe t.s (-((linOtherMax terms i - b) / t.c) - 1),
              linOtherMaxLits terms i ++
                [negLe t.s (-((linOtherMax terms i - b) / t.c) - 1)]) =
              (l, reason) := Option.some.inj hf
          have hl : l = negLe t.s (-((linOtherMax terms i - b) / t.c) - 1) :=
            (congrArg Prod.fst hpair).symm
          have hr : reason = linOtherMaxLits terms i ++
              [negLe t.s (-((linOtherMax terms i - b) / t.c) - 1)] :=
            (congrArg Prod.snd hpair).symm
          rw [← hl] at hr
          exact ⟨i, t, hterm, Or.inl ⟨hpos, hl, hlt, hr⟩⟩
        · simp at hf
      · rename_i hnotpos
        split at hf
        · rename_i hneg
          split at hf
          · rename_i hlt
            have hpair : (posLe t.s ((b - linOtherMax terms i) / t.c),
                linOtherMaxLits terms i ++
                  [posLe t.s ((b - linOtherMax terms i) / t.c)]) =
                (l, reason) := Option.some.inj hf
            have hl : l = posLe t.s ((b - linOtherMax terms i) / t.c) :=
              (congrArg Prod.fst hpair).symm
            have hr : reason = linOtherMaxLits terms i ++
                [posLe t.s ((b - linOtherMax terms i) / t.c)] :=
              (congrArg Prod.snd hpair).symm
            rw [← hl] at hr
            exact ⟨i, t, hterm, Or.inr ⟨hnotpos, hneg, hl, hlt, hr⟩⟩
          · simp at hf
        · simp at hf

/-! ## Fixed-domain facts for disequality literals

The `linNe` propagator explains itself with `posNe` singleton negations.
On a view domain whose `lo?`/`hi?` coincide, such a literal is definitely
false; on a domain that does not already fix the value it is undefined.
-/

theorem DomC.evalLit_posNe_intKind {d : DomC} (hWF : d.WF)
    (hk : d.intKindB = true) {s : Nat} {lo hi : Int}
    (hlo : d.lo? = some lo) (hhi : d.hi? = some hi) (heq : lo = hi) :
    d.evalLit (posNe s lo) = some false := by
  cases d with
  | bool _ => simp [DomC.intKindB] at hk
  | bounds lo' hi' =>
      simp only [DomC.lo?, DomC.hi?] at hlo hhi
      split at hlo <;> simp at hlo
      split at hhi <;> simp at hhi
      rw [hlo, hhi]
      have hbeq : (lo == hi) = true := by rw [beq_iff_eq]; exact heq
      have hfix : (DomC.bounds lo hi).fixedValue.isSome = true := by
        simp [DomC.fixedValue, hbeq]
      have hmiv : (DomC.bounds lo hi).memIntView lo = true := by
        simp [DomC.memIntView, DomC.mem, heq]
      simp [posNe, DomC.evalLit, hfix, hmiv]
  | bitset lo' words =>
      have hm := bitset_mem_int_of_lo?_eq hlo
      have hmiv := DomC.memIntView_true_of_mem hm (v := lo) rfl
      have hbeq : (lo == hi) = true := by rw [beq_iff_eq]; exact heq
      have hfix : (DomC.bitset lo' words).fixedValue.isSome = true := by
        simp [DomC.fixedValue, hlo, hhi, hbeq]
      simp [posNe, DomC.evalLit, hfix, hmiv]
  | boundsHoles lo' hi' holes =>
      have hhi' : (DomC.boundsHoles lo' hi' holes).hi? = some lo := by
        rw [← heq] at hhi
        exact hhi
      have hm := boundsHoles_mem_int_of_lo?_hi?_eq hWF hlo hhi'
      have hmiv := DomC.memIntView_true_of_mem hm (v := lo) rfl
      have hbeq : (lo == hi) = true := by rw [beq_iff_eq]; exact heq
      have hfix : (DomC.boundsHoles lo' hi' holes).fixedValue.isSome = true := by
        simp [DomC.fixedValue, hlo, hhi, hbeq]
      simp [posNe, DomC.evalLit, hfix, hmiv]
  | sparse values =>
      have hhead : arrayHead? values = some lo := by
        simpa [DomC.lo?] using hlo
      have hlast : arrayLast? values = some hi := by
        simpa [DomC.hi?] using hhi
      have hmemlo : lo ∈ values.toList := by
        obtain ⟨hpos, hx0⟩ := arrayHead?_eq_some hhead
        rw [← hx0]
        exact Array.mem_toList_iff.mpr
          (Array.mem_of_getElem? (Array.getElem?_eq_getElem hpos))
      have hm : (DomC.sparse values).mem (.int lo) = true := by
        simp only [DomC.mem]
        exact (memHoleRange_eq_true_iff hWF).mpr hmemlo
      have hmiv := DomC.memIntView_true_of_mem hm (v := lo) rfl
      have hbeq : (lo == hi) = true := by rw [beq_iff_eq]; exact heq
      have hfix : (DomC.sparse values).fixedValue.isSome = true := by
        simp only [DomC.fixedValue, hhead, hlast]
        rw [hbeq]
        rfl
      simp [posNe, DomC.evalLit, hfix, hmiv]

/-! ## Assignment-level reasons for the inequality passes -/

theorem linPrunes_reason_satisfied {terms : List LinTerm} {b : Int} {a : Assignment}
    (hint : ∀ t ∈ terms, ∃ x, slotInt a t.s = some x)
    (hle : linDotSum terms a ≤ b)
    {l : Literal} {reason : Clause}
    (hprune : (l, reason) ∈ linPrunes terms b) :
    reason.SatisfiedBy a := by
  apply Classical.byContradiction
  intro hno
  have hnotTrue : ∀ q ∈ reason, q.eval a ≠ some true := by
    intro q hq htrue
    exact hno ⟨q, hq, htrue⟩
  obtain ⟨i, t, hterm, hbranch⟩ := linPrunes_mem hprune
  have ht : t ∈ terms := by
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hterm
    exact List.mem_iff_getElem.mpr ⟨i, hlt, hget⟩
  have hotherFalse : ∀ q ∈ linOtherLits terms i, q.eval a = some false := by
    intro q hq
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (by
      simpa [linOtherLits, linConflictLits] using hq)
    have hu' : u ∈ terms := List.mem_of_mem_eraseIdx hu
    obtain ⟨x, hx⟩ := hint u hu'
    have hqOther : linMinNegLit u.s u.c u.lo u.hi ∈ linOtherLits terms i :=
      List.mem_map.mpr ⟨u, hu, rfl⟩
    have hqReason : linMinNegLit u.s u.c u.lo u.hi ∈ reason := by
      rcases hbranch with ⟨_, _, _, hreason⟩ | ⟨_, _, _, _, hreason⟩
      · rw [hreason]; exact List.mem_append_left _ hqOther
      · rw [hreason]; exact List.mem_append_left _ hqOther
    exact linMinNegLit_eval_false_of_not_true hx (hnotTrue _ hqReason)
  have hother := linTotalMin_le_linDotSum (terms.eraseIdx i) a (by
    intro q hq
    exact hotherFalse q (by simpa [linOtherLits] using hq))
  obtain ⟨xt, hxt⟩ := hint t ht
  have hsplit := linDotSum_eq_eraseIdx_add (terms := terms) (i := i) (t := t)
    hterm hxt
  rcases hbranch with ⟨hpos, hl, hlt, hreason⟩ | ⟨hnotpos, hneg, hl, hlt, hreason⟩
  · have hqReason : l ∈ reason := by
      rw [hreason]; exact List.mem_append_right _ (by simp)
    have hpl : (posLe t.s ((b - linOtherMin terms i) / t.c)).eval a = some false :=
      posLe_eval_false_of_not_true (k := (b - linOtherMin terms i) / t.c) hxt (by
        rw [← hl]; exact hnotTrue _ hqReason)
    obtain ⟨x, hx, hnle⟩ := (eval_posLe_false_iff a t.s
      ((b - linOtherMin terms i) / t.c)).mp hpl
    have hxle : (b - linOtherMin terms i) / t.c < x := by omega
    have hmul := linPrunePos_newHi_lt_mul (c := t.c)
      (newHi := (b - linOtherMin terms i) / t.c) (x := x)
      (b := b) (other := linOtherMin terms i) hpos rfl hxle
    have hxxt : x = xt := by
      rw [hxt] at hx
      exact (Option.some.inj hx.symm)
    have hbig : b < linDotSum (terms.eraseIdx i) a + t.c * x := by
      unfold linOtherMin at hmul
      omega
    have hsum : linDotSum terms a = linDotSum (terms.eraseIdx i) a + t.c * x := by
      rw [hxxt]; exact hsplit
    rw [hsum] at hle
    omega
  · have hqReason : l ∈ reason := by
      rw [hreason]; exact List.mem_append_right _ (by simp)
    have hnl : (negLe t.s (-((b - linOtherMin terms i) / (-t.c)) - 1)).eval a =
        some false :=
      negLe_eval_false_of_not_true
        (k := -((b - linOtherMin terms i) / (-t.c)) - 1) hxt (by
          rw [← hl]; exact hnotTrue _ hqReason)
    obtain ⟨x, hx, hxle⟩ := (eval_negLe_false_iff a t.s
      (-((b - linOtherMin terms i) / (-t.c)) - 1)).mp hnl
    have hmul := linPruneNeg_mul_lt (c := t.c)
      (newLo := -((b - linOtherMin terms i) / (-t.c))) (x := x)
      (b := b) (other := linOtherMin terms i) hneg rfl hxle
    have hxxt : x = xt := by
      rw [hxt] at hx
      exact (Option.some.inj hx.symm)
    have hbig : b < linDotSum (terms.eraseIdx i) a + t.c * x := by
      unfold linOtherMin at hmul
      omega
    have hsum : linDotSum terms a = linDotSum (terms.eraseIdx i) a + t.c * x := by
      rw [hxxt]; exact hsplit
    rw [hsum] at hle
    omega

theorem linPrunesGe_reason_satisfied {terms : List LinTerm} {b : Int} {a : Assignment}
    (hint : ∀ t ∈ terms, ∃ x, slotInt a t.s = some x)
    (hge : b ≤ linDotSum terms a)
    {l : Literal} {reason : Clause}
    (hprune : (l, reason) ∈ linPrunesGe terms b) :
    reason.SatisfiedBy a := by
  apply Classical.byContradiction
  intro hno
  have hnotTrue : ∀ q ∈ reason, q.eval a ≠ some true := by
    intro q hq htrue
    exact hno ⟨q, hq, htrue⟩
  obtain ⟨i, t, hterm, hbranch⟩ := linPrunesGe_mem hprune
  have ht : t ∈ terms := by
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hterm
    exact List.mem_iff_getElem.mpr ⟨i, hlt, hget⟩
  have hotherFalse : ∀ q ∈ linOtherMaxLits terms i, q.eval a = some false := by
    intro q hq
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (by
      simpa [linOtherMaxLits, linMaxLits] using hq)
    have hu' : u ∈ terms := List.mem_of_mem_eraseIdx hu
    obtain ⟨x, hx⟩ := hint u hu'
    have hqOther : linMaxNegLit u.s u.c u.lo u.hi ∈ linOtherMaxLits terms i :=
      List.mem_map.mpr ⟨u, hu, rfl⟩
    have hqReason : linMaxNegLit u.s u.c u.lo u.hi ∈ reason := by
      rcases hbranch with ⟨_, _, _, hreason⟩ | ⟨_, _, _, _, hreason⟩
      · rw [hreason]; exact List.mem_append_left _ hqOther
      · rw [hreason]; exact List.mem_append_left _ hqOther
    exact linMaxNegLit_eval_false_of_not_true hx (hnotTrue _ hqReason)
  have hother := linDotSum_le_linTotalMax (terms.eraseIdx i) a (by
    intro q hq
    exact hotherFalse q (by simpa [linOtherMaxLits] using hq))
  obtain ⟨xt, hxt⟩ := hint t ht
  have hsplit := linDotSum_eq_eraseIdx_add (terms := terms) (i := i) (t := t)
    hterm hxt
  rcases hbranch with ⟨hpos, hl, hlt, hreason⟩ | ⟨hnotpos, hneg, hl, hlt, hreason⟩
  · have hqReason : l ∈ reason := by
      rw [hreason]; exact List.mem_append_right _ (by simp)
    have hnl : (negLe t.s (-((linOtherMax terms i - b) / t.c) - 1)).eval a =
        some false :=
      negLe_eval_false_of_not_true
        (k := -((linOtherMax terms i - b) / t.c) - 1) hxt (by
          rw [← hl]; exact hnotTrue _ hqReason)
    obtain ⟨x, hx, hxle⟩ := (eval_negLe_false_iff a t.s
      (-((linOtherMax terms i - b) / t.c) - 1)).mp hnl
    have hmul := linPruneGePos_mul_lt (c := t.c)
      (newLo := -((linOtherMax terms i - b) / t.c)) (x := x)
      (b := b) (other := linOtherMax terms i) hpos rfl hxle
    have hxxt : x = xt := by
      rw [hxt] at hx
      exact (Option.some.inj hx.symm)
    have hlow : linDotSum (terms.eraseIdx i) a + t.c * x < b := by
      unfold linOtherMax at hmul
      omega
    have hsum : linDotSum terms a = linDotSum (terms.eraseIdx i) a + t.c * x := by
      rw [hxxt]; exact hsplit
    rw [hsum] at hge
    omega
  · have hqReason : l ∈ reason := by
      rw [hreason]; exact List.mem_append_right _ (by simp)
    have hpl : (posLe t.s ((b - linOtherMax terms i) / t.c)).eval a = some false :=
      posLe_eval_false_of_not_true (k := (b - linOtherMax terms i) / t.c) hxt (by
        rw [← hl]; exact hnotTrue _ hqReason)
    obtain ⟨x, hx, hnle⟩ := (eval_posLe_false_iff a t.s
      ((b - linOtherMax terms i) / t.c)).mp hpl
    have hxlt : (b - linOtherMax terms i) / t.c < x := by omega
    have hmul := linPruneGeNeg_mul_lt (c := t.c)
      (newHi := (b - linOtherMax terms i) / t.c) (x := x)
      (b := b) (other := linOtherMax terms i) hneg rfl hxlt
    have hxxt : x = xt := by
      rw [hxt] at hx
      exact (Option.some.inj hx.symm)
    have hlow : linDotSum (terms.eraseIdx i) a + t.c * x < b := by
      unfold linOtherMax at hmul
      omega
    have hsum : linDotSum terms a = linDotSum (terms.eraseIdx i) a + t.c * x := by
      rw [hxxt]; exact hsplit
    rw [hsum] at hge
    omega

theorem linConflict_satisfied {terms : List LinTerm} {b : Int} {a : Assignment}
    (hint : ∀ t ∈ terms, ∃ x, slotInt a t.s = some x)
    (hdot : linDotSum terms a = b)
    (hconf : b < linTotalMin terms) :
    Clause.SatisfiedBy (linConflictLits terms) a := by
  apply Classical.byContradiction
  intro hno
  have hnotTrue : ∀ l ∈ linConflictLits terms, l.eval a ≠ some true := by
    intro l hl htrue
    exact hno ⟨l, hl, htrue⟩
  have hfalse : ∀ l ∈ linConflictLits terms, l.eval a = some false := by
    intro l hl
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hl
    obtain ⟨x, hx⟩ := hint t ht
    exact linMinNegLit_eval_false_of_not_true hx (hnotTrue _ hl)
  have hle := linTotalMin_le_linDotSum terms a hfalse
  omega

theorem linMaxConflict_satisfied {terms : List LinTerm} {b : Int} {a : Assignment}
    (hint : ∀ t ∈ terms, ∃ x, slotInt a t.s = some x)
    (hdot : linDotSum terms a = b)
    (hconf : linTotalMax terms < b) :
    Clause.SatisfiedBy (linMaxLits terms) a := by
  apply Classical.byContradiction
  intro hno
  have hnotTrue : ∀ l ∈ linMaxLits terms, l.eval a ≠ some true := by
    intro l hl htrue
    exact hno ⟨l, hl, htrue⟩
  have hfalse : ∀ l ∈ linMaxLits terms, l.eval a = some false := by
    intro l hl
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hl
    obtain ⟨x, hx⟩ := hint t ht
    exact linMaxNegLit_eval_false_of_not_true hx (hnotTrue _ hl)
  have hle := linDotSum_le_linTotalMax terms a hfalse
  omega

/-! ## Assignment-level reasons for disequalities -/

def linNeConflictLits (terms : List LinTerm) : List Literal :=
  terms.map fun t => posNe t.s t.lo

def linFixedLits (terms : List LinTerm) : List Literal :=
  terms.map fun t => posNe t.s t.lo

def linNonFixedIndices (terms : List LinTerm) : List Nat :=
  (List.range terms.length).filter fun i =>
    match terms[i]? with
    | some t => !(t.lo == t.hi)
    | none => false

theorem linNonFixedIndices_mem {terms : List LinTerm} {i : Nat} :
    i ∈ linNonFixedIndices terms ↔ ∃ t, terms[i]? = some t ∧ t.lo ≠ t.hi := by
  unfold linNonFixedIndices
  rw [List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨_, h⟩
    cases ht : terms[i]? with
    | none => simp [ht] at h
    | some t =>
        simp only [ht] at h
        have hf : (t.lo == t.hi) = false := by simpa using h
        have hne : t.lo ≠ t.hi := by
          intro he
          rw [beq_iff_eq.mpr he] at hf
          simp at hf
        exact ⟨t, rfl, hne⟩
  · rintro ⟨t, ht, hne⟩
    have hi : i < terms.length := by
      apply Nat.lt_of_not_le
      intro hle
      have hnone := List.getElem?_eq_none hle
      rw [ht] at hnone
      cases hnone
    refine ⟨hi, ?_⟩
    have hf : (t.lo == t.hi) = false := by
      cases h : (t.lo == t.hi) with
      | false => rfl
      | true => exact absurd (beq_iff_eq.mp h) hne
    simp [ht, hf]

theorem linNonFixedIndices_nil_spec {terms : List LinTerm}
    (h : linNonFixedIndices terms = []) :
    ∀ t ∈ terms, t.lo = t.hi := by
  intro t ht
  apply Classical.byContradiction
  intro hne
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp ht
  have hmem : j ∈ linNonFixedIndices terms := by
    rw [linNonFixedIndices_mem]
    exact ⟨t, by rw [List.getElem?_eq_getElem hj]; exact congrArg some hget, hne⟩
  rw [h] at hmem
  simp at hmem

theorem linNonFixedIndices_singleton_spec {terms : List LinTerm} {i : Nat}
    (h : linNonFixedIndices terms = [i]) :
    ∃ t, terms[i]? = some t ∧ t.lo ≠ t.hi := by
  have hmem : i ∈ linNonFixedIndices terms := by rw [h]; simp
  exact linNonFixedIndices_mem.mp hmem

theorem linNonFixedIndices_singleton_fixed_erase {terms : List LinTerm} {i : Nat}
    (h : linNonFixedIndices terms = [i]) :
    ∀ u ∈ terms.eraseIdx i, u.lo = u.hi := by
  intro u hu
  apply Classical.byContradiction
  intro hne
  obtain ⟨j, hj, hji, hget⟩ := List.mem_eraseIdx_iff_getElem.mp hu
  have hmem : j ∈ linNonFixedIndices terms := by
    rw [linNonFixedIndices_mem]
    exact ⟨u, by rw [List.getElem?_eq_getElem hj]; exact congrArg some hget, hne⟩
  rw [h] at hmem
  simp only [List.mem_singleton] at hmem
  omega

theorem linDotSum_eq_linTotalMin_of_fixed (terms : List LinTerm) (a : Assignment)
    (hfix : ∀ t ∈ terms, t.lo = t.hi)
    (hval : ∀ t ∈ terms, slotInt a t.s = some t.lo) :
    linDotSum terms a = linTotalMin terms := by
  induction terms with
  | nil => simp [linDotSum, linTotalMin]
  | cons t ts ih =>
      have hhead := hval t (by simp)
      have hlo := hfix t (by simp)
      have hmin : t.min = t.c * t.lo := by
        by_cases hc : 0 ≤ t.c
        · simp [LinTerm.min, linTermMin, hc]
        · have hcl : t.min = t.c * t.hi := by
            simp [LinTerm.min, linTermMin, hc]
          rw [hcl, ← hlo]
      have ih' := ih
        (fun u hu => hfix u (List.mem_cons_of_mem _ hu))
        (fun u hu => hval u (List.mem_cons_of_mem _ hu))
      simp only [linDotSum, linTotalMin]
      rw [hhead, Option.getD_some, hmin, ih']

theorem linNeConflict_satisfied {terms : List LinTerm} {b : Int} {a : Assignment}
    (hall : linNonFixedIndices terms = [])
    (hmin : linTotalMin terms = b)
    (hint : ∀ t ∈ terms, ∃ x, slotInt a t.s = some x)
    (hne : linDotSum terms a ≠ b) :
    Clause.SatisfiedBy (linNeConflictLits terms) a := by
  apply Classical.byContradiction
  intro hno
  have hnotTrue : ∀ l ∈ linNeConflictLits terms, l.eval a ≠ some true := by
    intro l hl htrue
    exact hno ⟨l, hl, htrue⟩
  have hval : ∀ t ∈ terms, slotInt a t.s = some t.lo := by
    intro t ht
    have hl : (posNe t.s t.lo) ∈ linNeConflictLits terms :=
      List.mem_map.mpr ⟨t, ht, rfl⟩
    obtain ⟨x, hx⟩ := hint t ht
    have hfalse : (posNe t.s t.lo).eval a = some false := by
      cases he : (posNe t.s t.lo).eval a with
      | none =>
          rw [eval_posNe, hx] at he
          simp at he
      | some b' =>
          cases b' with
          | false => rfl
          | true => exact absurd he (hnotTrue _ hl)
    obtain ⟨y, hy, hyv⟩ := (eval_posNe_false_iff a t.s t.lo).mp hfalse
    have hxy : x = y := Option.some.inj (hx.symm.trans hy)
    rw [hxy, hyv] at hx
    exact hx
  have hfix := linNonFixedIndices_nil_spec hall
  have hdot := linDotSum_eq_linTotalMin_of_fixed terms a hfix hval
  exact hne (by rw [hdot, hmin])

theorem linNePrune_satisfied {terms : List LinTerm} {b : Int} {a : Assignment}
    {i : Nat} {t : LinTerm} {v : Int}
    (hterm : terms[i]? = some t)
    (hnon : linNonFixedIndices terms = [i])
    (heq : t.c * v = b - linOtherMin terms i)
    (hint : ∀ u ∈ terms, ∃ x, slotInt a u.s = some x)
    (hne : linDotSum terms a ≠ b) :
    Clause.SatisfiedBy (linFixedLits (terms.eraseIdx i) ++ [posNe t.s v]) a := by
  apply Classical.byContradiction
  intro hno
  have hnotTrue : ∀ q ∈ linFixedLits (terms.eraseIdx i) ++ [posNe t.s v],
      q.eval a ≠ some true := by
    intro q hq htrue
    exact hno ⟨q, hq, htrue⟩
  have hotherVal : ∀ u ∈ terms.eraseIdx i, slotInt a u.s = some u.lo := by
    intro u hu
    have hq : posNe u.s u.lo ∈ linFixedLits (terms.eraseIdx i) :=
      List.mem_map.mpr ⟨u, hu, rfl⟩
    have hqReason : posNe u.s u.lo ∈
        linFixedLits (terms.eraseIdx i) ++ [posNe t.s v] :=
      List.mem_append_left _ hq
    obtain ⟨x, hx⟩ := hint u (List.mem_of_mem_eraseIdx hu)
    have hfalse : (posNe u.s u.lo).eval a = some false := by
      cases he : (posNe u.s u.lo).eval a with
      | none =>
          rw [eval_posNe, hx] at he
          simp at he
      | some b' =>
          cases b' with
          | false => rfl
          | true => exact absurd he (hnotTrue _ hqReason)
    obtain ⟨y, hy, hyv⟩ := (eval_posNe_false_iff a u.s u.lo).mp hfalse
    have hxy : x = y := Option.some.inj (hx.symm.trans hy)
    rw [hxy, hyv] at hx
    exact hx
  obtain ⟨xt, hxt⟩ := hint t (by
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hterm
    exact List.mem_iff_getElem.mpr ⟨i, hlt, hget⟩)
  have hqLast : posNe t.s v ∈ linFixedLits (terms.eraseIdx i) ++ [posNe t.s v] :=
    List.mem_append_right _ (by simp)
  have hfalseT : (posNe t.s v).eval a = some false := by
    cases he : (posNe t.s v).eval a with
    | none =>
        rw [eval_posNe, hxt] at he
        simp at he
    | some b' =>
        cases b' with
        | false => rfl
        | true => exact absurd he (hnotTrue _ hqLast)
  obtain ⟨y, hy, hyv⟩ := (eval_posNe_false_iff a t.s v).mp hfalseT
  rw [hxt] at hy
  have hxeq : xt = y := Option.some.inj hy
  have hvalT : slotInt a t.s = some v := by
    rw [hxt, hxeq, hyv]
  have hfix := linNonFixedIndices_singleton_fixed_erase hnon
  have hdotOther := linDotSum_eq_linTotalMin_of_fixed (terms.eraseIdx i) a hfix hotherVal
  have hsplit := linDotSum_eq_eraseIdx_add (terms := terms) (i := i) (t := t)
    hterm hvalT
  have hdot : linDotSum terms a = b := by
    rw [hsplit, hdotOther]
    have heq' : t.c * v = b - linTotalMin (terms.eraseIdx i) := heq
    omega
  exact hne hdot

/-! ## Problem-level integer guards

The reified constraints only constrain the dot product when the reification
slot is a Boolean; on a non-integer operand the accepted assignments are
vacuous, but the propagator reasons about the integer view.  These guards
let a builder decline such problems instead of proving unsound clauses.
-/

def domIntB (o : Option Dom) : Bool :=
  match o with
  | none => false
  | some d => Dom.allIntBStruct d

def slotsIntB (p : CompiledProblem DomConstraint) (is : List Nat) : Bool :=
  is.all fun s => domIntB p.domains[s]?

def viewIntKindB (view : EngineView) (slots : Array Nat) : Bool :=
  slots.all fun s => (view.doms.getD s DomC.empty).intKindB

theorem domIntB_spec {o : Option Dom} {d : Dom} (h : domIntB o = true)
    (ho : o = some d) : ∀ v ∈ Dom.enum d, ∃ x, v = .int x := by
  subst ho
  unfold domIntB at h
  simp only [Dom.allIntBStruct_eq] at h
  rw [List.all_eq_true] at h
  intro v hv
  have hv' := h v hv
  cases v with
  | bool _ => simp [Dom.isIntV] at hv'
  | int x => exact ⟨x, rfl⟩
  | setOfInt _ => simp [Dom.isIntV] at hv'
  | array _ => simp [Dom.isIntV] at hv'

theorem slotsIntB_spec {p : CompiledProblem DomConstraint} {is : List Nat}
    (h : slotsIntB p is = true) {a : Assignment}
    (ha : a ∈ allAssigns p.domains) {s : Nat} (hs : s ∈ is) :
    ∃ x, a[s]? = some (.int x) := by
  unfold slotsIntB at h
  rw [List.all_eq_true] at h
  have hg := h s hs
  obtain ⟨hlen, hmem⟩ := allAssigns_fits_dom p.domains a ha
  cases hd : p.domains[s]? with
  | none =>
      rw [hd] at hg
      simp [domIntB] at hg
  | some d =>
      rw [hd] at hg
      have hslen : s < p.domains.length := by
        obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hd
        exact hlt
      have has : s < a.length := by rw [hlen]; exact hslen
      have hap : a[s]? = some a[s] := List.getElem?_eq_getElem has
      have hm : a[s] ∈ d := by
        have := hmem s a[s] hap
        simpa [hd] using this
      have hmemBool : d.memBool a[s] = true := by
        simpa only [Membership.mem] using hm
      have hen : a[s] ∈ Dom.enum d := (Dom.memBool_iff d a[s]).mp hmemBool
      obtain ⟨x, hx⟩ := domIntB_spec hg rfl a[s] hen
      exact ⟨x, by rw [hap, hx]⟩

theorem viewIntKindB_spec {view : EngineView} {slots : Array Nat}
    (h : viewIntKindB view slots = true) {s : Nat} (hs : s ∈ slots.toList) :
    (view.doms.getD s DomC.empty).intKindB = true := by
  unfold viewIntKindB at h
  rw [Array.all_eq_true] at h
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hs
  have hlt : i < slots.size := by simpa using hi
  have hsi : slots[i] = s := hget
  have := h i hlt
  simpa [hsi] using this

theorem linTerms_slot_mem_is {coeffs : List Int} {is : List Nat} {view : EngineView}
    {bds : Array (Int × Int)} {t : LinTerm}
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (ht : t ∈ linTerms coeffs.toArray is.toArray bds) : t.s ∈ is := by
  have hbdsize : bds.size = is.toArray.size := (linExtractBounds_spec hbds).1
  have := linTerms_slot_mem (cs := coeffs.toArray) (slots := is.toArray)
    (bds := bds) hsize hbdsize ht
  simpa using this

theorem linTerms_hint_of_dotProduct
    (coeffs : List Int) (is : List Nat) (view : EngineView)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    {a : Assignment} {d : Int}
    (hdot : dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) = some d) :
    ∀ t ∈ linTerms coeffs.toArray is.toArray bds,
      ∃ x, slotInt a t.s = some x := by
  intro t ht
  have hs := linTerms_slot_mem_is hsize hbds ht
  obtain ⟨x, hx⟩ := dotProduct_reads_int_local hdot t.s hs
  exact ⟨x, slotInt_eq_some_of_getElem!_int hx⟩

theorem dotProduct_eq_linDotSum_of_slotsIntB {p : CompiledProblem DomConstraint}
    (coeffs : List Int) (is : List Nat) (view : EngineView)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hguard : slotsIntB p is = true)
    {a : Assignment} (ha : a ∈ allAssigns p.domains) :
    dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) =
      some (linDotSum (linTerms coeffs.toArray is.toArray bds) a) := by
  have hbdsize : bds.size = is.toArray.size := (linExtractBounds_spec hbds).1
  have hxall : ∀ s ∈ is.toArray.toList, ∃ x, a[s]! = .int x := by
    intro s hs
    have hs' : s ∈ is := by simpa using hs
    obtain ⟨x, hx⟩ := slotsIntB_spec hguard ha hs'
    exact ⟨x, List.getElem!_of_getElem? hx⟩
  have hbridge := dotProduct_eq_linDotSum (cs := coeffs.toArray)
    (slots := is.toArray) (bds := bds) hsize hbdsize a hxall
  simpa using hbridge

/-! ## Extracting the numeric relation from `accepts` -/

theorem dotProduct_decide_eq_true {vals xs : List Value} {b : Int}
    (h : (match dotProduct vals xs with
      | some d => decide (d = b)
      | none => false) = true) :
    dotProduct vals xs = some b := by
  by_cases hd : dotProduct vals xs = some b
  · exact hd
  · exfalso
    cases hsome : dotProduct vals xs with
    | none => rw [hsome] at h; simp at h
    | some d =>
        rw [hsome] at h
        have hdb : d = b := of_decide_eq_true h
        exact hd (by rw [hsome, hdb])

theorem linEq_accepts_facts (p : CompiledProblem DomConstraint)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linEq coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    {a : Assignment} (hacc : accepts p a = true) :
    (∀ t ∈ linTerms coeffs.toArray is.toArray bds,
      ∃ x, slotInt a t.s = some x) ∧
      linDotSum (linTerms coeffs.toArray is.toArray bds) a = b := by
  have hdc : (DomConstraint.linEq coeffs is b).satisfiedB a = true :=
    accepts_satisfiedB hacc hmem
  have hdot : dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) = some b := by
    have hdef : (DomConstraint.linEq coeffs is b).satisfiedB a =
        (match dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) with
         | some d => decide (d = b)
         | none => false) := rfl
    rw [hdef] at hdc
    exact dotProduct_decide_eq_true hdc
  have hbdsize : bds.size = is.toArray.size := (linExtractBounds_spec hbds).1
  have hxall : ∀ s ∈ is.toArray.toList, ∃ x, a[s]! = .int x := by
    intro s hs
    exact dotProduct_reads_int_local hdot s (by simpa using hs)
  have hbridge := dotProduct_eq_linDotSum (cs := coeffs.toArray)
    (slots := is.toArray) (bds := bds) hsize hbdsize a hxall
  rw [hdot] at hbridge
  have hd_eq : b = linDotSum (linTerms coeffs.toArray is.toArray bds) a :=
    Option.some.inj hbridge
  exact ⟨linTerms_hint_of_dotProduct coeffs is view hsize bds hbds hdot,
    hd_eq.symm⟩

theorem linNe_accepts_facts (p : CompiledProblem DomConstraint)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linNe coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    {a : Assignment} (hacc : accepts p a = true) :
    (∀ t ∈ linTerms coeffs.toArray is.toArray bds,
      ∃ x, slotInt a t.s = some x) ∧
      ∃ d, linDotSum (linTerms coeffs.toArray is.toArray bds) a = d ∧ d ≠ b := by
  have hdc : (DomConstraint.linNe coeffs is b).satisfiedB a = true :=
    accepts_satisfiedB hacc hmem
  have hdotne : dotNe (intVals coeffs) (is.map (fun i => a[i]!)) b = true := by
    have hdef : (DomConstraint.linNe coeffs is b).satisfiedB a =
        dotNe (intVals coeffs) (is.map (fun i => a[i]!)) b := rfl
    rw [hdef] at hdc
    exact hdc
  obtain ⟨d, hdot, hdne⟩ := (dotNe_eq _ _ _).mp hdotne
  have hbdsize : bds.size = is.toArray.size := (linExtractBounds_spec hbds).1
  have hxall : ∀ s ∈ is.toArray.toList, ∃ x, a[s]! = .int x := by
    intro s hs
    exact dotProduct_reads_int_local hdot s (by simpa using hs)
  have hbridge := dotProduct_eq_linDotSum (cs := coeffs.toArray)
    (slots := is.toArray) (bds := bds) hsize hbdsize a hxall
  rw [hdot] at hbridge
  have hd_eq : d = linDotSum (linTerms coeffs.toArray is.toArray bds) a :=
    Option.some.inj hbridge
  exact ⟨linTerms_hint_of_dotProduct coeffs is view hsize bds hbds hdot,
    ⟨d, hd_eq.symm, hdne⟩⟩

theorem linLeReif_accepts_facts (p : CompiledProblem DomConstraint)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linLeReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hguard : slotsIntB p is = true)
    {a : Assignment} (ha : a ∈ allAssigns p.domains)
    (hacc : accepts p a = true) {rb : Bool} (hrb : a[r]? = some (.bool rb)) :
    (∀ t ∈ linTerms coeffs.toArray is.toArray bds,
      ∃ x, slotInt a t.s = some x) ∧
      (rb = true → linDotSum (linTerms coeffs.toArray is.toArray bds) a ≤ b) ∧
      (rb = false → b + 1 ≤ linDotSum (linTerms coeffs.toArray is.toArray bds) a) := by
  have hdc : (DomConstraint.linLeReif coeffs is b r).satisfiedB a = true :=
    accepts_satisfiedB hacc hmem
  have hrel : rb = dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b := by
    have hdef : (DomConstraint.linLeReif coeffs is b r).satisfiedB a =
        (match a[r]? with
         | some (.bool rb') =>
             decide (rb' = dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b)
         | _ => false) := rfl
    rw [hdef, hrb] at hdc
    exact of_decide_eq_true hdc
  have hbridge := dotProduct_eq_linDotSum_of_slotsIntB (p := p) coeffs is view
    hsize bds hbds hguard ha
  refine ⟨?_, ?_, ?_⟩
  · exact linTerms_hint_of_dotProduct coeffs is view hsize bds hbds hbridge
  · intro hrbt
    have hdle : dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b = true := by
      rw [← hrel, hrbt]
    unfold dotLe at hdle
    rw [hbridge] at hdle
    exact of_decide_eq_true hdle
  · intro hrbf
    have hdle : dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b = false := by
      rw [← hrel, hrbf]
    unfold dotLe at hdle
    rw [hbridge] at hdle
    have hgt : ¬ linDotSum (linTerms coeffs.toArray is.toArray bds) a ≤ b :=
      of_decide_eq_false hdle
    omega

theorem linEqReif_accepts_facts (p : CompiledProblem DomConstraint)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linEqReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hguard : slotsIntB p is = true)
    {a : Assignment} (ha : a ∈ allAssigns p.domains)
    (hacc : accepts p a = true) {rb : Bool} (hrb : a[r]? = some (.bool rb)) :
    (∀ t ∈ linTerms coeffs.toArray is.toArray bds,
      ∃ x, slotInt a t.s = some x) ∧
      (rb = true → linDotSum (linTerms coeffs.toArray is.toArray bds) a = b) ∧
      (rb = false → linDotSum (linTerms coeffs.toArray is.toArray bds) a ≠ b) := by
  have hdc : (DomConstraint.linEqReif coeffs is b r).satisfiedB a = true :=
    accepts_satisfiedB hacc hmem
  have hrel : rb =
      (match dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) with
       | some d => decide (d = b)
       | none => false) := by
    have hdef : (DomConstraint.linEqReif coeffs is b r).satisfiedB a =
        (match a[r]? with
         | some (.bool rb') =>
             decide (rb' =
               (match dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) with
                | some d => decide (d = b)
                | none => false))
         | _ => false) := rfl
    rw [hdef, hrb] at hdc
    exact of_decide_eq_true hdc
  have hbridge := dotProduct_eq_linDotSum_of_slotsIntB (p := p) coeffs is view
    hsize bds hbds hguard ha
  refine ⟨linTerms_hint_of_dotProduct coeffs is view hsize bds hbds hbridge, ?_, ?_⟩
  · intro hrbt
    have hrelt :
        (match dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) with
         | some d => decide (d = b)
         | none => false) = true := by rw [← hrel, hrbt]
    rw [hbridge] at hrelt
    change decide (linDotSum (linTerms coeffs.toArray is.toArray bds) a = b) = true at hrelt
    exact of_decide_eq_true hrelt
  · intro hrbf
    have hrelf :
        (match dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) with
         | some d => decide (d = b)
         | none => false) = false := by rw [← hrel, hrbf]
    rw [hbridge] at hrelf
    change decide (linDotSum (linTerms coeffs.toArray is.toArray bds) a = b) = false at hrelf
    exact of_decide_eq_false hrelf

theorem linNeReif_accepts_facts (p : CompiledProblem DomConstraint)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linNeReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hguard : slotsIntB p is = true)
    {a : Assignment} (ha : a ∈ allAssigns p.domains)
    (hacc : accepts p a = true) {rb : Bool} (hrb : a[r]? = some (.bool rb)) :
    (∀ t ∈ linTerms coeffs.toArray is.toArray bds,
      ∃ x, slotInt a t.s = some x) ∧
      (rb = true → linDotSum (linTerms coeffs.toArray is.toArray bds) a ≠ b) ∧
      (rb = false → linDotSum (linTerms coeffs.toArray is.toArray bds) a = b) := by
  have hdc : (DomConstraint.linNeReif coeffs is b r).satisfiedB a = true :=
    accepts_satisfiedB hacc hmem
  have hrel : rb = dotNe (intVals coeffs) (is.map (fun i => a[i]!)) b := by
    have hdef : (DomConstraint.linNeReif coeffs is b r).satisfiedB a =
        (match a[r]? with
         | some (.bool rb') =>
             decide (rb' = dotNe (intVals coeffs) (is.map (fun i => a[i]!)) b)
         | _ => false) := rfl
    rw [hdef, hrb] at hdc
    exact of_decide_eq_true hdc
  have hbridge := dotProduct_eq_linDotSum_of_slotsIntB (p := p) coeffs is view
    hsize bds hbds hguard ha
  unfold dotNe at hrel
  rw [hbridge] at hrel
  change rb = decide (linDotSum (linTerms coeffs.toArray is.toArray bds) a ≠ b) at hrel
  refine ⟨linTerms_hint_of_dotProduct coeffs is view hsize bds hbds hbridge, ?_, ?_⟩
  · intro hrbt
    have hdect : decide (linDotSum (linTerms coeffs.toArray is.toArray bds) a ≠ b) = true := by
      rw [← hrel, hrbt]
    exact of_decide_eq_true hdect
  · intro hrbf
    have hdecf : decide (linDotSum (linTerms coeffs.toArray is.toArray bds) a ≠ b) = false := by
      rw [← hrel, hrbf]
    have hne : ¬ linDotSum (linTerms coeffs.toArray is.toArray bds) a ≠ b :=
      of_decide_eq_false hdecf
    apply Classical.byContradiction
    intro h
    exact hne h

/-! ## Assignment-level conflict lemmas for the inequality passes -/

theorem linLeConflict_satisfied {terms : List LinTerm} {b : Int} {a : Assignment}
    (hint : ∀ t ∈ terms, ∃ x, slotInt a t.s = some x)
    (hle : linDotSum terms a ≤ b)
    (hconf : b < linTotalMin terms) :
    Clause.SatisfiedBy (linConflictLits terms) a := by
  apply Classical.byContradiction
  intro hno
  have hnotTrue : ∀ l ∈ linConflictLits terms, l.eval a ≠ some true := by
    intro l hl htrue
    exact hno ⟨l, hl, htrue⟩
  have hfalse : ∀ l ∈ linConflictLits terms, l.eval a = some false := by
    intro l hl
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hl
    obtain ⟨x, hx⟩ := hint t ht
    exact linMinNegLit_eval_false_of_not_true hx (hnotTrue _ hl)
  have hmin := linTotalMin_le_linDotSum terms a hfalse
  omega

theorem linMaxConflict_satisfied_of_ge {terms : List LinTerm} {b : Int} {a : Assignment}
    (hint : ∀ t ∈ terms, ∃ x, slotInt a t.s = some x)
    (hge : b ≤ linDotSum terms a)
    (hconf : linTotalMax terms < b) :
    Clause.SatisfiedBy (linMaxLits terms) a := by
  apply Classical.byContradiction
  intro hno
  have hnotTrue : ∀ l ∈ linMaxLits terms, l.eval a ≠ some true := by
    intro l hl htrue
    exact hno ⟨l, hl, htrue⟩
  have hfalse : ∀ l ∈ linMaxLits terms, l.eval a = some false := by
    intro l hl
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hl
    obtain ⟨x, hx⟩ := hint t ht
    exact linMaxNegLit_eval_false_of_not_true hx (hnotTrue _ hl)
  have hmax := linDotSum_le_linTotalMax terms a hfalse
  omega


/-! ## Row-slack skip lemmas

A row whose total maximum already satisfies `dot ≤ b` cannot produce a
lower-side prune or a conflict, and a row whose total minimum already
satisfies `dot ≥ c` cannot produce an upper-side prune or a conflict.
These are the arithmetic facts behind the conservative skip used by the
reified inequality propagator; they do not assume any particular bound
ordering beyond `min ≤ max` for each term.
-/

theorem linTermMin_le_max {c lo hi : Int} (h : lo ≤ hi) :
    linTermMin c lo hi ≤ linTermMax c lo hi := by
  unfold linTermMin linTermMax
  by_cases hc : 0 ≤ c
  · simp [hc]
    exact Int.mul_le_mul_of_nonneg_left h hc
  · have hc' : c ≤ 0 := by omega
    simp [hc]
    exact Int.mul_le_mul_of_nonpos_left hc' h

theorem linTotalMin_le_totalMax {terms : List LinTerm}
    (hmm : ∀ t ∈ terms, t.min ≤ t.max) : linTotalMin terms ≤ linTotalMax terms := by
  induction terms with
  | nil => simp [linTotalMin, linTotalMax]
  | cons t ts ih =>
      simp only [linTotalMin, linTotalMax]
      have ht := hmm t (by simp)
      have hts : ∀ u ∈ ts, u.min ≤ u.max := fun u hu => hmm u (by simp [hu])
      have := ih hts
      omega

theorem linPrunes_eq_nil_of_totalMax_le {terms : List LinTerm} {b : Int}
    (hmm : ∀ t ∈ terms, t.min ≤ t.max)
    (h : linTotalMax terms ≤ b) : linPrunes terms b = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro p hp
  obtain ⟨i, t, ht, hbr⟩ := linPrunes_mem hp
  have hother : linTotalMin (terms.eraseIdx i) ≤ linTotalMax (terms.eraseIdx i) := by
    apply linTotalMin_le_totalMax
    intro u hu
    exact hmm u (List.mem_of_mem_eraseIdx hu)
  have hsum := linTotalMax_eq_eraseIdx_add (terms := terms) (i := i) (t := t) ht
  have hb : t.max ≤ b - linTotalMin (terms.eraseIdx i) := by
    omega
  rcases hbr with ⟨hc, hl, hlt, hr⟩ | ⟨hnc, hc, hl, hlt, hr⟩
  · have hlt' : (b - linTotalMin (terms.eraseIdx i)) / t.c < t.hi := by
      simpa [linOtherMin] using hlt
    have htmax : t.max = t.c * t.hi := by
      unfold LinTerm.max linTermMax
      simp [show 0 ≤ t.c from by omega]
    have hge : t.hi ≤ (b - linTotalMin (terms.eraseIdx i)) / t.c := by
      apply Int.le_ediv_of_mul_le hc
      rw [Int.mul_comm]
      rw [← htmax]
      exact hb
    omega
  · have hlt' : t.lo < -((b - linTotalMin (terms.eraseIdx i)) / (-t.c)) := by
      simpa [linOtherMin] using hlt
    have htmax : t.max = t.c * t.lo := by
      unfold LinTerm.max linTermMax
      simp [show ¬ 0 ≤ t.c from by omega]
    have hB : t.c * t.lo ≤ b - linTotalMin (terms.eraseIdx i) := by
      rw [← htmax]
      exact hb
    have hle : -((b - linTotalMin (terms.eraseIdx i)) / (-t.c)) ≤ t.lo := by
      have hneg : 0 < -t.c := by omega
      have h' : (-t.lo) * (-t.c) ≤ b - linTotalMin (terms.eraseIdx i) := by
        rw [Int.neg_mul_neg, Int.mul_comm]
        exact hB
      have := Int.le_ediv_of_mul_le (a := -t.lo) (b := b - linTotalMin (terms.eraseIdx i)) (c := -t.c) hneg h'
      omega
    omega

theorem linPrunesGe_eq_nil_of_le_totalMin {terms : List LinTerm} {c : Int}
    (hmm : ∀ t ∈ terms, t.min ≤ t.max)
    (h : c ≤ linTotalMin terms) : linPrunesGe terms c = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro p hp
  obtain ⟨i, t, ht, hbr⟩ := linPrunesGe_mem hp
  have hother : linTotalMin (terms.eraseIdx i) ≤ linTotalMax (terms.eraseIdx i) := by
    apply linTotalMin_le_totalMax
    intro u hu
    exact hmm u (List.mem_of_mem_eraseIdx hu)
  have hsum : linTotalMin terms = linTotalMin (terms.eraseIdx i) + t.min :=
    linTotalMin_eq_eraseIdx_add ht
  have hb : c - linTotalMax (terms.eraseIdx i) ≤ t.min := by
    omega
  rcases hbr with ⟨hc, hl, hlt, hr⟩ | ⟨hnc, hc, hl, hlt, hr⟩
  · have hlt' : t.lo < -((linTotalMax (terms.eraseIdx i) - c) / t.c) := by
      simpa [linOtherMax] using hlt
    have htmin : t.min = t.c * t.lo := by
      unfold LinTerm.min linTermMin
      simp [show 0 ≤ t.c from by omega]
    have hlo : -((linTotalMax (terms.eraseIdx i) - c) / t.c) ≤ t.lo := by
      have h1 : (-t.lo) * t.c ≤ linTotalMax (terms.eraseIdx i) - c := by
        rw [Int.neg_mul]
        rw [Int.mul_comm t.lo t.c, ← htmin]
        omega
      have h' := Int.le_ediv_of_mul_le (a := -t.lo) (b := linTotalMax (terms.eraseIdx i) - c) (c := t.c) hc h1
      omega
    omega
  · have hlt' : (c - linTotalMax (terms.eraseIdx i)) / t.c < t.hi := by
      simpa [linOtherMax] using hlt
    have htmin : t.min = t.c * t.hi := by
      unfold LinTerm.min linTermMin
      simp [show ¬ 0 ≤ t.c from by omega]
    have hhi : t.hi ≤ (c - linTotalMax (terms.eraseIdx i)) / t.c := by
      have hneg : 0 < -t.c := by omega
      have h1 : c - linTotalMax (terms.eraseIdx i) ≤ (-t.hi) * (-t.c) := by
        rw [Int.neg_mul_neg, Int.mul_comm]
        rw [← htmin]
        exact hb
      have hq := Int.ediv_le_of_le_mul (a := c - linTotalMax (terms.eraseIdx i)) (b := -t.hi) (c := -t.c) hneg h1
      rw [Int.ediv_neg] at hq
      omega
    omega

/-- Every term extracted from a well-formed view has `min ≤ max`. -/
theorem linTerms_min_le_max {view : EngineView} {cs : Array Int} {slots : Array Nat}
    {bds : Array (Int × Int)}
    (h1 : cs.size = slots.size)
    (hbds : linExtractBounds view.doms slots = some bds)
    (hWF : ViewWF view slots) :
    ∀ t ∈ linTerms cs slots bds, t.min ≤ t.max := by
  intro t ht
  obtain ⟨hlo, hhi⟩ := linTerms_mem_bounds h1 hbds ht
  have hbdsize := (linExtractBounds_spec hbds).1
  have hmem : t.s ∈ slots.toList := linTerms_slot_mem h1 hbdsize ht
  have hdWF := hWF.dom_wf hmem
  have hle : t.lo ≤ t.hi := DomC.lo?_le_hi? _ hdWF hlo hhi
  exact linTermMin_le_max hle

end LeanFzn.Engine

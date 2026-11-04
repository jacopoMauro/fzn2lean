/-
File: LeanFzn/Solver/Propagation/DbScanIndex.lean

Purpose (PLAN tasks P1b/M1): an OPTIMISED, PROVABLY EQUAL re-implementation
of the learned-database scan chain `scanDatabase` -> `clauseRemaining` ->
`literalImpossible`, with the slot index hoisted out of the per-literal loop
and a per-slot possibility summary deciding the common literal shapes in O(1).

Measured hot spots (E1 instrumentation, the retired ScanCounts diagnostic +
`Tests/Legacy/Benchmarks/DbScanCounts.lean`): the chain is the single largest component of
the step cost (~51% of the estimated per-step time on the harness battery).
The cost is per LITERAL of every VISITED clause of the learned database:

* `Frame.domains f` is `f.2.map (fun v => [v]) ++ f.1` — the projection
  ALLOCATES the pinned-singleton prefix on every call, once per literal;
* `List.getD` then WALKS the domain list to the literal's slot, once per
  literal (the battery's real frames average ~50 slots, the deep instances
  far more);
* `c.filter` walks EVERY literal of the clause even when two remaining
  literals already settle the classification;
* `literalImpossible` WALKS the whole domain of the literal's slot, once per
  literal — and most literals are order literals (`.intLe`) or value pins
  (`.intNe`), for which the extremes of the domain's integer-view image
  settle possibility in O(1).

The optimised scan fixes all four, with no change of semantics:

* `frameDomainArray` builds the slot index ONCE per scan (one projection +
  `toArray`), and `literalImpossibleArr` looks a slot up in O(1);
* `slotSumOfDomain` computes, in ONE `foldl` pass per domain, the integer
  extremes of the `Value.intView` image (`minInt`, `maxInt`) and the two
  boolean memberships (`hasTrue`, `hasFalse`); `literalImpossibleFast`
  classifies `.intLe`/`.intNe`-positive/`.boolEq` literals from the summary
  in O(1), and falls back to the certified domain walk only for negative
  `.intNe` (a membership test the summary does not decide);
* `clauseClassify`/`clauseClassifyFast` is a first-order recursion that stops
  at the SECOND remaining literal and never allocates the remaining list;
* `productiveFast` fuses the two `Frame.mass` traversals of `productive`
  into a single test on the one domain `filterFrame` can change.

HYBRID DISPATCH (measured 2026-10-17 on
`minizinc-challenge/2025fzn/proteindesign12/1HZ5.12p.9aa.usingEref_self.fzn`,
169 domains / 3,272,799 values): the array copy alone costs ~143 ms per step
for a database of only 4 clauses, while the certified reference scan
allocates nothing. `scanDatabaseFast` therefore uses the reference
`scanDatabase` directly while `db.length ≤ 8` (a literal small-database
threshold; `if` evaluates only the taken branch, so the array is never built
there) and the indexed `scanDatabaseFastAux` otherwise. The name, type and
the unconditional equality `scanDatabaseFast_eq` are unchanged.

`scanDatabaseFast_eq` proves — UNCONDITIONALLY, on every frame and database —
that the optimised scan returns exactly the certified `scanDatabase` event.
`scanDatabase` and `clauseRemaining`/`literalImpossible` are UNTOUCHED, so
every certified lemma about them continues to hold verbatim; the scheduled
route (`nextPruningEventSched`) is the only consumer wired to the fast scan.

DAG: Pruning + ClausePropagation -> DbScanIndex -> ScheduledPropagation.
-/
import LeanFzn.Legacy.Solver.Propagation.Pruning
import LeanFzn.Legacy.Solver.Propagation.ClausePropagation
open LeanFzn.Semantics LeanFzn.Solver.Propagation


namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-! ## The slot index -/

/-- The frame's slot→domain index as an array. Built once per scan; the
slot order is exactly `Frame.domains`'s (pinned singletons ++ remaining). -/
def frameDomainArray (f : BranchFrame) : Array Domain :=
  (Frame.domains f).toArray

/-- `literalImpossible` against a precomputed slot index. -/
def literalImpossibleArr (a : Array Domain) (l : Literal) : Bool :=
  ((a[l.atom.slot]?.getD Dom.empty).enum.all fun v => !l.valueHolds v)

/-- **EQUIVALENCE (literal form)**: the indexed literal test is the certified
`literalImpossible` at the frame's own slot index. -/
theorem literalImpossibleArr_eq (f : BranchFrame) (l : Literal) :
    literalImpossibleArr (frameDomainArray f) l = literalImpossible f l := by
  unfold literalImpossibleArr literalImpossible frameDomainArray
  rw [List.getElem?_toArray, List.getD_eq_getElem?_getD]

/-! ## Per-slot possibility summaries

`Value.intView` maps integers to themselves and booleans to 0/1, and `none`
for sets and arrays; `Literal.valueHolds` of an order literal only reads that
view, so the integer extremes of the view image decide `.intLe` possibility
and positive `.intNe` possibility, while a `.boolEq` is a membership test for
one of the two boolean values. All four facts are collected in one pass. -/

/-- A one-pass summary of a domain, sufficient to decide order literals and
boolean pins in O(1). The extremes range over `Value.intView`, which covers
booleans as 0/1; non-int/bool values never satisfy these literals. -/
structure SlotSum where
  minInt : Option Int
  maxInt : Option Int
  hasTrue : Bool
  hasFalse : Bool
  deriving Repr

/-- The neutral summary of the empty domain (also the missing-slot default). -/
def emptySum : SlotSum := ⟨none, none, false, false⟩

/-- One fold step: update the integer extremes from `Value.intView`, then the
boolean memberships. -/
def SlotSum.step (s : SlotSum) (v : Value) : SlotSum :=
  let s :=
    match Value.intView v with
    | some i =>
      { s with
        minInt := some (match s.minInt with | some a => min a i | none => i)
        maxInt := some (match s.maxInt with | some a => max a i | none => i) }
    | none => s
  match v with
  | .bool b => { s with hasTrue := s.hasTrue || b, hasFalse := s.hasFalse || !b }
  | _ => s

/-- The per-domain summary, computed in a single pass. -/
def slotSumOfDomain (d : Domain) : SlotSum := (Dom.enum d).foldl SlotSum.step emptySum

/-- Per-slot summaries, one `slotSumOfDomain` per slot index. -/
def sumsOfArray (a : Array Domain) : Array SlotSum := a.map slotSumOfDomain

/-! ### One-step projections of the combined fold -/

private def minStepV (acc : Option Int) (v : Value) : Option Int :=
  match Value.intView v with
  | some i => some (match acc with | some a => min a i | none => i)
  | none => acc

private def maxStepV (acc : Option Int) (v : Value) : Option Int :=
  match Value.intView v with
  | some i => some (match acc with | some a => max a i | none => i)
  | none => acc

private def bTrueStep (acc : Bool) (v : Value) : Bool :=
  acc || (match v with | .bool true => true | _ => false)

private def bFalseStep (acc : Bool) (v : Value) : Bool :=
  acc || (match v with | .bool false => true | _ => false)

private theorem foldl_step_minInt (l : List Value) (s : SlotSum) :
    (l.foldl SlotSum.step s).minInt = l.foldl minStepV s.minInt := by
  induction l generalizing s with
  | nil => rfl
  | cons v rest ih =>
    show (rest.foldl SlotSum.step (SlotSum.step s v)).minInt =
      rest.foldl minStepV (minStepV s.minInt v)
    rw [ih (SlotSum.step s v)]
    congr 1
    cases v <;> rfl

private theorem foldl_step_maxInt (l : List Value) (s : SlotSum) :
    (l.foldl SlotSum.step s).maxInt = l.foldl maxStepV s.maxInt := by
  induction l generalizing s with
  | nil => rfl
  | cons v rest ih =>
    show (rest.foldl SlotSum.step (SlotSum.step s v)).maxInt =
      rest.foldl maxStepV (maxStepV s.maxInt v)
    rw [ih (SlotSum.step s v)]
    congr 1
    cases v <;> rfl

private theorem foldl_step_hasTrue (l : List Value) (s : SlotSum) :
    (l.foldl SlotSum.step s).hasTrue = l.foldl bTrueStep s.hasTrue := by
  induction l generalizing s with
  | nil => rfl
  | cons v rest ih =>
    show (rest.foldl SlotSum.step (SlotSum.step s v)).hasTrue =
      rest.foldl bTrueStep (bTrueStep s.hasTrue v)
    rw [ih (SlotSum.step s v)]
    congr 1
    cases v with
    | bool b => cases b <;> simp [bTrueStep, SlotSum.step, Value.intView]
    | int i => simp [bTrueStep, SlotSum.step, Value.intView]
    | setOfInt s => simp [bTrueStep, SlotSum.step, Value.intView]
    | array a => simp [bTrueStep, SlotSum.step, Value.intView]

private theorem foldl_step_hasFalse (l : List Value) (s : SlotSum) :
    (l.foldl SlotSum.step s).hasFalse = l.foldl bFalseStep s.hasFalse := by
  induction l generalizing s with
  | nil => rfl
  | cons v rest ih =>
    show (rest.foldl SlotSum.step (SlotSum.step s v)).hasFalse =
      rest.foldl bFalseStep (bFalseStep s.hasFalse v)
    rw [ih (SlotSum.step s v)]
    congr 1
    cases v with
    | bool b => cases b <;> simp [bFalseStep, SlotSum.step, Value.intView]
    | int i => simp [bFalseStep, SlotSum.step, Value.intView]
    | setOfInt s => simp [bFalseStep, SlotSum.step, Value.intView]
    | array a => simp [bFalseStep, SlotSum.step, Value.intView]

/-! ### Folds over the view image -/

private theorem foldl_min_eq (l : List Int) (a : Int) :
    l.foldl min a = l.min?.elim a (min a) := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, List.min?_cons, ih (min a x)]
    cases hm : xs.min? with
    | none => rfl
    | some m => simp only [Option.elim_some]; rw [Int.min_assoc]

private theorem foldl_max_eq (l : List Int) (a : Int) :
    l.foldl max a = l.max?.elim a (max a) := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, List.max?_cons, ih (max a x)]
    cases hm : xs.max? with
    | none => rfl
    | some m => simp only [Option.elim_some]; rw [Int.max_assoc]

private theorem foldl_minStepV_some (l : List Value) (a : Int) :
    l.foldl minStepV (some a) = some ((l.filterMap Value.intView).foldl min a) := by
  induction l generalizing a with
  | nil => rfl
  | cons v rest ih =>
    show rest.foldl minStepV (minStepV (some a) v) =
      some ((v :: rest).filterMap Value.intView |>.foldl min a)
    cases hv : Value.intView v with
    | none =>
      rw [show minStepV (some a) v = some a from by simp [minStepV, hv], ih a]
      simp [hv]
    | some i =>
      rw [show minStepV (some a) v = some (min a i) from by simp [minStepV, hv], ih (min a i)]
      simp only [List.filterMap_cons, hv, List.foldl_cons]

private theorem foldl_maxStepV_some (l : List Value) (a : Int) :
    l.foldl maxStepV (some a) = some ((l.filterMap Value.intView).foldl max a) := by
  induction l generalizing a with
  | nil => rfl
  | cons v rest ih =>
    show rest.foldl maxStepV (maxStepV (some a) v) =
      some ((v :: rest).filterMap Value.intView |>.foldl max a)
    cases hv : Value.intView v with
    | none =>
      rw [show maxStepV (some a) v = some a from by simp [maxStepV, hv], ih a]
      simp [hv]
    | some i =>
      rw [show maxStepV (some a) v = some (max a i) from by simp [maxStepV, hv], ih (max a i)]
      simp only [List.filterMap_cons, hv, List.foldl_cons]

private theorem foldl_minStepV_none (l : List Value) :
    l.foldl minStepV none = (l.filterMap Value.intView).min? := by
  induction l with
  | nil => rfl
  | cons v rest ih =>
    show rest.foldl minStepV (minStepV none v) = ((v :: rest).filterMap Value.intView).min?
    cases hv : Value.intView v with
    | none =>
      rw [show minStepV none v = none from by simp [minStepV, hv], ih]
      simp [hv]
    | some i =>
      rw [show minStepV none v = some i from by simp [minStepV, hv],
        foldl_minStepV_some rest i, List.filterMap_cons, hv, List.min?_cons]
      exact congrArg some (foldl_min_eq (rest.filterMap Value.intView) i)

private theorem foldl_maxStepV_none (l : List Value) :
    l.foldl maxStepV none = (l.filterMap Value.intView).max? := by
  induction l with
  | nil => rfl
  | cons v rest ih =>
    show rest.foldl maxStepV (maxStepV none v) = ((v :: rest).filterMap Value.intView).max?
    cases hv : Value.intView v with
    | none =>
      rw [show maxStepV none v = none from by simp [maxStepV, hv], ih]
      simp [hv]
    | some i =>
      rw [show maxStepV none v = some i from by simp [maxStepV, hv],
        foldl_maxStepV_some rest i, List.filterMap_cons, hv, List.max?_cons]
      exact congrArg some (foldl_max_eq (rest.filterMap Value.intView) i)

/-! ### Boolean membership flags -/

private theorem foldl_bTrueStep_true (l : List Value) : l.foldl bTrueStep true = true := by
  induction l with
  | nil => rfl
  | cons v rest ih =>
    show rest.foldl bTrueStep (bTrueStep true v) = true
    exact ih

private theorem foldl_bFalseStep_true (l : List Value) : l.foldl bFalseStep true = true := by
  induction l with
  | nil => rfl
  | cons v rest ih =>
    show rest.foldl bFalseStep (bFalseStep true v) = true
    exact ih

private theorem foldl_bTrueStep_false_iff (l : List Value) :
    l.foldl bTrueStep false = true ↔ Value.bool true ∈ l := by
  induction l with
  | nil => simp
  | cons v rest ih =>
    show rest.foldl bTrueStep (bTrueStep false v) = true ↔ Value.bool true ∈ v :: rest
    cases v with
    | bool b =>
      cases b with
      | true => simp [bTrueStep, foldl_bTrueStep_true]
      | false => simpa [bTrueStep] using ih
    | int i => simpa [bTrueStep] using ih
    | setOfInt s => simpa [bTrueStep] using ih
    | array a => simpa [bTrueStep] using ih

private theorem foldl_bFalseStep_false_iff (l : List Value) :
    l.foldl bFalseStep false = true ↔ Value.bool false ∈ l := by
  induction l with
  | nil => simp
  | cons v rest ih =>
    show rest.foldl bFalseStep (bFalseStep false v) = true ↔ Value.bool false ∈ v :: rest
    cases v with
    | bool b =>
      cases b with
      | true => simpa [bFalseStep] using ih
      | false => simp [bFalseStep, foldl_bFalseStep_true]
    | int i => simpa [bFalseStep] using ih
    | setOfInt s => simpa [bFalseStep] using ih
    | array a => simpa [bFalseStep] using ih

/-! ### The summary characterizations -/

private theorem slotSumOfDomain_minInt (d : Domain) :
    (slotSumOfDomain d).minInt = ((Dom.enum d).filterMap Value.intView).min? := by
  unfold slotSumOfDomain
  rw [foldl_step_minInt (Dom.enum d) emptySum]
  exact foldl_minStepV_none (Dom.enum d)

private theorem slotSumOfDomain_maxInt (d : Domain) :
    (slotSumOfDomain d).maxInt = ((Dom.enum d).filterMap Value.intView).max? := by
  unfold slotSumOfDomain
  rw [foldl_step_maxInt (Dom.enum d) emptySum]
  exact foldl_maxStepV_none (Dom.enum d)

private theorem slotSumOfDomain_hasTrue (d : Domain) :
    (slotSumOfDomain d).hasTrue = true ↔ Value.bool true ∈ Dom.enum d := by
  unfold slotSumOfDomain
  rw [foldl_step_hasTrue (Dom.enum d) emptySum]
  exact foldl_bTrueStep_false_iff (Dom.enum d)

private theorem slotSumOfDomain_hasFalse (d : Domain) :
    (slotSumOfDomain d).hasFalse = true ↔ Value.bool false ∈ Dom.enum d := by
  unfold slotSumOfDomain
  rw [foldl_step_hasFalse (Dom.enum d) emptySum]
  exact foldl_bFalseStep_false_iff (Dom.enum d)

/-- The structural per-domain summary: extrema from the compact
    representation and Boolean membership from the bit pattern, with no
    enumeration of the domain. -/
def slotSumOfDomainFast (d : Domain) : SlotSum :=
  { minInt := Dom.minInt?Fast d
    maxInt := Dom.maxInt?Fast d
    hasTrue := Dom.hasBoolBStruct d true
    hasFalse := Dom.hasBoolBStruct d false }

private theorem any_bool_eq_true_iff (l : List Value) (c : Bool) :
    (l.any (fun v => match v with | .bool b => b == c | _ => false)) = true ↔
      Value.bool c ∈ l := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨v, hv, hvc⟩
    cases v with
    | bool b =>
        rw [beq_iff_eq] at hvc
        subst hvc
        exact hv
    | int i => simp at hvc
    | setOfInt s => simp at hvc
    | array a => simp at hvc
  · intro hv
    exact ⟨Value.bool c, hv, by simp⟩

theorem slotSumOfDomainFast_eq (d : Domain) :
    slotSumOfDomainFast d = slotSumOfDomain d := by
  have hmin : (slotSumOfDomainFast d).minInt = (slotSumOfDomain d).minInt :=
    (Dom.minInt?Fast_eq d).trans (Dom.minInt?_eq_domInts_min d)
      |>.trans (slotSumOfDomain_minInt d).symm
  have hmax : (slotSumOfDomainFast d).maxInt = (slotSumOfDomain d).maxInt :=
    (Dom.maxInt?Fast_eq d).trans (Dom.maxInt?_eq_domInts_max d)
      |>.trans (slotSumOfDomain_maxInt d).symm
  have htru : (slotSumOfDomainFast d).hasTrue = (slotSumOfDomain d).hasTrue := by
    show Dom.hasBoolBStruct d true = (slotSumOfDomain d).hasTrue
    rw [Dom.hasBoolBStruct_eq]
    apply Bool.eq_iff_iff.mpr
    rw [slotSumOfDomain_hasTrue]
    exact any_bool_eq_true_iff (Dom.enum d) true
  have hfal : (slotSumOfDomainFast d).hasFalse = (slotSumOfDomain d).hasFalse := by
    show Dom.hasBoolBStruct d false = (slotSumOfDomain d).hasFalse
    rw [Dom.hasBoolBStruct_eq]
    apply Bool.eq_iff_iff.mpr
    rw [slotSumOfDomain_hasFalse]
    exact any_bool_eq_true_iff (Dom.enum d) false
  cases hf : slotSumOfDomainFast d with
  | mk a b c e =>
    cases hs : slotSumOfDomain d with
    | mk a' b' c' e' =>
      simp only [hf] at hmin hmax htru hfal
      simp only [hs] at hmin hmax htru hfal
      exact (SlotSum.mk.injEq a b c e a' b' c' e').mpr
        ⟨hmin, hmax, htru, hfal⟩

/-- Compiled twin of `sumsOfArray` using the structural summaries. -/
def sumsOfArrayFast (a : Array Domain) : Array SlotSum := a.map slotSumOfDomainFast

theorem sumsOfArrayFast_eq (a : Array Domain) :
    sumsOfArrayFast a = sumsOfArray a := by
  simp [sumsOfArrayFast, sumsOfArray, slotSumOfDomainFast_eq]

attribute [implemented_by sumsOfArrayFast] sumsOfArray

private theorem hasBool_eq_true_iff (d : Domain) (w : Bool) :
    (if w then (slotSumOfDomain d).hasTrue else (slotSumOfDomain d).hasFalse) = true ↔
      Value.bool w ∈ Dom.enum d := by
  cases w with
  | true => exact slotSumOfDomain_hasTrue d
  | false => exact slotSumOfDomain_hasFalse d

private theorem hasBool_eq_false_iff (d : Domain) (w : Bool) :
    (if w then (slotSumOfDomain d).hasTrue else (slotSumOfDomain d).hasFalse) = false ↔
      Value.bool w ∉ Dom.enum d := by
  rw [Bool.eq_false_iff]
  exact not_congr (hasBool_eq_true_iff d w)

/-! ### The O(1) literal test -/

/-- `literalImpossible` decided from a per-slot summary: `.intLe` and positive
`.intNe` literals read `minInt`/`maxInt`, `.boolEq` literals read
`hasTrue`/`hasFalse`, and negative `.intNe` (a membership test the summary
does not decide) falls back to the certified domain walk. -/
def literalImpossibleFast (a : Array Domain) (sums : Array SlotSum) (l : Literal) : Bool :=
  match l.atom, l.positive with
  | .boolEq s expected, positive =>
    let want := if positive then expected else !expected
    !(if want then (sums[s]?.getD emptySum).hasTrue
      else (sums[s]?.getD emptySum).hasFalse)
  | .intLe s k, true =>
    match (sums[s]?.getD emptySum).minInt with
    | some lo => decide (k < lo)
    | none => true
  | .intLe s k, false =>
    match (sums[s]?.getD emptySum).maxInt with
    | some hi => decide (hi ≤ k)
    | none => true
  | .intNe s v, true =>
    let sc := sums[s]?.getD emptySum
    match sc.minInt, sc.maxInt with
    | some lo, some hi => lo == v && hi == v
    | _, _ => true
  | .intNe s v, false =>
    let d := a[s]?.getD Dom.empty
    if Dom.allIntBStruct d then !Dom.memBool d (Value.int v)
    else literalImpossibleArr a l

/-! ### Pointwise truth lemmas for `Value.intView` predicates -/

private theorem intLe_pos_valueHolds_eq_false_iff (v : Value) (s : Nat) (k : Int) :
    Literal.valueHolds ⟨.intLe s k, true⟩ v = false ↔
      ∀ i, Value.intView v = some i → k < i := by
  cases hv : Value.intView v with
  | none => simp [Literal.valueHolds, hv]
  | some i => simp [Literal.valueHolds, hv]

private theorem intLe_neg_valueHolds_eq_false_iff (v : Value) (s : Nat) (k : Int) :
    Literal.valueHolds ⟨.intLe s k, false⟩ v = false ↔
      ∀ i, Value.intView v = some i → i ≤ k := by
  cases hv : Value.intView v with
  | none => simp [Literal.valueHolds, hv]
  | some i => simp [Literal.valueHolds, hv]

private theorem intNe_pos_valueHolds_eq_false_iff (v : Value) (s : Nat) (k : Int) :
    Literal.valueHolds ⟨.intNe s k, true⟩ v = false ↔
      ∀ i, Value.intView v = some i → i = k := by
  cases hv : Value.intView v with
  | none => simp [Literal.valueHolds, hv]
  | some i => simp [Literal.valueHolds, hv]

private theorem boolEq_valueHolds_eq_true_iff (v : Value) (s : Nat) (expected positive : Bool) :
    Literal.valueHolds ⟨.boolEq s expected, positive⟩ v = true ↔
      v = Value.bool (if positive then expected else !expected) := by
  cases v <;> cases positive <;> cases expected <;> simp [Literal.valueHolds]

/-! ### The domain-level characterizations -/

private theorem all_intLe_pos_eq_decide (d : Domain) (s : Nat) (k : Int) :
    ((Dom.enum d).all fun v => !(Literal.valueHolds ⟨.intLe s k, true⟩ v)) =
      decide (∀ i ∈ (Dom.enum d).filterMap Value.intView, k < i) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [List.all_eq_true]
  constructor
  · intro h i hi
    obtain ⟨v, hv, hiv⟩ := List.mem_filterMap.mp hi
    have hvv := h v hv
    rw [Bool.not_eq_true'] at hvv
    exact (intLe_pos_valueHolds_eq_false_iff v s k).mp hvv i hiv
  · intro h v hv
    rw [Bool.not_eq_true']
    exact (intLe_pos_valueHolds_eq_false_iff v s k).mpr fun i hi =>
      h i (List.mem_filterMap.mpr ⟨v, hv, hi⟩)

private theorem all_intLe_neg_eq_decide (d : Domain) (s : Nat) (k : Int) :
    ((Dom.enum d).all fun v => !(Literal.valueHolds ⟨.intLe s k, false⟩ v)) =
      decide (∀ i ∈ (Dom.enum d).filterMap Value.intView, i ≤ k) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [List.all_eq_true]
  constructor
  · intro h i hi
    obtain ⟨v, hv, hiv⟩ := List.mem_filterMap.mp hi
    have hvv := h v hv
    rw [Bool.not_eq_true'] at hvv
    exact (intLe_neg_valueHolds_eq_false_iff v s k).mp hvv i hiv
  · intro h v hv
    rw [Bool.not_eq_true']
    exact (intLe_neg_valueHolds_eq_false_iff v s k).mpr fun i hi =>
      h i (List.mem_filterMap.mpr ⟨v, hv, hi⟩)

private theorem all_intNe_pos_eq_decide (d : Domain) (s : Nat) (k : Int) :
    ((Dom.enum d).all fun v => !(Literal.valueHolds ⟨.intNe s k, true⟩ v)) =
      decide (∀ i ∈ (Dom.enum d).filterMap Value.intView, i = k) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [List.all_eq_true]
  constructor
  · intro h i hi
    obtain ⟨v, hv, hiv⟩ := List.mem_filterMap.mp hi
    have hvv := h v hv
    rw [Bool.not_eq_true'] at hvv
    exact (intNe_pos_valueHolds_eq_false_iff v s k).mp hvv i hiv
  · intro h v hv
    rw [Bool.not_eq_true']
    exact (intNe_pos_valueHolds_eq_false_iff v s k).mpr fun i hi =>
      h i (List.mem_filterMap.mpr ⟨v, hv, hi⟩)

private theorem all_boolEq_eq_false_iff (d : Domain) (s : Nat) (expected positive : Bool) :
    ((Dom.enum d).all fun v => !(Literal.valueHolds ⟨.boolEq s expected, positive⟩ v)) = true ↔
      Value.bool (if positive then expected else !expected) ∉ Dom.enum d := by
  rw [List.all_eq_true]
  constructor
  · intro h hmem
    have hvv := h _ hmem
    rw [Bool.not_eq_true'] at hvv
    have h2 : Literal.valueHolds ⟨.boolEq s expected, positive⟩
        (Value.bool (if positive then expected else !expected)) = true :=
      (boolEq_valueHolds_eq_true_iff _ s expected positive).mpr rfl
    simp [hvv] at h2
  · intro hn v hv
    rw [Bool.not_eq_true', Bool.eq_false_iff]
    intro hvh
    exact hn (by rwa [← (boolEq_valueHolds_eq_true_iff v s expected positive).mp hvh])

private theorem minInt_decide_eq_decide (d : Domain) (k : Int) :
    (match (slotSumOfDomain d).minInt with
     | some lo => decide (k < lo)
     | none => true) =
      decide (∀ i ∈ (Dom.enum d).filterMap Value.intView, k < i) := by
  cases hm : (slotSumOfDomain d).minInt with
  | none =>
    have hnil : (Dom.enum d).filterMap Value.intView = [] :=
      List.min?_eq_none_iff.mp (by rw [← slotSumOfDomain_minInt]; exact hm)
    rw [hnil]
    simp
  | some lo =>
    have hiff := List.min?_eq_some_iff.mp (by rw [← slotSumOfDomain_minInt]; exact hm)
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro hk i hi
      have hle := hiff.2 i hi
      omega
    · intro h
      exact h lo hiff.1

private theorem maxInt_decide_eq_decide (d : Domain) (k : Int) :
    (match (slotSumOfDomain d).maxInt with
     | some hi => decide (hi ≤ k)
     | none => true) =
      decide (∀ i ∈ (Dom.enum d).filterMap Value.intView, i ≤ k) := by
  cases hm : (slotSumOfDomain d).maxInt with
  | none =>
    have hnil : (Dom.enum d).filterMap Value.intView = [] :=
      List.max?_eq_none_iff.mp (by rw [← slotSumOfDomain_maxInt]; exact hm)
    rw [hnil]
    simp
  | some hi =>
    have hiff := List.max?_eq_some_iff.mp (by rw [← slotSumOfDomain_maxInt]; exact hm)
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro h i hi_mem
      have hle := hiff.2 i hi_mem
      omega
    · intro h
      exact h hi hiff.1

private theorem minMax_decide_eq_decide (d : Domain) (k : Int) :
    (match (slotSumOfDomain d).minInt, (slotSumOfDomain d).maxInt with
     | some lo, some hi => lo == k && hi == k
     | _, _ => true) =
      decide (∀ i ∈ (Dom.enum d).filterMap Value.intView, i = k) := by
  cases hm : (slotSumOfDomain d).minInt with
  | none =>
    have hnil : (Dom.enum d).filterMap Value.intView = [] :=
      List.min?_eq_none_iff.mp (by rw [← slotSumOfDomain_minInt]; exact hm)
    rw [hnil]
    simp
  | some lo =>
    cases hM : (slotSumOfDomain d).maxInt with
    | none =>
      have hnil : (Dom.enum d).filterMap Value.intView = [] :=
        List.max?_eq_none_iff.mp (by rw [← slotSumOfDomain_maxInt]; exact hM)
      rw [hnil]
      simp
    | some hi =>
      have hlo := List.min?_eq_some_iff.mp (by rw [← slotSumOfDomain_minInt]; exact hm)
      have hhi := List.max?_eq_some_iff.mp (by rw [← slotSumOfDomain_maxInt]; exact hM)
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, Bool.and_eq_true]
      constructor
      · intro h i hi_mem
        have hlo_eq : lo = k := beq_iff_eq.mp h.1
        have hhi_eq : hi = k := beq_iff_eq.mp h.2
        have hle_hi : i ≤ hi := hhi.2 i hi_mem
        have hge_lo : lo ≤ i := hlo.2 i hi_mem
        omega
      · intro h
        exact ⟨beq_iff_eq.mpr (h lo hlo.1), beq_iff_eq.mpr (h hi hhi.1)⟩

/-- **EQUIVALENCE (fast literal form)**: the summary-driven literal test is
the certified `literalImpossible` at the same slot index — for every frame
slot array, i.e. for every domain. -/
private theorem all_intNe_neg_eq_of_allInt (d : Domain) (s : Nat) (k : Int)
    (hint : ∀ w ∈ Dom.enum d, ∃ i : Int, w = Value.int i) :
    ((Dom.enum d).all fun w => !(Literal.valueHolds ⟨.intNe s k, false⟩ w)) =
      !Dom.memBool d (Value.int k) := by
  by_cases h : Value.int k ∈ Dom.enum d
  · have hb : Dom.memBool d (Value.int k) = true := (Dom.memBool_iff d _).mpr h
    rw [hb, Bool.not_true, Bool.eq_false_iff]
    intro hall
    rw [List.all_eq_true] at hall
    have hh := hall _ h
    rw [Bool.not_eq_true', Dom.valueHolds_intNe_neg] at hh
    exact absurd hh (by simp)
  · have hb : Dom.memBool d (Value.int k) = false := by
      cases hm : Dom.memBool d (Value.int k) with
      | false => rfl
      | true => exact absurd ((Dom.memBool_iff d _).mp hm) h
    rw [hb, Bool.not_false]
    rw [List.all_eq_true]
    intro w hw
    obtain ⟨i, rfl⟩ := hint w hw
    rw [Bool.not_eq_true', Dom.valueHolds_intNe_neg, decide_eq_false_iff_not]
    intro hik
    exact h (hik ▸ hw)

theorem literalImpossibleFast_eq (a : Array Domain) (l : Literal) :
    literalImpossibleFast a (sumsOfArray a) l = literalImpossibleArr a l := by
  obtain ⟨atom, positive⟩ := l
  cases atom with
  | boolEq s expected =>
    cases positive with
    | true =>
      simp only [literalImpossibleFast, literalImpossibleArr, sumsOfArray,
        Array.getElem?_map, Atom.slot]
      cases ha : a[s]? with
      | none => simp [emptySum, Dom.enum_empty]
      | some d =>
        apply Bool.eq_iff_iff.mpr
        rw [Bool.not_eq_true']
        exact (hasBool_eq_false_iff d _).trans
          (all_boolEq_eq_false_iff d s expected true).symm
    | false =>
      simp only [literalImpossibleFast, literalImpossibleArr, sumsOfArray,
        Array.getElem?_map, Atom.slot]
      cases ha : a[s]? with
      | none => simp [emptySum, Dom.enum_empty]
      | some d =>
        apply Bool.eq_iff_iff.mpr
        rw [Bool.not_eq_true']
        exact (hasBool_eq_false_iff d _).trans
          (all_boolEq_eq_false_iff d s expected false).symm
  | intLe s k =>
    cases positive with
    | true =>
      simp only [literalImpossibleFast, literalImpossibleArr, sumsOfArray,
        Array.getElem?_map, Atom.slot]
      cases ha : a[s]? with
      | none => simp [emptySum, Dom.enum_empty]
      | some d =>
        exact (minInt_decide_eq_decide d k).trans (all_intLe_pos_eq_decide d s k).symm
    | false =>
      simp only [literalImpossibleFast, literalImpossibleArr, sumsOfArray,
        Array.getElem?_map, Atom.slot]
      cases ha : a[s]? with
      | none => simp [emptySum, Dom.enum_empty]
      | some d =>
        exact (maxInt_decide_eq_decide d k).trans (all_intLe_neg_eq_decide d s k).symm
  | intNe s v =>
    cases positive with
    | true =>
      simp only [literalImpossibleFast, literalImpossibleArr, sumsOfArray,
        Array.getElem?_map, Atom.slot]
      cases ha : a[s]? with
      | none => simp [emptySum, Dom.enum_empty]
      | some d =>
        exact (minMax_decide_eq_decide d v).trans (all_intNe_pos_eq_decide d s v).symm
    | false =>
      simp only [literalImpossibleFast, literalImpossibleArr, Atom.slot]
      by_cases hb : Dom.allIntBStruct (a[s]?.getD Dom.empty) = true
      · rw [if_pos hb]
        exact (all_intNe_neg_eq_of_allInt (a[s]?.getD Dom.empty) s v
          (fun w hw => (Dom.allIntB_iff _).mp
            (by rw [← Dom.allIntBStruct_eq_allIntB]; exact hb) w hw)).symm
      · rw [if_neg hb]

/-! ## First-order clause classification -/

/-- The compressed remaining set: `none` = no remaining literal (the scan
reports a conflict on the clause), `some (some l)` = exactly one remaining
(the first one, in clause order), `some none` = at least two remaining. -/
def reduceRemaining : Clause → Option (Option Literal)
  | [] => none
  | [l] => some (some l)
  | _ => some none

/-- First-order classification of one clause against a slot index: the
`acc` carries the first remaining literal seen so far. Runs in clause order,
short-circuits at the second remaining literal, and allocates nothing. -/
def clauseClassify (a : Array Domain) : List Literal → Option Literal → Option (Option Literal)
  | [], none => none
  | [], some l => some (some l)
  | l :: ls, acc =>
    match literalImpossibleArr a l with
    | true => clauseClassify a ls acc
    | false =>
      match acc with
      | none => clauseClassify a ls (some l)
      | some _ => some none

/-- **EQUIVALENCE (one remaining already seen)**: with a remaining literal
already recorded, the classifier reports `some (some l₀)` iff no further
remaining literal exists and `some none` otherwise — exactly the compressed
remaining set of the certified `clauseRemaining`. -/
theorem clauseClassify_some (a : Array Domain) (f : BranchFrame) (c : Clause)
    (l₀ : Literal)
    (h : ∀ l ∈ c, literalImpossibleArr a l = literalImpossible f l) :
    clauseClassify a c (some l₀)
      = (match c.filter (fun l => !literalImpossible f l) with
         | [] => some (some l₀)
         | _ => some none) := by
  induction c with
  | nil => rfl
  | cons l ls ih =>
      have hl : literalImpossibleArr a l = literalImpossible f l :=
        h l (List.mem_cons_self ..)
      have hls : ∀ q ∈ ls, literalImpossibleArr a q = literalImpossible f q :=
        fun q hq => h q (List.mem_cons_of_mem _ hq)
      rw [clauseClassify, hl]
      by_cases himp : literalImpossible f l = true
      · rw [himp]
        rw [List.filter_cons_of_neg (p := fun l => !literalImpossible f l) (by simp [himp])]
        rw [ih hls]
      · have hf : literalImpossible f l = false := Bool.eq_false_iff.mpr himp
        rw [hf]
        rw [List.filter_cons_of_pos (p := fun l => !literalImpossible f l) (by simp [hf])]

/-- **EQUIVALENCE (no remaining literal seen)**: the first-order classifier at
the start state IS the compressed remaining set of the certified
`clauseRemaining` (i.e. of `c.filter (¬literalImpossible)`). -/
theorem clauseClassify_none (a : Array Domain) (f : BranchFrame) (c : Clause)
    (h : ∀ l ∈ c, literalImpossibleArr a l = literalImpossible f l) :
    clauseClassify a c none = reduceRemaining (c.filter (fun l => !literalImpossible f l)) := by
  induction c with
  | nil => rfl
  | cons l ls ih =>
      have hl : literalImpossibleArr a l = literalImpossible f l :=
        h l (List.mem_cons_self ..)
      have hls : ∀ q ∈ ls, literalImpossibleArr a q = literalImpossible f q :=
        fun q hq => h q (List.mem_cons_of_mem _ hq)
      rw [clauseClassify, hl]
      by_cases himp : literalImpossible f l = true
      · rw [himp]
        rw [List.filter_cons_of_neg (p := fun l => !literalImpossible f l) (by simp [himp])]
        rw [ih hls]
      · have hf : literalImpossible f l = false := Bool.eq_false_iff.mpr himp
        rw [hf]
        rw [List.filter_cons_of_pos (p := fun l => !literalImpossible f l) (by simp [hf])]
        rw [clauseClassify_some a f ls l hls]
        cases hq : ls.filter (fun l => !literalImpossible f l) with
        | nil => simp only [hq, reduceRemaining]
        | cons q qs => simp only [hq, reduceRemaining]

/-- The summary-driven twin of `clauseClassify`: identical recursion, calling
`literalImpossibleFast a sums` instead of `literalImpossibleArr a`. -/
def clauseClassifyFast (a : Array Domain) (sums : Array SlotSum) :
    List Literal → Option Literal → Option (Option Literal)
  | [], none => none
  | [], some l => some (some l)
  | l :: ls, acc =>
    match literalImpossibleFast a sums l with
    | true => clauseClassifyFast a sums ls acc
    | false =>
      match acc with
      | none => clauseClassifyFast a sums ls (some l)
      | some _ => some none

/-- **EQUIVALENCE (fast classifier, one remaining already seen)**: same
statement as `clauseClassify_some` with the summary-driven literal test. -/
theorem clauseClassifyFast_some (a : Array Domain) (sums : Array SlotSum)
    (f : BranchFrame) (c : Clause) (l₀ : Literal)
    (h : ∀ l ∈ c, literalImpossibleFast a sums l = literalImpossible f l) :
    clauseClassifyFast a sums c (some l₀)
      = (match c.filter (fun l => !literalImpossible f l) with
         | [] => some (some l₀)
         | _ => some none) := by
  induction c with
  | nil => rfl
  | cons l ls ih =>
      have hl : literalImpossibleFast a sums l = literalImpossible f l :=
        h l (List.mem_cons_self ..)
      have hls : ∀ q ∈ ls, literalImpossibleFast a sums q = literalImpossible f q :=
        fun q hq => h q (List.mem_cons_of_mem _ hq)
      rw [clauseClassifyFast, hl]
      by_cases himp : literalImpossible f l = true
      · rw [himp]
        rw [List.filter_cons_of_neg (p := fun l => !literalImpossible f l) (by simp [himp])]
        rw [ih hls]
      · have hf : literalImpossible f l = false := Bool.eq_false_iff.mpr himp
        rw [hf]
        rw [List.filter_cons_of_pos (p := fun l => !literalImpossible f l) (by simp [hf])]

/-- **EQUIVALENCE (fast classifier, no remaining literal seen)**: same
statement as `clauseClassify_none` with the summary-driven literal test. -/
theorem clauseClassifyFast_none (a : Array Domain) (sums : Array SlotSum)
    (f : BranchFrame) (c : Clause)
    (h : ∀ l ∈ c, literalImpossibleFast a sums l = literalImpossible f l) :
    clauseClassifyFast a sums c none =
      reduceRemaining (c.filter (fun l => !literalImpossible f l)) := by
  induction c with
  | nil => rfl
  | cons l ls ih =>
      have hl : literalImpossibleFast a sums l = literalImpossible f l :=
        h l (List.mem_cons_self ..)
      have hls : ∀ q ∈ ls, literalImpossibleFast a sums q = literalImpossible f q :=
        fun q hq => h q (List.mem_cons_of_mem _ hq)
      rw [clauseClassifyFast, hl]
      by_cases himp : literalImpossible f l = true
      · rw [himp]
        rw [List.filter_cons_of_neg (p := fun l => !literalImpossible f l) (by simp [himp])]
        rw [ih hls]
      · have hf : literalImpossible f l = false := Bool.eq_false_iff.mpr himp
        rw [hf]
        rw [List.filter_cons_of_pos (p := fun l => !literalImpossible f l) (by simp [hf])]
        rw [clauseClassifyFast_some a sums f ls l hls]
        cases ls.filter (fun l => !literalImpossible f l) with
        | nil => simp only [reduceRemaining]
        | cons q qs => simp only [reduceRemaining]

/-! ## The optimised database scan -/

/-- The optimised scan recursion: the certified `scanDatabase` with a
prebuilt slot index, per-slot summaries, the summary-driven clause
classifier and the fused (productivity-equivalent) `productiveFast` gate.
Same recursion order, same event payloads, same `original.contains` flag. -/
private def scanDatabaseIndexed (original : List Clause) (f : BranchFrame)
    (a : Array Domain) (sums : Array SlotSum) : List Clause → PruningEvent
  | [] => .stable
  | c :: rest =>
    match clauseClassifyFast a sums c none with
    | none => .conflict [c]
    | some none => scanDatabaseIndexed original f a sums rest
    | some (some l) =>
        match productiveFast l f with
        | true => .implied l c false (!(original.contains c))
        | false => scanDatabaseIndexed original f a sums rest

/-- The indexed scan recursion agrees with the certified `scanDatabase` at
any slot index whose summaries classify exactly like `literalImpossible`. -/
private theorem scanDatabaseIndexed_eq (original : List Clause) (f : BranchFrame)
    (a : Array Domain) (sums : Array SlotSum)
    (h : ∀ l, literalImpossibleFast a sums l = literalImpossible f l) (db : List Clause) :
    scanDatabaseIndexed original f a sums db = scanDatabase original f db := by
  induction db with
  | nil => rfl
  | cons c rest ih =>
      rw [scanDatabaseIndexed, scanDatabase]
      rw [clauseClassifyFast_none a sums f c (fun l _ => h l)]
      rw [show c.filter (fun l => !literalImpossible f l) = clauseRemaining f c from rfl]
      cases hr : clauseRemaining f c with
      | nil => simp only [reduceRemaining]
      | cons x xs =>
          cases xs with
          | nil =>
              simp only [reduceRemaining]
              rw [productiveFast_eq x f]
              by_cases hp : productive x f = true
              · rw [hp]
                simp
              · rw [Bool.eq_false_iff.mpr hp]
                simp only [Bool.false_eq_true, ↓reduceIte]
                exact ih
          | cons y ys =>
              exact ih

/-- The optimised scan: the certified `scanDatabase` recursion over the
summary-driven classifier. Builds the per-slot index and its summaries ONCE
per scan (`sumsOfArray`, one pass per domain) and then classifies every
visited clause literal in O(1) except negative `.intNe`, which falls back to
the certified domain walk. Same recursion order, same event payloads, same
`original.contains` flag. -/
def scanDatabaseFastAux (original : List Clause) (f : BranchFrame) (a : Array Domain)
    (db : List Clause) : PruningEvent :=
  scanDatabaseIndexed original f a (sumsOfArray a) db

/-- **THE EQUALITY THEOREM (P1b DoD, indexed form)**: at any slot index that
agrees with `literalImpossible` pointwise, the optimised scan returns exactly
the certified `scanDatabase` event. -/
theorem scanDatabaseFastAux_eq (original : List Clause) (f : BranchFrame)
    (a : Array Domain)
    (h : ∀ l, literalImpossibleArr a l = literalImpossible f l) (db : List Clause) :
    scanDatabaseFastAux original f a db = scanDatabase original f db := by
  unfold scanDatabaseFastAux
  exact scanDatabaseIndexed_eq original f a (sumsOfArray a)
    (fun l => (literalImpossibleFast_eq a l).trans (h l)) db

/-- The hybrid database scan — the wired fast scan of
`nextPruningEventSched`. The indexed branch BUILDS the slot index once
(`frameDomainArray`, one full pass over every domain value: ~143 ms per step
on the wide measured instance above) plus the per-slot summaries, which only
pays off on a database long enough to amortise it; the certified reference
`scanDatabase` allocates nothing. The literal threshold `8` is the measured
crossover: for `db.length ≤ 8` the reference scan is cheaper, otherwise the
indexed scan runs. `if` only evaluates the taken branch, so the small branch
never builds the array. Both branches are the certified `scanDatabase` event
(`scanDatabaseFast_eq`), so this is purely a performance knob. -/
def scanDatabaseFast (original : List Clause) (f : BranchFrame) (db : List Clause) :
    PruningEvent :=
  if db.length ≤ 8 then scanDatabase original f db
  else scanDatabaseFastAux original f (frameDomainArray f) db

/-- **THE EQUALITY THEOREM (P1b DoD)**: the optimised database scan returns
EXACTLY the certified `scanDatabase` event — on every frame, every database
and every original clause list; no invariant, no side condition. The hybrid
dispatch cannot change this: the small branch IS `scanDatabase`, and the
indexed branch is `scanDatabaseFastAux_eq`. -/
theorem scanDatabaseFast_eq (original : List Clause) (f : BranchFrame)
    (db : List Clause) :
    scanDatabaseFast original f db = scanDatabase original f db := by
  unfold scanDatabaseFast
  by_cases h : db.length ≤ 8
  · rw [if_pos h]
  · rw [if_neg h]
    exact scanDatabaseFastAux_eq original f (frameDomainArray f)
      (fun l => literalImpossibleArr_eq f l) db

end LeanFzn.Solver.Propagation

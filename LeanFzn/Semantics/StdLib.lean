import LeanFzn.Semantics.Model
open LeanFzn.Semantics


/-!
# Standard FlatZinc predicate library

Signatures (`stdSig`) and mathematical interpretations (`stdInterp`) for the
standard FlatZinc builtins of the integer/Boolean/set fragment (no floats),
following the MiniZinc 2.10.0 FlatZinc specification's standard-predicate
table (the vendored `lib-flatzinc-*.html` pages, inventoried in
`specification/minizinc-2.10.0/predicates_and_globals_report.md`).

`stdSig` is a `SigEnv`: it can be passed to `wellFormedB` so that models
using standard predicates are statically checked against their official
signatures.  `stdInterp` is a `PredicateInterpretation`: it gives each
predicate its intended mathematical meaning, so `Satisfies stdSig stdInterp
m store` states that `store` solves `m` under the standard semantics.

## Sources of semantics

The meaning of each builtin follows, in order of precedence: (1) the
vendored handbook pages; (2) the pinned stdlib decompositions; (3)
reference-LeanFzn.Solver behavior where both are loose.  The decisions that
went beyond a literal reading — truncated `int_div`/`int_mod`,
`int_pow` at corner exponents, the lexicographic reading of
`set_le`/`set_lt`, `nonshifted` element variants coinciding with the
plain forms on `1..n` arrays — are recorded with their justifications
in `specification/flatzinc_specification_assumptions.md`, G-series
(G2, G4, G5, G6); per-predicate citations appear at each definition
below.

Interpretations are written to be decidable wherever practical: computable
Boolean helpers (`Value.eqB`, `valuesAllDifferent`, `dotProduct`, …) are
used instead of quantifiers over infinite domains, so the tests in
`Tests/Semantics/StdLib.lean` can evaluate them with `decide`.

The set predicates whose meaning is inherently extensional (`set_eq`,
`set_subset`, `set_union`, `set_intersect`, `set_diff`, the set
comparisons `set_ne`, `set_le`, `set_lt`, `set_superset`, `set_symdiff`
with their reified variants, and the set-valued element constraints
`array_set_element`, `array_var_set_element`,
`array_var_set_element_nonshifted`) quantify over all integers (or
compare whole sets), are not computable here, and have **no case in
`stdInterpB`**; their executable twins live in `FznSolution.lean`'s
`interpB`, which decides them by enumerating the finitely many elements
of each `IntSetValue`.

## Agreement proofs

Every builtin handled by `stdInterpB` has a per-name agreement theorem
`builtin_<name>_iff` proving

`stdInterpB (Ident.mk "<name>") args = true ↔ stdInterp (Ident.mk "<name>") args`,

derived from one generic *shape* lemma per argument shape (`agreeII`,
`agreeIII`, …) by a single `exact`.  The dispatcher `stdInterpB_agree` in
`FznSolution.lean` case-splits on the `stdNames` list and applies these
lemmas, so no monolithic case analysis over both names and argument
shapes is needed.
-/

open LeanFzn.Semantics

namespace LeanFzn.Semantics

open LeanFzn

/-! ## Computable helpers -/

/-- Structural equality test on integer sets. -/
def IntSetValue.eqB : IntSetValue → IntSetValue → Bool
  | .enumeration xs, .enumeration ys =>
      xs.length == ys.length &&
        (xs.zip ys).all (fun (a, b) => a == b)
  | .interval lo hi, .interval lo' hi' => lo == lo' && hi == hi'
  | _, _ => false

/- Structural equality test on values, and on lists of values (arrays
    compare elementwise).  Defined mutually so the recursion is
    first-order. -/
mutual
  def Value.eqB : Value → Value → Bool
    | .bool a, .bool b => a == b
    | .int a, .int b => a == b
    | .setOfInt a, .setOfInt b => a.eqB b
    | .array xs, .array ys => valuesEqB xs ys
    | _, _ => false

  def valuesEqB : List Value → List Value → Bool
    | [], [] => true
    | x :: xs, y :: ys => x.eqB y && valuesEqB xs ys
    | _, _ => false
end

/-- Cardinality of an integer set: number of *distinct* elements of an
    enumeration (`{1,1}` has one element), size of an interval (zero
    when the bounds are reversed, R1). -/
def IntSetValue.card : IntSetValue → Nat
  | .enumeration xs => xs.eraseDups.length
  | .interval lo hi => if hi < lo then 0 else (hi - lo + 1).toNat

/-- Membership in an integer set is decidable. -/
instance : DecidablePred (IntSetValue.Contains s) := by
  cases s with
  | enumeration xs =>
      intro a
      show Decidable (a ∈ xs)
      infer_instance
  | interval lo hi =>
      intro a
      show Decidable (lo ≤ a ∧ a ≤ hi)
      infer_instance

/-- Are all elements of the value list pairwise distinct? -/
def valuesAllDifferent : List Value → Bool
  | [] => true
  | x :: xs => !(xs.any (fun y => x.eqB y)) && valuesAllDifferent xs

/-! ## Fast pairwise distinctness

`valuesAllDifferent` is the *logical* definition: a linear scan per
element, O(n²), and the one every proof in this development reasons
about.  For execution, integer lists (the decoded shape of every
`all_different`-style constraint) are checked by sorting
(O(n log n)) and comparing adjacent elements.  The two agree
(`valuesAllDifferentFast_iff` below), so the *executable* twins use
the fast path while every theorem keeps reasoning about the
quadratic definition. -/

/-- Are all adjacent elements of the integer list distinct? -/
private def adjNe : List Int → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a ≠ b) && adjNe (b :: rest)

/-- Are the integers pairwise distinct?  Sorting-based executable
    twin of `valuesAllDifferent (intVals l)`. -/
def intsAllDifferentFast (l : List Int) : Bool :=
  adjNe (l.mergeSort (fun a b => decide (a ≤ b)))

/-- Encode a list of integers as a list of values. -/
def intVals : List Int → List Value
  | [] => []
  | x :: xs => .int x :: intVals xs

/-- The integers of a value list, if every element is one. -/
private def valueIntsOpt : List Value → Option (List Int)
  | [] => some []
  | .int x :: rest => (valueIntsOpt rest).map (x :: ·)
  | _ => none

/-- Fast executable pairwise distinctness of a value list: sort the
    decoded integers when they are all integers, and fall back to the
    quadratic definition otherwise (mixed lists never occur in the
    fragment: argument shapes are checked by the predicate twins
    before this is called). -/
def valuesAllDifferentFast (xs : List Value) : Bool :=
  match valueIntsOpt xs with
  | some l => intsAllDifferentFast l
  | none => valuesAllDifferent xs

/-! ### Agreement of the fast twin

The bridge runs through `List.Nodup`, which both twins decide:

* the quadratic definition scans each element against the tail
  (exactly the contrapositive of `List.nodup_cons`);
* the fast twin sorts and compares neighbors — on a sorted list a
  duplicate pins two equal neighbors between its occurrences (all
  elements between them are sandwiched to the duplicated value),
  and conversely equal neighbors are an immediate duplicate. -/

/-- Unfolding lemma for `adjNe` on lists of at least two
    elements. -/
private theorem adjNe_cons {a b : Int} {rest : List Int} :
    adjNe (a :: b :: rest) = true ↔ (a ≠ b ∧ adjNe (b :: rest) = true) := by
  simp only [adjNe, Bool.and_eq_true, decide_eq_true_eq]

/-- The head of a sorted list of at least two elements is ≤ the
    second. -/
private theorem sorted_head_le_second {z w : Int} {ws : List Int}
    (hs : List.Pairwise (fun a b => a ≤ b) (z :: w :: ws)) : z ≤ w :=
  (List.pairwise_cons.mp hs).1 w (List.mem_cons_self)

/-- If the head of a sorted list reappears in its tail, the second
    element is sandwiched to it and the first adjacent pair is
    equal. -/
private theorem head_reappears_adj {z : Int} {rest : List Int}
    (hs : List.Pairwise (fun a b => a ≤ b) (z :: rest))
    (ha : adjNe (z :: rest) = true) (hzmem : z ∈ rest) : False := by
  match hrest : rest with
  | [] => cases hzmem
  | w :: ws =>
      subst hrest
      have hwsorted : List.Pairwise (fun a b => a ≤ b) (w :: ws) :=
        List.Pairwise.tail hs
      have hwlez : w ≤ z := by
        rcases List.mem_cons.mp hzmem with rfl | hzmem'
        · exact Int.le_refl _
        · exact (List.pairwise_cons.mp hwsorted).1 z hzmem'
      have hzlew : z ≤ w := sorted_head_le_second hs
      have hc := adjNe_cons.mp ha
      have hne : z ≠ w := hc.1
      omega

/-- A sorted list with all-adjacent-distinct has no duplicates. -/
private theorem sorted_adj_nodup {l : List Int}
    (hs : List.Pairwise (fun a b => a ≤ b) l) (ha : adjNe l = true) :
    l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
      have hxs_sorted : List.Pairwise (fun a b => a ≤ b) xs :=
        List.Pairwise.tail hs
      match hxs : xs with
      | [] =>
          subst hxs
          rw [List.nodup_cons]
          refine ⟨?_, List.nodup_nil⟩
          intro h
          exact nomatch h
      | z :: zs =>
          subst hxs
          have hc := adjNe_cons.mp ha
          rw [List.nodup_cons]
          refine ⟨?_, ?_⟩
          · intro hmem
            have hzlex : z ≤ x := by
              rcases List.mem_cons.mp hmem with rfl | hmem'
              · exact Int.le_refl _
              · exact (List.pairwise_cons.mp hxs_sorted).1 x hmem'
            have hxlez : x ≤ z := sorted_head_le_second hs
            have hxeqz : x = z := by omega
            have hxmemzs : x ∈ zs := by
              rcases List.mem_cons.mp hmem with rfl | hmem'
              · exact absurd rfl hc.1
              · exact hmem'
            have hzmemzs : z ∈ zs := hxeqz ▸ hxmemzs
            exact head_reappears_adj (z := z) hxs_sorted hc.2 hzmemzs
          · exact ih hxs_sorted hc.2

/-- A list with equal adjacent elements has a duplicate. -/
private theorem not_nodup_of_adj_eq {z w : Int} {ws : List Int}
    (h : z = w) : ¬ (z :: w :: ws).Nodup := by
  intro hn
  rw [List.nodup_cons] at hn
  exact hn.1 (h ▸ List.mem_cons_self)

/-- A duplicate-free list has all adjacent elements distinct. -/
private theorem nodup_adj_ne {l : List Int} (h : l.Nodup) :
    adjNe l = true := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      have hnd : ¬ x ∈ xs := (List.nodup_cons.mp h).1
      match hxs : xs with
      | [] => subst hxs; rfl
      | z :: zs =>
          subst hxs
          have hc := List.nodup_cons.mp h
          have hxz : x ≠ z := fun heq => hnd (heq ▸ List.mem_cons_self)
          rw [adjNe_cons]
          exact ⟨hxz, ih hc.2⟩

/-- The fast twin decides duplicate-freedom. -/
theorem intsAllDifferentFast_iff (l : List Int) :
    intsAllDifferentFast l = true ↔ l.Nodup := by
  constructor
  · intro h
    have hsorted : List.Pairwise (fun a b => a ≤ b)
        (l.mergeSort (fun a b => decide (a ≤ b))) := by
      have hs := List.pairwise_mergeSort (le := fun a b => decide (a ≤ b))
        (fun a b c h1 h2 => by
          simp only [decide_eq_true_eq] at h1 h2 ⊢; omega)
        (fun a b => by
          simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l
      exact hs.imp (fun {_ _} h => by simpa using h)
    have hadj : adjNe (l.mergeSort (fun a b => decide (a ≤ b))) = true := by
      rw [intsAllDifferentFast] at h
      exact h
    have hnd : (l.mergeSort (fun a b => decide (a ≤ b))).Nodup :=
      sorted_adj_nodup hsorted hadj
    exact (List.mergeSort_perm l _).nodup_iff.mp hnd
  · intro h
    have hnd : (l.mergeSort (fun a b => decide (a ≤ b))).Nodup :=
      (List.mergeSort_perm l _).nodup_iff.mpr h
    exact nodup_adj_ne hnd

/-- Decoding a list of integers and re-encoding is the identity on
    the `valueIntsOpt` view. -/
private theorem valueIntsOpt_intVals (l : List Int) :
    valueIntsOpt (intVals l) = some l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [intVals, valueIntsOpt, ih, Option.map_some]

/-- A value list whose decode succeeds is the encoding of the
    decoded integers. -/
private theorem eq_intVals_of_valueIntsOpt {xs : List Value} {l : List Int}
    (hv : valueIntsOpt xs = some l) : xs = intVals l := by
  induction xs generalizing l with
  | nil => cases l with
    | nil => rfl
    | cons z zs => rw [valueIntsOpt] at hv; simp at hv
  | cons v vs ih =>
      cases v with
      | int x =>
          rw [valueIntsOpt] at hv
          cases hvs : valueIntsOpt vs with
          | none => rw [hvs] at hv; simp at hv
          | some ls =>
              rw [hvs] at hv
              simp only [Option.map_some, Option.some.injEq] at hv
              cases l with
              | nil => cases hv
              | cons y ys =>
                  simp only [List.cons.injEq] at hv
                  obtain ⟨hxy, hlys⟩ := hv
                  subst hxy
                  subst hlys
                  rw [intVals, ih hvs]
      | bool _ | setOfInt _ | array _ =>
          exact absurd hv (by
            show (none : Option (List Int)) = some l → False
            intro h
            exact nomatch h)

/-- Membership in an encoded list, in `Value.eqB` terms. -/
private theorem mem_intVals_iff {xs : List Int} {w : Value} :
    w ∈ intVals xs ↔ ∃ y : Int, y ∈ xs ∧ w = Value.int y := by
  induction xs with
  | nil => simp [intVals]
  | cons z zs ih =>
      rw [intVals, List.mem_cons, ih]
      constructor
      · rintro (hw | ⟨y, hy, hw⟩)
        · exact ⟨z, List.mem_cons_self, hw⟩
        · exact ⟨y, List.mem_cons_of_mem _ hy, hw⟩
      · rintro ⟨y, hmem, hw⟩
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · exact Or.inl hw
        · exact Or.inr ⟨y, hmem', hw⟩

/-- `Value.eqB` on encoded integers is integer equality. -/
private theorem eqB_int_true {x y : Int} :
    (Value.int x).eqB (Value.int y) = true ↔ x = y := by
  simp only [Value.eqB, beq_iff_eq]

/-- The logical twin decides duplicate-freedom of the decoded
    integers. -/
private theorem valuesAllDifferent_intVals_iff (l : List Int) :
    valuesAllDifferent (intVals l) = true ↔ l.Nodup := by
  induction l with
  | nil => exact ⟨fun _ => List.nodup_nil, fun _ => rfl⟩
  | cons x xs ih =>
      rw [List.nodup_cons]
      show (!((intVals xs).any (fun y => (Value.int x).eqB y)) &&
          valuesAllDifferent (intVals xs)) = true ↔ _
      rw [Bool.and_eq_true, Bool.not_eq_true']
      constructor
      · rintro ⟨hany, hxs⟩
        refine ⟨?_, ih.mp hxs⟩
        intro hmem
        have htrue : (intVals xs).any (fun y => (Value.int x).eqB y) = true := by
          rw [List.any_eq_true]
          refine ⟨Value.int x, mem_intVals_iff.mpr ⟨x, hmem, rfl⟩, ?_⟩
          exact eqB_int_true.mpr rfl
        rw [hany] at htrue
        exact Bool.noConfusion htrue
      · rintro ⟨hnd, hxs⟩
        refine ⟨?_, ih.mpr hxs⟩
        show ((intVals xs).any (fun y => (Value.int x).eqB y)) = false
        cases ha : (intVals xs).any (fun y => (Value.int x).eqB y) with
        | false => rfl
        | true =>
            rw [List.any_eq_true] at ha
            obtain ⟨w, hw, hweq⟩ := ha
            obtain ⟨y, hy, rfl⟩ := mem_intVals_iff.mp hw
            rw [eqB_int_true] at hweq
            exact absurd (hweq ▸ hy) hnd

/-- The fast twin agrees with the logical definition. -/
theorem valuesAllDifferentFast_iff (xs : List Value) :
    valuesAllDifferentFast xs = true ↔ valuesAllDifferent xs = true := by
  unfold valuesAllDifferentFast
  cases hv : valueIntsOpt xs with
  | none =>
      show (valuesAllDifferent xs = true) ↔ (valuesAllDifferent xs = true)
      exact Iff.rfl
  | some l =>
      have hxs : xs = intVals l := eq_intVals_of_valueIntsOpt hv
      subst hxs
      show (intsAllDifferentFast l = true) ↔
        (valuesAllDifferent (intVals l) = true)
      rw [intsAllDifferentFast_iff, valuesAllDifferent_intVals_iff]

/-- Pairwise distinctness ignoring zeros: two elements may be equal only
    when at least one of them is zero. -/
def valuesAllDifferentExcept0 : List Value → Bool
  | [] => true
  | x :: xs =>
      !(xs.any (fun y => !(x.eqB (.int 0)) && !(y.eqB (.int 0)) && x.eqB y))
        && valuesAllDifferentExcept0 xs

/-- Dot product of an integer list and a value list; `none` on shape or
    length mismatch. -/
def dotProduct : List Value → List Value → Option Int
  | .int a :: as_, .int x :: xs =>
      match dotProduct as_ xs with
      | some s => some (a * x + s)
      | none => none
  | [], [] => some 0
  | _, _ => none

/-- `dotProduct as_ xs` exists and is at most `b`. -/
def dotLe (as_ xs : List Value) (b : Int) : Bool :=
  match dotProduct as_ xs with
  | some d => decide (d ≤ b)
  | none => false

/-- `dotProduct as_ xs` exists and differs from `b`. -/
def dotNe (as_ xs : List Value) (b : Int) : Bool :=
  match dotProduct as_ xs with
  | some d => decide (d ≠ b)
  | none => false

/-- Dot product of an integer coefficient list and a Boolean value list
    (Booleans coerced to 0/1, as in MiniZinc's Boolean linear
    constraints); `none` on shape or length mismatch. -/
def boolDotProduct : List Value → List Value → Option Int
  | .int a :: as_, .bool x :: xs =>
      match boolDotProduct as_ xs with
      | some s => some (a * (if x then 1 else 0) + s)
      | none => none
  | [], [] => some 0
  | _, _ => none

/-- `boolDotProduct as_ xs` exists and is at most `b`. -/
def boolDotLe (as_ xs : List Value) (b : Int) : Bool :=
  match boolDotProduct as_ xs with
  | some d => decide (d ≤ b)
  | none => false

/-- Maximum of the integers in a value list; `none` if empty or any
    element is not an integer. -/
def maxValue : List Value → Option Int
  | [] => none
  | .int x :: xs => match maxValue xs with
    | some m => some (max x m)
    | none => some x
  | _ :: _ => none

/-- Minimum of the integers in a value list; `none` if empty or any
    element is not an integer. -/
def minValue : List Value → Option Int
  | [] => none
  | .int x :: xs => match minValue xs with
    | some m => some (min x m)
    | none => some x
  | _ :: _ => none

/-- 1-based element access (FlatZinc arrays are 1-based): the `i`-th
    element of a value list when `1 ≤ i ≤ length`, `none` otherwise. -/
def valuesGet1 : List Value → Int → Option Value :=
  fun xs i => if 0 < i then xs[i.toNat - 1]? else none

/-- The integer element twin decides `valuesGet1` equality. -/
theorem valuesGet1_int_iff (i : Int) (xs : List Value) (e : Int) :
    (match valuesGet1 xs i with
      | some (.int v) => decide (v = e)
      | _ => false) = true ↔
      valuesGet1 xs i = some (.int e) := by
  cases valuesGet1 xs i with
  | none => simp
  | some v =>
    cases v with
    | int a => simp
    | bool a => simp
    | setOfInt a => simp
    | array a => simp

/-- The Boolean element twin decides `valuesGet1` equality. -/
theorem valuesGet1_bool_iff (i : Int) (xs : List Value) (e : Bool) :
    (match valuesGet1 xs i with
      | some (.bool v) => decide (v = e)
      | _ => false) = true ↔
      valuesGet1 xs i = some (.bool e) := by
  cases valuesGet1 xs i with
  | none => simp
  | some v =>
    cases v with
    | int a => simp
    | bool a => simp
    | setOfInt a => simp
    | array a => simp

/-- Odd number of `true`s among the Boolean values: the `Xor` of the
    list (`array_bool_xor`). -/
def valuesXorB (xs : List Value) : Bool :=
  (xs.countP (fun x => x.eqB (.bool true))) % 2 == 1

/-- MiniZinc integer power `pow x y`: `x ^ y` for nonnegative `y`, and
    `1 div x ^ |y|` (truncated division, per the handbook) for negative
    `y`.  The undefined `0 ^ negative` case returns `0`; `int_pow`
    excludes it by a side condition. -/
def intPow (x y : Int) : Int :=
  if y < 0 then Int.tdiv 1 (x ^ (-y).toNat) else x ^ y.toNat

/-- The sorted, deduplicated element list of an integer set: the
    canonical representation used by the lexicographic set comparisons
    `set_le`/`set_lt` (MiniZinc defines them as the lexicographic order
    of the sorted lists of elements).  Enumeration order and duplicates
    are normalized away; reversed intervals are empty (R1). -/
def IntSetValue.sortElems : IntSetValue → List Int
  | .enumeration xs => xs.eraseDups.mergeSort (fun a b => decide (a ≤ b))
  | .interval lo hi =>
      if hi < lo then []
      else List.map (fun k : Nat => lo + (k : Int)) (List.range ((hi - lo + 1).toNat))

/-- Lexicographic ≤ on integer lists: a proper prefix is ≤ any extension,
    then elementwise.  (Prop twin of `lexLeB`.) -/
def listLexLe : List Int → List Int → Prop
  | [], _ => True
  | _ :: _, [] => False
  | a :: as, b :: bs => a < b ∨ (a = b ∧ listLexLe as bs)

/-- Lexicographic ≤ on integer lists (Bool twin of `listLexLe`). -/
def lexLeB : List Int → List Int → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
      if a < b then true else if b < a then false else lexLeB as bs

/-- `lexLeB` decides `listLexLe`. -/
theorem lexLeB_iff {xs ys : List Int} : lexLeB xs ys = true ↔ listLexLe xs ys := by
  induction xs generalizing ys with
  | nil => simp [lexLeB, listLexLe]
  | cons a as ih =>
    cases ys with
    | nil => simp [lexLeB, listLexLe]
    | cons b bs =>
      by_cases h1 : a < b
      · simp [lexLeB, listLexLe, h1]
      · by_cases h2 : b < a
        · have hab : a ≠ b := by omega
          simp [lexLeB, listLexLe, h1, h2, hab]
        · have hab : a = b := by omega
          rw [hab]
          have hnb : ¬ (b < b) := by omega
          simp only [lexLeB, listLexLe, hnb, reduceIte]
          simp only [false_or, true_and]
          exact ih

/-- Lexicographic < on integer lists (a total order, so `<` is `≤` and
    not `≥`).  (Prop twin of `lexLtB`.) -/
def listLexLt (xs ys : List Int) : Prop :=
  listLexLe xs ys ∧ ¬ listLexLe ys xs

/-- Lexicographic < on integer lists (Bool twin of `listLexLt`). -/
def lexLtB (xs ys : List Int) : Bool :=
  lexLeB xs ys && !(lexLeB ys xs)

/-- `lexLtB` decides `listLexLt`. -/
theorem lexLtB_iff (xs ys : List Int) :
    lexLtB xs ys = true ↔ listLexLt xs ys := by
  constructor
  · intro h
    rw [show lexLtB xs ys = (lexLeB xs ys && !(lexLeB ys xs)) from rfl,
      Bool.and_eq_true, Bool.not_eq_true'] at h
    refine ⟨lexLeB_iff.mp h.1, ?_⟩
    intro hq
    have hb := (lexLeB_iff (xs := ys) (ys := xs)).mpr hq
    rw [hb] at h
    exact Bool.noConfusion h.2
  · rintro ⟨h1, h2⟩
    rw [show lexLtB xs ys = (lexLeB xs ys && !(lexLeB ys xs)) from rfl,
      Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨lexLeB_iff.mpr h1, ?_⟩
    have hcontra : lexLeB ys xs = false := by
      cases hb : lexLeB ys xs with
      | false => rfl
      | true => exact absurd (lexLeB_iff.mp hb) h2
    rw [hcontra]

/-! ## Standard signatures -/

/-- Signature environment for the standard FlatZinc predicates of the
    integer/Boolean/set fragment.  Parameter types follow the MiniZinc
    2.10.0 FlatZinc specification (the vendored `lib-flatzinc-*.html`
    pages): par parameters (e.g. the coefficient arrays of the linear
    predicates, the right-hand side of `int_lin_*_reif`, `bool_lin_le`
    and the exponent of `int_pow_fixed`) accept only fixed arguments,
    var parameters also accept fixed ones. -/
def stdSig : SigEnv := fun x =>
  match x.name with
  | "int_eq" => some [.basic (.var (.par .int)), .basic (.var (.par .int))]
  | "int_ne" => some [.basic (.var (.par .int)), .basic (.var (.par .int))]
  | "int_le" => some [.basic (.var (.par .int)), .basic (.var (.par .int))]
  | "int_lt" => some [.basic (.var (.par .int)), .basic (.var (.par .int))]
  | "int_ge" => some [.basic (.var (.par .int)), .basic (.var (.par .int))]
  | "int_gt" => some [.basic (.var (.par .int)), .basic (.var (.par .int))]
  | "int_eq_reif" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .bool))]
  | "int_ne_reif" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .bool))]
  | "int_le_reif" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .bool))]
  | "int_lt_reif" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .bool))]
  | "int_ge_reif" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .bool))]
  | "int_gt_reif" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .bool))]
  | "bool_eq" => some [.basic (.var (.par .bool)), .basic (.var (.par .bool))]
  | "bool_not" => some [.basic (.var (.par .bool)), .basic (.var (.par .bool))]
  | "bool_and" =>
      some [.basic (.var (.par .bool)), .basic (.var (.par .bool)),
        .basic (.var (.par .bool))]
  | "bool_or" =>
      some [.basic (.var (.par .bool)), .basic (.var (.par .bool)),
        .basic (.var (.par .bool))]
  | "bool_xor" =>
      some [.basic (.var (.par .bool)), .basic (.var (.par .bool)),
        .basic (.var (.par .bool))]
  | "bool_le" => some [.basic (.var (.par .bool)), .basic (.var (.par .bool))]
  | "bool_lt" => some [.basic (.var (.par .bool)), .basic (.var (.par .bool))]
  | "bool_eq_reif" =>
      some [.basic (.var (.par .bool)), .basic (.var (.par .bool)),
        .basic (.var (.par .bool))]
  | "bool_le_reif" =>
      some [.basic (.var (.par .bool)), .basic (.var (.par .bool)),
        .basic (.var (.par .bool))]
  | "bool_lt_reif" =>
      some [.basic (.var (.par .bool)), .basic (.var (.par .bool)),
        .basic (.var (.par .bool))]
  | "bool_clause" =>
      some [.array .int (.var (.par .bool)), .array .int (.var (.par .bool))]
  | "bool_clause_reif" =>
      some [.array .int (.var (.par .bool)), .array .int (.var (.par .bool)),
        .basic (.var (.par .bool))]
  | "bool2int" =>
      some [.basic (.var (.par .bool)), .basic (.var (.par .int))]
  | "int_plus" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]
  | "int_minus" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]
  | "int_times" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]
  | "int_div" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]
  | "int_mod" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]
  | "int_min" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]
  | "int_max" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]
  | "int_abs" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .int))]
  | "int_pow" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]
  | "int_pow_fixed" =>
      some [.basic (.var (.par .int)), .basic (.par .int),
        .basic (.var (.par .int))]
  | "set_in" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .setOfInt))]
  | "set_in_reif" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .setOfInt)),
        .basic (.var (.par .bool))]
  | "set_eq" =>
      some [.basic (.var (.par .setOfInt)), .basic (.var (.par .setOfInt))]
  | "set_eq_reif" =>
      some [.basic (.var (.par .setOfInt)), .basic (.var (.par .setOfInt)),
        .basic (.var (.par .bool))]
  | "set_ne" =>
      some [.basic (.var (.par .setOfInt)), .basic (.var (.par .setOfInt))]
  | "set_ne_reif" =>
      some [.basic (.var (.par .setOfInt)), .basic (.var (.par .setOfInt)),
        .basic (.var (.par .bool))]
  | "set_le" =>
      some [.basic (.var (.par .setOfInt)), .basic (.var (.par .setOfInt))]
  | "set_le_reif" =>
      some [.basic (.var (.par .setOfInt)), .basic (.var (.par .setOfInt)),
        .basic (.var (.par .bool))]
  | "set_lt" =>
      some [.basic (.var (.par .setOfInt)), .basic (.var (.par .setOfInt))]
  | "set_lt_reif" =>
      some [.basic (.var (.par .setOfInt)), .basic (.var (.par .setOfInt)),
        .basic (.var (.par .bool))]
  | "set_subset" =>
      some [.basic (.var (.par .setOfInt)), .basic (.var (.par .setOfInt))]
  | "set_subset_reif" =>
      some [.basic (.var (.par .setOfInt)), .basic (.var (.par .setOfInt)),
        .basic (.var (.par .bool))]
  | "set_superset" =>
      some [.basic (.var (.par .setOfInt)), .basic (.var (.par .setOfInt))]
  | "set_superset_reif" =>
      some [.basic (.var (.par .setOfInt)), .basic (.var (.par .setOfInt)),
        .basic (.var (.par .bool))]
  | "set_card" =>
      some [.basic (.var (.par .setOfInt)), .basic (.var (.par .int))]
  | "set_union" =>
      some [.basic (.var (.par .setOfInt)), .basic (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt))]
  | "set_intersect" =>
      some [.basic (.var (.par .setOfInt)), .basic (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt))]
  | "set_diff" =>
      some [.basic (.var (.par .setOfInt)), .basic (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt))]
  | "set_symdiff" =>
      some [.basic (.var (.par .setOfInt)), .basic (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt))]
  | "all_different" => some [.array .int (.var (.par .int))]
  | "all_different_except_0" => some [.array .int (.var (.par .int))]
  | "int_lin_eq" =>
      some [.array .int (.par .int), .array .int (.var (.par .int)),
        .basic (.var (.par .int))]
  | "int_lin_le" =>
      some [.array .int (.par .int), .array .int (.var (.par .int)),
        .basic (.var (.par .int))]
  | "int_lin_ne" =>
      some [.array .int (.par .int), .array .int (.var (.par .int)),
        .basic (.var (.par .int))]
  | "int_lin_eq_reif" =>
      some [.array .int (.par .int), .array .int (.var (.par .int)),
        .basic (.par .int), .basic (.var (.par .bool))]
  | "int_lin_le_reif" =>
      some [.array .int (.par .int), .array .int (.var (.par .int)),
        .basic (.par .int), .basic (.var (.par .bool))]
  | "int_lin_ne_reif" =>
      some [.array .int (.par .int), .array .int (.var (.par .int)),
        .basic (.par .int), .basic (.var (.par .bool))]
  | "bool_lin_eq" =>
      some [.array .int (.par .int), .array .int (.var (.par .bool)),
        .basic (.var (.par .int))]
  | "bool_lin_le" =>
      some [.array .int (.par .int), .array .int (.var (.par .bool)),
        .basic (.par .int)]
  | "array_int_element" =>
      some [.basic (.var (.par .int)), .array .int (.par .int),
        .basic (.var (.par .int))]
  | "array_var_int_element" =>
      some [.basic (.var (.par .int)), .array .int (.var (.par .int)),
        .basic (.var (.par .int))]
  | "array_bool_element" =>
      some [.basic (.var (.par .int)), .array .int (.par .bool),
        .basic (.var (.par .bool))]
  | "array_var_bool_element" =>
      some [.basic (.var (.par .int)), .array .int (.var (.par .bool)),
        .basic (.var (.par .bool))]
  | "array_set_element" =>
      some [.basic (.var (.par .int)), .array .int (.par .setOfInt),
        .basic (.var (.par .setOfInt))]
  | "array_var_set_element" =>
      some [.basic (.var (.par .int)), .array .int (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt))]
  | "array_var_int_element_nonshifted" =>
      some [.basic (.var (.par .int)), .array .int (.var (.par .int)),
        .basic (.var (.par .int))]
  | "array_var_bool_element_nonshifted" =>
      some [.basic (.var (.par .int)), .array .int (.var (.par .bool)),
        .basic (.var (.par .bool))]
  | "array_var_set_element_nonshifted" =>
      some [.basic (.var (.par .int)), .array .int (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt))]
  | "array_int_maximum" =>
      some [.basic (.var (.par .int)), .array .int (.var (.par .int))]
  | "array_int_minimum" =>
      some [.basic (.var (.par .int)), .array .int (.var (.par .int))]
  | "array_bool_and" =>
      some [.array .int (.var (.par .bool)), .basic (.var (.par .bool))]
  | "array_bool_xor" => some [.array .int (.var (.par .bool))]
  | "array_bool_or" =>
      some [.array .int (.var (.par .bool)), .basic (.var (.par .bool))]
  | "true" => some []
  | "dom" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .setOfInt))]
  | _ => none

/-- Convenience: static well-formedness under the standard signatures. -/
def stdWellFormed (m : Model) : Bool := wellFormedB stdSig m

/-! ## Standard interpretations -/

/-- Mathematical interpretations of the standard FlatZinc predicates.
    Each case matches the argument list; a wrong shape yields `False`.
    Quantifier-free cases are decidable; the extensional set predicates
    (`set_eq`, `set_subset`, `set_union`, `set_intersect`, `set_diff`,
    the set comparisons `set_ne`, `set_le`, `set_lt`, `set_superset`,
    `set_symdiff` and their reified variants, and the set-valued
    `array_set_element` family) quantify over all integers or compare
    whole sets and are not decidable here. -/
def stdInterp : PredicateInterpretation := fun x =>
  match x.name with
  | "int_eq" => fun args =>
    match args with
    | [.int a, .int b] => a = b
    | _ => False
  | "int_ne" => fun args =>
    match args with
    | [.int a, .int b] => a ≠ b
    | _ => False
  | "int_le" => fun args =>
    match args with
    | [.int a, .int b] => a ≤ b
    | _ => False
  | "int_lt" => fun args =>
    match args with
    | [.int a, .int b] => a < b
    | _ => False
  | "int_ge" => fun args =>
    match args with
    | [.int a, .int b] => a ≥ b
    | _ => False
  | "int_gt" => fun args =>
    match args with
    | [.int a, .int b] => a > b
    | _ => False
  | "int_eq_reif" => fun args =>
    match args with
    | [.int a, .int b, .bool r] => (r = true ∧ a = b) ∨ (r = false ∧ a ≠ b)
    | _ => False
  | "int_ne_reif" => fun args =>
    match args with
    | [.int a, .int b, .bool r] => (r = true ∧ a ≠ b) ∨ (r = false ∧ a = b)
    | _ => False
  | "int_le_reif" => fun args =>
    match args with
    | [.int a, .int b, .bool r] => (r = true ∧ a ≤ b) ∨ (r = false ∧ a > b)
    | _ => False
  | "int_lt_reif" => fun args =>
    match args with
    | [.int a, .int b, .bool r] => (r = true ∧ a < b) ∨ (r = false ∧ a ≥ b)
    | _ => False
  | "int_ge_reif" => fun args =>
    match args with
    | [.int a, .int b, .bool r] => (r = true ∧ a ≥ b) ∨ (r = false ∧ a < b)
    | _ => False
  | "int_gt_reif" => fun args =>
    match args with
    | [.int a, .int b, .bool r] => (r = true ∧ a > b) ∨ (r = false ∧ a ≤ b)
    | _ => False
  | "bool_eq" => fun args =>
    match args with
    | [.bool a, .bool b] => a = b
    | _ => False
  | "bool_not" => fun args =>
    match args with
    | [.bool a, .bool b] => b = !a
    | _ => False
  | "bool_and" => fun args =>
    match args with
    | [.bool a, .bool b, .bool c] => c = (a && b)
    | _ => False
  | "bool_or" => fun args =>
    match args with
    | [.bool a, .bool b, .bool c] => c = (a || b)
    | _ => False
  | "bool_xor" => fun args =>
    match args with
    | [.bool a, .bool b, .bool c] => c = (a ^^ b)
    | _ => False
  | "bool_le" => fun args =>
    match args with
    | [.bool a, .bool b] => a ≤ b
    | _ => False
  | "bool_lt" => fun args =>
    match args with
    | [.bool a, .bool b] => a = false ∧ b = true
    | _ => False
  | "bool_eq_reif" => fun args =>
    match args with
    | [.bool a, .bool b, .bool r] => (r = true ∧ a = b) ∨ (r = false ∧ a ≠ b)
    | _ => False
  | "bool_le_reif" => fun args =>
    match args with
    | [.bool a, .bool b, .bool r] => (r = true ∧ a ≤ b) ∨ (r = false ∧ ¬ a ≤ b)
    | _ => False
  | "bool_lt_reif" => fun args =>
    match args with
    | [.bool a, .bool b, .bool r] =>
        (r = true ∧ a = false ∧ b = true) ∨ (r = false ∧ (a = true ∨ b = false))
    | _ => False
  | "bool_clause" => fun args =>
    match args with
    | [.array xs, .array ys] =>
        ((xs.any (fun x => x.eqB (.bool true))) ||
          (ys.any (fun y => y.eqB (.bool false)))) = true
    | _ => False
  | "bool_clause_reif" => fun args =>
    match args with
    | [.array xs, .array ys, .bool r] =>
        (r = true ∧ ((xs.any (fun x => x.eqB (.bool true))) ||
          (ys.any (fun y => y.eqB (.bool false))))) ∨
          (r = false ∧ ¬((xs.any (fun x => x.eqB (.bool true))) ||
            (ys.any (fun y => y.eqB (.bool false)))))
    | _ => False
  | "bool2int" => fun args =>
    match args with
    | [.bool b, .int i] => i = (if b then 1 else 0)
    | _ => False
  | "int_plus" => fun args =>
    match args with
    | [.int a, .int b, .int c] => a + b = c
    | _ => False
  | "int_minus" => fun args =>
    match args with
    | [.int a, .int b, .int c] => a - b = c
    | _ => False
  | "int_times" => fun args =>
    match args with
    | [.int a, .int b, .int c] => a * b = c
    | _ => False
  | "int_div" => fun args =>
    match args with
    | [.int a, .int b, .int c] => b ≠ 0 ∧ c = Int.tdiv a b
    | _ => False
  | "int_mod" => fun args =>
    match args with
    | [.int a, .int b, .int c] => b ≠ 0 ∧ c = Int.tmod a b
    | _ => False
  | "int_min" => fun args =>
    match args with
    | [.int a, .int b, .int c] => c = min a b
    | _ => False
  | "int_max" => fun args =>
    match args with
    | [.int a, .int b, .int c] => c = max a b
    | _ => False
  | "int_abs" => fun args =>
    match args with
    | [.int a, .int b] => b = if a < 0 then -a else a
    | _ => False
  | "int_pow" => fun args =>
    match args with
    | [.int x, .int y, .int z] => (y < 0 → x ≠ 0) ∧ z = intPow x y
    | _ => False
  | "int_pow_fixed" => fun args =>
    match args with
    | [.int x, .int y, .int z] => (y < 0 → x ≠ 0) ∧ z = intPow x y
    | _ => False
  | "set_in" => fun args =>
    match args with
    | [.int a, .setOfInt s] => s.Contains a
    | _ => False
  | "set_in_reif" => fun args =>
    match args with
    | [.int a, .setOfInt s, .bool r] =>
        (r = true ∧ s.Contains a) ∨ (r = false ∧ ¬ s.Contains a)
    | _ => False
  | "dom" => fun args =>
    match args with
    | [.int a, .setOfInt s] => s.Contains a
    | _ => False
  | "set_card" => fun args =>
    match args with
    | [.setOfInt s, .int n] => n = s.card
    | _ => False
  | "set_eq" => fun args =>
    match args with
    | [.setOfInt a, .setOfInt b] => ∀ i, a.Contains i ↔ b.Contains i
    | _ => False
  | "set_eq_reif" => fun args =>
    match args with
    | [.setOfInt a, .setOfInt b, .bool r] =>
        (r = true ∧ ∀ i, a.Contains i ↔ b.Contains i) ∨
          (r = false ∧ ¬ ∀ i, a.Contains i ↔ b.Contains i)
    | _ => False
  | "set_ne" => fun args =>
    match args with
    | [.setOfInt a, .setOfInt b] => ¬ ∀ i, a.Contains i ↔ b.Contains i
    | _ => False
  | "set_ne_reif" => fun args =>
    match args with
    | [.setOfInt a, .setOfInt b, .bool r] =>
        (r = true ∧ ¬ ∀ i, a.Contains i ↔ b.Contains i) ∨
          (r = false ∧ ∀ i, a.Contains i ↔ b.Contains i)
    | _ => False
  | "set_le" => fun args =>
    match args with
    | [.setOfInt a, .setOfInt b] => listLexLe a.sortElems b.sortElems
    | _ => False
  | "set_le_reif" => fun args =>
    match args with
    | [.setOfInt a, .setOfInt b, .bool r] =>
        (r = true ∧ listLexLe a.sortElems b.sortElems) ∨
          (r = false ∧ ¬ listLexLe a.sortElems b.sortElems)
    | _ => False
  | "set_lt" => fun args =>
    match args with
    | [.setOfInt a, .setOfInt b] => listLexLt a.sortElems b.sortElems
    | _ => False
  | "set_lt_reif" => fun args =>
    match args with
    | [.setOfInt a, .setOfInt b, .bool r] =>
        (r = true ∧ listLexLt a.sortElems b.sortElems) ∨
          (r = false ∧ ¬ listLexLt a.sortElems b.sortElems)
    | _ => False
  | "set_subset" => fun args =>
    match args with
    | [.setOfInt a, .setOfInt b] => ∀ i, a.Contains i → b.Contains i
    | _ => False
  | "set_subset_reif" => fun args =>
    match args with
    | [.setOfInt a, .setOfInt b, .bool r] =>
        (r = true ∧ ∀ i, a.Contains i → b.Contains i) ∨
          (r = false ∧ ¬ ∀ i, a.Contains i → b.Contains i)
    | _ => False
  | "set_superset" => fun args =>
    match args with
    | [.setOfInt a, .setOfInt b] => ∀ i, b.Contains i → a.Contains i
    | _ => False
  | "set_superset_reif" => fun args =>
    match args with
    | [.setOfInt a, .setOfInt b, .bool r] =>
        (r = true ∧ ∀ i, b.Contains i → a.Contains i) ∨
          (r = false ∧ ¬ ∀ i, b.Contains i → a.Contains i)
    | _ => False
  | "set_union" => fun args =>
    match args with
    | [.setOfInt a, .setOfInt b, .setOfInt c] =>
        ∀ i, c.Contains i ↔ a.Contains i ∨ b.Contains i
    | _ => False
  | "set_intersect" => fun args =>
    match args with
    | [.setOfInt a, .setOfInt b, .setOfInt c] =>
        ∀ i, c.Contains i ↔ a.Contains i ∧ b.Contains i
    | _ => False
  | "set_diff" => fun args =>
    match args with
    | [.setOfInt a, .setOfInt b, .setOfInt c] =>
        ∀ i, c.Contains i ↔ a.Contains i ∧ ¬ b.Contains i
    | _ => False
  | "set_symdiff" => fun args =>
    match args with
    | [.setOfInt a, .setOfInt b, .setOfInt c] =>
        ∀ i, c.Contains i ↔ ¬ (a.Contains i ↔ b.Contains i)
    | _ => False
  | "all_different" => fun args =>
    match args with
    | [.array xs] => valuesAllDifferent xs
    | _ => False
  | "all_different_except_0" => fun args =>
    match args with
    | [.array xs] => valuesAllDifferentExcept0 xs
    | _ => False
  | "int_lin_eq" => fun args =>
    match args with
    | [.array as_, .array xs, .int b] => dotProduct as_ xs = some b
    | _ => False
  | "int_lin_le" => fun args =>
    match args with
    | [.array as_, .array xs, .int b] => dotLe as_ xs b = true
    | _ => False
  | "int_lin_ne" => fun args =>
    match args with
    | [.array as_, .array xs, .int b] => dotNe as_ xs b = true
    | _ => False
  | "int_lin_eq_reif" => fun args =>
    match args with
    | [.array as_, .array xs, .int b, .bool r] =>
        (r = true ∧ dotProduct as_ xs = some b) ∨
          (r = false ∧ dotProduct as_ xs ≠ some b)
    | _ => False
  | "int_lin_le_reif" => fun args =>
    match args with
    | [.array as_, .array xs, .int b, .bool r] =>
        (r = true ∧ dotLe as_ xs b = true) ∨ (r = false ∧ dotLe as_ xs b = false)
    | _ => False
  | "int_lin_ne_reif" => fun args =>
    match args with
    | [.array as_, .array xs, .int b, .bool r] =>
        (r = true ∧ dotNe as_ xs b = true) ∨ (r = false ∧ dotNe as_ xs b = false)
    | _ => False
  | "bool_lin_eq" => fun args =>
    match args with
    | [.array as_, .array xs, .int y] => boolDotProduct as_ xs = some y
    | _ => False
  | "bool_lin_le" => fun args =>
    match args with
    | [.array as_, .array xs, .int y] => boolDotLe as_ xs y = true
    | _ => False
  | "array_int_element" => fun args =>
    match args with
    | [.int i, .array xs, .int e] => valuesGet1 xs i = some (.int e)
    | _ => False
  | "array_var_int_element" => fun args =>
    match args with
    | [.int i, .array xs, .int e] => valuesGet1 xs i = some (.int e)
    | _ => False
  | "array_var_int_element_nonshifted" => fun args =>
    match args with
    | [.int i, .array xs, .int e] => valuesGet1 xs i = some (.int e)
    | _ => False
  | "array_bool_element" => fun args =>
    match args with
    | [.int i, .array xs, .bool e] => valuesGet1 xs i = some (.bool e)
    | _ => False
  | "array_var_bool_element" => fun args =>
    match args with
    | [.int i, .array xs, .bool e] => valuesGet1 xs i = some (.bool e)
    | _ => False
  | "array_var_bool_element_nonshifted" => fun args =>
    match args with
    | [.int i, .array xs, .bool e] => valuesGet1 xs i = some (.bool e)
    | _ => False
  | "array_set_element" => fun args =>
    match args with
    | [.int i, .array xs, .setOfInt e] =>
        match valuesGet1 xs i with
        | some (.setOfInt v) => ∀ j, v.Contains j ↔ e.Contains j
        | _ => False
    | _ => False
  | "array_var_set_element" => fun args =>
    match args with
    | [.int i, .array xs, .setOfInt e] =>
        match valuesGet1 xs i with
        | some (.setOfInt v) => ∀ j, v.Contains j ↔ e.Contains j
        | _ => False
    | _ => False
  | "array_var_set_element_nonshifted" => fun args =>
    match args with
    | [.int i, .array xs, .setOfInt e] =>
        match valuesGet1 xs i with
        | some (.setOfInt v) => ∀ j, v.Contains j ↔ e.Contains j
        | _ => False
    | _ => False
  | "array_int_maximum" => fun args =>
    match args with
    | [.int m, .array xs] => maxValue xs = some m
    | _ => False
  | "array_int_minimum" => fun args =>
    match args with
    | [.int m, .array xs] => minValue xs = some m
    | _ => False
  | "array_bool_and" => fun args =>
    match args with
    | [.array xs, .bool r] => r = (xs.all (fun x => x.eqB (.bool true)))
    | _ => False
  | "array_bool_xor" => fun args =>
    match args with
    | [.array xs] => valuesXorB xs
    | _ => False
  | "array_bool_or" => fun args =>
    match args with
    | [.array xs, .bool r] => r = (xs.any (fun x => x.eqB (.bool true)))
    | _ => False
  | "true" => fun args =>
    match args with
    | [] => True
    | _ => False
  | _ => fun _ => False

/-! ## The executable twin of the decidable fragment

The set-valued element constraints and the extensional set comparisons
have no case here (see `stdInterp`): their twins live in
`FznSolution.lean`'s `interpB`.  The 2.0.2 `*_nonshifted` element
constraints coincide with their plain versions in this fragment: a
nonshifted index is shifted by `min(index_set(xs)) - 1` (MiniZinc
`redefinitions-2.0.2.mzn`), and the index sets of this project's arrays
are all `1..n`, so the shift is zero. -/

/-- **Executable twin of `stdInterp`**: computes the truth of the decidable
    standard-predicate interpretations.  Mirrors `stdInterp` case by case;
    the extensional set predicates (`set_eq`, `set_subset`, `set_union`,
    `set_intersect`, `set_diff`, `set_ne`, `set_le`, `set_lt`,
    `set_superset`, `set_symdiff` with their reified variants, and the
    set-valued element family) quantify over all integers, are not
    computable, and return `false` here — use `stdInterp` for their
    mathematical meaning (or `FznSolution.interpB` for their decided
    twins). -/
def stdInterpB : Ident → List Value → Bool := fun x =>
  match x.name with
  | "int_eq" => fun args =>
    match args with
    | [.int a, .int b] => decide (a = b)
    | _ => false
  | "int_ne" => fun args =>
    match args with
    | [.int a, .int b] => decide (a ≠ b)
    | _ => false
  | "int_le" => fun args =>
    match args with
    | [.int a, .int b] => decide (a ≤ b)
    | _ => false
  | "int_lt" => fun args =>
    match args with
    | [.int a, .int b] => decide (a < b)
    | _ => false
  | "int_ge" => fun args =>
    match args with
    | [.int a, .int b] => decide (a ≥ b)
    | _ => false
  | "int_gt" => fun args =>
    match args with
    | [.int a, .int b] => decide (a > b)
    | _ => false
  | "int_eq_reif" => fun args =>
    match args with
    | [.int a, .int b, .bool r] =>
        decide ((r = true ∧ a = b) ∨ (r = false ∧ a ≠ b))
    | _ => false
  | "int_ne_reif" => fun args =>
    match args with
    | [.int a, .int b, .bool r] =>
        decide ((r = true ∧ a ≠ b) ∨ (r = false ∧ a = b))
    | _ => false
  | "int_le_reif" => fun args =>
    match args with
    | [.int a, .int b, .bool r] =>
        decide ((r = true ∧ a ≤ b) ∨ (r = false ∧ a > b))
    | _ => false
  | "int_lt_reif" => fun args =>
    match args with
    | [.int a, .int b, .bool r] =>
        decide ((r = true ∧ a < b) ∨ (r = false ∧ a ≥ b))
    | _ => false
  | "int_ge_reif" => fun args =>
    match args with
    | [.int a, .int b, .bool r] =>
        decide ((r = true ∧ a ≥ b) ∨ (r = false ∧ a < b))
    | _ => false
  | "int_gt_reif" => fun args =>
    match args with
    | [.int a, .int b, .bool r] =>
        decide ((r = true ∧ a > b) ∨ (r = false ∧ a ≤ b))
    | _ => false
  | "bool_eq" => fun args =>
    match args with
    | [.bool a, .bool b] => decide (a = b)
    | _ => false
  | "bool_not" => fun args =>
    match args with
    | [.bool a, .bool b] => decide (b = !a)
    | _ => false
  | "bool_and" => fun args =>
    match args with
    | [.bool a, .bool b, .bool c] => decide (c = (a && b))
    | _ => false
  | "bool_or" => fun args =>
    match args with
    | [.bool a, .bool b, .bool c] => decide (c = (a || b))
    | _ => false
  | "bool_xor" => fun args =>
    match args with
    | [.bool a, .bool b, .bool c] => decide (c = (a ^^ b))
    | _ => false
  | "bool_le" => fun args =>
    match args with
    | [.bool a, .bool b] => decide (a ≤ b)
    | _ => false
  | "bool_lt" => fun args =>
    match args with
    | [.bool a, .bool b] => decide (a = false ∧ b = true)
    | _ => false
  | "bool_eq_reif" => fun args =>
    match args with
    | [.bool a, .bool b, .bool r] =>
        decide ((r = true ∧ a = b) ∨ (r = false ∧ a ≠ b))
    | _ => false
  | "bool_le_reif" => fun args =>
    match args with
    | [.bool a, .bool b, .bool r] =>
        decide ((r = true ∧ a ≤ b) ∨ (r = false ∧ ¬ a ≤ b))
    | _ => false
  | "bool_lt_reif" => fun args =>
    match args with
    | [.bool a, .bool b, .bool r] =>
        decide ((r = true ∧ a = false ∧ b = true) ∨
          (r = false ∧ (a = true ∨ b = false)))
    | _ => false
  | "bool_clause" => fun args =>
    match args with
    | [.array xs, .array ys] =>
        (xs.any (fun x => x.eqB (.bool true))) ||
          (ys.any (fun y => y.eqB (.bool false)))
    | _ => false
  | "bool_clause_reif" => fun args =>
    match args with
    | [.array xs, .array ys, .bool r] =>
        decide ((r = true ∧ ((xs.any (fun x => x.eqB (.bool true))) ||
          (ys.any (fun y => y.eqB (.bool false))))) ∨
          (r = false ∧ ¬((xs.any (fun x => x.eqB (.bool true))) ||
            (ys.any (fun y => y.eqB (.bool false))))))
    | _ => false
  | "bool2int" => fun args =>
    match args with
    | [.bool b, .int i] => decide (i = (if b then 1 else 0))
    | _ => false
  | "int_plus" => fun args =>
    match args with
    | [.int a, .int b, .int c] => decide (a + b = c)
    | _ => false
  | "int_minus" => fun args =>
    match args with
    | [.int a, .int b, .int c] => decide (a - b = c)
    | _ => false
  | "int_times" => fun args =>
    match args with
    | [.int a, .int b, .int c] => decide (a * b = c)
    | _ => false
  | "int_div" => fun args =>
    match args with
    | [.int a, .int b, .int c] => decide (b ≠ 0 ∧ c = Int.tdiv a b)
    | _ => false
  | "int_mod" => fun args =>
    match args with
    | [.int a, .int b, .int c] => decide (b ≠ 0 ∧ c = Int.tmod a b)
    | _ => false
  | "int_min" => fun args =>
    match args with
    | [.int a, .int b, .int c] => decide (c = min a b)
    | _ => false
  | "int_max" => fun args =>
    match args with
    | [.int a, .int b, .int c] => decide (c = max a b)
    | _ => false
  | "int_abs" => fun args =>
    match args with
    | [.int a, .int b] => decide (b = if a < 0 then -a else a)
    | _ => false
  | "int_pow" => fun args =>
    match args with
    | [.int x, .int y, .int z] => decide ((y < 0 → x ≠ 0) ∧ z = intPow x y)
    | _ => false
  | "int_pow_fixed" => fun args =>
    match args with
    | [.int x, .int y, .int z] => decide ((y < 0 → x ≠ 0) ∧ z = intPow x y)
    | _ => false
  | "set_in" => fun args =>
    match args with
    | [.int a, .setOfInt s] => decide (s.Contains a)
    | _ => false
  | "set_in_reif" => fun args =>
    match args with
    | [.int a, .setOfInt s, .bool r] =>
        decide ((r = true ∧ s.Contains a) ∨ (r = false ∧ ¬ s.Contains a))
    | _ => false
  | "dom" => fun args =>
    match args with
    | [.int a, .setOfInt s] => decide (s.Contains a)
    | _ => false
  | "set_card" => fun args =>
    match args with
    | [.setOfInt s, .int n] => decide (n = s.card)
    | _ => false
  | "all_different" => fun args =>
    match args with
    | [.array xs] => valuesAllDifferentFast xs
    | _ => false
  | "all_different_except_0" => fun args =>
    match args with
    | [.array xs] => valuesAllDifferentExcept0 xs
    | _ => false
  | "int_lin_eq" => fun args =>
    match args with
    | [.array as_, .array xs, .int b] => dotProduct as_ xs == some b
    | _ => false
  | "int_lin_le" => fun args =>
    match args with
    | [.array as_, .array xs, .int b] => dotLe as_ xs b
    | _ => false
  | "int_lin_ne" => fun args =>
    match args with
    | [.array as_, .array xs, .int b] => dotNe as_ xs b
    | _ => false
  | "int_lin_eq_reif" => fun args =>
    match args with
    | [.array as_, .array xs, .int b, .bool r] =>
        decide ((r = true ∧ dotProduct as_ xs = some b) ∨
          (r = false ∧ dotProduct as_ xs ≠ some b))
    | _ => false
  | "int_lin_le_reif" => fun args =>
    match args with
    | [.array as_, .array xs, .int b, .bool r] =>
        decide ((r = true ∧ dotLe as_ xs b = true) ∨
          (r = false ∧ dotLe as_ xs b = false))
    | _ => false
  | "int_lin_ne_reif" => fun args =>
    match args with
    | [.array as_, .array xs, .int b, .bool r] =>
        decide ((r = true ∧ dotNe as_ xs b = true) ∨
          (r = false ∧ dotNe as_ xs b = false))
    | _ => false
  | "bool_lin_eq" => fun args =>
    match args with
    | [.array as_, .array xs, .int y] => boolDotProduct as_ xs == some y
    | _ => false
  | "bool_lin_le" => fun args =>
    match args with
    | [.array as_, .array xs, .int y] => boolDotLe as_ xs y
    | _ => false
  | "array_int_element" => fun args =>
    match args with
    | [.int i, .array xs, .int e] =>
        match valuesGet1 xs i with
        | some (.int v) => decide (v = e)
        | _ => false
    | _ => false
  | "array_var_int_element" => fun args =>
    match args with
    | [.int i, .array xs, .int e] =>
        match valuesGet1 xs i with
        | some (.int v) => decide (v = e)
        | _ => false
    | _ => false
  | "array_var_int_element_nonshifted" => fun args =>
    match args with
    | [.int i, .array xs, .int e] =>
        match valuesGet1 xs i with
        | some (.int v) => decide (v = e)
        | _ => false
    | _ => false
  | "array_bool_element" => fun args =>
    match args with
    | [.int i, .array xs, .bool e] =>
        match valuesGet1 xs i with
        | some (.bool v) => decide (v = e)
        | _ => false
    | _ => false
  | "array_var_bool_element" => fun args =>
    match args with
    | [.int i, .array xs, .bool e] =>
        match valuesGet1 xs i with
        | some (.bool v) => decide (v = e)
        | _ => false
    | _ => false
  | "array_var_bool_element_nonshifted" => fun args =>
    match args with
    | [.int i, .array xs, .bool e] =>
        match valuesGet1 xs i with
        | some (.bool v) => decide (v = e)
        | _ => false
    | _ => false
  | "array_int_maximum" => fun args =>
    match args with
    | [.int m, .array xs] => maxValue xs == some m
    | _ => false
  | "array_int_minimum" => fun args =>
    match args with
    | [.int m, .array xs] => minValue xs == some m
    | _ => false
  | "array_bool_and" => fun args =>
    match args with
    | [.array xs, .bool r] => r == (xs.all (fun x => x.eqB (.bool true)))
    | _ => false
  | "array_bool_xor" => fun args =>
    match args with
    | [.array xs] => valuesXorB xs
    | _ => false
  | "array_bool_or" => fun args =>
    match args with
    | [.array xs, .bool r] => r == (xs.any (fun x => x.eqB (.bool true)))
    | _ => false
  | "true" => fun args =>
    match args with
    | [] => true
    | _ => false
  | _ => fun _ => false

/-! ## Generic shape lemmas

For each argument shape, agreement between a Boolean-valued and a
Prop-valued interpretation of the same body reduces to a case analysis
over the argument list: the well-shaped case is the hypothesis, every
wrong shape makes both sides false.  The per-name theorems below apply
these lemmas with `exact`, so the big `stdInterp`/`stdInterpB` matches
reduce by definitional equality alone. -/

/-- Agreement for two-integer predicates. -/
theorem agreeII {f : Int → Int → Bool} {P : Int → Int → Prop}
    (h : ∀ a b, f a b = true ↔ P a b) : ∀ args : List Value,
    (match args with
      | [.int a, .int b] => f a b
      | _ => false) = true ↔
    (match args with
      | [.int a, .int b] => P a b
      | _ => False) := by
  intro args
  cases args with
  | nil => simp
  | cons v vs =>
    cases v with
    | int a =>
      cases vs with
      | nil => simp
      | cons w ws =>
        cases w with
        | int b =>
          cases ws with
          | nil => exact h a b
          | cons _ _ => simp
        | bool _ => simp
        | setOfInt _ => simp
        | array _ => simp
    | bool _ => simp
    | setOfInt _ => simp
    | array _ => simp

/-- Agreement for three-integer predicates. -/
theorem agreeIII {f : Int → Int → Int → Bool} {P : Int → Int → Int → Prop}
    (h : ∀ a b c, f a b c = true ↔ P a b c) : ∀ args : List Value,
    (match args with
      | [.int a, .int b, .int c] => f a b c
      | _ => false) = true ↔
    (match args with
      | [.int a, .int b, .int c] => P a b c
      | _ => False) := by
  intro args
  cases args with
  | nil => simp
  | cons v vs =>
    cases v with
    | int a =>
      cases vs with
      | nil => simp
      | cons w ws =>
        cases w with
        | int b =>
          cases ws with
          | nil => simp
          | cons u us =>
            cases u with
            | int c =>
              cases us with
              | nil => exact h a b c
              | cons _ _ => simp
            | bool _ => simp
            | setOfInt _ => simp
            | array _ => simp
        | bool _ => simp
        | setOfInt _ => simp
        | array _ => simp
    | bool _ => simp
    | setOfInt _ => simp
    | array _ => simp

/-- Agreement for (int, int, bool) reified comparisons. -/
theorem agreeIIB {f : Int → Int → Bool → Bool} {P : Int → Int → Bool → Prop}
    (h : ∀ a b r, f a b r = true ↔ P a b r) : ∀ args : List Value,
    (match args with
      | [.int a, .int b, .bool r] => f a b r
      | _ => false) = true ↔
    (match args with
      | [.int a, .int b, .bool r] => P a b r
      | _ => False) := by
  intro args
  cases args with
  | nil => simp
  | cons v vs =>
    cases v with
    | int a =>
      cases vs with
      | nil => simp
      | cons w ws =>
        cases w with
        | int b =>
          cases ws with
          | nil => simp
          | cons u us =>
            cases u with
            | bool r =>
              cases us with
              | nil => exact h a b r
              | cons _ _ => simp
            | int _ => simp
            | setOfInt _ => simp
            | array _ => simp
        | bool _ => simp
        | setOfInt _ => simp
        | array _ => simp
    | bool _ => simp
    | setOfInt _ => simp
    | array _ => simp

/-- Agreement for two-Boolean predicates. -/
theorem agreeBB {f : Bool → Bool → Bool} {P : Bool → Bool → Prop}
    (h : ∀ a b, f a b = true ↔ P a b) : ∀ args : List Value,
    (match args with
      | [.bool a, .bool b] => f a b
      | _ => false) = true ↔
    (match args with
      | [.bool a, .bool b] => P a b
      | _ => False) := by
  intro args
  cases args with
  | nil => simp
  | cons v vs =>
    cases v with
    | bool a =>
      cases vs with
      | nil => simp
      | cons w ws =>
        cases w with
        | bool b =>
          cases ws with
          | nil => exact h a b
          | cons _ _ => simp
        | int _ => simp
        | setOfInt _ => simp
        | array _ => simp
    | int _ => simp
    | setOfInt _ => simp
    | array _ => simp

/-- Agreement for three-Boolean predicates. -/
theorem agreeBBB {f : Bool → Bool → Bool → Bool} {P : Bool → Bool → Bool → Prop}
    (h : ∀ a b c, f a b c = true ↔ P a b c) : ∀ args : List Value,
    (match args with
      | [.bool a, .bool b, .bool c] => f a b c
      | _ => false) = true ↔
    (match args with
      | [.bool a, .bool b, .bool c] => P a b c
      | _ => False) := by
  intro args
  cases args with
  | nil => simp
  | cons v vs =>
    cases v with
    | bool a =>
      cases vs with
      | nil => simp
      | cons w ws =>
        cases w with
        | bool b =>
          cases ws with
          | nil => simp
          | cons u us =>
            cases u with
            | bool c =>
              cases us with
              | nil => exact h a b c
              | cons _ _ => simp
            | int _ => simp
            | setOfInt _ => simp
            | array _ => simp
        | int _ => simp
        | setOfInt _ => simp
        | array _ => simp
    | int _ => simp
    | setOfInt _ => simp
    | array _ => simp

/-- Agreement for (bool, int) predicates (`bool2int`). -/
theorem agreeBI {f : Bool → Int → Bool} {P : Bool → Int → Prop}
    (h : ∀ a i, f a i = true ↔ P a i) : ∀ args : List Value,
    (match args with
      | [.bool a, .int i] => f a i
      | _ => false) = true ↔
    (match args with
      | [.bool a, .int i] => P a i
      | _ => False) := by
  intro args
  cases args with
  | nil => simp
  | cons v vs =>
    cases v with
    | bool a =>
      cases vs with
      | nil => simp
      | cons w ws =>
        cases w with
        | int i =>
          cases ws with
          | nil => exact h a i
          | cons _ _ => simp
        | bool _ => simp
        | setOfInt _ => simp
        | array _ => simp
    | int _ => simp
    | setOfInt _ => simp
    | array _ => simp

/-- Agreement for (int, set) predicates (`set_in`, `dom`). -/
theorem agreeIS {f : Int → IntSetValue → Bool} {P : Int → IntSetValue → Prop}
    (h : ∀ a s, f a s = true ↔ P a s) : ∀ args : List Value,
    (match args with
      | [.int a, .setOfInt s] => f a s
      | _ => false) = true ↔
    (match args with
      | [.int a, .setOfInt s] => P a s
      | _ => False) := by
  intro args
  cases args with
  | nil => simp
  | cons v vs =>
    cases v with
    | int a =>
      cases vs with
      | nil => simp
      | cons w ws =>
        cases w with
        | setOfInt s =>
          cases ws with
          | nil => exact h a s
          | cons _ _ => simp
        | bool _ => simp
        | int _ => simp
        | array _ => simp
    | bool _ => simp
    | setOfInt _ => simp
    | array _ => simp

/-- Agreement for (int, set, bool) reified membership. -/
theorem agreeISB {f : Int → IntSetValue → Bool → Bool}
    {P : Int → IntSetValue → Bool → Prop}
    (h : ∀ a s r, f a s r = true ↔ P a s r) : ∀ args : List Value,
    (match args with
      | [.int a, .setOfInt s, .bool r] => f a s r
      | _ => false) = true ↔
    (match args with
      | [.int a, .setOfInt s, .bool r] => P a s r
      | _ => False) := by
  intro args
  cases args with
  | nil => simp
  | cons v vs =>
    cases v with
    | int a =>
      cases vs with
      | nil => simp
      | cons w ws =>
        cases w with
        | setOfInt s =>
          cases ws with
          | nil => simp
          | cons u us =>
            cases u with
            | bool r =>
              cases us with
              | nil => exact h a s r
              | cons _ _ => simp
            | int _ => simp
            | setOfInt _ => simp
            | array _ => simp
        | bool _ => simp
        | int _ => simp
        | array _ => simp
    | bool _ => simp
    | setOfInt _ => simp
    | array _ => simp

/-- Agreement for (set, int) predicates (`set_card`). -/
theorem agreeSI {f : IntSetValue → Int → Bool} {P : IntSetValue → Int → Prop}
    (h : ∀ s n, f s n = true ↔ P s n) : ∀ args : List Value,
    (match args with
      | [.setOfInt s, .int n] => f s n
      | _ => false) = true ↔
    (match args with
      | [.setOfInt s, .int n] => P s n
      | _ => False) := by
  intro args
  cases args with
  | nil => simp
  | cons v vs =>
    cases v with
    | setOfInt s =>
      cases vs with
      | nil => simp
      | cons w ws =>
        cases w with
        | int n =>
          cases ws with
          | nil => exact h s n
          | cons _ _ => simp
        | bool _ => simp
        | setOfInt _ => simp
        | array _ => simp
    | bool _ => simp
    | int _ => simp
    | array _ => simp

/-- Agreement for single-array predicates. -/
theorem agreeA {f : List Value → Bool} {P : List Value → Prop}
    (h : ∀ xs, f xs = true ↔ P xs) : ∀ args : List Value,
    (match args with
      | [.array xs] => f xs
      | _ => false) = true ↔
    (match args with
      | [.array xs] => P xs
      | _ => False) := by
  intro args
  cases args with
  | nil => simp
  | cons v vs =>
    cases v with
    | array xs =>
      cases vs with
      | nil => exact h xs
      | cons _ _ => simp
    | bool _ => simp
    | int _ => simp
    | setOfInt _ => simp

/-- Agreement for two-array predicates (`bool_clause`). -/
theorem agreeAA {f : List Value → List Value → Bool} {P : List Value → List Value → Prop}
    (h : ∀ xs ys, f xs ys = true ↔ P xs ys) : ∀ args : List Value,
    (match args with
      | [.array xs, .array ys] => f xs ys
      | _ => false) = true ↔
    (match args with
      | [.array xs, .array ys] => P xs ys
      | _ => False) := by
  intro args
  cases args with
  | nil => simp
  | cons v vs =>
    cases v with
    | array xs =>
      cases vs with
      | nil => simp
      | cons w ws =>
        cases w with
        | array ys =>
          cases ws with
          | nil => exact h xs ys
          | cons _ _ => simp
        | bool _ => simp
        | int _ => simp
        | setOfInt _ => simp
    | bool _ => simp
    | int _ => simp
    | setOfInt _ => simp

/-- Agreement for two-array-and-Bool predicates (`bool_clause_reif`). -/
theorem agreeAAB {f : List Value → List Value → Bool → Bool}
    {P : List Value → List Value → Bool → Prop}
    (h : ∀ xs ys r, f xs ys r = true ↔ P xs ys r) : ∀ args : List Value,
    (match args with
      | [.array xs, .array ys, .bool r] => f xs ys r
      | _ => false) = true ↔
    (match args with
      | [.array xs, .array ys, .bool r] => P xs ys r
      | _ => False) := by
  intro args
  cases args with
  | nil => simp
  | cons v vs =>
    cases v with
    | array xs =>
      cases vs with
      | nil => simp
      | cons w ws =>
        cases w with
        | array ys =>
          cases ws with
          | nil => simp
          | cons u us =>
            cases u with
            | bool r =>
              cases us with
              | nil => exact h xs ys r
              | cons _ _ => simp
            | int _ => simp
            | setOfInt _ => simp
            | array _ => simp
        | bool _ => simp
        | int _ => simp
        | setOfInt _ => simp
    | bool _ => simp
    | int _ => simp
    | setOfInt _ => simp

/-- Agreement for (array, array, int) linear predicates. -/
theorem agreeAAI {f : List Value → List Value → Int → Bool}
    {P : List Value → List Value → Int → Prop}
    (h : ∀ as_ xs b, f as_ xs b = true ↔ P as_ xs b) : ∀ args : List Value,
    (match args with
      | [.array as_, .array xs, .int b] => f as_ xs b
      | _ => false) = true ↔
    (match args with
      | [.array as_, .array xs, .int b] => P as_ xs b
      | _ => False) := by
  intro args
  cases args with
  | nil => simp
  | cons v vs =>
    cases v with
    | array as_ =>
      cases vs with
      | nil => simp
      | cons w ws =>
        cases w with
        | array xs =>
          cases ws with
          | nil => simp
          | cons u us =>
            cases u with
            | int b =>
              cases us with
              | nil => exact h as_ xs b
              | cons _ _ => simp
            | bool _ => simp
            | setOfInt _ => simp
            | array _ => simp
        | bool _ => simp
        | int _ => simp
        | setOfInt _ => simp
    | bool _ => simp
    | int _ => simp
    | setOfInt _ => simp

/-- Agreement for (array, array, int, bool) reified linear predicates. -/
theorem agreeAAIB {f : List Value → List Value → Int → Bool → Bool}
    {P : List Value → List Value → Int → Bool → Prop}
    (h : ∀ as_ xs b r, f as_ xs b r = true ↔ P as_ xs b r) :
    ∀ args : List Value,
    (match args with
      | [.array as_, .array xs, .int b, .bool r] => f as_ xs b r
      | _ => false) = true ↔
    (match args with
      | [.array as_, .array xs, .int b, .bool r] => P as_ xs b r
      | _ => False) := by
  intro args
  cases args with
  | nil => simp
  | cons v vs =>
    cases v with
    | array as_ =>
      cases vs with
      | nil => simp
      | cons w ws =>
        cases w with
        | array xs =>
          cases ws with
          | nil => simp
          | cons u us =>
            cases u with
            | int b =>
              cases us with
              | nil => simp
              | cons t ts =>
                cases t with
                | bool r =>
                  cases ts with
                  | nil => exact h as_ xs b r
                  | cons _ _ => simp
                | int _ => simp
                | setOfInt _ => simp
                | array _ => simp
            | bool _ => simp
            | setOfInt _ => simp
            | array _ => simp
        | bool _ => simp
        | int _ => simp
        | setOfInt _ => simp
    | bool _ => simp
    | int _ => simp
    | setOfInt _ => simp

/-- Agreement for (array, bool) predicates (`array_bool_and`,
    `array_bool_or`). -/
theorem agreeAB {f : List Value → Bool → Bool} {P : List Value → Bool → Prop}
    (h : ∀ xs r, f xs r = true ↔ P xs r) : ∀ args : List Value,
    (match args with
      | [.array xs, .bool r] => f xs r
      | _ => false) = true ↔
    (match args with
      | [.array xs, .bool r] => P xs r
      | _ => False) := by
  intro args
  cases args with
  | nil => simp
  | cons v vs =>
    cases v with
    | array xs =>
      cases vs with
      | nil => simp
      | cons w ws =>
        cases w with
        | bool r =>
          cases ws with
          | nil => exact h xs r
          | cons _ _ => simp
        | int _ => simp
        | setOfInt _ => simp
        | array _ => simp
    | bool _ => simp
    | int _ => simp
    | setOfInt _ => simp

/-- Agreement for (int, array) predicates (`array_int_maximum`,
    `array_int_minimum`). -/
theorem agreeIA {f : Int → List Value → Bool} {P : Int → List Value → Prop}
    (h : ∀ m xs, f m xs = true ↔ P m xs) : ∀ args : List Value,
    (match args with
      | [.int m, .array xs] => f m xs
      | _ => false) = true ↔
    (match args with
      | [.int m, .array xs] => P m xs
      | _ => False) := by
  intro args
  cases args with
  | nil => simp
  | cons v vs =>
    cases v with
    | int m =>
      cases vs with
      | nil => simp
      | cons w ws =>
        cases w with
        | array xs =>
          cases ws with
          | nil => exact h m xs
          | cons _ _ => simp
        | bool _ => simp
        | int _ => simp
        | setOfInt _ => simp
    | bool _ => simp
    | setOfInt _ => simp
    | array _ => simp

/-- Agreement for (int, array, int) element predicates. -/
theorem agreeIAI {f : Int → List Value → Int → Bool}
    {P : Int → List Value → Int → Prop}
    (h : ∀ i xs e, f i xs e = true ↔ P i xs e) : ∀ args : List Value,
    (match args with
      | [.int i, .array xs, .int e] => f i xs e
      | _ => false) = true ↔
    (match args with
      | [.int i, .array xs, .int e] => P i xs e
      | _ => False) := by
  intro args
  cases args with
  | nil => simp
  | cons v vs =>
    cases v with
    | int i =>
      cases vs with
      | nil => simp
      | cons w ws =>
        cases w with
        | array xs =>
          cases ws with
          | nil => simp
          | cons u us =>
            cases u with
            | int e =>
              cases us with
              | nil => exact h i xs e
              | cons _ _ => simp
            | bool _ => simp
            | setOfInt _ => simp
            | array _ => simp
        | bool _ => simp
        | int _ => simp
        | setOfInt _ => simp
    | bool _ => simp
    | setOfInt _ => simp
    | array _ => simp

/-- Agreement for (int, array, bool) element predicates. -/
theorem agreeIAB {f : Int → List Value → Bool → Bool}
    {P : Int → List Value → Bool → Prop}
    (h : ∀ i xs e, f i xs e = true ↔ P i xs e) : ∀ args : List Value,
    (match args with
      | [.int i, .array xs, .bool e] => f i xs e
      | _ => false) = true ↔
    (match args with
      | [.int i, .array xs, .bool e] => P i xs e
      | _ => False) := by
  intro args
  cases args with
  | nil => simp
  | cons v vs =>
    cases v with
    | int i =>
      cases vs with
      | nil => simp
      | cons w ws =>
        cases w with
        | array xs =>
          cases ws with
          | nil => simp
          | cons u us =>
            cases u with
            | bool e =>
              cases us with
              | nil => exact h i xs e
              | cons _ _ => simp
            | int _ => simp
            | setOfInt _ => simp
            | array _ => simp
        | bool _ => simp
        | int _ => simp
        | setOfInt _ => simp
    | bool _ => simp
    | setOfInt _ => simp
    | array _ => simp

/-- Agreement for nullary predicates (`true`). -/
theorem agreeNil {P : Prop} (h : P) : ∀ args : List Value,
    (match args with
      | [] => true
      | _ => false) = true ↔
    (match args with
      | [] => P
      | _ => False) := by
  intro args
  cases args with
  | nil => exact ⟨fun _ => h, fun _ => rfl⟩
  | cons _ _ => simp

/-! ## Per-name agreement theorems -/

/-- `int_eq` agreement. -/
theorem builtin_int_eq_iff (args : List Value) :
    stdInterpB (Ident.mk "int_eq") args = true ↔
      stdInterp (Ident.mk "int_eq") args :=
  agreeII (fun _ _ => decide_eq_true_iff) args

/-- `int_ne` agreement. -/
theorem builtin_int_ne_iff (args : List Value) :
    stdInterpB (Ident.mk "int_ne") args = true ↔
      stdInterp (Ident.mk "int_ne") args :=
  agreeII (fun _ _ => decide_eq_true_iff) args

/-- `int_le` agreement. -/
theorem builtin_int_le_iff (args : List Value) :
    stdInterpB (Ident.mk "int_le") args = true ↔
      stdInterp (Ident.mk "int_le") args :=
  agreeII (fun _ _ => decide_eq_true_iff) args

/-- `int_lt` agreement. -/
theorem builtin_int_lt_iff (args : List Value) :
    stdInterpB (Ident.mk "int_lt") args = true ↔
      stdInterp (Ident.mk "int_lt") args :=
  agreeII (fun _ _ => decide_eq_true_iff) args

/-- `int_ge` agreement. -/
theorem builtin_int_ge_iff (args : List Value) :
    stdInterpB (Ident.mk "int_ge") args = true ↔
      stdInterp (Ident.mk "int_ge") args :=
  agreeII (fun _ _ => decide_eq_true_iff) args

/-- `int_gt` agreement. -/
theorem builtin_int_gt_iff (args : List Value) :
    stdInterpB (Ident.mk "int_gt") args = true ↔
      stdInterp (Ident.mk "int_gt") args :=
  agreeII (fun _ _ => decide_eq_true_iff) args

/-- `int_eq_reif` agreement. -/
theorem builtin_int_eq_reif_iff (args : List Value) :
    stdInterpB (Ident.mk "int_eq_reif") args = true ↔
      stdInterp (Ident.mk "int_eq_reif") args :=
  agreeIIB (fun _ _ _ => decide_eq_true_iff) args

/-- `int_ne_reif` agreement. -/
theorem builtin_int_ne_reif_iff (args : List Value) :
    stdInterpB (Ident.mk "int_ne_reif") args = true ↔
      stdInterp (Ident.mk "int_ne_reif") args :=
  agreeIIB (fun _ _ _ => decide_eq_true_iff) args

/-- `int_le_reif` agreement. -/
theorem builtin_int_le_reif_iff (args : List Value) :
    stdInterpB (Ident.mk "int_le_reif") args = true ↔
      stdInterp (Ident.mk "int_le_reif") args :=
  agreeIIB (fun _ _ _ => decide_eq_true_iff) args

/-- `int_lt_reif` agreement. -/
theorem builtin_int_lt_reif_iff (args : List Value) :
    stdInterpB (Ident.mk "int_lt_reif") args = true ↔
      stdInterp (Ident.mk "int_lt_reif") args :=
  agreeIIB (fun _ _ _ => decide_eq_true_iff) args

/-- `int_ge_reif` agreement. -/
theorem builtin_int_ge_reif_iff (args : List Value) :
    stdInterpB (Ident.mk "int_ge_reif") args = true ↔
      stdInterp (Ident.mk "int_ge_reif") args :=
  agreeIIB (fun _ _ _ => decide_eq_true_iff) args

/-- `int_gt_reif` agreement. -/
theorem builtin_int_gt_reif_iff (args : List Value) :
    stdInterpB (Ident.mk "int_gt_reif") args = true ↔
      stdInterp (Ident.mk "int_gt_reif") args :=
  agreeIIB (fun _ _ _ => decide_eq_true_iff) args

/-- `bool_eq` agreement. -/
theorem builtin_bool_eq_iff (args : List Value) :
    stdInterpB (Ident.mk "bool_eq") args = true ↔
      stdInterp (Ident.mk "bool_eq") args :=
  agreeBB (fun _ _ => decide_eq_true_iff) args

/-- `bool_not` agreement. -/
theorem builtin_bool_not_iff (args : List Value) :
    stdInterpB (Ident.mk "bool_not") args = true ↔
      stdInterp (Ident.mk "bool_not") args :=
  agreeBB (fun _ _ => decide_eq_true_iff) args

/-- `bool_and` agreement. -/
theorem builtin_bool_and_iff (args : List Value) :
    stdInterpB (Ident.mk "bool_and") args = true ↔
      stdInterp (Ident.mk "bool_and") args :=
  agreeBBB (fun _ _ _ => decide_eq_true_iff) args

/-- `bool_or` agreement. -/
theorem builtin_bool_or_iff (args : List Value) :
    stdInterpB (Ident.mk "bool_or") args = true ↔
      stdInterp (Ident.mk "bool_or") args :=
  agreeBBB (fun _ _ _ => decide_eq_true_iff) args

/-- `bool_xor` agreement. -/
theorem builtin_bool_xor_iff (args : List Value) :
    stdInterpB (Ident.mk "bool_xor") args = true ↔
      stdInterp (Ident.mk "bool_xor") args :=
  agreeBBB (fun _ _ _ => decide_eq_true_iff) args

/-- `bool_le` agreement. -/
theorem builtin_bool_le_iff (args : List Value) :
    stdInterpB (Ident.mk "bool_le") args = true ↔
      stdInterp (Ident.mk "bool_le") args :=
  agreeBB (fun _ _ => decide_eq_true_iff) args

/-- `bool_lt` agreement. -/
theorem builtin_bool_lt_iff (args : List Value) :
    stdInterpB (Ident.mk "bool_lt") args = true ↔
      stdInterp (Ident.mk "bool_lt") args :=
  agreeBB (fun _ _ => decide_eq_true_iff) args

/-- `bool_eq_reif` agreement. -/
theorem builtin_bool_eq_reif_iff (args : List Value) :
    stdInterpB (Ident.mk "bool_eq_reif") args = true ↔
      stdInterp (Ident.mk "bool_eq_reif") args :=
  agreeBBB (fun _ _ _ => decide_eq_true_iff) args

/-- `bool_le_reif` agreement. -/
theorem builtin_bool_le_reif_iff (args : List Value) :
    stdInterpB (Ident.mk "bool_le_reif") args = true ↔
      stdInterp (Ident.mk "bool_le_reif") args :=
  agreeBBB (fun _ _ _ => decide_eq_true_iff) args

/-- `bool_lt_reif` agreement. -/
theorem builtin_bool_lt_reif_iff (args : List Value) :
    stdInterpB (Ident.mk "bool_lt_reif") args = true ↔
      stdInterp (Ident.mk "bool_lt_reif") args :=
  agreeBBB (fun _ _ _ => decide_eq_true_iff) args

/-- `bool_clause` agreement. -/
theorem builtin_bool_clause_iff (args : List Value) :
    stdInterpB (Ident.mk "bool_clause") args = true ↔
      stdInterp (Ident.mk "bool_clause") args :=
  agreeAA (fun _ _ => Iff.rfl) args

/-- `bool_clause_reif` agreement. -/
theorem builtin_bool_clause_reif_iff (args : List Value) :
    stdInterpB (Ident.mk "bool_clause_reif") args = true ↔
      stdInterp (Ident.mk "bool_clause_reif") args :=
  agreeAAB (fun _ _ _ => decide_eq_true_iff) args

/-- `bool2int` agreement. -/
theorem builtin_bool2int_iff (args : List Value) :
    stdInterpB (Ident.mk "bool2int") args = true ↔
      stdInterp (Ident.mk "bool2int") args :=
  agreeBI (fun _ _ => decide_eq_true_iff) args

/-- `int_plus` agreement. -/
theorem builtin_int_plus_iff (args : List Value) :
    stdInterpB (Ident.mk "int_plus") args = true ↔
      stdInterp (Ident.mk "int_plus") args :=
  agreeIII (fun _ _ _ => decide_eq_true_iff) args

/-- `int_minus` agreement. -/
theorem builtin_int_minus_iff (args : List Value) :
    stdInterpB (Ident.mk "int_minus") args = true ↔
      stdInterp (Ident.mk "int_minus") args :=
  agreeIII (fun _ _ _ => decide_eq_true_iff) args

/-- `int_times` agreement. -/
theorem builtin_int_times_iff (args : List Value) :
    stdInterpB (Ident.mk "int_times") args = true ↔
      stdInterp (Ident.mk "int_times") args :=
  agreeIII (fun _ _ _ => decide_eq_true_iff) args

/-- `int_div` agreement. -/
theorem builtin_int_div_iff (args : List Value) :
    stdInterpB (Ident.mk "int_div") args = true ↔
      stdInterp (Ident.mk "int_div") args :=
  agreeIII (fun _ _ _ => decide_eq_true_iff) args

/-- `int_mod` agreement. -/
theorem builtin_int_mod_iff (args : List Value) :
    stdInterpB (Ident.mk "int_mod") args = true ↔
      stdInterp (Ident.mk "int_mod") args :=
  agreeIII (fun _ _ _ => decide_eq_true_iff) args

/-- `int_min` agreement. -/
theorem builtin_int_min_iff (args : List Value) :
    stdInterpB (Ident.mk "int_min") args = true ↔
      stdInterp (Ident.mk "int_min") args :=
  agreeIII (fun _ _ _ => decide_eq_true_iff) args

/-- `int_max` agreement. -/
theorem builtin_int_max_iff (args : List Value) :
    stdInterpB (Ident.mk "int_max") args = true ↔
      stdInterp (Ident.mk "int_max") args :=
  agreeIII (fun _ _ _ => decide_eq_true_iff) args

/-- `int_abs` agreement. -/
theorem builtin_int_abs_iff (args : List Value) :
    stdInterpB (Ident.mk "int_abs") args = true ↔
      stdInterp (Ident.mk "int_abs") args :=
  agreeII (fun _ _ => decide_eq_true_iff) args

/-- `int_pow` agreement. -/
theorem builtin_int_pow_iff (args : List Value) :
    stdInterpB (Ident.mk "int_pow") args = true ↔
      stdInterp (Ident.mk "int_pow") args :=
  agreeIII (fun _ _ _ => decide_eq_true_iff) args

/-- `int_pow_fixed` agreement. -/
theorem builtin_int_pow_fixed_iff (args : List Value) :
    stdInterpB (Ident.mk "int_pow_fixed") args = true ↔
      stdInterp (Ident.mk "int_pow_fixed") args :=
  agreeIII (fun _ _ _ => decide_eq_true_iff) args

/-- `set_in` agreement. -/
theorem builtin_set_in_iff (args : List Value) :
    stdInterpB (Ident.mk "set_in") args = true ↔
      stdInterp (Ident.mk "set_in") args :=
  agreeIS (fun _ _ => decide_eq_true_iff) args

/-- `set_in_reif` agreement. -/
theorem builtin_set_in_reif_iff (args : List Value) :
    stdInterpB (Ident.mk "set_in_reif") args = true ↔
      stdInterp (Ident.mk "set_in_reif") args :=
  agreeISB (fun _ _ _ => decide_eq_true_iff) args

/-- `dom` agreement. -/
theorem builtin_dom_iff (args : List Value) :
    stdInterpB (Ident.mk "dom") args = true ↔
      stdInterp (Ident.mk "dom") args :=
  agreeIS (fun _ _ => decide_eq_true_iff) args

/-- `set_card` agreement. -/
theorem builtin_set_card_iff (args : List Value) :
    stdInterpB (Ident.mk "set_card") args = true ↔
      stdInterp (Ident.mk "set_card") args :=
  agreeSI (fun _ _ => decide_eq_true_iff) args

/-- `all_different` agreement. -/
theorem builtin_all_different_iff (args : List Value) :
    stdInterpB (Ident.mk "all_different") args = true ↔
      stdInterp (Ident.mk "all_different") args :=
  agreeA (fun _ => valuesAllDifferentFast_iff _) args

/-- `all_different_except_0` agreement. -/
theorem builtin_all_different_except_0_iff (args : List Value) :
    stdInterpB (Ident.mk "all_different_except_0") args = true ↔
      stdInterp (Ident.mk "all_different_except_0") args :=
  agreeA (fun _ => Iff.rfl) args

/-- `int_lin_eq` agreement. -/
theorem builtin_int_lin_eq_iff (args : List Value) :
    stdInterpB (Ident.mk "int_lin_eq") args = true ↔
      stdInterp (Ident.mk "int_lin_eq") args :=
  agreeAAI (fun _ _ _ => beq_iff_eq) args

/-- `int_lin_le` agreement. -/
theorem builtin_int_lin_le_iff (args : List Value) :
    stdInterpB (Ident.mk "int_lin_le") args = true ↔
      stdInterp (Ident.mk "int_lin_le") args :=
  agreeAAI (fun _ _ _ => Iff.rfl) args

/-- `int_lin_ne` agreement. -/
theorem builtin_int_lin_ne_iff (args : List Value) :
    stdInterpB (Ident.mk "int_lin_ne") args = true ↔
      stdInterp (Ident.mk "int_lin_ne") args :=
  agreeAAI (fun _ _ _ => Iff.rfl) args

/-- `int_lin_eq_reif` agreement. -/
theorem builtin_int_lin_eq_reif_iff (args : List Value) :
    stdInterpB (Ident.mk "int_lin_eq_reif") args = true ↔
      stdInterp (Ident.mk "int_lin_eq_reif") args :=
  agreeAAIB (fun _ _ _ _ => decide_eq_true_iff) args

/-- `int_lin_le_reif` agreement. -/
theorem builtin_int_lin_le_reif_iff (args : List Value) :
    stdInterpB (Ident.mk "int_lin_le_reif") args = true ↔
      stdInterp (Ident.mk "int_lin_le_reif") args :=
  agreeAAIB (fun _ _ _ _ => decide_eq_true_iff) args

/-- `int_lin_ne_reif` agreement. -/
theorem builtin_int_lin_ne_reif_iff (args : List Value) :
    stdInterpB (Ident.mk "int_lin_ne_reif") args = true ↔
      stdInterp (Ident.mk "int_lin_ne_reif") args :=
  agreeAAIB (fun _ _ _ _ => decide_eq_true_iff) args

/-- `bool_lin_eq` agreement. -/
theorem builtin_bool_lin_eq_iff (args : List Value) :
    stdInterpB (Ident.mk "bool_lin_eq") args = true ↔
      stdInterp (Ident.mk "bool_lin_eq") args :=
  agreeAAI (fun _ _ _ => beq_iff_eq) args

/-- `bool_lin_le` agreement. -/
theorem builtin_bool_lin_le_iff (args : List Value) :
    stdInterpB (Ident.mk "bool_lin_le") args = true ↔
      stdInterp (Ident.mk "bool_lin_le") args :=
  agreeAAI (fun _ _ _ => Iff.rfl) args

/-- `array_int_element` agreement. -/
theorem builtin_array_int_element_iff (args : List Value) :
    stdInterpB (Ident.mk "array_int_element") args = true ↔
      stdInterp (Ident.mk "array_int_element") args :=
  agreeIAI valuesGet1_int_iff args

/-- `array_var_int_element` agreement. -/
theorem builtin_array_var_int_element_iff (args : List Value) :
    stdInterpB (Ident.mk "array_var_int_element") args = true ↔
      stdInterp (Ident.mk "array_var_int_element") args :=
  agreeIAI valuesGet1_int_iff args

/-- `array_var_int_element_nonshifted` agreement. -/
theorem builtin_array_var_int_element_nonshifted_iff (args : List Value) :
    stdInterpB (Ident.mk "array_var_int_element_nonshifted") args = true ↔
      stdInterp (Ident.mk "array_var_int_element_nonshifted") args :=
  agreeIAI valuesGet1_int_iff args

/-- `array_bool_element` agreement. -/
theorem builtin_array_bool_element_iff (args : List Value) :
    stdInterpB (Ident.mk "array_bool_element") args = true ↔
      stdInterp (Ident.mk "array_bool_element") args :=
  agreeIAB valuesGet1_bool_iff args

/-- `array_var_bool_element` agreement. -/
theorem builtin_array_var_bool_element_iff (args : List Value) :
    stdInterpB (Ident.mk "array_var_bool_element") args = true ↔
      stdInterp (Ident.mk "array_var_bool_element") args :=
  agreeIAB valuesGet1_bool_iff args

/-- `array_var_bool_element_nonshifted` agreement. -/
theorem builtin_array_var_bool_element_nonshifted_iff (args : List Value) :
    stdInterpB (Ident.mk "array_var_bool_element_nonshifted") args = true ↔
      stdInterp (Ident.mk "array_var_bool_element_nonshifted") args :=
  agreeIAB valuesGet1_bool_iff args

/-- `array_int_maximum` agreement. -/
theorem builtin_array_int_maximum_iff (args : List Value) :
    stdInterpB (Ident.mk "array_int_maximum") args = true ↔
      stdInterp (Ident.mk "array_int_maximum") args :=
  agreeIA (fun _ _ => beq_iff_eq) args

/-- `array_int_minimum` agreement. -/
theorem builtin_array_int_minimum_iff (args : List Value) :
    stdInterpB (Ident.mk "array_int_minimum") args = true ↔
      stdInterp (Ident.mk "array_int_minimum") args :=
  agreeIA (fun _ _ => beq_iff_eq) args

/-- `array_bool_and` agreement. -/
theorem builtin_array_bool_and_iff (args : List Value) :
    stdInterpB (Ident.mk "array_bool_and") args = true ↔
      stdInterp (Ident.mk "array_bool_and") args :=
  agreeAB (fun _ _ => beq_iff_eq) args

/-- `array_bool_xor` agreement. -/
theorem builtin_array_bool_xor_iff (args : List Value) :
    stdInterpB (Ident.mk "array_bool_xor") args = true ↔
      stdInterp (Ident.mk "array_bool_xor") args :=
  agreeA (fun _ => Iff.rfl) args

/-- `array_bool_or` (deprecated) agreement. -/
theorem builtin_array_bool_or_iff (args : List Value) :
    stdInterpB (Ident.mk "array_bool_or") args = true ↔
      stdInterp (Ident.mk "array_bool_or") args :=
  agreeAB (fun _ _ => beq_iff_eq) args

/-- `true` agreement. -/
theorem builtin_true_iff (args : List Value) :
    stdInterpB (Ident.mk "true") args = true ↔
      stdInterp (Ident.mk "true") args :=
  agreeNil trivial args

end LeanFzn.Semantics

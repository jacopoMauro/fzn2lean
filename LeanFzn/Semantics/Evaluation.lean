import LeanFzn.Semantics.StdLib
open LeanFzn.Semantics


namespace LeanFzn.Semantics.Evaluation

open LeanFzn LeanFzn.Semantics

/-! ## The decidable interpretation bridge

`stdInterp` is Prop-valued; five set predicates quantify over all
integers.  Both sets in each argument are finitely represented
(enumerations or intervals), so extensional equality and inclusion are
decidable by enumerating the elements of the finite representations:
`i ∈ s ↔ i ∈ s.toList` for every integer `i`. -/

/-- The finitely many elements of an integer set (order-preserving for
    intervals; empty when the bounds are reversed, R1). -/
def setElems : IntSetValue → List Int
  | .enumeration xs => xs
  | .interval lo hi =>
      if hi < lo then []
      else List.map (fun k : Nat => lo + (k : Int)) (List.range ((hi - lo + 1).toNat))

/-- Membership agrees with the element list. -/
theorem setElems_mem_iff {s : IntSetValue} {i : Int} :
    s.Contains i ↔ i ∈ setElems s := by
  cases s with
  | enumeration xs => rfl
  | interval lo hi =>
      by_cases h : hi < lo
      · have hempty : setElems (IntSetValue.interval lo hi) = [] := by
          simp [setElems, h]
        rw [hempty]
        simp only [List.not_mem_nil, iff_false]
        intro hmem
        obtain ⟨h1, h2⟩ := hmem
        omega
      · have hle : lo ≤ hi := by omega
        have hset : setElems (IntSetValue.interval lo hi)
            = List.map (fun k : Nat => lo + (k : Int))
                (List.range ((hi - lo + 1).toNat)) := by
          simp only [setElems, if_neg h]
        rw [hset, List.mem_map]
        constructor
        · rintro ⟨h1, h2⟩
          have hi0 : 0 ≤ i - lo := by omega
          have hk : (i - lo).toNat < (hi - lo + 1).toNat := by omega
          refine ⟨(i - lo).toNat, List.mem_range.mpr hk, ?_⟩
          have hofnat := Int.ofNat_toNat (i - lo)
          rw [show ((i - lo).toNat : Int) = max (i - lo) 0 from hofnat]
          omega
        · rintro ⟨k, hk, hkeq⟩
          rw [List.mem_range] at hk
          constructor
          · omega
          · omega

/-! ## The total Boolean twin of `stdInterp`

`stdInterpB` (in `FznStdLib.lean`) covers the decidable fragment with
per-name agreement theorems `builtin_<name>_iff`; the extensional set
predicates are completed here by deciding the pointwise conditions
through the finite element lists (`setElems`), and the resulting
relation `interpB` is proved to agree with `stdInterp` (via the
dispatchers `interpB_std_iff` and `interpB_set_iff`). -/

/-- Does `p` hold on the `n` consecutive integers starting at `lo`?
    Exits at the first failure and allocates no element list. -/
def intRangeAll (p : Int → Bool) (lo : Int) : Nat → Bool
  | 0 => true
  | n + 1 => p lo && intRangeAll p (lo + 1) n

theorem intRangeAll_iff (p : Int → Bool) : ∀ (n : Nat) (lo : Int),
    intRangeAll p lo n = true ↔ ∀ i, lo ≤ i → i < lo + n → p i = true := by
  intro n
  induction n with
  | zero => intro lo; simp only [intRangeAll, true_iff]; intro i h1 h2; omega
  | succ n ih =>
    intro lo
    simp only [intRangeAll, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h0, hrest⟩ i h1 h2
      by_cases hi : i = lo
      · subst hi; exact h0
      · exact hrest i (by omega) (by omega)
    · intro h
      exact ⟨h lo (Int.le_refl _) (by omega), fun i h1 h2 => h i (by omega) (by omega)⟩

/-- Does `p` hold on every element of the set?  Intervals are scanned
    without materializing their elements. -/
def setAllB (s : IntSetValue) (p : Int → Bool) : Bool :=
  match s with
  | .enumeration xs => xs.all p
  | .interval lo hi => intRangeAll p lo (hi - lo + 1).toNat

theorem setAllB_iff {s : IntSetValue} {p : Int → Bool} :
    setAllB s p = true ↔ ∀ i, s.Contains i → p i = true := by
  cases s with
  | enumeration xs => simp [setAllB, IntSetValue.Contains, List.all_eq_true]
  | interval lo hi =>
    simp only [setAllB, intRangeAll_iff, IntSetValue.Contains]
    constructor
    · rintro h i ⟨h1, h2⟩; exact h i h1 (by omega)
    · intro h i h1 h2; exact h i ⟨h1, by omega⟩

/-- Extensional set inclusion, decided.  An interval inside an interval
    is decided from the bounds; otherwise the elements of `a` are
    checked one by one, stopping at the first one missing from `b` (so
    an interval inside an enumeration `ys` costs at most `ys.length + 1`
    steps, whatever the interval's width). -/
def setSubB (a b : IntSetValue) : Bool :=
  match a, b with
  | .interval lo hi, .interval lo' hi' => decide (hi < lo ∨ (lo' ≤ lo ∧ hi ≤ hi'))
  | _, _ => setAllB a (fun x => decide (b.Contains x))

/-- `setSubB` decides extensional inclusion. -/
theorem setSubB_iff {a b : IntSetValue} :
    setSubB a b = true ↔ ∀ i, a.Contains i → b.Contains i := by
  have generic : setAllB a (fun x => decide (b.Contains x)) = true ↔
      ∀ i, a.Contains i → b.Contains i := by
    rw [setAllB_iff]; simp
  cases a with
  | enumeration xs => cases b <;> exact generic
  | interval lo hi =>
    cases b with
    | enumeration ys => exact generic
    | interval lo' hi' =>
      simp only [setSubB, decide_eq_true_eq, IntSetValue.Contains]
      constructor
      · rintro (h | ⟨h1, h2⟩) i ⟨hi1, hi2⟩
        · omega
        · exact ⟨by omega, by omega⟩
      · intro h
        by_cases hlt : hi < lo
        · exact Or.inl hlt
        · exact Or.inr ⟨(h lo ⟨Int.le_refl _, by omega⟩).1, (h hi ⟨by omega, Int.le_refl _⟩).2⟩

/-- Extensional set equality, decided. -/
def setEqB (a b : IntSetValue) : Bool :=
  setSubB a b && setSubB b a

/-- `setEqB` decides extensional equality. -/
theorem setEqB_iff {a b : IntSetValue} :
    setEqB a b = true ↔ ∀ i, a.Contains i ↔ b.Contains i := by
  unfold setEqB
  rw [Bool.and_eq_true, setSubB_iff, setSubB_iff]
  constructor
  · rintro ⟨hsub, hsup⟩ i
    exact ⟨hsub i, hsup i⟩
  · intro h
    exact ⟨fun i => (h i).mp, fun i => (h i).mpr⟩

/-- Extensional equality of an optional element result and a set:
    `none` is falsity (used by the set-valued element constraints). -/
private def setEqOptB (o : Option Value) (e : IntSetValue) : Bool :=
  match o with
  | some (.setOfInt v) => setEqB v e
  | _ => false

/-- `setEqOptB` decides optional extensional equality. -/
private theorem setEqOptB_iff (o : Option Value) (e : IntSetValue) :
    setEqOptB o e = true ↔
      (match o with
       | some (.setOfInt v) => ∀ j, v.Contains j ↔ e.Contains j
       | _ => False) := by
  cases o with
  | none => simp [setEqOptB]
  | some v =>
    cases v with
    | bool _ => simp [setEqOptB]
    | int _ => simp [setEqOptB]
    | setOfInt s => exact setEqB_iff
    | array _ => simp [setEqOptB]

/-- The total Boolean twin of the standard interpretation.  The five
    classic set predicates, the set comparisons (`set_ne`, `set_le`,
    `set_lt`, `set_superset`, `set_symdiff` and their reified
    variants), and the set-valued element family are decided through
    `setElems`/`lexLeB`/`lexLtB`; everything else delegates to
    `stdInterpB`. -/
def interpB (x : Ident) (args : List Value) : Bool :=
  match x.name with
  | "set_eq" =>
    match args with
    | [.setOfInt a, .setOfInt b] => setEqB a b
    | _ => false
  | "set_ne" =>
    match args with
    | [.setOfInt a, .setOfInt b] => !setEqB a b
    | _ => false
  | "set_le" =>
    match args with
    | [.setOfInt a, .setOfInt b] => lexLeB a.sortElems b.sortElems
    | _ => false
  | "set_lt" =>
    match args with
    | [.setOfInt a, .setOfInt b] => lexLtB a.sortElems b.sortElems
    | _ => false
  | "set_subset" =>
    match args with
    | [.setOfInt a, .setOfInt b] => setSubB a b
    | _ => false
  | "set_superset" =>
    match args with
    | [.setOfInt a, .setOfInt b] => setSubB b a
    | _ => false
  | "set_eq_reif" =>
    match args with
    | [.setOfInt a, .setOfInt b, .bool r] =>
        (r && setEqB a b) || (!r && !setEqB a b)
    | _ => false
  | "set_ne_reif" =>
    match args with
    | [.setOfInt a, .setOfInt b, .bool r] =>
        (r && !setEqB a b) || (!r && setEqB a b)
    | _ => false
  | "set_le_reif" =>
    match args with
    | [.setOfInt a, .setOfInt b, .bool r] =>
        (r && lexLeB a.sortElems b.sortElems) ||
          (!r && !lexLeB a.sortElems b.sortElems)
    | _ => false
  | "set_lt_reif" =>
    match args with
    | [.setOfInt a, .setOfInt b, .bool r] =>
        (r && lexLtB a.sortElems b.sortElems) ||
          (!r && !lexLtB a.sortElems b.sortElems)
    | _ => false
  | "set_subset_reif" =>
    match args with
    | [.setOfInt a, .setOfInt b, .bool r] =>
        (r && setSubB a b) || (!r && !setSubB a b)
    | _ => false
  | "set_superset_reif" =>
    match args with
    | [.setOfInt a, .setOfInt b, .bool r] =>
        (r && setSubB b a) || (!r && !setSubB b a)
    | _ => false
  | "set_union" =>
    match args with
    | [.setOfInt a, .setOfInt b, .setOfInt c] =>
        setSubB a c && setSubB b c &&
          (setElems c).all (fun x => decide (a.Contains x ∨ b.Contains x))
    | _ => false
  | "set_intersect" =>
    match args with
    | [.setOfInt a, .setOfInt b, .setOfInt c] =>
        (setElems c).all (fun x => decide (a.Contains x ∧ b.Contains x)) &&
        (setElems a).all (fun x => decide (x ∈ setElems b → c.Contains x))
    | _ => false
  | "set_diff" =>
    match args with
    | [.setOfInt a, .setOfInt b, .setOfInt c] =>
        (setElems c).all (fun x => decide (a.Contains x ∧ ¬ b.Contains x)) &&
        (setElems a).all (fun x => decide (¬ b.Contains x → c.Contains x))
    | _ => false
  | "set_symdiff" =>
    match args with
    | [.setOfInt a, .setOfInt b, .setOfInt c] =>
        (setElems c).all (fun x =>
          decide (¬ (a.Contains x ↔ b.Contains x))) &&
        (setElems a).all (fun x =>
          decide (¬ (a.Contains x ↔ b.Contains x) → c.Contains x)) &&
        (setElems b).all (fun x =>
          decide (¬ (a.Contains x ↔ b.Contains x) → c.Contains x))
    | _ => false
  | "array_set_element" =>
    match args with
    | [.int i, .array xs, .setOfInt e] =>
        setEqOptB (valuesGet1 xs i) e
    | _ => false
  | "array_var_set_element" =>
    match args with
    | [.int i, .array xs, .setOfInt e] =>
        setEqOptB (valuesGet1 xs i) e
    | _ => false
  | "array_var_set_element_nonshifted" =>
    match args with
    | [.int i, .array xs, .setOfInt e] =>
        setEqOptB (valuesGet1 xs i) e
    | _ => false
  | _ => stdInterpB x args

/-- The names of the extensional set predicates decided here.  The
    reified comparisons all have shape (set, set, bool); the plain
    comparisons and `set_eq`/`set_subset`/`set_ne`/`set_le`/`set_lt`/
    `set_superset` have shape (set, set); `set_union`, `set_intersect`,
    `set_diff`, `set_symdiff` have shape (set, set, set); the set
    element family has shape (int, array, set). -/
def setNames : List String :=
  ["set_eq", "set_ne", "set_le", "set_lt", "set_subset", "set_superset",
   "set_eq_reif", "set_ne_reif", "set_le_reif", "set_lt_reif",
   "set_subset_reif", "set_superset_reif", "set_union", "set_intersect",
   "set_diff", "set_symdiff", "array_set_element", "array_var_set_element",
   "array_var_set_element_nonshifted"]

/-! ### Per-name agreement lemmas for the extensional set predicates -/

/-- `set_eq` agreement. -/
private theorem interpB_set_eq_iff (a b : IntSetValue) :
    interpB (Ident.mk "set_eq") [.setOfInt a, .setOfInt b] = true ↔
      stdInterp (Ident.mk "set_eq") [.setOfInt a, .setOfInt b] := setEqB_iff

/-- `set_ne` agreement. -/
private theorem interpB_set_ne_iff (a b : IntSetValue) :
    interpB (Ident.mk "set_ne") [.setOfInt a, .setOfInt b] = true ↔
      stdInterp (Ident.mk "set_ne") [.setOfInt a, .setOfInt b] := by
  have hB : interpB (Ident.mk "set_ne") [.setOfInt a, .setOfInt b]
      = !setEqB a b := rfl
  have hI : stdInterp (Ident.mk "set_ne") [.setOfInt a, .setOfInt b]
      = ¬ ∀ i, a.Contains i ↔ b.Contains i := rfl
  rw [hB, hI]
  have hnot : (!setEqB a b) = true ↔ setEqB a b = false := by
    cases setEqB a b <;> simp
  rw [hnot]
  constructor
  · intro hf hP
    have htrue : setEqB a b = true := setEqB_iff.mpr hP
    rw [htrue] at hf
    exact Bool.noConfusion hf
  · intro hne
    cases hb : setEqB a b with
    | true => exact absurd (setEqB_iff.mp hb) hne
    | false => rfl

/-- `set_le` agreement. -/
private theorem interpB_set_le_iff (a b : IntSetValue) :
    interpB (Ident.mk "set_le") [.setOfInt a, .setOfInt b] = true ↔
      stdInterp (Ident.mk "set_le") [.setOfInt a, .setOfInt b] := by
  show lexLeB a.sortElems b.sortElems = true ↔ listLexLe a.sortElems b.sortElems
  exact lexLeB_iff

/-- `set_lt` agreement. -/
private theorem interpB_set_lt_iff (a b : IntSetValue) :
    interpB (Ident.mk "set_lt") [.setOfInt a, .setOfInt b] = true ↔
      stdInterp (Ident.mk "set_lt") [.setOfInt a, .setOfInt b] := by
  show lexLtB a.sortElems b.sortElems = true ↔ listLexLt a.sortElems b.sortElems
  exact lexLtB_iff _ _

/-- `set_subset` agreement. -/
private theorem interpB_set_subset_iff (a b : IntSetValue) :
    interpB (Ident.mk "set_subset") [.setOfInt a, .setOfInt b] = true ↔
      stdInterp (Ident.mk "set_subset") [.setOfInt a, .setOfInt b] := setSubB_iff

/-- `set_superset` agreement. -/
private theorem interpB_set_superset_iff (a b : IntSetValue) :
    interpB (Ident.mk "set_superset") [.setOfInt a, .setOfInt b] = true ↔
      stdInterp (Ident.mk "set_superset") [.setOfInt a, .setOfInt b] := by
  show setSubB b a = true ↔ ∀ i, b.Contains i → a.Contains i
  exact setSubB_iff

/-- `set_union` agreement. -/
private theorem interpB_set_union_iff (a b c : IntSetValue) :
    interpB (Ident.mk "set_union") [.setOfInt a, .setOfInt b, .setOfInt c] = true ↔
      stdInterp (Ident.mk "set_union") [.setOfInt a, .setOfInt b, .setOfInt c] := by
  have hB : interpB (Ident.mk "set_union") [.setOfInt a, .setOfInt b, .setOfInt c]
      = (setSubB a c && setSubB b c &&
          (setElems c).all (fun x => decide (a.Contains x ∨ b.Contains x))) := rfl
  have hI : stdInterp (Ident.mk "set_union") [.setOfInt a, .setOfInt b, .setOfInt c]
      = (∀ i, c.Contains i ↔ a.Contains i ∨ b.Contains i) := rfl
  rw [hB, hI]
  simp only [Bool.and_eq_true, setSubB_iff,
    List.all_eq_true, setElems_mem_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hac, hbc⟩, hcc⟩ i
    constructor
    · intro hmem
      rcases hcc i hmem with hin | hin
      · exact Or.inl hin
      · exact Or.inr hin
    · rintro (hin | hin)
      · exact hac i hin
      · exact hbc i hin
  · intro h
    refine ⟨⟨fun i hin => (h i).mpr (Or.inl hin),
      fun i hin => (h i).mpr (Or.inr hin)⟩, ?_⟩
    intro i hmem
    rcases (h i).mp hmem with hin | hin
    · exact Or.inl hin
    · exact Or.inr hin

/-- `set_intersect` agreement. -/
private theorem interpB_set_intersect_iff (a b c : IntSetValue) :
    interpB (Ident.mk "set_intersect") [.setOfInt a, .setOfInt b, .setOfInt c] = true ↔
      stdInterp (Ident.mk "set_intersect") [.setOfInt a, .setOfInt b, .setOfInt c] := by
  have hB : interpB (Ident.mk "set_intersect") [.setOfInt a, .setOfInt b, .setOfInt c]
      = ((setElems c).all (fun x => decide (a.Contains x ∧ b.Contains x)) &&
         (setElems a).all (fun x => decide (x ∈ setElems b → c.Contains x))) := rfl
  have hI : stdInterp (Ident.mk "set_intersect") [.setOfInt a, .setOfInt b, .setOfInt c]
      = (∀ i, c.Contains i ↔ a.Contains i ∧ b.Contains i) := rfl
  rw [hB, hI]
  simp only [Bool.and_eq_true, List.all_eq_true,
    setElems_mem_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩ i
    constructor
    · intro hmem
      exact h1 i hmem
    · rintro ⟨hia, hib⟩
      exact h2 i hia hib
  · intro h
    constructor
    · intro i hmem
      exact (h i).mp hmem
    · intro i hia hib
      exact (h i).mpr ⟨hia, hib⟩

/-- `set_diff` agreement. -/
private theorem interpB_set_diff_iff (a b c : IntSetValue) :
    interpB (Ident.mk "set_diff") [.setOfInt a, .setOfInt b, .setOfInt c] = true ↔
      stdInterp (Ident.mk "set_diff") [.setOfInt a, .setOfInt b, .setOfInt c] := by
  have hB : interpB (Ident.mk "set_diff") [.setOfInt a, .setOfInt b, .setOfInt c]
      = ((setElems c).all (fun x => decide (a.Contains x ∧ ¬ b.Contains x)) &&
         (setElems a).all (fun x => decide (¬ b.Contains x → c.Contains x))) := rfl
  have hI : stdInterp (Ident.mk "set_diff") [.setOfInt a, .setOfInt b, .setOfInt c]
      = (∀ i, c.Contains i ↔ a.Contains i ∧ ¬ b.Contains i) := rfl
  rw [hB, hI]
  simp only [Bool.and_eq_true, List.all_eq_true,
    setElems_mem_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩ i
    constructor
    · intro hmem
      exact h1 i hmem
    · rintro ⟨hia, hnb⟩
      exact h2 i hia hnb
  · intro h
    constructor
    · intro i hmem
      exact (h i).mp hmem
    · intro i hia hnb
      exact (h i).mpr ⟨hia, hnb⟩

/-- `set_symdiff` agreement: `c` contains exactly the elements in
    exactly one of `a` and `b`. -/
private theorem interpB_set_symdiff_iff (a b c : IntSetValue) :
    interpB (Ident.mk "set_symdiff") [.setOfInt a, .setOfInt b, .setOfInt c] = true ↔
      stdInterp (Ident.mk "set_symdiff") [.setOfInt a, .setOfInt b, .setOfInt c] := by
  -- the three decided conjuncts: every element of `c` is in exactly
  -- one of `a`/`b`; every element of `a` (resp. `b`) that is in
  -- exactly one of `a`/`b` is in `c`
  have h1 : ((setElems c).all
      (fun x => decide (¬ (a.Contains x ↔ b.Contains x)))) = true ↔
      ∀ i, c.Contains i → ¬ (a.Contains i ↔ b.Contains i) := by
    constructor
    · intro h i hci
      have hall := List.all_eq_true.mp h
      exact of_decide_eq_true (hall i (setElems_mem_iff.mp hci))
    · intro h
      refine List.all_eq_true.mpr ?_
      intro x hx
      exact decide_eq_true (h x (setElems_mem_iff.mpr hx))
  have h2 : ∀ s : IntSetValue,
      ((setElems s).all
        (fun x => decide (¬ (a.Contains x ↔ b.Contains x) → c.Contains x))) = true ↔
      ∀ i, s.Contains i → (¬ (a.Contains i ↔ b.Contains i) → c.Contains i) := by
    intro s
    constructor
    · intro h i hsi hxn
      have hall := List.all_eq_true.mp h
      exact of_decide_eq_true (hall i (setElems_mem_iff.mp hsi)) hxn
    · intro h
      refine List.all_eq_true.mpr ?_
      intro x hx
      exact decide_eq_true (h x (setElems_mem_iff.mpr hx))
  have hB : interpB (Ident.mk "set_symdiff") [.setOfInt a, .setOfInt b, .setOfInt c]
      = ((setElems c).all (fun x =>
           decide (¬ (a.Contains x ↔ b.Contains x))) &&
         (setElems a).all (fun x =>
           decide (¬ (a.Contains x ↔ b.Contains x) → c.Contains x)) &&
         (setElems b).all (fun x =>
           decide (¬ (a.Contains x ↔ b.Contains x) → c.Contains x))) := rfl
  have hI : stdInterp (Ident.mk "set_symdiff") [.setOfInt a, .setOfInt b, .setOfInt c]
      = (∀ i, c.Contains i ↔ ¬ (a.Contains i ↔ b.Contains i)) := rfl
  rw [hB, hI, Bool.and_eq_true, Bool.and_eq_true]
  rw [h1, h2 a, h2 b]
  constructor
  · rintro ⟨⟨hc, ha⟩, hb⟩ i
    constructor
    · intro hci
      exact hc i hci
    · intro hxn
      by_cases hia : a.Contains i
      · exact ha i hia hxn
      · have hib : b.Contains i := by
          by_cases hib' : b.Contains i
          · exact hib'
          · exact absurd hxn (fun hn =>
              hn ⟨fun hai => absurd hai hia, fun hbi => absurd hbi hib'⟩)
        exact hb i hib hxn
  · intro h
    refine ⟨⟨fun i hci => (h i).mp hci, fun i hia hxn => (h i).mpr hxn⟩,
      fun i hib hxn => (h i).mpr hxn⟩

/-- `array_set_element` agreement. -/
private theorem interpB_array_set_element_iff (i : Int) (xs : List Value)
    (e : IntSetValue) :
    interpB (Ident.mk "array_set_element") [.int i, .array xs, .setOfInt e] = true ↔
      stdInterp (Ident.mk "array_set_element") [.int i, .array xs, .setOfInt e] :=
  setEqOptB_iff (valuesGet1 xs i) e

/-- `array_var_set_element` agreement. -/
private theorem interpB_array_var_set_element_iff (i : Int) (xs : List Value)
    (e : IntSetValue) :
    interpB (Ident.mk "array_var_set_element") [.int i, .array xs, .setOfInt e] = true ↔
      stdInterp (Ident.mk "array_var_set_element") [.int i, .array xs, .setOfInt e] :=
  setEqOptB_iff (valuesGet1 xs i) e

/-- `array_var_set_element_nonshifted` agreement. -/
private theorem interpB_array_var_set_element_nonshifted_iff (i : Int)
    (xs : List Value) (e : IntSetValue) :
    interpB (Ident.mk "array_var_set_element_nonshifted")
        [.int i, .array xs, .setOfInt e] = true ↔
      stdInterp (Ident.mk "array_var_set_element_nonshifted")
        [.int i, .array xs, .setOfInt e] :=
  setEqOptB_iff (valuesGet1 xs i) e

/-! ### Reified-set helpers -/

/-- Reified agreement for a decided base predicate `p`/`P`: the twin
    `(r && p) || (!r && !p)` decides `r ↔ P`. -/
private theorem reifB_iff {p : Bool} {P : Prop} (h : p = true ↔ P) (r : Bool) :
    ((r && p) || (!r && !p)) = true ↔
      (r = true ∧ P) ∨ (r = false ∧ ¬ P) := by
  cases r <;> cases p <;> simp_all

/-- Reified agreement for a *negated* decided base predicate: the twin
    `(r && !p) || (!r && p)` decides `r ↔ ¬P`. -/
private theorem reifNB_iff {p : Bool} {P : Prop} (h : p = true ↔ P) (r : Bool) :
    ((r && !p) || (!r && p)) = true ↔
      (r = true ∧ ¬ P) ∨ (r = false ∧ P) := by
  cases r <;> cases p <;> simp_all

/-- `set_eq_reif` agreement. -/
private theorem interpB_set_eq_reif_iff (a b : IntSetValue) (r : Bool) :
    interpB (Ident.mk "set_eq_reif") [.setOfInt a, .setOfInt b, .bool r] = true ↔
      stdInterp (Ident.mk "set_eq_reif") [.setOfInt a, .setOfInt b, .bool r] := by
  have hB : interpB (Ident.mk "set_eq_reif") [.setOfInt a, .setOfInt b, .bool r]
      = ((r && setEqB a b) || (!r && !setEqB a b)) := rfl
  have hI : stdInterp (Ident.mk "set_eq_reif") [.setOfInt a, .setOfInt b, .bool r]
      = ((r = true ∧ ∀ i, a.Contains i ↔ b.Contains i) ∨
          (r = false ∧ ¬ ∀ i, a.Contains i ↔ b.Contains i)) := rfl
  rw [hB, hI]
  exact reifB_iff setEqB_iff r

/-- `set_ne_reif` agreement. -/
private theorem interpB_set_ne_reif_iff (a b : IntSetValue) (r : Bool) :
    interpB (Ident.mk "set_ne_reif") [.setOfInt a, .setOfInt b, .bool r] = true ↔
      stdInterp (Ident.mk "set_ne_reif") [.setOfInt a, .setOfInt b, .bool r] := by
  have hB : interpB (Ident.mk "set_ne_reif") [.setOfInt a, .setOfInt b, .bool r]
      = ((r && !setEqB a b) || (!r && setEqB a b)) := rfl
  have hI : stdInterp (Ident.mk "set_ne_reif") [.setOfInt a, .setOfInt b, .bool r]
      = ((r = true ∧ ¬ ∀ i, a.Contains i ↔ b.Contains i) ∨
          (r = false ∧ ∀ i, a.Contains i ↔ b.Contains i)) := rfl
  rw [hB, hI]
  exact reifNB_iff setEqB_iff r

/-- `set_le_reif` agreement. -/
private theorem interpB_set_le_reif_iff (a b : IntSetValue) (r : Bool) :
    interpB (Ident.mk "set_le_reif") [.setOfInt a, .setOfInt b, .bool r] = true ↔
      stdInterp (Ident.mk "set_le_reif") [.setOfInt a, .setOfInt b, .bool r] := by
  have hB : interpB (Ident.mk "set_le_reif") [.setOfInt a, .setOfInt b, .bool r]
      = ((r && lexLeB a.sortElems b.sortElems) ||
          (!r && !lexLeB a.sortElems b.sortElems)) := rfl
  have hI : stdInterp (Ident.mk "set_le_reif") [.setOfInt a, .setOfInt b, .bool r]
      = ((r = true ∧ listLexLe a.sortElems b.sortElems) ∨
          (r = false ∧ ¬ listLexLe a.sortElems b.sortElems)) := rfl
  rw [hB, hI]
  exact reifB_iff (lexLeB_iff (xs := a.sortElems) (ys := b.sortElems)) r

/-- `set_lt_reif` agreement. -/
private theorem interpB_set_lt_reif_iff (a b : IntSetValue) (r : Bool) :
    interpB (Ident.mk "set_lt_reif") [.setOfInt a, .setOfInt b, .bool r] = true ↔
      stdInterp (Ident.mk "set_lt_reif") [.setOfInt a, .setOfInt b, .bool r] := by
  have hB : interpB (Ident.mk "set_lt_reif") [.setOfInt a, .setOfInt b, .bool r]
      = ((r && lexLtB a.sortElems b.sortElems) ||
          (!r && !lexLtB a.sortElems b.sortElems)) := rfl
  have hI : stdInterp (Ident.mk "set_lt_reif") [.setOfInt a, .setOfInt b, .bool r]
      = ((r = true ∧ listLexLt a.sortElems b.sortElems) ∨
          (r = false ∧ ¬ listLexLt a.sortElems b.sortElems)) := rfl
  rw [hB, hI]
  exact reifB_iff (lexLtB_iff _ _) r

/-- `set_subset_reif` agreement. -/
private theorem interpB_set_subset_reif_iff (a b : IntSetValue) (r : Bool) :
    interpB (Ident.mk "set_subset_reif") [.setOfInt a, .setOfInt b, .bool r] = true ↔
      stdInterp (Ident.mk "set_subset_reif") [.setOfInt a, .setOfInt b, .bool r] := by
  have hB : interpB (Ident.mk "set_subset_reif") [.setOfInt a, .setOfInt b, .bool r]
      = ((r && setSubB a b) || (!r && !setSubB a b)) := rfl
  have hI : stdInterp (Ident.mk "set_subset_reif") [.setOfInt a, .setOfInt b, .bool r]
      = ((r = true ∧ ∀ i, a.Contains i → b.Contains i) ∨
          (r = false ∧ ¬ ∀ i, a.Contains i → b.Contains i)) := rfl
  rw [hB, hI]
  exact reifB_iff setSubB_iff r

/-- `set_superset_reif` agreement. -/
private theorem interpB_set_superset_reif_iff (a b : IntSetValue) (r : Bool) :
    interpB (Ident.mk "set_superset_reif") [.setOfInt a, .setOfInt b, .bool r] = true ↔
      stdInterp (Ident.mk "set_superset_reif") [.setOfInt a, .setOfInt b, .bool r] := by
  have hB : interpB (Ident.mk "set_superset_reif") [.setOfInt a, .setOfInt b, .bool r]
      = ((r && setSubB b a) || (!r && !setSubB b a)) := rfl
  have hI : stdInterp (Ident.mk "set_superset_reif") [.setOfInt a, .setOfInt b, .bool r]
      = ((r = true ∧ ∀ i, b.Contains i → a.Contains i) ∨
          (r = false ∧ ¬ ∀ i, b.Contains i → a.Contains i)) := rfl
  rw [hB, hI]
  exact reifB_iff (setSubB_iff (a := b) (b := a)) r

/-- Agreement of the twin with the mathematical interpretation on the
    extensional set predicates: the dispatcher case-splits on the
    argument shape first; each admissible shape covers only a handful
    of names (closed by the per-name lemmas), and every other
    combination makes both sides false. -/
theorem interpB_set_iff {x : Ident} {args : List Value}
    (hname : x.name ∈ setNames) :
    interpB x args = true ↔ stdInterp x args := by
  obtain ⟨n⟩ := x
  have hmem : n ∈ setNames := hname
  simp only [setNames, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  -- Shape dispatch on the (now concrete) name: each of the 19 names
  -- admits only one shape; a single unfolding decides the rest.
  all_goals
    cases args with
    | nil =>
        exact iff_of_eq (Bool.false_eq_true ..)
    | cons v vs =>
      cases v with
      | setOfInt a =>
          cases vs with
          | cons w ws =>
            cases w with
            | setOfInt b =>
              cases ws with
              | nil =>
                  first
                  | exact interpB_set_eq_iff a b
                  | exact interpB_set_ne_iff a b
                  | exact interpB_set_le_iff a b
                  | exact interpB_set_lt_iff a b
                  | exact interpB_set_subset_iff a b
                  | exact interpB_set_superset_iff a b
                  | exact iff_of_eq (Bool.false_eq_true ..)
              | cons u us =>
                cases u with
                | bool r =>
                    cases us with
                    | nil =>
                        first
                        | exact interpB_set_eq_reif_iff a b r
                        | exact interpB_set_ne_reif_iff a b r
                        | exact interpB_set_le_reif_iff a b r
                        | exact interpB_set_lt_reif_iff a b r
                        | exact interpB_set_subset_reif_iff a b r
                        | exact interpB_set_superset_reif_iff a b r
                        | exact iff_of_eq (Bool.false_eq_true ..)
                    | cons _ _ =>
                        exact iff_of_eq (Bool.false_eq_true ..)
                | setOfInt c =>
                  cases us with
                  | nil =>
                      first
                      | exact interpB_set_union_iff a b c
                      | exact interpB_set_intersect_iff a b c
                      | exact interpB_set_diff_iff a b c
                      | exact interpB_set_symdiff_iff a b c
                      | exact iff_of_eq (Bool.false_eq_true ..)
                  | cons _ _ =>
                      exact iff_of_eq (Bool.false_eq_true ..)
                | int _ | array _ =>
                    exact iff_of_eq (Bool.false_eq_true ..)
            | bool _ | int _ | array _ =>
                exact iff_of_eq (Bool.false_eq_true ..)
          | nil =>
              exact iff_of_eq (Bool.false_eq_true ..)
      | int i =>
          cases vs with
          | cons w ws =>
            cases w with
            | array xs =>
              cases ws with
              | cons u us =>
                cases u with
                | setOfInt e =>
                  cases us with
                  | nil =>
                      first
                      | exact interpB_array_set_element_iff i xs e
                      | exact interpB_array_var_set_element_iff i xs e
                      | exact interpB_array_var_set_element_nonshifted_iff i xs e
                      | exact iff_of_eq (Bool.false_eq_true ..)
                  | cons _ _ =>
                      exact iff_of_eq (Bool.false_eq_true ..)
                | bool _ | int _ | array _ =>
                    exact iff_of_eq (Bool.false_eq_true ..)
              | nil =>
                  exact iff_of_eq (Bool.false_eq_true ..)
            | bool _ | int _ | setOfInt _ =>
                exact iff_of_eq (Bool.false_eq_true ..)
          | nil =>
              exact iff_of_eq (Bool.false_eq_true ..)
      | bool _ | array _ =>
          exact iff_of_eq (Bool.false_eq_true ..)

/-- The names of the non-extensional standard predicates (those whose
    executable twin is `stdInterpB` itself). -/
def stdNames : List String :=
  ["int_eq", "int_ne", "int_le", "int_lt", "int_ge", "int_gt",
   "int_eq_reif", "int_ne_reif", "int_le_reif", "int_lt_reif",
   "int_ge_reif", "int_gt_reif", "bool_eq", "bool_not", "bool_and",
   "bool_or", "bool_xor", "bool_le", "bool_lt", "bool_eq_reif",
   "bool_le_reif", "bool_lt_reif", "bool_clause", "bool_clause_reif",
   "bool2int", "int_plus", "int_minus", "int_times", "int_div",
   "int_mod", "int_min", "int_max", "int_abs", "int_pow",
   "int_pow_fixed", "set_in", "set_in_reif", "dom", "set_card",
   "all_different", "all_different_except_0", "int_lin_eq",
   "int_lin_le", "int_lin_ne", "int_lin_eq_reif", "int_lin_le_reif",
   "int_lin_ne_reif", "bool_lin_eq", "bool_lin_le",
   "array_int_element", "array_var_int_element",
   "array_var_int_element_nonshifted", "array_bool_element",
   "array_var_bool_element", "array_var_bool_element_nonshifted",
   "array_int_maximum", "array_int_minimum", "array_bool_and",
   "array_bool_xor", "array_bool_or", "true"]

/-- `stdInterpB` agrees with `stdInterp` on the non-extensional
    predicates: a dispatch on the name list, each case being the
    per-name lemma `builtin_<name>_iff` from `FznStdLib.lean`. -/
theorem stdInterpB_agree (n : String) (args : List Value)
    (hn : n ∈ stdNames) :
    stdInterpB (Ident.mk n) args = true ↔ stdInterp (Ident.mk n) args := by
  simp only [stdNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | exact builtin_int_eq_iff args
    | exact builtin_int_ne_iff args
    | exact builtin_int_le_iff args
    | exact builtin_int_lt_iff args
    | exact builtin_int_ge_iff args
    | exact builtin_int_gt_iff args
    | exact builtin_int_eq_reif_iff args
    | exact builtin_int_ne_reif_iff args
    | exact builtin_int_le_reif_iff args
    | exact builtin_int_lt_reif_iff args
    | exact builtin_int_ge_reif_iff args
    | exact builtin_int_gt_reif_iff args
    | exact builtin_bool_eq_iff args
    | exact builtin_bool_not_iff args
    | exact builtin_bool_and_iff args
    | exact builtin_bool_or_iff args
    | exact builtin_bool_xor_iff args
    | exact builtin_bool_le_iff args
    | exact builtin_bool_lt_iff args
    | exact builtin_bool_eq_reif_iff args
    | exact builtin_bool_le_reif_iff args
    | exact builtin_bool_lt_reif_iff args
    | exact builtin_bool_clause_iff args
    | exact builtin_bool_clause_reif_iff args
    | exact builtin_bool2int_iff args
    | exact builtin_int_plus_iff args
    | exact builtin_int_minus_iff args
    | exact builtin_int_times_iff args
    | exact builtin_int_div_iff args
    | exact builtin_int_mod_iff args
    | exact builtin_int_min_iff args
    | exact builtin_int_max_iff args
    | exact builtin_int_abs_iff args
    | exact builtin_int_pow_iff args
    | exact builtin_int_pow_fixed_iff args
    | exact builtin_set_in_iff args
    | exact builtin_set_in_reif_iff args
    | exact builtin_dom_iff args
    | exact builtin_set_card_iff args
    | exact builtin_all_different_iff args
    | exact builtin_all_different_except_0_iff args
    | exact builtin_int_lin_eq_iff args
    | exact builtin_int_lin_le_iff args
    | exact builtin_int_lin_ne_iff args
    | exact builtin_int_lin_eq_reif_iff args
    | exact builtin_int_lin_le_reif_iff args
    | exact builtin_int_lin_ne_reif_iff args
    | exact builtin_bool_lin_eq_iff args
    | exact builtin_bool_lin_le_iff args
    | exact builtin_array_int_element_iff args
    | exact builtin_array_var_int_element_iff args
    | exact builtin_array_var_int_element_nonshifted_iff args
    | exact builtin_array_bool_element_iff args
    | exact builtin_array_var_bool_element_iff args
    | exact builtin_array_var_bool_element_nonshifted_iff args
    | exact builtin_array_int_maximum_iff args
    | exact builtin_array_int_minimum_iff args
    | exact builtin_array_bool_and_iff args
    | exact builtin_array_bool_xor_iff args
    | exact builtin_array_bool_or_iff args
    | exact builtin_true_iff args

/-- Agreement on the non-extensional fragment: for names outside the
    extensional set-predicate list, `interpB` delegates to
    `stdInterpB`, whose agreement is `stdInterpB_agree`. -/
theorem interpB_std_iff {n : String} {args : List Value}
    (hn : n ∈ stdNames) :
    interpB (Ident.mk n) args = true ↔ stdInterp (Ident.mk n) args := by
  unfold interpB
  split
  next heq => exact absurd hn (by rw [show n = "set_eq" from heq]; decide)
  next heq => exact absurd hn (by rw [show n = "set_ne" from heq]; decide)
  next heq => exact absurd hn (by rw [show n = "set_le" from heq]; decide)
  next heq => exact absurd hn (by rw [show n = "set_lt" from heq]; decide)
  next heq => exact absurd hn (by rw [show n = "set_subset" from heq]; decide)
  next heq => exact absurd hn (by rw [show n = "set_superset" from heq]; decide)
  next heq => exact absurd hn (by rw [show n = "set_eq_reif" from heq]; decide)
  next heq => exact absurd hn (by rw [show n = "set_ne_reif" from heq]; decide)
  next heq => exact absurd hn (by rw [show n = "set_le_reif" from heq]; decide)
  next heq => exact absurd hn (by rw [show n = "set_lt_reif" from heq]; decide)
  next heq => exact absurd hn (by rw [show n = "set_subset_reif" from heq]; decide)
  next heq => exact absurd hn (by rw [show n = "set_superset_reif" from heq]; decide)
  next heq => exact absurd hn (by rw [show n = "set_union" from heq]; decide)
  next heq => exact absurd hn (by rw [show n = "set_intersect" from heq]; decide)
  next heq => exact absurd hn (by rw [show n = "set_diff" from heq]; decide)
  next heq => exact absurd hn (by rw [show n = "set_symdiff" from heq]; decide)
  next heq => exact absurd hn (by rw [show n = "array_set_element" from heq]; decide)
  next heq => exact absurd hn (by rw [show n = "array_var_set_element" from heq]; decide)
  next heq => exact absurd hn (by rw [show n = "array_var_set_element_nonshifted" from heq]; decide)
  exact stdInterpB_agree n args hn

/-- The names of all predicates with executable, verified
    interpretations. -/
def checkableNames : List String :=
  stdNames ++ setNames

end LeanFzn.Semantics.Evaluation

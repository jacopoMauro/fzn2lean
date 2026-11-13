import LeanFzn.Semantics.Globals.LexSort
open LeanFzn.Semantics


/-!
# Reverse and 2D lexicographic global constraints

Mathematical interpretations (`lexChainInterp`) and executable Boolean
twins (`lexChainInterpB`) for the reverse lexicographic predicates and
the chain/matrix lexicographic family of the pinned MiniZinc 2.10.1
tree.

Per the pinned decompositions (recorded in
`specification/flatzinc_specification_assumptions.md`, G24):

* `fzn_lex_greater_int(xs, ys) ≡ fzn_lex_less_int(ys, xs)` and
  `fzn_lex_greatereq_int(xs, ys) ≡ fzn_lex_lesseq_int(ys, xs)`
  (upstream has no greater-direction `fzn_` files; user-level
  `lex_greater` is defined by argument swap, `lex_greater.mzn`).
* `fzn_lex_chain_less_int` / `fzn_lex_chain_lesseq_int` compare
  adjacent *columns* of a matrix (`fzn_lex_chain_less_int.mzn`);
  `fzn_lex2` compares adjacent columns of the matrix and of its
  transpose with `lesseq`, `fzn_strict_lex2` with `less`
  (`fzn_lex2.mzn`, `fzn_strict_lex2.mzn`); the orbitope variant adds
  row-sum conditions (`_kind` 1: exactly 1; 2: at most 1;
  `fzn_lex_chain_lesseq_orbitope.mzn`).
* `fzn_lex_chain_greater_int` / `fzn_lex_chain_greatereq_int` /
  `fzn_lex_chain_greatereq_orbitope` are the greater-direction
  versions: the user-level `lex_chain_greater.mzn`,
  `lex_chain_greatereq.mzn`, and
  `lex_chain_greatereq_orbitope.mzn` reverse the column index set
  (`index_set_2of2`) and delegate to the less/lesseq versions, so
  these are `lexChainLess`/`lexChainLesseq`/`orbitopeProp` on the
  *reversed* column list (`cols.reverse`).

**Representation (G24):** the 2D predicates are declared
`array [int,int] of var int` upstream, but FlatZinc's grammar has
only 1D arrays and flat literals.  The matrix therefore arrives as a
*nested* array value (one inner list per column, in FlatZinc
row-major order) — an explicit, documented extension of the value
model used only by these predicates.  Real `.fzn` files cannot carry
such arguments; the interpretation exists so the supported-name
inventory is complete and the checker reports genuine semantic
content rather than guessing.
-/

open LeanFzn.Semantics

open LeanFzn.Semantics.Evaluation

namespace LeanFzn.Semantics.Globals.LexChain

open LeanFzn LeanFzn.Semantics.Globals LeanFzn.Semantics.Evaluation

/-! ## Matrix helpers

A matrix is a list of columns (the FlatZinc 2D argument order). -/

/-- Lexicographic strict order chain over adjacent columns. -/
def lexChainLess (cols : List (List Int)) : Prop :=
  match cols with
  | [] => True
  | [_] => True
  | a :: b :: rest => LexSort.lexLess a b ∧ lexChainLess (b :: rest)

/-- Boolean twin of `lexChainLess`. -/
def lexChainLessB (cols : List (List Int)) : Bool :=
  match cols with
  | [] => true
  | [_] => true
  | a :: b :: rest => LexSort.lexLessB a b && lexChainLessB (b :: rest)

theorem lexChainLessB_iff (cols : List (List Int)) :
    lexChainLessB cols = true ↔ lexChainLess cols := by
  induction cols with
  | nil => simp [lexChainLessB, lexChainLess]
  | cons a cols ih =>
    cases cols with
    | nil => simp [lexChainLessB, lexChainLess]
    | cons b rest =>
      simp only [lexChainLessB, lexChainLess, Bool.and_eq_true, LexSort.lexLessB_iff,
        ih]

/-- Lexicographic non-strict order chain over adjacent columns. -/
def lexChainLesseq (cols : List (List Int)) : Prop :=
  match cols with
  | [] => True
  | [_] => True
  | a :: b :: rest => LexSort.lexLesseq a b ∧ lexChainLesseq (b :: rest)

/-- Boolean twin of `lexChainLesseq`. -/
def lexChainLesseqB (cols : List (List Int)) : Bool :=
  match cols with
  | [] => true
  | [_] => true
  | a :: b :: rest => LexSort.lexLesseqB a b && lexChainLesseqB (b :: rest)

theorem lexChainLesseqB_iff (cols : List (List Int)) :
    lexChainLesseqB cols = true ↔ lexChainLesseq cols := by
  induction cols with
  | nil => simp [lexChainLesseqB, lexChainLesseq]
  | cons a cols ih =>
    cases cols with
    | nil => simp [lexChainLesseqB, lexChainLesseq]
    | cons b rest =>
      simp only [lexChainLesseqB, lexChainLesseq, Bool.and_eq_true,
        LexSort.lexLesseqB_iff, ih]

/-- Lexicographic strict-greater order chain over adjacent columns:
    `fzn_lex_chain_greater_int` is `lex_chain_less_int` on the
    reversed columns (per `lex_chain_greater.mzn`, which reverses
    `index_set_2of2` before delegating to `lex_chain_less`). -/
def lexChainGreater (cols : List (List Int)) : Prop :=
  lexChainLess cols.reverse

/-- Boolean twin of `lexChainGreater`. -/
def lexChainGreaterB (cols : List (List Int)) : Bool :=
  lexChainLessB cols.reverse

theorem lexChainGreaterB_iff (cols : List (List Int)) :
    lexChainGreaterB cols = true ↔ lexChainGreater cols :=
  lexChainLessB_iff cols.reverse

/-- Lexicographic non-strict-greater order chain over adjacent
    columns: `fzn_lex_chain_greatereq_int` is `lex_chain_lesseq_int`
    on the reversed columns (per `lex_chain_greatereq.mzn`). -/
def lexChainGreatereq (cols : List (List Int)) : Prop :=
  lexChainLesseq cols.reverse

/-- Boolean twin of `lexChainGreatereq`. -/
def lexChainGreatereqB (cols : List (List Int)) : Bool :=
  lexChainLesseqB cols.reverse

theorem lexChainGreatereqB_iff (cols : List (List Int)) :
    lexChainGreatereqB cols = true ↔ lexChainGreatereq cols :=
  lexChainLesseqB_iff cols.reverse

/-- Transpose of a column-list matrix: row `i` of the result is the
    `i`-th element of every column. -/
def transpose (cols : List (List Int)) : List (List Int) :=
  let n := ((cols.map List.length).foldl (fun a b => max a b) 0)
  (List.range n).map (fun i => cols.map (fun c => c.getD i 0))

/-- `lex2`: adjacent columns and adjacent rows non-decreasing. -/
def lex2Prop (cols : List (List Int)) : Prop :=
  lexChainLesseq cols ∧ lexChainLesseq (transpose cols)

def lex2B (cols : List (List Int)) : Bool :=
  lexChainLesseqB cols && lexChainLesseqB (transpose cols)

theorem lex2B_iff (cols : List (List Int)) :
    lex2B cols = true ↔ lex2Prop cols := by
  simp only [lex2B, lex2Prop, Bool.and_eq_true, lexChainLesseqB_iff]

/-- Strict `lex2`: adjacent columns strictly increasing and the same
    on the transpose. -/
def strictLex2Prop (cols : List (List Int)) : Prop :=
  lexChainLess cols ∧ lexChainLess (transpose cols)

def strictLex2B (cols : List (List Int)) : Bool :=
  lexChainLessB cols && lexChainLessB (transpose cols)

theorem strictLex2B_iff (cols : List (List Int)) :
    strictLex2B cols = true ↔ strictLex2Prop cols := by
  simp only [strictLex2B, strictLex2Prop, Bool.and_eq_true, lexChainLessB_iff]

/-- Row sums of a column-list matrix (row `i` sums element `i` of
    every column; ragged rows contribute `0` for out-of-range
    columns, matching `List.getD`). -/
def rowSums (cols : List (List Int)) : List Int :=
  (List.range ((cols.map List.length).foldl (fun a b => max a b) 0)).map
    (fun i => (cols.map (fun c => c.getD i 0)).foldl (fun a b => a + b) 0)

/-- The orbitope: `lesseq` column chain plus row-sum conditions.
    `_kind` 0 = none, 1 = every row sums to 1, 2 = every row sums to
    at most 1 (per `fzn_lex_chain_lesseq_orbitope.mzn`). -/
def orbitopeProp (kind : Int) (cols : List (List Int)) : Prop :=
  lexChainLesseq cols ∧
    (kind = 1 → (rowSums cols).all (· = 1)) ∧
    (kind = 2 → (rowSums cols).all (· ≤ 1))
def orbitopeB (kind : Int) (cols : List (List Int)) : Bool :=
  lexChainLesseqB cols &&
    (!(kind == 1) || (rowSums cols).all (fun s => decide (s = 1))) &&
    (!(kind == 2) || (rowSums cols).all (fun s => decide (s ≤ 1)))

theorem orbitopeB_iff (kind : Int) (cols : List (List Int)) :
    orbitopeB kind cols = true ↔ orbitopeProp kind cols := by
  simp only [orbitopeB, orbitopeProp, Bool.and_eq_true, lexChainLesseqB_iff,
    Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true,
    decide_eq_true_iff]
  cases hkind1 : (kind == 1) with
  | true =>
      have hk1 : kind = 1 := by simpa using hkind1
      subst hk1
      simp
  | false =>
      have hk1 : kind ≠ 1 := by simpa using hkind1
      cases hkind2 : (kind == 2) with
      | true =>
          have hk2 : kind = 2 := by simpa using hkind2
          subst hk2
          simp
      | false =>
          have hk2 : kind ≠ 2 := by simpa using hkind2
          simp [hk1, hk2]

/-- The greater-eq orbitope: `fzn_lex_chain_greatereq_orbitope` is
    `lex_chain_lesseq_orbitope` on the reversed columns with the same
    `_kind` (per `lex_chain_greatereq_orbitope.mzn`, which reverses
    `index_set_2of2` before delegating). -/
def orbitopeGreatereqProp (kind : Int) (cols : List (List Int)) : Prop :=
  orbitopeProp kind cols.reverse

def orbitopeGreatereqB (kind : Int) (cols : List (List Int)) : Bool :=
  orbitopeB kind cols.reverse

theorem orbitopeGreatereqB_iff (kind : Int) (cols : List (List Int)) :
    orbitopeGreatereqB kind cols = true ↔ orbitopeGreatereqProp kind cols :=
  orbitopeB_iff kind cols.reverse

/-! ## Argument decoders -/

/-- Decode a nested-array matrix argument: a list of columns. -/
private def matrixArg (args : List Value) : Option (List (List Int)) :=
  match args with
  | [Value.array outer] =>
      (outer.mapM (fun v => match v with
        | Value.array col => valueInts col
        | _ => none))
  | _ => none

/-- Decode (matrix, int-kind) arguments. -/
private def matrixAndKind (args : List Value) : Option (List (List Int) × Int) :=
  match args with
  | [Value.array outer, Value.int k] =>
      match (outer.mapM (fun v => match v with
        | Value.array col => valueInts col
        | _ => none)) with
      | some m => some (m, k)
      | none => none
  | _ => none

/-! ## The interpretations -/

/-- Mathematical interpretations of the reverse and 2D lex
    predicates; wrong shapes yield `False`. -/
def lexChainInterp : LeanFzn.Semantics.PredicateInterpretation := fun x =>
  match x.name with
  | "fzn_lex_greater_int" => fun args =>
    match LexSort.twoIntArrays' args with
    | some (a, b) => LexSort.lexLess b a
    | none => False
  | "fzn_lex_greatereq_int" => fun args =>
    match LexSort.twoIntArrays' args with
    | some (a, b) => LexSort.lexLesseq b a
    | none => False
  | "fzn_lex_chain_less_int" => fun args =>
    match matrixArg args with
    | some cols => lexChainLess cols
    | none => False
  | "fzn_lex_chain_lesseq_int" => fun args =>
    match matrixArg args with
    | some cols => lexChainLesseq cols
    | none => False
  | "fzn_lex2" => fun args =>
    match matrixArg args with
    | some cols => lex2Prop cols
    | none => False
  | "fzn_strict_lex2" => fun args =>
    match matrixArg args with
    | some cols => strictLex2Prop cols
    | none => False
  | "fzn_lex_chain_lesseq_orbitope" => fun args =>
    match matrixAndKind args with
    | some (cols, kind) => orbitopeProp kind cols
    | none => False
  | "fzn_lex_chain_greater_int" => fun args =>
    match matrixArg args with
    | some cols => lexChainGreater cols
    | none => False
  | "fzn_lex_chain_greatereq_int" => fun args =>
    match matrixArg args with
    | some cols => lexChainGreatereq cols
    | none => False
  | "fzn_lex_chain_greatereq_orbitope" => fun args =>
    match matrixAndKind args with
    | some (cols, kind) => orbitopeGreatereqProp kind cols
    | none => False
  | _ => fun _ => False

/-- **Executable twin of `lexChainInterp`.** -/
def lexChainInterpB : LeanFzn.Ident → List Value → Bool := fun x =>
  match x.name with
  | "fzn_lex_greater_int" => fun args =>
    match LexSort.twoIntArrays' args with
    | some (a, b) => LexSort.lexLessB b a
    | none => false
  | "fzn_lex_greatereq_int" => fun args =>
    match LexSort.twoIntArrays' args with
    | some (a, b) => LexSort.lexLesseqB b a
    | none => false
  | "fzn_lex_chain_less_int" => fun args =>
    match matrixArg args with
    | some cols => lexChainLessB cols
    | none => false
  | "fzn_lex_chain_lesseq_int" => fun args =>
    match matrixArg args with
    | some cols => lexChainLesseqB cols
    | none => false
  | "fzn_lex2" => fun args =>
    match matrixArg args with
    | some cols => lex2B cols
    | none => false
  | "fzn_strict_lex2" => fun args =>
    match matrixArg args with
    | some cols => strictLex2B cols
    | none => false
  | "fzn_lex_chain_lesseq_orbitope" => fun args =>
    match matrixAndKind args with
    | some (cols, kind) => orbitopeB kind cols
    | none => false
  | "fzn_lex_chain_greater_int" => fun args =>
    match matrixArg args with
    | some cols => lexChainGreaterB cols
    | none => false
  | "fzn_lex_chain_greatereq_int" => fun args =>
    match matrixArg args with
    | some cols => lexChainGreatereqB cols
    | none => false
  | "fzn_lex_chain_greatereq_orbitope" => fun args =>
    match matrixAndKind args with
    | some (cols, kind) => orbitopeGreatereqB kind cols
    | none => false
  | _ => fun _ => false

/-! ## Per-name agreement theorems -/

theorem fzn_lex_greater_int_iff (args : List Value) :
    lexChainInterpB (Ident.mk "fzn_lex_greater_int") args = true ↔
      lexChainInterp (Ident.mk "fzn_lex_greater_int") args := by
  have hB : ∀ args, lexChainInterpB (Ident.mk "fzn_lex_greater_int") args
      = match LexSort.twoIntArrays' args with
      | some (a, b) => LexSort.lexLessB b a
      | none => false
      := fun _ => rfl
  have hI : ∀ args, lexChainInterp (Ident.mk "fzn_lex_greater_int") args
      = match LexSort.twoIntArrays' args with
      | some (a, b) => LexSort.lexLess b a
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : LexSort.twoIntArrays' args with
  | none => simp
  | some p =>
    obtain ⟨a, b⟩ := p
    simp only
    exact LexSort.lexLessB_iff b a

theorem fzn_lex_greatereq_int_iff (args : List Value) :
    lexChainInterpB (Ident.mk "fzn_lex_greatereq_int") args = true ↔
      lexChainInterp (Ident.mk "fzn_lex_greatereq_int") args := by
  have hB : ∀ args, lexChainInterpB (Ident.mk "fzn_lex_greatereq_int") args
      = match LexSort.twoIntArrays' args with
      | some (a, b) => LexSort.lexLesseqB b a
      | none => false
      := fun _ => rfl
  have hI : ∀ args, lexChainInterp (Ident.mk "fzn_lex_greatereq_int") args
      = match LexSort.twoIntArrays' args with
      | some (a, b) => LexSort.lexLesseq b a
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : LexSort.twoIntArrays' args with
  | none => simp
  | some p =>
    obtain ⟨a, b⟩ := p
    simp only
    exact LexSort.lexLesseqB_iff b a

theorem fzn_lex_chain_less_int_iff (args : List Value) :
    lexChainInterpB (Ident.mk "fzn_lex_chain_less_int") args = true ↔
      lexChainInterp (Ident.mk "fzn_lex_chain_less_int") args := by
  have hB : ∀ args, lexChainInterpB (Ident.mk "fzn_lex_chain_less_int") args
      = match matrixArg args with
      | some cols => lexChainLessB cols
      | none => false
      := fun _ => rfl
  have hI : ∀ args, lexChainInterp (Ident.mk "fzn_lex_chain_less_int") args
      = match matrixArg args with
      | some cols => lexChainLess cols
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : matrixArg args with
  | none => simp
  | some cols =>
    simp only
    exact lexChainLessB_iff cols

theorem fzn_lex_chain_lesseq_int_iff (args : List Value) :
    lexChainInterpB (Ident.mk "fzn_lex_chain_lesseq_int") args = true ↔
      lexChainInterp (Ident.mk "fzn_lex_chain_lesseq_int") args := by
  have hB : ∀ args, lexChainInterpB (Ident.mk "fzn_lex_chain_lesseq_int") args
      = match matrixArg args with
      | some cols => lexChainLesseqB cols
      | none => false
      := fun _ => rfl
  have hI : ∀ args, lexChainInterp (Ident.mk "fzn_lex_chain_lesseq_int") args
      = match matrixArg args with
      | some cols => lexChainLesseq cols
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : matrixArg args with
  | none => simp
  | some cols =>
    simp only
    exact lexChainLesseqB_iff cols

theorem fzn_lex2_iff (args : List Value) :
    lexChainInterpB (Ident.mk "fzn_lex2") args = true ↔
      lexChainInterp (Ident.mk "fzn_lex2") args := by
  have hB : ∀ args, lexChainInterpB (Ident.mk "fzn_lex2") args
      = match matrixArg args with
      | some cols => lex2B cols
      | none => false
      := fun _ => rfl
  have hI : ∀ args, lexChainInterp (Ident.mk "fzn_lex2") args
      = match matrixArg args with
      | some cols => lex2Prop cols
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : matrixArg args with
  | none => simp
  | some cols =>
    simp only
    exact lex2B_iff cols

theorem fzn_strict_lex2_iff (args : List Value) :
    lexChainInterpB (Ident.mk "fzn_strict_lex2") args = true ↔
      lexChainInterp (Ident.mk "fzn_strict_lex2") args := by
  have hB : ∀ args, lexChainInterpB (Ident.mk "fzn_strict_lex2") args
      = match matrixArg args with
      | some cols => strictLex2B cols
      | none => false
      := fun _ => rfl
  have hI : ∀ args, lexChainInterp (Ident.mk "fzn_strict_lex2") args
      = match matrixArg args with
      | some cols => strictLex2Prop cols
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : matrixArg args with
  | none => simp
  | some cols =>
    simp only
    exact strictLex2B_iff cols

theorem fzn_lex_chain_lesseq_orbitope_iff (args : List Value) :
    lexChainInterpB (Ident.mk "fzn_lex_chain_lesseq_orbitope") args = true ↔
      lexChainInterp (Ident.mk "fzn_lex_chain_lesseq_orbitope") args := by
  have hB : ∀ args, lexChainInterpB (Ident.mk "fzn_lex_chain_lesseq_orbitope") args
      = match matrixAndKind args with
      | some (cols, kind) => orbitopeB kind cols
      | none => false
      := fun _ => rfl
  have hI : ∀ args, lexChainInterp (Ident.mk "fzn_lex_chain_lesseq_orbitope") args
      = match matrixAndKind args with
      | some (cols, kind) => orbitopeProp kind cols
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : matrixAndKind args with
  | none => simp
  | some p =>
    obtain ⟨cols, kind⟩ := p
    simp only
    exact orbitopeB_iff kind cols

theorem fzn_lex_chain_greater_int_iff (args : List Value) :
    lexChainInterpB (Ident.mk "fzn_lex_chain_greater_int") args = true ↔
      lexChainInterp (Ident.mk "fzn_lex_chain_greater_int") args := by
  have hB : ∀ args, lexChainInterpB (Ident.mk "fzn_lex_chain_greater_int") args
      = match matrixArg args with
      | some cols => lexChainGreaterB cols
      | none => false
      := fun _ => rfl
  have hI : ∀ args, lexChainInterp (Ident.mk "fzn_lex_chain_greater_int") args
      = match matrixArg args with
      | some cols => lexChainGreater cols
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : matrixArg args with
  | none => simp
  | some cols =>
    simp only
    exact lexChainGreaterB_iff cols

theorem fzn_lex_chain_greatereq_int_iff (args : List Value) :
    lexChainInterpB (Ident.mk "fzn_lex_chain_greatereq_int") args = true ↔
      lexChainInterp (Ident.mk "fzn_lex_chain_greatereq_int") args := by
  have hB : ∀ args, lexChainInterpB (Ident.mk "fzn_lex_chain_greatereq_int") args
      = match matrixArg args with
      | some cols => lexChainGreatereqB cols
      | none => false
      := fun _ => rfl
  have hI : ∀ args, lexChainInterp (Ident.mk "fzn_lex_chain_greatereq_int") args
      = match matrixArg args with
      | some cols => lexChainGreatereq cols
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : matrixArg args with
  | none => simp
  | some cols =>
    simp only
    exact lexChainGreatereqB_iff cols

theorem fzn_lex_chain_greatereq_orbitope_iff (args : List Value) :
    lexChainInterpB (Ident.mk "fzn_lex_chain_greatereq_orbitope") args = true ↔
      lexChainInterp (Ident.mk "fzn_lex_chain_greatereq_orbitope") args := by
  have hB : ∀ args, lexChainInterpB (Ident.mk "fzn_lex_chain_greatereq_orbitope") args
      = match matrixAndKind args with
      | some (cols, kind) => orbitopeGreatereqB kind cols
      | none => false
      := fun _ => rfl
  have hI : ∀ args, lexChainInterp (Ident.mk "fzn_lex_chain_greatereq_orbitope") args
      = match matrixAndKind args with
      | some (cols, kind) => orbitopeGreatereqProp kind cols
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : matrixAndKind args with
  | none => simp
  | some p =>
    obtain ⟨cols, kind⟩ := p
    simp only
    exact orbitopeGreatereqB_iff kind cols

end LeanFzn.Semantics.Globals.LexChain

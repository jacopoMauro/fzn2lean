/-
Purpose: Executable solution checker definitions and required local lemmas.
Dependencies: Shared lexer/parser vocabulary, independent SolutionGrammar, and semantics.
DAG: Checker.Runtime.Solution -> Checker.Proofs.Solution -> compatibility import Checker.Solution.
-/
import LeanFzn.Parser.Parser
import LeanFzn.Checker.SolutionGrammar
import LeanFzn.Semantics.Evaluation
import LeanFzn.Semantics.ValueEquality
import Lean
import Std.Data.HashMap.Lemmas
open LeanFzn.Semantics LeanFzn.Parser LeanFzn.Semantics.Evaluation


/-!
# Solution checking

An *executable* checker that decides whether a FlatZinc solution string
(Section 4.3.3.1 of the MiniZinc 2.10.1 handbook: lines of the form
`x = <literal>;`, `xs = [ ... ];`, or the historical
`xs = array1d(1..n, [ ... ]);`) solves a given
FlatZinc model, together with a machine-checked proof of its correctness
(`checkSolutionFull_correct`, proved in `FznGlobals.lean` on the full
predicate scope): the checker returns `true` **if and only if**
the assignment described by the solution string satisfies every dynamic
condition of the `Satisfies` semantics of `FznSemantics.lean` — variable
domains, initializers, and all constraints under the standard predicate
interpretation `stdInterp`.

## Design

* The solution parser is total without fuel. Set enumerations recurse on
  token tails; array and assignment parsers use the strictly decreasing
  length of the unconsumed token suffix. Each literal parser consumes its
  following delimiter, including after multi-element sets.
* `SolutionGrammar.lean` independently specifies assignment syntax and values.
  `Proofs/SolutionParser.lean` proves success exactly for those derivations.
  The solution stream's status/separator lines are handled separately by
  `stripSeparators` and the CLI's stream splitter.
* The parameters (whose values are fixed by the model) are loaded into
  the initial store; a solution string never assigns them.
* Every dynamic condition is mirrored by a Boolean function with an
  `iff`-theorem against the corresponding semantic predicate, following
  the `wellFormedB_iff` pattern of `FznSemantics.lean`.  The constraint
  checker uses `interpB`, a total Boolean twin of `stdInterp` —
  including the extensional set predicates (`set_eq`, `set_subset`,
  `set_union`, `set_intersect`, `set_diff`, the set comparisons
  `set_ne`, `set_le`, `set_lt`, `set_superset`, `set_symdiff` with
  their reified variants, and the set-valued element family), decided
  by enumerating the finitely many elements of each `IntSetValue`
  (`interpB_set_iff`).
* Static well-formedness of the model is a *precondition* of the main
  theorem (hypothesis `WellFormed stdSig m`), not re-decided by the
  checker; `stdWellFormed` can decide it.
* The optimality component of `IsSolution` quantifies over all other
  stores and is therefore deliberately *not* part of the checker: it
  validates that a store is a satisfying assignment (the meaning of a
  solution printed by a solver), not that it is an optimal one.
-/

open LeanFzn.Semantics

open LeanFzn.Semantics.Evaluation

namespace LeanFzn.Checker.Solution

open LeanFzn.Parser.Lexer LeanFzn.Parser

/-! ## Parsing the solution string

The grammar of one solution line, for this fragment:

```
line      ::= ident "=" literal ";"
            | ident "=" "[" literals "]" ";"
            | ident "=" "array1d" "(" int ".." int "," "[" literals "]" ")" ";"
literal   ::= bool | int | set-literal
```

The FlatZinc `array1d(1..n, [...])` wrapper is accepted and checked to
be 1-based, matching the guarantee of MiniZinc >= 2.7.8 that output
arrays are one-dimensional and 1-based. Bare array output follows the current
handbook production. Arrays are flat; scalar elements may be Booleans,
integers, integer ranges, or enumerated integer sets. Commas are required
between elements, and trailing commas and unterminated suffixes are rejected.
The independent derivation rules live in `SolutionGrammar.lean`; parser
soundness and completeness are proved in `Proofs/SolutionParser.lean`. -/

/-- The semantic value of a solution value. -/
def SolValue.toValue : SolValue → Value
  | .scalar l => l.denote
  | .array ls => .array (ls.map (·.denote))

/-- Parse the context delimiter after a literal. -/
def parseSolTerminator : Token → Except String SolTerminator
  | .comma => .ok .comma
  | .rBrack => .ok .rBrack
  | .semi => .ok .semi
  | _ => .error "expected literal delimiter"

/-- Parse an integer enumeration, consuming the closing brace. -/
def parseSolSetTail : List Token → Except String (List Int × List Token)
  | .rBrace :: rest => .ok ([], rest)
  | .intLit i :: .rBrace :: rest => .ok ([i], rest)
  | .intLit i :: .comma :: .intLit j :: rest =>
      match parseSolSetTail (.intLit j :: rest) with
      | .ok (is, out) => .ok (i :: is, out)
      | .error e => .error e
  | _ => .error "expected integer or '}' in set literal"

/-- Parse one literal together with its following delimiter. Consuming the
same delimiter for every literal form prevents set/array comma confusion. -/
def parseSolLiteral : List Token →
    Except String (BasicLiteral × SolTerminator × List Token)
  | .boolLit b :: t :: rest => do
      let term ← parseSolTerminator t
      .ok (.bool b, term, rest)
  | .intLit lo :: .dotDot :: .intLit hi :: t :: rest => do
      let term ← parseSolTerminator t
      .ok (.set (.intRange lo hi), term, rest)
  | .intLit i :: t :: rest => do
      let term ← parseSolTerminator t
      .ok (.int i, term, rest)
  | .lBrace :: rest => do
      let (is, out) ← parseSolSetTail rest
      match out with
      | t :: tail => do
          let term ← parseSolTerminator t
          .ok (.set (.intSet is), term, tail)
      | [] => .error "expected delimiter after set literal"
  | _ => .error "expected literal"

theorem parseSolSetTail_suffix {toks is out}
    (h : parseSolSetTail toks = .ok (is, out)) : ∃ pre, toks = pre ++ out := by
  fun_induction parseSolSetTail toks generalizing is out with
  | case1 rest =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[.rBrace], rfl⟩
  | case2 i rest =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[.intLit i, .rBrace], rfl⟩
  | case3 i j rest js out hp ih =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨pre, hp⟩ := ih hp
      exact ⟨.intLit i :: .comma :: pre, by simp [hp]⟩
  | case4 => cases h
  | case5 => cases h

theorem parseSolLiteral_lt {toks l term out}
    (h : parseSolLiteral toks = .ok (l, term, out)) : out.length < toks.length := by
  unfold parseSolLiteral at h
  split at h
  all_goals
    try simp only [Bind.bind, Except.bind] at h
    repeat split at h
    all_goals try simp_all only [Except.ok.injEq, Prod.mk.injEq, List.length_cons]
  all_goals first | contradiction | omega | skip
  rename_i rest pair hp
  obtain ⟨is, remaining⟩ := pair
  cases remaining with
  | nil => simp at h
  | cons t tail =>
      simp only at h
      split at h
      · contradiction
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨pre, hpre⟩ := parseSolSetTail_suffix hp
        have := congrArg List.length hpre
        simp only [List.length_append, List.length_cons] at this ⊢
        omega


/-- Nonempty array contents; a comma always requires another literal. -/
def parseSolArrayItems (toks : List Token) : Except String (List BasicLiteral × List Token) :=
  match h : parseSolLiteral toks with
  | .ok (l, .rBrack, rest) => .ok ([l], rest)
  | .ok (l, .comma, rest) =>
      match parseSolArrayItems rest with
      | .ok (ls, out) => .ok (l :: ls, out)
      | .error e => .error e
  | .ok (_, .semi, _) => .error "expected ',' or ']' after array element"
  | .error e => .error e
termination_by toks.length
decreasing_by exact parseSolLiteral_lt h

/-- Possibly empty array contents, consuming `]`. -/
def parseSolArray : List Token → Except String (List BasicLiteral × List Token)
  | .rBrack :: rest => .ok ([], rest)
  | toks => parseSolArrayItems toks

theorem parseSolArrayItems_lt {toks ls out}
    (h : parseSolArrayItems toks = .ok (ls, out)) : out.length < toks.length := by
  fun_induction parseSolArrayItems toks generalizing ls out
  all_goals try contradiction
  case case1 toks l rest hp =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact parseSolLiteral_lt hp
  case case2 toks l rest hp ls' out' hparse ih =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Nat.lt_trans (ih hparse) (parseSolLiteral_lt hp)

theorem parseSolArray_lt {toks ls out}
    (h : parseSolArray toks = .ok (ls, out)) : out.length < toks.length := by
  unfold parseSolArray at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  · exact parseSolArrayItems_lt h

/-- One complete assignment with the unconsumed suffix returned. -/
def parseSolEntry : List Token → Except String (Entry × List Token)
  | .ident x :: .eq :: .lBrack :: rest => do
      let (ls, out) ← parseSolArray rest
      match out with
      | .semi :: tail => .ok (⟨x, .array ls⟩, tail)
      | _ => .error "expected ';' after array assignment"
  | .ident x :: .eq :: .ident "array1d" :: .lParen ::
      .intLit lo :: .dotDot :: .intLit hi :: .comma :: .lBrack :: rest => do
      if lo != 1 then .error "array1d index set must start at 1" else do
        let (ls, out) ← parseSolArray rest
        match out with
        | .rParen :: .semi :: tail =>
            if hi == (ls.length : Int) then .ok (⟨x, .array ls⟩, tail)
            else .error "array1d length mismatch"
        | _ => .error "expected ')' and ';' after array1d elements"
  | .ident x :: .eq :: rest => do
      let (l, term, out) ← parseSolLiteral rest
      match term with
      | .semi => .ok (⟨x, .scalar l⟩, out)
      | _ => .error "expected ';' after scalar assignment"
  | _ => .error "expected solution line 'name = value;'"

theorem parseSolEntry_lt {toks e out}
    (h : parseSolEntry toks = .ok (e, out)) : out.length < toks.length := by
  unfold parseSolEntry at h
  split at h
  all_goals
    try simp only [Bind.bind, Except.bind] at h
    repeat' split at h
    all_goals try simp_all only [Except.ok.injEq, Prod.mk.injEq, List.length_cons]
  all_goals first | contradiction | omega | skip
  all_goals
    first
    | (rename_i hpArray _ _ hrest
       have hb := parseSolArray_lt hpArray
       simp_all only [List.length_cons]
       omega)
    | (rename_i hpArray _ _ hrest _
       have hb := parseSolArray_lt hpArray
       simp_all only [List.length_cons]
       omega)
    | (rename_i hpLiteral _ hterm
       have hb := parseSolLiteral_lt hpLiteral
       simp_all only [List.length_cons]
       omega)

/-- Parse a complete sequence of assignments; no token suffix is discarded. -/
def parseSolutionTokens : List Token → Except String (List Entry)
  | [] => .ok []
  | toks =>
      match h : parseSolEntry toks with
      | .ok (e, rest) =>
          match parseSolutionTokens rest with
          | .ok es => .ok (e :: es)
          | .error err => .error err
      | .error err => .error err
termination_by toks => toks.length
decreasing_by exact parseSolEntry_lt h

/-- Parse whitespace/comment-separated solution assignments, accepting both
handbook bare arrays and historical one-based `array1d` output. -/
def parseSolution (src : String) : Except String (List Entry) := do
  let toks ← tokenize src
  parseSolutionTokens toks.toList

/-! ## Building the store

The store of a candidate solution consists of the model's parameters
(fixed by the model text) extended by the solution string's entries.

Both layers are kept in a `Std.HashMap` keyed by identifier name, so
lookup is O(1) on average instead of a linear walk over nested
closures — the checker evaluates every argument occurrence of every
constraint against the store, and models produced by the MiniZinc
compiler have thousands of variables.  The completion layer below
works on the same map. -/

/-- The parameter map of a model: each parameter name bound to the
    value its declaration fixes. -/
def paramMap (m : Model) : Std.HashMap String Value :=
  m.parameters.foldl (fun acc d => acc.insert d.name.name d.value) {}

/-- The solution entries inserted over the parameter map. -/
def entryMap (m : Model) (es : List Entry) : Std.HashMap String Value :=
  es.foldl (fun acc e => acc.insert e.name e.value.toValue) (paramMap m)

/-! ### Compilation safeguard for the store constructors

`Store` is a function type, so Lean's compiler (arity-raising in the
lambda-lifting pass) fuses a `let store := <map construction>`
binding with consumer loops and re-runs the *whole map construction
once per lookup* — an O(n²) blow-up of the checker on
compiler-produced models.  `@[never_extract]` does not block it, and
neither does an `@[implemented_by]` twin on its own: the lifter
expands *through* the twin.

What does block it: returning the store **inside a constructor
allocation across an `implemented_by` boundary**.  A single-field
structure allocated by the runtime twin cannot be arity-raised or
erased at the consumer, because the consumer never sees the
construction — it calls the twin and receives a value whose field is
applied with the generic `lean_apply_1`.  This was verified against
the generated C before adopting it here.

The logical constants below are ordinary definitions, and each
`implemented_by` twin has *the same body* (`mapStoreI_eq`,
`completedBoxI_eq` hold by `rfl`).  The twins only change what the
compiler sees, so the kernel can unfold `completedStore`, and the
theorems at the end of this section (`completedStore_entry`,
`completedStore_paramHonest`) tie the store to the solution entries
and the model's parameters. -/

/-- A store wrapped in a constructor allocation (see the
    compilation-safeguard note above). -/
structure StoreBox where
  f : Store
  deriving Nonempty, Inhabited

/-- Runtime twin of `mapStore` (same body). -/
private def mapStoreI (pms : Std.HashMap String Value) : Store :=
  fun x => pms[x.name]?

/-- View a hash map keyed by names as a store. -/
@[implemented_by mapStoreI]
def mapStore (pms : Std.HashMap String Value) : Store :=
  fun x => pms[x.name]?

private theorem mapStoreI_eq : mapStoreI = mapStore := rfl

/-! ## Initializer completion

A LeanFzn.Solver's solution string assigns only the *output* variables
(`:: output_var` / `:: output_array`); compiler-introduced variables
are omitted.  A variable omitted from the string but pinned by its
declaration's initializer (`array [1..3] of var 1..9: a = [x, y, z];`)
has its value determined by the model.  The checker therefore closes
the candidate store under the initializers: any variable absent from
the store whose initializer evaluates in the current store is added
with that value.  Values are only ever *added* (an explicit solution
entry is never overridden; `completeFix_getElem?_of_some`).

The completion works on a hash map (O(1) average lookups) and stops
at the fixed point rather than running a fixed number of passes. -/

/-- The value a variable declaration's initializer denotes in a
    store; `none` without initializer or when not evaluable. -/
def initValue (store : Store) : VarDeclItem → Option Value
  | .basic _ _ _ (some v) => v.eval store
  | .array _ _ _ es =>
      (es.mapM (fun e => BasicExpr.eval store e)).map Value.array
  | _ => none

/-- One completion pass over a map of known values: add
    initializer-derived values for the variables that are absent and
    derivable. -/
def completePass (vars : List VarDeclItem)
    (known : Std.HashMap String Value) : Std.HashMap String Value :=
  vars.foldl (fun acc d =>
    if acc.contains d.name.name then acc
    else
      match initValue (fun x => acc[x.name]?) d with
      | some v => acc.insert d.name.name v
      | none => acc) known

/-- Iterate the completion passes until the fixed point (a pass that
    adds nothing) or the bound (the number of variables) is reached.
    Each pass either adds at least one entry or leaves the map
    unchanged, so the number of variables bounds the iterations. -/
def completeFix (vars : List VarDeclItem) : Nat →
    Std.HashMap String Value → Std.HashMap String Value
  | 0, known => known
  | n + 1, known =>
      let known' := completePass vars known
      if known'.size == known.size then known'  -- fixed point reached
      else completeFix vars n known'

/-- The candidate map closed under variable initializers. -/
def completedMap (m : Model) (es : List Entry) : Std.HashMap String Value :=
  completeFix m.variables m.variables.length (entryMap m es)

/-- Runtime twin of `completedBox` (same body; see the
    compilation-safeguard note above). -/
private def completedBoxI (m : Model) (es : List Entry) : StoreBox :=
  ⟨mapStore (completedMap m es)⟩

/-- The completed store in a constructor allocation. -/
@[implemented_by completedBoxI]
def completedBox (m : Model) (es : List Entry) : StoreBox :=
  ⟨mapStore (completedMap m es)⟩

private theorem completedBoxI_eq : completedBoxI = completedBox := rfl

/-- The completed store: the model's parameters, overridden by the
    solution entries, closed under variable initializers.  A solution
    string assigning only the output variables still yields a total
    store whenever the omitted variables are pinned by their
    initializers. -/
def completedStore (m : Model) (es : List Entry) : Store :=
  (completedBox m es).f

/-! ### What the completed store contains -/

/-! ## The executable checker -/

/-- Evaluate a constraint's arguments and check the predicate
    (executable twin of `ConstraintItem.Holds stdInterp`). -/
def constraintHoldsB (store : Store) (c : ConstraintItem) : Bool :=
  match c.args.mapM (Expr.eval store) with
  | some args => interpB c.name args
  | none => false

/-! ## The top-level checker

`checkSolution m sol` parses the solution string, builds the candidate
store, and checks every dynamic condition of `Satisfies` — variable
domains, initializers, and constraints — with executable Boolean
twins.  `checkSolutionFull_correct` (in `FznGlobals.lean`) proves the
result correct **iff** against `Satisfies` for models whose
constraints all use checkable predicates and whose variables are all
assigned by the solution.  The full-scope fast twin
`checkSolutionFullFast` (in `FznGlobals.lean`) and the per-condition
Boolean twins below carry per-name `iff`-theorems. -/

/-- Domains: does the value lie in the variable's declared domain? -/
def varTypeContainsB (ty : BasicVarType) (v : Value) : Bool :=
  match ty, v with
  | .par .bool, .bool _ => true
  | .par .int, .int _ => true
  | .par .setOfInt, .setOfInt _ => true
  | .intRange lo hi, .int x => decide (lo ≤ x ∧ x ≤ hi)
  | .intSet xs, .int x => decide (x ∈ xs)
  | .setOfIntRange lo hi, .setOfInt s => setSubB s (.interval lo hi)
  | .setOfIntSet allowed, .setOfInt s => setSubB s (.enumeration allowed)
  | _, _ => false

/-- Executable `Value.SemEq`: sets are compared extensionally. -/
def semEqB : Value → Value → Bool
  | .bool a, .bool b => a == b
  | .int a, .int b => a == b
  | .setOfInt a, .setOfInt b => setEqB a b
  | _, _ => false

/-- Executable `Forall2 Value.SemEq`. -/
def semEqListB : List Value → List Value → Bool
  | [], [] => true
  | a :: as, b :: bs => semEqB a b && semEqListB as bs
  | _, _ => false

/-- Initializers: the declared variable equals its initializer's value
    (semantically: set values are compared by their elements). -/
def initializerHoldsB (store : Store) : VarDeclItem → Bool
  | .basic _ _ _ none => true
  | .basic _ n _ (some v) =>
      match v.eval store, store n with
      | some val, some val' => semEqB val val'
      | _, _ => false
  | .array _ n _ es =>
      match (es.mapM (fun e => e.eval store)), store n with
      | some vs, some (.array ws) => semEqListB vs ws
      | _, _ => false

/-- Check all variable declarations (domains and initializers). -/
def varDeclsOkB (store : Store) (vars : List VarDeclItem) : Bool :=
  vars.all (fun d =>
    match d with
    | .basic ty n _ _ =>
        match store n with
        | some v => varTypeContainsB ty v &&
            initializerHoldsB store d
        | none => false
    | .array ty n _ _ =>
        match store n with
        | some (.array vs) =>
            decide (vs.length = ty.idx.length) &&
            vs.all (fun v => varTypeContainsB ty.elem v) &&
            initializerHoldsB store d
        | _ => false)

/-- Check that all declared variables are assigned (present in the store). -/
def allAssignedB (store : Store) (vars : List VarDeclItem) : Bool :=
  vars.all (fun d => (store d.name).isSome)

/-- Strip the standard FlatZinc solution separators (`----------` and
    `==========` lines) from a solution string.  Statistics lines
    (`%%%mzn-stat`) are FlatZinc comments, which the lexer skips. -/
def stripSeparators (sol : String) : String :=
  String.intercalate "\n" (((sol.split '\n').toList.map String.Slice.copy).filter (fun l =>
    !(l.startsWith "----------" || l.startsWith "==========")))

/-- The top-level solution checker. -/
def checkSolution (m : Model) (sol : String) : Bool :=
  match parseSolution (stripSeparators sol) with
  | .error _ => false
  | .ok es =>
      let box := completedBox m es
      allAssignedB box.f m.variables &&
      varDeclsOkB box.f m.variables &&
      m.constraints.all (fun c => constraintHoldsB box.f c)

end LeanFzn.Checker.Solution

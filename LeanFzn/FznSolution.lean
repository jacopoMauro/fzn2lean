import LeanFzn.FznParser
import LeanFzn.FznStdLib
import Lean

/-!
# Solution checking

An *executable* checker that decides whether a FlatZinc solution string
(Section 4.3.3.1 of the MiniZinc 2.10.0 handbook: lines of the form
`x = <literal>;` or `xs = array1d(1..n, [ ... ]);`) solves a given
FlatZinc model, together with a machine-checked proof of its correctness
(`checkSolutionFull_correct`, proved in `FznGlobals.lean` on the full
predicate scope): the checker returns `true` **if and only if**
the assignment described by the solution string satisfies every dynamic
condition of the `Satisfies` semantics of `FznSemantics.lean` — variable
domains, initializers, and all constraints under the standard predicate
interpretation `stdInterp`.

## Design

* The solution parser recurses structurally on the token list, so its
  termination is syntactic (no fuel needed): a solution line contains no
  nested arrays, only literals.
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

namespace LeanFzn.Solution

open LeanFzn.Lexer LeanFzn.Parser

/-! ## Parsing the solution string

The grammar of one solution line, for this fragment:

```
line      ::= ident "=" literal ";"
            | ident "=" "array1d" "(" int ".." int "," "[" literals "]" ")" ";"
literal   ::= bool | int | set-literal
```

The FlatZinc `array1d(1..n, [...])` wrapper is accepted and checked to
be 1-based, matching the guarantee of MiniZinc >= 2.7.8 that output
arrays are one-dimensional and 1-based.  All parsers below are
structural in the token list: every recursive call is on a `.tail` of
the matched constructor pattern, so termination is syntactic. -/

/-- A scalar or array solution value. -/
inductive SolValue where
  | scalar (l : BasicLiteral)
  | array (elems : List BasicLiteral)
  deriving Repr, Inhabited

/-- One solution line: variable name and its scalar-or-array value. -/
structure Entry where
  name : String
  value : SolValue
  deriving Repr, Inhabited

/-- The semantic value of a solution value. -/
def SolValue.toValue : SolValue → Value
  | .scalar l => l.denote
  | .array ls => .array (ls.map (·.denote))

/-- The continuation of a set literal after `{`: more comma-separated
    atoms until `}`, which is consumed.  The result list is built by
    append, keeping the recursion structural on the token list. -/
private def parseSetTail : List Token → Except String (List Int × List Token)
  | .intLit i :: .comma :: rest =>
      match parseSetTail rest with
      | .ok (is, rest') => .ok (i :: is, rest')
      | .error e => .error e
  | .intLit i :: .rBrace :: rest => .ok ([i], rest)
  | .rBrace :: rest => .ok ([], rest)
  | _ => .error "expected integer or '}' in set literal"

/-- `parseSetTail` returns a suffix of its input: it only consumes
    tokens from the front. -/
private theorem parseSetTail_suffix : ∀ (n : Nat) (toks : List Token),
    toks.length ≤ n → ∀ (out : List Token) (is : List Int),
    parseSetTail toks = .ok (is, out) → ∃ pre, toks = pre ++ out := by
  intro n
  induction n with
  | zero =>
      intro toks hle out is h
      cases toks with
      | nil => cases h
      | cons t ts => simp only [List.length_cons] at hle; omega
  | succ n ih =>
      intro toks hle out is h
      cases toks with
      | nil => cases h
      | cons t ts =>
        cases ts with
        | nil =>
            cases t with
            | rBrace =>
                simp only [parseSetTail, Except.ok.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact ⟨[.rBrace], rfl⟩
            | _ => simp [parseSetTail] at h
        | cons t2 ts2 =>
          cases t with
          | intLit i =>
              cases t2 with
              | comma =>
                  simp only [parseSetTail] at h
                  cases hp : parseSetTail ts2 with
                  | error e => rw [hp] at h; simp at h
                  | ok p2 =>
                      obtain ⟨is2, out2⟩ := p2
                      rw [hp] at h
                      simp only [Except.ok.injEq, Prod.mk.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      have hle2 : ts2.length ≤ n := by
                        simp only [List.length_cons] at hle; omega
                      obtain ⟨pre, hpre⟩ := ih ts2 hle2 out2 is2 hp
                      exact ⟨.intLit i :: .comma :: pre, by simp [hpre]⟩
              | rBrace =>
                  simp only [parseSetTail, Except.ok.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  exact ⟨[.intLit i, .rBrace], rfl⟩
              | _ => simp [parseSetTail] at h
          | rBrace =>
              simp only [parseSetTail, Except.ok.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨[.rBrace], rfl⟩
          | _ => simp [parseSetTail] at h

/-- A comma-separated list of basic literals up to (but not consuming)
    the closing `]`.  Every recursive call is on the tail of the matched
    pattern: set literals are spelt out case by case (empty, one
    element, several), so no separate set-atom helper is needed. -/
private def parseLiteralList : List Token →
    Except String (List BasicLiteral × List Token)
  | .rBrack :: toks => .ok ([], .rBrack :: toks)
  | .boolLit b :: .comma :: rest =>
      match parseLiteralList rest with
      | .ok (ls, rest') => .ok (.bool b :: ls, rest')
      | .error e => .error e
  | .boolLit b :: .rBrack :: rest => .ok ([.bool b], .rBrack :: rest)
  | .intLit i :: .dotDot :: .intLit hi :: .comma :: rest =>
      match parseLiteralList rest with
      | .ok (ls, rest') => .ok (.set (.intRange i hi) :: ls, rest')
      | .error e => .error e
  | .intLit i :: .dotDot :: .intLit hi :: .rBrack :: rest =>
      .ok ([.set (.intRange i hi)], .rBrack :: rest)
  | .intLit i :: .comma :: rest =>
      match parseLiteralList rest with
      | .ok (ls, rest') => .ok (.int i :: ls, rest')
      | .error e => .error e
  | .intLit i :: .rBrack :: rest => .ok ([.int i], .rBrack :: rest)
  | .lBrace :: .rBrace :: .comma :: rest =>
      match parseLiteralList rest with
      | .ok (ls, rest') => .ok (.set (.intSet []) :: ls, rest')
      | .error e => .error e
  | .lBrace :: .rBrace :: .rBrack :: rest =>
      .ok ([.set (.intSet [])], .rBrack :: rest)
  | .lBrace :: .intLit i :: .rBrace :: .comma :: rest =>
      match parseLiteralList rest with
      | .ok (ls, rest') => .ok (.set (.intSet [i]) :: ls, rest')
      | .error e => .error e
  | .lBrace :: .intLit i :: .rBrace :: .rBrack :: rest =>
      .ok ([.set (.intSet [i])], .rBrack :: rest)
  | .lBrace :: .intLit i :: .comma :: rest =>
      match _hset : parseSetTail (.intLit i :: .comma :: rest) with
      | .ok (is, out) =>
          match _hlist : parseLiteralList out with
          | .ok (ls, rest3) => .ok (.set (.intSet is) :: ls, rest3)
          | .error e => .error e
      | .error e => .error e
  | _ => .error "expected literal"
termination_by toks => toks.length
decreasing_by
  all_goals
    simp only [List.length_cons]
  all_goals
    first
    | omega
    | (obtain ⟨pre, hpre⟩ := parseSetTail_suffix ((.intLit i :: .comma :: rest).length)
         (.intLit i :: .comma :: rest) (Nat.le_refl _) out is _hset
       have hlen : (.intLit i :: .comma :: rest).length = pre.length + out.length := by
         rw [hpre]; simp [List.length_append]
       simp only [List.length_cons] at hlen
       cases pre with
       | nil =>
           rw [List.nil_append] at hpre
           rw [← hpre]
           simp only [List.length_cons]
           omega
       | cons p ps =>
           simp only [List.length_cons] at hlen
           omega)

/-- Parse `array1d ( <int> ".." <int> , [ <literals> ] )`, checking the
    index set is 1-based and matches the element count. -/
private def parseArray1d : List Token →
    Except String (List BasicLiteral × List Token)
  | .ident "array1d" :: .lParen :: .intLit lo :: .dotDot :: .intLit hi ::
    .comma :: .lBrack :: rest =>
      if lo != 1 then
        .error "array1d index set must start at 1"
      else
        match parseLiteralList rest with
        | .ok (elems, .rBrack :: .rParen :: rest') =>
            if hi - lo + 1 == elems.length then
              .ok (elems, rest')
            else
              .error "array1d length mismatch"
        | .ok _ => .error "expected ']' after array1d elements"
        | .error e => .error e
  | _ => .error "expected array1d"

/-- Parse a single literal after `=`: a bool, int, range set, or
    enumerated set, followed by `;`. -/
private def parseScalarEntry (x : String) : List Token →
    Except String (Entry × List Token)
  | .boolLit b :: .semi :: rest => .ok (⟨x, .scalar (.bool b)⟩, rest)
  | .intLit i :: .dotDot :: .intLit hi :: .semi :: rest =>
      .ok (⟨x, .scalar (.set (.intRange i hi))⟩, rest)
  | .intLit i :: .semi :: rest => .ok (⟨x, .scalar (.int i)⟩, rest)
  | .lBrace :: rest =>
      match parseSetTail rest with
      | .ok (is, .semi :: rest') => .ok (⟨x, .scalar (.set (.intSet is))⟩, rest')
      | .ok _ => .error s!"expected ';' after assignment to '{x}'"
      | .error e => .error e
  | _ => .error s!"expected literal or ';' after assignment to '{x}'"

/-- Parse a single solution line `<ident> "=" <value> ";"`. -/
private def parseEntry : List Token → Except String (Entry × List Token)
  | .ident x :: .eq :: .ident "array1d" :: rest =>
      match parseArray1d (.ident "array1d" :: rest) with
      | .ok (elems, .semi :: rest') => .ok (⟨x, .array elems⟩, rest')
      | .ok _ => .error s!"expected ';' after assignment to '{x}'"
      | .error e => .error e
  | .ident x :: .eq :: rest => parseScalarEntry x rest
  | _ => .error "expected solution line 'name = value;'"

/-- The shortest prefix ending in `;` (kept as the last token), and the
    rest. -/
private def splitAtSemi : List Token → Option (List Token × List Token)
  | .semi :: rest => some ([.semi], rest)
  | t :: rest =>
      match splitAtSemi rest with
      | some (line, rest') => some (t :: line, rest')
      | none => none
  | [] => none

/-- A successful `splitAtSemi` strictly shortens the input: the
    returned rest is shorter than the input. -/
private theorem splitAtSemi_lt (toks : List Token) :
    ∀ (p : List Token × List Token), splitAtSemi toks = some p →
      p.2.length < toks.length := by
  induction toks with
  | nil => intro p h; cases h
  | cons t ts ih =>
    intro p h
    match hh : splitAtSemi (t :: ts) with
    | none => rw [hh] at h; cases h
    | some p2 =>
        rw [hh] at h
        simp only [Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        match t, ts with
        | .semi, rest =>
            -- hh : splitAtSemi (semi :: rest) = some p, and by def = some ([semi], rest)
            rw [show splitAtSemi (.semi :: rest) = some ([.semi], rest) from rfl] at hh
            simp only [Option.some.injEq] at hh
            obtain ⟨rfl, rfl⟩ := hh
            simp [List.length_cons]
        | t', t2 :: ts2 =>
            cases t' with
            | semi =>
                -- splitAtSemi (semi :: t2 :: ts2) = some ([semi], t2 :: ts2) = some p
                rw [show splitAtSemi (.semi :: t2 :: ts2) = some ([.semi], t2 :: ts2) from rfl] at hh
                simp only [Option.some.injEq] at hh
                obtain ⟨rfl, rfl⟩ := hh
                simp [List.length_cons]
            | _ =>
              simp only [splitAtSemi] at hh
              cases hp : splitAtSemi (t2 :: ts2) with
              | none =>
                  rw [hp] at hh
                  simp at hh
              | some q =>
                  rw [hp] at hh
                  simp only [Option.some.injEq] at hh
                  obtain ⟨rfl, rfl⟩ := hh
                  have := ih q hp
                  simp only [List.length_cons] at *
                  omega
        | t0, [] =>
            revert hh
            cases t0 with
            | semi =>
                intro hh
                rw [show splitAtSemi [.semi] = some ([.semi], []) from rfl] at hh
                simp only [Option.some.injEq] at hh
                obtain ⟨rfl, rfl⟩ := hh
                decide
            | _ =>
                intro hh
                simp only [splitAtSemi] at hh
                cases hh

/-- Split a token list into `;`-terminated chunks (the trailing `;` of each
    chunk is kept as its last token). -/
private def splitLines : List Token → List (List Token) → List (List Token)
  | [], acc => acc.reverse
  | toks, acc =>
      match _hh : splitAtSemi toks with
      | some p => splitLines p.2 (p.1 :: acc)
      | none => acc.reverse
termination_by toks => toks.length
decreasing_by
  all_goals
    first
    | simp +arith
    | (have := splitAtSemi_lt toks _ _hh
       omega)

/-- Parse all solution lines from a token list: split into `;`-chunks
    and parse each independently; every chunk must parse and consume
    exactly its tokens (structural recursion on the chunk list). -/
private def parseEntries : List (List Token) → Except String (List Entry)
  | [] => .ok []
  | line :: lines =>
      match parseEntry line with
      | .ok (e, rest) =>
          if rest == [] then
            match parseEntries lines with
            | .ok es => .ok (e :: es)
            | .error err => .error err
          else
            .error "trailing tokens in solution line"
      | .error e => .error e

/-- Parse a whole solution string: `x = v;` lines, with FlatZinc
    comments and whitespace allowed anywhere (the model lexer is
    reused).  Fails if the string is not a sequence of solution lines.
    A string that tokenizes to nothing but whitespace and comments
    parses as the empty entry list (all output variables omitted);
    a string with tokens but no `;`-terminated line is rejected
    (it cannot be a suffix of a well-formed solution). -/
def parseSolution (src : String) : Except String (List Entry) := do
  let toks ← tokenize src
  if toks.toList.isEmpty then
    .ok []
  else
    match splitLines toks.toList [] with
    | [] => .error "no solution assignment found"
    | lines => parseEntries lines

/-! ## Building the store

The store of a candidate solution consists of the model's parameters
(fixed by the model text) extended by the solution string's entries.

Both layers are kept in a `Std.HashMap` keyed by identifier name, so
lookup is O(1) on average instead of a linear walk over nested
closures — the checker evaluates every argument occurrence of every
constraint against the store, and models produced by the MiniZinc
compiler have thousands of variables.  The completion layer below
works on the same map. -/

/-- The value of a parameter declaration. -/
private def parValue : ParDeclItem → Value
  | .basic _ _ v => v.denote
  | .array _ _ _ vs => .array (vs.map (·.denote))

/-- The parameter map of a model. -/
private def paramMap (m : Model) : Std.HashMap String Value :=
  m.parameters.foldl (fun acc d => acc.insert (d.name).name (parValue d)) {}

/-! ### Compilation safeguard for the store constructors

`Store` is a function type, so Lean's compiler (arity-raising in the
lambda-lifting pass) fuses a `let store := <map construction>`
binding with consumer loops and re-runs the *whole map construction
once per lookup* — an O(n²) blow-up of the checker on
compiler-produced models.  Neither `opaque`+`@[implemented_by]` on
the store constants nor `@[never_extract]` blocks it: the lifter
expands *through* the `implemented_by` twin.

What does block it: returning the store **inside a constructor
allocation across an `implemented_by` boundary**.  A single-field
structure allocated by the (unsafe) runtime twin cannot be arity-raised
or erased at the consumer, because the consumer never sees the
construction — it calls an opaque constant and receives a value whose
field is applied with the generic `lean_apply_1`.  This was verified
against the generated C before adopting it here.

Everything is definitionally transparent to the kernel:
`StoreBox.mk s |>.f = s` holds by `rfl`, so every proof about the
checkers is unaffected; no proof in this development unfolds
`completedStore`, `candidateStore`, or `storeBox` (the master theorem
`checkSolutionFull_correct` unfolds `checkSolutionFull`, whose body
mentions only `storeBox … |>.f`, definitionally the store). -/

/-- A store wrapped in a constructor allocation (see the
    compilation-safeguard note above). -/
structure StoreBox where
  f : Store
  deriving Nonempty, Inhabited

/-- Runtime twin of `mapStore` (the body the plain `def` had). -/
private def mapStoreI (pms : Std.HashMap String Value) : Store :=
  fun x => pms[x.name]?

/-- Wrap a hash map as a store closure (logical, opaque view;
    `implemented_by` its runtime twin above). -/
@[implemented_by mapStoreI]
opaque mapStore : Std.HashMap String Value → Store

/-- Runtime twin of `candidateStore` (the body the plain `def`
    had). -/
private def candidateStoreI (m : Model) (es : List Entry) : Store :=
  mapStore (es.foldl (fun acc e => acc.insert e.name e.value.toValue)
    (paramMap m))

/-- The candidate store: parameters plus solution entries (entries
    override parameters of the same name — a solution assigning a
    parameter name is rejected later by the domain checks, since a
    parameter's model value is what counts). -/
@[implemented_by candidateStoreI]
opaque candidateStore : Model → List Entry → Store

/-- The parameter store of a model (hash-map backed). -/
def paramStore (m : Model) : Store :=
  mapStore (paramMap m)

/-! ## Initializer completion

A solver's solution string assigns only the *output* variables
(`:: output_var` / `:: output_array`); compiler-introduced variables
are omitted.  A variable omitted from the string but pinned by its
declaration's initializer (`array [1..3] of var 1..9: a = [x, y, z];`)
has its value determined by the model.  The checker therefore closes
the candidate store under the initializers: any variable absent from
the store whose initializer evaluates in the current store is added
with that value.  Values are only ever *added* (an explicit solution
entry is never overridden).

The completion works on a hash map (O(1) average lookups) and stops
at the fixed point rather than running a fixed number of passes. -/

/-- The value a variable declaration's initializer denotes in a
    store; `none` without initializer or when not evaluable. -/
private def initValue (store : Store) : VarDeclItem → Option Value
  | .basic _ _ _ (some v) => v.eval store
  | .array _ _ _ es =>
      (es.mapM (fun e => BasicExpr.eval store e)).map Value.array
  | _ => none

/-- One completion pass over a map of known values: add
    initializer-derived values for the variables that are absent and
    derivable. -/
private def completePass (vars : List VarDeclItem)
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
private def completeFix (vars : List VarDeclItem) : Nat →
    Std.HashMap String Value → Std.HashMap String Value
  | 0, known => known
  | n + 1, known =>
      let known' := completePass vars known
      if known'.size == known.size then known'  -- fixed point reached
      else completeFix vars n known'

/-- Runtime twin of `completedBox` (the body the plain `def` had;
    see the compilation-safeguard note above). -/
private def completedBoxI (m : Model) (es : List Entry) : StoreBox :=
  ⟨mapStore (completeFix m.variables m.variables.length
    (es.foldl (fun acc e => acc.insert e.name e.value.toValue)
      (paramMap m)))⟩

/-- The completed store in a constructor allocation (logical, opaque
    view; `implemented_by` its runtime twin above). -/
@[implemented_by completedBoxI]
opaque completedBox : Model → List Entry → StoreBox

/-- The completed store: the candidate store closed under variable
    initializers.  A solution string assigning only the output
    variables still yields a total store whenever the omitted
    variables are pinned by their initializers. -/
def completedStore (m : Model) (es : List Entry) : Store :=
  (completedBox m es).f

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

/-- Extensional set equality, decided. -/
private def setEqB (a b : IntSetValue) : Bool :=
  (setElems a).all (fun x => decide (b.Contains x)) &&
  (setElems b).all (fun x => decide (a.Contains x))

/-- Extensional set inclusion, decided. -/
private def setSubB (a b : IntSetValue) : Bool :=
  (setElems a).all (fun x => decide (b.Contains x))

/-- `setSubB` decides extensional inclusion. -/
private theorem setSubB_iff {a b : IntSetValue} :
    setSubB a b = true ↔ ∀ i, a.Contains i → b.Contains i := by
  constructor
  · intro h i hmem
    have hi : i ∈ setElems a := setElems_mem_iff.mp hmem
    have hall := List.all_eq_true.mp h
    have hxall := hall i hi
    have := of_decide_eq_true hxall
    exact this
  · intro h
    refine List.all_eq_true.mpr ?_
    intro x hx
    exact decide_eq_true (h x (setElems_mem_iff.mpr hx))

/-- `setEqB` decides extensional equality. -/
private theorem setEqB_iff {a b : IntSetValue} :
    setEqB a b = true ↔ ∀ i, a.Contains i ↔ b.Contains i := by
  unfold setEqB
  rw [Bool.and_eq_true]
  have h1 : ((setElems a).all fun x => decide (b.Contains x)) = true ↔
      ∀ i, a.Contains i → b.Contains i := setSubB_iff
  have h2 : ((setElems b).all fun x => decide (a.Contains x)) = true ↔
      ∀ i, b.Contains i → a.Contains i := setSubB_iff
  rw [h1, h2]
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

/-! ## The executable checker -/

/-- Evaluate a constraint's arguments and check the predicate
    (executable twin of `ConstraintItem.Holds stdInterp`). -/
def constraintHoldsB (store : Store) (c : ConstraintItem) : Bool :=
  match c.args.mapM (Expr.eval store) with
  | some args => interpB c.name args
  | none => false

/-- `constraintHoldsB` decides `Holds stdInterp` for standard
    predicates. -/
private theorem constraintHoldsB_iff {store : Store} {c : ConstraintItem}
    (hname : c.name.name ∈ stdNames ∨ c.name.name ∈ setNames) :
    constraintHoldsB store c = true ↔ c.Holds stdInterp store := by
  unfold constraintHoldsB ConstraintItem.Holds
  cases hargs : c.args.mapM (Expr.eval store) with
  | none =>
      constructor
      · intro hfalse
        exact absurd hfalse (by intro hc; cases hc)
      · rintro ⟨args, hnone, _⟩
        cases hnone
  | some args =>
      constructor
      · intro h
        refine ⟨args, rfl, ?_⟩
        have hred : interpB c.name args = true := h
        rcases hname with h | h
        · cases hc : c.name with
          | mk n' =>
              rw [hc] at hred h
              exact (interpB_std_iff (n := n') (show n' ∈ stdNames from h)).mp hred
        · exact (interpB_set_iff h).mp hred
      · rintro ⟨args', hargs', hinterp⟩
        have hargs_eq : args = args' := Option.some.inj hargs'
        subst hargs_eq
        -- goal: (match some args with | some args => interpB c.name args) = true
        show interpB c.name args = true
        rcases hname with h | h
        · cases hc : c.name with
          | mk n' =>
              rw [hc] at hinterp h
              exact (interpB_std_iff (n := n') (show n' ∈ stdNames from h)).mpr hinterp
        · exact (interpB_set_iff h).mpr hinterp

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
  | .setOfIntRange lo hi, .setOfInt s =>
      (setElems s).all (fun x => decide (lo ≤ x ∧ x ≤ hi))
  | .setOfIntSet allowed, .setOfInt s =>
      (setElems s).all (fun x => decide (x ∈ allowed))
  | _, _ => false

/-- `varTypeContainsB` decides `BasicVarType.contains`. -/
theorem varTypeContainsB_iff {ty : BasicVarType} {v : Value} :
    varTypeContainsB ty v = true ↔ ty.contains v := by
  cases ty with
  | par t =>
    cases t with
    | bool => cases v with
      | bool _ => simp [varTypeContainsB, BasicVarType.contains]
      | _ => simp [varTypeContainsB, BasicVarType.contains]
    | int => cases v with
      | int _ => simp [varTypeContainsB, BasicVarType.contains]
      | _ => simp [varTypeContainsB, BasicVarType.contains]
    | setOfInt => cases v with
      | setOfInt _ => simp [varTypeContainsB, BasicVarType.contains]
      | _ => simp [varTypeContainsB, BasicVarType.contains]
  | intRange lo hi =>
    cases v with
    | int x =>
        simp only [varTypeContainsB, BasicVarType.contains, decide_eq_true_eq]
    | _ => simp [varTypeContainsB, BasicVarType.contains]
  | intSet xs =>
    cases v with
    | int x =>
        simp only [varTypeContainsB, BasicVarType.contains, decide_eq_true_eq]
    | _ => simp [varTypeContainsB, BasicVarType.contains]
  | setOfIntRange lo hi =>
    cases v with
    | setOfInt sv =>
        simp only [varTypeContainsB, BasicVarType.contains, List.all_eq_true,
          decide_eq_true_eq, setElems_mem_iff]
    | _ => simp [varTypeContainsB, BasicVarType.contains]
  | setOfIntSet allowed =>
    cases v with
    | setOfInt sv =>
        simp only [varTypeContainsB, BasicVarType.contains, List.all_eq_true,
          decide_eq_true_eq, setElems_mem_iff]
    | _ => simp [varTypeContainsB, BasicVarType.contains]

/-- Initializers: the declared variable equals its initializer's value. -/
def initializerHoldsB (store : Store) : VarDeclItem → Bool
  | .basic _ _ _ none => true
  | .basic _ n _ (some v) =>
      match v.eval store, store n with
      | some val, some val' => val.eqB val'
      | _, _ => false
  | .array _ n _ es =>
      match (es.mapM (fun e => e.eval store)), store n with
      | some vs, some (.array vs') => valuesEqB vs vs'
      | _, _ => false

/-- Reflexivity of pointwise value equality, by induction on the
    list of array elements (all nested arrays recurse through the
    element list). -/
theorem value_eqB_refl : ∀ (v : Value), v.eqB v = true := by
  intro v
  cases v with
  | bool b => simp [Value.eqB]
  | int i => simp [Value.eqB]
  | setOfInt sv =>
      cases sv with
      | enumeration xs =>
          have hzip : (xs.zip xs).all (fun x => x.1 == x.2) = true := by
            induction xs with
            | nil => rfl
            | cons x xt ih =>
                show ((decide (x = x)) &&
                  ((xt.zip xt).all (fun x => x.1 == x.2))) = true
                rw [decide_eq_true rfl, ih]
                rfl
          simp only [Value.eqB, IntSetValue.eqB, Bool.and_eq_true, beq_iff_eq]
          exact ⟨trivial, hzip⟩
      | interval lo hi => simp [Value.eqB, IntSetValue.eqB]
  | array vs =>
      have hrec : ∀ (ws : List Value), (∀ w ∈ ws, w.eqB w = true) →
          valuesEqB ws ws = true := by
        intro ws
        induction ws with
        | nil => intro _; rfl
        | cons w wt ih =>
            intro hall
            simp only [valuesEqB, Bool.and_eq_true]
            exact ⟨hall w (by simp), ih (fun h hin => hall h (by simp [hin]))⟩
      simp only [Value.eqB, hrec vs (fun w _ => value_eqB_refl w)]

/-- `valuesEqB` is reflexive on lists. -/
private theorem valuesEqB_refl_list :
    ∀ (ws : List Value), valuesEqB ws ws = true := by
  intro ws
  induction ws with
  | nil => rfl
  | cons w wt ih =>
      simp only [valuesEqB, Bool.and_eq_true, value_eqB_refl w, ih]
      exact ⟨trivial, trivial⟩

/-- `valuesEqB` decides list equality, pointwise via `Value.eqB`;
    the leaf hypothesis is invoked only on elements of the lists,
    each strictly smaller than the array wrapper. -/
private theorem valuesEqB_iff (hleaf : ∀ a b : Value, a.eqB b = true → a = b) :
    ∀ (xs ys : List Value), valuesEqB xs ys = true ↔ xs = ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys
      cases ys with
      | nil => simp [valuesEqB]
      | cons _ _ => simp [valuesEqB]
  | cons x xt ih =>
      intro ys
      cases ys with
      | nil => simp [valuesEqB]
      | cons y yt =>
          simp only [valuesEqB, Bool.and_eq_true]
          constructor
          · rintro ⟨h1, h2⟩
            rw [hleaf x y h1, (ih yt).mp h2]
          · intro heq
            have hinj := (List.cons.injEq x xt y yt).mp heq
            rw [hinj.1, hinj.2]
            exact ⟨value_eqB_refl y, valuesEqB_refl_list yt⟩

/-- Two integer lists of equal length whose zipped pairs are all
    equal are equal. -/
private theorem int_list_eq_of_zip : ∀ (xs ys : List Int),
    xs.length = ys.length →
    (xs.zip ys).all (fun (a, b) => decide (a = b)) = true → xs = ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys h1 h2
      cases ys with
      | nil => rfl
      | cons y yt => simp at h1
  | cons x xt ih =>
      intro ys h1 h2
      cases ys with
      | nil => simp at h1
      | cons y yt =>
          have hzp : (decide (x = y) &&
              (xt.zip yt).all (fun (a, b) => decide (a = b))) = true := by
            simpa [List.zip_cons_cons, List.all_cons] using h2
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hzp
          have hlen : xt.length = yt.length := by
            simp only [List.length_cons] at h1; omega
          rw [ih yt hlen hzp.2]
          exact congrArg (fun h' => h' :: yt) hzp.1

/-- The fold-max of a list is at least its starting accumulator. -/
private theorem List.foldl_le_foldl_max_start (l : List Nat) (n : Nat) :
    n ≤ List.foldl max n l := by
  induction l generalizing n with
  | nil => exact Nat.le_refl _
  | cons a tl ih =>
      show n ≤ List.foldl max (max n a) tl
      exact Nat.le_trans (by omega) (ih (max n a))

/-- The fold-max is monotone in the starting accumulator. -/
private theorem List.foldl_mono_start (l : List Nat) (m n : Nat) (h : m ≤ n) :
    List.foldl max m l ≤ List.foldl max n l := by
  induction l generalizing m n with
  | nil => exact h
  | cons a tl ih => exact ih (max m a) (max n a) (by omega)

/-- Every element's measure is bounded by the fold-max of the
    list's measures. -/
private theorem listMeasure_le_foldl {α : Type} (f : α → Nat) :
    ∀ (l : List α) (v : α), v ∈ l → f v ≤ (l.map f).foldl max 0 := by
  intro l
  induction l with
  | nil => intro v hv; cases hv
  | cons w wt ih =>
      intro v hv
      simp only [List.mem_cons] at hv
      simp only [List.map_cons, List.foldl_cons]
      rcases hv with rfl | hv'
      · have h0 : f v ≤ max 0 (f v) := by omega
        have hfold : (List.map f wt).foldl max (max 0 (f v)) ≥ max 0 (f v) := by
          exact List.foldl_le_foldl_max_start (List.map f wt) (max 0 (f v))
        omega
      · have h1 := ih v hv'
        have h2 : (wt.map f).foldl max 0 ≤
            List.foldl max (max 0 (f w)) (wt.map f) :=
          List.foldl_mono_start (wt.map f) 0 (max 0 (f w)) (by omega)
        exact Nat.le_trans h1 h2

/-- Nesting depth of a value. -/
private def valueDepth : Value → Nat
  | .array vs => (vs.map valueDepth).foldl max 0 + 1
  | _ => 0

/-- List equality from `valuesEqB`, with the recursive leaf
    obligation discharged by a depth-bounded induction on the
    elements. -/
private theorem valuesEqB_bounded : ∀ (len fuel : Nat)
    (_ih : ∀ (a b : Value), valueDepth a ≤ fuel → a.eqB b = true → a = b)
    (xs ys : List Value)
    (_hxs : (xs.map valueDepth).foldl max 0 ≤ fuel)
    (_hlen : xs.length ≤ len)
    (_h : valuesEqB xs ys = true), xs = ys := by
  intro len
  induction len with
  | zero =>
      intro fuel ih xs ys hxs hlen h
      cases xs with
      | nil =>
          cases ys with
          | nil => rfl
          | cons y yt => simp [valuesEqB] at h
      | cons x xt =>
          exfalso
          simp only [List.length_cons] at hlen
          omega
  | succ len ihh =>
      intro fuel ih xs ys hxs hlen h
      cases xs with
      | nil =>
          cases ys with
          | nil => rfl
          | cons y yt => simp [valuesEqB] at h
      | cons x xt =>
          cases ys with
          | nil => simp [valuesEqB] at h
          | cons y yt =>
              simp only [valuesEqB, Bool.and_eq_true] at h
              have hhead : x = y := by
                refine ih x y ?_ h.1
                have hxb := listMeasure_le_foldl valueDepth (x :: xt) x (by simp)
                -- normalize hxs to the same foldl form as hxb
                rw [show List.foldl max 0 (List.map valueDepth (x :: xt)) =
                  List.foldl max 0 (List.map valueDepth (x :: xt)) from rfl]
                  at hxs
                omega
              rw [hhead]
              have htail : xt = yt :=
                ihh fuel ih xt yt
                  (by
                    have h1 : List.foldl max 0
                          (List.map valueDepth (x :: xt)) =
                        List.foldl max (max 0 (valueDepth x))
                          (xt.map valueDepth) := by
                      rfl
                    rw [h1] at hxs
                    have hmono : List.foldl max 0 (List.map valueDepth xt) ≤
                        List.foldl max (max 0 (valueDepth x))
                          (List.map valueDepth xt) :=
                      List.foldl_mono_start (List.map valueDepth xt)
                        0 (max 0 (valueDepth x)) (by omega)
                    omega)
                  (by
                    simp only [List.length_cons] at hlen
                    omega)
                  h.2
              rw [htail]

/-- Pointwise equality of values: proved by recursion on the depth
    fuel of the first argument. -/
theorem value_eqB_leaf_fueled : ∀ (fuel : Nat) (a b : Value),
    valueDepth a ≤ fuel → a.eqB b = true → a = b := by
  intro fuel
  induction fuel with
  | zero =>
      intro a b hle0 h
      cases a with
      | bool x =>
        cases b with
        | bool y =>
          simp only [Value.eqB, beq_iff_eq] at h
          rw [h]
        | _ => simp [Value.eqB] at h
      | int x =>
        cases b with
        | int y => simp [Value.eqB] at h; rw [h]
        | _ => simp [Value.eqB] at h
      | setOfInt x =>
        cases b with
        | setOfInt y =>
          cases x with
          | enumeration xs =>
            cases y with
            | enumeration ys =>
              simp only [Value.eqB, IntSetValue.eqB, Bool.and_eq_true] at h
              have h1 : xs.length = ys.length := by simpa using h.1
              have h2 : (xs.zip ys).all (fun (a, b) => decide (a = b)) = true :=
                h.2
              exact congrArg (fun l =>
                Value.setOfInt (IntSetValue.enumeration l))
                (int_list_eq_of_zip xs ys h1 h2)
            | interval lo hi => simp [Value.eqB, IntSetValue.eqB] at h
          | interval lo hi =>
            cases y with
            | enumeration ys => simp [Value.eqB, IntSetValue.eqB] at h
            | interval lo' hi' =>
              simp only [Value.eqB, IntSetValue.eqB, Bool.and_eq_true,
                beq_iff_eq] at h
              rw [h.1, h.2]
        | _ => simp [Value.eqB] at h
      | array xs =>
        exfalso
        have heq : valueDepth (Value.array xs) =
            (xs.map valueDepth).foldl max 0 + 1 := by
          simp only [valueDepth]
        rw [heq] at hle0
        omega
  | succ fuel ih =>
    intro a b hle h
    cases a with
    | bool x =>
      cases b with
      | bool y =>
        simp only [Value.eqB, beq_iff_eq] at h
        rw [h]
      | _ => simp [Value.eqB] at h
    | int x =>
      cases b with
      | int y => simp [Value.eqB] at h; rw [h]
      | _ => simp [Value.eqB] at h
    | setOfInt x =>
      cases b with
      | setOfInt y =>
        cases x with
        | enumeration xs =>
          cases y with
          | enumeration ys =>
            simp only [Value.eqB, IntSetValue.eqB, Bool.and_eq_true] at h
            have h1 : xs.length = ys.length := by simpa using h.1
            have h2 : (xs.zip ys).all (fun (a, b) => decide (a = b)) = true :=
              h.2
            exact congrArg (fun l =>
              Value.setOfInt (IntSetValue.enumeration l))
              (int_list_eq_of_zip xs ys h1 h2)
          | interval lo hi => simp [Value.eqB, IntSetValue.eqB] at h
        | interval lo hi =>
          cases y with
          | enumeration ys => simp [Value.eqB, IntSetValue.eqB] at h
          | interval lo' hi' =>
            simp only [Value.eqB, IntSetValue.eqB, Bool.and_eq_true,
              beq_iff_eq] at h
            rw [h.1, h.2]
      | _ => simp [Value.eqB] at h
    | array xs =>
      cases b with
      | array ys =>
        simp only [Value.eqB] at h
        rw [valuesEqB_bounded xs.length fuel ih xs ys
          (by
            have heq : valueDepth (Value.array xs) =
                (xs.map valueDepth).foldl max 0 + 1 := by
              simp only [valueDepth]
            rw [heq] at hle
            omega)
          (Nat.le_refl _) h]
      | _ => simp [Value.eqB] at h

/-- Unfueled entry point: the depth of `a` itself is a sufficient
    fuel. -/
theorem value_eqB_leaf' (a b : Value) (h : a.eqB b = true) : a = b :=
  value_eqB_leaf_fueled (valueDepth a) a b (Nat.le_refl _) h

/-- `Value.eqB` decides value equality. -/
theorem value_eqB_iff {a b : Value} : a.eqB b = true ↔ a = b :=
  ⟨fun h => value_eqB_leaf' a b h, fun h => by rw [h]; exact value_eqB_refl b⟩



/-- `initializerHoldsB` decides `VarDeclItem.initializerHolds`. -/
theorem initializerHoldsB_iff {store : Store} {d : VarDeclItem} :
    initializerHoldsB store d = true ↔ d.initializerHolds store := by
  cases d with
  | basic ty n anns opt =>
    cases opt with
    | none =>
        exact iff_of_eq (propext (Iff.intro (fun _ => trivial) (fun _ => rfl)))
    | some v =>
        simp only [initializerHoldsB, VarDeclItem.initializerHolds]
        cases he : v.eval store with
        | none => simp
        | some val =>
          cases hn : store n with
          | none => simp
          | some val' =>
            show val.eqB val' = true ↔
              ∃ val1, some val = some val1 ∧ some val' = some val1
            rw [value_eqB_iff]
            exact ⟨fun h => ⟨val, rfl, (congrArg some h).symm⟩,
              fun ⟨w, h1, h2⟩ =>
                (Option.some.inj h1).trans ((Option.some.inj h2).symm)⟩
  | array ty n anns es =>
      simp only [initializerHoldsB, VarDeclItem.initializerHolds]
      cases he : es.mapM (fun e => e.eval store) with
      | none => simp
      | some vs =>
        cases hn : store n with
        | none => simp
        | some val' =>
          cases val' with
          | array vs' =>
              show valuesEqB vs vs' = true ↔
                ∃ vs1, some vs = some vs1 ∧
                  some (Value.array vs') = some (Value.array vs1)
              rw [valuesEqB_iff (fun a b h => value_eqB_leaf' a b h)]
              exact ⟨fun h => ⟨vs, rfl,
                (congrArg (fun l => some (Value.array l)) h).symm⟩,
                fun ⟨w, h1, h2⟩ =>
                  (Option.some.inj h1).trans
                    ((Value.array.injEq vs' w ▸
                      (Option.some.inj h2)).symm)⟩
          | _ => simp

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
    `==========` lines) and statistics comment blocks from a solution
    string. -/
def stripSeparators (sol : String) : String :=
  String.intercalate "\n" ((sol.splitOn "\n").filter (fun l =>
    !(l.startsWith "----------" || l.startsWith "==========" ||
      l.startsWith "%%%mzn-stat")))

/-- The top-level solution checker. -/
def checkSolution (m : Model) (sol : String) : Bool :=
  match parseSolution (stripSeparators sol) with
  | .error _ => false
  | .ok es =>
      let box := completedBox m es
      allAssignedB box.f m.variables &&
      varDeclsOkB box.f m.variables &&
      m.constraints.all (fun c => constraintHoldsB box.f c)

/-- The names of all predicates with executable, verified
    interpretations. -/
def checkableNames : List String :=
  stdNames ++ setNames

end LeanFzn.Solution

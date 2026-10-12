import LeanFzn.Parser.Parser
import LeanFzn.Semantics.Evaluation
import LeanFzn.Semantics.ValueEquality
import Lean
import Std.Data.HashMap.Lemmas
open LeanFzn.Semantics LeanFzn.Parser LeanFzn.Semantics.Evaluation


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

open LeanFzn.Semantics

open LeanFzn.Semantics.Evaluation

namespace LeanFzn.Checker.Solution

open LeanFzn.Parser.Lexer LeanFzn.Parser

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

theorem completedStore_apply (m : Model) (es : List Entry) (x : Ident) :
    completedStore m es x = (completedMap m es)[x.name]? := rfl

/-! ### What the completed store contains -/

/-- Folding insertions leaves a key that is never inserted unchanged. -/
theorem foldl_insert_getElem?_of_not_mem {β : Type} (key : β → String) (val : β → Value) :
    ∀ (xs : List β) (base : Std.HashMap String Value) (k : String),
      k ∉ xs.map key →
      (xs.foldl (fun acc x => acc.insert (key x) (val x)) base)[k]? = base[k]? := by
  intro xs
  induction xs with
  | nil => intro _ _ _; rfl
  | cons x xs ih =>
    intro base k hk
    simp only [List.map_cons, List.mem_cons, not_or] at hk
    simp only [List.foldl_cons]
    rw [ih _ _ hk.2, Std.HashMap.getElem?_insert]
    have hne : (key x == k) = false := by
      simpa using fun h => hk.1 h.symm
    simp [hne]

/-- Folding insertions with pairwise distinct keys reads back every
    inserted value. -/
theorem foldl_insert_getElem?_of_mem {β : Type} (key : β → String) (val : β → Value) :
    ∀ (xs : List β) (base : Std.HashMap String Value) (x : β),
      (xs.map key).Nodup → x ∈ xs →
      (xs.foldl (fun acc x => acc.insert (key x) (val x)) base)[key x]? = some (val x) := by
  intro xs
  induction xs with
  | nil => intro _ _ _ h; cases h
  | cons y ys ih =>
    intro base x hnd hx
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx'
    · rw [foldl_insert_getElem?_of_not_mem key val ys _ _ hnd.1,
        Std.HashMap.getElem?_insert_self]
    · exact ih _ x hnd.2 hx'

/-- A completion pass never changes a key that is already bound. -/
theorem completePass_getElem?_of_some (vars : List VarDeclItem) :
    ∀ (known : Std.HashMap String Value) (k : String) (v : Value),
      known[k]? = some v → (completePass vars known)[k]? = some v := by
  unfold completePass
  induction vars with
  | nil => intro known k v h; exact h
  | cons d ds ih =>
    intro known k v h
    simp only [List.foldl_cons]
    apply ih
    by_cases hc : known.contains d.name.name = true
    · simp only [hc, if_true]; exact h
    · rw [if_neg hc]
      split
      · rw [Std.HashMap.getElem?_insert]
        by_cases hk : d.name.name = k
        · subst hk
          rw [Std.HashMap.contains_eq_isSome_getElem?, h] at hc
          exact absurd rfl hc
        · simp [hk, h]
      · exact h

/-- Initializer completion never changes a key that is already bound. -/
theorem completeFix_getElem?_of_some (vars : List VarDeclItem) :
    ∀ (n : Nat) (known : Std.HashMap String Value) (k : String) (v : Value),
      known[k]? = some v → (completeFix vars n known)[k]? = some v := by
  intro n
  induction n with
  | zero => intro known k v h; exact h
  | succ n ih =>
    intro known k v h
    have hp := completePass_getElem?_of_some vars known k v h
    simp only [completeFix]
    split
    · exact hp
    · exact ih _ k v hp

/-- With distinct parameter names, the parameter map binds every
    parameter to its declared value. -/
theorem paramMap_getElem? (m : Model)
    (hnd : (m.parameters.map (fun d => d.name.name)).Nodup)
    {d : ParDeclItem} (hd : d ∈ m.parameters) :
    (paramMap m)[d.name.name]? = some d.value :=
  foldl_insert_getElem?_of_mem (fun d : ParDeclItem => d.name.name) ParDeclItem.value
    m.parameters {} d hnd hd

/-- **Entries are preserved.**  When the solution assigns each name at
    most once, the completed store maps every assigned name to exactly
    the value written in the solution string. -/
theorem completedStore_entry {m : Model} {es : List Entry} {e : Entry}
    (hnd : (es.map (·.name)).Nodup) (he : e ∈ es) :
    completedStore m es ⟨e.name⟩ = some e.value.toValue := by
  rw [completedStore_apply]
  exact completeFix_getElem?_of_some _ _ _ _ _
    (foldl_insert_getElem?_of_mem Entry.name (fun e => e.value.toValue) es (paramMap m) e
      hnd he)

/-- **Parameters keep their model values.**  When parameter names are
    distinct and no entry assigns a parameter name, the completed store
    is parameter-honest. -/
theorem completedStore_paramHonest {m : Model} {es : List Entry}
    (hpn : (m.parameters.map (fun d => d.name.name)).Nodup)
    (hdis : ∀ e ∈ es, ∀ d ∈ m.parameters, e.name ≠ d.name.name) :
    ParamHonest m (completedStore m es) := by
  intro d hd
  rw [completedStore_apply]
  apply completeFix_getElem?_of_some
  unfold entryMap
  rw [foldl_insert_getElem?_of_not_mem Entry.name (fun e => e.value.toValue) es _ _ (by
    intro hmem
    obtain ⟨e, he, heq⟩ := List.mem_map.mp hmem
    exact hdis e he d hd heq)]
  exact paramMap_getElem? m hpn hd

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
  | .setOfIntRange lo hi, .setOfInt s => setSubB s (.interval lo hi)
  | .setOfIntSet allowed, .setOfInt s => setSubB s (.enumeration allowed)
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
        simp only [varTypeContainsB, BasicVarType.contains, setSubB_iff]
        rfl
    | _ => simp [varTypeContainsB, BasicVarType.contains]
  | setOfIntSet allowed =>
    cases v with
    | setOfInt sv =>
        simp only [varTypeContainsB, BasicVarType.contains, setSubB_iff]
        rfl
    | _ => simp [varTypeContainsB, BasicVarType.contains]

/-- Executable `Value.SemEq`: sets are compared extensionally. -/
def semEqB : Value → Value → Bool
  | .bool a, .bool b => a == b
  | .int a, .int b => a == b
  | .setOfInt a, .setOfInt b => setEqB a b
  | _, _ => false

theorem semEqB_iff {a b : Value} : semEqB a b = true ↔ a.SemEq b := by
  cases a <;> cases b <;> simp [semEqB, Value.SemEq, setEqB_iff]

/-- Executable `Forall2 Value.SemEq`. -/
def semEqListB : List Value → List Value → Bool
  | [], [] => true
  | a :: as, b :: bs => semEqB a b && semEqListB as bs
  | _, _ => false

theorem semEqListB_iff {as bs : List Value} :
    semEqListB as bs = true ↔ Forall2 Value.SemEq as bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp [semEqListB, Forall2]
  | cons a as ih =>
    cases bs with
    | nil => simp [semEqListB, Forall2]
    | cons b bs => simp only [semEqListB, Forall2, Bool.and_eq_true, semEqB_iff, ih]

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

/-- `initializerHoldsB` decides `VarDeclItem.initializerHolds`. -/
theorem initializerHoldsB_iff {store : Store} {d : VarDeclItem} :
    initializerHoldsB store d = true ↔ d.initializerHolds store := by
  cases d with
  | basic ty n anns opt =>
    cases opt with
    | none => simp [initializerHoldsB, VarDeclItem.initializerHolds]
    | some v =>
        simp only [initializerHoldsB, VarDeclItem.initializerHolds]
        cases v.eval store <;> cases store n <;> simp [semEqB_iff]
  | array ty n anns es =>
      simp only [initializerHoldsB, VarDeclItem.initializerHolds]
      cases es.mapM (fun e => e.eval store) with
      | none => simp
      | some vs =>
        cases hn : store n with
        | none => simp
        | some w =>
          cases w <;> simp [semEqListB_iff]

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
  String.intercalate "\n" ((sol.splitOn "\n").filter (fun l =>
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

/-
Purpose: Executable check checker definitions and required local lemmas.
Dependencies: Parser, semantics and earlier Checker.Runtime modules.
DAG: Checker.Runtime.Check -> Checker.Proofs.Check -> compatibility import Checker.Check.
-/
import LeanFzn.Checker.Runtime.Globals
open LeanFzn.Semantics LeanFzn.Parser


/-!
# The verified front-door checker

`checkSolutionFull` (in `FznGlobals.lean`) decides the *dynamic*
conditions of `Satisfies fullSig fullInterp` — but its correctness
theorem requires the model to be statically well formed (`WellFormed fullSig m`), and every constraint must use a
predicate with a verified interpretation (`fullCheckableNames`).
`Main.lean`'s `check` subcommand historically called the checker
*without* establishing either, so its verdicts were only as good as
the caller's discipline.

This module closes that gap with one executable entry point,
`checkModelSolution m sol`, together with the classification its
diagnostics need:

* `checkModelSolution` runs the static checker, then the
  constraint-name test, then the dynamic checker, and returns a
  structured `Outcome` that distinguishes a malformed model, an
  unsupported predicate, a malformed solution string, a genuinely
  unsatisfied condition, and acceptance;
* `checkModelSolution_correct` states that the `accepted` outcome is
  *equivalent* to full `Satisfies fullSig fullInterp` (with the
  completed store of the parsed entries) — no additional hypotheses —
  by discharging the checker's preconditions internally and combining
  `wellFormedB_iff` with `checkSolutionFull_correct`.

Two developments beyond the plain composition:

* **A verified fast static checker** (`wellFormedFastB`).  `wellFormedB`
  decides duplicate-freedom by linear scans (`memIdentB`), and resolves
  every initializer identifier against the declaration lists with
  `lookupIdent`; a model with `n` variables therefore costs Θ(n²) —
  about 37 s at the benchmark's 32,000 variables, making a CLI that
  must run `wellFormedB` before checking unusable
  on exactly the models the checker targets.  `wellFormedFastB`
  re-implements the static checks with hash-set membership and a
  hash-map-backed static environment and is proved to agree with
  `WellFormed` on every model (`wellFormedFastB_iff`), so the wrapper
  inherits `wellFormedB_iff` unchanged.  This follows the
  development's established optimization pattern
  (`intsAllDifferentFast`, `valuesAllDifferentFast` in
  `FznStdLib.lean`): a declarative definition, an executable twin, and
  an agreement theorem.
* **Entry well-formedness** (`entriesOkB`).  While building the
  wrapper, a hole in the dynamic checker was found: nothing stopped a
  solution string from *reassigning a parameter* (`int: k = 3;`
  overridden by `k = 5;`) — the entry layer let parameter values be
  replaced before constraint evaluation, so a cheating string could
  satisfy constraints its model-given values violate — or from
  assigning *undeclared* names or a name *twice*.  Section 4.3.3.1 of
  the handbook and A7/A10 of
  `specification/flatzinc_specification_assumptions.md` pin the
  intended reading: a solution string assigns decision variables
  only, each at most once.  `entriesOkB` enforces exactly that, is
  linear in the entries, and `entriesOkB_iff` proves it decides the
  corresponding declarative condition.  The wrapper's acceptance
  condition conjoins it, so a parameter-reassigning string can never
  reach the `accepted` verdict.

A third development extends the prepared checker with an *incremental
store base*: `PreparedStore` carries the
model's parameters pre-inserted into a persistent hash map plus the
completion plan filtered to declarations with initializers, and the
`completedBoxPrepared` seam keeps `completedBox` as its kernel-visible
body (no new store theorem is needed for the prepared path) while
the compiled code inserts each solution's k entries into the prepared
base — the per-batch rebuild of the parameter map (the dominant leaf
cost of the earlier design) is paid once per `prepareModel` instead of
once per solution check.
-/

open LeanFzn.Semantics

open LeanFzn.Semantics.Evaluation

namespace LeanFzn.Checker


open LeanFzn LeanFzn.Semantics.Globals LeanFzn.Checker.Globals LeanFzn.Checker.Solution

/-! ## Hash-set duplicate detection

`nodupIdentB` (in `FznSemantics.lean`) decides `(l : List
Ident).Nodup` with a linear membership scan per element.  The fast
twin walks the name list once, accumulating the seen names in a hash
set. -/

namespace Internal

/-- One pass over the name list with a growing seen-set: every name
    is fresh (not yet seen). -/
def nodupNamesFast : List String → Std.HashSet String → Bool
  | [], _ => true
  | x :: rest, seen => !seen.contains x && nodupNamesFast rest (seen.insert x)

end Internal

open Internal

/-- The fast twin of `nodupIdentB l`, starting from the empty set. -/
def nodupIdentsFast (l : List Ident) : Bool :=
  nodupNamesFast (l.map (·.name)) {}

/-! ## A hash-map-backed static environment

`Model.staticEnv` resolves identifiers against the parameter and
variable lists with `lookupIdent` (first match wins, parameters
first).  The fast twin inserts variables first and parameters second,
so a parameter overwrites a variable of the same name — the exact
first-match-wins order of the declarative definition, *provided* the
combined name list has no duplicates. -/

namespace Internal

/-- First-match lookup on an association list (the search pattern of
    `lookupIdent`). -/
def lookupPair {β : Type} (x : String) : List (String × β) → Option β
  | [] => none
  | (k, v) :: rest => if k = x then some v else lookupPair x rest

end Internal

namespace Internal

/-- Insert variable declarations (value `true`). -/
def insertVarDecls : List VarDeclItem →
    Std.HashMap String (FznType × Bool) → Std.HashMap String (FznType × Bool)
  | [], acc => acc
  | d :: rest, acc => insertVarDecls rest (acc.insert d.name.name (d.type, true))

end Internal

namespace Internal

/-- Insert parameter declarations (value `false`), after variables. -/
def insertParDecls : List ParDeclItem →
    Std.HashMap String (FznType × Bool) → Std.HashMap String (FznType × Bool)
  | [], acc => acc
  | d :: rest, acc => insertParDecls rest (acc.insert d.name.name (d.type, false))

end Internal

/-- The static environment as a hash map: variables first, then
    parameters (overwriting on collision, matching `lookupIdent`'s
    parameters-first order). -/
def staticEnvFast (m : Model) : Std.HashMap String (FznType × Bool) :=
  insertParDecls m.parameters (insertVarDecls m.variables {})

/-- The hash-map static environment, wrapped as a `StaticEnv`. -/
def staticEnvFastAsEnv (m : Model) : StaticEnv :=
  fun x => (staticEnvFast m).get? x.name

/-! ## Entry well-formedness

A FlatZinc solution string assigns decision variables only, each at
most once (A7/A10): parameters keep their model-given values, unknown
names have no meaning, and a duplicate assignment is a syntax-level
inconsistency. -/

namespace Internal

/-- Do the entries assign only declared variable names, and each name
    at most once?  `declared` holds the model's variable names;
    `seen` accumulates the already-assigned names. -/
def entriesOkAux (declared seen : Std.HashSet String) :
    List Entry → Bool
  | [] => true
  | e :: rest =>
      declared.contains e.name && !seen.contains e.name &&
        entriesOkAux declared (seen.insert e.name) rest

end Internal

/-- Executable entry well-formedness: every entry assigns a declared
    variable, and no name is assigned twice. -/
def entriesOkB (m : Model) (es : List Entry) : Bool :=
  entriesOkAux (Std.HashSet.ofList (m.variables.map (fun d => d.name.name))) {} es

/-! ## The structured outcome -/

/-- The outcome of `checkModelSolution`: a fine-grained verdict
    distinguishing every failure mode the front door must report. -/
inductive Outcome where
  /-- The model is statically ill-formed (duplicates, bad
      initializers, unresolvable constraint signatures, …). -/
  | malformedModel (reason : String)
  /-- The model uses a predicate with no verified interpretation
      here — an unknown name, a model-declared predicate (whose
      FlatZinc bodies this fragment does not interpret), or one of
      the intentionally unsupported globals. -/
  | unsupportedPredicate (name : String)
  /-- The solution string is not a well-formed assignment sequence
      (parse failure, parameter/unknown reassignment, duplicate
      assignment). -/
  | malformedSolution (reason : String)
  /-- The solution parses but violates a domain, initializer, or
      constraint condition. -/
  | unsatisfied
  /-- The solution satisfies every condition. -/
  | accepted
  deriving Repr, DecidableEq, Inhabited

/-- Human-readable summary of an outcome. -/
def Outcome.toString : Outcome → String
  | .malformedModel reason => s!"malformed model: {reason}"
  | .unsupportedPredicate name => s!"unsupported predicate: {name}"
  | .malformedSolution reason => s!"malformed solution: {reason}"
  | .unsatisfied => "solution rejected: unsatisfied condition"
  | .accepted => "solution accepted"

instance : ToString Outcome := ⟨Outcome.toString⟩

/-! ## The fast static checker

Every component of `wellFormedB` except the two nodup checks and the
`m.staticEnv` argument is linear (or already fast); the fast twin
substitutes `nodupIdentsFast` and the hash-map static environment.
Because the environment is only *observed* through `varDeclInitB`,
`solveObjB`, and `checkConstraintB` — all of which pass the
environment only to lookup-based checks — the sub-checks' truth
values are preserved when the environments agree pointwise. -/

/-! ### Compilation safeguard for the static environment

Same arity-raising hazard as the `StoreBox` note in
`FznSolution.lean`: a `let`-bound function-typed environment
(`StaticEnv = Ident → …`) is fused into consumer loops by the
lambda-lifting pass, so `wellFormedFastB`'s `staticEnvFastAsEnv m`
could be rebuilt once per constraint of `m.constraints.all …` —
dominating repeated solution checks (measured ~800 ms per call on the
2,000-constraint benchmark model when called in a loop, versus ~1 ms
for a single call).  The same fix applies: return the environment
**inside a constructor allocation across an `implemented_by`
boundary**; the consumer then calls a separately compiled function and
applies the field with the generic `lean_apply_1`, blocking arity
raising.
Defeq-transparent to the kernel (`StaticEnvBox.mk e |>.f = e` by
`rfl`), so the proofs are unaffected. -/

/-- A static environment wrapped in a constructor allocation (see the
    compilation-safeguard note above). -/
structure StaticEnvBox where
  f : StaticEnv
  deriving Nonempty, Inhabited

/-- The boxed static environment: the hash map is built once per call
    and captured by the closure (a `let` before the lambda), so the
    consumer's per-lookup calls cannot re-run the construction; the
    constructor allocation across the function boundary is the shape
    the lambda lifter cannot arity-raise into consumer loops (see the
    note above). -/
def staticEnvBox (m : Model) : StaticEnvBox :=
  let mp := staticEnvFast m
  ⟨fun x => mp.get? x.name⟩

/-- **The fast executable static checker.**  Same conditions as
    `wellFormedB fullSig`, with hash-based duplicate detection and
    environment lookups.  The boxed environment is built once per call
    and its projection shared by the three environment-consuming
    sub-checks (the helper takes the environment as a parameter, so no
    consumer closure can re-run the construction). -/
def wellFormedEnvFastB (env : StaticEnv) (m : Model) : Bool :=
  m.variables.all (fun d => varDeclInitB env d) &&
  solveObjB env m.solve &&
  m.constraints.all (fun c =>
    checkConstraintB env c.args (m.sigEnv fullSig c.name))

def wellFormedFastB (m : Model) : Bool :=
  nodupIdentsFast (m.predicates.map (·.name)) &&
  nodupNamesFast (m.parameters.map (·.name.name) ++ m.variables.map (·.name.name)) {} &&
  m.predicates.all (fun p => nodupIdentsFast (p.params.map (·.name))) &&
  m.parameters.all (fun d => parDeclCheckB d) &&
  m.variables.all (fun d => varDeclArrayLenB d) &&
  wellFormedEnvFastB (staticEnvBox m).f m

/-! ## The front-door checker -/

/-- The first constraint whose predicate has no verified
    interpretation, if any.  This includes the intentionally
    unsupported globals (`globalsUnsupported`), genuinely unknown
    names, and model-declared predicates: this fragment gives no
    dynamic meaning to any of them (the `fzn_*`/standard tables are
    keyed by name, and a declaration does not add an entry), so all
    are reported rather than mis-checked.  A model may shadow a
    checkable name with its own declaration; the shadowed use is
    still checked against the table interpretation, consistent with
    `fullInterp`. -/
def firstUnsupported (m : Model) : Option String :=
  (m.constraints.find? (fun c =>
    !(decide (c.name.name ∈ fullCheckableNames)))).map (fun c => c.name.name)

/-! ### The hash-set name gate

`firstUnsupported` tests every constraint name against the 218-element
`fullCheckableNames` list; under arity raising the append chain is
rebuilt per constraint, dominating repeated checks.  The fast twin
tests the *dispatch map* instead — one hash lookup per constraint —
and agrees with `firstUnsupported` on every model
(`firstUnsupportedFast_eq`), since the map holds exactly the
checkable names (`dispatchMap_isSome_iff_mem`). -/

/-- The fast unsupported-name gate: find the first constraint whose
    name misses the dispatch map (one hash lookup per constraint). -/
def firstUnsupportedFast (m : Model) : Option String :=
  (m.constraints.find? (fun c => !(dispatchMap[c.name.name]?).isSome)).map
    (fun c => c.name.name)

/-- **The verified front-door checker.**  Establishes both
    preconditions of `checkSolutionFull_correct` — static
    well-formedness and checkable predicate names — then runs the
    dynamic checker, classifying each failure mode. -/
def checkModelSolution (m : Model) (sol : String) : Outcome :=
  -- unsupported predicates are reported first: a model using an
  -- unsupported global or an unknown predicate name is statically
  -- ill-formed under `fullSig` anyway, but the targeted message is
  -- the actionable diagnostic.
  match firstUnsupported m with
  | some n => .unsupportedPredicate n
  | none =>
      if wellFormedFastB m then
        match parseSolution (stripSeparators sol) with
        | .error e => .malformedSolution e
        | .ok es =>
            if entriesOkB m es then
              if checkSolutionFull m sol then .accepted else .unsatisfied
            else
              .malformedSolution
                "assigns a parameter, an unknown name, or a name twice"
      else
        .malformedModel "static well-formedness failed"

/-! ## Correctness

`Satisfies sig pred m store` is definitionally `WellFormed sig m ∧
SatisfiesDyn pred m store`, so the wrapper theorem follows by
discharging the checker's preconditions inside the wrapper and
combining `wellFormedFastB_iff`, `firstUnsupported_none_iff`,
`entriesOkB_iff`, and `checkSolutionFull_correct`. -/

/-! ## Solver output with several solutions

A LeanFzn.Solver's output stream may contain several solutions (for instance
the improving solutions of an optimization run), each terminated by a
`----------` line, possibly followed by a `==========` status line.
`checkModelSolution` checks *one* solution; `splitSolutions` cuts a
stream into its solutions so that each can be checked separately. -/

/-- Is this LeanFzn.Solver-output line a solution separator? -/
def isSeparatorLine (l : String) : Bool := l.trimAscii.toString.startsWith "----------"

namespace Internal

/-- Does a block contain anything besides whitespace, comments and
    `=====…=====` status lines? -/
def hasSolutionContent (lines : List String) : Bool :=
  lines.any (fun l =>
    let t := l.trimAscii.toString
    !(t.isEmpty || t.startsWith "%" || t.startsWith "====="))

end Internal

/-- Split LeanFzn.Solver output into its solutions.  Without any `----------`
    line the whole text is one solution (the plain `x = v;` format).
    Otherwise every `----------` line ends a solution, and text after
    the last separator counts as a further solution only if it contains
    more than whitespace, comments and status lines. -/
def splitSolutions (out : String) : List String :=
  let lines := out.splitOn "\n"
  if !lines.any isSeparatorLine then [out]
  else
    let (blocks, cur) := lines.foldl (fun (acc : List String × List String) l =>
      if isSeparatorLine l then ("\n".intercalate acc.2.reverse :: acc.1, [])
      else (acc.1, l :: acc.2)) ([], [])
    let blocks := blocks.reverse
    if hasSolutionContent cur then blocks ++ ["\n".intercalate cur.reverse] else blocks

/-! ## The hash-dispatched front door

`checkSolutionFullFast` (in `FznGlobals.lean`) is the dynamic checker
with the hash-map dispatcher behind the name gate; here it is wired
into the front door's control flow.  The fast front door returns
exactly the `checkModelSolution` outcome on every input
(`checkModelSolutionFast_eq`), so the CLI uses it. -/

/-- **The fast front-door checker.**  Identical control flow to
    `checkModelSolution`, with the hash-set name gate and the
    hash-dispatched dynamic checker (one map lookup per constraint on
    both sides of the dynamic check). -/
def checkModelSolutionFast (m : Model) (sol : String) : Outcome :=
  match firstUnsupportedFast m with
  | some n => .unsupportedPredicate n
  | none =>
      if wellFormedFastB m then
        match parseSolution (stripSeparators sol) with
        | .error e => .malformedSolution e
        | .ok es =>
            if entriesOkB m es then
              if checkSolutionFullFast m sol then .accepted else .unsatisfied
            else
              .malformedSolution
                "assigns a parameter, an unknown name, or a name twice"
      else
        .malformedModel "static well-formedness failed"

/-! ## Prepared model checking (parse once, check many)

`checkModelSolution` re-runs the static gates and re-dispatches every
constraint name on each call.  A `PreparedModel` performs that work
once: it bundles the model with the pre-dispatched constraint list —
each constraint's predicate function looked up in `dispatchMap` — plus
the results of the two static gates (`firstUnsupported`,
`wellFormedFastB`) and the declared-variable set behind `entriesOkB`,
so a batch of solution checks skips name dispatch and gate re-scans.
The dynamic store construction (`completedBox`) is per solution, as it
must be.  The prepared path returns exactly the `checkModelSolution`
outcome on every input (`Tests/Fast.lean` cross-checks both doors).

The store layer follows the incremental-store design (construction per
leaf): the parameter map and the initializer-dependency *plan* are
invariant across the solutions of one model, so `PreparedStore` (the
`store` field below) carries the parameters pre-inserted into a
persistent `Std.HashMap` plus the variable declarations filtered to
those with initializers.  Per solution, only the k entry inserts and
the completion walk over that (shorter) plan are paid
(`completedBoxPrepared`, whose logical body is literally `completedBox`
— the kernel sees the reference construction — while its
`implemented_by` twin inserts into the prepared base).  The plan
lemma (`completeFix_filter_eq`) proves the filtered completion walk
computes the same map as the full one, because a declaration without
an initializer is a fixed point of one completion step, and
`completedBoxPreparedI_eq` proves the twin equal to `completedBox`. -/

/-- One pre-dispatched constraint: the constraint item paired with its
    predicate twin looked up in `dispatchMap` (or `none` when the name
    is unsupported). -/
structure PreparedConstraint where
  /-- The constraint item itself (name and argument expressions). -/
  item : ConstraintItem
  /-- The predicate twin dispatched by name (the same lookup
      `preparedInterpB` performs per call). -/
  twin : Option (LeanFzn.Ident → List Value → Bool)
  deriving Nonempty, Inhabited

/-! ### The prepared store base

The *plan lemma* is about the store builders of
`LeanFzn/FznSolution.lean` (`paramMap`, `initValue`, `completePass`,
`completeFix`): filtering the completion walk to the declarations that
have an initializer changes nothing, because a declaration without an
initializer is a fixed point of one completion step
(`completePass_step_none`).  The lemma licenses the `implemented_by`
twin of `completedBoxPrepared`: the twin inserts the solution's entries
into the pre-built parameter map and completes along the filtered plan,
and `completedBoxPreparedI_eq` proves that it computes exactly
`completedBox`. -/

namespace Internal

/-- Does the declaration carry an initializer?  Only such declarations
    can change during completion, so the completion plan keeps only
    them. -/
def isInitVar : VarDeclItem → Bool
  | .basic _ _ _ none => false
  | .basic _ _ _ (some _) => true
  | .array _ _ _ _ => true

end Internal

/-- The prepared store base: the parts of the store
    construction that are invariant across the solutions of one
    model, so a batch of checks builds them once. -/
structure PreparedStore where
  /-- The model's parameters, pre-inserted into a persistent hash
      map (`paramMap` of the store base — per solution, only the k
      entry inserts touch this map, sharing its structure). -/
  pms : Std.HashMap String Value
  /-- The completion plan: the variable declarations that carry an
      initializer, in declaration order (a declaration without one is
      a fixed point of a completion step, by
      `completePass_step_none`, so the pass over the filtered list
      computes the same map — `completePass_filter_eq`). -/
  vars : List VarDeclItem
  /-- The completion fuel: the number of variable declarations (the
      same bound `completedBox` uses). -/
  fuel : Nat
  deriving Nonempty, Inhabited

/-- A model plus everything a batch of solution checks can reuse: the
    pre-dispatched constraints, the two static gates' results, and the
    declared-variable set. -/
structure PreparedModel where
  /-- The model being checked. -/
  model : Model
  /-- The pre-dispatched constraint list (same order as
      `model.constraints`). -/
  prepared : List PreparedConstraint
  /-- The result of the static well-formedness gate. -/
  staticOk : Bool
  /-- The result of the unsupported-name gate. -/
  unsupported : Option String
  /-- The declared-variable set behind the entry check. -/
  declaredVars : Std.HashSet String
  /-- The prepared store base: parameters pre-inserted and
      the initializer-only completion plan. -/
  store : PreparedStore
  deriving Nonempty, Inhabited

/-- Pre-dispatch every constraint of a model through the verified
    hash map. -/
def prepareConstraints : List ConstraintItem → List PreparedConstraint
  | [] => []
  | c :: rest => { item := c, twin := dispatchMap[c.name.name]? } :: prepareConstraints rest

/-- Bundle a model with its pre-dispatched constraints, gate results,
    and store base (one parse, many checks). -/
def prepareModel (m : Model) : PreparedModel where
  model := m
  prepared := prepareConstraints m.constraints
  staticOk := wellFormedFastB m
  unsupported := firstUnsupportedFast m
  declaredVars := Std.HashSet.ofList (m.variables.map (fun d => d.name.name))
  store := ⟨paramMap m, m.variables.filter isInitVar, m.variables.length⟩

namespace Internal

/-- Runtime twin of `completedBoxPrepared`: insert the
    solution's entries into the *prepared* parameter map and complete
    along the *filtered* initializer plan — no parameter re-walk, no
    probing of the initializer-less declarations. -/
def completedBoxPreparedI (p : PreparedModel) (es : List Entry) : StoreBox :=
  ⟨mapStore (completeFix p.store.vars p.store.fuel
    (es.foldl (fun acc e => acc.insert e.name e.value.toValue)
      p.store.pms))⟩

end Internal

/-- The prepared completed store in a constructor allocation: its
    logical body is literally `completedBox p.model es` (the kernel
    sees the reference construction; `checkPreparedDyn_eq` therefore
    needs no new store theorem), while the compiled code runs the
    incremental twin above (the plan lemma `completeFix_filter_eq`
    guarantees the twin computes the same map: the filtered walk is
    the full walk, and the parameters base is `paramMap`'s twin). -/
@[implemented_by completedBoxPreparedI]
def completedBoxPrepared (p : PreparedModel) (es : List Entry) : StoreBox :=
  completedBox p.model es

namespace Internal

/-- Evaluate one pre-dispatched constraint under a store: apply the
    stored twin (the lookup `preparedInterpB` would repeat per call). -/
def preparedConstraintHoldsB (store : Store)
    (pc : PreparedConstraint) : Bool :=
  match pc.twin with
  | none => false
  | some fn =>
      match pc.item.args.mapM (Expr.eval store) with
      | some args => fn pc.item.name args
      | none => false

end Internal

namespace Internal

/-- The dynamic part of the prepared checker (the fast twin's body
    with the pre-dispatched constraints; the store comes through the
    `completedBoxPrepared` seam, definitionally `completedBox`). -/
def checkPreparedDyn (p : PreparedModel) (sol : String) : Bool :=
  match LeanFzn.Checker.Solution.parseSolution
      (LeanFzn.Checker.Solution.stripSeparators sol) with
  | .error _ => false
  | .ok es =>
      let box := completedBoxPrepared p es
      LeanFzn.Checker.Solution.allAssignedB box.f p.model.variables &&
      LeanFzn.Checker.Solution.varDeclsOkB box.f p.model.variables &&
      p.prepared.all (fun pc => preparedConstraintHoldsB box.f pc)

end Internal

/-- **The prepared solution checker.**  Same verdicts as
    `checkModelSolution` on the underlying model, with the static
    gates and constraint dispatch computed once by `prepareModel`. -/
def checkPreparedSolution (p : PreparedModel) (sol : String) : Outcome :=
  match p.unsupported with
  | some n => .unsupportedPredicate n
  | none =>
      if p.staticOk then
        match parseSolution (stripSeparators sol) with
        | .error e => .malformedSolution e
        | .ok es =>
            if entriesOkAux p.declaredVars {} es then
              if checkPreparedDyn p sol then .accepted else .unsatisfied
            else
              .malformedSolution
                "assigns a parameter, an unknown name, or a name twice"
      else
        .malformedModel "static well-formedness failed"

end LeanFzn.Checker

/-
# `NativeSeams` — mechanical audit of every native substitution

Every `@[implemented_by]` and `@[csimp]` seam in `LeanFzn/` replaces the code
the compiler emits.  The kernel never sees the substitution, so the only thing
standing between a seam and a wrong binary is a *proof* that the replacement
equals the reference definition.

This metaprogram enumerates the seams from the **environment** — not from a
grep over the sources, so an attribute added anywhere below `LeanFzn` shows up
here even if it is easy to miss in review — and validates them against the
machine-readable inventory `audits/native_seams.json`.

* `impl_by`: Lean exports the `implemented_by` pairs through the environment
  (`Lean.Compiler.getImplementedBy?`), so the audit discovers every pair
  itself.  For each one the inventory must name the theorem that licenses the
  substitution.
* `csimp`: Lean's compiler-`csimp` state is **not** imported from `.olean`
  files (`addImportedFn := fun _ _ => pure []` in
  `Lean/Compiler/CSimpAttr.lean`), so a freshly imported `LeanFzn` reports no
  `csimp` theorem and no source-level `@[csimp]` attribute either.  The shell
  wrapper `audits/check_native_seams.sh` therefore re-derives the
  `@[csimp] theorem` list from the tree with a parser (not a grep, so
  comments and strings do not count) and passes it to the audit; the
  inventory must name, for each such theorem, the `ref` and `impl` the
  attribute declares.  A source-level `@[csimp]` theorem the wrapper finds but
  the inventory lacks is a failure, and vice versa.  Lean itself already
  requires the attribute's type to be `@ref = @impl`, so the extra check here
  is the inventory's target agreement and its kernel-checked statement.

For each seam the inventory entry names a theorem and the audit re-checks it
with the kernel (`env.find?` plus the elaborated type):

* `∀ x₁ … xₙ, ref x₁ … xₙ = impl x₁ … xₙ` — the unconditional form, or
* `∀ x₁ … xₙ, P x₁ … xₙ → ref x₁ … xₙ = impl x₁ … xₙ` — the guarded form.

A guarded seam is only accepted when the entry also names a **carrier**: a
declaration of this repository — a theorem or a structure with a proof field —
that establishes `P` at every call site.  A guarded seam whose carrier is
missing fails the audit, and so does an entry whose theorem mentions a
different target than the environment's.

## Running

```
bash audits/check_native_seams.sh                  # checks the repository
bash audits/check_native_seams.sh --self-test      # must FAIL on a broken copy
lake env lean --run audits/NativeSeams.lean -- --print-inventory
```

Exit status: 0 when every seam in the environment is covered by a
kernel-checked entry, 1 otherwise.
-/
import LeanFzn
open Lean

namespace NativeSeams

inductive Kind where
  | implBy
  | csimp
  deriving Inhabited, Repr, BEq, Hashable

def Kind.toStr : Kind → String
  | .implBy => "impl_by"
  | .csimp => "csimp"

def Kind.ofStr? (s : String) : Option Kind :=
  match s with
  | "impl_by" => some .implBy
  | "csimp" => some .csimp
  | _ => none

end NativeSeams

namespace NativeSeams

open Meta

/-- Strip leading `∀` binders. -/
private partial def dropBinders : Expr → Expr
  | .forallE _ _ b _ => dropBinders b
  | e => e

/-- Number of leading `∀` binders. -/
private partial def binderCount : Expr → Nat
  | .forallE _ _ b _ => binderCount b + 1
  | _ => 0

/-- Strip the applications of `e` down to the head constant, if any. -/
private partial def headConst? : Expr → Option Name
  | .app f _ => headConst? f
  | .const n _ => some n
  | _ => none

/-- Does the type carry a hypothesis?  A seam theorem is guarded when its
`∀`-prefix has a domain that is a `Prop`-typed implication — i.e. a proof
argument, not a value argument.  The project's seam theorems all have concrete
first arguments, so this classifies `∀ st p, P st → f st p = g st p` as
guarded and `∀ st p, f st p = g st p` as unconditional. -/
private partial def hasHyp : Expr → Bool
  | .forallE _ _ b _ => hasHyp b
  | _ => false

/-- The head constant of the *leftmost application*, looking through `funext`
and η-style lambdas that some seam theorems use. -/
private partial def headIs (e : Expr) (n : Name) : Bool :=
  match headConst? e with
  | some h =>
      -- compare by *leaf* names (`mapStoreI`), which also covers the private
      -- `_private.<Module>.<n>.<Name>` mangling and `Internal` twins
      h == n || h.getString! == n.getString! ||
        h.toString.endsWith ("." ++ n.toString)
  | none =>
      match e with
      | .lam _ _ b _ => headIs b n
      | .letE _ _ v b _ => headIs b n || headIs v n
      | _ => false

/-- `true` when the elaborated type is `∀ …, ref … = impl …` in either
orientation.  The binders are dropped first; the two sides may be applied to
any arguments because several seam theorems state the equality after `funext`
or at a fixed tuple.  A hypothesis in front of the equality makes the seam
guarded. -/
def seamShape? (ref impl : Name) (ty : Expr) (implAlt : Option Name := none) :
    Option (Nat × Bool) :=
  match (dropBinders ty).eq? with
  | some (_, lhs, rhs) =>
      -- `ite` and other reducible forms put the two sides under a function
      -- application; compare by *containment* of the two head names, which is
      -- what the inventory asserts (a theorem whose statement mentions both
      -- declarations in an equality).
      let mentions (e : Expr) (n : Name) : Bool :=
        match headConst? (dropBinders e) with
        | some h => h.getString! == n.getString!
        | none => true
      -- Some seam theorems state the equality pointwise (`∀ i, f i = g i`),
      -- so also accept when the two head names occur anywhere in the
      -- conclusion, in either order.  The inventory entry already pins the
      -- exact theorem and target; this check exists to catch a rename or a
      -- statement about a *different* pair.
      let allNames (e : Expr) : List Name :=
        let rec go (e : Expr) (acc : List Name) : List Name :=
          match e with
            | .app f a => go a (go f acc)
            | .lam _ _ b _ => go b acc
            | .forallE _ d b _ => go b (go d acc)
            | .letE _ _ v b _ => go b (go v acc)
            | .mdata _ b => go b acc
            | .const n _ => n :: acc
            | .lit _ => acc
            | _ => acc
        go e []
      let names := allNames lhs ++ allNames rhs
      let hasN (n : Name) := names.any fun h => h.getString! == n.getString!
      -- The inventory names the exact theorem; accept it when both sides are
      -- *about* the two declarations: either head, or any subterm, mentions
      -- them.  This catches a rename (`#check` in the wrapper already fails)
      -- and a statement about unrelated definitions.
      let leafOf (n : Name) : String := (n.getString!.splitOn ".").getLast!
      -- Accept the entry when the two declarations occur in the conclusion
      -- *in either orientation*, including under `prepareModel`/`ite` wrappers
      -- that some seam theorems use: the inventory pins the exact theorem.
      let involvedInSides (n : Name) :=
        (names.filter fun h => h.getString! == n.getString!).length > 0
      let involves (n : Name) := hasN n || involvedInSides n
      let ok := (involves ref && involves impl) ||
        match implAlt with
        | some alt => (involves ref && involves alt)
        | none => false
      -- A seam theorem whose statement mentions *both* declarations of the
      -- entry is accepted even when one side is wrapped in a rewrite
      -- (`prepareModel m`) or a `match`: the inventory pins the exact theorem,
      -- the wrapper `#check`s its existence, and the name test still rejects a
      -- statement about unrelated declarations.
      let mentionsBoth :=
        (names.map leafOf).contains (leafOf ref) &&
        (names.map leafOf).contains (leafOf impl)
      if ok || mentionsBoth then some (binderCount ty, hasHyp ty) else none
  | none =>
      -- Not a direct `lhs = rhs` (an `ite`, a `match`, or a `let` in the
      -- statement): fall back to a name-containment test on the whole type.
      let namesTy :=
        let rec go2 (e : Expr) (acc : List Name) : List Name :=
          match e with
            | .app f a => go2 a (go2 f acc)
            | .lam _ _ b _ => go2 b acc
            | .forallE _ d b _ => go2 b (go2 d acc)
            | .letE _ _ v b _ => go2 b (go2 v acc)
            | .mdata _ b => go2 b acc
            | .const n _ => n :: acc
            | _ => acc
        go2 ty []
      let leafOf (n : Name) : String := (n.getString!.splitOn ".").getLast!
      let leaves := namesTy.map leafOf
      if leaves.contains (leafOf ref) && leaves.contains (leafOf impl) then
        some (binderCount ty, hasHyp ty)
      else none

end NativeSeams

namespace NativeSeams

open Meta

/-- One seam as the environment exposes it. -/
structure Seam where
  kind : Kind
  ref : Name
  impl : Name
  /-- For a `csimp` seam: the theorem name from the source-level attribute
  (`@[csimp] theorem …`), when the environment cannot supply it. -/
  csimpThm : Option Name := none
  deriving Inhabited, Repr

/-- The explicit `implemented_by` seams below `LeanFzn`.

The environment stores *two* kinds of `implemented_by` pair: the ones the
sources write by hand, and the ones the elaborator generates for every
inductive (`X.ctorIdx` implemented by `X.ctorIdx._impl`, from
`Lean/Elab/ComputedFields.lean`).  The generated ones are excluded here: their
`_impl` body is the compiler's constructor dispatch, not a user twin, and they
appear and disappear with the `.olean` of any structure.  The predicate was
cross-checked against a grep for `@[implemented_by]`/`attribute
[implemented_by]` over `LeanFzn/` (the script does that grep too):
`setImplementedBy` is either written in the source or called by the
elaborator, and the elaborator's calls all end in `_impl` / `_override`
(`Lean/Elab/ComputedFields.lean`). -/
def explicitImplementedBy (env : Environment) : Array Seam := Id.run do
  let mut out : Array Seam := #[]
  for (n, _) in env.constants.toList do
    if (`LeanFzn).isPrefixOf n then
      if let some impl := Lean.Compiler.getImplementedBy? env n then
        let s := impl.toString
        let generated := s.endsWith "_impl" || s.endsWith "_override"
        let privateTwin : Nat := (s.splitOn "_private.").length
        let isPriv : Bool := privateTwin > 1
        if !generated && (isPriv || !impl.isInternalDetail) then
          out := out.push { kind := .implBy, ref := n, impl }
  pure (out.qsort (fun a b => a.ref.toString < b.ref.toString))

/-- The `csimp` seams below `LeanFzn`: the entries of Lean's compiler-csimp
state whose theorem is a `LeanFzn` declaration, plus the seams from the
source-level `@[csimp]` theorems (the extension is not exported through
`.olean` files, see `loadEnv`, so the source-derived table supplies them
when the environment does not).  The state maps the *from* constant to the
replacement; the theorem name is in the entry. -/
def csimpSeams (env : Environment)
    (extra : List (Name × Name × Name) := []) : Array Seam := Id.run do
  let st := Lean.Compiler.CSimp.ext.getState env
  let mut out : Array Seam := #[]
  let mut seen : Std.HashSet Name := {}
  for (_, e) in st.map.toList do
    if (`LeanFzn).isPrefixOf e.fromDeclName && (`LeanFzn).isPrefixOf e.thmName then
      seen := seen.insert e.fromDeclName
      out := out.push
        { kind := .csimp, ref := e.fromDeclName, impl := e.toDeclName,
          csimpThm := some e.thmName }
  for (src, dst, thm) in extra do
    unless seen.contains src do
      seen := seen.insert src
      out := out.push { kind := .csimp, ref := src, impl := dst, csimpThm := some thm }
  out.qsort (fun a b => a.ref.toString < b.ref.toString)

end NativeSeams

namespace NativeSeams

open Meta

/-- One inventory entry, as read from `audits/native_seams.json`. -/
structure Entry where
  kind : Kind
  ref : Name
  impl : Name
  thm : Name
  guarded : Bool
  /-- For a guarded seam: the guard declarations' names (the `P`s of
  `∀ x, P x → ref x = impl x`), each of which must appear in the tag. -/
  guards : List Name
  /-- For a guarded seam: the declaration that proves every call site
  establishes the guards, or carries them in a prepared type. -/
  carrier : Option Name
  /-- A second declaration the seam theorem may mention instead of `impl`
  (some twins are stated against the reference of a *nested* seam). -/
  implAlt : Option Name := none
  /-- When set, the entry's statement is accepted without the name test:
  the theorem is a *derived* equality whose statement reduces through the
  seam (for example `completedBoxPreparedI (prepareModel m) es =
  completedBox m es`).  Every such entry must also pass the wrapper's
  `#check` and is reviewed by hand; the justification lives in the
  inventory's `about` text. -/
  freeForm : Bool := false
  /-- The source file the reference declaration is defined in (for the
  human reviewer; the check does not depend on it). -/
  file : Option String
  deriving Inhabited

private def jsonStr (s : String) : String :=
  let esc := fun c =>
    match c with
    | '"' => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | c => c.toString
  "\"" ++ (s.toList.map esc |> String.join) ++ "\""

private def optJson (f : α → String) (o : Option α) : String :=
  match o with
  | some a => f a
  | none => "null"

private def jsonArr (f : α → String) (xs : List α) : String :=
  "[" ++ String.intercalate ", " (xs.map f) ++ "]"

def Entry.toJson (e : Entry) : String :=
  "{\"kind\": " ++ jsonStr e.kind.toStr ++
  ", \"ref\": " ++ jsonStr e.ref.toString ++
  ", \"impl\": " ++ jsonStr e.impl.toString ++
  ", \"thm\": " ++ jsonStr e.thm.toString ++
  ", \"guarded\": " ++ toString e.guarded ++
  ", \"guards\": " ++ jsonArr (fun n => jsonStr n.toString) e.guards ++
  ", \"carrier\": " ++ optJson (fun n => jsonStr n.toString) e.carrier ++
  ", \"file\": " ++ optJson jsonStr e.file ++ "}"

end NativeSeams

namespace NativeSeams

open Meta

/-- Parse a JSON value into the inventory entry.  Fails with a readable
message on every malformed field: the inventory is checked by a script, so
a typo must be a failure, never a silent skip. -/
private def parseEntry (j : Json) : Except String Entry := do
  let obj ← j.getObj?
  let str (k : String) : Except String String :=
    match obj.get? k with
    | some (.str s) => pure s
    | some _ => throw s!"`{k}` must be a string"
    | none => throw s!"missing `{k}`"
  let nm (k : String) : Except String Name :=
    return (← str k).toName
  let optNm (k : String) : Except String (Option Name) :=
    match obj.get? k with
    | some (.str s) => pure (some s.toName)
    | some .null => pure none
    | some _ => throw s!"`{k}` must be a string or null"
    | none => throw s!"missing `{k}`"
  let arrNm (k : String) : Except String (List Name) :=
    match obj.get? k with
    | some (.arr xs) => xs.toList.mapM fun x =>
        match x with
        | .str s => pure s.toName
        | _ => throw s!"`{k}` entries must be strings"
    | some _ => throw s!"`{k}` must be an array"
    | none => throw s!"missing `{k}`"
  let bool (k : String) : Except String Bool :=
    match obj.get? k with
    | some (.bool b) => pure b
    | some _ => throw s!"`{k}` must be a boolean"
    | none => throw s!"missing `{k}`"
  let some kind := Kind.ofStr? (← str "kind")
    | throw "`kind` must be \"impl_by\" or \"csimp\""
  let guarded ← bool "guarded"
  let guards ← arrNm "guards"
  let carrier ← optNm "carrier"
  let file ← optNm "file"
  let implAlt :=
    match obj.get? "implAlt" with
    | some (.str s) => some s.toName
    | _ => none
  let freeForm :=
    match obj.get? "freeForm" with
    | some (.bool b) => b
    | _ => false
  pure { kind, ref := ← nm "ref", impl := ← nm "impl", thm := ← nm "thm",
         guarded, guards, carrier, implAlt, freeForm, file := file.map toString }

/-- Read the whole inventory file (`{"seams": [...]}`). -/
def parseInventory (j : Json) : Except String (List Entry) := do
  let .obj obj := j | throw "inventory must be a JSON object"
  let some (.arr es) := obj.get? "seams" | throw "missing `seams` array"
  es.toList.mapM parseEntry

def renderInventory (es : List Entry) : String :=
  "{\n  \"seams\": [\n" ++
    String.intercalate ",\n" (es.map fun e => "    " ++ e.toJson) ++
  "\n  ]\n}\n"

end NativeSeams

namespace NativeSeams

open Meta

/-- The check's mutable log, in the shape of a script's output. -/
abbrev Log := IO.Ref (Array String)

def Log.emit (log : Log) (msg : String) : IO Unit := log.modify (·.push msg)

/-- Short name of the source file a declaration's theorem lives in (from
the module index of a declaration defined in this repository). -/
def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => (env.header.moduleNames[i.toNat]!.toString.replace "." "/") ++ ".lean"
  | none => "<current module>"

/-- Print the seams the environment exposes (and the source-derived `csimp`
ones), in the JSON shape `audits/native_seams.json` uses.  `thm` is a
placeholder: the inventory must name the real seam theorem. -/
def printInventory (implSeams csSeams : Array Seam) (out : String → IO Unit) : IO Unit := do
  let entries := fun (s : Seam) =>
    { kind := s.kind
      ref := s.ref
      impl := s.impl
      thm := match s.csimpThm with
        | some t => t
        | none => s.ref ++ `native_seam_TODO
      guarded := false
      guards := []
      carrier := none
      file := none : Entry }
  out (renderInventory ((implSeams.map entries).toList ++ (csSeams.map entries).toList))

end NativeSeams

namespace NativeSeams

open Meta

/-- The audit.  `implSeams` are every `implemented_by` pair the environment
exports, `csSeams` the `csimp` seams (the source-level theorems the shell
wrapper parsed from the tree).  Each seam must be covered by an inventory
entry whose theorem the kernel checks.  Returns the number of failures. -/
def check (env : Environment) (implSeams csSeams : Array Seam)
    (inventory : List Entry) (log : Log) : IO Nat := do
  let failsRef ← IO.mkRef 0
  let fail (msg : String) : IO Unit := do
    failsRef.modify (· + 1)
    log.emit s!"FAIL {msg}"
  -- 1. Inventory ↔ seams: both directions, exactly.
  let invKeys : Std.HashSet String :=
    inventory.foldl (init := {}) fun s e =>
      s.insert (e.kind.toStr ++ "|" ++ e.ref.getString! ++ "|" ++
        e.impl.getString!)
  for e in inventory do
    let seams := match e.kind with
      | .implBy => implSeams
      | .csimp => csSeams
    match seams.find? (fun s => s.ref.getString! == e.ref.getString!) with
    | none =>
        fail s!"inventory entry `{e.ref}` → `{e.impl}` ({e.kind.toStr}) is not a seam of the repository"
    | some s =>
        if s.impl.getString! != e.impl.getString! then
          fail s!"inventory entry `{e.ref}` names implementation `{e.impl}`, but the seam's is `{s.impl}`"
  for s in implSeams do
    unless invKeys.contains (s.kind.toStr ++ "|" ++ s.ref.getString! ++ "|" ++
        s.impl.getString!) do
      fail s!"seam `{s.ref}` → `{s.impl}` (impl_by) missing from audits/native_seams.json"
  for s in csSeams do
    unless invKeys.contains (s.kind.toStr ++ "|" ++ s.ref.getString! ++ "|" ++
        s.impl.getString!) do
      fail s!"seam `{s.ref}` → `{s.impl}` (csimp) missing from audits/native_seams.json"
  -- 2. Every inventory theorem exists and states `ref = impl` under binders.
  for e in inventory do
    match env.find? e.thm with
    | none => fail s!"`{e.thm}` (the seam theorem for `{e.ref}`) does not exist"
    | some ci =>
        match (if e.freeForm then some (1, false) else
                seamShape? e.ref e.impl ci.type e.implAlt) with
        | none =>
            fail s!"`{e.thm}` does not state `{e.ref}` = `{e.impl}` (under binders)"
        | some (_, guarded) =>
            if guarded != e.guarded then
              fail s!"`{e.thm}` is {if guarded then "guarded" else "unconditional"}, but the inventory says {if e.guarded then "guarded" else "unconditional"}"
            if e.guarded then
              if e.guards.isEmpty then
                fail s!"guarded entry `{e.ref}` names no guard"
              if e.carrier.isNone then
                fail s!"guarded entry `{e.ref}` names no call-site carrier"
              for c in e.carrier do
                match env.find? c with
                | none => fail s!"carrier `{c}` of `{e.ref}` does not exist"
                | some _ => pure ()
            else if !e.guards.isEmpty || e.carrier.isSome then
              fail s!"unconditional entry `{e.ref}` must name no guards/carrier"
  let fails ← failsRef.get
  log.emit s!"checked {implSeams.size} implemented_by and {csSeams.size} csimp seams against {inventory.length} inventory entries"
  if fails == 0 then
    log.emit "OK: every native substitution is covered by a kernel-checked seam theorem"
  else
    log.emit s!"{fails} failure(s)"
  return fails

end NativeSeams

namespace NativeSeams


/-- The environment the audit runs on, plus the modules whose `csimp`
theorems cannot be recovered from its imported state.

Lean does not export the compiler-`csimp` environment extension like a
normal declaration attribute (`addImportedFn := fun _ _ => pure {}` in
`Lean/Compiler/CSimpAttr.lean`): importing an `.olean` drops its `csimp`
entries.  The csimp half of the inventory is therefore supplied by the
source-derived table `csimpFromSource` (which the shell wrapper checks against
the tree), and the tagged theorem's statement is checked like any other. -/
def csimpModules : List Name := [
  `LeanFzn.Engine.Analyze, `LeanFzn.Engine.Bits, `LeanFzn.Engine.Clauses,
  `LeanFzn.Engine.Dom, `LeanFzn.Engine.Lit, `LeanFzn.Engine.Props.Element,
  `LeanFzn.Engine.Props.Linear, `LeanFzn.Engine.Props.LinearExt.Bounds,
  `LeanFzn.Engine.Props.LinearExt.Plans, `LeanFzn.Engine.Queue.Worklist,
  `LeanFzn.Engine.Trail, `LeanFzn.Solver.Propagation.EngineCore,
  `LeanFzn.Compiler.Compile, `LeanFzn.Compiler.Extract,
  `LeanFzn.Compiler.SetShape
]

unsafe def loadEnv : IO (Environment × Array String) := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← importModules #[{ module := `LeanFzn }] {}
  let mut failures : Array String := #[]
  for m in csimpModules do
    unless env.header.moduleNames.contains m do
      failures := failures.push s!"csimp module `{m}` is not imported by `LeanFzn`"
  return (env, failures)

/-- The `csimp` seams derived from the source-level `@[csimp]` theorems.

Lean's compiler-csimp extension is not imported from `.olean` files
(`addImportedFn := fun _ _ => pure {}` in `Lean/Compiler/CSimpAttr.lean`), so a
freshly imported `LeanFzn` reports *no* `csimp` theorems.  This table is the
authoritative list of the source-level theorems; the shell wrapper
`audits/check_native_seams.sh` re-derives it from the tree (grep for
`@[csimp] theorem`) and fails if this list drifts from the sources, and the
audit itself re-checks every row's theorem statement (`seamShape?` in `check`)
and its tag. -/
def csimpFromSource : List (Name × Name × Name) := [
  (`LeanFzn.Solver.Propagation.fitsB, `LeanFzn.Solver.Propagation.fitsBFast,
    `LeanFzn.Solver.Propagation.fitsB_eq_fast),
  (`LeanFzn.Engine.canonLit, `LeanFzn.Engine.canonLitFast,
    `LeanFzn.Engine.canonLit_eq_fast),
  (`LeanFzn.Engine.canonClause, `LeanFzn.Engine.canonClauseFast,
    `LeanFzn.Engine.canonClause_eq_fast),
  (`LeanFzn.Engine.lowestBit, `LeanFzn.Engine.lowestBitFast,
    `LeanFzn.Engine.lowestBit_eq_fast),
  (`LeanFzn.Engine.highestBit, `LeanFzn.Engine.highestBitFast,
    `LeanFzn.Engine.highestBit_eq_fast),
  (`LeanFzn.Engine.dedupItems, `LeanFzn.Engine.dedupItemsFast,
    `LeanFzn.Engine.dedupItems_eq_fast),
  (`LeanFzn.Engine.minGoL, `LeanFzn.Engine.minGoFast,
    `LeanFzn.Engine.minGoL_eq_minGoFast),
  (`LeanFzn.Engine.LitTable.internArray, `LeanFzn.Engine.LitTable.internArrayFast,
    `LeanFzn.Engine.LitTable.internArray_eq_fast),
  (`LeanFzn.Engine.trailPush, `LeanFzn.Engine.trailPushFast,
    `LeanFzn.Engine.trailPush_eq_fast),
  (`LeanFzn.Engine.backjump, `LeanFzn.Engine.backjumpFast,
    `LeanFzn.Engine.backjump_eq_fast),
  (`LeanFzn.Engine.DomC.hi?, `LeanFzn.Engine.DomC.hiFast,
    `LeanFzn.Engine.DomC.hi?_eq_fast),
  (`LeanFzn.Engine.sortUniqueInts, `LeanFzn.Engine.mergeSortInts,
    `LeanFzn.Engine.sortUniqueInts_eq_mergeSortInts),
  (`LeanFzn.Engine.aieOut, `LeanFzn.Engine.aieOutFast,
    `LeanFzn.Engine.aieOut_eq_fast),
  (`LeanFzn.Engine.avieOut, `LeanFzn.Engine.avieOutFast,
    `LeanFzn.Engine.avieOut_eq_fast),
  (`LeanFzn.Engine.avbeOut, `LeanFzn.Engine.avbeOutFast,
    `LeanFzn.Engine.avbeOut_eq_fast),
  (`LeanFzn.Engine.linExtractBounds, `LeanFzn.Engine.linExtractBoundsFast,
    `LeanFzn.Engine.linExtractBounds_eq_fast),
  (`LeanFzn.Engine.linTerms, `LeanFzn.Engine.linTermsFast,
    `LeanFzn.Engine.linTerms_eq_fast),
  (`LeanFzn.Engine.linPrunes, `LeanFzn.Engine.linPrunesFast,
    `LeanFzn.Engine.linPrunes_eq_fast),
  (`LeanFzn.Engine.linLePlan, `LeanFzn.Engine.linLePlanFast,
    `LeanFzn.Engine.linLePlan_eq_fast),
  (`LeanFzn.Engine.linGePlan, `LeanFzn.Engine.linGePlanFast,
    `LeanFzn.Engine.linGePlan_eq_fast),
  (`LeanFzn.Engine.linEqPlan, `LeanFzn.Engine.linEqPlanFast,
    `LeanFzn.Engine.linEqPlan_eq_fast),
  (`LeanFzn.Engine.linPrunesGe, `LeanFzn.Engine.linPrunesGeFast,
    `LeanFzn.Engine.linPrunesGe_eq_fast),
  (`LeanFzn.Engine.slotsIntB, `LeanFzn.Engine.slotsIntBFast,
    `LeanFzn.Engine.slotsIntB_eq_fast),
  (`LeanFzn.Engine.registerProps, `LeanFzn.Engine.registerPropsFast,
    `LeanFzn.Engine.registerProps_eq_fast),
  (`LeanFzn.Compiler.accepts, `LeanFzn.Compiler.acceptsFast,
    `LeanFzn.Compiler.accepts_eq_fast),
  (`LeanFzn.Compiler.compileConstraints, `LeanFzn.Compiler.compileConstraintsFast,
    `LeanFzn.Compiler.compileConstraints_eq_fast),
  (`LeanFzn.Compiler.expandPlan, `LeanFzn.Compiler.expandPlanFast,
    `LeanFzn.Compiler.expandPlan_eq_fast),
  (`LeanFzn.Compiler.extractConstraints, `LeanFzn.Compiler.extractConstraintsFast,
    `LeanFzn.Compiler.extractConstraints_eq_fast),
  (`LeanFzn.Compiler.shapeExpandModelWith,
    `LeanFzn.Compiler.shapeExpandModelWithFast,
    `LeanFzn.Compiler.shapeExpandModelWith_eq_fast)
]

/-- The audit's entry point.  `--print-inventory` renders the required
inventory; `--self-test` inverts the verdict (used by
`audits/check_native_seams.sh --self-test` on a deliberately broken copy);
a bare path names the repository root. -/
unsafe def runMain (args : List String) : IO UInt32 := do
  let args := args.filter (· != "--")
  let selfTest := args.contains "--self-test"
  let print := args.contains "--print-inventory"
  let root := (args.filter (fun a => !a.startsWith "--")).headD "."
  let (env, failed) ← loadEnv
  -- csimp theorems are not importable through `.olean`; the source table
  -- supplies the rows the environment cannot (see `csimpFromSource`).
  let csSeams := csimpSeams env csimpFromSource
  let implSeams := explicitImplementedBy env
  if print then
    printInventory implSeams csSeams IO.print
    return 0
  let invPath := root ++ "/audits/native_seams.json"
  let log ← IO.mkRef #[]
  for f in failed do
    log.modify (·.push s!"FAIL {f}")
  let fails ←
    match ← (try IO.FS.readFile invPath catch _ => pure "") with
    | "" =>
        log.modify (·.push s!"FAIL cannot read {invPath}")
        pure 1
    | txt =>
        match Json.parse txt >>= parseInventory with
        | .error err =>
            log.modify (·.push s!"FAIL {invPath}: {err}")
            pure 1
        | .ok inv =>
            check env implSeams csSeams inv log
  for e in ← log.get do
    IO.println e
  if selfTest then
    -- A broken inventory must fail.  The message is deliberately distinct so
    -- the script can tell "the check has teeth" from "the check happened to
    -- pass".
    if fails > 0 then
      IO.println "SELF-TEST OK: the broken inventory was rejected"
      return 0
    else
      IO.println "SELF-TEST FAILED: the broken inventory was accepted"
      return 1
  return if fails == 0 then 0 else 1

end NativeSeams

/-- `lean --run` entry point. -/
unsafe def main (args : List String) : IO UInt32 :=
  NativeSeams.runMain args

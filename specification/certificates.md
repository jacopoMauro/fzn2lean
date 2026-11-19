# Exportable UNSAT and optimality certificates — design (Phase A)

Status: **design only**. This document specifies what an exportable proof
artifact for LeanFzn would be, what would have to be trusted to check one,
and which of two competing designs the project should adopt. It introduces no
code, no CLI flag, no axiom and no gate. Section 12 lists what a later
implementation phase (Phase B) would have to build.

## 0. Scope and non-goals

In scope:

* the trusted core of the solver as it stands (the Lean kernel, the
  LLVM-compiled `leanfzn` binary, and the `@[csimp]`/`@[implemented_by]`
  substitutions that make the compiled binary differ from the kernel
  definitions), and
* how an UNSAT answer, and an optimality answer for `solve minimize|maximize`,
  can be re-checked by a small program that trusts none of the above.

Out of scope: changing the solver, adding a `--proof-log` flag, writing a
checker, a PB format, or a VeriPB adapter. Also out of scope are
re-checking SAT answers (the verified solution checker
`checkSemanticModelSolution` already covers them) and certificates for models
outside the certified fragment.

## 1. What has to be certified, precisely

### 1.1 The compiled problem

`CompiledProblem DomConstraint` (`LeanFzn/Compiler/Types.lean:37`) extends the
shared `Core.Problem C Unit` with the `source : Model`, the store
reconstruction `toStore : Assignment → Store`, and the domain mirror
`domainsArray`/`domainsArray_to_list`. The constraint language is the payload
type `C`; the solver layer instantiates it with `DomConstraint`.
Concretely a compiled problem is

* `names : List String` (slot names, including aux slots),
* `domains : List Domain` (one finite domain per slot),
* `constraints : List DomConstraint` (`LeanFzn/Compiler/Types.lean:37-49`),
* `objective : Unit` (the solver payload is unused; the optimization front end
  keeps the objective in `ObjectiveSpec`, `LeanFzn/Compiler/Objective.lean:39`).

The meanings the certificate has to be checked against are
`allAssigns p.domains` (the box) and `accepts p` — `accepts` is
`problem.constraints.all fun c => c.satisfiedB assignment`
(`LeanFzn/Compiler/Compile.lean:90-92`), and `satisfiedB_iff` ties
`DomConstraint.satisfiedB` (`Repr.lean:371`) to the declarative
`DomConstraint.SatisfiedBy`
(`LeanFzn/Solver/Propagation/DomainConstraints/Repr.lean:253-…`).

So the two statements to certify are exactly:

* **UNSAT**: `∀ b ∈ allAssigns p.domains, accepts p b = false`
  (`LeanFzn/Engine/Search.lean:2306` `search_unsat`, and
  `coreSolve_unsat` at `LeanFzn/Engine/Search.lean:2755`).
* **Optimality**: for a returned `a` with objective value `v`, `a` is
  accepted and *no* accepted box member reads a strictly better value, i.e.
  `∀ b ∈ allAssigns p.domains, accepts (p.addConstraint (spec.improveBound v)) b = false`
  (`compileOpt_optimal`, `LeanFzn/Compiler/Proofs/Objective.lean:201-208`).

Note what is *not* in either statement: no reachability of any solver state,
no claim about propagation strength, no claim about the search order. A
certificate need only justify the two `∀ b` statements above; everything else
in the solver is an optimisation device.

### 1.2 The literal language

The engine reasons over signed atoms `Literal = ⟨atom, positive⟩`
(`LeanFzn/Solver/Propagation/Types.lean:24-39`) where
`Atom = boolEq slot b | intLe slot k | intNe slot k`. `atomSlot` reads the
slot (`LeanFzn/Engine/Lit.lean:47-51`). This is the only vocabulary a
certificate check needs: an `int` slot's domain can be described completely
by bound literals (`intLe slot k` / its negation `¬(slot ≤ k)` = `slot > k`),
a Boolean slot by `boolEq slot b`, and a sparse/holed domain by repeating
`intLe`/`intNe` literals (§11). The engine already uses exactly this
vocabulary for explanations (`LeanFzn/Solver/Propagation/Propagate.lean:1-20`).

### 1.3 Sizes

"Trace size" below means the ordered stream a checker would have to read. The
details are fixed per option in §4 and §5; the magnitude is measured in §8.

## 2. The compiled constraint families and their encodings

`DomConstraint` has the constructors listed at
`LeanFzn/Solver/Propagation/DomainConstraints/Repr.lean:70-235`. Every
constructor the compiler can emit must get an encoding. The compiler's
accepted surface is the 21 extracted shapes plus the aux-slot expansions of
`LeanFzn/Compiler/Compile.lean:1-70`, so the encodings below cover the closure
of what can reach `p.constraints`:

| `DomConstraint` constructor | source shape(s) | PB rows (over slot literals) | count |
| --- | --- | --- | --- |
| `constEq i v` | `int_eq(x,k)`, `bool_not` literals, aux pins | `v = Σ_{w∈D_i} w·x_{i,w}` (one equality) | 1 |
| `eqSlot i j` | `int_eq(x,y)`, `bool_eq` | `∀ w: x_{i,w} = x_{j,w}` over the intersection; plus the "value present in both" indicator equalities | \|D_i ∪ D_j\| equalities |
| `neSlot i j` | `int_ne(x,y)` | `x_{i,w} + x_{j,w} ≤ 1` for each common `w` | \|D_i ∩ D_j\| inequalities |
| `leSlot i j`, `ltSlot i j` | `int_le/int_lt(x,y)` | per-threshold: `x_{j,≤k} ≤ x_{i,≤k}` (resp. `x_{j,≤k} ≤ x_{i,≤k-1}`) for `k` in the relevant bound set | O(\|D\|) inequalities |
| `leConstHi/Lo`, `ltConstHi/Lo` | `int_le/lt` with a literal | one threshold row per affected value, or a single `≤` row over `Σ w·x` | 1–O(\|D\|) |
| `plusSlot i j k` | `int_plus`, the `[1,1]x+[1,1]y=k` rewrite | mixed-radix booleanisation of `x+y=z` (`O(\|D_i‖D_j\|)` auxiliary bits) | O(D²) |
| `timesSlot i j k` | `int_times` (all aux shapes) | product-support rows `x_{i,a}+x_{j,b}+x_{k,ab} ≥ 2` for each falsified triple (support encoding) | O(\|D_i‖D_j\|) |
| `minSlot/maxSlot i j k` | `int_min/max` incl. the literal-result rewrites | `z = min(x,y)` needs 3 rows per value pair (or per threshold) | O(D²) or O(D) threshold rows |
| `absSlot i k` | `int_abs` | 2 rows per value (`x_{i,±a}` ⇒ `x_{k,|a|}`), plus the reverse | O(\|D\|) |
| `allDiff is` | `all_different` | `x_{i,w} + x_{j,w} ≤ 1` for every pair and value | O(n²·D) |
| `linEq/linLe/linNe coeffs is b` | `int_lin_eq/le/ne` | pseudo-Boolean rows over the `x_{i,w}` bits (`Σ c_i·Σ w·x_{i,w} = / ≤ / ≠ b`); `≠` needs one row per side of the disjunction with a selector bit | 1 (eq/le), 2+ (ne) |
| `boolNotSlot i j` | `bool_not` | `x_{i,T} = x_{j,F}`, `x_{i,F} = x_{j,T}` | 2 |
| `boolAndSlot/boolOrSlot i j k` | `bool_and/or` | 4 truth-table rows each | 4 |
| `boolClauseSlot ps ns` | `bool_clause` | one clause row: `∨ ps ∨ ¬ns` | 1 |
| `arrayBoolAndSlot is k` | `array_bool_and` | 1 row per operand + 1 | \|is\|+1 |
| `bool2intSlot i k` | `bool2int` | `k = x_{i,T}` (a 0/1 channel equality) | 1 |
| `boolEqSlot i j` | `bool_eq` | 2 rows | 2 |
| `arrayIntElementSlot xs i k` | `array_int_element` | one implication per table position `x_{i,p} ⇒ x_{k,xs[p]}` plus a range row excluding out-of-range indices | \|xs\|+1 |
| `arrayVarIntElementSlot is i k` | `array_var_int_element` | per position `p`: `x_{i,p} ⇒ (x_{k,w} = x_{is[p],w})` for all `w` (equality-by-value channels) | O(\|is‖D\|) |
| `arrayVarBoolElementSlot is i k` | `array_var_bool_element` | the Boolean twin | O(\|is\|) |
| `eqReifSlot/leReifSlot/neReifSlot i j r` | `int_eq/le/ne_reif` | reification: the "R ⇔ φ" rows, 2–4 rows each | O(1) |
| `linEqReif/linLeReif/linNeReif` | `int_lin_*_reif` | reification of the PB row(s) with the selector bit | O(1) per row |
| `maxGen/minGen/divGen/modGen/minPair/maxPair` | `array_int_maximum/minimum`, `int_div/mod`, general `int_min/max` | table/support encodings; `div`/`mod` need a full multiplication-table relation per operand pair | O(D²) |
| `setInSlot i s`, `setInReifSlot i s r` | `set_in`, `set_in_reif` | a domain restriction: drop `x_{i,w}` for `w ∉ s` (a fixing row per excluded value), or one `Σ_{w∈s} x_{i,w} = 1` row | \|D_i \ s\| or 1 |

Two observations that matter for the comparison:

* **Domains are where the Boolean bits come from.** The PB encoding is only
  finite because every compiled domain is finite, and every `DomConstraint`
  is either a relation over a few slots (`eqSlot`, `leSlot`, …), a
  value-level relation (`allDiff`, elements), or a PB row (`linEq/linLe/ne`).
  So a value-based Booleanisation is the natural encoding; bound-based
  (order) encodings exist but only help the `le`/`lt` families.
* **The aux slots are real slots.** `expandPlan` (`LeanFzn/Compiler/Compile.lean:1223-1244`)
  appends pinned singleton slots to the slot list and rewrites literal
  arguments as already-certified shapes over them. An encoding therefore never
  needs to know about "literal arguments": `constEq aux k` handles them, and
  the aux slots are ordinary one-value slots in `allAssigns`. That is a large
  simplification for a PB encoding, and it is why the compiler's proof of
  `compileFull_exact` can be reused unchanged.

### 2.1 What is still needed after the encoding: the exactness bridge

An encoded problem is a *different* object from the compiled one. The bridge
is a theorem of the form

```
encodedAccept p enc(x) ↔ accepts p x            (x an assignment of the slots)
encodedBox p  ↔ allAssigns p.domains
```

The project already proves statements of exactly this shape for its own
intermediate representations: `compileFull_exact`
(`LeanFzn/Compiler/Proofs/Normalize.lean:2967`) says an accepted
`allAssigns` member maps to a `Satisfies` store, and the per-family
`Proofs/Exact.lean` (17k lines) proves source-predicate ↔ `DomConstraint`
equivalences. A PB encoding would need its own such bridge, per constructor,
roughly the size of `Compiler/Proofs/Exact.lean` (§6).

## 3. How the solver actually justifies a deduction

This is needed for **both** options: a trace checker has to validate each
step, and a VeriPB proof has to be *derived* from the same steps.

### 3.1 Reasons are entailed clauses

The engine's only soundness carrier is `EClause`
(`LeanFzn/Engine/Types.lean:176-180`): an array of packed literals plus a
field `ent : Entailed p (T.decodeClause lits)`, where
`Entailed p c := ∀ b ∈ allAssigns p.domains, accepts p b = true → c.SatisfiedBy b`
(`LeanFzn/Engine/Types.lean:169-172`). Every propagated literal, every
conflict and every learned clause is an `EClause`.

### 3.2 The propagator contract

A propagator is `PropV2` (`LeanFzn/Engine/Types.lean:192-197`):
`run : EngineView → PropOut`, with `PropOut.prune (Array (PLit × EClause))`
(one reason clause per pruned literal) and `PropOut.conflict (EClause)`.

The contract a trace checker can rely on is `PropV2.PruneSound`
(`LeanFzn/Engine/Proofs/PruneSound.lean:39-44`):

* the pruned literal is **unassigned** in the view,
* every **other** literal of the emitted reason clause is **false** in the
  view.

Together with `EClause.ent` this is exactly a "unit-consequence" step: the
problem entails the reason clause, the clause is unit under the current
literals, so the target literal is a consequence. A trace checker does not
need the propagator's internals: it needs the reason clause, and it can check
both conditions itself against the current assignment.

The static side — "every propagator in the table is prune-sound" — is
`PropsSound p T props` (`LeanFzn/Engine/Proofs/PruneSound.lean:56-58`), and
the per-family proofs are collected there (`plusPropWith_pruneSound`, …) and
instantiated by `propsOf_pruneSound` (`LeanFzn/Engine/Search.lean:378`).

### 3.3 Trail entries and decision levels

`Entry` (`LeanFzn/Engine/Types.lean:129-136`) carries `lit`, `level`,
`reason : ReasonRef` (`decision | learned id | reason id`) and the undo image
`prev`. `reasonClause?` (`LeanFzn/Engine/Clauses.lean:866`) maps a
`ReasonRef` to its `EClause`. Levels are needed only for learning and
backjumping; for a checker they matter in one way: a **decision** literal is
unjustified but *chosen* by the solver, so it must appear in the trace as an
explicit "the following case split is exhaustive" step, and a **root
refutation** must not contain decisions at all.

### 3.4 Conflict analysis

`analyze` (`LeanFzn/Engine/Analyze.lean:4096`) computes a first-UIP learned
clause over `CItem`s (`LeanFzn/Engine/Analyze.lean:42-50`). It is *already*
self-checking: every item records `pos` (the trail position whose undo image
first falsifies the literal) and `level`, and the analysis only accepts a
resolution step whose hints check out at runtime (`initSlotOKB`, `domFalseB`,
`itemCheckB`, `slotKindOKB`, `sortedB`, `slotObsB`, header of
`Analyze.lean:1-21`). Any doubt returns `ok = false` and `learned = none`.

The exported facts a certificate layer can reuse:

* `explainLit_spec` (`LeanFzn/Engine/Analyze.lean:462`): the produced item
  really explains falsity at the recorded position;
* `resolveWith_entailed` (`LeanFzn/Engine/Analyze.lean:2046`) and
  `chainReasonLits_entailed` (`LeanFzn/Engine/Analyze.lean:1138`): resolution
  of two entailed clauses stays entailed;
* `analyze_sound` (`LeanFzn/Engine/Analyze.lean:4143`): a successful
  `analyze` returns a clause that is `Entailed p`;
* `analyze_empty_unsat` (`LeanFzn/Engine/Analyze.lean:4197`): an empty learned
  clause proves `Entailed p []`, i.e. UNSAT;
* `analyze_asserting_mem` (`LeanFzn/Engine/Analyze.lean:4215`): the asserting
  literal is in the learned clause.

So the *justification format* for a learned clause is already fixed by the
engine: an item list, each item being (literal, trail position, level). That
is exactly the "hints" of a project-specific trace (§5), and it is also
enough to emit a resolution proof of the learned clause from the reason
clauses (§4.4).

### 3.5 Propagation at the root

Entry runs `addSeedClauses` then `propagateUnits` (`coreSolveFrom`,
`LeanFzn/Engine/Search.lean:2449-2530`). Seed clauses are the original
Boolean clauses of `boolClauseSlot` constraints, one per constraint
(`seedClauses`, `LeanFzn/Compiler/SeedClauses.lean:42`) and are entailed by
the leaf semantics (`seedClauses_mem_inv`, same file). A root unit
propagation is a sequence of clause steps with no decisions, so it is a
"clause-only" prefix in both designs.

### 3.6 Why the trace is a suffix of the CDCL run

The final `search` (`LeanFzn/Engine/Search.lean:1879`, soundness section at
`:2136`) has four leaves:
conflict (learn, backjump, or refute), decision, fixed-assignment check,
no-slot. Its soundness (`search_unsat`, `LeanFzn/Engine/Search.lean:2306`,
`search_sat` at 2275) is the statement a checker reproduces. Learning,
backjumping, restarts, reductions and activity are all *skipped* in the
soundness proof — the analysis of §3.4 is used only to justify the learned
clause and the refutation. This is the key structural fact for both options:
**a certificate is a stream of justification steps, not a replay of the
search policy.** Restarts, reductions (`LeanFzn/Engine/Reduce.lean:1-20`:
deletion loses propagation strength, never a proof), activity scores and the
portfolio are all invisible to the claim.

## 4. Option (a) — VeriPB proof logging over a PB encoding

### 4.1 Shape of the artifact

A VeriPB proof is emitted by the *solver*, in the sense of a proof log
produced during search, against a PB input file. Here the PB input would be
the *encoded compiled problem* (§2), not the source `.fzn`. The certificate
consumer runs VeriPB's checker on (PB rows, proof) and gets "infeasible" or a
refutation; no Lean code runs on the consumer's side.

### 4.2 What the encoding costs

The PB encoding is the table of §2. Its main properties:

* sizes are dominated by value Booleanisation: `allDiff` is `O(n²·D)`,
  `element` families `O(\|is‖D\|)`, products/min over value pairs `O(D²)`.
  On the measured `csplib12-gbac` model (§8) the compiled problem has 792
  reified equalities and 65/50 linear rows, so value Booleanisation would be
  large but flat.
* the encoding introduces **new Boolean variables** for values, and the
  solver's literals (`intLe`, `intNe`, `boolEq`) are *not* those variables.
  A proof log must therefore translate every engine step into the encoding's
  vocabulary: `intLe s k` becomes `Σ_{w≤k} x_{s,w}` being 1, `intNe s k`
  becomes `Σ_{w≠k} x_{s,w}` being 1, and so on.
* every `DomConstraint` family needs an encoded-correctness proof (§2.1) and
  a translation lemma for its propagator's reason clauses.

### 4.3 What a VeriPB step would be

VeriPB proofs are resolution/pseudo-Boolean derivations: the propagator's
reason clauses can be *added* (they are PB consequences of the encoding, by
§2.1 + §3.2), and unit propagation on the encoded formula yields the
deduction. Conflict analysis is resolution, which VeriPB natively supports.
So conceptually everything fits — the work is in the translation.

### 4.4 The honest problem: translating hints, not finding them

The engine does not record *which* reason clause justified *which* literal of
a learned clause; it records `CItem`s (literal, position, level). To emit a
VeriPB resolution proof of the learned clause, a Phase B implementation has to
recompute the resolution chain from the items and the reason clauses
(`chainReasonLits`, `LeanFzn/Engine/Analyze.lean:906`) and then map every
reason clause through the encoding translation. `resolveWith_entailed`
guarantees the Lean-level chain is a valid resolution; the encoding direction
is the extra step. That is an `O(items × reason size)` step per learned
clause, and it is exactly the step that a *native* checker can skip (§5).

### 4.5 Trust base

If option (a) is adopted, the answer "UNSAT"/"optimal" depends on:

1. VeriPB's checker being correct;
2. the PB input file being the correct encoding of *this* compiled problem —
   i.e. an unproved (or separately proved, §2.1) encoding translator;
3. the proof log translation being faithful (each reason clause really
   translated, each step really a VeriPB derivation);
4. the compiled problem being the correct compilation of the `.fzn` — a
   separate, already-proved statement (`compileFull_exact`) *if* the encoding
   translator consumes `CompiledProblem`; if it consumes the `.fzn` directly,
   the whole compiler correctness story is trusted instead.

Note that (4) moves: if the VeriPB input is generated from the *source* model
by a translator outside Lean — the cheap route — then the Lean compiler proofs
are bypassed and *the encoding becomes the trusted artifact*. That is a
weaker position than the project's current one, where the compiler is proved.

## 5. Option (b) — a project-specific trace with a small Lean checker

### 5.1 Shape of the artifact

The artifact is a stream of *justification steps* in the engine's own
vocabulary (slots, `Literal`s, levels, reason clauses), with no encoding
translation. It has:

```
header:   the compiled problem (names, domains, constraints) or its hash
          + the objective (slot, direction), if minimization/maximization
step:     decide  slot level (a declared, exhaustive case split)
        | propagate slot literal (reason clause: literals + level hints)
        | learn  clause (item list: literal, trail position, level)
        | conflict clause (item list)
        | bound  b        (optimization: the current incumbent value)
end:      refute (no decision above the last bound) | optimum v (last bound)
```

Two design decisions are load-bearing and both are already forced by the
existing code:

* **The learned-clause justification is the item list** of §3.4, i.e. exactly
  what `analyze` produces. The checker's job is `analyze_sound`'s statement:
  "the item list, resolved against the recorded reason clauses, yields an
  entailed clause".
* **The propagate step is `PruneSound`**: the checker verifies (i) the reason
  clause is entailed — by induction over the learned clauses already checked —
  and (ii) the reason's other literals are false under the current
  assignment, and the target is unassigned. This is a direct, a-priori
  verification of the two conditions in `PropsSound`; the checker never needs
  to know a propagator's name.

### 5.2 How `accepts` is recovered

The checker starts from `init (root domains)` and applies steps. Its final
claim `∀ b ∈ allAssigns p.domains, accepts p b = false` is proved by the same
argument as `search_unsat` (`LeanFzn/Engine/Search.lean:2306`): the only leaf
is an entailed empty clause, and `entailed_nil_unsat`
(`LeanFzn/Engine/Lit.lean`, §3.4). No step depends on a propagator being
complete, so a trace can be produced by *any* pruning policy — including the
current one, or a weaker one.

This is the project's key advantage over (a): the checker's soundness
theorem is stated against `accepts`, i.e. the very predicate `search_unsat`
and `compileFull_exact` already speak about. A proved checker
`checkTrace : Trace → Bool` with

```
checkTrace p tr = true → ∀ b ∈ allAssigns p.domains, accepts p b = false
```

is a theorem of the *same shape* as `coreSolve_unsat` and would reuse the
existing `Lit`/`Clauses`/`Analyze` lemmas (§3) rather than a new translation
layer. Phase A does not claim that theorem exists; it claims the statement is
the right one, and the ingredients for it are all published.

### 5.3 Size

Per conflict, the trace holds the learned clause (≈ `learnedLitsAfter`
literals, §8) plus an item list (two `Nat`s per literal: trail position and
level). Per propagation, one literal plus its reason clause (≈ its size) and
levels. No value Booleanisation, no encoding buffers. This is the smaller
artifact by construction: it is of the order of the solver's own proof
structures (`EClause`s + `CItem`s), whereas the PB encoding must additionally
carry the encoding of the whole problem (§2) and its translation.

### 5.4 Trust base

If option (b) is adopted, the answer depends on:

1. the Lean kernel (checking the single checker soundness proof);
2. the trace format and the checker program being the proved ones — i.e. the
   checker's compiled form must be tied to the proved definition. This is the
   `@[csimp]`/`@[implemented_by]` seam again (`audits/native_seams.json`), so
   the checker's own fast path must come with an equality theorem, or the
   checker must be shipped as a *ported, separately reviewed* program;
3. the compiled problem, i.e. `compileFull_exact` (already proved) —
   and *not* the compiled solver, not its propagators, not LLVM;
4. for optimality (§7): the claim "no accepted assignment beats `v`".

Note what disappears relative to (a): no encoding translator, no per-family
encoding-correctness proof, no PB semantics to trust. What remains is one
checker and one trace format.

## 6. The VeriPB maintenance load in this repository

A PB encoding is not just a file format; it is the closure of the table in §2,
which is exactly the closure the compiler proofs already enumerate (the 21
shapes + 34 aux shapes of `Compile.lean`). Two costs are worth stating
plainly:

* `Compiler/Proofs/Exact.lean` is 17k lines establishing
  source-predicate ↔ `DomConstraint` equivalence per family; the `SetShape`
  pair alone is ≈13k lines. A PB encoding whose correctness must be
  *proved* (rather than trusted) would need a comparable per-family
  development, because each family's PB rows are a different relation from
  the `DomConstraint` leaf.
* if instead the encoding is *trusted* (out-of-process translator), the
  project loses exactly the property it is built around: that the compiled
  problem is proved equivalent to the source model.

Option (b) has no such closure obligation: it never leaves the vocabulary in
which `accepts` is already defined.

## 7. Certifying optimality

Branch-and-bound is `optLoop`/`optLoopWith`
(`LeanFzn/Integration/Optimization/Basic.lean:236-`): solve, read `v`,
re-solve with `spec.improveBound v` added, repeat. `OptRun` records
`sols : List (List Value × Int)`, `complete`, `lastBound`
(`Basic.lean:232-236`). The objective is `(slot, dir)`
(`LeanFzn/Compiler/Objective.lean:39-42`) and the improving bound is
`leConstHi slot (v-1)` / `leConstLo slot (v+1)`
(`Objective.lean:62-66`).

`compileOpt_optimal` (`LeanFzn/Compiler/Proofs/Objective.lean:201-208`) says
exactly what a certificate must show:

> `a` is accepted, reads `v` at `spec.slot`, **and**
> `∀ b ∈ allAssigns p.domains, accepts (p.addConstraint (spec.improveBound v)) b = false`.

So the certificate for "v is optimal" is:

1. the SAT witness `a` (checked by the verified solution checker
   `checkSemanticModelSolution`, whose correctness is
   `checkSemanticModelSolution_correct` in `LeanFzn/Checker/Proofs/Check.lean:874`), and
2. an UNSAT certificate for the compiled problem with **one extra
   `DomConstraint`** — `leConstHi slot (v-1)` or `leConstLo slot (v+1)`.

That second part is an UNSAT certificate of exactly the §5 shape, over a
problem whose constraints list has one more row. Both options therefore
certify optimality as "UNSAT under the improving bound" without changing
their core. For option (a) the extra row is one more PB row; for option (b)
it is one more `DomConstraint` in the header. For an *optimality claim of the
last incumbent of a completed run* this is enough; the intermediate
incumbents do not need certificates (they are checked solutions).

The portfolio (`LeanFzn/Integration/Public/Driver.lean:112-260`, the
`PortfolioState`/`portfolioWorker` block) needs no
separate story: each worker's completed proof is an independent §7
certificate for the same bound, and "the portfolio's answer" is whichever
certificate the driver forwards. A checker checks that certificate; the
other workers' logs are discarded.

### 7.1 The existence half

`compileOpt_optimal` takes `a ∈ allAssigns` and `accepts p a`; a certificate
that only proves the bound infeasible proves "no better solution" but not
"`v` is attained". Both options must therefore pair the bound certificate
with the SAT witness — which is why the artifact is a *pair*.

## 8. Measurements

Run in `/tmp/wt/w9` (branch `w9/certificates`) with the prebuilt binary
`.lake/build/bin/leanfzn solve FILE --stats`, statistics line from
`EngineStats` (`LeanFzn/Engine/Types.lean:242-267`, printed by
`emitStats`, `LeanFzn/Integration/Public/Driver.lean:41`). **Measured**;
no figure below is extrapolated.

| fixture | result | decisions | conflicts | learned | learnedLitsBefore | learnedLitsAfter | propagations | reasonsTrimmed | source |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `int_ne_unsat` | UNSAT | 1 | 2 | 1 | 2 | 1 | 5 | 2 | `audits/benchmark_fixtures/int_ne_unsat.fzn` |
| `pigeon5_4` | UNSAT (root) | 0 | 1 | 0 | 0 | 0 | 0 | 0 | `audits/benchmark_fixtures/pigeon5_4.fzn` |
| `latin4` | SAT | 6 | 0 | 0 | 0 | 0 | 37 | 0 | `audits/benchmark_fixtures/latin4.fzn` |
| `reified_mix` | SAT | 2 | 0 | 0 | 0 | 0 | 4 | 0 | `audits/benchmark_fixtures/reified_mix.fzn` |
| `objective_sum` | 82 rounds | 161 | 1 | 0 | 0 | 0 | 370 | 0 | `audits/benchmark_fixtures/objective_sum.fzn` |
| `generated/pigeonhole_bool3` | UNSAT | 7 | 7 | 6 | 23 | 12 | 61 | 45 | `audits/benchmark_fixtures/generated/` |
| `generated/pigeonhole_bool4` | UNSAT | 69 | 42 | 41 | 313 | 168 | 443 | 386 | `audits/benchmark_fixtures/generated/` |
| `generated/gen_bool_dense40` | SAT | 42 | 36 | 36 | 369 | 198 | 852 | 782 | same |
| `generated/gen_bool_dense60` | SAT | 77 | 61 | 61 | 989 | 532 | 2381 | 2273 | same |
| `generated/latin5` | SAT | 10 | 0 | 0 | 0 | 0 | 78 | 0 | same |
| `generated/linear_chain_32` | SAT | 31 | 0 | 0 | 0 | 0 | 2 | 0 | same |
| `minizinc-challenge/2026fzn/gbac/csplib12-gbac.fzn` | SAT (106 rounds) | 59267 | 17137 | 17136 | 1300350 | 690837 | 1025211 | 658306 | challenge instance, 3.3 k lines, 1 723 constraints |

The two `minizinc-challenge/2026fzn` instances tried first —
`gbac/UD1-gbac.fzn` (2.1 MB) and `atp-stage2/instance1-stage2.fzn` — did not
finish within 120 s and are **not** reported as measurements.

### 8.1 Trace-size estimate from the measurements

Estimates are *derived* from the measured counters, with the derivation
stated:

* **per learned clause** the trace needs ≈ `learnedLitsAfter` literals plus
  ≈ 2 `Nat`s per conflict item; the item count is bounded by
  `learnedLitsBefore` (before minimisation, `EngineStats.learnedLitsBefore`).
  On `csplib12-gbac`: 17 136 learned clauses, 1.30 M literals before
  minimisation, 0.69 M stored — so ≈ **0.7 M clause literals + ≈ 2.6 M hint
  integers** (2 per pre-minimisation literal), before any compression.
* **per propagation** the trace needs one literal, its reason clause, and the
  level index of each reason literal. `propagations` = 1.03 M on the same
  instance, `reasonsTrimmed` = 0.66 M (transient reason slots reclaimed;
  a trace cannot rely on the solver's transient store, so it must carry the
  first-use copies), giving an order of magnitude of **1 M steps**.
* therefore, order **10⁶–10⁷ tokens** for a 60 k-decision run: an ASCII
  text trace would be order 10–100 MB per instance. This is an estimate, not
  a measurement; it is consistent with the 0.69 M stored clause literals.

The PB option's size is this trace *plus* the encoding of §2 (value
Booleanisation of every domain and every family), which on the same instance
is a function of ≈ 2.1 k slots and their domains, and is not measured here.

## 9. Comparison

| | (a) VeriPB over a PB encoding | (b) project trace + small Lean checker |
| --- | --- | --- |
| artifact | PB input + VeriPB proof log | header + justification-step stream |
| checker | VeriPB (independent, mature) | a new Lean checker, soundness proved against `accepts` |
| new proof obligation | per-family encoding correctness (`≈ Exact.lean` scale) or a *trusted* out-of-process translator | the checker's soundness theorem, reusing `Lit`/`Analyze`/`Clauses` lemmas |
| justification content | resolution chain recomputed per learned clause and translated through the encoding | the engine's own `CItem` lists and reason clauses, no translation |
| propagation justification | each reason clause added as a PB consequence; unit propagation replayed in the encoding | `PruneSound` checked directly (target unassigned, others false) |
| what is trusted | VeriPB, the encoding, the translator, the PB semantics | Lean kernel, the checker's compiled path (`csimp`/`implemented_by` seam), the proved compiler |
| bypasses the compiled solver, LLVM, seams? | yes (for the solver) — but the *encoding* is now the seam | yes (for the solver and its seams); the compiled problem is still the proved one |
| optimality | UNSAT under the improving bound, + witness | same |
| trace size | trace + encoding; larger | ≈ engine proof structures; smaller by construction |
| maintenance | a second semantics of every family, kept in step with the compiler | one format in the engine's existing vocabulary |

## 10. Recommendation

**Adopt option (b): a project-specific trace of justification steps, checked
by a small Lean checker whose soundness is stated against `accepts`.**

Three strongest reasons:

1. **The soundness statement already exists in the right shape.** `search_unsat`
   (`LeanFzn/Engine/Search.lean:2306`) and `analyze_empty_unsat`
   (`LeanFzn/Engine/Analyze.lean:4197`) are exactly the theorem a trace
   checker must instantiate; the checker can be built from `Lit`,
   `Clauses` and `Analyze` lemmas (`resolveWith_entailed`,
   `chainReasonLits_entailed`, `explainLit_spec`) instead of from a new
   semantics.
2. **No second semantics of the compiled families.** `DomConstraint` has 42
   constructors and the compiler's accepted surface is the 21 extracted
   shapes plus the 34 aux-slot pinning shapes (the `AuxShape` inductive,
   `LeanFzn/Compiler/Compile.lean:488-632`). Option (a) needs the
   per-family encoding-correctness development of §2.1 (comparable to the
   17 k-line `Compiler/Proofs/Exact.lean`) or an out-of-process translator
   that is *trusted*. Option (b) stays inside `DomConstraint`, whose leaf
   semantics is already tied to the source by `compileFull_exact`.
3. **The justification format is already self-checking.** `analyze` records
   trail positions and levels and refuses doubtful steps at runtime
   (`Analyze.lean:1-21`); `PruneSound` is exactly the condition a checker can
   verify a posteriori. So the trace is a by-product of the existing
   structure, not a new proof development inside the solver.

Option (a) remains attractive if an *externally maintained* checker is a hard
requirement; but then the honest price is the encoding proof (on top of the measured trace
cost of §8.1), and Phase B
must budget it explicitly.

## 11. Open problems

* **Sparse/holed domains.** `DomC` has `bitset`, `boundsHoles` and `sparse`
  (`LeanFzn/Engine/Types.lean:101-108`). A domain with holes is not a bound
  interval, so a trace's initial assignment must be the *materialised*
  domain, not `(lo, hi)`; a PB value encoding handles this naturally, and a
  bound-literal trace needs `intNe` literals. Which representation a
  trace carries is a Phase B decision; the engine already emits `intNe` atoms,
  so the vocabulary is there.
* **Set payloads.** `setInSlot`/`setInReifSlot` carry an `IntSetValue`
  payload, not a slot. Both options must treat it as a constant (it is), but
  a trace header must carry it.
* **Duplicated slots in constraints.** `SatisfiedBy` uses `a[i]!` and the
  propagators state their bounds "even when slot positions coincide"
  (`DomainConstraints/Core.lean`, `propPlusSlot`). A checker's reason-clause
  validation must use the same reading; this is a statement-level question,
  not a design change.
* **`analyze` give-ups.** `analyze` can return `ok = false` (fuel, missing
  explanation); such a run produces no refutation. A trace-producing solver
  must simply not claim UNSAT. No certificate obligation.
* **Checker seam.** The checker will be compiled; if it has a fast path it is
  a new `@[csimp]`/`@[implemented_by]` entry, so `audits/native_seams.json`
  would grow by one row and the checker's fast path needs its own equality
  theorem. Alternatively the checker runs as the slow kernel definition
  (small traces only). This is the one place where option (b)'s trust base is
  wider than "the kernel".
* **Portfolio nondeterminism.** The driver prints the first completed proof
  (`Driver.lean:112-260`). A certificate makes the printed answer
  checkable, but the *choice* among certificates is not certified; that is
  fine, since each candidate is independently checkable.
* **Canonicalisation.** `canonClause` (`LeanFzn/Engine/Clauses.lean:730`)
  re-interns literals; it preserves denotations (`canonClause_lits_decode`),
  so a trace may be emitted before or after canonicalisation. A Phase B
  decision, no semantic risk.
* **Cost of emitting.** Emitting the trace costs time proportional to
  `propagations + 2·learnedLitsBefore` (§8.1). Whether it is always on, or a
  flag, is a CLI policy question for the coordinator; it must not change any
  verdict.

## 12. What Phase B would need

1. A trace format (schemas for header, steps, end marker) with a version and
   a documented encoding of literals, levels and reason clauses.
2. Emit hooks in `Clauses.propagateLiteral`/`Propagate.PropOut` and in
   `Analyze` (the items are already computed) plus at the four `search`
   leaves; every emitted step is a *record*, no new proof inside the solver.
3. A checker module: a pure function over (header, steps) with a soundness
   theorem of the shape `check = true → ∀ b ∈ allAssigns, accepts p b = false`,
   built from `Lit`/`Clauses`/`Analyze` lemmas, with the optimality pair of
   §7.
4. A `--proof-log=FILE` flag (an output option, no verdict change), and a
   `leanfzn check-proof` mode, plus negative tests in `Tests/` that mutate
   steps and must be rejected, and positive tests over `audits/benchmark_fixtures`.
5. A gate row in `audits/run_gates.sh` (a trace round-trip check on the
   fixtures) and possibly a new `audits/native_seams.json` entry for the
   checker's fast path.
6. For option (a), in addition: the PB encoding, the per-family
   encoding-correctness proofs or a reviewed trusted translator, and a
   VeriPB integration test. Phase B should not start with (a).

## Appendix A — Sources cited

`LeanFzn/Compiler/Types.lean:37` (`CompiledProblem`) ·
`LeanFzn/Compiler/Compile.lean:90` (`accepts`) ·
`LeanFzn/Compiler/Compile.lean:1223` (`expandPlan`), `:1537` (`compileModel`) ·
`LeanFzn/Compiler/Objective.lean:39` (`ObjectiveSpec`), `:62` (`improveBound`) ·
`LeanFzn/Compiler/Proofs/Normalize.lean:2967` (`compileFull_exact`) ·
`LeanFzn/Compiler/Proofs/Objective.lean:201` (`compileOpt_optimal`) ·
`LeanFzn/Compiler/SeedClauses.lean:42` (`seedClauses`) ·
`LeanFzn/Solver/Propagation/Types.lean:24` (`Atom`), `:34` (`Literal`) ·
`LeanFzn/Solver/Propagation/DomainConstraints/Repr.lean:70` (`DomConstraint`),
`:253` (`SatisfiedBy`), `:371` (`satisfiedB`) ·
`LeanFzn/Engine/Types.lean:129` (`Entry`), `:169` (`Entailed`), `:176`
(`EClause`), `:192` (`PropV2`), `:242` (`EngineStats`), `:101` (`DomC`) ·
`LeanFzn/Engine/Lit.lean:47` (`atomSlot`) ·
`LeanFzn/Engine/Clauses.lean:730` (`canonClause`), `:866` (`reasonClause?`) ·
`LeanFzn/Engine/Analyze.lean:42` (`CItem`), `:462` (`explainLit_spec`),
`:906` (`chainReasonLits`), `:1138` (`chainReasonLits_entailed`), `:2046`
(`resolveWith_entailed`), `:4096` (`analyze`), `:4143` (`analyze_sound`),
`:4197` (`analyze_empty_unsat`), `:4215` (`analyze_asserting_mem`) ·
`LeanFzn/Engine/Search.lean:229` (`propsOf`), `:378` (`propsOf_pruneSound`),
`:2136` (search soundness section), `:2449` (`coreSolveFrom`), `:2306` (`search_unsat`), `:2755` (`coreSolve_unsat`) ·
`LeanFzn/Engine/Proofs/PruneSound.lean:39` (`PruneSound`), `:56`
(`PropsSound`) ·
`LeanFzn/Engine/Reduce.lean:1` (reduction) ·
`LeanFzn/Integration/Optimization/Basic.lean:232` (`OptRun`), `:265`
(`optimizeCertified`) ·
`LeanFzn/Integration/Optimization/Partial.lean:15` (`PartialCertSolver`) ·
`LeanFzn/Integration/Public/Optimize.lean:953` (`optimizeCore_solution_sound`),
`:961` (`optimizeCore_improving`), `:967` (`optimizeCore_optimal`) ·
`LeanFzn/Integration/Public/Driver.lean:41` (`emitStats`), `:160`
(portfolio) ·
`LeanFzn/Integration/Public/Solve.lean:52` (`solveModelWithStats`) ·
`audits/native_seams.json` (63 seams: 29 `csimp`, 34 `implemented_by`).

## Appendix B — Measured commands

```bash
cd /tmp/wt/w9
for f in int_ne_unsat pigeon5_4 latin4 reified_mix objective_sum; do
  .lake/build/bin/leanfzn solve audits/benchmark_fixtures/$f.fzn --stats
done
for f in pigeonhole_bool3 pigeonhole_bool4 gen_bool_dense40 gen_bool_dense60 \
         latin5 linear_chain_32; do
  .lake/build/bin/leanfzn solve audits/benchmark_fixtures/generated/$f.fzn --stats
done
.lake/build/bin/leanfzn solve \
  minizinc-challenge/2026fzn/gbac/csplib12-gbac.fzn --stats
```

The statistics line is `emitStats` (`LeanFzn/Integration/Public/Driver.lean:41`);
the counters are `EngineStats` (`LeanFzn/Engine/Types.lean:242-267`).

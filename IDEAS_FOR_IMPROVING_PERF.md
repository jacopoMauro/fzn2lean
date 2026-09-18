# Ideas for improving solver performance

> **Status note (2026-09-18).** This began as an audit of the original
> leaf-check architecture, so the descriptions and line numbers below are a
> historical baseline rather than a description of the current implementation.
> Items 1.1–1.6, 3, 4.1, and 4.5 have since been implemented with proved
> equivalence bridges. Item 2 has its string-splitting and lexer-composition
> layers, but still lacks the final entry/value round trip and string-free leaf
> wiring. The sparse reversible state from item 4.3 is proved through one-pass
> refinement but is not yet wired into search. See the
> [performance worklog in `PLAN.md`](PLAN.md#performance-worklog-ideas_for_improving_perfmd-progress)
> for the authoritative status and theorem names.

Findings from a full read of `solver/` and the checker hot paths it calls.
Each idea lists: what to change, why it is slow today (with file:line), the
expected win, and the proof obligation (the project rule: every fast path
keeps or adds a theorem connecting it to the existing verified definition —
see PLAN.md item 4 and the `implemented_by` pattern in
`LeanFzn/FznSolution.lean`).

Impact estimates are relative to the original leaf-check architecture, where
the verified front door revalidated every candidate from scratch.

---

## 0. Original dominant cost: every leaf re-ran the whole front door

`solveLeaf` (solver/Solve.lean:105) calls
`checkModelSolutionFast m (emitAssignment names asg)`. Per leaf this:

1. re-runs `firstUnsupportedFast m` — a scan over all constraints with a
   hash lookup each (LeanFzn/FznCheck.lean:1059-1060);
2. re-runs `wellFormedFastB m` — the full static well-formedness check
   (FznCheck.lean:1063);
3. renders the assignment to a string via `emitAssignment`
   (O(n²) appends, solver/Emit.lean:68-72);
4. `stripSeparators` + `tokenize` + `parseSolution` — re-lexes and re-parses
   the string we just built (FznCheck.lean:1064);
5. rebuilds the whole store: `paramMap m` (hash-insert of every parameter,
   again) + entries + the `completeFix` fixed-point walk over all variables
   (`completedBox`, LeanFzn/FznSolution.lean:503-506);
6. evaluates every constraint argument against that store
   (`constraintHoldsFullFastB`, LeanFzn/FznGlobals.lean:2266-2269).

All of (1)-(5) are invariant or nearly-invariant across the leaves of one
search. Ideas 1-3 below remove them.

---

## 1. Quick wins (proofs already exist, no new theorems needed)

### 1.1 Use `PreparedModel` in the leaf — the biggest cheap win

`PreparedModel` (LeanFzn/FznCheck.lean:1125-1160) exists exactly for batch
checking: it pre-computes the two static gates, the pre-dispatched
constraint list (`dispatchMap` lookups done once), and the declared-variable
set — with `checkPreparedSolution_eq` already proven. **The solver never
uses it**: every leaf re-pays items (1) and (2) above plus per-constraint
name dispatch.

Change: `solveLeaf` takes a `PreparedModel` (built once per solve) and
calls `checkPreparedSolution` instead of `checkModelSolutionFast`.
Proof cost: essentially zero — rewrite `solveModel_sat_sound` through
`checkPreparedSolution_eq`.

Expected impact: removes two full model scans + per-constraint hash lookups
per leaf. On models with many constraints this is a large constant factor
on the dominant cost.

### 1.2 Compute the `interVals` intersection once in `propEqSlot`

`propEqSlot` (solver/Propagators.lean:791-796) computes
`interVals (getSlot doms i) (getSlot doms j)` up to **four times** (twice in
the emptiness check, twice inside `eqNarrow`), and each `interVals`
(Propagators.lean:383) is `di.filter (fun v => valueMemB v dj)` — a linear
scan of `dj` per element of `di`, each comparison a boxed `Value.eqB`.

Change: bind `let xi := interVals di dj; let xj := interVals dj xi` once;
check emptiness and narrow on the bound values. Same for `propLeSlot`'s
`atMostVals`/`atLeastVals` pair (Propagators.lean:1094-1098).
Proof cost: zero — the twin is definitionally equal; or prove the obvious
`let`-dup lemma.

### 1.3 Precompute the inverse permutation in `heuristicSearch`

`unpermute` (solver/Heuristic.lean:174) is
`(List.range order.length).map (fun i => b.getD (order.idxOf i) default)` —
`idxOf` is a linear scan, so the leaf conjugation is **O(n²) per leaf**.

Change: compute `inv := order.map (order.idxOf ·)` once per search (or an
inverse array), then `unpermuteFast inv b := inv.map (b.getD · default)`.
Proof cost: an `unpermuteFast_eq` lemma from `idxOf` properties; or attach
with `implemented_by` per the established pattern.

### 1.4 Hoist repeated `slots.map Prod.fst` / `Prod.snd`

`solveModel` computes `slots.map Prod.fst` and `slots.map Prod.snd` at
least four times each (gates, search call, emit call — solver/Solve.lean:118-126).
Each is O(#slots) with allocation. Bind once with `let`.

### 1.5 O(1) fixpoint stability test

`fixpointFuel` detects the fixed point with `domsEqB` (solver/Fixpoint.lean:354+,
twin at Propagators.lean:741) — a full structural comparison of every domain
(every value) per round. Change: have `propPass` return a "did anything
change" bit (compare only the slots that were written, or count writes), or
compare domain lengths first (narrowing always shrinks). Proof cost: small —
a `changedFlag = domsEqB` bridge.

### 1.6 `String.Builder` twin for `emitSolution`

`emitSolution` (solver/Emit.lean:68-72) right-recurses with `++`, giving
O(n²) character copies. Twin with `String.Builder`, attach via
`implemented_by` (string equality is the observable, trivially preserved).

---

## 2. Skip the string round-trip in the leaf (biggest single win)

The leaf renders `names.zip asg` to text (idea 0.3) and the checker
immediately re-parses it back to `List Entry` (idea 0.4). The intended
invariant — the emitter's format is exactly what `parseScalarEntry`
reads — is already validated end-to-end by the test suite, but no theorem
pins it.

Change: prove the round-trip theorem
`parseSolution (stripSeparators (emitSolution ps)) = .ok (entriesOf ps)`
(name/shape as suits the statement; the value grammar is tiny — ident, `=`,
int/bool literal, `;`). Then add a leaf fast path that builds `es` directly
and calls the dynamic half (`checkPreparedDyn`-style) with `es`, skipping
string build, separator strip, lexing, and entry parsing entirely.
Proof cost: moderate — a parser round-trip lemma of the kind
`FznCompleteness/FznAssembled` already master for the model grammar; the
leaf-soundness rewrite is then mechanical. This kills items 0.3-0.4 and
most of the per-leaf allocation.

---

## 3. Incremental store construction per leaf

`completedBox m es` per leaf (idea 0.5): rebuilds `paramMap m` (all
parameters) and re-runs `completeFix` — at least one full
`completePass` over *every* variable declaration per leaf
(FznSolution.lean:480-506). Two layers:

1. **Base map**: parameters never change across leaves. Build `paramMap m`
   once per solve; per leaf, insert the k slot entries into the persistent
   `Std.HashMap` (structurally shared, O(k)).
2. **Completion plan**: precompute once the variable-initializer
   dependency order (topological sort of "whose initializer reads whose
   name"); per leaf, run completion along that plan — or better, note
   that initializer-derived variables depend only on slot values, so the
   plan is a fixed evaluation sequence with no `contains` probing.

Proof obligation: an extensional equality between the fast store builder
and `completedBox` (or the `Outcome`-level route used by
`checkPreparedDyn_eq`, which avoids unfolding the opaque `completedBox` by
keeping it on both sides — the established trick in FznCheck.lean:1233+).
This is PLAN.md item 4's "prepared checker / initializer plan" applied to
the solver leaf.

---

## 4. Data-structure replacements in the search core

### 4.1 `acc ++ [v]` — O(n) per node, O(n²) per branch

`search` (solver/Search.lean:57) and `enumerateAll` (solver/Enum.lean:109)
extend the accumulator with `acc ++ [v]`. Change: cons and reverse at the
leaf (or use a `Array` with copy-on-write). Proof cost: `searchRev` + a
`reverse` bridge lemma; the master theorems then transfer verbatim since
the emitted text uses the reversed list.

### 4.2 `splitBranch` copies the whole domain list per branch

`solver/Fixpoint.lean:486-490` rebuilds the entire slot list (`[] :: q.1`
patterns) for each child — O(#slots) allocations per node. This is exactly
what `RevState` (PLAN 6.4) fixes: finish wiring the sparse-set state into
`prunedSearch` (see 4.3).

### 4.3 Finish `RevState` integration (already half-built)

`solver/RevState.lean` implements verified sparse-set domains with O(1)
removal/backtrack and an O(1)-per-narrow compaction pass, plus the
refinement theorem `revPropPass_refines` connecting it to `propPass`. It is
**not wired into any search** — `prunedSearch` still operates on
`List (List Value)`. Remaining work: close the 6 `sorry`s
(RevState.lean:605-606, 827-832), write the trail-integrated search, and
prove it returns the same logical result as `prunedSearch` (the module
docstring already sketches exactly this refinement theorem). This is the
intended performance path of PLAN 6.4: O(1) backtracking instead of list
copies per node.

### 4.4 Integer-specialized domains

`VarDomain.intDom` already holds `List Int`, but `declSlot` immediately
materializes `.values` — `xs.map Value.int` (solver/Domain.lean:235) — and
the whole propagator stack then compares boxed `Value`s through
`Value.eqB` with constructor dispatch (Propagators.lean:358). Ideas, in
increasing invasiveness:

- keep `List Int` end-to-end for int-only models, with `Value` only at the
  emit boundary (needs a typed-domain layer above `PropResult` — a bigger
  refactor; the `Preserves` contract is generic enough to instantiate);
- canonical **sorted, duplicate-free** domain representation (PLAN 4's
  "canonical sorted representations"): intersection by merge instead of
  `filter`+scan, `domMin`/`domMax` in O(1), `removeVal` by position;
- bitsets (`ByteArray`/`Std.BitVec` window) for small ranges: O(1)
  membership/removal, cardinality by popcount — pairs naturally with the
  sparse-set `RevState` (a sparse set *is* an index bitset split into
  window + swap area).

### 4.5 `Enum`/`Optimize` result accumulation

- `enumerateAll` joins child results with `++` (O(k²) in solution count);
  add an accumulator parameter (order changes — state the membership
  theorem for the accumulated form, as `mem_allAssigns` already does for
  `allAssigns`).
- The final `dedup` of texts (solver/Enum.lean:310-315) is O(k²) string
  equality. Replace with a `Std.HashSet` seen-set + order-preserving fold
  (`dedup_mem_iff` restates almost unchanged).
- `optPairs` (solver/Optimize.lean:465) materializes **all** accepted
  assignments as strings before `pickBest` — a streaming fold (fold with
  running best) removes the memory blowup; the membership theorem becomes
  an extremal-value theorem over the enumeration.

---

## 5. More propagators (pruning beats everything)

Only four shapes are extracted today — `int_eq`, `int_ne`, `int_le`,
const-eq (solver/Extract.lean header table). Every other constraint
(including `all_different`, `int_plus`, linear) is only enforced at the
leaf by the full checker. Each new propagator follows the established
`Preserves` pattern (Propagators.lean:762-777), so the proof cost per
propagator is bounded and the search theorems need no changes. Ranked by
expected pruning per proof effort:

1. **`int_plus` / `int_times` / `int_min` / `int_max` / `int_abs`** —
   bounds propagation (min/max arithmetic on domain endpoints).
2. **Linear** `int_lin_eq` / `int_lin_le` — the MiniZinc compiler emits
   these constantly; bounds reasoning over coefficient-sorted domains.
3. **`all_different`** — at minimum pigeonhole counting (any k slots whose
   union of candidate values has < k values ⇒ contradiction; a counting
   variant of the existing `allDiffSetB` machinery in
   `FznGlobals/AllDiffCounting.lean`), better: Hall-interval bounds
   reasoning over sorted domains.
4. **Boolean connectives** (`bool_and`, `bool_or`, `bool_not`,
   `bool_clause`) — tiny domains, cheap fixes.
5. **`int_lt`** — currently folded through `int_le` extraction only as a
   pair of slot names; add the literal-argument shapes (`int_le(x, 5)`)
   which extraction currently skips (Extract.lean: "literals in
   `int_ne`/`int_le` positions ... not extracted").

---

## 6. Search heuristics (correctness-neutral by the existing theorems)

### 6.1 Combine propagation + MRV into one entry point

`solveModelProp` (Solve.lean:331) and `solveModelHeur` (Solve.lean:354) are
separate; no entry point prunes *and* reorders. The permutation machinery
(`heuristicSearch`, `IsPerm`) applies verbatim on top of `prunedSearch`'s
slot list; alternatively make `splitBranch`'s slot choice dynamic (see 6.2).

### 6.2 Dynamic MRV inside `prunedSearch`

`splitBranch` always branches on the **first** non-singleton slot in list
order (Fixpoint.lean:486-490). Static MRV (`mrvOrder`) is computed once from
the initial domains — after propagation shrinks domains the order is
stale. Dynamic MRV = choose the currently-smallest domain in `splitBranch`.
The branch-coverage obligation is exactly PLAN 6.5's lemma: the two
children cover every assignment of the parent (a `allAssigns doms =
allAssigns l ∪ allAssigns r`-style theorem over `splitBranch`, plus
permutation of which slot splits first).

### 6.3 Last-conflict restart bias (Sabori's single most effective component)

Per the sabori_csp write-up, after a failed subtree, prefer the
most-recently-conflicted variable. In this architecture, "conflict" is
well-defined and free: a propagator's `contradiction` names its slots (the
`DomConstraint` indices). A restart-scoped order permutation is
correctness-neutral by the same `IsPerm` theorems — the order may be any
function of the previous run's conflict data. Start simple: track a
per-slot `lastConflictRound : Array Nat`, re-sort once per restart
budget (Luby-style), rerun `prunedSearch` — the master theorems hold per
run, and `heuristicSearch_none_iff` composes across restarts exactly as
`optRefine`'s rounds already do.

### 6.4 Value ordering for optimization

`splitBranch` tries `v` (the domain head) first; for minimize/maximize,
ordering candidate values toward the objective's improving side finds
better incumbents earlier, which makes the B&B bound bite sooner (see 7.1).
Correctness-neutral (same branch partition, different order).

### 6.5 Early constraint checking (forward checking) inside the leaf check

Currently satisfaction is decided **only at complete leaves**. A
monotonicity observation unlocks partial-assignment pruning: if a
constraint's arguments are all already fixed by the partial assignment and
it fails, every completion fails too (store extension never changes an
evaluated result — `Expr.eval` only reads assigned names). Add a
`partialLeaf` that checks exactly the constraints whose argument names are
all bound, invoked at each node of `search`. Proof obligation: a
"store-extension stability" lemma for `Expr.eval`/`Holds` — one induction,
then a `prunedSearch`-style wrapper. This generalizes idea 5's propagation
to *all* constraint shapes at zero per-propagator proof cost, at the price
of per-node checker work (use with the prepared/compiled leaf of ideas
1.1-3).

---

## 7. Optimization-specific improvements

### 7.1 Integrate the bound into one search (single-pass branch-and-bound)

`optRefine` (solver/Optimize.lean:965-985) restarts `search` from scratch
each round with a better bound (`bbLeaf`); every round re-explores the
prefix of the tree above the bound. Classic B&B instead carries the
incumbent bound *into* the search: on each new incumbent, tighten a
slot-domain filter on the objective variable (a `removeVal`-style narrowing
whose preservation theorem is the same shape as `propConstEq`'s), and let
the existing propagation prune. The `.exhausted` fallback to full
enumeration (Optimize.lean:1194) then disappears for well-behaved fuel.

### 7.2 Objective propagation

A `propObjBound` propagator: `minimize x` with incumbent `w` narrows `x`'s
domain to values `< w` (or `≤ w` for non-strict). Same `Preserves` pattern;
one more constructor in `DomConstraint` (or a special-cased propagator over
the extracted objective slot, which `slotObjFn` already identifies).

### 7.3 Prune enumeration in `optPairs` by the incumbent

Even the reference path can fold with the running best instead of
collecting all pairs (see 4.5).

---

## 8. Fixpoint engine: event-driven propagation

`propPass` is round-robin: every propagator runs every round regardless of
which domains changed (Fixpoint.lean:271-277). Standard fix: per-slot
**watch lists** — each propagator registers the slot indices it reads
(`DomConstraint` already carries exactly these indices!); when
`setSlot` shrinks a slot, enqueue its watchers; process until the queue is
empty. Proof obligations (PLAN 6.4 lists them): (a) every affected
propagator eventually runs (queue fairness — one induction over the
enqueue sequence), (b) the queued engine reaches the same fixpoint as
round-robin (confluence: both compute the greatest common narrowing —
provable via the existing `AllPreserve`/subset contract plus an induction
on queue processing). Expected win: on models with many constraints but
small active frontier, rounds drop from O(#props) to O(#touched).

---

## 9. Lean-local compilation notes

- **`@[inline]`** the tiny hot functions: `getSlot`, `setSlot`
  (Propagators.lean:117-133), `valueMemB`, `emitScalar`, `emitInt` — they
  are called millions of times; cross-module inlining avoids closure
  dispatch.
- **`implemented_by` twins** (project pattern): for `emitSolution`
  (1.6), `unpermute` (1.3), the reversed-accumulator `search` (4.1), and
  the `Array`-backed `getSlot`/`setSlot` (each with an extensional
  equality theorem; `Array.toList_getD` bridges exist in RevState.lean's
  private lemmas already).
- **Build mode**: benchmark with `lake build --release`; the default
  build leaves the compiler's optimizer off for executables.
- **`Value` boxing**: `Value.int i` allocates; `Value.eqB` dispatches on
  constructors first (FznSolution.lean:1341+). Short of the typed-domain
  refactor (4.4), interning small integers or specializing
  `valueMemB : Value → List Value` to `Int → List Value` on int-only
  domains (both sides of the comparison known to be `.int`) removes a
  dispatch per comparison — provable by a degenerate-cases-simp lemma.
- **`leavesProduct` overflow**: none (Nat is bignum), but it is recomputed
  in several gates (`slotsChecked`, `optBbCore` at Optimize.lean:1191) —
  bind once.

---

## 10. Measure before/after (PLAN 4's rule)

`TestsBench.lean` times the three entry points but reports no counters.
Add machine-independent counters — nodes visited, propagator applications,
leaf checks, store builds, string bytes emitted — behind a `SolverStats`
accumulator (pure, threaded like `search`'s accumulator; no IO in the
verified core). These (not wall time) are the numbers to compare against
sabori's `SolverStats` when evaluating heuristic work (6.2-6.4): wall time
conflates engine speed with search quality, and only the latter should
move when a heuristic lands.

---

## Suggested order of attack

| # | Item | Proof cost | Expected impact |
|---|------|-----------|-----------------|
| 1 | 1.1 PreparedModel leaf | ~0 | large constant on dominant cost | ✅ done (11-13x on constraint-heavy leaves) |
| 2 | 1.2, 1.4, 1.5 hoisting/recompute fixes | ~0 | small-medium | ✅ 1.2 + emit 1.6 done |
| 3 | 2 string round-trip skip | moderate | very large (leaf cost) |
| 4 | 3 incremental store | moderate | large (leaf cost) |
| 5 | 5 propagators (`int_plus`/lin/all_diff) | per-propagator, bounded | large (pruning) |
| 6 | 6.1 combined entry, 6.4 value order | ~0 | medium |
| 7 | 4.1 cons/reverse, 4.5 streaming/dedup | small | medium at scale | (1.3 unpermuteFast done) |
| 8 | 4.3 finish RevState wiring | moderate (close 6 sorries) | large on wide models |
| 9 | 7.1 single-pass B&B | moderate | large on opt models |
| 10 | 8 event queue, 6.2 dynamic MRV, 6.3 last-conflict | higher | the sabori-class wins |

Items 1-4 attack the per-leaf constant (they compound multiplicatively);
items 5-8 attack the tree size; items in 9-10 make the engine and the
order smart. The correctness architecture (leaf-check + `Preserves` +
permutation heuristics) is built so that all of these drop in without
touching the master theorems' statements.

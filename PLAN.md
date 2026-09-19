# LeanFzn status and roadmap

This file records what is complete, what remains outside the supported
fragment, and the order in which future work should proceed. A feature is
only considered complete when its executable implementation is connected to
the declarative semantics by a Lean theorem and is covered by regression
tests.

## Current status

The grammar and parser are aligned. Parser soundness and completeness are
proved, and the recognition theorem holds without additional hypotheses. The
static semantics (`WellFormed`, with executable checker `wellFormedB`) covers
environments, name resolution, initializer and alias equality, array lengths,
objective types, duplicate declarations, and predicate-signature checking.

The repository also contains a canonical pretty-printer with round-trip
tests, standard FlatZinc predicate signatures and interpretations, and a
solution checker. The checker supports 218 predicate names: 61
non-extensional standard predicates, 19 extensional set predicates, and 138 `fzn_*`
global constraints. Each supported predicate has a mathematical `Prop`
interpretation, an executable Boolean twin, and an agreement theorem. The
combined results are `globalsInterpB_iff`, `fullInterpB_iff`, and
`checkSolutionFull_correct`; `#print axioms` reports only `propext`,
`Quot.sound`, and `Classical.choice`. The library, solver, and test sources
included in the documented build targets contain no `sorry` (scratch/probe
files are not part of this claim).

`Tests/Coverage.lean` exercises every supported predicate in accepting and
rejecting cases and checks that a new checkable name cannot be added without
dynamic coverage. The current suite has 465 cases and covers 218/218 names.
The Gecode-derived suite adds 64 solution checks over 15 models. The compiled
benchmark suite currently checks a 32,000-variable solution in about 50 ms
and parses a roughly 5 MB model in about 0.3 seconds on the development
environment; these figures are regression references, not portable
guarantees.

Item 1 below (the verified CLI front door) is complete: `LeanFzn/FznCheck.lean`
provides `checkModelSolution` — static validation through the verified fast
twin `wellFormedFastB` (hash-based, proved equivalent to `wellFormedB` by
`wellFormedFastB_iff`; the naive checker is Θ(n²), ~37 s at 32k variables),
predicate-name validation through `firstUnsupported`, entry well-formedness
(`entriesOkB`, closing a hole where a solution string could reassign a
parameter, assign an unknown name, or a name twice), and the dynamic checker
— with the unconditional correctness theorem `checkModelSolution_correct`
connecting acceptance to full `Satisfies fullSig fullInterp`. `Tests/Check.lean`
exercises all failure modes and exit codes; `Tests/Bench.lean` guards the
front door's linearity.

Item 6 (the verified constraint solver) is implemented, proved, and tested
through 6.1–6.7 (see the status block at the end of that item), and the CLI
exposes it: `leanfzn solve [--prop] [--mrv] [--budget N] [--nogoods]`,
`leanfzn enum`, and `leanfzn optimize` all run the verified stack
end-to-end (every emitted solution is re-checked through the verified
front door).

## Remaining work (authoritative checklist)

This is the authoritative list of open work as of 2026-09-19.  The detailed
sections and worklogs below preserve design context and completed theorem
names; where an older paragraph conflicts with this checklist, this checklist
wins.

### P0 — Finish the emitted-solution round trip

This closes the remaining proof gap needed to remove rendering and reparsing
from every solver leaf.

- [x] Rebuild lexer composition on the satisfiable foundations: the
  honest success-conditioned offset-transport stack — `lexInt_offset_ok`,
  `lexToken_offset_ok`, and the walk-level `tokenizeAux_offset_ok` (no scan
  premise at all; branch room derives from success via `lexUnsigned_gt`)
  — replaces the withdrawn vacuous `htw` family for the round-trip's
  needs.  The intra-line layer computes every entry-line token *in place*
  over the composite array (`lexToken_kw_segment`,
  `lexToken_ident_segment`, `lexToken_eq_segment`,
  `lexToken_semi_segment` on `composite_read`/`word_scan_acc`/
  `takeWhile_take_drop`), so no intra-line walk-agreement premises are
  needed: the `;`/`=`/space boundary characters fail all four scan
  predicates by decidability.
- [x] Finish the digit-literal segment token: `lexToken_int_segment` lands
  (P0.6) with the hex/octal guards closed by the two-character argument
  (the `q+1` char is a digit inside the segment, never `x`/`o`, or the
  y head — excluded by the `'0'`-head premise).
- [ ] Prove the emitted scalar-entry round trip through `parseEntry` for
  identifiers, Booleans, nonnegative integers, and negative integers.
  The four-step walk composition is mapped and its fuel landed
  (P0.7a/P0.7b: `tokenizeAux_step`, the skip facts,
  `composite_cons_head`, `composite_skip_origin_ident`); the remaining
  work is the step chain itself (ident/bool/negative-int siblings of
  `lexToken_int_segment`'s statement shape, validated).
- [ ] Assemble the list/line result into the master theorem
  `parseSolution (stripSeparators (emitSolution ps)) = .ok (entriesOf ps)`
  under the emitter's explicit name hypotheses.
- [ ] Add a string-free solver-leaf path that passes `entriesOf ps` directly
  to the prepared dynamic checker, and prove it equivalent to the existing
  emitted-text path.
- [ ] Add focused regression tests and before/after leaf benchmarks; retain
  the text path at the CLI boundary.

Already complete for this item: newline splitting/intercalation,
`tokenize_ident`, `tokenize_bool`, `tokenize_int_nonneg`,
`tokenize_int_negsucc`, `stripSeparators_emitSolution`, the honest
`takeWhile_append_of_tail_fail`/`noScans` token-level foundation, the
success-conditioned offset-transport stack (P0.2), the walk-level
`tokenizeAux_offset_ok` (P0.3), and the intra-line segment-token layer
(P0.5: kw/ident/eq/semi at offsets, `takeWhile_take_drop`,
`composite_read`/`composite_read_head`, `digit_not_punct`), plus the
digit-literal segment (P0.6: `lexInt_nonneg_segment`,
`lexToken_int_segment`, `guard_fail`).

### P1 — Wire the verified fast solver structures

- [ ] Integrate `RevState` into trail-based search and prove refinement to
  `prunedSearch`; the sparse-domain operations and one-pass refinement theorem
  already exist.
- [ ] Replace round-robin propagation with a queue and variable/constraint
  wake-up events; prove that every affected constraint is eventually run.
- [ ] Add watched-literal NoGood propagation and retain only globally valid
  learned facts across restarts.
- [ ] Make optimization a streaming, single-pass branch-and-bound traversal
  instead of materializing all accepted assignments; extend objectives beyond
  slot literals/identifiers.
- [ ] Remove the remaining quadratic accumulation paths, notably
  `searchBudget`'s `acc ++ [v]`, enumeration result concatenation, and
  string-based quadratic deduplication.
- [ ] Consider one-hot presolve rewrites only after each rewrite has an
  equisatisfiability theorem.

The linear propagators are not open work: `propLinEq_preserves` and
`propLinLe_preserves` are proved, wired into `domPropagators`, extracted for
`int_lin_eq`/`int_lin_le`, and covered by regression tests.  Propagation+MRV
is likewise already integrated by `solveModelPropMrv`.

### P2 — Engineering and independent assurance

- [ ] Add CI that performs a clean checkout, builds every documented Lake
  target, and runs every functional test suite.
- [ ] Implement §6.8 differential testing: exhaustively generate small finite
  models, compare the reference and optimized Lean solvers, and compare the
  common fragment with Gecode and Sabori.
- [ ] Expand malformed-input and adversarial-size tests, including integer
  boundaries, empty collections, duplicate assignments, and unsupported-name
  diagnostics.
- [ ] Generate the supported-predicate inventory and documentation from the
  Lean name lists so the reported names and counts cannot drift.
- [ ] Add `SolverStats` counters (nodes, propagations, failures, leaf checks,
  store builds) and use scaling-ratio thresholds in performance regressions.
- [ ] Keep the pinned MiniZinc source version and checksums explicit whenever
  the normative reference is upgraded.

Repository cleanup, archive classification, umbrella modules, Lake-target
cleanup, documentation reconciliation, and the 609-to-zero linter cleanup are
complete.  CI is the remaining clean-checkout enforcement mechanism.

### P3 — Further performance work

- [ ] Replace repeated predicate-name scans with a generated decision tree or
  verified hash-based dispatcher.
- [ ] Precompile typed constraint closures in `PreparedModel` so repeated
  checks avoid dispatch, arity checks, and expression-shape traversal.
- [ ] Reduce lexer/parser allocation with position-based and accumulator-based
  implementations, each connected to the reference operation by a theorem.
- [ ] Use canonical sorted domains, verified merge operations, or specialized
  integer-domain representations where benchmarks justify the change.
- [ ] Extend benchmarks to batches of solutions, large set/graph constraints,
  and peak-memory measurements.

### Deliberate scope boundaries

Optional-variable globals (`fzn_alternative`, `fzn_span`), float-dependent
globals, and `_reif`/float/opt variants remain outside the supported fragment.
Adding any of them is a fragment extension, not unfinished work in the current
integer/Boolean/set scope, and requires an authoritative semantic source plus
the usual declarative/executable agreement theorem and coverage.

## Detailed roadmap and completed milestones

The sections below retain the original milestone descriptions and proof
history.  Use the checklist above to select new work.

### 1. Clean and simplify — complete

Scratch experiments are archived, obsolete Lake targets were removed, the
library and solver have clear umbrella modules, the documentation reflects
the current tree, and the build is warning-free.  The clean-checkout build is
currently validated manually; automating it is tracked under P2.

### 2. Encode the missing global constraints

This item is **complete** for the integer/Boolean/set fragment: all 138
non-float, non-opt, non-reified `fzn_*` global-constraint names of the
fragment — including the graph, reachability, path, tree, Steiner-tree,
weighted-spanning-tree, regular/MDD, multidimensional (nested-array lex/
orbitope/geost/diffn_k), cumulatives, and partiality families — are
implemented with the established pattern (signature, declarative
interpretation, Boolean twin, per-name agreement theorem, dispatch
theorem, positive and negative dynamic cases, a well-formed static model,
and end-to-end solution checks).

Originally suggested order (all completed):

1. Reverse and chained lexicographic constraints:
   `fzn_lex_greater_int`, `fzn_lex_greatereq_int`,
   `fzn_lex_chain_less_int`, and `fzn_lex_chain_lesseq_int`.
2. Circuit constraints: `fzn_circuit` and `fzn_subcircuit`.
3. Scheduling composition: `fzn_cumulatives` and
   `fzn_cumulatives_decomp` (`fzn_alternative` and `fzn_span` stay
   unsupported — optional variables, see `globalsUnsupported`).
4. Regular-language constraints: `fzn_regular`, `fzn_regular_nfa`, and
   `fzn_cost_regular`.
5. Decision diagrams: `fzn_mdd`, `fzn_mdd_nondet`, and `fzn_cost_mdd`.
6. Graph, reachability, path, tree, Steiner-tree, and weighted-spanning-tree
   constraints.
7. Multidimensional constraints: `fzn_lex2`, `fzn_strict_lex2`, orbitope
   (including the greater-direction chain and orbitope variants),
   `fzn_geost*`, and `fzn_diffn*_k`.
8. Remaining partial or specialized constraints: `fzn_writes_seq` and
   `fzn_if_then_else_partiality` (`fzn_neural_net`,
   `fzn_piecewise_linear`, and `fzn_piecewise_linear_non_continuous` stay
   unsupported — floats, see `globalsUnsupported`).

The only remaining `fzn_*` names are deliberately outside the fragment
(listed in `globalsUnsupported`): `fzn_alternative`/`fzn_span`
(optional variables), `fzn_neural_net`/`fzn_piecewise_linear`/
`fzn_piecewise_linear_non_continuous` (floats), plus every `_reif`,
float, and opt variant. These remain explicitly outside the supported
fragment rather than receiving guessed semantics.

Before fixing the meaning of a new `fzn_*` predicate, record its authoritative
MiniZinc definition or decomposition and every additional semantic choice in
`specification/flatzinc_specification_assumptions.md`. Cross-check edge cases
against at least one reference solver where the library documentation is not
normative.

### 4. Improve speed while preserving correctness

Use `Tests/Bench.lean` to measure every optimization before and after it. Keep
the declarative definitions stable where possible, add optimized executable
twins, and prove each twin extensionally equal to the logical definition
before attaching it with `implemented_by`.

Done so far: the front door's static validation (`wellFormedFastB` in
`LeanFzn/FznCheck.lean`) is hash-based and linear — about 700× faster than
`wellFormedB` on the 32,000-variable benchmark — following exactly this
pattern (`wellFormedFastB_iff`). Prepared-model reuse, incremental prepared
stores, accumulator-based emission/search/enumeration, and the inverse MRV
permutation are also implemented; see the performance worklog below. The
following list records the broader optimization directions, including both
completed foundations and remaining extensions.

Potential improvements, in recommended order:

- Replace repeated linear membership tests in predicate dispatch with a
  generated decision tree or hash-based executable dispatcher, while proving
  agreement with `fullInterp` for `fullCheckableNames`.
- Extend the existing `PreparedModel` checker, which already reuses static
  gates, declaration data, initializer work, and constraint dispatch, with
  typed precompiled constraint closures.
- Build the candidate store and declaration lookup tables in a single pass,
  avoiding repeated list scans and intermediate arrays.
- Precompile each constraint into a typed executable closure after static
  validation, so repeated solution checks do not redo name dispatch, arity
  checks, or expression-shape traversal.
- Reduce allocation in the lexer and parser by using array positions and
  accumulator-based construction; every fast path must retain a theorem
  equating it with the existing parser operation.
- Improve large-set operations with canonical sorted representations or
  verified merge algorithms instead of repeated membership scans.
- Extend the benchmark suite with batches of solutions for one model, large
  set constraints, graph constraints as they are added, peak-memory checks,
  and thresholds based on scaling ratios rather than fragile absolute times.

### 5. Engineering and assurance

- Add continuous integration that builds every executable and runs all test
  suites on a clean checkout.
- Keep the build warning-free; the 609 existing Lean linter warnings were
  removed on 2026-09-18, with documented local suppressions only in the two
  split-heavy parser modules.
- Add tests for malformed models and solutions, duplicate assignments,
  unsupported predicate diagnostics, empty arrays and sets, integer boundary
  behavior, and adversarial input sizes.
- Generate the supported-name inventory and documentation from the Lean lists
  to prevent counts and names from drifting apart.
- Keep the vendored MiniZinc reference version and checksums explicit when
  upgrading the normative source.

### 6. Implement a verified constraint solver

The final major milestone is to turn LeanFzn from a parser and solution
checker into a solver that can produce solutions. Use
[`sabori_csp`](https://github.com/tofjw/sabori_csp) as the initial engineering
reference, while defining the Lean solver independently against LeanFzn's
existing declarative semantics.

Sabori's core is a finite-domain backtracking solver with queued constraint
propagation. It adds reversible domains, constraint wake-up events, variable
and value selection, restarts, activity scores, a Last-Conflict-style search
bias, and weak decision-trail NoGood learning. It deliberately avoids the
larger proof-producing machinery of lazy clause generation. This is a good
incremental model for LeanFzn: begin with a very small solver whose entire
search can be proved correct, then add propagators and heuristics behind
interfaces that preserve the original proof.

#### 6.1 Specify the solver contract

Start with finite-domain satisfaction only: integer and Boolean variables,
no optimization, no restarts, and a small constraint subset. Define a result
type that distinguishes `sat store`, `unsat`, and resource-limited `unknown`.
The initial public theorems should be:

- **SAT soundness:** if the solver returns `sat store`, then the model is
  well formed and `store` satisfies the declarative `fullInterp` semantics.
- **UNSAT soundness:** if it returns `unsat`, no satisfying store exists in
  the model's finite initial domains.
- **Completeness:** for a well-formed model in the supported finite fragment,
  the unbounded solver returns `sat` exactly when a satisfying store exists.
- **Termination:** the reference search terminates because every branch
  strictly decreases a finite-domain measure.

Keep `unknown` for future node, time, and memory limits. A bounded run may
return `unknown`, but it must never turn an interrupted search into `unsat`.

#### 6.2 Build the smallest complete reference solver

Implement a deliberately simple executable specification first:

1. Translate a statically validated FlatZinc model into a typed solver model.
2. Represent each variable by an explicit finite list or finite set of
   possible values.
3. Select the first non-singleton variable, branch on one value versus the
   remaining values, and enumerate until a complete assignment is found.
4. Use the existing verified checker semantics to validate leaves.
5. Convert a successful store to FlatZinc solution text and prove that parsing
   and checking that text succeeds.

This solver will not be fast, but it provides the semantic baseline and a
complete oracle for testing later propagators on small instances.

#### 6.3 Introduce verified propagation

Define a propagator result containing narrowed domains or a contradiction.
Each propagator needs a local preservation theorem:

> every satisfying assignment compatible with the input domains remains
> compatible with the output domains.

A reported contradiction must imply that no satisfying extension of the
input domains exists. Iteration to a propagation fixpoint needs a decreasing
measure, such as the sum of finite domain cardinalities, to prove termination.
Start with cheap propagators for equality, disequality, order, Boolean
connectives, simple arithmetic, and linear constraints. Then add element,
all-different, table, counting, inverse, scheduling, and other globals as
their semantics become available.

The search proof should depend only on the generic propagation contract. This
allows a weak propagator to be replaced by a stronger one without reproving
the entire solver: stronger pruning affects performance, while preservation
and contradiction soundness protect correctness.

#### 6.4 Add reversible executable state

After the functional reference implementation is stable, introduce an
efficient state with variable identifiers, mutable domain arrays, a
propagation queue, watched constraints, and a trail of reversible changes.
Sabori uses sparse-set domains so value removal is constant-time and
backtracking can restore a saved size; a similar representation is a useful
target, but it should refine the simple logical domain model.

Prove representation invariants and a refinement theorem connecting every
state transition to the functional solver. In particular, prove that:

- queued events eventually process every affected constraint;
- trail restoration recreates the exact ancestor domains;
- watched-constraint shortcuts cannot miss a required propagation or final
  constraint check; and
- the optimized search returns the same logical result as the reference
  search, apart from an allowed `unknown` caused by explicit resource limits.

Use `implemented_by` only after the optimized operation has an extensional
equivalence theorem. Keep a final call to the existing solution checker as a
defense-in-depth validation of every emitted solution.

#### 6.5 Add correctness-neutral search heuristics

Add heuristics only after exhaustive search is proved. Begin with minimum
remaining values (MRV), then reproduce Sabori's most useful lightweight
ideas: Last-Conflict-style selection after a backtrack and activity-based
selection during descent. These heuristics should choose only the order of
an otherwise exhaustive branch partition.

Prove a generic branch-coverage lemma: the child domains cover every value
allowed by the parent. Solver soundness and completeness can then remain
independent of the particular deterministic or randomized selector. Random
seeds must affect performance and solution order, never validity.

#### 6.6 Add sound learning and restarts

Start NoGood learning with Sabori's simple decision-trail NoGoods. Before a
NoGood may prune search, prove that it is entailed by the original model and
the decisions above its valid scope. Prove watched-literal propagation for
NoGoods against a simple declarative clause semantics. Activity bumps may use
approximate conflict attribution because they affect ordering only; pruning
may not.

Restarts must restore a proved root state while retaining only globally valid
learned facts. For an unbounded completeness theorem, either use a fair
restart schedule whose search limits eventually exceed every finite subtree,
or expose restarts only in a resource-bounded solver that may return
`unknown`. One-hot channel aggregation and other presolve rewrites can follow,
each with a theorem that the transformed model is equisatisfiable with the
original.

#### 6.7 Add enumeration and optimization

Once satisfaction is stable, add all-solutions enumeration by learning a
blocking NoGood for each emitted assignment. Prove that every reported
solution is distinct and satisfying, and that a completed enumeration returns
all satisfying assignments.

Add minimization and maximization last. Implement branch-and-bound using a
strict improving bound and prove that each bound preserves exactly the
solutions capable of improving the incumbent. An `optimal store` result must
include both satisfaction and the theorem that no satisfying store has a
better objective; interrupted optimization must return a feasible incumbent
with status `unknown`, not claim optimality.

#### 6.8 Validate and measure incrementally

- Differential-test the reference and optimized Lean solvers on exhaustively
  generated small finite models.
- Feed every produced solution through `checkSolutionFull`.
- Compare SAT/UNSAT results and solution sets with Gecode and Sabori on the
  common supported fragment.
- Add one benchmark per solver layer: raw enumeration, propagation, reversible
  state, heuristic selection, NoGoods, and restarts.
- Track nodes, propagations, failures, peak memory, and elapsed time separately
  so heuristic gains are not confused with stronger logical propagation.
- Preserve a slow proof-oriented mode with deterministic choices, even after
  a faster heuristic engine becomes the default.

#### Status (final)

All of 6.1–6.7 is implemented, proved, and tested:

- **6.1 (contract)** — `SolveResult` (sat/unsat/unsupported) and the four
  theorem shapes of 6.1: SAT soundness, UNSAT soundness, completeness half
  (through the `search_some`/`search_none` master theorems), termination
  (the slots measure); the resource-limited `unknown` verdict is delivered
  by `BoundedResult` (`solver/Restarts.lean`) and `ConfigResult`
  (`solver/Config.lean`).
- **6.2 (reference solver)** — `solveModel`: slot extraction
  (`varDomain_values_iff` ties the searched values to the declared
  domains), exhaustive `search`, leaf checking through the verified front
  door, emission in the checker's format.  Master theorems:
  `solveModel_sat_sound`, `solveModel_unsat_sound`.
- **6.3 (propagation)** — the `Preserves` contract and the four
  propagators (`propEqSlot`, `propNeSlot`, `propLeSlot`,
  `propConstEq`); the fuel-bounded fixpoint with conjunction-stable
  composition (`fixpointFuel_narrowed`/`_contradicts`); the pruning
  search (`prunedSearch_some`/`prunedSearch_none`); constraint
  extraction from model shapes (`extractConstraints`, with the
  store-level bridge lemma `extractConstraints_holds`); and the
  integrated entry point `solveModelProp` (SAT soundness
  unconditional; UNSAT soundness under the documented pruning
  licence).
- **6.4 (reversible state)** — sparse-set domains with a trail
  (`solver/RevState.lean`): `SparseDom`/`revGet` logical views,
  `sparseNarrow_spec`, the trail guarantee `revBacktrack_recovers`,
  and the propagation-pass refinement `revPropPass_refines` (one
  round-robin pass on the sparse state computes the same logical
  domains as the list-level `propPass`).  The propagation queue and
  watched constraints remain future work.
- **6.5 (MRV ordering)** — `mrvOrder`/`mrvSearch` with the
  branch-coverage lemma, and the integrated entry point
  `solveModelHeur` (both master theorems unconditional).
- **6.6 (learning and restarts)** — NoGood learning
  (`solver/Learning.lean`): the clause semantics
  `NoGood.Violated`/`violatedB_iff`, the scope-limited entailment
  `NoGood.EntailedOn`/`EntailedAt`, the agreement theorem
  `nogoodSearch_agrees`, the subtree entailment
  `failedSubtree_entailed`, and the loop `learnSearch` with
  `learnSearch_some`/`learnSearch_none` (unconditional).  Restarts
  (`solver/Restarts.lean`): `searchBudget` (found/exhausted/budgetOut
  with `searchBudget_search`, `searchBudget_monotone`), the restart
  loop `restartSearch` with `restartSearch_sat_sound` /
  `restartSearch_unsat_sound` / the safety theorem
  `restartSearch_never_falseUnsat` / the fair-schedule half
  `restartSearch_complete`, and the entry point `solveModelBounded`
  with all three theorems transferred.
- **6.7 (enumeration and optimization)** —
  `enumerateAll`/`enumModel` with the membership, completeness, UNSAT,
  and distinctness theorems; optimization via `optimizeModel`
  (reference) and `optimizeModelBb` (branch and bound), each with the
  four theorems (SAT soundness, optimality, UNSAT, value) and the
  agreement corollary `optimizeModelBb_agrees`
  (`solver/Optimize.lean`).
- **Final integration** — the composed front door `solveModelWith`
  (`solver/Config.lean`): `SolveConfig` (`useProp`/`useMrv`/`budget`/
  `nogoods`) dispatches to the proven entry points plus two glue
  entry points proved there — `solveModelPropMrv` (propagation +
  MRV by permutation composition, the bridge being
  `permConstraint_satisfiedBy_iff`) and `solveModelLearn` (NoGood
  learning).  Theorems: `solveModelWith_sat_sound` (the full
  supported config space, unconditional), `solveModelWith_unsat_sound`,
  and `solveModelWith_budget_never_falseUnsat`.  The supported matrix
  is each switch alone plus prop+mrv together; other combinations are
  returned `.unsupported` with a reason.

Future work: watched-literal NoGood propagation, queue-based
propagation, learned-fact retention across restarts, objective-shape
extension beyond slot-level literals/identifiers, one-hot
presolve rewrites, and optimization over initializer-derived stores
versus search slots.  The string round-trip step of the propagation
UNSAT licence (`completedStore` opacity) and the differential
testing of 6.8 against external solvers also remain.  (The CLI
exposure of the solver is DONE: `leanfzn solve`/`enum`/`optimize`
subcommands ship, with the `--prop`/`--mrv`/`--budget`/`--nogoods`
config switches.)

## Performance worklog (IDEAS_FOR_IMPROVING_PERF.md progress)

This section tracks the state of `IDEAS_FOR_IMPROVING_PERF.md`
(see that file for the ideas, numbering, and the order of attack).
Everything below is landed, compiles, and is covered by the
regression suites; the master theorems' statements are unchanged
throughout, and `#print axioms` on every touched theorem still
reports only `propext`, `Quot.sound`, and `Classical.choice`.

### Compilation-time work (Lean elaboration speed)

Diagnosis method: `lake env lean --profile` per module, bisection
of slow files, scratch-file measurement of proof recipes.

- **Per-name agreement theorems** (the `fzn_<name>_iff` family and
  the set-predicate theorems): the leading
  `simp only [<interp>, <interp>B]` normalized the entire name-
  dispatch match of both functions per theorem (up to ~13-16 s of
  `simp` time each, ~60 sites).  Replaced with one-case `have ... :=
  fun _ => rfl` iota-reductions plus `rw` (validated recipe; the
  statements are untouched).
  - `LeanFzn/FznSolution.lean`: 25.2 s → 11.2 s elaboration.
  - `LeanFzn/FznGlobals/Counting.lean`: 12.6 s → 5.1 s.
  - Graph 5.3→2.8, PackSched 4.3→2.9, SetMath, LexSort, Channeling,
    Sched2, LexChain similarly improved.  Regular and
    AllDiffCounting were already under threshold and skipped.
- **`LeanFzn/FznGlobals.lean`**: 58 s → 33.6 s elaboration.
  - The ten family dispatchers `globalsInterpB_<fam>_iff`: the
    quadratic `all_goals first | exact ...` chains (≈9.6k `exact`
    attempts) became `all_goals simp only [per-name lemmas]`.
  - `old_not_new`: the 6-way rcases + per-name `decide` (~13 s)
    became pure plumbing through the `X_not_other` bundles.
  - `dispatchList_nodup_fst`: one 217-element kernel string-`Nodup`
    `decide` (~26 s; kernel string Nodup is quadratic) decomposed
    into ten per-family `Nodup` decides + the existing disjointness
    lemmas (`fams_disj`, `globalsNames_nodup`,
    `fullCheckableNames_nodup`); the `set_option maxRecDepth` bump
    was removed.
  - `std_set_not_global`: the two `filter = []` decides (~8 s)
    replaced by reuse of `std_name_not_global` (identical
    statement).
  - The 43 pairwise disjointness lemmas `X_not_Y` were measured
    (compact form tried, no win) and left as they are.
  - A recipe that regressed (kept OUT): per-family `have/rfl`
    reduction lemmas + `rw` for the master `globalsInterpB_iff`
    (kernel `rfl` re-evaluates the membership chains; ~60 s vs 31 s
    for the existing shape).

### Solver-performance work (IDEAS items)

- **Item 1.1 (PreparedModel leaf)** — already done before this
  pass (`solveLeafP`, `solveLeafP_eq`; 11-13x on constraint-heavy
  leaves).
- **Item 1.2/1.4/1.6, item 1.3, and the 4.1/4.5 accumulator work**
  — already done before this pass: `propEqSlot`/`propLeSlot`
  single-intersection forms, hoisted slot projections,
  `emitSolutionFast` accumulator twin (`emitSolutionFast_eq`),
  `unpermuteFast`/`unpermuteI`, `searchGo`/`searchImpl`
  reversed-accumulator twin (`searchGo_search`, `searchImpl_eq`,
  `implemented_by searchImpl`), `enumFast` double-accumulator
  enumeration twin (`enumGo_enum`, `enumFast_eq`,
  `implemented_by enumFast`), hash-counted `dedupTexts`
  (`dedupTexts_eq`).  Verified this pass: all bridges compile,
  axioms clean, behavior unchanged.
- **Item 3 (incremental store per leaf)** — **done this pass**
  (`LeanFzn/FznCheck.lean`): `PreparedStore` (pre-inserted
  parameter map + initializer-only completion plan + fuel) as a
  new `PreparedModel.store` field; `completedBoxPrepared`
  (logical body literally `completedBox p.model es`, so
  `completedBoxPrepared_eq` is `rfl`;
  `@[implemented_by completedBoxPreparedI]` runs the k-entry
  inserts + filtered completion walk) with the plan lemmas
  `completePass_step_none`, `completePass_filter_eq`,
  `completeFix_filter_eq`.  The dynamic half `checkPreparedDyn`
  runs through it, and every existing theorem
  (`checkPreparedSolution_eq`, `checkModelSolution_correct`,
  `solveModel_sat_sound`, `solveModel_unsat_sound`) transferred
  with zero proof edits.  Measured on the interpreter:
  parameter-heavy dynamic check 1455 ms → 327 ms (4.5x), store
  build alone 6.8x.
- **Item 2 (emit/parse round-trip theorem)** — **layer 1 COMPLETE**
  (`solver/Emit.lean`): the byte-position dictionary
  (`byteLenL`, `utf8GetAux_appendIn`, `get/next/atEnd/extract`
  append laws), the boundary position lemmas
  (`get_ofList_at`, `atEnd_ofList`, `next_ofList_at` + slice
  transfers), the `Pos.Raw.extract` characterization
  (`extract_ofList_seg`/`extract_slice` through the `go₁`/`go₂`
  inductions), the shift lemmas (`get/atEnd/next_ofList_shift`),
  the split correspondence `splitAux_spec` (splitting
  `ofList (pre ++ seg ++ rest)` yields exactly the char-level
  `List.splitOnP` splits through `ofList`), the single-char-separator
  bridge `splitOnAux_eq_splitAux` (functional induction over
  `splitOnAux`), the master bridge `splitOn_eq_list`
  (`s.splitOn (ofList [c]) = (s.toList.splitOn c).map ofList`),
  and **the `splitOn "\n"` intercalate law**
  (`splitOn_intercalate_newline`: splitting the `"\n"`-intercalation
  of `'\n'`-free nonempty lines recovers the lines) — the first of
  the two open layers, proven.  All compiling, zero `sorry`, axioms
  clean (`propext`/`Quot.sound`/`Classical.choice` only).
  The remaining layers: the master theorem
  `parseSolution (stripSeparators (emitSolution ps)) = ...` and the
  string-free leaf wiring (item 2's runtime win not yet realized).
  **Lexer cons law (layer 2) — WITHDRAWN (2026-09-19 audit)**: the
  previously-claimed-complete cons-law stack
  (`lexToken_append_left'`, `tokenizeAux_append_right_ok`,
  `split_helper`, `walk_nl_eq_walk_t`, `tokenize_cons_newline`,
  `tokenize_cons_newline_full`, …) is **vacuous**: its `htw`
  scan premises (`∀ p q, pos ≤ q → (takeWhile p s q "").2 <
  s.size`, and the all-`q` variant) are UNSATISFIABLE —
  `takeWhile p s s.size "" = ("", s.size)` stops *at* the
  past-the-end position, so instantiating at `q = s.size`
  derives `False` (the all-`q` variant forces `s.size = 0`).
  Those lemmas are true but never applicable; the "COMPLETE"
  status is retracted (the proofs stand, the applications do
  not exist).  The honest repair landed the same day:
  `takeWhile_append_of_tail_fail` (scan agreement when every
  tail char fails the scan predicate — axioms
  `[propext, Quot.sound]`), the packaged `noScans t` premise
  (all four lexer scan predicates fail on every tail char),
  `takeWhile_noScans`, and the boundary instances
  (`boundary_noScans_semi/space/eq/nl/wsEq` — `;`, ` `, `=`,
  `\n` all fail all four predicates by `decide`).  The
  walk/token-level cons laws still need restatement on this
  foundation (see the remaining-work notes).  KEY SEMANTIC FACT
  (still valid, from the earlier pass): `lexToken`'s error
  MESSAGES embed the absolute position, so tail laws must be
  stated success-transport only — the tokenizer's downstream
  ignores messages, so this is the honest statement.

### Remaining work on IDEAS_FOR_IMPROVING_PERF.md

In the doc's own order of attack, with current status:

1. **Item 2, finish**: the `splitOn "\n"` intercalate law is
   PROVEN (`splitOn_intercalate_newline`, through
   `splitOn_eq_list`/`splitOnAux_eq_splitAux`/`splitAux_spec` and
   the byte dictionary — all in `solver/Emit.lean`).  The lexer
   cons law `tokenize (s ++ "\n" ++ t)` is **WITHDRAWN
   (2026-09-19 audit)**: the previously proven stack
   (`tokenize_cons_newline_full` via `split_helper`,
   `tokenizeAux_append_right_ok`, `walk_nl_eq_walk_t`, …) rests
   on the unsatisfiable `htw` scan premises — see the worklog
   entry above; the lemmas are true but vacuous (never
   applicable).  The honest foundation is landed
   (`takeWhile_append_of_tail_fail`, `noScans`, and the boundary
   instances — axioms clean); the **token-level agreement layer
   is rebuilt on it** (commit `286c02e`: `lexUnsigned_prefix_congr`,
   `lexUnsigned_left_of_noScans`, `lexInt_left_of_noScans` — all
   axiom-clean with satisfiable premises).  The walk-level cons
   law, the `lexToken` agreement on `noScans` (the 13-branch
   token walk, mirrors `lexToken_append_left'` but on the honest
   premises), and a `tokenize_cons_newline` restatement remain
   to be rebuilt on it (the `lexUnsigned` hex/octal arm needs
   an `'x'`/`'o'` lookahead exclusion premise mirroring
   `lexToken_append_left'`'s `':'`/`'.'` one, since a `'0'` at
   the very end of `s` with `'x'` heading `t` would extend the
   prefix check on the joined side only).  **The identifier half
   is PROVEN** (`tokenize_ident`
   in `solver/Emit.lean`: `tokenize (String.ofList l)
   = .ok #[.ident (String.ofList l)]` for nonempty `l` whose
   head is alpha/`_`, all chars ident chars, not keyword,
   not reserved — built on the list/array bridges
   `list_toArray_size`, `cons_toArray_read`,
   `takeWhile_cons_shift` (via `List.toArray_cons` +
   `takeWhile_append_right`), `takeWhile_list_all` (the
   induction over `takeWhile isIdentChar`), the char-class
   exclusions `isAlpha_not_ws`/`isAlpha_not_pct`,
   `skipTrivia_ident_head`, and `lexToken_ident`; axioms
   clean).  **The value half is PARTIALLY PROVEN**: the Boolean
   half is complete (`tokenize_bool` via `tokenize_keyword`, the
   keyword companion of `tokenize_ident`), together with the
   decimal-digit characterization of `Nat.toDigits`
   (`toDigits_digit`/`toDigits_isDigit`/`toDigits_nonempty`,
   `digitChar_isDigit`, `isDigit_not_ws`/`isDigit_not_pct`/
   `isDigit_not_alpha`, `takeWhile_digits_all`); the integer
   half's master assembly (`tokenize_int_nonneg`: wiring the
   scan facts through `lexInt`'s decimal branch and `repr_val`)
   is now PROVEN — see `solver/Emit.lean` (2026-09-18): the
   supporting stack is `digit_not_xo`/`digit_not_minus`/
   `isDigit_not_underscore` (the char-class exclusions),
   `lexUnsigned_decimal` and `lexInt_nonneg_head` (the decimal
   arm on all-digit input), `takeWhile_digits_end` (the scan
   runs to the end), `lexToken_digits` (the digit-head token
   pair), and `tokenizeAux_stop` (the past-end walk stop).
   Remaining in item 2: **the negative-`Int` half is PROVEN**
   (2026-09-18/19 — `tokenize_int_negsucc` in `solver/Emit.lean`,
   via `lexInt_neg_head` (the `-`-prefixed head dispatch),
   `lexUnsigned_decimalTail` and `takeWhile_digits_endTail`
   (the decimal-arm agreement after the sign), see the worklog
   below); **the strip layer is PROVEN** (2026-09-19 —
   `stripSeparators_emitSolution`, closing the last two proof
   holes of the emit-side stack; the `startsWith` transparency
   blocker was passed not by kernel-decoding the searcher but by
   the semantic route: `String.Slice.startsWith_string_iff` +
   the full-range copy bridge `toSlice_copy`
   (`ByteArray.extract_zero_size` + proof-irrelevance via
   `string_eq_of_ba`) give `startsWith_iff_isPrefix`, and the
   head-mismatch consequence `startsWith_eq_false_of_head` with
   `ident_head_not_sep` drive the filter-safety side; the
   theorem needed a strengthened hypothesis — identifier-start
   name heads, since `'\n'`-freedom alone admits a ten-dash
   name; all axiom-clean, no `decide +kernel` needed).  The
   remaining master theorem
   `parseSolution (stripSeparators (emitSolution ps)) = …` and
   the string-free leaf wiring remain.
2. **Item 5, more propagators** — **the linear family is
   COMPLETE** this pass: `propLinEq_preserves` and
   `propLinLe_preserves` are fully proven (all three
   obligations: narrowing soundness through the master
   induction `linNarrowAll_mem`, subset through
   `linNarrowAll_subset`, and contradiction soundness through
   the new `lin_head_filter_pass` — the factored interval
   derivation — plus the first-contradiction run analysis with
   `dotProduct_mismatch` for the shape-mismatch arm).  The
   propagators are WIRED into `domPropagators` (no more
   `propIdSlot` placeholder for the linear kinds), the shape
   check `coeffs.length = is.length` returns sound
   `.contradiction` on mismatch, and the CLI's
   `solve --prop` demonstrably prunes with them (verified:
   linear models solve and UNSAT linear models refute).
   Supporting lemmas all proven, zero `sorry`, axioms clean:
   `others_bound` (the filter-soundness core),
   `LinSat_cons` (the head-transport),
   `linTotal_split` (prefix+suffix extrema decomposition),
   `linExtract_length`, `linExtract_cover`,
   `dotProduct_some_int` (integrality from a successful dot
   product), `dotProduct_mismatch`,
   `linNarrowAll_subset`, `getSlot_eq_nil`,
   `mem_of_assign`.  **COMPLETE (follow-up passes)**: the
   `Extract.lean` extraction for `int_lin_eq`/`int_lin_le` and
   the extension families — `int_times`/`int_min`/`int_max`
   (ternary slot arithmetic), `int_abs`, `int_lt` (slot-slot and
   both literal directions), `bool_not`/`bool_and`/`bool_or`
   (Boolean connectives) — each with its `Preserves` theorem,
   extraction cases, permutation support in
   `solver/Config.lean`, and regression tests (109 propagator
   tests); the `all_different` pigeonhole counting propagator
   (`propAllDiff` + `allDiff_pigeonhole`) was already in place
   and is covered.
3. **Item 6.1/6.4**: the combined propagation+MRV entry point is complete
   (`solveModelPropMrv`); value ordering toward the objective for B&B remains.
4. **Item 4.5 streaming**: `optPairs` fold with running best
   (extremal-value membership theorem), replacing the
   materialize-all-assignments path; `solver/Restarts.lean`'s
   `searchBudget` still uses `acc ++ [v]` per node (the
   `searchGo` pattern applies verbatim).
5. **Item 4.3 RevState wiring**: close the remaining proof
   obligations and wire the sparse-set search (the 6 `sorry`s the
   doc mentions were already closed; what remains is the
   trail-integrated search + the refinement theorem connecting it
   to `prunedSearch`, per the module docstring).
6. **Item 7.1 single-pass B&B** and **item 8 event-driven
   propagation** (watch lists) — the sabori-class wins.
7. **Item 10**: `SolverStats` counters (nodes, propagations, leaf
   checks, store builds) for machine-independent measurement of
   the above.

### Engineering notes from this pass

- **2026-09-19 — VACUOUS-PREMISE AUDIT of the lexer cons-law
  stack** (IDEAS item 2): while assembling the entry-line tokenize
  round-trip, the `htw` scan premises of the (previously claimed
  COMPLETE) cons-law layer were found **unsatisfiable**:
  `takeWhile p s s.size "" = ("", s.size)` (the past-the-end
  `dif_neg` arm) means `∀ p q, pos ≤ q → (takeWhile p s q "").2 <
  s.size` derives `False` at `q = s.size` whenever `pos <
  s.size`, and the all-`q` variant forces `s.size = 0`.
  Affected (proven, axiom-clean, but never applicable):
  `lexUnsigned_append_left`, `lexInt_append_left`,
  `lexToken_append_left(_')`, `lexToken_append_right_ok`,
  `lexInt_append_right_ok`, `tokenizeAux_append_right_ok`,
  `walk_nl_eq_walk_t`, `split_helper`, `tokenize_cons_newline(_full)`.
  NOT affected (single-position premises):
  `takeWhile_append_left`, `skipTrivia_append_left/right`,
  `skipToNewline_append_right`, `takeWhile_append_right`,
  `tokenizeAux_skip_eq`, `skipTrivia_fixpoint`,
  `tokenizeAux_acc_append`, `tokenizeAux_exit_tail`, `skip_exit_join`.
  **Root cause**: "every scan the walk takes stops inside `s`"
  was stated with `q` quantified over ALL positions, including
  past-the-end ones where the scan trivially stops AT them.
  **Honest repair landed** (axioms `[propext, Quot.sound]`):
  `takeWhile_append_of_tail_fail` — scan agreement across a join
  whenever every tail character fails the scan predicate (then a
  scan that reaches `s.size` stops there on `s ++ t` too) —
  plus `noScans t` (all four lexer scan predicates fail on
  every tail char), `takeWhile_noScans`, `joined_read_past`
  (the prim-read bridge past the join), and the decided
  boundary instances (`boundary_noScans_semi/space/eq/nl/wsEq`).
  PLAN.md's earlier "lexer cons law COMPLETE" claims are
  retracted above; the withdrawn proofs remain in the file
  (harmless, but flagged as vacuous in the layer note).
  **Lesson recorded in repo memory**: quantify scan-stop premises
  over positions the walk actually visits, or state them as
  tail-character failures.
  **Progress on the honest replacement** (commit `286c02e`): the
  token-level agreement layer is rebuilt on `noScans` —
  `lexUnsigned_prefix_congr` (the hex/octal two-char lookahead
  agreement under a lookahead-exclusion premise; axioms
  `[propext, Quot.sound]`), `lexUnsigned_left_of_noScans` (the
  full `lexUnsigned` agreement: three scan arms +
  two prefix conditions), and `lexInt_left_of_noScans` (with the
  honest `hnonlastdash` premise: a `-` head never ends `s`, since
  emitted literals carry their digits).  All premises are
  satisfiable for the entry-line application (boundary chars
  `;`/` `/`=`/`\n` fail all four scan predicates and are never
  `x`/`o`/`:`/`.`).  **Next on item 2**: `lexToken_left_of_noScans`
  (the 13-branch token agreement — the `':'`/`'.'` lookahead
  mirrors `lexToken_append_left'`'s, the ident/int arm uses
  `lexInt_left_of_noScans` + `takeWhile_noScans`), then the
  walk-level cons law and the entry-line theorem
  `tokenize (emitEntry nm v) = #[ident nm, eq, literal, semi]`.

- **2026-09-19 — the `startsWith` strip layer unblocked and
  complete** (IDEAS item 2): `stripSeparators_emitSolution` is
  fully proven (0 sorries, axioms
  `[propext, Classical.choice, Quot.sound]`), closing the last
  two proof holes of the emit-side round-trip stack.  The
  blocker (documented in `solver/Emit.lean`'s strip-layer note):
  Lean 4.33's `String.startsWith` chains through
  `String.Slice.Pattern.ForwardPattern` instances whose
  `memcmpStr` recursion neither `rfl`/`decide`/`simp` (elaborator
  `whnf` does not run it) nor the banned `native_decide` could
  close even on literals.  TWO candidate escapes were probed:
  `decide +kernel` (the kernel *does* evaluate the searcher — it
  proves the three literal separator facts axiom-cleanly, and a
  `startsWith_short` size-guard lemma was proven through the
  searcher's `dif_pos` arm), and the eventually-used **semantic
  route**: core's `String.Slice.startsWith_string_iff` says
  `s.startsWith pat = true ↔ pat.toList <+: s.copy.toList`, and
  the `copy` conversion is discharged once by the new bridge
  `toSlice_copy` (a full-range slice copy is the string itself:
  `ByteArray.extract_zero_size` at the byte level, packaged via
  `string_eq_of_ba` — strings with equal `toByteArray` are equal,
  so the UTF-8 side condition is proof-irrelevant).  The result:
  `startsWith_iff_isPrefix` (the workhorse frame),
  `startsWith_eq_false_of_head` (a head mismatch kills a prefix
  — the entry-side mismatch: an entry line's head char is the
  name's head char, an identifier start via `ident_head_not_sep`
  never `'-'`/`'='`/`'%'`), the three literal facts
  (`sep_starts_sep` by the identity prefix `⟨[], rfl⟩`,
  `sep_starts_eqs`/`sep_starts_stat` by head chars), and
  `emitEntry_head_eq_name_head`/`emitEntry_not_sep` (the
  `name = value;` shape is a flat append starting with the name).
  Consequence for the statement: the theorem needed a
  **strengthened hypothesis** — identifier-start name heads
  (∃ head char, alpha or `_`) alongside the `'\n'`-freedom, since
  `'\n'`-freedom alone admits e.g. a ten-dash name whose entry
  line would genuinely start with the separator.  Validated:
  `lake build` green, all 22 test suites green (smoke 30,
  stdlib 64, solution, gecode 64, globals 52, coverage 465,
  wellformed 49, pretty 39, check 12, solver 198, prop 109,
  heur 93, fast 7, fix 21, enum 31, sbench 4, opt 73, rev 26,
  learn 37, restart 26, bench, prof), CLI sanity (`leanfzn
  solve` on a 1-var model), and `#print axioms` clean on the
  whole new stack.  What remains for item 2 is the parse side:
  the line-level entry round-trip through `parseEntry` and the
  master `parseSolution` assembly, then the string-free leaf
  wiring (Step 3 of the agreed plan).

- All timing measurements use `lake env lean <file>` (elaboration
  against existing oleans; does not touch the build state).  The
  resource discipline: one lean process at a time, hard-capped.
- The final state was validated with `lake build` (155 jobs, all
  targets incl. every test executable) and the full test suites
  (smoke 30, stdlib 64, solution, gecode 64, globals 52, coverage
  465, wellformed 49, pretty 39, check 12, solver 198, prop 86,
  heur 93, fast 7, fix 21, enum 31, sbench, opt 73, rev 26, learn
  37, restart 26, bench, prof) plus the CLI (`leanfzn solve` +
  `leanfzn check`) — all green.
- Scratch/probe files (`probe*.lean`, `BenchAB.lean`,
  `TestEnumTmp.lean`, `axcheck_tmp.lean`, `mini.lean`,
  `testBX.lean`) are untracked development artifacts, not part of
  any build target.

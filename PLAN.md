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

This is the authoritative list of open work as of 2026-09-20.  The detailed
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
  The segment layer now covers nonnegative integers, negative integers, and
  Booleans (`lexToken_int_segment`, `lexToken_neg_segment`, and
  `lexToken_bool_segment`). The complete nonnegative four-token walk is
  proved by `tokenizeAux_entry_line`, and `tokenizeAux_entry_line_gen`
  factors out the common identifier/`=`/literal/`;` walk for the remaining
  literal forms. The next step is to instantiate that generic walk for
  Boolean and negative literals and reduce the resulting four-token arrays
  through `parseEntry`.
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
literal segment and entry-walk layers (P0.6/P0.7:
`lexInt_nonneg_segment`, `lexToken_int_segment`, `lexInt_neg_segment`,
`lexToken_neg_segment`, `lexToken_bool_segment`, `tokenizeAux_entry_line`,
`tokenizeAux_entry_line_gen`, `entry_lit_head_read`, and
`entry_lit_drop`/`entry_lit_drop_rest`). The isolated
`solver.Emit.Roundtrip` module currently builds successfully.

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

### P4 — Simplify the module structure

These are documentation-backed refactoring candidates, not authorization to
change theorem statements or move code while P0 is active.  Do them in small,
build-checked steps after the emitted-solution round trip is complete.

- [ ] Resolve the two solver roots.  Today `solver.lean` imports only
  `Search`, `Domain`, `Emit`, and `Solve`, while `solver/Solver.lean` is the
  actual whole-stack umbrella used by the CLI and most tests.  Either make
  `solver.lean` the single public umbrella or rename/document it explicitly as
  a core-only root; avoid two files that both appear to mean “the solver”.
- [ ] Replace broad `import LeanFzn` dependencies in foundational solver
  modules (`Domain`, `Propagators`, `Fixpoint`, `Extract`, `Learning`, and
  `RevState`) with the smallest stable submodule imports.  Measure clean and
  incremental elaboration before and after each change.
- [x] Split `solver/Emit.lean`: executable emission and its accumulator proof
  live in stable `solver/Emit/Basic.lean`, while the evolving lexer/parser
  proof stack lives in `solver/Emit/Roundtrip.lean`.  `solver/Emit.lean`
  remains the stable public emission module and intentionally does not import
  the unfinished proof stack; the solver stack imports only `Basic`, so
  round-trip work does not recompile unrelated solver code.
- [ ] Separate generic search/propagation machinery from the FlatZinc-facing
  adapter currently concentrated in `solver/Solve.lean`; keep model
  extraction, checker integration, and emitted-text results at the boundary.
- [ ] Narrow test imports where a suite exercises only one layer.  Most solver
  tests currently import `solver.Solver`, forcing the entire stack into every
  test build; use the complete umbrella only for integration/configuration
  tests.
- [ ] Review the global-constraint dependency spine.  In particular,
  `FznGlobals/Common.lean` imports the full solution checker and therefore
  pulls parsing/checking into every global family.  If its helpers need only
  semantic types and Boolean agreement utilities, extract a smaller common
  foundation without changing the frozen predicate semantics.
- [ ] Generate `code-structure.md`'s direct-import inventory from source (or
  validate it in CI) so the dependency document cannot silently drift.

**Exit criteria:** one clearly documented public root per library, no
accidental umbrella imports in low-level modules, smaller incremental rebuild
cones demonstrated by measurements, and no changes to public results or
axiom profiles.

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
existing library and solver roots are documented, the documentation reflects
the current tree, and the build is warning-free.  Consolidating the two
solver-root conventions is tracked separately under P4.  The clean-checkout
build is currently validated manually; automating it is tracked under P2.

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

### 6. Verified constraint solver — complete baseline

The completed solver architecture, algorithms, and theorem inventory now live
in the README under **Verified finite-domain solver**.  This plan tracks only
the remaining solver work: P0 closes the emitted-solution round trip, P1 adds
the verified fast-state machinery, and P2 adds differential validation and
measurement.

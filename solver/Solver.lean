import LeanFzn
import LeanFzn.FznCheck
import solver.Search
import solver.Domain
import solver.Emit
import solver.Solve
import solver.Heuristic
import solver.Propagators
import solver.Fixpoint
import solver.Enum
import solver.Extract
import solver.Optimize
import solver.RevState
import solver.Learning
import solver.Restarts
import solver.Config

/-!
# Verified FlatZinc constraint solver (PLAN.md item 6)

This library implements a finite-domain satisfaction solver for the
LeanFzn fragment: integer and Boolean variables, the standard
predicates, and the `fzn_*` global constraints with verified
interpretations.  The stack of PLAN 6.1–6.7 is complete and
integrated; every executable step carries a theorem connecting it to
LeanFzn's declarative semantics, and the sources contain no admits
or placeholders.

## The stack (PLAN 6.1–6.7)

* `solver/Search.lean` (PLAN 6.1, 6.2) — the generic exhaustive
  reference search with the master soundness/completeness theorems
  (`search_some`, `search_none`) connecting the executable search to
  the declarative specification `allAssigns`; termination by the
  slots-measure argument of PLAN 6.1.
* `solver/Domain.lean` (PLAN 6.2) — finite-domain extraction from a
  parsed model (`modelSlots`/`slotsChecked`): the search slots are the
  initializer-free basic variables, whose candidate values are proved
  (`varDomain_values_iff`) to be exactly the declared domains, with
  the per-variable and total-leaf caps (`domainCap`, `leavesCap`).
* `solver/Emit.lean` (PLAN 6.2) — solution-text emission in the exact
  format the verified checker parses (`emitSolution`).
* `solver/Solve.lean` (PLAN 6.1, 6.2 + Round 3 integration) — the
  FlatZinc-facing entry points, all sharing the leaf-check
  architecture (every candidate leaf is validated by the verified
  checker itself, `solveLeaf`):
  - `solveModel` — the reference solver of PLAN 6.2, with the two
    master theorems of PLAN 6.1: SAT soundness
    (`solveModel_sat_sound`: a returned text is checker-accepted) and
    UNSAT soundness (`solveModel_unsat_sound`: an `unsat` verdict
    excludes every assignment of the slot domains);
  - `solveModelProp fuel` — the propagating solver of PLAN 6.3
    (`prunedSearch` over the extracted constraint set, with the
    empty-set uniformity making the no-extraction fallback the same
    code path), SAT soundness unconditional
    (`solveModelProp_sat_sound`), UNSAT soundness under the pruning
    licence (`solveModelProp_unsat_sound`, see below);
  - `solveModelHeur` — the MRV solver of PLAN 6.5 (`mrvSearch`:
    minimum-remaining-values branch order on an otherwise exhaustive
    partition), both master theorems unconditional
    (`solveModelHeur_sat_sound`, `solveModelHeur_unsat_sound`).
* `solver/Propagators.lean` (PLAN 6.3) — the propagation contract
  (`Preserves`: every satisfying assignment compatible with the input
  domains remains compatible with the narrowed domains, reported
  contradictions are sound, and domains only shrink) with the first
  propagators (`propEqSlot`, `propNeSlot`, `propLeSlot`,
  `propConstEq`), each carrying its preservation theorem.
* `solver/Fixpoint.lean` (PLAN 6.3) — the propagation fixpoint
  (fuel-bounded round-robin, preservation stable under conjunction:
  `fixpointFuel_narrowed` / `fixpointFuel_contradicts` and their
  P-generalized forms) and the pruning search that branches on the
  first undecided slot after propagation, with the master theorems
  `prunedSearch_some` / `prunedSearch_none` (the none-side under the
  leaf-implies-constraints licence, for every fuel).
* `solver/Heuristic.lean` (PLAN 6.5) — correctness-neutral search
  heuristics as permutation composition with the proved reference
  search: the branch-coverage lemma `unpermute_mem_allAssigns_iff`,
  `heuristicSearch` with its master theorems, and the MRV selector
  `mrvOrder` (admissible by `mrvOrder_isPerm`).
* `solver/Extract.lean` (PLAN 6.3 integration) — constraint
  extraction for propagation: `extractConstraints` scans the model's
  constraints for the shapes the phase-1 propagators understand
  (`int_eq(x, y)` → `eqSlot`, `int_ne` → `neSlot`, `int_le(x, y)` →
  `leSlot`, `int_eq(x, c)` → `constEq`, `int_le(x, c)` /
  `int_le(c, x)` → `leConstHi` / `leConstLo`, `int_plus(x, y, z)` →
  `plusSlot`, `all_different([x₁, …, xₘ])` → `allDiff`, at slot
  indices against `slotsChecked`), skipping every other shape (the
  propagation set is
  a subset; the leaf check still enforces everything).  The bridge
  lemma `extractConstraints_holds` proves — unconditionally, at the
  store level — that a store satisfying the model's constraints under
  `fullInterp` (the constraint half of what
  `checkModelSolution_correct` certifies for every accepted solution)
  and agreeing with the assignment at the slot names satisfies every
  extracted constraint.
* `solver/Enum.lean` (PLAN 6.7, part 1) — the all-solutions
  enumerator `enumerateAll` (the membership theorem
  `enumerateAll_mem_iff_root` gives satisfaction and completeness in
  one iff; `enumerateAll_nodup` distinctness under duplicate-free
  domains) and the FlatZinc-facing `enumModel` with
  `enumModel_sat_sound` / `enumModel_complete` / `enumModel_unsat` /
  `enumModel_nodup`.
* `solver/Optimize.lean` (PLAN 6.7, optimization half) — the two
  optimizers over the same leaf-check architecture and gates:
  `optimizeModel`, the reference optimizer (enumerate all accepted
  assignments once via `enumerateAll`, then pick the best objective
  with the proved-minimal fold `pickBest`), and `optimizeModelBb`,
  the improving-bound refinement (rounds of `search` with the leaf
  strengthened by the incumbent's value, `bbLeaf`; the first round
  uses the plain satisfaction leaf, a later empty round certifies
  optimality via `search_none`, fuel-bounded rounds with a
  full-enumeration fallback).  The objectives are evaluated at slot
  level (`slotObjective`: integer literals and integer-valued search
  slots; other shapes are refused as unsupported).  Both entry
  points carry the same unconditional master theorems:
  `optimizeModel_sat_sound` / `optimizeModelBb_sat_sound` (the
  returned text is checker-accepted),
  `optimizeModel_optimal` / `optimizeModelBb_optimal` (no accepted
  assignment has a better objective), `optimizeModel_unsat` /
  `optimizeModelBb_unsat`, `optimizeModel_value` /
  `optimizeModelBb_value`, and the agreement corollary
  `optimizeModelBb_agrees`.
* `solver/RevState.lean` (PLAN 6.4) — the sparse-set reversible
  state refining this list-of-lists representation: `SparseDom`
  (array + window, logical view `sparseToList`), constant-time
  `sparseRemove`/`sparseRestore`, in-place `sparseNarrow` (proved to
  compute exactly the filter of the logical view), the solver-level
  `RevState` with `revGet` logical views, the trail
  (`revNarrowStep`/`revBacktrack`, with `revBacktrack_recovers`
  restoring every slot's view after any recorded narrowing
  sequence), and the round-robin `revPropPass` with
  `revPropPass_refines` (the pass on the sparse state computes the
  same logical domains as the verified list-level `propPass`, for
  every propagator list meeting the subset half of the `Preserves`
  contract).  The propagation queue and watched constraints of PLAN
  6.4 are future work; this is the sparse-set-with-trail core.
* `solver/Learning.lean` (PLAN 6.6, learning half) — decision-trail
  NoGood learning with the entailment discipline the plan demands:
  the declarative clause semantics (`NoGood.Violated` with the
  executable twin `NoGood.violatedB` and the agreement theorem
  `violatedB_iff`), the scope-limited entailments
  (`NoGood.EntailedOn`/`NoGood.EntailedAt`), the NoGood-checked
  search `nogoodSearch` with the agreement theorem
  `nogoodSearch_agrees` (entailed NoGoods change nothing
  semantically), the subtree entailment theorem
  `failedSubtree_entailed`, and the learning loop `learnSearch` with
  unconditional master theorems `learnSearch_some` /
  `learnSearch_none` (every learned NoGood is entailed by
  construction, via `learned_entailed`).
* `solver/Restarts.lean` (PLAN 6.6, restart half) — the
  resource-bounded `unknown` discipline: `searchBudget` (the reference
  search with a node budget; `exhausted` carries `search_none`'s
  complete-exhaustion certificate, a sufficient budget reproduces
  `search` exactly by `searchBudget_search`, and claims are monotone
  in the budget by `searchBudget_monotone`), the restart loop
  `restartSearch` (fresh root state each attempt) with
  `restartSearch_sat_sound` / `restartSearch_unsat_sound` / the
  safety theorem `restartSearch_never_falseUnsat` and the
  fair-schedule half `restartSearch_complete`, and the FlatZinc
  entry point `solveModelBounded` with all three theorems
  transferred (`solveModelBounded_sat_sound`,
  `solveModelBounded_unsat_sound`,
  `solveModelBounded_never_falseUnsat`).
* `solver/Config.lean` (final integration) — **the composed front
  door**: `SolveConfig` (`useProp`, `useMrv`, `budget`, `nogoods`)
  selects the features, and `solveModelWith cfg m` runs the composed
  combination, dispatching to the proven entry points (`solveModel`,
  `solveModelProp`, `solveModelHeur`, `solveModelBounded`) plus two
  glue entry points proved here: `solveModelPropMrv` (propagation +
  MRV, composed by permutation — the extracted constraints are
  re-indexed along the MRV order, the composition bridge being
  `permConstraint_satisfiedBy_iff`, and the leaf unpermutes before
  consulting the checker, `mrvLeaf`) and `solveModelLearn`
  (NoGood learning via `learnSearch`).  The result type
  `ConfigResult` makes PLAN 6.1's `unknown` verdict explicit
  (budgeted runs report "no claim" as `.unknown`, never as `.unsat`).
  The theorems: `solveModelWith_sat_sound` (SAT soundness for the
  full supported config space, unconditional — each path routes
  through its component's theorem), `solveModelWith_unsat_sound`
  (UNSAT soundness; the propagation paths carry the pruning licence
  below), and `solveModelWith_budget_never_falseUnsat` (the PLAN
  6.6 safety theorem at config level: a budgeted run on a model
  with an accepted assignment is never `unsat`).

## The supported configuration matrix

| `useProp` | `useMrv` | `budget` | `nogoods` | runs                       |
|-----------|----------|----------|-----------|----------------------------|
| false     | false    | none     | false     | `solveModel`               |
| true      | false    | none     | false     | `solveModelProp`           |
| false     | true     | none     | false     | `solveModelHeur`           |
| true      | true     | none     | false     | `solveModelPropMrv`        |
| false     | false    | none     | true      | `solveModelLearn`          |
| false     | false    | some b   | false     | `solveModelBounded` (schedule `[b/8, b/4, b/2, b]`) |

Every other combination is returned as `.unsupported` with a reason
(the search-stack features do not currently compose with budgets or
learning; composing them needs a shared search spine, future work).

## The documented scope restrictions

* `solveModelProp_unsat_sound`,
  `solveModelPropMrv_unsat_sound`, and the propagation paths of
  `solveModelWith_unsat_sound` carry the pruning licence
  ("every leaf-passing assignment satisfies every extracted
  constraint") as an explicit hypothesis.  Its store-level content is
  `extractConstraints_holds`; the one deliberately unproven step is
  the string round trip from the checker's acceptance of an emitted
  text to the completed store's slot-name values — `completedStore`
  is `opaque` by design (a compilation safeguard,
  `LeanFzn/FznSolution.lean`), so no lemma can see its content.  No
  executable path depends on that step: the SAT side of every entry
  point is unconditional, and every leaf is decided by the verified
  checker itself, so pruning can never produce an unjustified
  `sat`.
* The objective shapes of `optimizeModel`/`optimizeModelBb` are
  slot-level only (integer literals and integer-valued search
  slots; see the module docstring of `solver/Optimize.lean`).
* `RevState`'s propagation-pass refinement (`revPropPass_refines`)
  covers one round-robin pass; its integration into a full search
  loop, the propagation queue, and watched constraints are future
  work.
* The budget of `searchBudget` is depth accounting: one unit per
  nested recursive call along a branch (`searchNodes` is the proved
  sufficient budget), not wall-clock time or node counts.
* NoGood learning retains nothing across restarts (no
  learned-fact retention schedule) and NoGood propagation is
  full-list scanning, not watched literals.
-/

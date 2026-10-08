# Remaining work for the finite-domain solver

Updated: 2026-10-08. This plan lists remaining work; completed implementation
steps and historical task descriptions have been removed.

## Verified current basis

The public path is `Main → Direct.solveCertified → LCG.solve → lcgSearch →
chronologicalSearch → frontierSolve`. The frontier consumes pending alternatives
permanently and checks complete assignments against domains, constraints and
original clauses. `frontierSolve` has a two-constructor SAT/UNSAT result and
kernel-checked well-founded recursion using `frontierCost`. There is no runtime
search fuel. Coverage, SAT/UNSAT soundness, completeness and the source-entry
total-verdict theorem are present. Bounded APIs remain diagnostic references;
propagation and learning do not prune the public search.

The compiler no longer enforces `domainCap` or `leavesCap`. Integer ranges and
enumerated domains are extracted directly; `slotsChecked` delegates to
`declSlots`. Extraction faithfulness and compiler correspondence proofs remain
in place. Unsupported types and constraint shapes remain outside the accepted
fragment. Source correctness retains its well-formedness assumptions and
parameter honesty for UNSAT. Mathematical termination does not bound elapsed
time or machine memory; domains are still materialized as lists.

Fresh validation on 2026-10-08: aggregate build passed (213 jobs), the
identity-checked axiom audit passed all 66 profiles with standard axioms only,
and comment-aware proof-hole/user-axiom scans were clean. All 15 retained test
suites passed, including 93 solver tests, 117 LCG tests and 89 propagator tests.
The axiom queries were run with explicit `-j2` and their captured output checked
by the audit script; normal-invocation hardening is deferred below.

The top priority is an active lazy clause generation (LCG) solver that reduces
search through propagation and learned clauses. Full enumeration is a checked
reference implementation, not the intended final public algorithm. Former cap
thresholds are no longer meaningful development targets.

## Priority 1 — Put propagation and clause learning into the public solver

Files: `solver/LCG/Engine.lean`, `Propagate.lean`, `TrailEval.lean`,
`Frontier.lean`, their proof modules, `Search.lean`, `Certified.lean`, and
`solver/Direct/Cli.lean`.

### 1. Define the search state and coverage invariant

- Retain explicit bookkeeping for exhausted alternatives: an explored branch
  must never become pending again merely because a conflict causes a backtrack.
- Relate the trail, narrowed domains, original/learned clauses and pending
  alternatives to the original problem's solutions. Every possible solution
  must remain represented until a proved conflict excludes its branch.
- Use the existing fuel-free exhaustive traversal as reference semantics and
  a small-instance oracle. Do not make enumeration the normal public fallback.

### 2. Propagate before branching and prove safe pruning

- Run constraint and clause propagation on partial assignments, before choosing
  another decision. Preserve every solution compatible with the current frame
  when narrowing domains or enqueuing a consequence.
- Prove that reported conflicts exclude the affected branch before removing it.
  Reuse existing propagator proofs where their hypotheses match the new state
  invariant; identify and discharge missing refinement obligations explicitly.
- Define a terminating propagation closure using finite domain/trail progress
  and a worklist or equivalent checked mechanism. Repeated deductions must not
  produce an endless loop; no fuel cutoff may stand in for convergence.

### 3. Learn explained conflicts and backtrack without losing alternatives

- Repair explanations for singleton bounds obtained through value removals,
  using actual trail evidence. Resolve Boolean/int literal distinctions and
  clause-scan/conflict ordering before relying on first-UIP analysis.
- Prove learned clauses follow from the original problem. Global entailment
  and pivot membership alone do not justify enqueuing a non-unit clause member.
- Use learned clauses to propagate or prune subsequent branches. Prove asserting
  literal/unit conditions and show backjumps preserve every still-possible
  alternative while retaining the record of exhausted ones.
- Treat the historical analysis/flip loop as reusable components requiring
  repair and integration, not a complete optimized driver ready to reactivate.

### 4. Prove termination and connect the public correctness contracts

- Supply a well-founded progress argument for propagation, decisions, conflict
  handling, learning and backtracking. The raw frontier measure does not
  automatically cover transitions that add or revisit work.
- Preserve fuel-free termination, SAT soundness, UNSAT exclusion and completeness;
  transport the existing source-level theorems and parameter-honesty scope.
- Route `LCG.solve` and `Direct.solveCertified` through the proved pruning driver.
  No internal budget, arbitrary input cap or unknown-on-exhaustion fallback.

### 5. Verify actual search reduction

- Compare public-driver verdicts and SAT witnesses with the exhaustive oracle
  on small instances, retaining the 64 graph cases and pigeonhole regression.
- Collect decision, propagation, conflict, learned-clause and checked-leaf counts
  without using them to stop search. Require deterministic regressions showing
  propagation eliminates branches and learned clauses prevent repeated work.
- Test both SAT and UNSAT, including conflicts after value removals, repeated
  conflicts, backjumps and exhausted siblings. Validate emitted SAT solutions.
- Preserve source theorem applications, check the new proof chain's axioms,
  and measure performance on representative supported constraints.

Completion gate: the public solver performs proved propagation and effective
clause learning, demonstrably explores less than the full assignment product
on pruning regressions, remembers exhausted branches and remains fuel-free,
complete and source-correct. Merely retaining unused LCG primitives or renaming
an exhaustive traversal does not satisfy this objective. Defer watched clauses,
scheduler tuning and stronger propagators until this foundation is checked.

## Priority 2 — Align regressions with the uncapped LCG public solver

Files: `solver/Tests.lean`, `solver/TestsLCG.lean`, CLI integration checks.

- Replace the misleading 12-value “above-cap” enumerated-domain case. Former
  10,000-value/1,000,000-product thresholds have no special solver meaning;
  do not use crossing them as the main acceptance or performance criterion.
- Use representative large finite range and enumerated domains and large
  products with constraints that support strong pruning. Test through
  `Direct.solveCertified` and the CLI, rather than only `Direct.solveCompiled`.
  Assert the verdict, validate emitted SAT output and verify search reduction
  with the Priority 1 counters. Avoid enormous unpruned UNSAT products.
- Keep a small compiler-only check that finite domain extraction is faithful
  and independent of arbitrary cardinality limits. If retaining an old-threshold
  case as a historical non-regression, label it accordingly; it is not a new cap.
- Keep late-witness SAT, beyond-former-budget UNSAT, zero-variable/empty-domain,
  duplicate-value, Boolean-domain and original-clause cases as correctness
  regressions. Do not require the optimized solver to enumerate the old number
  of transitions; effective pruning should change those counts.
- Correct comments to describe the implemented pruning behavior rather than
  assuming that equality constraints already bypass enumeration.

Completion gate: tests cover the actual public LCG path, semantic boundaries,
large supported finite models and measurable pruning; obsolete cap numbers do
not define the solver's scope or the development priority.

## Priority 3 — Make documentation match the implementation

Files: `README.md`, `code-structure.md`, `solver/LCG/Engine.lean`,
`audits/dependency_inventory.md`.

- Correct stale claims about fuel budgets, compiler caps and singleton-only gates.
- Document the active call graph and which propagation/learning features are
  actually enabled. Until Priority 1 is integrated, describe the current public
  path accurately as exhaustive and distinguish it from the intended LCG driver.
- Update test counts, CLI exit descriptions and module/proof dependencies.
  Keep unsupported-input errors distinct from UNSAT and retain source theorem
  assumptions. Remove obsolete plan task IDs.

Completion gate: documentation agrees with the executable and checked proofs.

## Local validation and deferred scope

For solver changes, run the relevant Lean build, targeted regressions and axiom
profiles locally; run the aggregate build and retained suites for integration.
CI and workflow maintenance are out of scope for now; do not recreate the
removed workflow. Audit-script hardening is deferred, not a prerequisite for
solver development. Until its normal invocation is repaired, run axiom queries
with explicit `-j2` and audit the captured output, as in the latest validation.


Lazy/range domains and more efficient prefix/stack representations require
semantic refinement and profiling; they are not reasons to restore admission
caps. Measure eager domain construction and exhaustive traversal separately.

Language expansion, enumeration and optimization remain separate projects.
Arrays, aliases/initializers, reified/element shapes, sets and other globals
need explicit semantics and compiler correspondence. Enumeration needs
coverage/uniqueness contracts; optimization needs an optimality contract.
The checker's predicate coverage is not solver coverage.

Work in order: integrate and prove active LCG pruning → align public-path
regressions → correct documentation. Preserve unrelated working-tree
changes and use one substantial Lean build at a time. Remove closed tasks from
this plan instead of accumulating another completed-task log.

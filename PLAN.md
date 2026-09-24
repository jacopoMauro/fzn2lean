# Plan to a fully certified FlatZinc solver

This is the authoritative execution plan. The goal is a non-vacuous,
end-to-end theorem connecting the executable solver directly to
`Satisfies fullSig fullInterp`, without using rendered output or the external
solution checker as part of the correctness argument.

## Certification target

For every well-formed model in a precisely defined finite FlatZinc fragment,
the public solver must return exactly one of:

- `sat store`: `store` is admissible and satisfies the source model;
- `unsat`: no admissible store satisfies the source model;
- `unsupported reason`: the model is outside the proved fragment;
- `unknown`: fuel, resources, or an incomplete operation ran out.

Required properties:

- SAT is proved before and independently of output rendering.
- UNSAT excludes semantic source models, not just an unproved candidate list.
- Resource exhaustion never becomes `unsat`.
- Every accepted compilation case has an exact semantic theorem.

The intended public results are:

```lean
theorem solve_sat_correct
    (h : solve model = .sat store) :
    Satisfies fullSig fullInterp model store

theorem solve_unsat_correct
    (h : solve model = .unsat) :
    ¬ ∃ store, AdmissibleStore model store ∧
      Satisfies fullSig fullInterp model store
```

If `Satisfies` already includes every required declaration, domain, and
initializer condition, `AdmissibleStore` may be omitted. The final interface
must make that choice explicit.

## Current status

- Parser exact recognition and the external solution checker are verified.
- `solver.Core`, `solver.Tree`, and `solver.LCG` provide the new architecture.
- The LCG engine executes propagation, decisions, conflict analysis, learning,
  backjumping, and bounded search.
- `LCG.solve_sat_correct` proves internal SAT correctness, assuming agreement
  between Boolean and declarative constraint evaluation.
- `LCG.solve_unsat_correct` still assumes `EngineSafe`. This is explicit proof
  debt, not a final certification theorem.
- **Step 1 is complete**: no active `sorry` or `admit` remains anywhere in
  `solver/`, `LeanFzn/`, or `Tests/`. Learned-clause entailment
  (`analyzeConflict_correct`) is fully proved from the `AnalysisReady`
  reachability premise (conflict-clause entailment, reason validity and
  normalization, chronology, root facts) and depends only on
  `[propext, Quot.sound]`.
- **Step 2 is in progress** (`solver/LCG/Proofs/Engine.lean`): the
  domain-extrema bounds, the trail↔domain coherence fold
  (`fits_fold_original`, single-step `fits_domOfLit_sat_pos/neg/bool`
  under the int/bool fragment invariant), the Step 2.1 Boolean
  clause-scanning soundness (`scanClause_conflict_falsified`,
  `scanClause_unit_justified`, `litOnTrail_satisfies`,
  `negOnTrail_falsifies`), the root-fact validity and membership
  characterization (`rootFacts_valid`, `rootFacts_go_mem`), and the
  full domain-coherence layer (`DomainCoherent` preserved by
  `enqueueNorm`/`repairAfterBackjump`, established at
  `initialStateWithRoots`) are proved, all axiom-clean.
- **Step 2 soundness core (new, `solver/LCG/Proofs/Lift.lean`) is
  sorry-free**: the propagator contract `PropContract`
  (implied-literal head justification + conflict falsification), the
  `firing` lemma (fits + satisfied literal ⇒ fits the narrowed
  domains; the forward direction of the step coherence), the norm-free
  scan soundness twins (`scanClause_conflict_falsified'`,
  `scanClause_unit_justified'` in `Proofs/Engine.lean`), the unit
  enqueue trail-soundness step (`unitEnqueue_trailSat`), the
  represented-solution preservation step (`unitEnqueue_represents`),
  and the one-propagator soundness step (`oneProp_sound`) are all
  proved. The engine now normalizes learned clauses (evaluation-
  preserving; `Literal.norm_eval`), which the semantic equivalence the
  reachability invariant needs (`clausesSatOfSol` etc.).
- **`propagateLoop_lift` is fully proved (Lift is sorry-free)**: the
  loop-level fuel induction now combines `scanAll_inl_inv` (a `.inl`
  verdict inverts to a scanClause witness on the reporting state), the
  unit-enqueue three-branch analysis (skip-on-trail recurses on `st`
  itself; the opposing-fact branch sets the conflict to the pair,
  discharged as arm (b) by complementarity; the fresh-enqueue branch
  never writes a conflict), the sweep pass-through guard
  (`runPropagators_go_conflict_fixed`: a set conflict survives every
  later fold step), and the sweep inversion
  (`runPropagators_conflict_inv`: a reported conflict's origin is some
  propagator's own report or the opposing-fact pair). The theorem's
  reported-clause origin is one of: (a) a scan verdict at some state
  the run reached, (b) the opposing-fact pair, (c) a propagator's own
  conflict report at some state.
- **Remaining Step 2 obligation (stated, not sorry)**: the `EngineSafe`
  bundle in `Proofs/Search.lean` — `unsat_root_conflict` and
  `unsat_root_leaf` are explicit premises of `LCG.solve_unsat_correct`
  (no `sorry` anywhere in `solver/`). Closing both constructively and
  dropping the premise is the next work item (order below).
- `solver.Direct.compileModel` rejects every model, so the existing source-level
  direct SAT/UNSAT theorems are vacuous.
- The LCG proof modules and direct correctness module build; all 31 LCG tests
  pass. A full clean build and all functional suites have not been rechecked
  for this status update.
- Plain `lake build` builds nothing because there is no default target.

## Execution order

### 2. Drop the `EngineSafe` premise (no artificial premises)

Goal: make `LCG.solve_unsat_correct` premise-free by proving both
`EngineSafe` fields constructively from what the engine's own run
actually establishes. No new opaque premises may be introduced; every
obligation must reduce to executable-state reasoning plus the fragment
assumption.

The two fields and their constructive discharge:

* `unsat_root_conflict`: a level-0 post-propagation conflict excludes
  every internal solution. Reduction: with `propagateLoop_lift`, the
  reported clause `cc` is (a) a `scanClause` verdict on a database
  clause, (b) an opposing-fact pair, or (c) a propagator's conflict
  report. Arm (a): the scanned clause is satisfied at every internal
  solution (`clausesSatOfSol` reachability) and falsified wherever
  `scanClause` fired (`scanClause_conflict_falsified'`), so no
  represented solution survives. Arm (b): the pair is complementary,
  so one literal agrees with the trail and its negation with the
  conflicting report — excluded by `RootFacts` + trail satisfaction.
  Arm (c): per-family propagator conflict soundness (Step 2.2
  premise 5): `propX_preserves`'s contradiction half is
  state-level; the LCG-level `PropagationResult.conflict` report must
  be lifted per family (narrow-by-narrow nogood validity).
* `unsat_root_leaf`: a level-0 conflict-free post-propagation state
  with `allSingleton = true`, `fitsB` or constraint check failed
  (else the verdict was `.sat`, not `.unsat`), excludes every internal
  solution. Reduction: the leaf report fires from
  `not (fitsB a && all constraints)` under the complete singleton
  assignment `a`; since `a` IS the only assignment the state
  represents (all domain slots are singletons), a violated `fitsB`
  conjunct contradicts `Represents a` (fit) and a failed constraint
  conjunct contradicts `clausesSatOfSol` via
  `DomConstraint.satisfiedB_iff`.

#### 2.E Execution order (each item ends in a compiling, axiom-clean theorem)

1. **Singleton characterization.** Prove in `Proofs/Engine.lean`
   (or a new `Proofs/Singleton.lean`):
   `allSingleton st = true` and
   `singletonAssignment st = some a` imply `∀ b, b.Fits st.domains →
   b = a` (every fitting assignment IS `a`). This is the leaf-shape's
   "only represented assignment" fact. Pure list lemma, no semantics.

2. **Leaf-shape exclusion.** In `Proofs/Search.lean`, unfold
   `lcgSearch.go`'s leaf branch under `decisionLevel = 0` and the
   false leaf condition; combine with item 1 and `Represents`'s
   `Fits` conjunct to discharge `EngineSafe.unsat_root_leaf` — the
   violated-constraint case additionally passes through
   `DomConstraint.satisfiedB_iff` (or the generic
   `constraintHoldsB`-agreement premise when instantiating).

3. **Database-clause scan exclusion (lift arm (a)).** Strengthen
   `propagateLoop_lift` (or state a corollary) to carry, alongside the
   origin, the *falsification*: for arm (a), from
   `scanClause st1 d = some (.inl cc)` derive `cc = d` and
   `∀ a, st1.TrailSatisfied a → ¬ cc.SatisfiedBy a` (combine
   `scanClause_conflict_falsified'` with the equality `cc = d`).

4. **Pair-arm exclusion (lift arm (b)).** For the opposing-fact pair
   `[w, w.negate]`: prove the `enqueueNorm` opposing-fact branch's
   state has `w.norm` falsified-by-trail (the branch fired because
   `negOnTrail` hit) and `w.negate` falsified (the report's head),
   so any trail-satisfying assignment satisfies ONE of them and
   `cc` cannot be satisfied — a two-literal contradiction for
   represented solutions.

5. **Propagator-arm exclusion (lift arm (c)) per family.** For each
   propagator used by `propagatorsOf` (plus/le/lt/eq/ne/linLe and the
   Boolean channelings): a theorem
   `propX_lcg_sound : p.run st = .conflict c →
      ∀ a, st.TrailSatisfied a → st.FitsOn a → ¬ c.SatisfiedBy a`.
   The heavy lifting is shared with `solver/Propagators.lean`
   preservation theorems (`Preserves.contradicts`), but the LCG
   propagator works on `State` (trail+domain extrema) rather than
   plain domain lists — a bridging lemma per family connects the two
   via `DomainCoherent`. Non-proven hybrids (`propIdSlot`,
   `linNarrowAll`) stay replaced (identity/deferred) — no new family
   work in this phase.

6. **Contract monotonicity through the loop.** Prove the sweep arm's
   intermediate states keep a `LoopInv`-shaped bundle (this is what
   `PropContract.problem`-level callers needed): from
   `enqueueNorm_coherent` + `unitEnqueue_trailSat` + item 5 soundness,
   induction over `runPropagators.go` re-establishes the contract at
   every state the arm (c) reading needs.

7. **Assemble and drop the premise.** In `Proofs/Search.lean`:
   `theorem unsat_root_conflict_constructive` from items 3+4+5+6, and
   `theorem unsat_root_leaf_constructive` from item 2; then delete
   `EngineSafe` and rewrite `solve_unsat_correct` premise-free.
   Update `README.md` / `code-structure.md` to the unconditional
   statement, re-run every functional suite, and commit.

Gate: `LCG.solve_unsat_correct` takes no `EngineSafe` (or equivalent)
premise; `lake build LeanFzn solver` + all suites stay green and
`#print axioms LCG.solve_unsat_correct` lists only `[propext,
Quot.sound]`.

### 3. Freeze the first certified FlatZinc fragment

Goal: specify a useful but small source subset that maps exactly to the proved
LCG kernel.

Actions:

1. Initially support finite-domain integer and Boolean decision variables,
   needed parameters/literals, domains and initializers, `solve satisfy`, and
   only constraint forms already handled by proved LCG propagators.
2. Initially defer optimization, set variables, optional values, floats,
   complex array aliasing, and unsupported globals.
3. Define decidable `SupportedModel`, or define it by successful exact
   compilation and prove a characterization theorem.
4. Specify duplicate declarations, empty domains, initialized variables,
   aliases, literal arguments, array indexing, and domain-size limits.
5. Give every rejection path a stable reason.
6. Add positive and negative boundary tests for every supported construct.

Completion gate:

- The fragment has a concise normative definition.
- No construct is silently ignored.
- Out-of-fragment models return `unsupported`, never `unknown` or `unsat`.

### 4. Implement exact source-to-core compilation

Goal: replace the closed `compileModel` stub. Add each source construct only
together with its exact correspondence proof.

#### 4.1 Declarations, domains, and stores

1. Assign every supported decision variable a stable `Core.Slot`.
2. Compile Boolean and finite integer domains; reject invalid, unbounded, or
   oversized domains according to the fragment definition.
3. Compile initializers as exact restrictions or constraints.
4. Define source `Store` ↔ core `Assignment`, including parameters,
   initialized variables, aliases, and undeclared names.
5. Prove every admissible source store induces an assignment fitting the
   compiled domains.
6. Prove every fitting assignment reconstructs an admissible source store.

#### 4.2 Constraints

1. Define declarative semantics for each internal constraint.
2. Prove Boolean/declarative evaluator agreement for each case.
3. Prove per-constraint exactness:

```lean
compiledConstraintHolds assignment ↔
  sourceConstraintHolds reconstructedStore
```

4. Lift exactness to the conjunction of all model constraints.
5. Reject any constraint, expression shape, coercion, or argument form without
   a proved case.

#### 4.3 Whole-model correspondence

1. Prove compilation soundness: satisfying internal assignments reconstruct
   source stores satisfying the original model.
2. Prove compilation coverage: every admissible satisfying source store is
   represented in the initial internal search space.
3. Combine these as compilation exactness.
4. Export evaluator agreement in the form required by internal SAT correctness.

Completion gate:

- `compileModel` succeeds on the declared fragment.
- Source SAT and UNSAT examples reach the real LCG engine.
- The vacuous branches in `solver.Direct.Correctness` are replaced with uses of
  compilation soundness and coverage.

### 5. Prove the public end-to-end solver

Goal: expose one source-level executable with non-vacuous semantic guarantees.

Actions:

1. Define one public result type and one source-level entry point.
2. Map compilation failure to `unsupported` and resource exhaustion to
   `unknown`.
3. Reconstruct a source `Store` from internal SAT before rendering anything.
4. Compose compilation soundness with internal SAT correctness.
5. Compose compilation coverage with internal UNSAT correctness.
6. Prove SAT directly against `Satisfies fullSig fullInterp`.
7. Prove UNSAT over every admissible source store, checking quantifier order
   so the result is not limited to a particular enumerator.

Completion gate:

- At least one SAT and one UNSAT source model exercise non-vacuous theorem
  branches.
- Public correctness does not import rendering or checker-acceptance lemmas.
- `#print axioms` for public SAT/UNSAT contains no project-declared axioms.

### 6. Switch the executable to the certified path

Goal: ensure the CLI advertised as certified invokes the theorem-covered code.

Actions:

1. Route CLI solving through the new compiled LCG entry point.
2. Render a returned `Store` only after semantic correctness is established.
3. Retain the external checker for user solutions and independent testing.
4. Remove or clearly label checker-mediated legacy solver entry points.
5. Keep enumeration and optimization outside the certified claim until they
   receive separate proofs over the new core.
6. Update `README.md` and `code-structure.md` with the actual public path and
   proof dependency DAG.

Completion gate:

- CLI behavior matches SAT/UNSAT/unsupported/unknown semantics.
- Rendering is absent from the correctness dependency chain.
- Documentation does not call the legacy path directly verified.

### 7. Add certification-grade automation

Goal: make proof and build regressions fail reproducibly.

Actions:

1. Configure meaningful default Lake targets or a documented aggregate target,
   so `lake build` cannot succeed while building nothing.
2. Add CI for a clean build of both libraries and every supported executable.
3. Run all functional tests separately from benchmarks.
4. Reject active-source `sorry` and `admit` in CI.
5. Check `#print axioms` for parser, checker, internal solver, and public
   SAT/UNSAT theorems.
6. Run exhaustive small-model differential tests against reference enumeration.
7. Pin the Lean toolchain and external specification revisions.
8. Document the trusted computing base and distinguish proved refinements from
   reference-only or uncertified implementations.

Completion gate:

- A clean checkout has one documented build-and-test command.
- CI fails on proof holes, unexpected axioms, omitted targets, or failed tests.
- Release documentation names the exact certified fragment and public theorems.

## Deferred until after initial certification

Defer work that does not block a small exact solver:

- watched-array clause databases and other low-level refinements;
- sparse/reversible domain refinements;
- VSIDS, phase saving, clause minimization/deletion, restarts, portfolios,
  presolve, cuts, and linear relaxation;
- broader global-constraint coverage;
- streaming enumeration and certified optimization.

Each later optimization must have a semantic preservation/refinement theorem or
remain outside the certified execution path.

## Definition of done

- [x] No active solver proof contains `sorry` or `admit`.
- [x] Learned clauses are proved entailed by the original internal problem, given `AnalysisReady`.
- [x] Internal SAT correctness has only explicit semantic assumptions.
- [ ] Internal UNSAT correctness does not assume `EngineSafe` or an equivalent
      opaque safety bundle.
- [ ] The supported FlatZinc fragment is precise, decidable, and documented.
- [ ] `compileModel` accepts exactly that fragment and rejects everything else.
- [ ] Compilation soundness, coverage, and exactness are proved.
- [ ] Public SAT implies `Satisfies fullSig fullInterp` directly.
- [ ] Public UNSAT excludes every admissible semantic store.
- [ ] Resource exhaustion returns `unknown`, never `unsat`.
- [ ] The CLI invokes the theorem-covered solver.
- [ ] Rendering and checker acceptance are outside the correctness path.
- [ ] Public theorem axiom profiles contain no project-declared axioms.
- [ ] A clean aggregate build and all functional tests pass in CI.
- [ ] Documentation states the exact fragment and trusted computing base.

## Immediate next action

Close `propagateLoop_lift` (fuel induction over `propagateLoop`, real
base at fuel 0, `succ` cases by the four branches: conflict-inject /
unit-enqueue (`unitEnqueue_trailSat` + `unitEnqueue_represents`) /
`runPropagators` sweep (contract monotonicity) / trail-extension
restart), then derive `EngineSafe` from it and remove the premise from
`LCG.solve_unsat_correct`. Build the affected proof modules and run the
LCG tests after each integrated proof change. Then proceed to the
supported fragment and exact compiler in Steps 3–4.

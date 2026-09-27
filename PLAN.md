# Plan for a certified FlatZinc solve command

## Target

For the documented, decidable supported fragment, `leanfzn solve` should
run LCG and have kernel-checked source-level theorems: `sat store` implies
`Satisfies fullSig fullInterp`, `unsat` excludes every semantic solution,
fuel exhaustion yields `unknown`, and failed compilation yields
`unsupported`. Rendering and checker acceptance are outside the solver
proof. Enumeration, optimization, sets, floats, and unsupported globals
remain outside the first certified fragment.

Audit date: 2026-09-26. This records the current uncommitted working tree.

## Current blocker

None (2026-09-26: the former blocker `int_read_of_checkArg_slot` is
finished — sorry-free, axiom profile `[propext, Quot.sound]` — and the
full baseline passes; see step 0).

## What exists

| Layer | Current state | Limitation |
| --- | --- | --- |
| Parser/checker | Recognition and checker proofs exist. | Separate from solver certification. |
| LCG | Search implements propagation, decisions, learning, backjumping, and bounded fuel. The decision-free `solve_certified_fragment_unsat` discharges `UnsatRun`. | Its `IntViewed`, propagator safety/entitlement, database entitlement, evaluator agreement, and `PropFragment` premises still need discharge for the actual compiler configuration. General search still needs positive-level analysis and decision-descent invariants. |
| Direct compiler | `compileModel` accepts a finite scalar int/bool fragment and produces `Core.Problem DomConstraint`. `extractConstraint_holds_converse` handles the 21 extracted shapes subject to integer-valued reads. | Whole-model exactness and coverage are unfinished. |
| Direct search proofs | `solve_sat_correct` and `solve_unsat_correct` are explicit about the needed compiler correspondence. | Both take `hpending`; neither is a closed source-level claim. Direct exhaustive search is a reference path, not the target public LCG backend. |
| CLI | `Main.lean` calls `Solver.solveModelWith`. | The certified LCG path is not wired to `leanfzn solve`. |

## Ordered work queue

### 0. Restore the baseline

- [x] Finish `int_read_of_checkArg_slot`; remove its two `sorry`s and
      resolve the reported errors. (2026-09-26: proved via the new
      helpers `getElem!_map_fst`, `getElem!_eq_getElem`,
      `getD_map_snd`, `lookupIdent_inv_mem`, `declSlots_mem`,
      `declSlot_basic_inv`, `varDomain_int_of_base`,
      `intDom_values_int`, `staticEnv_of_slot`, and
      `staticEnv_int_of_checkArg` — the full typing chain from
      `checkArg` to an int-valued slot read; axioms
      `[propext, Quot.sound]`.)
- [x] Pass `lake build LeanFzn solver leanfzn tests_solver tests_lcg`
      (156 jobs, 2026-09-26).
- [x] Run `lake env tests_solver` (211 passed) and `lake env tests_lcg`
      (31 passed); recorded 2026-09-26.
- [x] Audit active Lean files for `sorry`, `admit`, user axioms, and
      the axiom profiles of public theorems (2026-09-26: no active
      proof holes; every checked public theorem of the Direct layer,
      including `solve_sat_correct`/`solve_unsat_correct`, depends only
      on `[propext, Classical.choice, Quot.sound]`).

### 1. Close source compiler correspondence

- [x] Derive integer-valued reads from `WellFormed`, slot extraction,
      and assignment-domain membership. (2026-09-26: the typing chain
      is complete — `staticEnv_int_of_checkArg` + `staticEnv_of_slot`
      + `declSlot_basic_inv` + `varDomain_int_of_base` +
      `intDom_values_int` assemble into
      `int_read_of_checkArg_slot`, sorry-free with axioms
      `[propext, Quot.sound]`; the supporting slot-name machinery
      (`lookupIdent_inv_mem`, `declSlots_mem`,
      `declSlots_map_ok_inv`, `slot_name_eq_var`, `slotNames_nodup`)
      is proved the same way, closing the `hnu` premise the
      correspondence lemmas carry.)
- [x] Cover the compiler's additional literal-bound `int_plus`,
      `int_le`, `int_lt`, `int_ge`, and `int_gt` cases in both
      semantic directions. (2026-09-26: assignment→store converses
      `holds_int_(le|lt|gt|ge)_const_(hi|lo)_toStore` and
      `holds_int_plus_lit_toStore` + `dotProduct_two_one(_inv)`;
      store→assignment inversions `holds_int_gt_const`,
      `holds_int_gt_const'`, `holds_int_ge_const`,
      `holds_int_ge_const'` complement Extract.lean's existing ones;
      `eval_ident_E`/`eval_E_ident`/`eval_ident_ident_E`/
      `eval_allDiff_array`/`eval_allDiff_args`/`eval_lin_args` bridge
      the argument evaluation, all inside the 21-shape
      `extractConstraint_holds_converse`. Also proved:
      `fullInterp_std`, `getElem!_map_fst`, `getElem!_eq_getElem`,
      `getD_map_snd`. No active proof holes.)
- [ ] Prove an accepted assignment reconstructs a source store satisfying declarations and every source constraint (`compile_exact`).
      (2026-09-26 updated: the BLOCKER is resolved — the var-decls
      half no longer needs slot-pair uniqueness. New route via
      PRODUCTION: `declSlot_position` (declSlot of a declared
      variable produces a pair IN the slot list at a position whose
      nameIndex resolves to it; proof: `declSlots_produce` +
      `slot_getElem!_of_mem` + `nameIndex_at_nodup`, no uniqueness).
      Proved and committed this session (all sorry-free, axioms
      ≤ [propext, Classical.choice, Quot.sound]; 95 theorems total,
      156-job build, 211 solver + 31 LCG tests):
      slot machinery (`slot_getElem!_of_mem`, `declSlots_no_error`,
      `declSlots_produce`, `declSlot_basic_none`, `declSlot_position`);
      the compileModel gate inversions (`compileModel_vars_basic`,
      `compileModel_predicates_nil`, `compileModel_params_scalar`,
      `compileModel_solve_satisfy`); the VAR-DECLS HALF
      (`decl_var_basic_holds`: every declared basic variable reads
      its assignment value at its slot position with `ty.contains`,
      via `toStore_read` + `mem_allAssigns_fits` +
      `varDomain_values_iff`); the dispatch fuel (`accepts_of_true`,
      `toStore_param`, `eval_ident_E_any`/`eval_E_any` —
      value-generalized eval bridges;
      `compileArgVal_ident_inv`/`_par` — the fallback-gate argument
      inversions); and the name-conditioned int-reads
      (`forall2_mem`, `int_reads_of_mem_eq_ne`: any `int_eq`/
      `int_ne` constraint's identifier arguments read ints, via the
      signature check of WellFormed — this REPLACES the hargs2
      premises of the earlier linker design). Remaining for this
      box: (a) restate `extractConstraint_holds_converse`'s `hreads`
      premise name-conditioned (`hreads x i hxarg hxi` guarded by
      `c.name.name = "int_eq" ∨ "int_ne"`, vacuous otherwise — only
      the two eq/ne slot arms consult it) or add the name condition
      at the linker level; (b) the five fallback-shape linkers
      (probe `probeC7.lean` validated the gate-evaluation template:
      `rw [compileConstraint, hx]` + `rw [if_neg/if_pos]` gates +
      `rw [hslot0, hlit1]` makes the argval match reduce
      definitionally — NO split-at-match needed); (c) the
      whole-model induction over `m.constraints` via
      `compileConstraints_mem_inv` + the per-constraint linker.)
- [ ] Prove every satisfying source store maps into compiled domains and passes the internal evaluator (`compile_covers`).
- [ ] Remove `hpending` from `Direct.solve_sat_correct` and `Direct.solve_unsat_correct`; derive their inputs from compiler success and well-formedness.
- [ ] Re-run nonvacuous accepted SAT and UNSAT source tests and unsupported-model tests.

Gate: source SAT/UNSAT theorems are nonvacuous and have no caller-supplied compiler-correspondence premise. This gate concerns the reference search composition, not the CLI's LCG path.

### 2. Instantiate the LCG fragment

- [ ] Exhibit one SAT and one UNSAT internal problem satisfying executable `PropFragment` (all initial domains have at most one value).
- [ ] Connect compiled `DomConstraint` evaluation, original clauses, and slot/domain representation to the LCG problem.
- [ ] Prove `PropSafeUniv` and conflict entitlement for each enabled propagator family (`plus`, `le`, `lt`, `eq`, `ne`, `linLe`), or disable unproved families for the first fragment.
- [ ] Derive all premises of `solve_certified_fragment` and `solve_certified_fragment_unsat` from the supported-problem check. No public theorem should ask callers for universal safety or entitlement.
- [ ] For a larger fragment, prove positive-level analysis and decision-descent reachability, then remove general `UnsatRun`. This is a later expansion gate, not a prerequisite for the singleton fragment.

Gate: actual LCG calls on accepted problems have SAT/UNSAT theorems and fuel exhaustion yields only `unknown`.

### 3. Connect source and CLI

- [ ] Compose source compiler exactness/coverage with the proved LCG result.
- [ ] Route `leanfzn solve` through that same function; map `sat`, `unsat`, `unknown`, and `unsupported` to output and exit codes.
- [ ] Document the precise accepted grammar, limits, theorem names, trusted base, and unsupported forms.
- [ ] Add a clean-checkout aggregate build and CI gate for tests, active proof holes, and axiom profiles.

Gate: source SAT and UNSAT examples pass through the user-facing LCG path, with kernel-checked end-to-end theorems and a clean aggregate gate.

## Parser and solution-checker cleanup

This is a parallel maintenance track. Keep parser recognition and the
external solution checker available while the solver is migrated; neither
is a substitute for the source-level LCG proof. Remove a definition only
after its executable callers, theorem dependencies, and tests are mapped.

### P1. Establish a separate baseline

- [x] Build the parser/checker library and named targets:
  `lake build LeanFzn tests_smoke tests_solution tests_check tests_fast
  tests_pretty tests_wellformed tests_globals tests_coverage` (78 jobs,
  2026-09-26; independent of the failing direct compiler proof).
- [x] Run the corresponding eight `lake env` executables (all passed,
  2026-09-26). Record detailed case counts and `tests_fast` timing before
  changing checker behavior or performance-sensitive code.
- [ ] Record the public interfaces that must survive: `Parser.parseModel`,
  parser soundness/completeness and `parseModel_ok_iff_valid`,
  `Check.checkModelSolution_correct`, and any selected fast/prepared
  checker API used by CLI or benchmarks.

### P2. Trim the parser by dependency

- [ ] Inventory exported names and downstream uses in `FznLexer`,
  `FznParser`, `FznGrammar`, `FznSuffix`, `FznCorrectness`,
  `FznCompleteness`, and `FznAssembled`. Mark executable parser helpers,
  proof-only helpers, and genuinely unused declarations.
- [ ] Make proof-only helpers private where no external module imports
  them. Delete only declarations with no source use and no promised
  public API. Do this from leaf modules upward to preserve the proof DAG.
- [ ] Narrow imports from the broad `LeanFzn` root where doing so
  reduces dependencies without hiding a needed theorem. Preserve the
  aggregate root as the convenient public import until callers migrate.
- [ ] Consolidate stale module comments and duplicate descriptions;
  keep the lexer/parser/grammar and recognition theorems aligned with
  the documented MiniZinc fragment.

Gate: parser recognition theorems and parser/pretty/smoke tests still
pass; accepted and rejected grammar behavior is unchanged.

### P3. Trim the checker without losing its guarantees

- [ ] Trace the public paths through `FznSolution`, `FznGlobals/*`, and
  `FznCheck`: base dynamic checker, verified front door, fast path,
  and prepared repeated-check path. The fast and prepared paths are
  currently used by tests/benchmarks, and `checkModelSolutionFast_eq`
  is referenced by solver proofs; they are not unused today.
- [ ] Choose one canonical CLI entry point and keep theorem-backed
  equivalence for retained optimized paths. Move benchmark-only APIs
  behind a clearly named module if their callers remain.
- [ ] Review the two set-literal parsers in `FznSolution`
  (`parseSetAtoms` and `parseSetTail`) for true duplication. Replace
  one only after proving identical errors/results and rebuilding the
  suffix and checker theorems.
- [ ] Remove stale claims in file headers and README when the chosen
  API is fixed. Keep parameter reassignment, duplicate/undeclared
  entries, unsupported predicates, initializer completion, arrays,
  and set cases pinned by tests.
- [ ] Split or narrow imports only after measuring whether the change
  helps incremental builds; avoid moving large proofs for aesthetics.

Gate: `checkModelSolution_correct` and retained fast/prepared equivalence
theorems compile with the same axiom profile; checker and global suites
pass; CLI diagnostics and output are unchanged.

### P4. Final code hygiene

- [ ] Remove unreachable compatibility code and archived development
  probes only after all imports, test targets, and documentation links
  have been checked. Keep source history in Git instead of live modules.
- [ ] Run a clean checkout build, all named test suites, proof-hole and
  axiom audits, and parser/checker behavior tests before declaring the
  tree clean. Update `code-structure.md` to match actual imports.

## Updating this record

For each completed checkbox, add the theorem or command, result, and date. Re-audit this table after substantial code changes. Never infer proof completeness from test success or a passing build alone.

# Remaining work for the certified FlatZinc solver

Updated: 2026-10-05. This plan contains open work only. Completed tasks
and historical execution schedules have been removed; Git history retains
previous records.

The public solve path is `Main → Direct.solveCertified → LCG.solve`.
Source-level SAT and parameter-honest UNSAT theorems exist for the accepted
finite scalar integer/Boolean fragment. The remaining priorities are a
clean codebase, reproducible certification checks, and search progress.
Verdict soundness does not imply completeness or sufficient default fuel.

## Priority and dependency DAG

An arrow means the predecessor must be completed before the successor
is integrated. Tasks on separate branches can run in parallel, subject to
file ownership and available memory. P1 is the first task.

```mermaid
flowchart TD
    P1A["P1a · Map live code and proof dependencies"]
    P1B["P1b · Delete unused legacy code and proofs"]
    P1C["P1c · Restructure retained code and large proofs"]
    P1D["P1d · Preserve useful regressions; remove scratch"]
    P1E["P1e · Synchronize imports, audits, CI and docs"]
    P2["P2 · Reproduce build, tests and certification audit"]
    P3["P3 · Repair conflict fallback and certify progress"]
    P4["P4 · Prove completeness and a sufficient-fuel contract"]
    P5["P5 · Strengthen propagation in the current fragment"]
    P6["P6 · Refine clause and propagator scheduling"]
    P7["P7 · Integration tests, audits and performance baseline"]
    P8["P8 · Extend the certified language"]
    P9["P9 · Certified enumeration and optimization"]

    P1A --> P1B
    P1B --> P1C
    P1A --> P1D
    P1C --> P1E
    P1D --> P1E
    P1E --> P2
    P2 --> P3
    P3 --> P4
    P2 --> P5
    P2 --> P6
    P4 --> P7
    P5 --> P7
    P6 --> P7
    P7 --> P8
    P7 --> P9
```

P1d can run alongside P1b/P1c after the dependency inventory. After P2,
P3, P5 and P6 are independent development branches; shared engine,
registration and proof changes must be integrated one at a time. P4
follows the repaired reference engine in P3; P6 must preserve that engine's
semantics and transfer its guarantees. P8 and P9 are later extensions,
not prerequisites for delivering the current certified solver.

## P1 — Restructure and clean the code first

Goal: retain one clear public solver path, the verified parser/checker,
and useful tests and proofs. Delete obsolete implementation and proof
files rather than keeping them as live archives.

- [ ] **P1a — Establish the live dependency inventory.** Trace executable,
  import and theorem dependencies from `Main.lean`, the library roots,
  every retained Lake test target, and `audits/certified_axioms.lean`.
  Inspect declaration uses as well as imports, including namespace and
  dot-notation calls. Classify files and declarations as production,
  useful reference/regression, or removable. Replace the stale inventory
  in `audits/dependency_inventory.md` with the current result.
  **DONE 2026-10-05**: the refreshed inventory is in
  `audits/dependency_inventory.md` (93 reachable / 23 dead modules).
- [ ] **P1b — Delete unused legacy code and proofs.** *(DONE 2026-10-05:
  the 23 dead files — legacy Config/Solve/Enum/Optimize/RevState/
  Learning/Restarts/Fixpoint/Heuristic/Solver stack, the Tree family,
  and 8 orphaned legacy test files — were deleted; dead declarations
  were removed from FznCheck.lean and Search.lean.)*
- [ ] **P1c — Restructure retained modules.** *(DONE 2026-10-05 for the
  memory-critical module: Direct/Proofs/Compile.lean was split into
  CompileCore/CompileAux1/CompileAux2a/2b/2c behind a re-export shell;
  the OOM-blocking in-flight errors were repaired throughout. The
  remaining P1c items — narrowing the LeanFzn umbrella imports and any
  further oversized-module splits — are folded into P1e/P2 where they
  are validated together with the full build.)*
- [ ] **P1d — Remove development debris.** *(DONE 2026-10-05: tmp/ deleted
  after extracting the four machine-checked counterexamples into
  `solver/LCG/Proofs/Obstructions.lean`; the stale tmp/ prose citations
  in Run/Reason/Fam/Lin/Fallback now point there.)*
- [ ] **P1e — Finish cleanup integration.** Synchronize Lake targets,
  library exports, CI, theorem audit names, README and module comments.
  Remove stale singleton-only UNSAT claims, deleted-file references and
  historical task-number references. Check every deletion batch with
  scoped compilation; leave the final full validation to P2.
  REMAINING (as of 2026-10-05): CI (`.github/workflows/ci.yml`) still
  lists the old test-set shape and must be brought in line with the
  current 15 test executables plus the fail-on-unexpected-axioms gate
  from P2; `code-structure.md` needs the new Compile-split module DAG;
  README run-loop verification. The remaining Exact.lean size (still
  ~9.8k lines, builds within memory) can be split later if needed.

Completion gate: no unused legacy source retained without a stated
purpose, no missing imports or orphaned targets, no disposable scratch
folder, and a documented acyclic module structure. Existing useful
uncommitted implementation/proof work must survive the restructuring.

## Remaining tasks after cleanup

| Task | Depends on | Actions and completion gate |
| --- | --- | --- |
| **P2 · Restore a reproducible validation baseline** | P1e | Diagnose compiler-proof memory consumption and complete the aggregate build. Run all 15 retained test suites, proof-hole/user-axiom checks, the kernel axiom-profile audit, and CLI SAT/UNSAT/unknown/unsupported exit-code checks. Make CI fail on unexpected axioms, not merely print their profiles. Record commands and actual results. |
| **P3 · Repair fallback search progress** | P2 | Address nonempty unanalyzable conflicts, which currently retreat without learning. Evaluate the existing `FallbackRaw` entitlement lemma, implement a sound progress mechanism, and integrate its invariant transfers through the run proof and public certification. Account for the empty-conflict `trailBoolPinsOk` failure branch too. Prove progress rather than assuming that inserting a clause prevents repetition; add regressions for cycling cases. |
| **P4 · Specify and prove completeness/fuel guarantees** | P3 | Prove that accepted finite problems eventually yield SAT or UNSAT under the repaired reference engine, or explicitly state a narrower proved fragment. Establish a well-founded progress measure and sufficient fuel, or expose a justified fuel contract. Keep exhaustion as `unknown`; preserve parameter-honesty in source UNSAT. Validate both satisfiable and unsatisfiable multi-value cases. |
| **P5 · Strengthen propagation within the current fragment** | P2 | Add useful allDiff value-removal deductions using the existing `intNe` literals; assess remaining weak deductions in registered families. Each change needs sound deductions, valid explanation clauses, conflict entitlement, invariant compatibility and meaningful regression cases. Integrate registration/assembly changes serially. |
| **P6 · Refine propagation scheduling** | P2 | Replace full clause scans/propagator sweeps with watched literals and incremental wakeups where benchmarks justify it. Prove refinement of the reference semantics, including enqueueing, conflict detection and backjump repair; preserve or transfer P3/P4 guarantees. Measure runtime and memory against the reference implementation. |
| **P7 · Validate integrated changes** | P4, P5, P6 | Build the combined tree, run retained suites and CLI/checker regressions, audit public theorem axioms, and compare performance with P2. Update coverage and completeness claims to exactly what the proofs and checks establish. |
| **P8 · Extend the certified language** | P7 | Add unsupported scalar constraint shapes one family at a time, with compiler exactness/coverage, evaluator agreement, reason validity, propagator safety, conflict entitlement and source-level examples. Keep unsupported cases explicitly rejected until their complete proof package lands. Sets, floats and additional globals need separate scope decisions. |
| **P9 · Add certified enumeration/optimization** | P7 | Define result contracts and source-level proofs for complete enumeration and objective optimality before restoring these commands. Give them dedicated tests and documented output guarantees; keep rendering correctness separate from solver correctness. |

## Parallel execution boundaries

| Stage | Work that can proceed in parallel | Work to serialize |
| --- | --- | --- |
| Cleanup inventory | Read-only dependency, test and theorem-use inventory | Agree on the retained roots and deletion list before editing |
| Cleanup implementation | P1d regression preservation versus P1b/P1c code cleanup; disjoint module restructuring after boundaries are fixed | Deletion before dependent restructuring; shared imports, library roots and P1e integration |
| Solver development after P2 | P3 engine progress; P5 family packages; P6 scheduler design/refinement | Changes to shared Engine/Propagate modules, registration, run invariants and public certification |
| Completeness | P4 on the repaired reference engine; P5 packages and P6 refinement on separate modules | Transfer progress/completeness guarantees to the refined engine |
| Later extensions | P8 family packages and P9 result-contract work | Shared compiler/API changes and final integration |

One writer owns each shared file during integration. Use disjoint modules
or isolated checkouts for concurrent work; the DAG describes possible
parallelism, not a requirement to run all branches simultaneously. Use
one substantial Lean build at a time until memory usage is understood.

## Validation constraint carried into P1/P2

The latest attempted aggregate build was killed with exit code 137 in
`solver.Direct.Proofs.Compile` after 124 seconds; the cgroup reported an
OOM kill. The axiom audit could not run because that module's `.olean`
was missing. The 89 propagator tests passed, and a static scan found no
proof-hole tokens or user axiom declarations in 115 Lean files. This is
not a successful repository-wide certification run.

**UPDATE 2026-10-05 (P1c): RESOLVED.** The OOM was the monolithic
5,815-line `Direct/Proofs/Compile.lean`. It was split into five
elaboration-bounded modules (`CompileCore`, `CompileAux1`,
`CompileAux2a/2b/2c`) behind a re-export shell (`Compile.lean`), with
theorem statements unchanged. The split also surfaced ~40 in-flight
elaboration errors in the aux-expansion proofs and ~10 in
`Exact.lean`/`Reason.lean` that the OOM had masked (never-elaborated
code); all were repaired. The full certified chain now builds
(`lake build leanfzn`, 152 jobs), and the axiom audit passes with all
50 audited theorems depending only on the three standard Lean axioms
(no `sorryAx`, no user axioms). P2 can proceed on this basis.

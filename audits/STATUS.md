# Certification status

Current state of the LeanFzn assurance story on `main`. It states what is
certified, what each certificate's boundary is, what evidence exists and what
remains open. It is rewritten at every landing; history is in git.

Last updated: landing of round 1 (`L1`/`L0`, commit `64e50db`).
Every number below was produced on that commit; the log paths name the run.

## What is certified

All statements are relative to the project's formal semantics
(`LeanFzn/Semantics`); upstream correspondence is tracked separately in
`specification/minizinc-2.10.1/predicates_and_globals_report.md`.

| Layer | Certificate | Boundary |
| --- | --- | --- |
| Lexing | `Lexical.tokenize_correct` (every Lean String), `parseModel_iff_sourceGrammar` | Declared non-float/R11 lexical policy, not every upstream convention |
| Parsing | `parseModel_ok_iff_valid`, `parseModel_iff_sourceGrammar` | Same policy; fuel bound proved sufficient |
| Solution syntax | `parseSolution_ok_iff_valid`, `parseSolution_eq_ok_iff_grammar`, `Checker/SolutionGrammar` | Supported assignment fragment; floats and general expressions rejected |
| Solution emission | `emitCertifiedSolution_roundTrip`, `parse_emitCertifiedSolution_of_satisfies` | `Satisfies`/store-typing and `PrintableSolutionName` |
| Satisfaction | `solveModel_sat_correct`, `solveModel_unsat_correct`, `compileFull_exact`, `compileFull_covers` | `WellFormed fullSig m` and successful compilation of the admitted fragment |
| Gated verdicts | `Gate`/`GateProof` (P0): the driver returns a verdict only through `GatedModel` | `audits/check_gate_usage.py` — 3 raw-`Model` verdict functions, all allow-listed helpers or proved wrappers |
| Optimization | `optimizeCore_optimal`, `optimizeCore_unsat`, `compileOpt_exact`, `compileOpt_covers`, `compileOpt_optimal` | Completed run only; incomplete incumbents make no optimality claim |
| Reports and CLI | `satisfaction_report_truthful`, `optimization_report_truthful`, `terminalKind_*` | Back-translation from the actual result; unknown/incomplete/unsupported stay truthful |
| JSONL | `Report/Proofs` (`terminal_toJson_*`, `error_toJson_exit`) | `Lean.Data.Json` printer/parser trusted; member order unspecified |
| Native substitutions | `audits/native_seams.json` seam theorems (`ref = impl` or exact shape) | Two free-form entries (`completedBoxPrepared`, `expectTok`) are existence-checked only (W7b) |

## Trusted base

The Lean kernel and elaborator, the C backend, LLVM/clang, the linker and the
OS runtime. `@[csimp]`/`@[implemented_by]` substitutions are admissible only
with a registered equality theorem that `audits/check_native_seams.sh` accepts.
The Python wrapper, the benchmark harnesses and the MiniZinc/Gecode oracles are
tested, not proved; the oracles are independent evidence, never a pass source.

## Validation evidence (commit `64e50db`)

| Check | Result |
| --- | --- |
| `lake build LeanFzn Tests leanfzn` | pass (739 jobs) |
| `bash audits/run_gates.sh` | `GATES: PASS` (logs `tmp/gates-l0/`) |
| Axiom audit | 2074/2074 theorem profiles, allowlist-only axioms, no `sorryAx` |
| Module boundaries | 286 modules, no cycles, public Core/CLI independent of the retired solver |
| Gate usage | 3 raw-`Model` verdict definitions, all allow-listed, 14 entries |
| Native seams | pass, including `--self-test` |
| Semantic inventory | `--require-clean` pass: 218 implemented names, 281 rows (183 reviewed, 13 restricted, 15 extension, 70 unsupported), no open findings |
| Registered executables | 39 run, 2 skipped (`challenge_scan` is argument-driven, `leanfzn` runs through the suite) |
| Python suites | `Tests/Architecture`, `Tests/Audits` (including the minimal-repository check) pass |
| Quick suite | 11/11 complete, contract agreement 11/11, witnesses 8/8 |
| Coverage fuzz vs Gecode 6.4.0 | 842 models, 776 comparisons, 776 agree, 66 unsupported (rate 0.078) |
| `audits/check_repo_minimal.py` | pass: 159 support files audited, 1 allow-listed |
| Release gate (`audits/run_release_gates.sh`) | not yet run on `main` (step L3) |

The independent oracles are the pinned MiniZinc 2.10.1 bundle with Gecode
6.4.0 (`audits/install_oracles.sh`). A missing oracle fails the gate; it is
never a silent pass.

## Open gaps

- **W5** per-predicate Lean-vs-upstream differential testing, including the
  Lean side of the G-series assumption tests, is not built.
- **W4** independent reference semantics is a skeleton on `w4/upstream`; no
  equivalence theorem exists yet.
- **W7b** two free-form native-seam entries are only existence-checked.
- **W6** one theorem for what the CLI prints (event core + `IO` shell): not
  started.
- **W8** `output_var`/`output_array` selection in the proved emitter: not
  started.
- **W9 Phase B** certificate prototype: blocked on the maintainer decision
  recorded in `specification/certificates.md`.
- The Docker image is rebuilt from source but is not gated.

## Next steps

1. Run the release gate once on `main` and record the result here (L3).
2. Land the round-2 packages in the order fixed by the coordination plan
   (`W5` and `W7b`, then `W6` and `W8`), updating this file at each landing.
3. Keep the semantic inventory reviewed: a changed implementation, helper or
   reference invalidates its hash, and the gate fails until the contract is
   re-reviewed.

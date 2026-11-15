# PGO profile for the `leanfzn` build

`default.profdata` is an LLVM IR instrumented profile used by the package-level
`moreLeancArgs` in `lakefile.toml`:

```toml
moreLeancArgs = ["-fprofile-use=pgo/default.profdata", ...]
```

It is build metadata only: LLVM profile-guided optimization changes inlining,
branch layout and code placement. It does not change the Lean source, the
parsed model, the search configuration, the checker, or the emitted solution
format.

The enforced release policy is narrower than the old claim that PGO "cannot
affect solver answers". `audits/run_release_gates.sh` builds this committed
profile selection and a non-PGO selection from the same frozen source snapshot
in separate `.lake` trees, runs the committed `audits/release_cohort.tsv` with
equal flags, seeds and deterministic conflict limits, and requires: identical
deterministic single-worker action counters; the same terminal result and
exit class; the same declared objective value and the same known optimum where
one is known; and every emitted witness accepted by both binaries'
`leanfzn check` front doors. UNSAT and optimal answers in the cohort are pinned
to exhaustive or independently established fixtures. `manifest.json` records
the source file hashes, compiler/linker/LLVM/target versions, the PGO profile
checksum, the MiniZinc pin and both binary hashes.

This is an empirical behavioural check of that finite cohort, not a proof that
arbitrary optimized machine code is correct. The remaining trust is the same
compiler and linker trust every release build relies on, plus the cohort's
finite coverage. A stale profile is not a soundness finding: clang leaves
functions it cannot match unprofiled, so profile age is a
performance/regeneration question rather than a correctness result. Timings
are evidence, not a correctness threshold; performance claims still require
the paired measurements described under "Regenerating".

The resulting binary is ordinary x86-64 code for the default target: the
profile tunes inlining, branch layout and code placement for the training
workload, not for a particular CPU, so it runs on any machine the non-PGO
build runs on. Unlike `-march=native`, it does not tie the binary to this
machine.

## Provenance

- Moved from `audits/pgo/` to `pgo/` on 2026-11-10; the profile itself is
  unchanged.
- Created 2026-11-06 on `core-perf` at the D1 base (C4 `fc7b12a`).
- Retained on 2026-11-11: a regeneration on the final M13 tree (same seven
  training cases, LLVM 23 merge) measured 0.9717 regen/stale on the D1
  five-case fixed-limit comparison over 18 paired samples, below the 3% bar
  (ratio must be ≤ 0.97). The stale profile was restored and the build
  reproduced the same binary.
- Training binary: `lake build leanfzn` with
  `moreLeancArgs = ["-fprofile-generate"]` and the matching LLVM profile
  runtime linked with `-u__llvm_profile_runtime`.
- Training cases (disjoint from the D1 measurement cohort), `--conflict-limit=60`:

  | Case |
  | --- |
  | `tower_070_070_15_070-08.fzn` |
  | `layout_27.fzn` |
  | `h5-1.fzn` |
  | `8-8-4.fzn` |
  | `easy_01.fzn` |
  | `FBDk04.fzn` |
  | `stripboard_w20_h15_l4_c4_n24.fzn` |

- Merge: `llvm-profdata merge -o default.profdata *.profraw` with LLVM 23
  (LLVM 22 cannot read the raw profile version emitted by the pinned clang).
## Regenerating

The profile goes stale as the Core hot paths change. A stale profile is not a
correctness problem: clang uses the counters it can match and leaves changed
functions unprofiled (the build suppresses `-Wprofile-instr-unprofiled`). If
performance regresses, regenerate against current code and commit the new file:

1. Copy `lakefile.toml`'s package section to a scratch build and use
   `moreLeancArgs = ["-fprofile-generate"]`, linking the profile runtime with
   `-u__llvm_profile_runtime` and `libclang_rt.profile-x86_64.a` from the same
   LLVM major version as the pinned clang.
2. Run the training cases with
   `LLVM_PROFILE_FILE=/abs/path/train-%p.profraw`.
3. `llvm-profdata merge -o default.profdata train-*.profraw`.
4. Rebuild with `-fprofile-use` and compare against a non-PGO binary using
   `audits/fixed_k.py`; record counters, timing, source snapshot and workload
   before committing. Historical gains do not establish current performance.

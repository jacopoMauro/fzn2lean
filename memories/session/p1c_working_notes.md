# P1c working notes: Compile.lean split + in-flight proof repair

Date: 2026-10-05. These are the coordinator's working notes for P1c.
Everything here is evidence for decisions; the durable outcomes go to
PLAN.md and code-structure.md when the task completes.

## The situation

`solver/Direct/Proofs/Compile.lean` is 5,815 lines of in-flight proof
expansion (the aux-slot expansion layer) that was committed in the
2026-10-05 checkpoint `fe36f83` (it was the uncommitted working-tree
content the plan required to survive). At the last verified commit
(`0c58690`) the file was 2,534 lines and compiled. The 5,815-line
version has NEVER compiled successfully:

1. **OOM**: the monolithic elaboration is killed (exit 137) at
   ~74s single-threaded. Bisected to cumulative memory exhaustion that
   strikes around lines 4700–4720, i.e. inside
   `auxShapeOf_timesKRR_args` (the per-shape argument-inversion run:
   timesRK/KR/KR'/RKK/KRR/KKR, neRK/neKR, andTrue/andFalse/orTrue/
   orFalse at 4456–5010 are each very large and their cumulative
   residency exceeds the container's ~4.6 GB cgroup limit).
2. **Elaboration errors**: masked by the OOM, the in-flight expansion
   also contains 36 errors (as of the 4700-line prefix). All in the
   aux-expansion layer:
   - `expandPlan_aux_spec` (2980): rw failures — pattern
     `expandPlan taken (auxs ++ [...]) rest` not found in a target
     where the argument is `let auxs2 := ...`-bound (zeta-reduction
     mismatch between the definition's let-form and the proof's
     rewrite patterns).
   - `expandPlan_aux_grows` (3146), `expandPlan_pieces_mem` (3240),
     `auxShape_pin2_valued` (3514), `expandPlan_aux_pinval` (3580),
     `expandPlan_origin` (3640): same class (13 unsolved goals, 8
     rewrite failures, 9 type mismatches).
   - `expandPlan_keep` (4205): 2 errors.
   - `auxShapeOf_timesKRR_args` (4679): 3 errors (after these the OOM
     kills the run before more can flush).

## Bisected OOM data (prefix probes, `lean -j1 -s131072`)

| prefix | result |
| --- | --- |
| 23–2818 (core) | exit 0, peak RSS 1.9 GB |
| 23–4141 | exit 1 (36 errors flushed, no OOM) |
| 23–4600, 23–4680, 23–4700 | exit 1 (errors flushed, no OOM) |
| 23–4720, 23–4750, 23–5000, full 23–5814 | exit 137, empty log |

So the OOM boundary is inside `auxShapeOf_timesKRR_args`
(4679–4733) and everything after it is unelaboratable in one module.

## Split design (validated by probes)

- Boundary 1 at line 2819 (`## The auxiliary-slot expansion's
  infrastructure`): core = 23–2818 (compiles clean standalone, 1.9 GB
  peak; zero reverse deps from core to aux).
- The aux layer (2820–5814) needs a further split because its
  cumulative memory exceeds the limit: the per-shape inversion run
  (4456–5010) and the per-shape compile/bridge theorems (5166–5814)
  are each heavy. Aux layer split at 4142 (per-shape semantic bridges)
  into: AuxInfra (2820–4141), AuxShapes (4142–5010), AuxPieces
  (5011–5814) — subject to the errors being fixed first.
- Importers of the module: `solver/Direct/Proofs/Exact.lean` (35: the
  aux theorems feed its compile_exact) and
  `solver/LCG/Proofs/Fam/AllDiff.lean`. They see an unchanged API if
  `Compile.lean` becomes a re-export umbrella of the split parts.

## Repair strategy (ordered)

1. Fix the ~36 elaboration errors in the aux layer (zeta/let mismatch
   pattern in expandPlan rw steps + derived failures). These are
   tactic-level repairs, no statement changes.
2. Split the module at the boundaries above so each part elaborates
   under ~4 GB.
3. Re-validate: each part, then Exact.lean, then the audit.

## Probe scaffolding (disposable)

- `splitprobe/` directory (git-ignored scratch) holds the probe files.
- `/tmp/mergedlib` has a symlink tree of the repo's oleans plus the
  built core-half olean for cross-module probes.

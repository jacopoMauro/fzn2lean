# LeanFzn — remaining work plan

This file is the single source of truth for continuing the work. It is written
so that any agent can pick one task, do it, and know exactly when it is done.
The full history of earlier rounds (findings, refuted statements, merged
tasks) is archived in `docs/PLAN-history-2026-10-15.md`; read it only when a
task points there.

## Audit cleanup 2026-10-17

`audits/README.md` describes the retained tools and measurement provenance.
The stale compiler scan table, pre-update 300-second TSV, superseded P3b TSV,
and one-off P1b/P2/P3b log importers were removed. References to those files
below are historical records, not available current evidence. Run a new compiler
scan for C8; the retained JSON file list is only a fixed benchmark cohort.
The retained 60-second TSV is folded into JSON; no current 300-second result
exists. Old task narratives and coverage counts below require revalidation.

## 1. Goal

`leanfzn solve` is a **functional, certified lazy clause generation (LCG)
solver** for FlatZinc satisfaction and optimization over finite int/bool
variables:

- every SAT answer is a checked model, every UNSAT / optimum claim is backed
  by a Lean theorem (no `sorry`, no custom axiom, no `native_decide`);
- search is first-UIP conflict-driven learning with non-unit explanations;
- it solves a meaningful share of the agreed benchmark set (§5, task V2)
  within the time limits.

## 2a. Status check 2026-10-16, later (Claude)

Quick gate re-run in `/workspace` (code-focused, long benchmarks deferred):
aggregate build 0, audit **814/814** allowlist-only, boundaries **303**,
fuzz 200 seeds 0 wrong/bound/witness, `analysis=none causes: []`.
Merged since the plan rewrite: **L0** (all), **E2**, **E3**, **H1**,
**L1a** (pinned `int_lin_le_reif` propagator; pin-false = conflict only),
**L3 partial** (`int_max`/`int_min` slot forms `minSlot`/`maxSlot` now use
the explained `propMin`/`propMax`). Not merged: **L1b** (`wt/l1b` 91296a2,
B-arm reverted, see box), **L2** (recon only, `wt/l2` at baseline), **L3
remainder** (`minPair maxPair maxGen minGen`, `wt/l3` 0b0366b, 1 dirty file).
Open after that: L4, C5b (parked patch in `wt/l1`), L5–L8, P1b, P3, P2, O3,
C8, V2.

**In progress (2026-10-16, Claude coordinator):** L3 all-slot pairs MERGED
(remainder → C9); L2 MERGED (FBDk04 17 s); L4 in `/home/vscode/wt/l4` (sonnet worker); C5b MERGED; C9 MERGED (binary shapes); C8 in `/home/vscode/wt/c8`
(sonnet worker); was: C5b in `/home/vscode/wt/c5b` (sonnet
worker, parked patch applied there). Serial queue after them (all touch the
registration surface, so one at a time): L2 → L1b → L4 → L5 → L6 → L7 → L8,
then P1b → P2 → O3, then C8. Owner: D1, H2 (≈248 changed files), L1a pin-false limitation, long
benchmarks.

## 2a. Status check 2026-10-16 (second coordinator session, L1a merged)

Baseline re-verified at the start: UIP build 0, aggregate build 0 (588
jobs), audit 788/788, boundaries 303, quick fuzz clean.

**L1a is DONE-for-scope and merged** (§4 box): `propLinLeReif` is
registered for `.linLeReif`; all `PropSemContract` / emission-typing /
canonicality / no-Bool / A3 / decidedness / reason-contract obligations and
consumer arms are proved. Gate re-run in `/workspace` after the merge:
aggregate build **0** (588 jobs), audit **800/800** allowlist-only,
boundaries **303**, all **28** runnable exes exit 0, fuzz 50 seeds
0 wrong/bound/witness, CLI pinned-reif model SAT + checker-accepted,
`tests_public_lcg` 9 fixtures ok. Runtime effect: `.linLeReif` models now
have a learned-clause/pruning propagator when the reif slot is pinned
(pin-true: bound propagation; pin-false: conflict detection only —
recorded as an owner decision in the box). Working copy
`/home/vscode/wt/l1a` HEAD `d38eac8` (kept for the pin-false follow-up);
`/home/vscode/wt/l1a/l1a_integration_wip.patch` is superseded.

Key finding (also in the box): the originally-planned naive delegation is
unsound; `dotProduct` refusing Boolean operands while `intView` reads them
as 0/1 is the trap. The merged design uses escape literals + an
integer-operand guard. L1b should reuse that pattern.

**L1b is now PARTIAL with a validated core** (§4 box): the emission, its
guards (three of them — see the box; the L1a soundness lesson applies),
the new `dotOver_le_sumMax` arithmetic and the fitting-truth lemma all
compile green in `/home/vscode/wt/l1b` (`tmp/l1b_scratch.lean`, HEAD
`0e2035b`, patch `l1b_core_wip.patch`). Remaining: wire the branch into
`propLinLeReif`, extend the ~9 obligation lemmas, add the symmetric sumMin
arm, then gate + merge.

**Next, in order:** finish L1b (see the L1b box checklist) → L2 →
L3 → L4 → C5b (parked patch) → rerun E2 (60 s / 300 s) → L5–L8 → P1b →
P3 → P2 → O3 → C8 → V2. Owner decisions: D1 (lazy domains), H2 (commit
~260 changed files), the L1a pin-false limitation, and the deferred
`bash audits/run_challenge_solve.sh 60` / `300` re-runs plus the full
`tests_lcg_harness --fuzz 3000` and no-arg battery (long benchmarks
deferred to the owner).

## 2a. Status check 2026-10-16 (fifth session, coordinator: L1b + L5 + C9-partial merged)

Everything below is in `/workspace` (uncommitted, branch `lazySolver`; H2 is
still the owner's decision). Each integration re-ran the gate in `/workspace`:

| After merging | build | tests_solver | audit | boundaries |
|---|---|---|---|---|
| L1b | 0 (590 jobs) | 326 | **870/870** | 304 |
| L5 | 0 (590 jobs) | **342** | **908/908** | 304 |
| C9-partial (n=2 arrays + literal result) | 0 (590 jobs) | **376** | **925/925** | 304 |

L1b fuzz (required command, post-L1b binaries): `--fuzz 3000 100000 --bound
50000 --no-chrono` → instances 3000, rejected 0, SAT 825, UNSAT 2175,
**wrong/boundEx/rejectedWitness = 0**, 6367 conflict sites all
`analysis=some`, `analysis=none causes: []`, `semantic=0`.

- **L1b DONE and merged** (wt/l1b HEAD `d4a23b4`): the bounds-decide-`b` arm
  is WIRED with the sound design from this plan — `domPruningOkB` gained the
  `.linLeReif` operand-range/arity conjunct, `domPruningOk_lreif` extracts it,
  and it is threaded as an explicit `hlreif` premise through
  `boxPropagators_reasons` / `propagatorsOfProved_reasonSafeUniv`. DOCUMENTED
  STATEMENT CHANGES (hypothesis additions; no code callers):
  `compiled_domPruningOk` gains `hreif`;
  `fallbackCoverage_empty_of_proved`/`_of_proved`,
  `compiled_hfallbackng_of_compileModel`, `fallbackCoverage_of_compiled` gain
  the same operand-range premise; internal rename
  `propLinLeReif_run_stable` → `propLinLeReif_run_b` (statement widened from
  `.stable` to `= propLinLeReifB …`). Merge conflicts were resolved by hand in
  `Propagators.lean`, `Reason.lean`, `BoxPropagators.lean`, `FallbackFit.lean`
  (call-site threading) plus duplicate `typed_min`/`typed_max`/
  `min_canonical`/`max_canonical` blocks removed.
- **L4 DONE and merged earlier** (wt/l4 HEAD `2124809`): `eqReifSlot`/
  `neReifSlot`/`leReifSlot` pinned delegations, obligations, tests, audit.
- **L5 DONE and merged** (wt/l5 `7eb4f2e`/`ff06c0b`/`53509d5`, report
  `/home/vscode/wt/l5/REPORT-L5.md`): `propLinEqReif`/`propLinNeReif` pinned
  delegations with L1a escapes, all obligations + UIP arms, 6 new route
  fixtures, audit 908/908. No unpinned/decisive arm; L1b's range gate NOT
  extended (not needed). Pinned-false arms stay conflicts-only.
- **C9-partial DONE and merged** (wt/c9b `1e6f18c` + `2a2dd0c`):
  literal-RESULT `min/max(x,y,k)` → `minSlot`/`maxSlot` over a pinned aux, and
  two-element `array_int_minimum/maximum(r,[e1,e2])` → `int_min/int_max(e1,e2,r)`
  (no aux); semantics gap lemma `array_int_minimum_rewrite_gap` (minValue
  ignores a non-int TAIL ⇒ the rewrite is guarded by the WF int-typing
  recovery in Exact). OPEN: n ≥ 3 arrays (a 3-element array stays `.minGen`).
- Housekeeping carried over: wt/l3's remainder is only a stray newline
  (retired); wt/l1b, wt/c9b, wt/l4, wt/l5 are merged and can be retired.

## 2. Verified state (2026-10-15, after L0 merged)

Re-verified in `/workspace` (branch `lazySolver`, nothing committed since
`8cecfeb`; L0 applied from `wt/l0` HEAD `d79d283` on 2026-10-15):

| Check | Result |
|---|---|
| `lake build LeanFzn Tests leanfzn` | 0 (588 jobs, `/workspace` re-run) |
| `bash audits/run_axiom_audit.sh` | **788/788**, allowlist-only, no `sorryAx` |
| `python3 audits/check_module_boundaries.py` | **303 modules**, no cycles |
| test executables (31 built explicitly) | 28 runnable exit 0; `leanfzn`/`challenge_scan` skipped, harness run as below |
| Fuzz `tests_lcg_harness --fuzz 3000 100000 --bound 50000 --no-chrono` | 3,000 instances, 0 rejected, **0 wrong**; 1,400 instances / 29,017 conflict sites, all `analysis=some` (100%), `analysis=none causes: []`, `semantic=0` (L0c generator arms included) |
| No-arg harness battery | `ALL 50 INSTANCES: verdicts agree, witnesses accepted` |
| Challenge scan (124 files ≤ 3 MB) | 21 compile |
| Challenge solve, 60 s (`audits/challenge_solve_60s.tsv`) | **1/21 solved** (trivial atp-stage2); the 20 timeouts now all run on LCG (L0) |
| Challenge solve, 300 s (`audits/challenge_solve_300s.tsv`) | **2/21 solved**: `fbd1/FBDk04.fzn` in **66.9 s** (the first solve of an `int_lin_ne`-family model; it timed out at 60 s) + trivial atp-stage2; both TSVs folded into `audits/benchmark_lcg_results.json` (`challenge_solve.60s` / `.300s`, via `audits/fold_challenge_solve.py`) |

What exists:

- Public route `solveCompiledLcg` (Integration/Lcg.lean): certified LCG for a
  model whose constraints are `lcgFamB`-gated — **since L0 that is every
  constructor**, so every compiled model takes the LCG branch whenever the
  remaining gate conditions (shape-typing, slot range, no-Bool-on-int) hold;
  otherwise the certified chronological fallback.
- 17 families without a dedicated explained propagator register the generic
  checking propagator `propCheck` (fires only when every slot of the
  constraint is a singleton and the forced check fails); L1–L8 replace them
  family by family with pruning propagators.
- Optimization: certified branch-and-bound (Integration/Optimize.lean,
  LcgOptimize.lean) with streaming output and clause reuse across bounds.
- Compiler: scalars, par arrays, var-array aliases, satisfy/minimize/maximize,
  41 `DomConstraint` constructors.

The pre-L0 baseline of this section (778/778 audit, 301 modules, 2,256
conflict sites) and the family-history of `lcgFamB` are in
`docs/PLAN-history-2026-10-15.md`.

Public theorems and their premises (checked 2026-10-15): the public route
theorems have NO hypotheses beyond the result equation itself —
`solveCompiledLcgMixed_sat`/`_unsat`/`_total` and the `solveCompiledLcg*`
wrappers take only `{p} {a} (h : solveCompiledLcgMixed p = .sat a)` (resp.
`=.unsat` / `≠ .unknown`); the compiler-side `solveCertified_total`/`_sat`/
`_unsat` are likewise unconditional (the source-level correspondence is in
`Integration/CertifiedSolve.lean`). Every kit/invariant premise used inside
the proofs is discharged there (e.g. `lcgKitMixed` consumes only the gate
equation `lcgRouteGateMixed p = true`), and `bash audits/run_axiom_audit.sh`
reports 788/788 profiles with allowlist-only axioms `{propext,
Classical.choice, Quot.sound}` and no `sorryAx`, so no public theorem
carries an unproved premise. Known remaining limitations, stated per §5:
- Families still on the checking-only propagator `propCheck`: the seventeen
  `propCheckFamB` families, i.e. `timesSlot minSlot maxSlot absSlot linNe
  eqReifSlot leReifSlot neReifSlot linEqReif linLeReif linNeReif minPair
  maxPair divGen modGen maxGen minGen` (L1–L8 replace them; L1 is split into
  L1a/L1b with a recorded design).
- Compiler: reified constraints with a literal operand, `bool_xor`, and the
  general array-declaration/index forms are still rejected (C5b/C8/D1);
  5 files need D1 (owner-gated lazy/interval domains).
- Search: the decision order is fixed (P2 open), the learned-DB scan is
  unindexed (P1b open), and no restarts exist; the 300 s scan solves
  `fbd1/FBDk04.fzn` (66.9 s) and the trivial `atp-stage2`, and the remaining
  19 files time out.
- `code-structure.md`'s known internal strengthening item (joint semantic run
  induction for the mixed frame kit) is unchanged by L0; it is an internal
  strengthening opportunity, not a hypothesis of any public theorem.

`lcgFamB` (UIP/Proofs/LcgFamiliesRun.lean) **excludes 17 families**:
`timesSlot minSlot maxSlot absSlot linNe eqReifSlot leReifSlot neReifSlot
linEqReif linLeReif linNeReif minPair maxPair divGen modGen maxGen minGen`.

**Why the challenge files time out:** 17 of the 20 failing files contain an
excluded family, so they run on the slow fallback. By count:
`int_lin_le_reif` (EchoSched, filters, rect-euler), `int_lin_ne` (all of
fbd1), and `int_max`/`int_min`. Only the 3 proteindesign12 files actually run
on LCG, and they still time out. Widening LCG coverage (§4 L-tasks) is
therefore the highest-value work, followed by search performance (§4
P-tasks).

## 3. How to do a task (protocol for every agent)

1. **Workspace.** Never edit `/workspace` directly. Make a private copy
   `cp -a /workspace /home/vscode/wt/<task-id>`, then in the copy:
   `git add -A && git -c user.name=w -c user.email=w@l commit -qm "<id> baseline"`.
   Commit small checkpoints often, because workers get interrupted.
2. **Rules.**
   - No `sorry`, `admit`, custom `axiom` or `native_decide`.
   - Never weaken an existing theorem statement silently. List every changed
     statement as old → new.
   - If a statement looks false, look for a counterexample (harness or a
     kernel-checked Lean witness) and keep it as a theorem.
   - A runtime change is allowed only when the task says so, or a
     counterexample forces it.
   - Prefer a small proved runtime guard over a huge proof. Earlier examples
     are `assertExtra` and `learnedRepeats` (see history).
3. **Build hygiene.**
   - Run one heavy build at a time, and capture exit codes before reading logs.
   - Build `LeanFzn.Solver.UIP` before running the audit.
   - Executables must be built explicitly (`lake build <exe>`); aggregate
     builds leave `.lake/build/bin` stale.
4. **Standard acceptance gate (G).** A task is accepted only if, in the copy:
   - `lake build LeanFzn Tests leanfzn` → 0;
   - every `[[lean_exe]]` in `lakefile.toml` is built explicitly and exits 0
     (skip `leanfzn`, `challenge_scan`; run `tests_lcg_harness` as below);
   - `bash audits/run_axiom_audit.sh` → PASSED, with the task's main
     theorems added to `audits/certified_axioms.lean`;
   - `python3 audits/check_module_boundaries.py` → 0;
   - if runtime/search code changed:
     `.lake/build/bin/tests_lcg_harness --fuzz 3000 100000 --bound 50000 --no-chrono`
     reports 0 wrong / bound / witness failures and analysis = some at 100% of
     conflict sites, and the no-arg battery prints `ALL 50 INSTANCES: verdicts agree`.
5. **Merge (coordinator only).**
   - First grep `/workspace` for a marker of the work (new theorem name).
     **Never re-apply a merged patch**; this caused a past incident.
   - Then run, in `/workspace`:
     `git -C /home/vscode/wt/<id> diff --binary <baseline> HEAD -- . ':!PLAN.md' | git apply --reject`
   - Fix any `.rej` by hand; `audits/certified_axioms.lean` and
     `LeanFzn/Solver/UIP.lean` usually conflict, so re-add the lines.
   - Re-run gate G in `/workspace`, then delete the copy.
6. **Report.**
   - Status (DONE, PARTIAL or BLOCKED), commits, diff stat.
   - New and changed theorems, with exact statements for changed ones.
   - Remaining premises, stated exactly.
   - Gate exit codes and the harness line.
7. **Plan update.** After every merge or failure, tick the task here and add
   one line: date, result, the new theorem names, and any remaining premise.
   If work stops unfinished, record the copy path and last commit in the
   task.
8. **Worker availability (2026-10-15, binding for the next coordinator).**
   `runSubagent` with any premium model (Claude Sonnet/Haiku, GPT, Gemini,
   Grok, Auto) fails with
   *"You've reached your monthly credit limit … reset on November 1, 2026"*.
   The only usable worker models are the custom-endpoint ones
   (`GLM-5.3`, `GLM-5.3-Flash`, `DeepSeek-V4.1-Flash`). They succeeded on
   L0a/L0b1/L0b2 and on a one-line probe, but every long worker prompt for
   L1/L2/L0c after that returned *"Sorry, no response was returned"* or
   *"Agent completed with no output"* (L0c's worker died mid-edit; its edit
   was adopted and fixed by the coordinator). Practical guidance: prefer
   doing L1–L8, P1b, P2 yourself, or dispatch only short, tightly-scoped
   worker prompts (one file, one lemma) and verify every claim; always
   re-check the copy for uncommitted work after a failed dispatch.

## 4. Tasks

Status legend: `[ ]` open · `[~]` in progress (write copy path) · `[x]` done.
Model hint: **H** = Haiku-sized (mechanical, one module); **S** = Sonnet-sized
(new proof structure). Dependencies are listed per task.

### L — widen the LCG fragment (highest value)

Background:
- A family `F` is LCG-routable when `lcgFamB F = true` and the per-family
  obligations hold:
  - `PropSemContract` (pattern in `UIP/Proofs/LcgFamilies*.lean`, assembled in
    `propSem_of_family`);
  - `EmissionTyped` (`LcgEmissionTyped.lean`);
  - canonical emission (`LcgCanonicalFamilies.lean`);
  - no Boolean atom on int slots (`LcgNoBoolEmit.lean`);
  - the mixed-box versions (`LcgMixed*`).
- Flipping `lcgFamB` breaks every `cases dc` proof over gated families.
  Grep for `lcgFamB` and repair each one.
- **Common DoD for L1–L8:**
  1. `lcgFamB F = true`.
  2. All obligations above are proved for `F`.
  3. The explained propagator is sound: its reason clauses are entailed and
     semantically falsified (`SemReasonOK`), and its conflict clauses are
     entailed and falsified.
  4. Unit tests (SAT and UNSAT, against exhaustive enumeration) are added in
     `tests_solver` or a new test exe.
  5. A fuzz generator case for `F` is added to `Tests/UIP/LcgHarnessBattery.lean`.
  6. `tests_public_lcg` shows a model with `F` routed to LCG (`LCG=true`).
  7. Gate G passes.
  8. `bash audits/run_challenge_solve.sh 60` is rerun and the solved count is
     recorded here.

- [x] **L0 (S) — generic checking propagator: make every family LCG-routable.**
  DONE 2026-10-15 (sub-boxes L0a/L0b1/L0b2/L0c all verified; merged into
  `/workspace` from `wt/l0` HEAD `d79d283` — `/workspace` gate G re-run:
  build 588 jobs 0, audit 788/788 PASSED, boundaries 303, all 28 runnable exes
  0, fuzz `wrong/boundEx/rejectedWitness=0` with 1400 instances / 29,017
  conflict sites all `analysis=some`, battery `ALL 50 INSTANCES: verdicts
  agree, witnesses accepted`, `semantic=0`). Effect measured: the 300 s scan
  solves `fbd1/FBDk04.fzn` in 66.9 s (it timed out at 60 s before), i.e. the
  LCG routing + learning pays off even with the checking-only propagator.
  Merge note: L0 was merged as ONE patch (sub-boxes shared the copy).
  Split 2026-10-15 into L0a/L0b1/L0b2/L0c (it spans a new module, the
  registration change with two proof surfaces, and the tests/measurement).
  Copy: `/home/vscode/wt/l0` (merged; may be deleted once the 300 s scan in it
  is finished and its TSV copied to `/workspace`).

  - [x] **L0a (S) — define `propCheck` and prove its generic obligations.**
    DONE 2026-10-15 (verified by the coordinator: build 251 jobs exit 0,
    audit 785/785 PASSED, boundaries 303 modules, no `sorry`; registration
    untouched). `propCheck`/`dcSlotsFull` live in the Propagation layer,
    `LeanFzn/Solver/Propagation/Proofs/PropCheck.lean` (ns
    `LeanFzn.Solver.Propagation.DomainFiltering`), because `propagatorOfProved`
    must return `propCheck dc` in L0b and UIP imports Propagation, never the
    reverse. The UIP module `LeanFzn/Solver/UIP/Proofs/LcgPropCheck.lean`
    carries the four UIP-typed obligations. New theorems:
    `propCheck_implied_elim`, `satisfiedB_dcSlotsFull_congr`,
    `propCheck_conflict_entailed` (Propagation); `propCheck_sem`,
    `propCheck_canonical`, `propCheck_typed`, `propCheck_noBool` (UIP).
    Copy `/home/vscode/wt/l0`, last commit `b9f0f83` (>= L0a content).
    Merge policy for L0: sub-boxes share the copy, so L0 is merged into
    `/workspace` as ONE patch after L0c is verified (never per sub-box; that
    would double-apply).

  - [x] **L0b1 (S) — register `propCheck`, flip the gate, repair the library.**
    DONE 2026-10-15 (copy `wt/l0`, commits `ae093f1`/`6145bef`/`4892a28`;
    coordinator-verified: `lake build LeanFzn` 0 (299 jobs), audit 788/788
    PASSED, boundaries 303; `lake build LeanFzn Tests leanfzn` 0 (588 jobs)).
    New theorems: `propagatorOfProved_check_eq`,
    `propagatorOfProved_run_check`
    (`Propagation/Proofs/Propagators.lean`), `dcSlots_eq_full`
    (`UIP/Proofs/LcgEmissionTyped.lean`: `dcSlots = dcSlotsFull`),
    `propCheck_sem_aux` (`UIP/Proofs/LcgFamiliesRun.lean`, used by
    `propSem_of_family`). No theorem statement was weakened; only proof
    bodies/case arms changed, and `propagatorOfProved_run` gained the final
    disjunct `propCheckFamB dc = true ∧ (propCheck dc).run st = res`.
    RUNTIME CHANGE (intended by the task, recorded here):
    `minSlot/maxSlot/absSlot/timesSlot` previously registered
    `propMin`/`propMax`/`propAbs`/`propTimes` and `linNe` registered
    `propIdentity`; all 17 `propCheckFamB` families now register
    `propCheck` on BOTH routes. The removed A3 propagators return as proper
    explained propagators in L3 (min/max), L6 (times) and L7 (abs/div/mod);
    until then the fallback for models failing the OTHER gates keeps leaf
    enforcement only (sound, weaker pruning).
    Copy `/home/vscode/wt/l0` (continues from `b9f0f83`).
    - `propagatorOfProved` returns `some (propCheck dc)` for the 17 excluded
      families (`timesSlot minSlot maxSlot absSlot linNe eqReifSlot
      leReifSlot neReifSlot linEqReif linLeReif linNeReif minPair maxPair
      divGen modGen maxGen minGen`), replacing `propIdentity`/`none`; extend
      `propagatorOfProved_run` (its inverse disjunction) with the new arm.
    - Set `lcgFamB F = true` for all 17 in `UIP/Proofs/LcgFamiliesRun.lean`.
    - Extend `dcSlots` (`UIP/Proofs/LcgEmissionTyped.lean`) to cover the
      general/reified families (ideally `dcSlots := dcSlotsFull`) so the
      `kitGateB`/`mixedKitGateB` slot checks cover them.
    - Repair every proof broken by the flip, using the L0a theorems: the
      `PropSemContract`/`cases dc` arms (`propSem_of_family`), the emission
      typing (`emissionTyped_of_families` via `propCheck_typed`), canonicity
      (`emissionCanonical_of_families` via `propCheck_canonical`), no-Bool
      (`propCheck_noBool`), the `propagatorOfProved_run` consumers
      (`BoxPropagators.lean`, `Reason.lean`, `FallbackFit.lean`, …), the A3
      entailment surface (`BoxPropagators.boxPropagators_safe/conflicts` via
      `propCheck_conflict_entailed`/`propCheck_conflict_false`), and any
      `propagatorOfProved = none` routing proofs. Grep `propagatorOfProved`,
      `propIdentity`, `lcgFamB`.
    - DoD: `lake build LeanFzn` → 0; no `sorry`/`admit`/axiom/`native_decide`;
      list every statement you had to change as old → new.

  - [x] **L0b2 (S) — repair the tests, full gate G, routing check.**
    DONE 2026-10-15 (copy `wt/l0`, commits `0c5ba5d`/`513a5c4`;
    coordinator-verified independently: full build 588 jobs 0, all 31 exes
    built and the 28 runnable ones exit 0, fuzz (old generator)
    `wrong/boundEx/rejectedWitness=0` with 2256/2256 sites 
    `analysis=some`, `analysis=none causes: []`, `semantic=0`; battery
    `ALL 50 INSTANCES: verdicts agree, witnesses accepted`; audit 788/788;
    boundaries 303). No `Tests/**` repair was needed: nothing depended on
    `propagatorOfProved = none` / `lcgFamB = false` for the 17 families.
    Routing check: scratch `lake env lean --run` script over parsed
    `int_lin_ne` / `int_lin_le_reif` / `int_max` models printed `LCG=true`
    for all three (`all lcgFamB: true`); the permanent fixtures are in L0c.
    Challenge scan: 21/21 OK (unchanged). PLAN record in the copy
    (513a5c4) carries the exact script recipe.
    Copy `/home/vscode/wt/l0`. Depends: L0b1.
    - Repair `Tests/**` broken by the flip; then per gate G: every
      `[[lean_exe]]` built explicitly and exits 0 (skip `leanfzn`,
      `challenge_scan`; run `tests_lcg_harness` with
      `--fuzz 3000 100000 --bound 50000 --no-chrono`), audit PASSED with the
      new main theorems added to `audits/certified_axioms.lean`, boundaries 0,
      fuzz 0 wrong / analysis = some at 100% of conflict sites, no-arg
      battery `ALL 50 INSTANCES: verdicts agree`.
    - Routing check (replaces the earlier "CLI check" wording): a parsed
      `int_lin_ne` / `int_lin_le_reif` / `int_max` model satisfies
      `lcgRouteGateMixed = true` (a scratch `lake env lean` script evaluating
      the gate on the compiled problem, or a `tests_public_lcg`-style
      fixture); record the exact command and its `LCG=true` output. A
      permanent fixture is L0c's job.
    - Challenge scan: rerun `.lake/build/bin/challenge_scan --opt FILE` over
      the 21 compiling files listed in `audits/challenge_solve_60s.tsv` and
      record the OK count (must be 21, unchanged).
    - DoD: all of the above with exit codes and output lines reported.

  Original L0 DoD items 1–3 and 6–8 bind L0 as a whole (closed by L0b1/L0b2
  and L0c).
  - [x] **L0c (S) — L0 tests and measurement.** DONE 2026-10-15
    (coordinator-run; the delegated worker died mid-edit and its
    fuzz-generator edit was adopted and fixed). Copy `wt/l0`, commits
    `84ca492` + `d79d283`. `tests_solver` 280 pass (17 new `route:` checks),
    `tests_public_lcg` 9/9 fixtures `ok=true`, full fuzz with the new
    generator arms: 3000 instances, 0 rejected, 0 wrong, 1400 instances /
    29,017 conflict sites all `analysis=some`, `analysis=none causes: []`,
    `semantic=0`; no-arg battery green. `bash audits/run_challenge_solve.sh
    60` → **solved 1 / 21 within 60 s** (recorded in §2). L0 merged into
    `/workspace` and gate G re-run there (see the L0 box).
    - `tests_solver`: 17 new `route:` checks (linNe / leReif / max, SAT +
      UNSAT) asserting `lcgRouteGateMixed = true` and comparing
      `solveCompiledLcg` with exhaustive enumeration — `passed 280 solver
      tests`, exit 0.
    - `tests_public_lcg`: 3 new fixtures (`linne-sat`, `lereif-unsat`,
      `max-unsat`), all `ok=true LCG=true`; `max-unsat` shows 27 non-unit
      learned clauses / 35 backjumps, so `propCheck` conflicts drive real
      analysis and learning.
    - Fuzz generator: `fuzzSrc` gained `int_lin_ne`, `int_le_reif`,
      `int_lin_le_reif` arms (shared pinned Boolean slot `bb` declared
      before the constraints; `kind % 13`). First attempt produced
      1618/3000 parser rejections (declarations must precede constraints) —
      fixed; reduced 300-seed sweep: 0 rejected, 0 wrong, 2931 conflict
      sites vs ~226 for the old generator (so the new families really
      exercise the LCG analysis). Full 3000-seed fuzz + no-arg battery with
      the fixed generator: pending at record time.
    - `bash audits/run_challenge_solve.sh 60` → **solved 1 / 21 within 60 s**
      (unchanged; the 17 families now run on LCG, but `propCheck` does not
      prune and the timeouts are search-bound) — recorded in §2.
    - DoD (remaining): full 3000-seed fuzz + battery green, then merge L0
      into `/workspace` as one patch (see the merge note under L0a) and
      re-run gate G there.
  - Common DoD items 1–3 and 6–8 apply to the union of L0a–L0c.
  - Depends: none. This is the first task to do.
- [x] **L1 (S) — `int_lin_le_reif` explained propagator** (`linLeReif`).
  Split 2026-10-15 into L1a (pinned-direction delegation) and L1b (the
  bounds-decide-`b` arm). **L1a is DONE-for-scope 2026-10-16** (registered,
  all obligations proved, gate green — see the L1a box; note the soundness
  repair and the conflicts-only limitation there). **L1b is OPEN** and is the
  next task; note that L1b's `sumMax ≤ b ⇒ .implied (posBool r true)`
  emission will hit the same two obstacles L1a found (state-vs-solution facts
  and Boolean operand reads) unless it reuses L1a's escape-literal pattern
  (`insertAfterHead` + `Bool.escapes` + the operand guard).

  - [x] **L1a (S) — delegation when the reif slot is Boolean-pinned.**
    DONE-for-scope 2026-10-16 (coordinator, second session). The pinned
    delegation `propLinLeReif` IS REGISTERED for `.linLeReif` and every
    obligation and consumer arm is proved; `/workspace` gate re-run after
    the merge: aggregate build 0 (588 jobs), audit **800/800**
    allowlist-only, boundaries **303**, all **28** runnable exes exit 0,
    fuzz 50 seeds 0 wrong/bound/witness, and a pinned-reif CLI model
    (`int_lin_le_reif([1,1],[x,y],4,r)` with `bool_clause([r],[])`) solves
    SAT and is checker-accepted. `tests_public_lcg` 9 fixtures ok,
    `tests_solver` (incl. the L0c `route:` checks for this family) passes.
    Copy `/home/vscode/wt/l1a` (HEAD `d38eac8` = the green integration commit);
    the earlier parked patch `l1a_integration_wip.patch` is superseded.

    **Design (sound; supersedes the original box text — the naive
    delegation was UNSOUND).** Two causes, both fixed: (a) the naive form
    used the state's pin as a *solution* fact; (b) `dotProduct` refuses
    Boolean operands (a Boolean read makes `dotLe = false`, which
    *satisfies* `r = false`) while emitted bound literals evaluate
    Booleans as 0/1 through `Value.intView`. Fix: every emitted clause is
    augmented with "escape" literals (`insertAfterHead extras`):
    * `r` pinned `true` → extras `[posBool r false]` (true at `r = false`
      solutions; at `r = true` the reif fact forces integer reads so the
      `propLinLe2` nogood kernels apply);
    * `r` pinned `false` with the guard `domsIntOnlyB` (in-range,
      nonempty, integer-only operand domains) → extras `posBool r true ::
      flatMap (fun i => [posBool i false, posBool i true])` and
      **conflicts only** (`conflictsOnly`): the pin-false *implied* bounds
      would need a reason contract relating the state box's slot count to
      the problem box's (`PropagationContract.reason` /
      `boxPropagators_reasons` are evaluated at solutions that need not
      fit the state) — see the open item below.
    The propagator's outer guard includes `coeffs.length == is.length`
    (the extractor's own gate), so no obligation gained an arity premise.

    **Proved and merged** (`Fam/Lin.lean` §L1a, `LcgFamiliesRun`,
    `LcgEmissionTyped`, `LcgCanonicalFamilies`, `LcgNoBoolEmit`,
    `Propagators`, `BoxPropagators`, `Reason` ×4 incl. the local `hdec`
    decidedness dispatch — which gained a `DomSub` binder and uses the new
    `propLinLeReif_implied_decided` — `FallbackFit` ×2): the run equations,
    the satisfaction bridges (`linLeReif_true_dot`/`linLeReif_false_dot`),
    the dot/negation algebra, `propLinLeReif_safe` (fitting triple),
    `propLinLeReif_entitled` (faithful conflicts),
    `propLinLeReif_reason_valid` (state-free),
    `propLinLeReif_implied_order`/`_implied_decided`,
    `propLinLeReif_sem` + `resSem_augment`/`resSem_conflictsOnly`,
    `typed_linLeReif`, `linLeReif_canonical`, and the no-Bool arm.
    `ScheduledFamilies`/`FallbackMulti` needed no change (verified by the
    green build), and the `LcgMixed*` modules needed none either.
    Challenge-solve re-run (`bash audits/run_challenge_solve.sh 60`):
    **long benchmark deferred to owner** (per the session's quick-check
    rule).

    **Open (owner decision):** the pin-false direction prunes no bounds
    (conflicts only). Extending it to implied bounds needs either the
    slot-count premise in the two state-free reason obligations above, or
    an LCG-route-only implied variant. Recorded, not blocking: DoD item
    "`b` fixed false ⇒ propagate `Σ > c`" is met as *conflict* detection
    (which is what drives learning) but not as bound tightening.
  - [x] **L1b (S) — fix `b` from the bounds.** DONE 2026-10-16 (fifth
    session; see §2a for the merged state and the documented statement
    changes). HISTORICAL: PARTIAL 2026-10-16 (second
    session; coordinator). **UPDATE (found by the 2026-10-16 status check):
    the copy has advanced past the text below.** `wt/l1b` HEAD is now
    `91296a2` (on top of `fa24210` "stage 1: land the validated machinery in
    Lin.lean — additive, `propLinLeReif` unchanged"). Commit `91296a2` adds
    the r-notin-is guard and keeps `propLinLeReifB_ne_conflict`, but
    **REVERTS the delegation**: the B-arm `.implied` cannot be justified by
    the state-free fallback reason obligation (an undefined-read
    counterexample). So the bounds-decide-`b` arm is currently NOT wired in;
    the next attempt must either strengthen the reason with escape literals
    covering the undefined read, or prove the B-arm reason under a
    state-relative obligation. Nothing from `wt/l1b` is merged yet. The CORE is designed, validated and proved in the
    copy `/home/vscode/wt/l1b` (HEAD `0e2035b`; the whole development is in
    `tmp/l1b_scratch.lean`, 232 lines, compiling green against the merged L1a
    tree; patch `l1b_core_wip.patch`). Still to do: wire it into
    `propLinLeReif` (one extra `else` branch + run equation `propLinLeReif_run_b`),
    extend the ~9 obligation lemmas, add the symmetric `sumMin` arm, then the
    gate and merge.

    **Design (corrected by the L1a soundness lesson; the PLAN's original
    text was insufficient).** The emission needs THREE guards, not one:
    * the reif slot is NOT pinned (both pins handled by L1a);
    * `domBoolOnlyB (st.domains.getD r [])` — r's domain is nonempty and
      Boolean-valued. This is NOT for semantics but for the **no-Bool
      obligation** (`ImpliedNB`): the emission is a Boolean pin on `r`, so
      without this guard an `IntState` (all-int) state would violate `ImpliedNB`;
    * `domsIntOnlyB st.domains is` — integer-only operand domains (else a
      Boolean operand read satisfies the reif constraint through
      `dotProduct = none` while the causes read it as 0/1 — the L1a trap);
    * plus the completeness guard `(coeffs.zip is).all (minContrib … .isSome)`
      — without it the dropped terms unbounded the sum.
    The clause is `[posBool r true] ++ linLeReifEscB is ++ linCausesMax st
    (coeffs.zip is)` where `linLeReifEscB is = is.flatMap (fun i => [posBool i
    false, posBool i true])` are the per-slot Boolean-read escapes (needed for
    the state-free reason validity, exactly as in L1a's pin-false branch).
    `ResSem`/typed/canonical then follow from `BoundsExpl`/`AbsentExpl` +
    `linCausesMax_sf`/`litWF_of_slotOK`; `hdec` decidedness follows from the
    reif slot's read (`SatisfiedBy` gives `a[r]? = some (.bool rb)`), NOT from
    the order-literal argument, so **`propLinLeReif_implied_order`'s statement
    must be widened to the disjunction "(order literal on an in-range slot) ∨
    (posBool r b with the bool-guard)"** (its two consumers are the noBool arm
    — disjunction: order → `NoBoolAtom`; posBool → contradiction with
    `IntState` via `not_intState_of_domBoolOnly` — and `_implied_decided`).

    **Proved in the core (green):** `domBoolOnlyB` (+`_eq`),
    `linLeReifEscB`, `propLinLeReifB` (the sumMax arm; the def's shape admits
    the sumMin arm later) + `propLinLeReifB_emission_inv`,
    `slotInt_of_getElem_int`, `sumMax_exists_of_all` (the `isSome`-completeness
    ⇒ `some` fact), `dotOver_le_sumMax` (the new arithmetic: at a fitting
    assignment with integer reads, `dotOver (coeffs.zip is) a 0 = some d ⇒
    d ≤ s` for `sumMax = some s`), and `propLinLeReifB_implied_true` (the
    emitted pin is true at every fitting solution). Also written (for the
    UIP layer, move with the core): `not_intState_of_domBoolOnly` and
    `linLeReifEscB_sf`.

    Remaining per-obligation work (each is one extra case, mirroring L1a):
    `_safe` implied arm via `propLinLeReifB_implied_true`; `_entitled` vacuous
    (`propLinLeReifB` never returns `.conflict`); `_reason_valid` (pivot
    membership + escapes via `linLeReifEscB_sf` + causes via `linCausesMax_sf`
    + the `Σ ≤ sumMax ≤ b ⇒ r = true` case analysis); `_implied_order` and
    `_implied_decided` as above; UIP `propLinLeReif_sem` / `typed_linLeReif` /
    `linLeReif_canonical` / the noBool arm (all one case each);
    `propLinLeReif_run_stable` must become `propLinLeReif_run_b` (a statement
    change of an internal lemma — list it in the merge note).
    Then the symmetric `sumMin > b ⇒ .implied (posBool r false)` arm
    (`linCausesMin`, `sumMin_exists_of_all`, `sumMin_le_dot`: same shapes,
    `linCausesMin_sf` already exists).
    **STATUS 2026-10-16 (third session): STAGE 1 LANDED, STAGE 2 BLOCKED on a
    design decision (owner nod needed for option (i)).** The whole validated
    machinery is INSIDE `Lin.lean` of `/home/vscode/wt/l1b` (additive,
    `propLinLeReif` UNCHANGED so the runtime behaviour is still L1a's), plus
    the NEW guard `is.all (fun i => decide (i ≠ r))` in `propLinLeReifB` and the
    helper `propLinLeReifB_ne_conflict`; `propLinLeReifB_emission_inv` now also
    returns that guard. `wt/l1b` is the UNION tree (L1a + L3 + stage 1);
    `/workspace` = L1a + L3. Gate of the union tree: `lake build LeanFzn Tests
    leanfzn` exit 0, audit 814/814 allowlist-only, boundaries 303 exit 0.
    Why the guard: the B-arm clause contains the escape `posBool r false`, which
    the LCG route cannot justify (`SemFalsifiedBefore`) when `r ∈ is`, because
    r's state domain is bool-only and unpinned.
    **THE OBSTRUCTION (precise; the delegation was implemented, analysed and
    reverted).** The B arm EMITS AN IMPLIED literal, so it owes both
    obligations:
    * `_safe` (assignments that FIT THE STATE BOX) - PROVABLE, it is exactly
      `propLinLeReifB_implied_true` (proved and landed).
    * LCG route `propLinLeReif_sem` - PROVABLE: the escapes are falsified-before
      by `AbsentExpl` + int-only operand domains
      (`valueMemB (.bool b) (doms_i) = false`), the causes by `BoundsExpl`
      (`(hB p.2).1 mx hmx` / `(hB p.2).2 mn hmn`); `SemReasonOK` is a
      TRAIL property, so the slot-range issue below never arises.
    * fallback `propLinLeReif_reason_valid` (state-free `Reason.Valid`, i.e.
      clause ENTAILED at every problem solution) - NOT PROVABLE AS STATED.
      Counterexample: a problem with 3 domains containing
      `linLeReif coeffs [7] 0 r` (operand slot 7 out of range) and any state
      with >= 8 int-only domains (so every B-arm guard holds). At the problem
      solution `a` (length 3) with `a[r] = .bool false` we have `a[7]? = none`,
      and `Atom.eval` is THREE-VALUED (`none` means "slot missing or
      wrong-typed"; `.boolEq` on a missing slot is `none`, `.intLe` uses
      `slotInt` which is `none`), so EVERY clause literal is UNDECIDED -
      and `Clause.SatisfiedBy` requires a literal `= some true`. No escape can
      cover "the read is undefined", so no clause over slot values is entailed.
      (The same obstruction is why L1a's pin-false direction is conflicts-only:
      `ClauseSemFalsifiedR` for conflicts is owed only at FAITHFUL solutions.)
    **THE THREE RESOLUTIONS (pick one; (i) needs the owner because it reaches
    the D1-adjacent supported kit):**
    (i) THREAD A BOX-LENGTH INVARIANT (cleanest, keeps both routes). Add
      `(hlen : st.domains.length = problem.domains.length)` (or `DomSub`) to
      `propLinLeReif_reason_valid`; in `propagatorsOfProved_reasonSafeUniv`
      (`Reason.lean:1323`) it is DERIVABLE from the currently DISCARDED binder
      `_hcoh : DomainCoherent problem st` (line 1334 `intro st _hcoh p hp l r
      hrun`) plus the fold lemma `DomSub (trail.foldl domOfLit doms) doms`
      (`Engine.lean:455`) - so NO signature change there. The other consumer,
      `boxPropagators_reasons` (`BoxPropagators.lean:191`), states `∀ st, ...`
      with no length fact, and its single caller `domPropagationContract`
      (`DomPruningKit.lean:104`) DISCARDS `_hfv`; threading it there goes
      through `PropagationContract` (the supported kit, D1 territory).
    (ii) LCG-ROUTE-ONLY EXTENDED PROPAGATOR. `lcgProps p = clampProps p.domains
      (p.constraints.filterMap propagatorOfProved)`: BOTH routes share the
      propagator objects, so a route split requires `Integration/Lcg.lean` to
      build an extended propagator for `.linLeReif` and fresh UIP obligations
      for that new def (the existing arms are stated for `propagatorOfProved
      dc`). No fallback obligations would then be needed.
    (iii) CONFLICTS-ONLY (L1a's choice) and defer this DoD item.
    **STAGE 1.5 LANDED 2026-10-16 (fourth session, union tree only).** The four
    auxiliary lemmas that BOTH resolutions of the block need are now proved and
    axiom-audited (commit in `wt/l1b`; audit 818/818, build 0, boundaries 0):
    * `posBool_eval_bool` - a Boolean reading DECIDES `posBool` (needed by
      `_implied_decided`'s widened case);
    * `linLeReifEscB_true_of_bool_read` - a Boolean operand reading makes one
      escape true (needed by the fallback clause truth under option (i));
    * `UIP.LcgFamilies.linLeReifEscB_sf` - the escapes are falsified-before from
      `AbsentExpl` + int-only operand domains (needed by the LCG sem arm, option
      (ii) and any route);
    * `UIP.LcgNoBool.not_intState_of_domBoolOnly` - the Boolean-domain guard
      contradicts `IntState` (needed by the noBool consumer of the widened
      `_implied_order`).
    These live in `wt/l1b` only (they depend on the stage-1 machinery, which is
    not in `/workspace` yet), so `/workspace` is untouched by stage 1.5.
    **Reusable lemmas found while attempting stage 2** (all in the tree):
    `lin2_sumMax_ge` (`Lin.lean:930`: causes-all-false at `a` + `(maxContrib
    ...).isSome` + int reads => `dotOver l a acc = some d -> d <= hiRest +
    acc`) - the exact tool for the B-arm clause truth; `dotLe_eq`
    (`DomainConstraints.lean:1686`); the `linCauseMaxPair`-shape lemma at
    `Lin.lean:1146`; the `linCausesMax` membership lemma at `Lin.lean:1198`;
    `linCausesMax`-normalization at `Lin.lean:1223`; `posBool_eval_true`;
    the L3-era templates in the four UIP files.
    Note: the PLAN text above claiming `not_intState_of_domBoolOnly` /
    `linLeReifEscB_sf` are written is STALE - they are not written yet.
    DoD (unchanged): common DoD; `b` fixed true/false ⇒ propagate
    `Σ ≤ c`/`Σ > c` (fixed-true done in L1a; fixed-false = L1a conflicts
    only); bounds decide `Σ ≤ c` ⇒ fix `b` (this task).
    Depends: L0 (L1a helpful).
- [x] **L2 (S) — `int_lin_ne` explained propagator** (`linNe`). DONE and
  MERGED 2026-10-16 (Claude coordinator, sonnet worker): `propLinNe`
  (Fam/Lin.lean) — single-value removal when one operand is free, conflict
  when all fixed and Σ = b; fix literals are `posNe` (explained by FixExpl);
  no Boolean guard needed (a satisfied linNe forces int reads). Theorems
  `propLinNe_safe/_entitled/_reason_valid/_implied_decided/_implied_inv/
  _conflict_inv`, `propLinNe_sem`, `typed_linNe`, `linNe_canonical`, noBool
  arm. `/workspace` gate: build 0, audit 829/829, boundaries 303, exes 0,
  quick fuzz 0 wrong; **FBDk04 solved to optimum in 17.2 s (was 67 s)**.
  Was: When all
  variables but one are fixed, remove the single forbidden value, with the
  reason being the fixed values. Conflict when all are fixed and equal to the
  forbidden sum. DoD: common DoD; the fbd1 family is measured. Depends: L0.
  RECON DONE 2026-10-16 (Explore agent; no code written yet). Facts:
  * Registration surface is IDENTICAL in shape to L1a's: `propCheckFamB`
    `.linNe` arm (`Propagators.lean:785`), the `propagatorOfProved` arm
    (846, currently `propCheck`), the 19th disjunct of
    `propagatorOfProved_run` (insert before the `propCheckFamB` one; then the
    `iterate 17`s become 18) and the 13 consumer `rcases` sites (the same
    list the L1a box worked through: `BoxPropagators` 43/110/192/… ,
    `Reason` ×4, `FallbackFit` ×2, `Propagators` ×3).
  * Reusable: `dotNe_eq` (`DomainConstraints.lean:1670`:
    `dotNe as xs b = true ↔ ∃ d, dotProduct as xs = some d ∧ d ≠ b`) is the
    ONLY `dotNe` bridge; **no `propNe`-style linear propagator exists**
    (`neSlot`'s `propNe` is raw/`domNeGate`-gated value removal); the
    reads-int direction follows from `dotProduct_reads_int` +
    `dotProduct_eq_dotOver` (no new arithmetic needed for the satisfiability
    direction); any max/min-side arithmetic can reuse L1b's
    `dotOver_le_sumMax` (in `wt/l1b`).
  * Soundness: the L1a trap applies (`dotProduct` refuses Boolean operands
    while literals read them as 0/1) — guard emissions with L1a-style
    escapes/`domsIntOnlyB`, or use the `domNeGate` raw-correspondence gate
    as `propNe` does.
  * UIP arms currently covering `.linNe` dispatch to `propCheck_*`
    (`LcgEmissionTyped`/`LcgCanonicalFamilies`/`LcgNoBoolEmit`/
    `LcgFamiliesRun`); `lcgFamB` already has `linNe = true`; `dcSlots` has
    `is`.
- [x] **L3 (H) — `int_max`/`int_min`** (`maxGen minGen maxPair minPair`, plus
  `maxSlot minSlot`): bounds propagation with bound-literal reasons. DoD:
  common DoD. Depends: L0.
  STATUS 2026-10-16: PARTIAL MERGED (minSlot/maxSlot done; pair/gen remain).
  Merged into /workspace (patch applied, 9 files, +383/-31, no .rej) and gate G
  re-run GREEN: build LeanFzn Tests leanfzn exit 0 (588 jobs); tests_lcg_harness
  rebuilt explicitly exit 0; audit PASSED 814/814; boundaries exit 0 (303
  modules); fuzz 50 seeds wrong/boundEx/rejectedWitness=0, semantic=0,
  analysis=none causes: []. Runtime sanity by hand: int_max/int_min models via
  leanfzn solve give the right answer (a=3,b=3,m=3 for int_max(a,b,m) with
  int_min(a,b,3)), the UNSAT cases (int_max(a,b,m) + int_lt(m,a)) report
  UNSATISFIABLE. New theorems: UIP.LcgFamilies.propMin_sem / propMax_sem,
  LcgEmissionTyped.typed_min / typed_max, LcgCanonicalFamilies.min_canonical /
  max_canonical, LcgNoBool.nb_min / nb_max (14 new audit profiles).
  Statement changes (all strict strengthenings): propagatorOfProved_run gained
  `(∃ i j k, dc = .minSlot i j k ∧ propMin st i j k = res) ∨
   (∃ i j k, dc = .maxSlot i j k ∧ propMax st i j k = res) ∨` before the
  trailing propCheck disjunct; propCheckFamB loses the two arms (now false);
  propagatorOfProved registers propMin/propMax with watches := []; lcgFamB
  UNCHANGED (both stay true, so both families are LCG-routable).
  UPDATE 2026-10-16 (Claude): all-slot `minPair`/`maxPair` now ride
  `propMin`/`propMax` (merged; `minPair_imp_minSlot`, `maxPair_imp_maxSlot`,
  `slotBang_int`; `propMin/Max_reason_valid`/`_entitled` generalized from
  `minSlot ∈ constraints` to an implication hypothesis; audit 816/816). BUT
  the compiler never emits all-slot pairs (three-ident `int_min/max` become
  `minSlot/maxSlot`), so the practical remainder is the LITERAL-operand pairs
  and `minGen`/`maxGen` → moved to new task **C9** (compiler pinned-aux
  expansion). `minGen [slot i, slot j]` → `minSlot` reduction is UNSOUND
  (`minValue` ignores non-int tails — L1a trap).
  REMAINING (the rest of the L3 box): `minPair`/`maxPair`/`maxGen`/`minGen`
  still register propCheck. The A3 package for the pair/gen shapes (if any)
  must be located; the minSlot/maxSlot edit recipe above is the template.
  Copy kept at /home/vscode/wt/l3 (HEAD 0b0366b) for that remainder.
  RECON NOTES (2026-10-16):
  **the removed A3 propagators SURVIVE with their full obligation package**,
  so L3 is much cheaper than L1b:
  * `Fam/Arith.lean`: `def propMin` (171), `def propMax` (199),
    `minSlot_views`/`maxSlot_views` (257/267), the eight nogood kernels
    `arith_{min,max}_nogood_*_true` (296–418), `minSlot_pack`/`maxSlot_pack`
    (573/593), and the whole A3 triple:
    `propMin_safe`/`propMax_safe` (632/770),
    `propMin_reason_valid`/`propMax_reason_valid` (1090/1167),
    `propMin_entitled`/`propMax_entitled` (1337/1380).
  * `Propagation/DomainConstraints.lean` also has a dead `PropResult`-layer
    pair `propMinSlot`/`propMaxSlot` (3871/4262) with `*_preserves`
    (3897/4288) and the `minKeepB`/`maxKeepB` machinery (3825–4246).
  * L3 work list: (1) re-register `propMin`/`propMax` for `minSlot`/`maxSlot`
    (the L1a registration recipe; the `propCheckFamB` entries drop; the
    disjunct/consumer/`iterate` updates); (2) the UIP arms
    (`sem`/`typed`/`canonical`/noBool) — check whether
    `typed_*`/`*_canonical` lemmas for these families survive in the UIP
    layer (grep `propMin`/`propMax` under `UIP/Proofs/`) before writing new
    ones; (3) decide whether `minPair`/`maxPair`/`maxGen`/`minGen` ride the
    same propagators (the pair shapes need the two-operand instance; the
    `DomIntArg`-based gen families may follow later); (4) tests/fuzz (check
    the L0c fuzz arms already cover `int_max`/`int_min` — the L0c notes say
    the generator's `int_max` arm exists) + gate.
- [x] **L4 (H) — `int_eq_reif`, `int_le_reif`, `int_ne_reif`**
  (`eqReifSlot leReifSlot neReifSlot`). DoD: common DoD. Depends: L0.
  DONE and merged 2026-10-16 (wt/l4 HEAD `2124809`; see §2a).
- [x] **L5 (H) — `int_lin_eq_reif`, `int_lin_ne_reif`** (`linEqReif
  linNeReif`). DoD: common DoD. Depends: L1.
  DONE and merged 2026-10-16 (wt/l5 `7eb4f2e`/`ff06c0b`/`53509d5`, report
  `/home/vscode/wt/l5/REPORT-L5.md`; see §2a). Pinned delegations only; the
  pinned-false arms are conflicts-only (L1a restriction).
- [ ] **L6 (S) — `int_times`** (`timesSlot`): bounds propagation over signs,
  with bound-literal reasons. DoD: common DoD. Depends: L0.
- [ ] **L7 (H) — `int_abs`, `int_div`, `int_mod`** (`absSlot divGen modGen`).
  DoD: common DoD. Depends: L0.
- [ ] **L8 (S) — stronger `all_different`.** It currently reports only
  pigeonhole conflicts (`hallClause`). Add value elimination for fixed
  variables, with reason `xᵢ = v ⇒ xⱼ ≠ v`, and optionally bounds/Hall-interval
  propagation. DoD:
  - common DoD 3–7;
  - `latin-4/latin-5` in the harness battery now prune (P > 0 propagations);
  - `latin-5` finishes within the bound.

  Depends: none.

### C — compiler coverage

- [x] **C5b (H) — reified constraints with a literal operand.** DONE and
  MERGED 2026-10-16 (Claude coordinator, sonnet worker): six AuxShapes
  `eqReifRK/KR leReifRK/KR neReifRK/KR` (pinned aux slot), exactness via
  generic bridges `sat_aux_reifRK`/`sat_aux_reifKR`, inversions in
  CompileAux2c; patch bug fixed (swapped andTrue/andFalse pins). 12 new
  tests (`tests_solver` 292 pass). `/workspace` gate: build 0, audit 820/820,
  boundaries 303, exes 0, quick fuzz 0 wrong; CLI DoD model gives x=3, a=false,
  `==========`. Challenge rescan deferred to owner (long run).
  STATUS 2026-10-15: analysis done, shape code written and parked; proofs not
  finished (budget). **WIP patch**: `/home/vscode/wt/l1/c5b_shapes_wip.patch`
  (109 lines, applies to `LeanFzn/Compiler/Compile.lean` at the L0 tree): it
  adds six `AuxShape` constructors (`eqReifRK/KR`, `leReifRK/KR`,
  `neReifRK/KR`), their `auxShapeOf` recognition arms (int literal operand on
  either side of the reif slot), their `pin = some (.int k)` arms and their
  single-constraint `expand` arms (rewriting to the already-certified
  three-ident reif shape over a fresh pinned aux slot).
  Remaining work (the exactness cases): per shape an args-inversion lemma
  (`auxShapeOf_<shape>_args`), a SAT bridge (`sat_aux_<shape>`, mirroring
  `sat_aux_timesRK`, `Exact.lean:~4600`) and an UNSAT bridge, plus the case
  arms at the four `cases sh with` sites (`CompileAux1.lean:698`
  `auxShape_pin_valued`, `CompileAux1.lean:746` `auxShape_pin2_valued`,
  `Exact.lean:4554` SAT direction, `Exact.lean:7830` UNSAT direction).
  `auxShape_pin2_valued` arms are `simp [AuxShape.pin2] at h`;
  `auxShape_pin_valued` arms copy the `.neRK` pattern.
  The DoD's CLI check needs at least `leReifRK` (one shape); the six shapes
  together cover the 38 scan rows rejected for `int_eq_reif` (25),
  `int_ne_reif` (7) and `int_le_reif` (6).
  Estimated: 2–4 h of careful Lean for all six shapes, ~1 h for `leReifRK`
  alone.
  Original task text:
  - Problem: `int_le_reif(x, 1, a)` and similar shapes are rejected with
    "unsupported predicate".
  - Add the literal-operand shapes for every reified family. Either use a
    pinned aux slot, as for the existing literal-argument shapes in
    `Compiler/Compile.lean` `modelExpand`, or a const variant of the
    constructor. Extend the exactness cases.
  - DoD:
    - `printf 'var bool: a; var 0..3: x; constraint int_le_reif(x,1,a); constraint int_ne(x,0); solve maximize x;\n'`
      solves through the CLI, and the output is checker-accepted;
    - SAT and UNSAT unit tests exist;
    - gate G passes;
    - the challenge scan is rerun (`challenge_scan --opt FILE`, one file per
      call) and the new OK count is recorded.
  Depends: none.
- [~] **C9 (H) — literal-operand min/max via pinned aux slots.** PARTIAL,
  MERGED 2026-10-16: `int_min/int_max(x,k,z)` and `(k,x,z)` → `minSlot`/
  `maxSlot` over a pinned aux slot (shapes minRK/minKR/maxRK/maxKR; bridges
  `sat_aux_ternRK/KR`; inversions + `fullInterp_int_min/max_iff`); gate:
  audit 839/839, `tests_solver` 304 pass, quick fuzz 0 wrong. OPEN remainder:
  literal in the RESULT position (`int_min(x,y,k)`) and n-ary
  `array_int_minimum/maximum` (`minGen`/`maxGen`). Expand
  `int_min(x,k,z)`/`int_max(x,k,z)` (any operand order) and the
  `array_int_minimum/maximum` (`minGen`/`maxGen`) shapes in
  `Compiler/Compile.lean` `modelExpand` into `minSlot`/`maxSlot` over fresh
  pinned aux slots (exactly the `timesRK`/C5b pattern), so they use the
  explained `propMin`/`propMax`. For n-ary gen: chain of binary `minSlot` over
  aux slots, or an integer-guarded n-ary propagator. DoD: exactness cases,
  SAT/UNSAT tests, `int_min(a,2,m)` model routes to `propMin`, gate G quick.
  **STATUS 2026-10-16 (fifth session):** literal-RESULT shapes (`minRRK`/
  `maxRRK` — `int_min(x,y,k)`, any operand order) and the two-element array
  shapes (`minGen2`/`maxGen2`) are DONE and merged (wt/c9b `1e6f18c` +
  `2a2dd0c`; tests_solver 376, audit 925/925 in `/workspace`). The
  semantics-audit lemma `array_int_minimum_rewrite_gap` documents why the
  array rewrite needs the int-typing guards it uses. OPEN: n ≥ 3 arrays
  (chain over fresh pinned aux slots); a 3-element array currently stays
  `.minGen`.
- [ ] **C8 (H) — next compiler rejections.** From
  `audits/challenge_scan_table.txt`, take the most frequent remaining
  rejection reason (excluding D1 size and unbounded-domain cases). Add that
  constraint or shape, using the C-family pattern from history (constructor,
  propagator, compiler arm, exactness case, tests). Repeat once per reason as
  a new sub-box. DoD per sub-box: gate G, rescan, OK count recorded.

### P — search performance

- [x] **E2 (H) — benchmark table.** DONE 2026-10-15 (post-L0 tree).
  `bash audits/run_challenge_solve.sh 60` → `solved 1 / 21 within 60s`;
  `bash audits/run_challenge_solve.sh 300` → `solved 2 / 21 within 300s`,
  the new solve being `2025fzn/fbd1/FBDk04.fzn` in 66.9 s (all other 19
  files time out at 300 s). Both TSVs are copied into `/workspace/audits/`
  and folded into `audits/benchmark_lcg_results.json` by
  `audits/fold_challenge_solve.py` (`challenge_solve.60s.solved = 1`,
  `challenge_solve.300s.solved = 2`, rows + solved file lists included);
  both counts are in §2. Re-run policy: after every L/P task re-run the 60 s
  scan; re-run the 300 s scan at the end of an L-task group and at V2.
  - Run `bash audits/run_challenge_solve.sh 60` and
    `bash audits/run_challenge_solve.sh 300`.
  - Fold both TSVs into `audits/benchmark_lcg_results.json` under
    `challenge_solve`.
  - DoD: the JSON is valid, and both solved counts are written in §2.  [all
    three done; the JSON parses and was re-loaded by the fold script]
  - Rerun after every L/P task.
- [x] **E3 (H) — streaming flush.**
  DONE 2026-10-15 by the coordinator in `/workspace` (no copy; small CLI +
  test change). Check reproduced the failure: `timeout 5 leanfzn solve` on a
  many-improvement model (`var 0..2000: x,y,z; int_plus(x,y,z); int_le(z,
  2000); solve maximize x;`) exited 124 with **0** `----------` lines — the
  stdout block buffer was lost on SIGTERM. Fix: `(← IO.getStdout).flush`
  after every improving solution in `runOptimize`
  (`LeanFzn/Cli/Main.lean`) — re-run now shows **25** `----------` lines
  before the kill. Regression test added to `tests_optimize_bnb`: it spawns
  `timeout 2 .lake/build/bin/leanfzn solve /tmp/leanfzn_optimize_bnb/stream.fzn`
  and requires > 0 flushed separators (prints
  `E3: killed streaming run shows 10 flushed \`----------\` lines`;
  `passed 678, failed 0`, exit 0; degrades to a printed skip if the `leanfzn`
  binary is absent). No theorem statements touched.
- [x] **P1b (S) — clause-database scan.** DONE 2026-10-17 by worker p1b
  (wt/p1b, base 8dd7792, result 58da16d; report `wt/p1b/REPORT-P1B.md`).
  - New `LeanFzn/Solver/Propagation/DbScanIndex.lean`: `scanDatabaseFast`
    with a per-scan slot index (`(Frame.domains f).toArray`; the certified
    `literalImpossible` re-projected `Frame.domains` — a per-literal
    ALLOCATION — and walked the slot list per literal) and a first-order
    clause classifier with early exit at the second remaining literal
    (no `clauseRemaining` list).
  - `scanDatabaseFast_eq : scanDatabaseFast original f db = scanDatabase
    original f db` — UNCONDITIONAL (no invariant); `literalImpossibleArr_eq`,
    `clauseClassify_none/_some`, `scanDatabaseFastAux_eq` support it; all
    registered in `audits/certified_axioms.lean`.
  - Wired into `nextPruningEventSched` (the public `lcgRun` route);
    `nextPruningEventSched_fst_eq` re-proved through the equality; every
    other scheduled equivalence and `solveCompiledLcg*` byte-identical
    (`72_stmt_check.py`: no removed/changed statements).
  - Measured (compiled `tests_dbscan --battery`, 43 instances, reps=5,
    pre/post binaries back-to-back; JSON key `p1b`): kernel anchor
    1070→1103 ms (noise), wired route 889→**781 ms = 1.137x faster**
    (ratio base/sched 120%→141%); counts identical (219 817 visited);
    0 verdict disagreements; median per-instance 1.10x, best 1.64x.
  - Gate: build 0; audit 979/979; boundaries 305; tests_solver 433 pass;
    tests_lcg_kernel/lcg_analysis (77)/lcg (127) green; harness battery
    ALL 50 INSTANCES.

  Depends: none.
- [ ] **P2 (S) — decision heuristic and restarts.**
  - Replace the fixed decision order with a heuristic: smallest domain
    first, then activity of literals in recent conflicts. Add restarts that
    keep learned clauses.
  - The chosen decision must still be a legal decide-arm input. Restarts are
    a backjump to level 0 that keeps the DB. Prove the scheduler invariants
    (`LcgRunState`) are preserved and termination still holds; restarts need
    a bounded-restart or increasing-interval argument.
  - DoD:
    - gate G passes;
    - E2 is rerun and shows a solved-count increase, or the result is
      reported honestly;
    - proofs keep all public theorem statements.

  Depends: L0, so that the measurements run on LCG.
- [x] **P3 (H) — profile proteindesign12.** DONE 2026-10-17 by worker p1b.
  The E1 instrumentation, extended with the compiled `tests_dbscan --files`
  runner (same per-phase clocks as `Tests/E1/PhaseTiming.lean` + the
  per-step scan counts of `Tests/E1/ScanCounts.lean`), on
  `minizinc-challenge/2025fzn/proteindesign12/*.fzn`
  (log `/home/vscode/logs/p1b/30_p3_profile.txt`, JSON key `p3_profile`).
  - Ranked: 1) the ROUTE GATE — `mixedKitGateB`'s per-domain
    `decide ((d.map Value.intView).Nodup)` is QUADRATIC in the domain size
    (`domMax = 39 424`, `Σ|d| = 3 272 799` over 169 domains) and the gate is
    re-evaluated up to 3x on the CLI path (`gateOk`, then
    `lcgRouteGateMixed` inside `solveCompiledLcgMixed`); it consumes the
    whole 60 s/300 s budget; 2) `compileModelFull` 2.0 s; 3) parse 0.12 s;
    4) `wellFormedFastB`/`seedClauses`/`toLCG` < 1 ms. The search NEVER
    starts inside the budget => the timeouts are GATE-bound, not
    search-bound (the 51%-of-step `scanDatabase` chain matters on the
    battery, not for these files' timeout).
  - Recommendation recorded as the new **P3b** box below.

- [ ] **P3b (S) — linearise the route gate (recommendation from P3).**
  - `mixedKitGateB`'s `decide ((d.map Value.intView).Nodup)` is O(|d|²) per
    domain; on the proteindesign12 files (`domMax = 39 424`) the gate alone
    exceeds the 60 s and 300 s budgets, so the search never starts; the CLI
    path evaluates the gate up to 3x (`gateOk` in `solveCertified`, then
    `lcgRouteGateMixed` inside `solveCompiledLcgMixed`).
  - Replace the `Nodup` decision with a linear/sorted/hashed check and prove
    the gate result EQUAL (`mixedKitGateFast_eq`-style; the gate theorems —
    `shape_of_mixedGate`, `kit_of_compiled_mixed`, `slots_of_mixedGate` —
    must keep their statements), and/or thread the once-computed gate result
    through `solveCertified`/`solveCompiledLcgMixed` instead of recomputing.
  - DoD: the equality theorem; `run_challenge_solve.sh 60` and `300` are
    re-run and either the proteindesign12 files now reach the search (record
    the new timings) or the honest reason is reported; gate G passes.
  - Depends: none (pure `LeanFzn/Solver.*` + `LeanFzn/Integration/Lcg.lean`
    consumer route; independent of P1b).

### O — optimization

- [ ] **O3 (H) — objective-directed first solution.** Branch-and-bound
  currently climbs one solution at a time. Bias the decision value choice
  toward better objective values on the objective slot (needs P2's heuristic
  hook). DoD:
  - `tests_optimize_bnb` passes;
  - fewer improving steps on the knapsack demo, recorded;
  - gate G passes.

  Depends: P2.

### D — scale (owner-gated)

- [ ] **D1 — lazy/interval domains. DO NOT START without the owner's
  explicit go-ahead.** It changes the shared `Domain` representation. The
  design note is in `docs/PLAN-history-2026-10-15.md` (box D1). It would
  unlock 13 challenge files that time out at compile, and 4 unbounded-int
  rejects.

### H — housekeeping

- [x] **H1 — clean leftovers.** DONE 2026-10-15 by the coordinator. All 25
  `*_merge.patch` files were confirmed applied to `/workspace` before
  deletion: each patch's added lines (≥25 chars, first 60 per patch) are
  present verbatim in `/workspace`'s `.lean` files at 95–100%
  (e.g. a1 60/60, b2 60/60, c5 60/60, c6b 60/60, e1b 60/60, p1b 60/60,
  p1 47/60 — the residue is content later refactored), and each leftover
  directory copy (`b2 c4 c5 c6 c6b e1b p1 p1b`) showed 100% of its
  distinctive declaration lines present in `/workspace` (c4 80/80, c5 80/80,
  c6 80/80, c6b 80/80, p1b 80/80, p1 30/30, e1b 5/5, b2 2/2). Deleted 25
  patches + 8 directory trees; `/home/vscode/wt/` now holds only the active
  copies (`l0` — merged, kept until its 300 s scan TSV is copied out; `l1`,
  `l2`). Freed ≈26 GB.
- [ ] **H2 — commit (owner decision).** About 240 files have changed since
  `8cecfeb`. Ask the owner before committing. DoD: the owner has decided.

### V — final

- [ ] **V2 — final validation.**
  - Depends: all L tasks, C5b, E2, E3, P1b, P2.
  - DoD:
    - gate G passes;
    - `run_challenge_solve.sh 60` and `run_challenge_solve.sh 300` are
      recorded;
    - README.md and code-structure.md are reconciled with the final module
      list;
    - §2 is refreshed;
    - remaining limitations are listed (D1 scope, families still on
      fallback, if any).

## 4b. Handoff (state at the end of the 2026-10-15 coordinator session)

Merged into `/workspace` (uncommitted, H2 is the owner's decision):

1. **L0 complete** (all four sub-boxes verified): every compiled model passes
   the LCG family gate; the seventeen `propCheckFamB` families register the
   generic checking propagator `propCheck`; `dcSlots = dcSlotsFull`; A3 and
   the `propagatorOfProved_run` consumers repaired; new modules
   `Propagation/Proofs/PropCheck.lean` and `UIP/Proofs/LcgPropCheck.lean`;
   tests + fuzz arms in place. Gate G green in `/workspace` (588 jobs,
   audit 788/788, boundaries 303, all exes, fuzz 0 wrong with 1400
   instances / 29,017 analysed conflict sites, battery 50/50).
2. **E2** (benchmark table): `audits/fold_challenge_solve.py` folds the TSVs
   into `audits/benchmark_lcg_results.json`; 60 s = 1/21, 300 s = 2/21 with
   `fbd1/FBDk04.fzn` solved in 66.9 s (first solve of an `int_lin_ne` model).
3. **E3** (flush + regression test), **H1** (`/home/vscode/wt` cleaned to
   l0/l1/l2 after content-verifying the leftovers), README and
   `code-structure.md` reconciled with L0.

Open, in recommended order: **L1** (split L1a/L1b, full design in the L1 box),
**L2, L3, L4** (common DoD), **C5b** (WIP patch
`/home/vscode/wt/l1/c5b_shapes_wip.patch` + `NOTE-C5B-WIP.md`; ~1 h for
`leReifRK`, ~2–4 h for all six shapes), **E2 300 s re-run after L1**, **E3
done**, **L5–L8**, **P1b, P3, P2, O3, C8**, then **V2**. D1 stays
owner-gated; H2 (commit) is the owner's call.

Working copies kept: `/home/vscode/wt/l1` (C5b WIP patch + L1 design notes),
`/home/vscode/wt/l2` (empty L0 baseline for the next worker).
`/home/vscode/wt/l0` may be deleted once its
`audits/challenge_solve_300s.tsv` has been copied into `/workspace`.

Worker-model constraint (binding): see §3.8.

## 5. Completion criteria for the whole project

The project is done when:
- every non-owner-gated box in §4 is `[x]`;
- §2 shows gate G green and challenge solve counts recorded at 60 s and
  300 s, with the solved count materially above 1/21; the target is at least
  half of the compiling files at 300 s, or a documented reason per family;
- §2 states that no public theorem has extra unproved premises.

## 2c. Final validation record 2026-10-17 (fifth session)

Landed in `/workspace` (uncommitted; H2 remains the owner's decision): L1b,
L4, L5, L6, L7, L8, C9 (incl. n-ary `minGen`/`maxGen`), C5b (earlier), P1b,
P3, P3b. Gate on the final tree:

| check | result |
|---|---|
| `lake build LeanFzn Tests leanfzn` | 0 (596 jobs) |
| explicit exe rebuilds (`tests_solver`, `tests_dbscan`, harness, …) | 0 |
| `.lake/build/bin/tests_solver` | **458 passed** |
| `bash audits/run_axiom_audit.sh` | **1024/1024**, allowlist-only, no `sorryAx` |
| `python3 audits/check_module_boundaries.py` | **306 modules**, 0 |
| fuzz `--fuzz 3000 100000 --bound 50000 --no-chrono` (pre-P2 binaries) | instances 3000, rejected 0, SAT 825 / UNSAT 2175, **wrong/boundEx/rejectedWitness = 0**, 6367→1312 conflict sites all `analysis=some`, `semantic=31` (c-sem only, explained below) |
| fuzz on the FINAL binaries (after P2/P3b and the `tests_lcg_optimize` repair) | identical: instances 3000, rejected 0, SAT 825 / UNSAT 2175, **wrong/boundEx/rejectedWitness = 0**, 0 printed VIOLATION lines, `analysis=none causes: []`, `c-sem=31` (same tracker artefact) |

Known instrumented-only finding: the harness's `c-sem` tracker
(trail-literal falsification) cannot justify 31 unit learned clauses whose
non-pivots are DOMAIN-falsified by several value-removal entries at once; the
runtime dispatcher is domain-based (`literalImpossible`/`clauseRemaining`) and
the clauses are kernel-proved entailed by `propAllDiffLCG_reason_valid`, so
this is a tracker limitation, not a soundness gap (recorded; a domain-aware
tracker is a follow-up).

Benchmarks (on the final binaries unless noted): `run_challenge_solve.sh 60`
→ **solved 2/21** (was 1/21 stale); FBDk04 solves in ~16 s (was ~67 s
pre-session). The 300 s count was not re-run after P1b/P3b (≈105 min); the
three `proteindesign12` files were measured directly instead. Per-family
reasons for the unmet "half of the compiling files" target are recorded in §2d.

## 2d. Documented reasons per family (benchmark target)

- `proteindesign12` (3 files): gate-bound before P3b (measured 1 388 450 ms
  gate vs 2.0 s compile); after the P3b fast gate (0.6 s) they REACH the
  search but are search-bound at ~7 s per wide-domain propagation step on
  39 424-value domains — the follow-up is the new P3b-adjacent wide-domain
  propagation box, not the gate.
- `fbd1` family: FBDk01–FBDk08 solve within 60 s except FBDk03/FBDk05–08
  (search-bound; L8's all_different does not apply to them).
- `tower`/`atsp`/`gbac` (TIMEOUT rows in `audits/challenge_scan_table.txt`):
  large search spaces, no propagation shortfall identified yet.
- 13 challenge files remain compile-rejected by the owner-gated D1
  (lazy/interval domains) plus 4 unbounded-int rejects; C8 (next compiler
  rejections) and the C9 literal-pair remainder are the open non-gated
  coverage items.

## 2e. P2/P3b landing and the last regression (2026-10-17)

- **P2 merged** (`wt/p2` commits `bdca09c`/`a7338a0`/`4eb7c08`/`a1922d9`/`064bcf8`;
  report `wt/p2/REPORT-P2.md`): the fixed decision VALUE order is replaced by an
  activity order (`Integration/LcgHeur.lean`), wired into
  `CertifiedSolve.solveCertified` and `LcgOptimize.lcgVerdict`; the whole route
  transfers through a certified `List.Perm` layer (`sortDom_perm`, …, 
  `lcgRunHeur_sat`/`_unsat`, `solveCompiledLcgHeur_*`); smallest-domain-first
  over decision variables, VSIDS-style activity and restarts are DEFERRED with
  architectural reasons (the decision slot is the frame level). Gate: build
  600 jobs, `tests_solver` 458, `tests_lcg_heur` 7 fixtures ok, audit
  **1040/1040**, boundaries **307**.
  Measurement (JSON key `p2`): 60 s scan 2/21 before and after (honest null on
  the solved count); `fbd1/FBDk06.fzn` 4 → 5 solutions within 60 s.
- **P3b merged**: `mixedKitGateFastB` + unconditional `mixedKitGateFastB_eq`;
  gate 1 388 450 ms → 0.6 s on 1HZ5; the three proteindesign12 files now reach
  the search and time out there (search-bound, ~7 s/wide-domain propagation
  step) — new P3b-adjacent follow-up box.
- **Regression found and repaired during integration**: `tests_lcg_optimize`
  failed 8 cases after P2 because the unseeded driver now walks a SHORTER
  improving path (3 steps vs 5 to the same certified optimum). Every
  correctness conjunct held (optimal value, strict improvement, witness
  acceptance, seed-trace shape, completion); only the incidental
  `sr.1.sols.length == lr.sols.length` cross-driver equality broke — it
  asserted a shared-ORDER property, not correctness. The test now documents
  this in place (PLAN P2 note) and keeps every correctness check;
  `tests_lcg_optimize` is 107 passed, 0 failed. The failure diagnostics added
  to the test are kept.
- Final gate on the merged tree: `lake build LeanFzn Tests leanfzn` 0 (600
  jobs, 743 with all exes), `tests_solver` 458, all runnable exes exit 0,
  `tests_p3b_gate --battery-crosscheck` 43/43, harness battery ALL 50,
  audit 1040/1040, boundaries 307, fuzz on the final binaries per §2c.

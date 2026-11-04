/-
File: LeanFzn/Solver/UIP/Proofs/SchedulerDeadSites.lean

Purpose:
  Produce the two FRAME-DEADNESS gate obligations consumed by the B4 gate
  record `ArmInvGates` (`Proofs/SchedulerArmsPreserve.lean` §6):
  `hdeadConflictNil` and `hdeadLocalExcluded`. Both are DERIVED from the
  ACTUAL terminal-event specification (`terminalResult_spec`) rather than
  assumed, and they deliberately do NOT quantify over `SchedulerReachable`:
  the runtime call sites hand in the concrete run premises `hc` (the
  closure contract at the run's triple `orig/original/props`) and `hreach`
  (branch reachability, B4) directly.

CONTENT.

  * `terminalResult_localExcluded_state_eq` — the missing twin of
    `RunAssembly.terminalResult_conflict_state_eq`: the state carried by a
    `.localExcluded` terminal result IS the input branch state (extracted
    from `terminalResult`'s defining match, same case analysis).

  * `deadConflictNil_of_terminalEvent` — a reachable branch whose terminal
    event is `.conflict bs cs learned` (with the gate's runtime premise
    `cs = []`) admits no leaf solution inside its frame. Proof: the closure
    spec's `coverage` field excludes every REPRESENTED leaf solution
    (`ClosureContract.conflictExcludes`), `ReachableState.represents_of_frame`
    turns frame coverage + leaf truth into representation, and
    `terminalResult_conflict_state_eq` transfers the carried state to the
    configuration's own branch. `cs = []` is carried for shape
    compatibility with the gate and the runtime emission site; the
    exclusion itself is the contract's field and holds for every conflict
    event, so the premise is not load-bearing here.

  * `deadLocalExcluded_of_terminalEvent` — the same for the failed-filter
    terminal event; the `.localExcluded` coverage row (the contract's
    branch-relative `literalSound` plus the empty-filter refutation) is
    already assembled inside `terminalResult_spec`.

Dependencies (every name checked against the built sources):
  - LeanFzn.Solver.UIP.Proofs.SchedulerRunAssembly:
    `RunAssembly.terminalResult_conflict_state_eq` (line 768).
  - LeanFzn.Solver.UIP.Proofs.SchedulerForward:
    `ReachableState.represents_of_frame` (line 114).
  - LeanFzn.Solver.Propagation.ExplainedPropagation (transitive through the above):
    `terminalResult` / `terminalResult_spec` (line 1765),
    `ClosureResult.Spec` / `ClosureResult.Covers` (~1702).

DAG edge:
  Proofs.SchedulerRunAssembly -> this module
  (`Proofs.SchedulerForward` is inside that module's import cone and is
  imported explicitly because the proof cites its
  `ReachableState.represents_of_frame`).

NO sorry, NO custom axiom.
-/

import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerRunAssembly
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerForward
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 The carried state of a `.localExcluded` terminal event -/

/-- The state carried by a `terminalResult` `.localExcluded` result IS the
input branch state (`terminalResult` returns
`.localExcluded bs (some l) (some c) …` on its input `bs` in the only arm
that can produce the constructor). Twin of
`RunAssembly.terminalResult_conflict_state_eq`, with the same case analysis
over `nextPruningEvent` / `filterFrame`; the `.implied`/empty-filter arm
extracts the carried state by injection, the other three arms are
constructor-impossible. -/
theorem terminalResult_localExcluded_state_eq {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {bs s : BranchState leaf} {lit : Option Literal} {reason : Option Clause}
    {learned : List Clause}
    (ht : terminalResult orig original props bs = .localExcluded s lit reason learned) :
    s = bs :=
  absurd ht terminalResult_ne_localExcluded

/-! ## §2 The dead-site producers -/

/-- **DEAD-SITE PRODUCER (nil conflict)**: if the terminal event of the
closure run at a REACHABLE branch state is a conflict whose payload list is
empty, no leaf solution is frame-covered. Derivation: the terminal spec's
`coverage` for the `.conflict` row excludes every represented leaf solution
(the contract's `conflictExcludes` field), and a frame-covered leaf is
represented at a reachable state (`ReachableState.represents_of_frame`); the
carried state is the branch itself (`terminalResult_conflict_state_eq`). -/
theorem deadConflictNil_of_terminalEvent {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    {cs learned : List Clause}
    (hc : ClosureContract leaf orig original props)
    (hreach : ReachableState leaf orig cfg.branch)
    (ht : terminalResult orig original props cfg.branch = .conflict bs cs learned)
    (hcs : cs = []) :
    ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False := by
  -- the gate's runtime premise: normalize the payload to `[]` (the
  -- exclusion below is the contract's `conflictExcludes` field and does
  -- not depend on the payload being empty; the premise is carried for
  -- interface compatibility with the emission site and the gate shape)
  subst hcs
  have hspec := terminalResult_spec hc hreach
  rw [ht] at hspec
  have hbs : bs = cfg.branch := RunAssembly.terminalResult_conflict_state_eq ht
  subst hbs
  intro a hleaf hcov
  exact hspec.coverage a hleaf (hreach.represents_of_frame hleaf hcov)

/-- **DEAD-SITE PRODUCER (local exclusion)**: if the terminal event of the
closure run at a REACHABLE branch state is `.localExcluded` (the selected
deduction's literal failed to narrow the frame), no leaf solution is
frame-covered. Derivation: the terminal spec's `coverage` for the
`.localExcluded` row excludes every represented leaf solution (assembled
there from the contract's branch-relative `literalSound` and the
empty-filter refutation); `ReachableState.represents_of_frame` supplies the
representation, and `terminalResult_localExcluded_state_eq` transfers the
carried state to the branch. -/
theorem deadLocalExcluded_of_terminalEvent {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    {lit : Option Literal} {reason : Option Clause} {learned : List Clause}
    (hc : ClosureContract leaf orig original props)
    (hreach : ReachableState leaf orig cfg.branch)
    (ht : terminalResult orig original props cfg.branch =
      .localExcluded bs lit reason learned) :
    ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False := by
  have hspec := terminalResult_spec hc hreach
  rw [ht] at hspec
  have hbs : bs = cfg.branch := terminalResult_localExcluded_state_eq ht
  subst hbs
  intro a hleaf hcov
  exact hspec.coverage a hleaf (hreach.represents_of_frame hleaf hcov)

/-- **DEAD-SITE PRODUCER (terminal conflict, ANY payload)**: the `cs = []`
premise of `deadConflictNil_of_terminalEvent` is NOT load-bearing — the
exclusion is the contract's `conflictExcludes` field and is uniform in the
payload. This is the shape the RECORDED-evidence sites need (the recording
site always carries `cs = c :: rest`), and it is what the E1 fallback
producers consume. -/
theorem frameDead_of_terminalConflict {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    {cs learned : List Clause}
    (hc : ClosureContract leaf orig original props)
    (hreach : ReachableState leaf orig cfg.branch)
    (ht : terminalResult orig original props cfg.branch = .conflict bs cs learned) :
    ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False := by
  have hspec := terminalResult_spec hc hreach
  rw [ht] at hspec
  have hbs : bs = cfg.branch := RunAssembly.terminalResult_conflict_state_eq ht
  subst hbs
  intro a hleaf hcov
  exact hspec.coverage a hleaf (hreach.represents_of_frame hleaf hcov)

end LeanFzn.Solver.UIP

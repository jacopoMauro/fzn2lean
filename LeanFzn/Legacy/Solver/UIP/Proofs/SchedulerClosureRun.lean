/-
File: LeanFzn/Solver/UIP/Proofs/SchedulerClosureRun.lean

Purpose: the `hclos` TRANSFER ENABLER. `ArmInvGatesCore.hclos`
(`Proofs/SchedulerArmGatesProduced.lean`) is the residual gate

    ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
      ClosureContract leaf cfg.orig cfg.original cfg.props

`ClosureContract` (`ExplainedPropagation.lean`, §"whole-run obligations")
is a STATIC property of the problem triple `(orig, original, props)`: it
has NO configuration input, only the problem parameters. Every real
successor preserves exactly that triple (`W1.schedulerNext_succ_inputs`,
`Proofs/SchedulerRun.lean` §1 — the Round-12 static-input frames), so ONE
problem-level contract transfers to every configuration of the run:

  * `closureContract_along_run` — from a problem-level contract
    `h0 : ClosureContract leaf orig original props`, EVERY reachable `cfg`
    whose triple agrees with `(orig, original, props)` satisfies its own
    `ClosureContract leaf cfg.orig cfg.original cfg.props`. Proof:
    structural induction on the reachability derivation; the root case is
    the definitional triple of `SchedulerConfig.init` (equality transport
    of `h0`), the step case transports the goal's equalities through
    `W1.schedulerNext_succ_inputs` and applies the induction hypothesis.
    Pure equality transport — no field reasoning, no extra premise, no
    change of statement.
  * `closureContract_init` — the root instance: a problem-level contract
    IS the init configuration's contract, up to the definitional
    projections of `SchedulerConfig.init` (cheap corollary of the transfer
    theorem; consumed by the problem-level providers, e.g.
    `domExplainedContract`).

WIRING FOLLOW-UP (coordinator, record restatement): restate the `hclos`
field (of `ArmInvGatesCore` and of the §6 `ArmInvGates` copy) on the run
triple, i.e.

    ∀ {orig original props cfg}, SchedulerReachable cfg →
      cfg.orig = orig → cfg.original = original → cfg.props = props →
        ClosureContract leaf orig original props

and assemble via `ArmInvGatesCore.toArmInvGates`; this module supplies the
cfg-indexed transfer the restated gate consumes. No consumer statement
changes: the arm sites that call `hg.hclos hreach` keep receiving the same
cfg-indexed contract through the restatement's internal
`closureContract_along_run` application (the current propagate/conflict
consumers already use the cfg-indexed form).

DAG edge: Proofs.SchedulerRun (W1 `schedulerNext_succ_inputs`) +
ExplainedPropagation (`ClosureContract`) -> this module. Registration owes
the umbrella line `import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerClosureRun` in
`LeanFzn.Solver/LeanFzn.Solver.UIP.lean` (coordinator).

NO sorry, NO custom axiom.
-/

import LeanFzn.Legacy.Solver.Propagation.ExplainedPropagation
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerRun
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 Static-input transfer of one problem-level contract -/

/-- **THE `hclos` TRANSFER.** `ClosureContract` is a STATIC property of
the problem triple `(orig, original, props)`, and every real scheduler
successor preserves that triple (`W1.schedulerNext_succ_inputs`).
Therefore ONE problem-level contract transfers to every reachable
configuration whose triple is that problem triple. Structural induction
on reachability; the step case is pure equality transport (no field
reasoning). -/
theorem closureContract_along_run {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    (h0 : ClosureContract leaf orig original props) :
    ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
      cfg.orig = orig → cfg.original = original → cfg.props = props →
        ClosureContract leaf cfg.orig cfg.original cfg.props := by
  intro cfg hreach
  induction hreach with
  | init o ori pr =>
      -- root: the `SchedulerConfig.init` triple is definitional, so the
      -- goal's projections are reached by transporting `h0` along the
      -- three equalities (rewriting the hypothesis keeps the shape used
      -- by the case goal untouched)
      intro ho horig hp
      rw [← ho, ← horig, ← hp] at h0
      exact h0
  | step hnext hsucc hr ih =>
      -- name the generalized index variables (`induction` hid them behind
      -- inaccessible names; the stale outer `cfg` is dropped first)
      clear cfg
      rename_i cfg cfg' tD
      intro ho horig hp
      -- ONE real dispatcher step preserves the static triple
      have hs : (schedulerNext cfg).successor = some cfg' := by
        rw [hnext]; exact hsucc
      obtain ⟨e1, e2, e3⟩ := W1.schedulerNext_succ_inputs hs
      -- transport the successor's goal back to the predecessor triple and
      -- apply the induction hypothesis
      rw [e1, e2, e3]
      exact ih (e1.symm.trans ho) (e2.symm.trans horig) (e3.symm.trans hp)

/-- The root instance: a problem-level contract IS the init
configuration's contract, up to the definitional projections of
`SchedulerConfig.init`. Corollary of `closureContract_along_run` at
`SchedulerReachable.init`; the follow-up consumer is the problem-level
provider (`domExplainedContract`). -/
theorem closureContract_init {prio : List Nat} {actBump : Bool} {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    (h0 : ClosureContract leaf orig original props)
    (hent : LearnedEntailed leaf original) :
    ClosureContract leaf
      (SchedulerConfig.init (leaf := leaf) orig original props prio actBump).orig
      (SchedulerConfig.init (leaf := leaf) orig original props prio actBump).original
      (SchedulerConfig.init (leaf := leaf) orig original props prio actBump).props :=
  closureContract_along_run h0
    (SchedulerReachable.init (leaf := leaf) orig original props hent) rfl rfl rfl

end LeanFzn.Solver.UIP

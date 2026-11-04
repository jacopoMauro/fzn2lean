/-
File: LeanFzn/Integration/Optimization/Primal.lean

Purpose (PLAN F6 phase 2, class W): witness-checked primal heuristics on top
of the certified branch-and-bound.  A dive slice is a deterministic,
fuel-bounded run of the F5 seeded kernel on the configured presentation; its
candidate is admitted only after `checkedObjective` accepts the emitted text.
The candidate can only tighten the initial bound of the certified B&B, so it
never supports an UNSAT/optimality claim by itself.

This module contains the F6.1 pure surface:

* the `PrimalHit` candidate and its class-W `Sound` predicate;
* `primalStepsPerMs`/`primalMsToFuel`, the nominal step budget;
* `diveSlice`, one deterministic root dive from the empty seed;
* `diveSlice_sound` (T9): every admitted hit is a checked candidate;
* `primalBound_optimal` (T4): a checked witness plus a completed bounded B&B
  with no solution proves the witness store optimal.

The optimality-transfer lemmas live next to their drivers: T1
`compileOpt_optimal_of_bound` in `Compiler/Proofs/Objective.lean` and T2
`optLoopWith_optimal` in `Integration/Optimize.lean`.  `lnsRound`/T10 and the
seeded B&B adapters are F6.2 work and are deliberately absent; the F6.1
driver accepts `--primal=dive` with `--opt=linear` only.

DAG: Optimize + LcgSeedBudget + LcgSeedConfig + CertifiedSolve +
Checker.Objective + Compiler.Proofs.Objective -> this file -> StrategyDriver.
NO `sorry`, NO custom axiom.
-/
import LeanFzn.Integration.Optimization.Basic
import LeanFzn.Legacy.Integration.Optimization.Chronological
import LeanFzn.Legacy.Integration.Optimization.KernelSeedBudget
import LeanFzn.Legacy.Integration.Optimization.KernelSeedConfig
import LeanFzn.Legacy.Integration.Solve.Certified
import LeanFzn.Compiler.Proofs.Objective
import LeanFzn.Checker.Objective

namespace LeanFzn.Integration
open LeanFzn.Semantics LeanFzn.Semantics.Globals LeanFzn.Semantics.Evaluation
open LeanFzn.Compiler LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP
open LeanFzn.Checker LeanFzn.Checker.Solution

/-! ## §1 Primal hits and their class-W soundness predicate -/

/-- One admitted primal candidate: the compiled assignment the slice found,
the checker-accepted emitted text, and the checked objective value. -/
structure PrimalHit where
  assignment : Assignment
  text : String
  value : Int

/-- Class-W soundness of one hit.  The emitted text is checked by the
certified checker (`checkedObjective`), and the checked value agrees with the
compiled assignment used by the driver. -/
def PrimalHit.Sound (m : Model) (p : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) (h : PrimalHit) : Prop :=
  h.assignment ∈ allAssigns p.domains ∧
  accepts p h.assignment = true ∧
  h.assignment[spec.slot]? = some (.int h.value) ∧
  checkedObjective m h.text = some h.value

/-- The integer objective value read from a compiled assignment, if the slot
holds an integer.  (`Value` has no `DecidableEq`, so the check is a match.) -/
def objSlot? (a : Assignment) (slot : Nat) : Option Int :=
  match a[slot]? with
  | some (.int v) => some v
  | _ => none

/-- A successful `objSlot?` read is exactly an integer at the slot. -/
theorem objSlot?_sound {a : Assignment} {slot : Nat} {v : Int}
    (h : objSlot? a slot = some v) : a[slot]? = some (.int v) := by
  unfold objSlot? at h
  split at h
  · rename_i w hw
    cases h
    simpa using hw
  all_goals cases h

/-! ## §2 The nominal step budget -/

/-- Calibration from F6.1: one nominal primal millisecond is this many
certified kernel steps.  It is a deterministic step budget, not a wall-clock
guarantee (same convention as `portfolioMsToFuel`).

The value is calibrated on the slow-step controls: the default 1000 nominal
milliseconds is a 1000-step slice.  On `fir_4_2` 1000 steps cost about 1.4 s
(annot B&B 6.0 s) and on `saeling/j0005` about 0.6 s (annot B&B 5.4 s), so the
slice plus the B&B stays under the 10 s campaign cap; 10 000 steps cost
16.4 s and 14.6 s respectively and would erase those proofs.  A 1000-step
slice already finds the FBDk04 and atp-stage2 candidates. -/
def primalStepsPerMs : Nat := 1

/-- `--primal-time=MS` as a deterministic fuel budget. -/
def primalMsToFuel (ms : Nat) : Nat := ms * primalStepsPerMs

/-! ## §3 The dive slice -/

/-- One deterministic dive from the root: the F5 budgeted seeded kernel on the
configured presentation, with the empty seed and no carry-out.  The result is
admitted only after the emitted text passes `checkedObjective` and the checked
value agrees with the assignment's objective slot. -/
def diveSlice (m : Model) (p : CompiledProblem DomConstraint)
    (o : SearchConfig) (spec : ObjectiveSpec) (fuel : Nat) : Option PrimalHit :=
  if hg : lcgRouteGateMixed (lcgConfigProblem p o) = true then
    match hrun : lcgSeedRunBudget (lcgConfigProblem p o)
        (SeedDb.nil (lcgConfigProblem p o).domains) hg
        (lcgConfigPrio o (lcgConfigProblem p o)) (lcgConfigActBump o) fuel with
    | .sat a =>
        match hcheck : checkedObjective m
            (emitCertifiedSolution m (p.toStore a)) with
        | some v =>
            if hv : objSlot? a spec.slot = some v then
              some ⟨a, emitCertifiedSolution m (p.toStore a), v⟩
            else none
        | none => none
    | .unsat => none
    | .exhausted => none
  else none

/-- **T9 (dive soundness)**: every admitted dive hit is a witness-checked
candidate of the source model. -/
theorem diveSlice_sound {m : Model} {p : CompiledProblem DomConstraint}
    {o : SearchConfig} {spec : ObjectiveSpec} {fuel : Nat} {hit : PrimalHit}
    (h : diveSlice m p o spec fuel = some hit) :
    PrimalHit.Sound m p spec hit := by
  unfold diveSlice at h
  split at h
  · rename_i hg
    split at h
    · rename_i a hrun
      split at h
      · rename_i v hcheck
        split at h
        · rename_i hv
          simp only [Option.some.injEq] at h
          subst h
          obtain ⟨hmem, hacc⟩ :=
            lcgSeedRunBudget_sat (lcgConfigProblem p o)
              (SeedDb.nil (lcgConfigProblem p o).domains) hg
              (lcgConfigPrio o (lcgConfigProblem p o)) (lcgConfigActBump o) hrun
          exact ⟨(mem_allAssigns_lcgConfigProblem p o a).mp hmem,
            by simpa [accepts_lcgConfigProblem] using hacc,
            objSlot?_sound hv, hcheck⟩
        · cases h
      · cases h
    · cases h
    · cases h
  · cases h

/-! ## §4 Optimality transfer for the bounded B&B -/

/-- **T4 (primal bound optimality)**: a checked primal witness `v` followed by
a completed bounded B&B with no solution proves the witness store optimal. -/
theorem primalBound_optimal {S : CertSolver} {m : Model}
    {p : CompiledProblem DomConstraint} {spec : ObjectiveSpec}
    (hc : compileModelOpt m = .ok (p, spec)) (hwf : WellFormed fullSig m)
    {text : String} {v : Int} (hcheck : checkedObjective m text = some v)
    {prev : Option (List Value)} {run : OptRun}
    (hrun : run = optLoopWith S p spec prev (some v))
    (hcomp : run.complete = true) (hnil : run.sols = []) :
    ∃ es, parseSolution (stripSeparators text) = .ok es ∧
      IsSolution fullSig fullInterp m (completedStore m es) := by
  obtain ⟨es, hparse, hsat, hpar, hobj⟩ := checkedObjective_sound hcheck
  rw [hrun] at hcomp hnil
  have hinv := optLoopWith_inv S p spec _ prev (some v) rfl
  have hlb := hinv.nil_bound hnil
  have hopt := hinv.optimal hcomp
  rw [hlb] at hopt
  refine ⟨es, hparse, ?_⟩
  exact compileOpt_optimal_of_bound hc hwf hsat hpar hobj (fun b hb => by
    simpa [curP] using hopt b hb)

end LeanFzn.Integration

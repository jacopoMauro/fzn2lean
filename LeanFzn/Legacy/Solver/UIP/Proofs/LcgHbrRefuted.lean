/-
File: LeanFzn/Solver/UIP/Proofs/LcgHbrRefuted.lean

H1 finding: the premise `hbr` (`ReachableState leaf orig cfg.branch` along `SupportedReach`) is FALSE
for the clamped LCG kit on non-unit instances.

`ReachableState.wf` carries the EXACT chronology conjunct of `BranchState.WellFormed`: every
non-pivot literal `l` of a trail reason has a trail entry `e'` with `e'.literal = l.negate`
earlier than the reasoned entry.  An LCG reason is only SEMANTICALLY falsified
(`SemReasonOK`: an earlier entry IMPLIES the negation, or the literal is false at the root), so
the exact conjunct fails.  Concrete instance (three variables in `0..10`,
`x + y ≤ 8`, `-x - y - z ≤ -15`): after propagate, propagate, decide `x = 0`, propagate the
trail holds `x1>4 @1 : [x1>4 | x0>0 | x2>10]`; the non-pivot `x0>0` is falsified only by the
decision `x0=0` (not literally `x0<=0`) and `x2>10` only at the root.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgAsserting
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP.LcgClamp
open LeanFzn.Solver.UIP.ClampPool LeanFzn.Solver.UIP

namespace LeanFzn.Solver.UIP.LcgHbrRefuted

variable {leaf : Assignment → Bool}

/-- Boolean detector of a violated exact-chronology conjunct. -/
def badChrono (tr : List TrailEntry) : Bool :=
  tr.any fun e =>
    match e.reason with
    | none => false
    | some r => r.clause.any fun l =>
        !(litEqB l e.literal) && !(tr.any fun e' => litEqB e'.literal l.negate)

theorem not_wf_of_badChrono {bs : BranchState leaf} (h : badChrono bs.trail = true) :
    ¬ bs.WellFormed := by
  intro hwf
  have h4 := hwf.2.2.2.1
  unfold badChrono at h
  obtain ⟨e, he, h⟩ := List.any_eq_true.mp h
  cases hr : e.reason with
  | none => rw [hr] at h; simp at h
  | some r =>
    rw [hr] at h
    obtain ⟨l, hl, h⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hne, hno⟩ := h
    have hne' : l ≠ e.literal := fun heq => by
      have := litEqB_iff.mpr heq; rw [this] at hne; cases hne
    obtain ⟨e', he', hlit, -⟩ := h4 e he r hr l hl hne'
    have : (bs.trail.any fun e' => litEqB e'.literal l.negate) = true :=
      List.any_eq_true.mpr ⟨e', he', litEqB_iff.mpr hlit⟩
    rw [this] at hno; cases hno

/-- Run `n` real dispatcher steps. -/
def runSched : Nat → SchedulerConfig leaf → Option (SchedulerConfig leaf)
  | 0, c => some c
  | n + 1, c => ((schedulerNext c).successor).bind (runSched n)

theorem supportedReach_runSched {orig : List Domain} {original : List Clause}
    {props : List Propagator} :
    ∀ (n : Nat) {c c' : SchedulerConfig leaf},
      SupportedReach orig original props c → runSched n c = some c' →
      SupportedReach orig original props c' := by
  intro n
  induction n with
  | zero => intro c c' h hr; simp [runSched] at hr; subst hr; exact h
  | succ n ih =>
      intro c c' h hr
      simp only [runSched] at hr
      cases hs : (schedulerNext c).successor with
      | none => rw [hs] at hr; simp at hr
      | some d =>
          rw [hs] at hr
          exact ih (SupportedReach.step h hs) hr

/-- The witness instance. -/
def dom : Domain := Dom.ofList ((List.range 11).map fun n => Value.int (Int.ofNat n))
def origW : List Domain := [dom, dom, dom]
def dcsW : List DomConstraint := [.linLe [1, 1] [0, 1] 8, .linLe [-1, -1, -1] [0, 1, 2] (-15)]
def propsW : List Propagator := clampProps origW (dcsW.filterMap propagatorOfProved)

theorem dcsW_fam : ∀ dc ∈ dcsW, lcgFamB dc = true := by
  intro dc h
  simp only [dcsW, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> rfl

/-- The witness leaf (any leaf works; the trail of the first four steps does not read it). -/
def leafW : Assignment → Bool := fun _ => false

theorem witness_badChrono :
    ((runSched 4 (SchedulerConfig.init (leaf := leafW) origW [] propsW)).map
      fun c => badChrono c.branch.trail) = some true := by
  decide +kernel

/-- **`hbr` is refuted for the clamped LCG kit** on the witness instance, for every leaf. -/
theorem hbr_refuted :
    ¬ (∀ {cfg : SchedulerConfig leafW}, SupportedReach origW [] propsW cfg →
        ReachableState leafW origW cfg.branch) := by
  intro hbr
  cases hr : runSched 4 (SchedulerConfig.init (leaf := leafW) origW [] propsW) with
  | none => have := witness_badChrono; rw [hr] at this; simp at this
  | some c =>
    have hreach : SupportedReach origW [] propsW c :=
      supportedReach_runSched 4 (SupportedReach.init (fun c hc => by cases hc)) hr
    have := witness_badChrono
    rw [hr] at this
    simp only [Option.map_some, Option.some.injEq] at this
    exact not_wf_of_badChrono this (hbr hreach).wf

end LeanFzn.Solver.UIP.LcgHbrRefuted


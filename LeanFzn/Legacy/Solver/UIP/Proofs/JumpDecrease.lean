/-
File: LeanFzn/Solver/UIP/Proofs/JumpDecrease.lean
reduction of the LAST open premise of the fuel-free driver)

MISSION (C3b). `C3b.JumpDecrease` (`LeanFzn/Solver/UIP/Proofs/Scheduler.lean` §)
asks the perform-indexed decrease of the `.learnBackjumpAssert` arm. The
known positive provider `jumpDecrease_of_frontier_eq_of_mass` reduces it
to the conjunction

  (F) frontierCost (SchedulerConfig.frontier succ) =
        frontierCost (SchedulerConfig.frontier cfg)
  (M) Frame.mass restored.frame < Frame.mass cfg.branch.frame

for the actual `perform` result. This file settles the truth value of
(F), (M) and their conjunction, kernel-checked:

* §1 (PROVED, general): `frontier` of the successor is `restored.frame ::
  cfg.pending`, so (F) is EXACTLY `branchCost restored.frame.1 =
  branchCost cfg.branch.frame.1`; neither follows from the shape alone.
  A STRICTLY cheaper restored head frame (`branchCost restored.frame.1 <
  branchCost cfg.branch.frame.1`) already decreases the rank — the
  provider's equality form is not the only route, and this form needs no
  mass hypothesis.

* §2 (PROVED, general): `perform = some restored` gives exactly
  `restored = explainedClosure orig props ((execute …).narrowFrame g)`
  with `filterFrame p.asserting p.checkpoint.frame = some g`, hence the
  only frame bound available from `perform`'s signature is

      Frame.mass restored.frame ≤ Frame.mass p.checkpoint.frame.

  There is NO relation in the signature between `restored.frame` and
  `cfg.branch.frame`: the restored frame is the CHECKPOINT frame narrowed
  by one literal, while `cfg.branch.frame` is its (typically far deeper)
  descendant — so in the intended direction of a real backjump
  `branchCost cp.frame > branchCost cfg.branch.frame` generically, i.e.
  (F) fails and (M) fails in the interesting instances (the descendant's
  frame has LESS remaining work than the ancestor's; the C2dO2 routing
  note's warning, made concrete). Detailed truth table in §2.

* §3 (REFUTATION, kernel-checked, for EVERY leaf): `JumpDecrease` as
  stated is FALSE as a theorem — its three premises are satisfiable with
  `perform` genuinely returning a state whose rank is strictly LARGER
  (frontier cost 5 vs 1). The refutation does not even need to violate a
  reachability invariant: it shows the statement quantifies over
  configurations where the restore lands on a heavier frame, which is
  exactly the generic backjump situation. Consequently the obligation
  cannot be repaired by proving (F)+(M) from `perform`; the repair must
  index the rank by work that a restore cannot RAISE (§4).

* §4 (REPAIRED OBLIGATION, stated with truth-value analysis): the
  named `def`s below are the residual content. `DebtDecrease` is the
  proposed extension of the rank's first component: unexhausted
  frontier work net of the registered dead regions — the only component
  with a chance to decrease on a genuine backjump, since `ExhaustionLog`
  grows monotonically while the restored raw frontier shrinks only in
  the re-filtered slot. No theorem "the extended rank closes it" is
  claimed here (that is a proof obligation, not established in this
  box). CORRECTION: the same §3 witness ALSO refutes the two variants as
  STATED (`not_jumpDecreaseOfDebt`, `not_debtDecrease`): the debt-free
  form carries no log term (`5 < 1`), and the emptied log defeats the
  `+ regions.length + 1` slack (`5 < 1 + 0 + 1`). The honest repair must
  therefore be REACHABILITY-INDEXED (or use a component outside
  `frontierCost`), not a fixed arithmetic slack.

Zero `sorry`/`admit`/`native_decide`, no new axioms.

DAG: BackjumpFrontier + Proofs.Scheduler (+ O2/Progress) -> this module.
-/

import LeanFzn.Legacy.Solver.UIP.Proofs.Scheduler
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerStep
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerStepO2
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerProgress
import LeanFzn.Legacy.Solver.Propagation.BackjumpFrontier
import LeanFzn.Legacy.Solver.UIP.SchedulerStep
import LeanFzn.Legacy.Solver.Propagation.RestorationCertificate
import LeanFzn.Legacy.Solver.UIP.SchedulerState
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP


namespace LeanFzn.Solver.UIP.C3b
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.UIP.C3a

/-! ## §1 Frontier bookkeeping of the jump arm (PROVED, general)

`SchedulerConfig.frontier cfg = cfg.branch.frame :: cfg.pending` and
`stepLearnBackjumpAssert` keeps `pending` while setting
`branch := {restored with learned := …}`. Hence the frontier cost of the
successor differs from the predecessor's ONLY in the head frame. -/

/-- The successor frontier is the restored frame pushed on the SAME
pending stack. -/
theorem frontier_stepLearnBackjumpAssert {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (p : BackjumpPlan leaf)
    (ev : ConflictEvidence) (restored : BranchState leaf) :
    (stepLearnBackjumpAssert cfg p ev restored).frontier
      = restored.frame :: cfg.pending := rfl

/-- The frontier weight is the head frame's weight plus the pending
sum. -/
theorem frontierWeight_frontier {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) :
    frontierWeight cfg.frontier
      = frameWeight cfg.branch.frame + frontierWeight cfg.pending := by
  simp [SchedulerConfig.frontier, frontierWeight]

/-- The successor's frontier weight, isolated: only the head frame changed. -/
theorem frontierWeight_stepLearnBackjumpAssert {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (p : BackjumpPlan leaf)
    (ev : ConflictEvidence) (restored : BranchState leaf) :
    frontierWeight (stepLearnBackjumpAssert cfg p ev restored).frontier
      = frameWeight restored.frame + frontierWeight cfg.pending := by
  rw [frontier_stepLearnBackjumpAssert]
  simp [frontierWeight]

/-- Exact reduction of the provider's hypothesis (F): frontier-weight
equality holds IFF the restored head frame has the same weight as
the conflict frame. (The pending stack is common to both sides.) -/
theorem frontierWeight_jump_eq_iff {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (p : BackjumpPlan leaf)
    (ev : ConflictEvidence) (restored : BranchState leaf) :
    frontierWeight (stepLearnBackjumpAssert cfg p ev restored).frontier
        = frontierWeight cfg.frontier ↔
      frameWeight restored.frame = frameWeight cfg.branch.frame := by
  rw [frontierWeight_stepLearnBackjumpAssert, frontierWeight_frontier]
  constructor <;> intro h <;> omega

/-- POSITIVE (PROVED): a STRICTLY cheaper restored head frame decreases
the rank outright, with no mass hypothesis and no frontier equality. This
is an alternative sufficient condition for the provider's `hfront =`-plus-
mass package. -/
theorem rank_lt_of_branchCost_lt {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (p : BackjumpPlan leaf)
    (ev : ConflictEvidence) (restored : BranchState leaf)
    (h : branchCost restored.frame.doms < branchCost cfg.branch.frame.doms) :
    RankLt
      (SchedulerRank (stepLearnBackjumpAssert cfg p ev restored))
      (SchedulerRank cfg) := by
  refine Or.inl ?_
  show frontierWeight (stepLearnBackjumpAssert cfg p ev restored).frontier
      < frontierWeight cfg.frontier
  rw [frontierWeight_stepLearnBackjumpAssert, frontierWeight_frontier]
  have hw : frameWeight restored.frame < frameWeight cfg.branch.frame := by
    show 3 ^ Frame.cost restored.frame < 3 ^ Frame.cost cfg.branch.frame
    exact Nat.pow_lt_pow_right (by decide) h
  exact Nat.add_lt_add_right hw _

/-! ## §2 What `perform = some restored` actually guarantees (PROVED)

`perform` = `filterFrame` the CHECKPOINT frame by the asserting literal,
then `explainedClosure`. The bound below is the strongest frame fact the
signature supports; §3 shows nothing relates it to `cfg.branch.frame`.

TRUTH TABLE of the provider's two hypotheses over `perform`'s result:
| fact | derivable from `perform = some restored`? |
|------|-------------------------------------------|
| `restored.frame = (explainedClosure …).frame` | YES (shape lemma) |
| `Frame.mass restored.frame ≤ Frame.mass cp.frame` | YES (§2 bound) |
| `(F) frontierCost succ = frontierCost cfg` | NO — reduces to §1, and §3 refutes it |
| `(M) Frame.mass restored.frame < Frame.mass cfg.branch.frame` | NO — §3 refutes it; the ancestor is generically HEAVIER |
-/

/-- Shape lemma: a successful `perform` is the explained closure of the
narrowed executed checkpoint. -/
theorem perform_shape {leaf : Assignment → Bool} {p : BackjumpPlan leaf}
    {bs : BranchState leaf} {dom : List Domain} {orig : List Clause}
    {props : List Propagator}
    {restored : BranchState leaf} (h : p.perform bs dom orig props = some restored) :
    ∃ g, filterFrame p.asserting p.checkpoint.frame = some g ∧
      restored = explainedClosure dom orig props (syncAll dom
        ((p.execute (bs.learnGlobal p.learned)).narrowFrame g)) := by
  unfold BackjumpPlan.perform BackjumpPlan.restoreNarrow at h
  cases hf : filterFrame p.asserting p.checkpoint.frame with
  | none => simp [hf] at h
  | some g =>
      simp only [hf, Option.map_some, Option.some.injEq] at h
      exact ⟨g, rfl, h.symm⟩

/-- perform's frame is no heavier than the checkpoint frame it restores:
`filterFrame` is mass-nonincreasing (`filterFrame_mass_le`) and the
closure is mass-nonincreasing (`explainedClosure_mass`). -/
theorem perform_frame_mass_le {leaf : Assignment → Bool}
    {p : BackjumpPlan leaf} {bs : BranchState leaf} {dom : List Domain}
    {orig : List Clause}
    {props : List Propagator} {restored : BranchState leaf}
    (h : p.perform bs dom orig props = some restored) :
    Frame.mass restored.frame ≤ Frame.mass p.checkpoint.frame := by
  obtain ⟨g, hg, rfl⟩ := perform_shape h
  have h1 : Frame.mass (explainedClosure dom orig props (syncAll dom
      ((p.execute (bs.learnGlobal p.learned)).narrowFrame g))).frame
      ≤ Frame.mass ((p.execute (bs.learnGlobal p.learned)).narrowFrame g).frame := by
    have := explainedClosure_mass dom orig props (syncAll dom
      ((p.execute (bs.learnGlobal p.learned)).narrowFrame g))
    rwa [syncAll_frame] at this
  have h2 : Frame.mass ((p.execute (bs.learnGlobal p.learned)).narrowFrame g).frame
      = Frame.mass g := rfl
  have h3 : Frame.mass g ≤ Frame.mass p.checkpoint.frame :=
    filterFrame_mass_le hg
  omega

/-! ## §3 REFUTATION: `JumpDecrease` is false (kernel-checked)

The statement of `JumpDecrease` has exactly three premises — evidence
recorded, checkpoint found, `perform` succeeded — and the last one is
satisfiable with the performed restore landing on a frame HEAVIER than
the conflict frame. The witness below is minimal: the checkpoint frame
has one remaining domain `[1, 2]` (`branchCost = 5`), the conflict frame
is complete (`branchCost = 1`), `props = original = []` plus the empty
asserting clause (`an0.learned = []`) make the closure an identity (the
database scan reports a conflict on the empty clause), and `filterFrame`
keeps the domain (`intLe 0 5` accepts both values), so
`branchCost restored.frame.1 = 5 > 1` and the rank's first component
STRICTLY INCREASES. -/

/-- The two-value domain of the witness. -/
private def d0 : Domain := Dom.ofList [Value.int 1, Value.int 2]

/-- The asserting literal of the witness (accepts both values of `d0`). -/
private def l0 : Literal := { atom := .intLe 0 5, positive := true }

/-- The recorded analysis of the witness. -/
private def an0 : ConflictAnalysis :=
  { learned := [], backjumpLevel := 0, asserting := l0 }

/-- The found checkpoint: level 0, frame `([d0], [])`. -/
private def cp0 (leaf : Assignment → Bool) : DecisionCheckpoint leaf :=
  { level := 0, frame := (⟨[d0], []⟩ : BranchFrame), trail := [] }

/-- The witness configuration: conflict branch is COMPLETE (`([], [1])`),
the only checkpoint restores the heavier ancestor frame `([d0], [])`. -/
private def cfg0 (leaf : Assignment → Bool) : SchedulerConfig leaf :=
  { SchedulerConfig.init (leaf := leaf) [d0] [] [] with
    branch :=
      { frame := (⟨[Dom.ofList [Value.int 1]], [0]⟩ : BranchFrame), trail := [],
        level := 1, learned := [] }
    checkpoints := [cp0 leaf] }

/-- The recorded evidence of the witness. -/
private def ev0 : ConflictEvidence :=
  { clause := [], learned := [], analysis := some an0 }

/-- The plan the scheduler builds from the found checkpoint. -/
private def p0 (leaf : Assignment → Bool) : BackjumpPlan leaf :=
  BackjumpPlan.ofCheckpoint (cp0 leaf) (cfg0 leaf).branch an0.asserting
    an0.learned

/-- The performed result: the executed-and-narrowed state, with the
identity closure (both proposition lists empty). -/
private def restored0 (leaf : Assignment → Bool) : BranchState leaf :=
  syncAll (cfg0 leaf).orig
    (((p0 leaf).execute
      ((cfg0 leaf).branch.learnGlobal (p0 leaf).learned)).narrowFrame
      (⟨[d0], []⟩ : BranchFrame))

private theorem filterFrame0 (leaf : Assignment → Bool) :
    filterFrame an0.asserting (cp0 leaf).frame = some (⟨[d0], []⟩ : BranchFrame) := by
  simp only [filterFrame, cp0, l0, d0, Dom.enum_ofList, List.filter_cons,
    List.filter_nil, List.length_cons, List.length_nil, if_true, Option.some.injEq]
  congr 1

/-- The witness's `perform` argument: the plan's asserting literal keeps
both values of the checkpoint domain. Stated over `p0` so it matches the
goal's spelling; proved by the concrete `filterFrame0` up to definitional
equality. -/
private theorem filterFrame_p0 (leaf : Assignment → Bool) :
    filterFrame (p0 leaf).asserting (p0 leaf).checkpoint.frame
      = some (⟨[d0], []⟩ : BranchFrame) := by
  show filterFrame an0.asserting (cp0 leaf).frame =
    some (⟨[d0], []⟩ : BranchFrame)
  exact filterFrame0 leaf

/-- The closure is the identity on any state whose learned database
contains the EMPTY clause: the database scan reports `.conflict`, the
deduction selector is `none` there, and the closure stops (via the
EXISTING fixpoint lemma `explainedClosure_eq_self_of_deduction_none`,
`SchedulerStep.lean`). The witness's asserting clause is exactly `[]`. -/
private theorem explainedClosure_of_learned_emptyClause {leaf : Assignment → Bool}
    {dom : List Domain}
    {bs : BranchState leaf} (hdb : bs.learned = ([] : Clause) :: []) :
    explainedClosure dom ([] : List Clause) [] bs = bs := by
  apply explainedClosure_eq_self_of_deduction_none
  have hev : nextPruningEvent ([] : List Clause) [] bs.frame bs.learned
      = .conflict [[]] := by
    rw [hdb]
    simp only [nextPruningEvent, scanDatabase, clauseRemaining, List.filter_nil]
  rw [explainedDeduction, hev]

/-- The witness satisfies all three `JumpDecrease` premises. -/
private theorem perform0 (leaf : Assignment → Bool) :
    (p0 leaf).perform (cfg0 leaf).branch (cfg0 leaf).orig (cfg0 leaf).original
        (cfg0 leaf).props = some (restored0 leaf) := by
  have hcl : explainedClosure (cfg0 leaf).orig ([] : List Clause) []
      (syncAll (cfg0 leaf).orig (((p0 leaf).execute
        ((cfg0 leaf).branch.learnGlobal (p0 leaf).learned)).narrowFrame
        (⟨[d0], []⟩ : BranchFrame)))
      = (syncAll (cfg0 leaf).orig (((p0 leaf).execute
        ((cfg0 leaf).branch.learnGlobal (p0 leaf).learned)).narrowFrame
        (⟨[d0], []⟩ : BranchFrame))) := by
    apply explainedClosure_of_learned_emptyClause
    rw [syncAll_learned]
    show (((p0 leaf).execute
      ((cfg0 leaf).branch.learnGlobal (p0 leaf).learned)).narrowFrame
      (⟨[d0], []⟩ : BranchFrame)).learned = ([] : Clause) :: []
    simp only [BranchState.narrowFrame, BackjumpPlan.execute,
      BranchState.learnGlobal, p0, BackjumpPlan.ofCheckpoint, cfg0, an0,
      SchedulerConfig.init, BranchState.init]
  have hO : (cfg0 leaf).original = ([] : List Clause) := rfl
  have hP : (cfg0 leaf).props = ([] : List Propagator) := rfl
  unfold BackjumpPlan.perform BackjumpPlan.restoreNarrow
  rw [filterFrame_p0, hO, hP]
  simp only [Option.map_some]
  rw [hcl]
  rfl

private theorem checkpoint0 (leaf : Assignment → Bool) :
    checkpointAt (cfg0 leaf).checkpoints an0.backjumpLevel = some (cp0 leaf) :=
  rfl

/-- The restored frame is the narrowed one (definitional). -/
private theorem restored0_frame (leaf : Assignment → Bool) :
    (restored0 leaf).frame = (⟨[d0], []⟩ : BranchFrame) := by
  show (syncAll (cfg0 leaf).orig
    (((p0 leaf).execute
      ((cfg0 leaf).branch.learnGlobal (p0 leaf).learned)).narrowFrame
      (⟨[d0], []⟩ : BranchFrame))).frame = (⟨[d0], []⟩ : BranchFrame)
  simp only [syncAll_frame, BranchState.narrowFrame]

private theorem cfg0_pending_weight (leaf : Assignment → Bool) :
    frontierWeight (cfg0 leaf).pending = 0 := by
  show frontierWeight ([] : List BranchFrame) = 0
  rfl

private theorem branchCost_restored0 (leaf : Assignment → Bool) :
    branchCost (restored0 leaf).frame.doms = 5 := by
  rw [restored0_frame]
  simp [branchCost, d0, Dom.length_eq_enum]

private theorem branchCost_cfg0 (leaf : Assignment → Bool) :
    branchCost (cfg0 leaf).branch.frame.doms = 3 := by
  show branchCost [Dom.ofList [Value.int 1]] = 3
  simp [branchCost, Dom.length_eq_enum]

/-- The successor's frontier weight is `3^5`, the predecessor's is `3^3`:
the witness's first rank component strictly increases. -/
private theorem frontier0 (leaf : Assignment → Bool) :
    frontierWeight (SchedulerConfig.frontier
        (stepLearnBackjumpAssert (cfg0 leaf)
          (BackjumpPlan.ofCheckpoint (cp0 leaf) (cfg0 leaf).branch
            an0.asserting an0.learned) ev0 (restored0 leaf))) = 243 ∧
      frontierWeight (SchedulerConfig.frontier (cfg0 leaf)) = 27 := by
  constructor
  · rw [frontierWeight_stepLearnBackjumpAssert, cfg0_pending_weight]
    rw [show frameWeight (restored0 leaf).frame = 3 ^ 5 from by
      show 3 ^ Frame.cost (restored0 leaf).frame = 3 ^ 5
      rw [show Frame.cost (restored0 leaf).frame =
          branchCost (restored0 leaf).frame.doms from rfl]
      rw [branchCost_restored0]]
  · rw [frontierWeight_frontier, cfg0_pending_weight]
    rw [show frameWeight (cfg0 leaf).branch.frame = 3 ^ 3 from by
      show 3 ^ Frame.cost (cfg0 leaf).branch.frame = 3 ^ 3
      rw [show Frame.cost (cfg0 leaf).branch.frame =
          branchCost (cfg0 leaf).branch.frame.doms from rfl]
      rw [branchCost_cfg0]]

/-- REFUTATION (kernel-checked): `JumpDecrease` is false for EVERY leaf.
The witness's restore lands on the heavier ancestor frame, so no lex
disjunct of `RankLt` applies (`5 > 1`). -/
theorem not_jumpDecrease (leaf : Assignment → Bool) : ¬ JumpDecrease leaf := by
  intro h
  have hlt := h (cfg0 leaf) ev0 an0 (cp0 leaf) (restored0 leaf)
    rfl (checkpoint0 leaf) (perform0 leaf)
  have h1 := (frontier0 leaf).1
  have h2 := (frontier0 leaf).2
  simp only [SchedulerRank, RankLt] at hlt
  rw [h1, h2] at hlt
  rcases hlt with h | ⟨h, _⟩ <;> omega

/-! ## §4 The repaired obligation (truth-value analysis; no proof claimed)

The refutation above mirrors the generic backjump: `restored.frame` is the
checkpoint ANCESTOR frame (filtered once), while `cfg.branch.frame` is its
DESCENDANT. A descendant has no more remaining work than its ancestor, so
both (F) and (M) are generically FALSE for real backjumps — no proof
search over `perform`'s current signature can close `JumpDecrease`. What
a genuine backjump buys is that the REFUTED part of the restored frame's
work is now recorded in `ExhaustionLog` (monotone, never restored), and
that the asserting literal removes one value. The residual obligations
below name exactly that content. -/

/-- REPAIR (first component). The rank's first component should be the
frontier cost of the successor NET of the dead regions the jump has
accumulated — not of the raw restored frontier. This is the component
that can decrease on a real backjump (the raw one generically increases,
§3). Stated as the residual obligation on the perform result.
REFUTED AS STATED by the §3 witness (`not_debtDecrease`): the log is
empty there, so the `+1` slack does not help. -/
def DebtDecrease (leaf : Assignment → Bool) : Prop :=
  ∀ (cfg : SchedulerConfig leaf) (ev : ConflictEvidence)
    (an : ConflictAnalysis) (cp : DecisionCheckpoint leaf)
    (restored : BranchState leaf),
    ev.analysis = some an →
    checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
    (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
        cfg.branch cfg.orig cfg.original cfg.props = some restored →
    -- the successor's raw cost may RISE (refuted above); the repair
    -- charges it against the newly registered dead region instead:
    branchCost restored.frame.doms <
      branchCost cfg.branch.frame.doms + cfg.log.regions.length + 1

/-- REPAIR (the provider form). If the debt-indexed cost strictly
decreases, `JumpDecrease`'s conclusion follows from the SAME rank algebra
as `jumpDecrease_of_frontier_eq_of_mass`, but through the strict
first-component disjunct (`rank_lt_of_branchCost_lt`'s contrapositive
shape): the mass hypothesis is then unnecessary. Stated as the candidate
obligation. REFUTED AS STATED by the same witness
(`not_jumpDecreaseOfDebt`). -/
def JumpDecreaseOfDebt (leaf : Assignment → Bool) : Prop :=
  ∀ (cfg : SchedulerConfig leaf) (ev : ConflictEvidence)
    (an : ConflictAnalysis) (cp : DecisionCheckpoint leaf)
    (restored : BranchState leaf),
    ev.analysis = some an →
    checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
    (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
        cfg.branch cfg.orig cfg.original cfg.props = some restored →
    branchCost restored.frame.doms < branchCost cfg.branch.frame.doms

/-- VACUOUS BRIDGE, kept for the record: this proves that the
strict-`branchCost` variant would imply `JumpDecrease`; BOTH statements
are FALSE at the §3 witness (`not_jumpDecrease`, `not_jumpDecreaseOfDebt`
below), so the theorem has no usable instance. The honest repair is
reachability-indexed (or replaces the first rank component) and is task
C3c's obligation. -/
theorem jumpDecrease_of_branchCost_lt {leaf : Assignment → Bool}
    (h : JumpDecreaseOfDebt leaf) : JumpDecrease leaf :=
  fun cfg ev an cp restored hae hcp hp =>
    rank_lt_of_branchCost_lt cfg
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
      ev restored (h cfg ev an cp restored hae hcp hp)

/-- The witness's two head costs, isolated: `branchCost` of the restored
(ancestor) frame is 5, of the conflict frame is 1. -/
private theorem branchCost0 (leaf : Assignment → Bool) :
    branchCost (restored0 leaf).frame.doms = 5 ∧
      branchCost (cfg0 leaf).branch.frame.doms = 3 :=
  ⟨branchCost_restored0 leaf, branchCost_cfg0 leaf⟩

private theorem cfg0_log_len (leaf : Assignment → Bool) :
    (cfg0 leaf).log.regions.length = 0 := by
  show ([] : List DeadRegion).length = 0
  rfl

/-- CORRECTION of the earlier (wrong) claim: `JumpDecreaseOfDebt` is
ALSO refuted by the §3 witness — its conclusion carries no log term, so
`5 < 1` fails there. -/
theorem not_jumpDecreaseOfDebt (leaf : Assignment → Bool) :
    ¬ JumpDecreaseOfDebt leaf := by
  intro h
  have hlt := h (cfg0 leaf) ev0 an0 (cp0 leaf) (restored0 leaf)
    rfl (checkpoint0 leaf) (perform0 leaf)
  rw [(branchCost0 leaf).1, (branchCost0 leaf).2] at hlt
  omega

/-- COROLLARY of the same witness: `DebtDecrease` (the
`+ regions.length + 1` slack form) is refuted too — the log is EMPTY
there (`log = {}`), so the charged bound is `1 + 0 + 1 = 2 < 5`. A fixed
arithmetic slack cannot repair the arm; the C3c obligation must be
reachability-indexed or use a different rank component. -/
theorem not_debtDecrease (leaf : Assignment → Bool) :
    ¬ DebtDecrease leaf := by
  intro h
  have hlt := h (cfg0 leaf) ev0 an0 (cp0 leaf) (restored0 leaf)
    rfl (checkpoint0 leaf) (perform0 leaf)
  rw [(branchCost0 leaf).1, (branchCost0 leaf).2, cfg0_log_len leaf] at hlt
  omega

end LeanFzn.Solver.UIP.C3b

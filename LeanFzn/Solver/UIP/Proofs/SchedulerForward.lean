/-
File: LeanFzn/Solver/UIP/Proofs/SchedulerForward.lean

Purpose:
  FORWARD PROGRESS of the scheduler of `LeanFzn/Solver/UIP/SchedulerStep.lean`:
  invariant and coverage preservation for the NON-CONFLICT transitions
  (`init`, productive `propagate`, `decide`/split), the SAT-witness
  containment, the new checkpoint identity of a split, the sibling
  provenance of a deduced literal, and the counterexample showing where
  the decision policy MUST refuse a redundant pin.

  Field map (INTERFACES §9.1, C2a-owned fields):
  * `reachable`             — `stepPropagate_reachable` (via E1's
                              `explainedDeduction_narrow_reachable`),
                              `stepDecide_reachable[_of_second_value]`
                              (via A1's `reachable_decide[_of_second_value]`).
  * `checkpoints_identify`  — `stepPropagate_checkpoints_identify`,
                              `stepDecide_checkpoints_identify` (the newest
                              checkpoint of a split identifies the pinned
                              child at the fresh level).
  * `pending_fits`          — `stepPropagate_pending_fits` (unchanged),
                              `stepDecide_pending_fits` (the sibling is a
                              sub-box: `vs ⊆ v :: vs`, the rest identical).
  * `branch_fits`           — `stepPropagate_branch_fits` (pointwise subset
                              from `filterFrame`), `stepDecide_branch_fits`
                              (A1's `fullDomains_decide_subset`).
  * `coverage`              — `stepPropagate_covers` (the deduction literal
                              is sound at every REPRESENTED leaf solution,
                              so `filterFrame` keeps it; the database only
                              grows) and `stepDecide_covers` (A0/C1's
                              `covers_split`: the parent frame is replaced
                              by its two children — no leaf solution is
                              lost, so this is a genuine preservation, not
                              a stability weakening).
  * `log_sound`             — CARRIED THROUGH UNCHANGED (`propagate` and
                              `decide` never touch the log). Stated
                              explicitly in `stepPropagate_invariant` /
                              `stepDecide_invariant`.
  * `learned_entailed`      — CARRIED THROUGH for `decide`; for `propagate`
                              the new payload `d.learned` is entailed by
                              E1's `explainedDeduction_learned_entailed`
                              (the reason clause is globally entailed by
                              `ClosureContract.reasonEntailed`), the old
                              clauses are untouched. Also stated explicitly.

  SUPPORTING INVARIANT (runtime note): `CheckpointsBelow` — every saved
  checkpoint's level is at most the current branch level. `Identifies`
  alone does not bound `cp.level` above when the checkpoint's trail
  already equals the branch trail (the saved suffix is then empty), so
  the identity of PRE-EXISTING checkpoints under a trail append needs it.
  It is closed under the runtime operations: `checkpointsBelow_init`
  (root, level 0), `checkpointsBelow_decide` (the new checkpoint sits at
  the new level), `checkpointsBelow_propagate` (level and list
  unchanged), and it is preserved by C2c's checkpoint filter
  (`stepLearnBackjumpAssert` only RETIRES checkpoints and restores to
  `p.target ≤` the source level). The integration owner should keep it
  in `SchedulerConfig.WellFormed`.

  SAT WITNESS: `leafWitness_solution` — the witness reported by the leaf
  check is an original solution (`SolutionWitness`/`OriginalLeaves`), from
  `leafWitness_eq_some_iff` (complete frame + passing leaf) and the
  reachable state's `full_fits`.

  FINDING (defect evidence, decision policy): `stableStep`/`splitData`
  accept a SINGLETON head domain (`v :: []`), and `stepDecide` then pins
  `v` at a fresh level. When the pin's normalized literal is ALREADY
  recorded on the trail (the exact shape `explainedDeduction` skips as a
  redundant deduction), the decision duplicates the entry and destroys
  `TrailLiteralsDistinct` — `stepDecide_redundant_not_distinct`, an
  instance of A1's `decide_duplicates`. The absence check
  (`TrailRedundant cfg.branch.trail l = false`, the same gate
  `explainedDeduction` uses) is therefore a NECESSARY runtime guard for
  the decision, and the theorems below take it as the premise.

Dependencies:
  - LeanFzn.Solver.UIP.SchedulerStep: `stepPropagate`, `stepDecide`, `splitData`,
    `splitData_eq_some_iff`, `leafWitness`, `leafWitness_eq_some_iff`,
    `stableStep`.
  - LeanFzn.Solver.UIP.Proofs.SchedulerInvariant (S0): `SchedulerInvariant`,
    `RootInvariant`, `schedulerInvariant_init`.
  - LeanFzn.Solver.UIP.Proofs.LearnedExplanation (E1): `ClauseProvenance`,
    `clauseProvenance_of_contract`, `learnedProvenance_narrow_of_members`;
    `explainedDeduction_learned_entailed` from `ExplainedPropagation`.

DAG:
  SchedulerStep + Proofs.SchedulerInvariant + Proofs.LearnedExplanation
    -> Proofs.SchedulerForward (this module; consumed by C2c/C2d and the
    coordinator's registration). No runtime module imports it.
-/

import LeanFzn.Solver.UIP.SchedulerStep
import LeanFzn.Solver.UIP.Proofs.SchedulerInvariant
import LeanFzn.Solver.UIP.Proofs.LearnedExplanation
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 Auxiliary invariants and transfer lemmas -/

/-- `branch_fits` is the frame-level reading of branch coherence: A1's
`ReachableState.full_fits` already forbids invented values. -/
theorem _root_.LeanFzn.Solver.Propagation.ReachableState.branch_fits {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf}
    (h : ReachableState leaf orig bs) :
    ∀ i v, v ∈ (Frame.domains bs.frame).getD i [] → v ∈ orig.getD i [] :=
  fun i v hv => h.full_fits i v hv

/-- A frame-covered leaf solution is REPRESENTED: the trail agrees with
the frame (`ReachableState.agrees`) and the database is globally entailed
(`WellFormed`'s last conjunct). This is what makes the branch-relative
`ClosureContract.literalSound` applicable at an arbitrary frontier
member instead of only at call sites that already carry `Represents`. -/
theorem _root_.LeanFzn.Solver.Propagation.ReachableState.represents_of_frame {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf}
    (h : ReachableState leaf orig bs) {a : Assignment}
    (hleaf : leaf a = true) (hcov : FrameCovers bs.frame a) :
    bs.Represents a :=
  ⟨hcov, fun e he => h.agrees e he a hcov,
    fun c hc => h.wf.2.2.2.2 c hc a hleaf⟩

/-- The checkpoint-level discipline: no saved checkpoint sits above the
current branch level. See the module header for why `Identifies` alone
does not supply it and why the runtime maintains it. -/
def CheckpointsBelow {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) : Prop :=
  ∀ cp ∈ cfg.checkpoints, cp.level ≤ cfg.branch.level

/-- The root configuration satisfies the checkpoint-level discipline. -/
theorem checkpointsBelow_init (leaf : Assignment → Bool)
    (orig : List Domain) (original : List Clause) (props : List Propagator) :
    CheckpointsBelow (SchedulerConfig.init (leaf := leaf) orig original props) := by
  intro cp hcp
  simp only [SchedulerConfig.init, List.mem_singleton] at hcp
  subst hcp
  exact Nat.le_refl 0

/-- `propagate` keeps the checkpoint-level discipline (level and list are
unchanged). -/
theorem checkpointsBelow_propagate {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {d : ProductiveDeduction leaf cfg.branch}
    (h : CheckpointsBelow cfg) : CheckpointsBelow (stepPropagate cfg d) := by
  intro cp hcp
  exact h cp (by simpa [stepPropagate] using hcp)

/-- `decide` keeps the checkpoint-level discipline: the pushed checkpoint
is the PARENT snapshot (level = parent level, REPAIRED by the integration
fix), and the old ones move down by one. -/
theorem checkpointsBelow_decide {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {v : Value} {vs : Domain}
    {doms : List Domain} {l : Literal} (h : CheckpointsBelow cfg) :
    CheckpointsBelow (stepDecide cfg v vs doms l) := by
  intro cp hcp
  rcases List.mem_cons.mp hcp with rfl | hcp
  · show cfg.branch.level ≤ cfg.branch.level + 1
    exact Nat.le_succ _
  · exact Nat.le_succ_of_le (h cp hcp)

/-- `decideSkip` keeps the checkpoint-level discipline (branch level and
checkpoint list are unchanged). -/
theorem checkpointsBelow_decideSkip {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {v : Value} {doms : List Domain}
    (h : CheckpointsBelow cfg) :
    CheckpointsBelow (stepDecideSkip cfg v doms) := by
  simpa only [stepDecideSkip, CheckpointsBelow] using h

/-- The consume runtime EMPTIES the checkpoint list (R2 repair: the
canonical resume's frame-derived trail does not extend stale snapshots).
This is the sublist half of the push bundle at the consume arm. -/
theorem stepConsume_checkpoints_sublist {leaf : Assignment → Bool}
    {cfg next : SchedulerConfig leaf} {f : BranchFrame}
    {rest : List BranchFrame}
    (hp : cfg.pending = f :: rest) (h : stepConsume cfg = some next) :
    List.Sublist next.checkpoints cfg.checkpoints := by
  unfold stepConsume at h
  rw [hp] at h
  simp only [Option.some.injEq] at h
  subst h
  exact List.nil_sublist _

/-- `analyzeConflict` keeps the checkpoint-level discipline (branch and
checkpoint list are unchanged). -/
theorem checkpointsBelow_analyzeConflict {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {c : Clause} {learned : List Clause}
    (h : CheckpointsBelow cfg) :
    CheckpointsBelow (stepAnalyzeConflict cfg c learned) := by
  simpa only [stepAnalyzeConflict, CheckpointsBelow] using h

/-- The counted analyze site keeps the checkpoint-level discipline
(`countResolutions` touches only `events`/`conflict`). -/
theorem checkpointsBelow_analyzeConflictCounted {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {c : Clause} {learned : List Clause}
    {n : Nat} (h : CheckpointsBelow cfg) :
    CheckpointsBelow (stepAnalyzeConflictCounted cfg c learned n) := by
  simpa only [stepAnalyzeConflictCounted, SchedulerConfig.countResolutions,
    CheckpointsBelow] using checkpointsBelow_analyzeConflict h

/-- `localExclude` keeps the checkpoint-level discipline (registration
only touches log/status/conflict). -/
theorem checkpointsBelow_localExclude {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {learned : List Clause} {r : DeadRegion}
    (h : CheckpointsBelow cfg) :
    CheckpointsBelow (stepLocalExclude cfg learned r) := by
  simpa only [stepLocalExclude, CheckpointsBelow] using h

/-- `chronologicalFallback` keeps the checkpoint-level discipline (no
trail/level movement). -/
theorem checkpointsBelow_chronologicalFallback {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {r : DeadRegion}
    (h : CheckpointsBelow cfg) :
    CheckpointsBelow (stepChronologicalFallback cfg r) := by
  simpa only [stepChronologicalFallback, CheckpointsBelow] using h

/-- **R2 REPAIR CLOSURE**: `consume` EMPTIES the checkpoint list, so the
checkpoint-level discipline holds at the successor vacuously (no premise
on the predecessor). Motivation: the canonical resume's frame-derived
trail does not extend stale checkpoint trails, so retaining any survivor
would falsify the identity condition (`Identifies`) the jump restores by. -/
theorem checkpointsBelow_consume {leaf : Assignment → Bool}
    {cfg next : SchedulerConfig leaf} {f : BranchFrame}
    {rest : List BranchFrame}
    (hp : cfg.pending = f :: rest) (h : stepConsume cfg = some next) :
    CheckpointsBelow next := by
  unfold stepConsume at h
  rw [hp] at h
  simp only [Option.some.injEq] at h
  subst h
  intro cp' hmem
  cases hmem

/-! ## §2 Initialization (re-export of S0's non-vacuous witness) -/

/-- C2a's `init` case: the real root configuration satisfies the
invariant (`schedulerInvariant_init`, S0) — a re-export so the C2d
assembly cites a single name per transition. -/
theorem schedulerForward_init (leaf : Assignment → Bool)
    (orig : List Domain) (original : List Clause) (props : List Propagator) :
    RootInvariant leaf orig original props :=
  schedulerInvariant_init leaf orig original props

/-- The root also satisfies the checkpoint-level discipline. -/
theorem schedulerForward_init_checkpointsBelow (leaf : Assignment → Bool)
    (orig : List Domain) (original : List Clause) (props : List Propagator) :
    CheckpointsBelow (SchedulerConfig.init (leaf := leaf) orig original props) :=
  checkpointsBelow_init leaf orig original props

/-! ## §3 Productive propagation -/

/-- COHERENCE at the real dispatch site: the deduction the driver selected
keeps the reachable invariant, with every obligation derived from the
closure contract (E1's `explainedDeduction_narrow_reachable`). -/
theorem stepPropagate_reachable {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf}
    (hc : ClosureContract leaf cfg.orig cfg.original cfg.props)
    (hinv : SchedulerInvariant cfg)
    (hu : UnitDB cfg.branch.learned)
    {d : ProductiveDeduction leaf cfg.branch}
    (hd : explainedDeduction cfg.original cfg.props cfg.branch = some d) :
    ReachableState leaf cfg.orig (stepPropagate cfg d).branch :=
  explainedDeduction_narrow_reachable hc hinv.reachable hu hd

/-- `propagate` never touches the pending frontier. -/
theorem stepPropagate_pending_fits {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} (hinv : SchedulerInvariant cfg)
    (d : ProductiveDeduction leaf cfg.branch) :
    ∀ f ∈ (stepPropagate cfg d).pending, ∀ i v,
      v ∈ (Frame.domains f).getD i [] → v ∈ cfg.orig.getD i [] := by
  intro f hf i v hv
  exact hinv.pending_fits f (by simpa [stepPropagate] using hf) i v hv

/-- `propagate` keeps the current frame inside the original box (the
narrowed frame is a pointwise subset of the old one). -/
theorem stepPropagate_branch_fits {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} (hinv : SchedulerInvariant cfg)
    (d : ProductiveDeduction leaf cfg.branch) :
    ∀ i v, v ∈ (Frame.domains (stepPropagate cfg d).branch.frame).getD i [] →
      v ∈ cfg.orig.getD i [] :=
  fun i v hv => hinv.branch_fits i v (Frame.domains_subsets d.filtered i v hv)

/-- PRE-EXISTING CHECKPOINT IDENTITY under propagation: the trail append
stays at the checkpoint-identifying shape (all later entries at or above
the checkpoint's level) and the narrowed frame still descends from the
checkpoint's frame. -/
theorem stepPropagate_checkpoints_identify {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} (hinv : SchedulerInvariant cfg)
    (hlevel : CheckpointsBelow cfg) (d : ProductiveDeduction leaf cfg.branch) :
    ∀ cp ∈ (stepPropagate cfg d).checkpoints,
      cp.Identifies (stepPropagate cfg d).branch cp.level := by
  intro cp hcp
  have hmem : cp ∈ cfg.checkpoints := by simpa [stepPropagate] using hcp
  obtain ⟨hlev, ⟨mid, htrail, hmid⟩, hdesc⟩ := hinv.checkpoints_identify cp hmem
  have hle : cp.level ≤ cfg.branch.level := hlevel cp hmem
  refine ⟨hlev, ⟨mid ++ [(⟨d.literal.norm, cfg.branch.level,
      some { clause := d.reason }⟩ : TrailEntry)], ?_, ?_⟩, ?_⟩
  · simp only [stepPropagate, narrowState]
    rw [htrail, List.append_assoc]
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact hmid e he
    · simp only [List.mem_singleton] at he
      rw [he]
      show cp.level ≤ cfg.branch.level
      exact hle
  · intro a ha
    exact hdesc a (filterFrame_refines d.filtered ha)

/-- FIELD-ONLY VARIANT of `stepPropagate_checkpoints_identify` (J1 hident
wrapper): the supported identifies+chain induction carries only the
`checkpoints_identify` conjunct, never the whole `SchedulerInvariant`. -/
theorem stepPropagate_checkpoints_identify_of_identifies {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf}
    (hident : ∀ cp ∈ cfg.checkpoints, cp.Identifies cfg.branch cp.level)
    (hlevel : CheckpointsBelow cfg) (d : ProductiveDeduction leaf cfg.branch) :
    ∀ cp ∈ (stepPropagate cfg d).checkpoints,
      cp.Identifies (stepPropagate cfg d).branch cp.level := by
  intro cp hcp
  have hmem : cp ∈ cfg.checkpoints := by simpa [stepPropagate] using hcp
  obtain ⟨hlev, ⟨mid, htrail, hmid⟩, hdesc⟩ := hident cp hmem
  have hle : cp.level ≤ cfg.branch.level := hlevel cp hmem
  refine ⟨hlev, ⟨mid ++ [(⟨d.literal.norm, cfg.branch.level,
      some { clause := d.reason }⟩ : TrailEntry)], ?_, ?_⟩, ?_⟩
  · simp only [stepPropagate, narrowState]
    rw [htrail, List.append_assoc]
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact hmid e he
    · simp only [List.mem_singleton] at he
      rw [he]
      show cp.level ≤ cfg.branch.level
      exact hle
  · intro a ha
    exact hdesc a (filterFrame_refines d.filtered ha)

/-- COVERAGE under propagation: no leaf solution is lost. Every remaining
leaf solution is represented, hence satisfies the deduced literal (the
branch-relative `ClosureContract.literalSound`), hence survives the
`filterFrame` narrowing; the database only grows and the pending stack is
untouched. -/
theorem stepPropagate_covers {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf}
    (hc : ClosureContract leaf cfg.orig cfg.original cfg.props)
    (hinv : SchedulerInvariant cfg)
    {d : ProductiveDeduction leaf cfg.branch}
    (hd : explainedDeduction cfg.original cfg.props cfg.branch = some d) :
    (stepPropagate cfg d).coverage := by
  intro a hleaf
  rcases hinv.coverage a hleaf with ⟨f, hf, hcov⟩ | hdb
  · rcases List.mem_cons.mp hf with rfl | hf
    · left
      have hleafl : leaf a = true := hleaf.1
      have hrep := hinv.reachable.represents_of_frame hleafl hcov
      obtain ⟨lr, fl, hev⟩ := explainedDeduction_event hd
      have hlit := hc.literalSound cfg.branch hinv.reachable d.literal d.reason
        lr fl hev a hleafl hrep
      have hlit' : d.literal.eval a = some true := by
        rwa [Literal.norm_eval] at hlit
      obtain ⟨g, hg, hcov'⟩ := filterFrame_preserves hcov hlit'
      have hg' : g = d.frame := Option.some.inj (hg.symm.trans d.filtered)
      subst hg'
      exact ⟨d.frame, List.mem_cons_self .., hcov'⟩
    · left
      exact ⟨f, List.mem_cons_of_mem _ hf, hcov⟩
  · right
    rcases hdb with ⟨c, hc', hnc⟩
    exact ⟨c, List.mem_append.mpr (Or.inr hc'), hnc⟩

/-- SIBLING PROVENANCE of the learned payload (E1's discipline): the
clause the deduction records carries `ClauseProvenance` from the contract
at the selected event — the pivot is the normalized deduced literal, the
falsifiers are the trail. The narrowed state has the same trail as the
`recordImplied` site E1's constructor is stated for. -/
theorem stepPropagate_clauseProvenance {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf}
    (hc : ClosureContract leaf cfg.orig cfg.original cfg.props)
    (hinv : SchedulerInvariant cfg)
    (hu : UnitDB cfg.branch.learned)
    {d : ProductiveDeduction leaf cfg.branch}
    (hd : explainedDeduction cfg.original cfg.props cfg.branch = some d) :
    ClauseProvenance leaf (stepPropagate cfg d).branch d.reason := by
  obtain ⟨lr, fl, hev⟩ := explainedDeduction_event hd
  exact clauseProvenance_of_contract hc hinv.reachable hu hev

/-- The learned payload of `explainedDeduction` is exactly the reason
clause (or nothing): the purity fact `learnedProvenance_narrow_of_members`
consumes. A complement to E1's `explainedDeduction_learned_entailed`. -/
theorem explainedDeduction_learned_members {leaf : Assignment → Bool}
    {original : List Clause} {props : List Propagator}
    {bs : BranchState leaf} {d : ProductiveDeduction leaf bs}
    (h : explainedDeduction original props bs = some d) :
    ∀ c' ∈ d.learned, c' = d.reason := by
  cases hev : nextPruningEvent original props bs.frame bs.learned with
  | stable => simp only [explainedDeduction, hev] at h; cases h
  | conflict cs => simp only [explainedDeduction, hev] at h; cases h
  | implied l c lr fl =>
      simp only [explainedDeduction, hev] at h
      by_cases ht : TrailRedundant bs.trail l = true
      · simp only [ht] at h; cases h
      · have hred : TrailRedundant bs.trail l = false := by
          cases hb : TrailRedundant bs.trail l
          · rfl
          · exact absurd hb ht
        simp only [hred] at h
        split at h
        · simp at h
        · rename_i g hf
          split at h
          · rename_i hm
            have hd := Option.some.inj h
            have hc : d.reason = c := by rw [← hd]
            have hle : d.learned =
                (if lr && !(bs.learned.contains c) then [c] else []) := by
              rw [← hd]
            intro c' hc'
            rw [hle] at hc'
            split at hc'
            · rw [List.mem_singleton] at hc'
              rw [hc', hc]
            · simp at hc'
          · simp at h

/-- The learned database of the propagation successor carries E1's
invariant, given it held before (the old clauses keep their provenance,
the new one is `stepPropagate_clauseProvenance`). -/
theorem stepPropagate_learnedProvenance {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf}
    (hc : ClosureContract leaf cfg.orig cfg.original cfg.props)
    (hinv : SchedulerInvariant cfg)
    (hu : UnitDB cfg.branch.learned)
    (hprov : LearnedProvenance leaf cfg.branch)
    {d : ProductiveDeduction leaf cfg.branch}
    (hd : explainedDeduction cfg.original cfg.props cfg.branch = some d) :
    LearnedProvenance leaf (stepPropagate cfg d).branch := by
  obtain ⟨lr, fl, hev⟩ := explainedDeduction_event hd
  have hpivot := hc.pivot cfg.branch hinv.reachable hu d.literal d.reason lr fl hev
  have hchron := hc.chronology cfg.branch hinv.reachable hu d.literal d.reason
    lr fl hev
  have hmem := explainedDeduction_learned_members hd
  have h : LearnedProvenance leaf
      (narrowState cfg.branch d.frame d.literal d.reason d.learned) :=
    learnedProvenance_narrow_of_members (g := d.frame) hprov hpivot hchron
      (fun c' hc' => hmem c' hc')
  exact h

/-- INVARIANT PRESERVATION for `propagate`, field by field. `log_sound`
and `learned_entailed` are carried through (`propagate` never touches the
log; the learned payload is entailed by the contract's reason clause). -/
theorem stepPropagate_invariant {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf}
    (hc : ClosureContract leaf cfg.orig cfg.original cfg.props)
    (hinv : SchedulerInvariant cfg) (hlevel : CheckpointsBelow cfg)
    (hu : UnitDB cfg.branch.learned)
    {d : ProductiveDeduction leaf cfg.branch}
    (hd : explainedDeduction cfg.original cfg.props cfg.branch = some d) :
    SchedulerInvariant (stepPropagate cfg d) := by
  obtain ⟨lr, fl, hev⟩ := explainedDeduction_event hd
  have hentReason := hc.reasonEntailed cfg.branch hinv.reachable d.literal d.reason
    lr fl hev
  have hentLearned := explainedDeduction_learned_entailed hd hentReason
  refine ⟨stepPropagate_reachable hc hinv hu hd,
    stepPropagate_checkpoints_identify hinv hlevel d,
    stepPropagate_pending_fits hinv d,
    stepPropagate_branch_fits hinv d,
    ?_, stepPropagate_covers hc hinv hd, ?_⟩
  · -- log_sound: untouched
    exact hinv.log_sound
  · -- learned_entailed: new clauses entailed, old ones untouched
    intro c hcmem
    rcases List.mem_append.mp hcmem with hcmem | hcmem
    · refine fun c' hc' => ?_
      rw [List.mem_singleton] at hc'
      rw [hc']
      exact hentLearned c hcmem
    · exact hinv.learned_entailed c hcmem

/-! ## §4 Decision / split -/

/-- The split data determines the parent frame shape (C1's
`splitData_eq_some_iff`), so the parent is exactly the `covers_split`
shape. -/
theorem splitData_parent {f : BranchFrame} {l : Literal} {v : Value}
    {vs : Domain} {doms : List Domain}
    (h : splitData f = some (l, v, vs, doms)) :
    f = (((v :: vs) :: doms), f.2) :=
  Prod.ext (splitData_eq_some_iff.mp h).1 rfl

/-- A frame with an EMPTY head domain has no split data: the dispatcher
cannot decide an exhausted slot (`splitData` returns `none`). -/
theorem splitData_none_of_empty_head {f : BranchFrame} {rest : List Domain}
    (h : f.1 = [] :: rest) : splitData f = none := by
  obtain ⟨slots, chosen⟩ := f
  simp only at h
  rw [h]
  rfl

/-- `stableStep` reports exactly the split the transition function
consumes: the bridge C2d needs to match the dispatcher's `Literal`. -/
theorem stableStep_decide {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain}
    {doms : List Domain} (hw : leafWitness leaf cfg = none)
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms)) :
    stableStep cfg = .decide (stepDecide cfg v vs doms l) l := by
  simp only [stableStep, hw, hsplit]

/-- COHERENCE under a decision: A1's `reachable_decide`, with the
freshness premise supplied by the runtime's absence check
(`TrailRedundant ... = false`, the same gate `explainedDeduction` uses —
see `stepDecide_redundant_not_distinct` for why it is necessary). -/
theorem stepDecide_reachable {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain}
    {doms : List Domain} (hinv : SchedulerInvariant cfg)
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms))
    (hpin : ∀ a : Assignment, a.Fits cfg.orig →
      (l.norm.eval a = some true ↔
        a[cfg.branch.frame.2.length]? = some v))
    (hred : TrailRedundant cfg.branch.trail l = false) :
    ReachableState leaf cfg.orig (stepDecide cfg v vs doms l).branch := by
  have hdom := (splitData_eq_some_iff.mp hsplit).1
  exact reachable_decide hinv.reachable hdom (List.mem_cons_self ..) hpin
    (not_trailRedundant_iff.mp hred)

/-- COHERENCE for a GENUINE branch: a second value in the head domain plus
a completable tail makes the pin unforced, so the decision needs no
runtime absence check (A1's `reachable_decide_of_second_value`; the
forced/redundant case is exactly the counterexample below). -/
theorem stepDecide_reachable_of_second_value {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain}
    {doms : List Domain} (hinv : SchedulerInvariant cfg)
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms))
    (hpin : ∀ a, l.norm.eval a = some true ↔
      a[cfg.branch.frame.2.length]? = some v)
    (hsecond : ∃ w' ∈ (v :: vs), w' ≠ v)
    (htail : ∃ tail, tail ∈ allAssigns doms) :
    ReachableState leaf cfg.orig (stepDecide cfg v vs doms l).branch := by
  have hdom := (splitData_eq_some_iff.mp hsplit).1
  exact reachable_decide_of_second_value hinv.reachable hdom
    (List.mem_cons_self ..) hsecond hpin htail

/-- The BOOLEAN specialization: `splitData`'s pin literal is
`valueLiteral`'s, and `valueLiteral_holds_iff` derives the pin semantics,
so `stepDecide_reachable`'s premises reduce to the runtime absence check.
The INT-valued case pins via the integer view (`slotInt`); its bridge is
`IntViewedDomain`'s (ExplainedPropagation §"root-fact soundness") — see
the C2a resume note for the named gap. -/
theorem stepDecide_bool_reachable {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {b : Bool} {vs : Domain}
    {doms : List Domain} (hinv : SchedulerInvariant cfg)
    (hsplit : splitData cfg.branch.frame = some (l, .bool b, vs, doms))
    (hred : TrailRedundant cfg.branch.trail l = false) :
    ReachableState leaf cfg.orig (stepDecide cfg (.bool b) vs doms l).branch := by
  have hwl := (splitData_eq_some_iff.mp hsplit).2
  refine stepDecide_reachable hinv hsplit ?_ hred
  intro a _
  rw [Literal.norm_eval]
  simpa using valueLiteral_holds_iff hwl a

/-- THE SINGLETON CASE (`vs = []`, an already-forced head value): the
decision is coherent exactly when the absence check passes — the
specialization of `stepDecide_reachable` the "already-forced decision"
acceptance condition asks for. -/
theorem stepDecide_singleton_reachable {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value}
    {doms : List Domain} (hinv : SchedulerInvariant cfg)
    (hsplit : splitData cfg.branch.frame = some (l, v, [], doms))
    (hpin : ∀ a : Assignment, a.Fits cfg.orig →
      (l.norm.eval a = some true ↔
        a[cfg.branch.frame.2.length]? = some v))
    (hred : TrailRedundant cfg.branch.trail l = false) :
    ReachableState leaf cfg.orig (stepDecide cfg v [] doms l).branch :=
  stepDecide_reachable hinv hsplit hpin hred

/-- FINDING — the redundant pin DESTROYS the duplicate-safe discipline: if
the decision's normalized literal is already recorded at another level,
`stepDecide` duplicates the trail entry (A1's `decide_duplicates`). The
runtime must therefore refuse a decided pin that fails
`TrailRedundant ... = false`; `splitData` accepts singleton head domains,
so this guard is a genuine runtime obligation, not a hypothetical. -/
theorem stepDecide_redundant_not_distinct {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain}
    {doms : List Domain}
    (hmem : ∃ e ∈ cfg.branch.trail, e.literal = l.norm ∧
      e.level ≠ cfg.branch.level + 1) :
    ¬ TrailLiteralsDistinct (stepDecide cfg v vs doms l).branch.trail :=
  TrailLiteralsDistinct.decide_duplicates hmem

/-- The sibling alternative stays inside the original box: `vs` is a
sub-domain of the parent head `v :: vs` and the remaining slots are
literally the parent's. -/
theorem stepDecide_pending_fits {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain}
    {doms : List Domain} (hinv : SchedulerInvariant cfg)
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms)) :
    ∀ f ∈ (stepDecide cfg v vs doms l).pending, ∀ i w,
      w ∈ (Frame.domains f).getD i [] → w ∈ cfg.orig.getD i [] := by
  have hdom := (splitData_eq_some_iff.mp hsplit).1
  have hfe : cfg.branch.frame = (((v :: vs) :: doms), cfg.branch.frame.2) :=
    Prod.ext hdom rfl
  -- the sibling `(vs :: doms, pre)`: its remaining domains are the
  -- parent's, shifted by the pinned head (`vs ⊆ v :: vs`)
  have htail : ∀ i w, w ∈ (vs :: doms).getD i [] →
      w ∈ ((v :: vs) :: doms).getD i [] := by
    intro i w hw
    cases i with
    | zero => exact List.mem_cons_of_mem v (by simpa using hw)
    | succ j => simpa using hw
  have hsib : ∀ i w, w ∈ (Frame.domains ((vs :: doms), cfg.branch.frame.2)).getD i [] →
      w ∈ (Frame.domains (((v :: vs) :: doms), cfg.branch.frame.2)).getD i [] := by
    intro i w hw
    simp only [Frame.domains] at hw ⊢
    exact getD_append_subset htail i w hw
  intro f hf i w hw
  rcases List.mem_cons.mp hf with rfl | hf
  · refine hinv.branch_fits i w ?_
    rw [hfe]
    exact hsib i w hw
  · exact hinv.pending_fits f hf i w hw

/-- The pinned child stays inside the original box (A1's
`fullDomains_decide_subset`). -/
theorem stepDecide_branch_fits {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain}
    {doms : List Domain} (hinv : SchedulerInvariant cfg)
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms)) :
    ∀ i w, w ∈ (Frame.domains (stepDecide cfg v vs doms l).branch.frame).getD i [] →
      w ∈ cfg.orig.getD i [] := by
  have hdom := (splitData_eq_some_iff.mp hsplit).1
  have hfe : cfg.branch.frame = (((v :: vs) :: doms), cfg.branch.frame.2) :=
    Prod.ext hdom rfl
  have hw : v ∈ (v :: vs : Domain) := List.mem_cons_self ..
  intro i w hw'
  refine hinv.branch_fits i w ?_
  rw [hfe]
  exact fullDomains_decide_subset hw i w
    (by simpa only [fullDomains, stepDecide_frame] using hw')

/-- COVERAGE under a split: the parent frame is REPLACED by its two
children (`covers_split`), so no leaf solution leaves the frontier; the
pending stack and the database are untouched. This is a genuine
preservation: neither child drops a covered solution. -/
theorem stepDecide_covers {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain}
    {doms : List Domain} (hinv : SchedulerInvariant cfg)
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms)) :
    (stepDecide cfg v vs doms l).coverage := by
  have hdom := (splitData_eq_some_iff.mp hsplit).1
  intro a hleaf
  rcases hinv.coverage a hleaf with ⟨f, hf, hcov⟩ | hdb
  · rcases List.mem_cons.mp hf with rfl | hf
    · left
      have hsplitcov := (covers_split v vs doms cfg.branch.frame.2 a).mp (by
        rw [show cfg.branch.frame = (((v :: vs) :: doms), cfg.branch.frame.2)
          from Prod.ext hdom rfl] at hcov
        exact hcov)
      rcases hsplitcov with hchild | hsib
      · exact ⟨(doms, cfg.branch.frame.2 ++ [v]),
          List.mem_cons_self .., hchild⟩
      · exact ⟨(vs :: doms, cfg.branch.frame.2),
          List.mem_cons_of_mem _ (List.mem_cons_self ..), hsib⟩
    · left
      exact ⟨f, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hf), hcov⟩
  · right
    exact hdb

/-- CHECKPOINT IDENTITY of a split: the newest checkpoint (the pre-pinning
parent frame at the fresh level) identifies the pinned child, and the
older checkpoints still identify it. -/
theorem stepDecide_checkpoints_identify {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain}
    {doms : List Domain} (hinv : SchedulerInvariant cfg)
    (hlevel : CheckpointsBelow cfg)
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms)) :
    ∀ cp ∈ (stepDecide cfg v vs doms l).checkpoints,
      cp.Identifies (stepDecide cfg v vs doms l).branch cp.level := by
  have hdom := (splitData_eq_some_iff.mp hsplit).1
  have hchild : FrameDescendsFrom (doms, cfg.branch.frame.2 ++ [v])
      cfg.branch.frame := by
    rw [show cfg.branch.frame = (((v :: vs) :: doms), cfg.branch.frame.2)
      from Prod.ext hdom rfl]
    exact fun a ha => FrameCovers_decide (List.mem_cons_self ..) ha
  intro cp hcp
  rcases List.mem_cons.mp hcp with rfl | hcp
  · -- the new checkpoint: the parent snapshot, at the parent level; the
    -- child trail extends it by exactly the decision entry (at or above
    -- the parent level)
    refine ⟨rfl, ⟨[(⟨l.norm, cfg.branch.level + 1, none⟩ : TrailEntry)],
      ?_, ?_⟩, hchild⟩
    · simp only [stepDecide, BranchState.decide, DecisionCheckpoint.ofBranch]
    · intro e he
      simp only [List.mem_singleton] at he
      subst he
      show cfg.branch.level ≤ cfg.branch.level + 1
      exact Nat.le_succ _
  · -- the old checkpoints: append the decision entry at the new level
    obtain ⟨hlev, ⟨mid, htrail, hmid⟩, hdesc⟩ := hinv.checkpoints_identify cp hcp
    have hle : cp.level ≤ cfg.branch.level := hlevel cp hcp
    refine ⟨hlev, ⟨mid ++ [(⟨l.norm, cfg.branch.level + 1, none⟩ : TrailEntry)],
      ?_, ?_⟩, ?_⟩
    · simp only [stepDecide, BranchState.decide]
      rw [htrail, List.append_assoc]
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact hmid e he
      · simp only [List.mem_singleton] at he
        rw [he]
        show cp.level ≤ cfg.branch.level + 1
        exact Nat.le_succ_of_le hle
    · intro a ha
      exact hdesc a (hchild a ha)

/-- FIELD-ONLY VARIANT of `stepDecide_checkpoints_identify` (J1 hident
wrapper): the supported identifies+chain induction carries only the
`checkpoints_identify` conjunct. -/
theorem stepDecide_checkpoints_identify_of_identifies {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain}
    {doms : List Domain}
    (hident : ∀ cp ∈ cfg.checkpoints, cp.Identifies cfg.branch cp.level)
    (hlevel : CheckpointsBelow cfg)
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms)) :
    ∀ cp ∈ (stepDecide cfg v vs doms l).checkpoints,
      cp.Identifies (stepDecide cfg v vs doms l).branch cp.level := by
  have hdom := (splitData_eq_some_iff.mp hsplit).1
  have hchild : FrameDescendsFrom (doms, cfg.branch.frame.2 ++ [v])
      cfg.branch.frame := by
    rw [show cfg.branch.frame = (((v :: vs) :: doms), cfg.branch.frame.2)
      from Prod.ext hdom rfl]
    exact fun a ha => FrameCovers_decide (List.mem_cons_self ..) ha
  intro cp hcp
  rcases List.mem_cons.mp hcp with rfl | hcp
  · -- the new checkpoint: the parent snapshot, at the parent level; the
    -- child trail extends it by exactly the decision entry (at or above
    -- the parent level)
    refine ⟨rfl, ⟨[(⟨l.norm, cfg.branch.level + 1, none⟩ : TrailEntry)],
      ?_, ?_⟩, hchild⟩
    · simp only [stepDecide, BranchState.decide, DecisionCheckpoint.ofBranch]
    · intro e he
      simp only [List.mem_singleton] at he
      subst he
      show cfg.branch.level ≤ cfg.branch.level + 1
      exact Nat.le_succ _
  · -- the old checkpoints: append the decision entry at the new level
    obtain ⟨hlev, ⟨mid, htrail, hmid⟩, hdesc⟩ := hident cp hcp
    have hle : cp.level ≤ cfg.branch.level := hlevel cp hcp
    refine ⟨hlev, ⟨mid ++ [(⟨l.norm, cfg.branch.level + 1, none⟩ : TrailEntry)],
      ?_, ?_⟩, ?_⟩
    · simp only [stepDecide, BranchState.decide]
      rw [htrail, List.append_assoc]
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact hmid e he
      · simp only [List.mem_singleton] at he
        rw [he]
        show cp.level ≤ cfg.branch.level + 1
        exact Nat.le_succ_of_le hle
    · intro a ha
      exact hdesc a (hchild a ha)

/-- INVARIANT PRESERVATION for `decide`, field by field. `log_sound` and
`learned_entailed` are carried through unchanged (`decide` touches
neither the log nor the learned database). -/
theorem stepDecide_invariant {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain}
    {doms : List Domain} (hinv : SchedulerInvariant cfg)
    (hlevel : CheckpointsBelow cfg)
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms))
    (hpin : ∀ a : Assignment, a.Fits cfg.orig →
      (l.norm.eval a = some true ↔
        a[cfg.branch.frame.2.length]? = some v))
    (hred : TrailRedundant cfg.branch.trail l = false) :
    SchedulerInvariant (stepDecide cfg v vs doms l) :=
  ⟨stepDecide_reachable hinv hsplit hpin hred,
    stepDecide_checkpoints_identify hinv hlevel hsplit,
    stepDecide_pending_fits hinv hsplit,
    stepDecide_branch_fits hinv hsplit,
    hinv.log_sound,
    stepDecide_covers hinv hsplit,
    hinv.learned_entailed⟩

/-! ## §5 The SAT witness of the leaf check -/

/-- SAT WITNESS CONTAINMENT (C2a deliverable): the witness reported by
`leafWitness` is an original leaf solution — the frame is complete, so
`full_fits` bounds every value of the assignment by the original domains
and `length_ok` matches the box length. -/
theorem leafWitness_solution {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {w : Assignment}
    (hreach : ReachableState leaf cfg.orig cfg.branch)
    (h : leafWitness leaf cfg = some w) :
    SolutionWitness leaf cfg.orig w := by
  obtain ⟨hframe, hleaf, rfl⟩ := leafWitness_eq_some_iff.mp h
  have hfe : cfg.branch.frame = ((([] : List Domain), cfg.branch.frame.2)) :=
    Prod.ext hframe rfl
  refine ⟨hleaf, ?_, ?_⟩
  · have hlen : (fullDomains ((([] : List Domain),
        cfg.branch.frame.2) : BranchFrame)).length = cfg.orig.length :=
      hfe ▸ hreach.length_ok
    simpa [fullDomains, Frame.domains] using hlen
  · intro slot value hget
    have hmem : value ∈ (fullDomains ((([] : List Domain),
        cfg.branch.frame.2) : BranchFrame)).getD slot [] := by
      have h1 : fullDomains ((([] : List Domain),
          cfg.branch.frame.2) : BranchFrame)
          = List.map (fun v => [v]) cfg.branch.frame.2 := by
        simp [fullDomains, Frame.domains]
      rw [h1, List.getD_eq_getElem?_getD, List.getElem?_map, hget]
      exact List.mem_singleton_self value
    rw [← hfe] at hmem
    exact hreach.full_fits slot value hmem

/-- The dispatcher-level SAT witness: when the stable dispatcher reports
`.sat w`, `w` fits the original box (C2d's `sat` arm consumes this). -/
theorem stableStep_sat_solution {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {w : Assignment}
    (hreach : ReachableState leaf cfg.orig cfg.branch)
    (h : stableStep cfg = .sat w) :
    SolutionWitness leaf cfg.orig w := by
  unfold stableStep at h
  split at h
  · rename_i w' hw'
    cases h
    exact leafWitness_solution hreach hw'
  · split at h <;> cases h

end LeanFzn.Solver.UIP

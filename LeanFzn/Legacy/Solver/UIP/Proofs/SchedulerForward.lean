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

import LeanFzn.Legacy.Solver.UIP.SchedulerStep
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerInvariant
import LeanFzn.Legacy.Solver.UIP.Proofs.LearnedExplanation
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
    ∀ i v, v ∈ (Frame.domains bs.frame).getD i Dom.empty → v ∈ orig.getD i Dom.empty :=
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
theorem checkpointsBelow_init {prio : List Nat} {actBump : Bool} (leaf : Assignment → Bool)
    (orig : List Domain) (original : List Clause) (props : List Propagator) :
    CheckpointsBelow (SchedulerConfig.init (leaf := leaf) orig original props prio actBump) := by
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
  simpa [stepPropagate, narrowState] using h cp (by simpa [stepPropagate] using hcp)

/-- `decide` keeps the checkpoint-level discipline: the pushed checkpoint
is the PARENT snapshot (level = parent level, REPAIRED by the integration
fix), and the old ones move down by one. -/
theorem checkpointsBelow_decide {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {k : Nat} {v : Value} {vs : Domain}
    {l : Literal} (h : CheckpointsBelow cfg) :
    CheckpointsBelow (stepDecide cfg k v vs l) := by
  intro cp hcp
  rcases List.mem_cons.mp hcp with rfl | hcp
  · show cfg.branch.level ≤ cfg.branch.level + 1
    exact Nat.le_succ _
  · exact Nat.le_succ_of_le (h cp hcp)

/-- `decideSkip` keeps the checkpoint-level discipline (branch level and
checkpoint list are unchanged). -/
theorem checkpointsBelow_decideSkip {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {k : Nat} {v : Value}
    (h : CheckpointsBelow cfg) :
    CheckpointsBelow (stepDecideSkip cfg k v) := by
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
    (orig : List Domain) (original : List Clause) (props : List Propagator)
    (hent : LearnedEntailed leaf original) :
    RootInvariant leaf orig original props :=
  schedulerInvariant_init leaf orig original props hent

/-- The root also satisfies the checkpoint-level discipline. -/
theorem schedulerForward_init_checkpointsBelow {prio : List Nat} {actBump : Bool} (leaf : Assignment → Bool)
    (orig : List Domain) (original : List Clause) (props : List Propagator) :
    CheckpointsBelow (SchedulerConfig.init (leaf := leaf) orig original props prio actBump) :=
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
  syncSlot_reachable _ (explainedDeduction_narrow_reachable hc hinv.reachable hu hd)
    hc.leafFits

/-- `propagate` never touches the pending frontier. -/
theorem stepPropagate_pending_fits {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} (hinv : SchedulerInvariant cfg)
    (d : ProductiveDeduction leaf cfg.branch) :
    ∀ f ∈ (stepPropagate cfg d).pending, ∀ i v,
      v ∈ (Frame.domains f).getD i Dom.empty → v ∈ cfg.orig.getD i Dom.empty := by
  intro f hf i v hv
  exact hinv.pending_fits f (by simpa [stepPropagate] using hf) i v hv

/-- `propagate` keeps the current frame inside the original box (the
narrowed frame is a pointwise subset of the old one). -/
theorem stepPropagate_branch_fits {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} (hinv : SchedulerInvariant cfg)
    (d : ProductiveDeduction leaf cfg.branch) :
    ∀ i v, v ∈ (Frame.domains (stepPropagate cfg d).branch.frame).getD i Dom.empty →
      v ∈ cfg.orig.getD i Dom.empty :=
  fun i v hv => hinv.branch_fits i v (Frame.domains_subsets d.filtered i v
    (by simpa [stepPropagate, narrowState] using hv))

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
  obtain ⟨-, -, -, ex, hex, hexl⟩ := syncSlot_shape cfg.orig
    (narrowState cfg.branch d.frame d.literal d.reason d.learned) d.literal.atom.slot
  refine ⟨hlev, ⟨mid ++ ([(⟨d.literal.norm, cfg.branch.level,
      some { clause := d.reason }⟩ : TrailEntry)] ++ ex), ?_, ?_⟩, ?_⟩
  · simp only [stepPropagate]
    rw [hex]
    simp only [narrowState]
    rw [htrail, List.append_assoc, List.append_assoc]
  · intro e he
    have he' : e ∈ mid ∨ e = (⟨d.literal.norm, cfg.branch.level,
        some { clause := d.reason }⟩ : TrailEntry) ∨ e ∈ ex := by
      simpa [or_assoc] using he
    rcases he' with he | he | he
    · exact hmid e he
    · rw [he]
      show cp.level ≤ cfg.branch.level
      exact hle
    · rw [hexl e he]
      exact hle
  · intro a ha
    exact hdesc a (FrameCovers_of_subsets (filterFrame_rem_length d.filtered)
      (filterFrame_subsets d.filtered)
      (by simpa [stepPropagate, narrowState] using ha))

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
  obtain ⟨-, -, -, ex, hex, hexl⟩ := syncSlot_shape cfg.orig
    (narrowState cfg.branch d.frame d.literal d.reason d.learned) d.literal.atom.slot
  refine ⟨hlev, ⟨mid ++ ([(⟨d.literal.norm, cfg.branch.level,
      some { clause := d.reason }⟩ : TrailEntry)] ++ ex), ?_, ?_⟩, ?_⟩
  · simp only [stepPropagate]
    rw [hex]
    simp only [narrowState]
    rw [htrail, List.append_assoc, List.append_assoc]
  · intro e he
    have he' : e ∈ mid ∨ e = (⟨d.literal.norm, cfg.branch.level,
        some { clause := d.reason }⟩ : TrailEntry) ∨ e ∈ ex := by
      simpa [or_assoc] using he
    rcases he' with he | he | he
    · exact hmid e he
    · rw [he]
      show cp.level ≤ cfg.branch.level
      exact hle
    · rw [hexl e he]
      exact hle
  · intro a ha
    exact hdesc a (FrameCovers_of_subsets (filterFrame_rem_length d.filtered)
      (filterFrame_subsets d.filtered)
      (by simpa [stepPropagate, narrowState] using ha))

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
      exact ⟨d.frame, by simp [SchedulerConfig.frontier, stepPropagate, narrowState], hcov'⟩
    · left
      exact ⟨f, List.mem_cons_of_mem _ hf, hcov⟩
  · right
    rcases hdb with ⟨c, hc', hnc⟩
    exact ⟨c, by simpa [stepPropagate, narrowState] using Or.inr hc', hnc⟩

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
  refine clauseProvenance_mono ?_ (clauseProvenance_of_contract hc hinv.reachable hu hev)
  obtain ⟨-, -, -, ex, hex, -⟩ := syncSlot_shape cfg.orig
    (narrowState cfg.branch d.frame d.literal d.reason d.learned) d.literal.atom.slot
  intro e he
  simp only [stepPropagate]
  rw [hex]
  exact List.mem_append_left _ he

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
  obtain ⟨-, -, -, ex, hex, -⟩ := syncSlot_shape cfg.orig
    (narrowState cfg.branch d.frame d.literal d.reason d.learned) d.literal.atom.slot
  refine learnedProvenance_mono ?_ (by simp [stepPropagate]) h
  intro e he
  simp only [stepPropagate]
  rw [hex]
  exact List.mem_append_left _ he

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
    rcases List.mem_append.mp (by simpa [stepPropagate, narrowState] using hcmem) with hcmem | hcmem
    · refine fun c' hc' => ?_
      rw [List.mem_singleton] at hc'
      rw [hc']
      exact hentLearned c hcmem
    · exact hinv.learned_entailed c hcmem

/-! ## §4 Decision / split -/

/-- The split data determines the parent frame's selected-slot
decomposition (C1's `splitData_eq_some_iff`): the parent admits `v :: vs`
at the policy-selected slot `k`, and the children are `f.pin k v` /
`f.retire k vs`. -/
theorem splitData_parent {f : BranchFrame} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain} {σ : List Nat} (h : splitData f σ = some (l, k, v, vs)) :
    f.doms[k]?.map Dom.enum = some (v :: vs.enum) :=
  (splitData_eq_some_iff.mp h).2.1

/-- The selected split slot, read as the structural domain and its
enumeration. -/
theorem exists_dom_of_splitData {f : BranchFrame} {l : Literal} {k : Nat}
    {v : Value} {vs : Domain} {σ : List Nat}
    (h : splitData f σ = some (l, k, v, vs)) :
    ∃ d : Domain, f.doms[k]? = some d ∧ Dom.enum d = v :: vs.enum := by
  have hmap := splitData_parent h
  cases hk : f.doms[k]? with
  | none => rw [hk] at hmap; simp at hmap
  | some d =>
      rw [hk, Option.map_some, Option.some.injEq] at hmap
      exact ⟨d, rfl, hmap⟩

/-- The selected split slot's enumeration, read through `getD`. -/
theorem enum_getD_of_splitData {f : BranchFrame} {l : Literal} {k : Nat}
    {v : Value} {vs : Domain} {σ : List Nat}
    (h : splitData f σ = some (l, k, v, vs)) :
    Dom.enum (f.doms.getD k Dom.empty) = v :: vs.enum := by
  obtain ⟨d, hd, hde⟩ := exists_dom_of_splitData h
  rw [List.getD_eq_getElem?_getD, hd, Option.getD_some, hde]

/-- `stableStep` reports exactly the split the transition function
consumes: the bridge C2d needs to match the dispatcher's `Literal`. -/
theorem stableStep_decide {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain} (hw : leafWitness leaf cfg = none)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs)) :
    stableStep cfg = .decide (stepDecide cfg k v vs l) l := by
  simp only [stableStep, hw, hsplit]

/-- COHERENCE under a decision: A1's `reachable_decide`, with the
freshness premise supplied by the runtime's absence check
(`TrailRedundant ... = false`, the same gate `explainedDeduction` uses —
see `stepDecide_redundant_not_distinct` for why it is necessary). -/
theorem stepDecide_reachable {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain} (hinv : SchedulerInvariant cfg)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hpin : ∀ a : Assignment, a.Fits cfg.orig →
      (l.norm.eval a = some true ↔ a[k]? = some v))
    (hred : TrailRedundant cfg.branch.trail l = false) :
    ReachableState leaf cfg.orig (stepDecide cfg k v vs l).branch := by
  obtain ⟨d, hd, hde⟩ := exists_dom_of_splitData hsplit
  refine reachable_decide hinv.reachable hd ?_ hpin
    (not_trailRedundant_iff.mp hred)
  exact (DomainLike.mem_iff _ _).mpr (by
    rw [domElems_eq_enum, hde]
    exact List.mem_cons_self ..)

/-- COHERENCE for a GENUINE branch: a second value in the head domain plus
a completable tail makes the pin unforced, so the decision needs no
runtime absence check (A1's `reachable_decide_of_second_value`; the
forced/redundant case is exactly the counterexample below). -/
theorem stepDecide_reachable_of_second_value {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain} (hinv : SchedulerInvariant cfg)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hpin : ∀ a, l.norm.eval a = some true ↔ a[k]? = some v)
    (hsecond : ∃ w' ∈ (v :: vs.enum), w' ≠ v)
    (hlive : ∃ a, FrameCovers cfg.branch.frame a) :
    ReachableState leaf cfg.orig (stepDecide cfg k v vs l).branch := by
  obtain ⟨w', hw', hne⟩ := hsecond
  obtain ⟨d, hd, hde⟩ := exists_dom_of_splitData hsplit
  refine reachable_decide_of_second_value hinv.reachable hd ?_ ?_ hne hpin hlive
  · exact (DomainLike.mem_iff _ _).mpr (by
      rw [domElems_eq_enum, hde]
      exact List.mem_cons_self ..)
  · exact (DomainLike.mem_iff _ _).mpr (by
      rw [domElems_eq_enum, hde]
      exact hw')

/-- The BOOLEAN specialization: `splitData`'s pin literal is
`valueLiteral`'s, and `valueLiteral_holds_iff` derives the pin semantics,
so `stepDecide_reachable`'s premises reduce to the runtime absence check.
The INT-valued case pins via the integer view (`slotInt`); its bridge is
`IntViewedDomain`'s (ExplainedPropagation §"root-fact soundness") — see
the C2a resume note for the named gap. -/
theorem stepDecide_bool_reachable {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {b : Bool}
    {vs : Domain} (hinv : SchedulerInvariant cfg)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, .bool b, vs))
    (hred : TrailRedundant cfg.branch.trail l = false) :
    ReachableState leaf cfg.orig (stepDecide cfg k (.bool b) vs l).branch := by
  have hwl := (splitData_eq_some_iff.mp hsplit).2.2.1
  refine stepDecide_reachable hinv hsplit ?_ hred
  intro a _
  rw [Literal.norm_eval]
  simpa using valueLiteral_holds_iff hwl a

/-- FINDING — the redundant pin DESTROYS the duplicate-safe discipline: if
the decision's normalized literal is already recorded at another level,
`stepDecide` duplicates the trail entry (A1's `decide_duplicates`). The
runtime must therefore refuse a decided pin that fails
`TrailRedundant ... = false`; `splitData` accepts singleton head domains,
so this guard is a genuine runtime obligation, not a hypothetical. -/
theorem stepDecide_redundant_not_distinct {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain}
    (hmem : ∃ e ∈ cfg.branch.trail, e.literal = l.norm ∧
      e.level ≠ cfg.branch.level + 1) :
    ¬ TrailLiteralsDistinct (stepDecide cfg k v vs l).branch.trail :=
  TrailLiteralsDistinct.decide_duplicates hmem

/-- The sibling alternative stays inside the original box: `vs` is a
sub-domain of the parent head `v :: vs` and the remaining slots are
literally the parent's. -/
theorem stepDecide_pending_fits {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain} (hinv : SchedulerInvariant cfg)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs)) :
    ∀ f ∈ (stepDecide cfg k v vs l).pending, ∀ i w,
      w ∈ (Frame.domains f).getD i Dom.empty → w ∈ cfg.orig.getD i Dom.empty := by
  obtain ⟨d, hd, hde⟩ := exists_dom_of_splitData hsplit
  -- the sibling `f.retire k vs`: its box is the parent's with `vs` at `k`
  have hsub : ∀ w ∈ vs, w ∈ cfg.branch.frame.doms.getD k Dom.empty := by
    intro w hw
    have hwE : w ∈ vs.enum := by
      simpa [domElems_eq_enum] using (DomainLike.mem_iff _ _).mp hw
    refine (DomainLike.mem_iff _ _).mpr ?_
    rw [domElems_eq_enum, List.getD_eq_getElem?_getD, hd, Option.getD_some, hde]
    exact List.mem_cons_of_mem _ hwE
  intro f hf i w hw
  rcases List.mem_cons.mp hf with rfl | hf
  · refine hinv.branch_fits i w ?_
    simpa only [Frame.domains, stepDecide_frame, BranchFrame.retire_doms] using
      getD_set_subset hsub i w (by
        simpa only [Frame.domains, stepDecide_frame, BranchFrame.retire_doms] using hw)
  · exact hinv.pending_fits f hf i w hw

/-- The pinned child stays inside the original box (A1's
`fullDomains_decide_subset`). -/
theorem stepDecide_branch_fits {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain} (hinv : SchedulerInvariant cfg)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs)) :
    ∀ i w, w ∈ (Frame.domains (stepDecide cfg k v vs l).branch.frame).getD i Dom.empty →
      w ∈ cfg.orig.getD i Dom.empty := by
  obtain ⟨d, hd, hde⟩ := exists_dom_of_splitData hsplit
  have hsub : ∀ w ∈ (Dom.ofList [v] : Domain), w ∈ cfg.branch.frame.doms.getD k Dom.empty := by
    intro w hw
    have hwv : w = v := by
      simpa [domElems_eq_enum] using (DomainLike.mem_iff _ _).mp hw
    subst hwv
    refine (DomainLike.mem_iff _ _).mpr ?_
    rw [domElems_eq_enum, List.getD_eq_getElem?_getD, hd, Option.getD_some, hde]
    exact List.mem_cons_self ..
  intro i w hw'
  refine hinv.branch_fits i w ?_
  simpa only [Frame.domains, stepDecide_frame, BranchFrame.pin_doms] using
    getD_set_subset hsub i w (by
      simpa only [Frame.domains, stepDecide_frame, BranchFrame.pin_doms] using hw')

/-- COVERAGE under a split: the parent frame is REPLACED by its two
children (`covers_split`), so no leaf solution leaves the frontier; the
pending stack and the database are untouched. This is a genuine
preservation: neither child drops a covered solution. -/
theorem stepDecide_covers {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain} (hinv : SchedulerInvariant cfg)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs)) :
    (stepDecide cfg k v vs l).coverage := by
  have hdom := (splitData_eq_some_iff.mp hsplit).2.1
  intro a hleaf
  rcases hinv.coverage a hleaf with ⟨f, hf, hcov⟩ | hdb
  · rcases List.mem_cons.mp hf with rfl | hf
    · left
      rcases (covers_split_at hdom a).mp hcov with hchild | hsib
      · exact ⟨cfg.branch.frame.pin k v,
          List.mem_cons_self .., hchild⟩
      · exact ⟨cfg.branch.frame.retire k vs,
          List.mem_cons_of_mem _ (List.mem_cons_self ..), hsib⟩
    · left
      exact ⟨f, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hf), hcov⟩
  · right
    exact hdb

/-- CHECKPOINT IDENTITY of a split: the newest checkpoint (the pre-pinning
parent frame at the fresh level) identifies the pinned child, and the
older checkpoints still identify it. -/
theorem stepDecide_checkpoints_identify {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain} (hinv : SchedulerInvariant cfg)
    (hlevel : CheckpointsBelow cfg)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs)) :
    ∀ cp ∈ (stepDecide cfg k v vs l).checkpoints,
      cp.Identifies (stepDecide cfg k v vs l).branch cp.level := by
  obtain ⟨d, hd, hde⟩ := exists_dom_of_splitData hsplit
  have hv : v ∈ d := (DomainLike.mem_iff _ _).mpr (by
    rw [domElems_eq_enum, hde]
    exact List.mem_cons_self ..)
  have hchild : FrameDescendsFrom (cfg.branch.frame.pin k v)
      cfg.branch.frame :=
    fun a ha => FrameCovers_pin_subset hd hv ha
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
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain}
    (hident : ∀ cp ∈ cfg.checkpoints, cp.Identifies cfg.branch cp.level)
    (hlevel : CheckpointsBelow cfg)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs)) :
    ∀ cp ∈ (stepDecide cfg k v vs l).checkpoints,
      cp.Identifies (stepDecide cfg k v vs l).branch cp.level := by
  obtain ⟨d, hd, hde⟩ := exists_dom_of_splitData hsplit
  have hv : v ∈ d := (DomainLike.mem_iff _ _).mpr (by
    rw [domElems_eq_enum, hde]
    exact List.mem_cons_self ..)
  have hchild : FrameDescendsFrom (cfg.branch.frame.pin k v)
      cfg.branch.frame :=
    fun a ha => FrameCovers_pin_subset hd hv ha
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
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain} (hinv : SchedulerInvariant cfg)
    (hlevel : CheckpointsBelow cfg)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hpin : ∀ a : Assignment, a.Fits cfg.orig →
      (l.norm.eval a = some true ↔ a[k]? = some v))
    (hred : TrailRedundant cfg.branch.trail l = false) :
    SchedulerInvariant (stepDecide cfg k v vs l) :=
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
  obtain ⟨hframe, hleaf⟩ := leafWitness_eq_some_iff.mp h
  have hdom := (BranchFrame.assignment?_eq_some_iff cfg.branch.frame w).mp hframe
  refine ⟨hleaf, ?_, ?_⟩
  · have hlen : w.length = cfg.branch.frame.doms.length := by
      have := congrArg List.length hdom
      simpa using this.symm
    rw [hlen]
    simpa [fullDomains, Frame.domains] using hreach.length_ok
  · intro slot value hget
    have hmap : (cfg.branch.frame.doms.map Dom.enum)[slot]? =
        (w.map (fun v => [v]))[slot]? := by rw [hdom]
    rw [List.getElem?_map, List.getElem?_map, hget] at hmap
    have hmem' : value ∈ cfg.branch.frame.doms.getD slot Dom.empty := by
      cases hk : cfg.branch.frame.doms[slot]? with
      | none =>
          rw [hk] at hmap
          simp at hmap
      | some d =>
          rw [hk] at hmap
          simp only [Option.map_some, Option.some.injEq] at hmap
          rw [List.getD_eq_getElem?_getD, hk, Option.getD_some]
          exact (DomainLike.mem_iff _ _).mpr (by
            rw [domElems_eq_enum, hmap]
            exact List.mem_singleton_self value)
    exact hreach.full_fits slot value hmem'

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

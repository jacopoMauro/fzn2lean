/-
File: LeanFzn/Solver/UIP/Proofs/FreshCoverless.lean
coverless-site `hfresh` producer and its level-separation residual)

Purpose: discharge (PLAN.md C2) the `hfresh` family of
`supportedHpre_of_snapshots` / `supportedHfresh_of_site`

    hfresh : ∀ {cfg ev an cp}, SupportedReach … cfg → cfg.conflict = some ev →
      ev.analysis = some an → checkpointAt cfg.checkpoints an.backjumpLevel
        = some cp → ∀ e ∈ cp.trail, e.literal ≠ an.asserting.norm

without the KERNEL-REFUTED inhabitedness premise. C2a
(`Proofs/SiteInhabited.lean`) refuted the all-sites family; C2a-2
(`Proofs/SiteLiveness.lean`) refuted the recorded-site family for the unit
kit (`recordedInhabited_false`). The landed producers
(`CheckpointPrefix.supportedHfresh_of_reach`, `HdeadCkpt.supportedHfresh_of_site`)
consume inhabitedness because their argument needs a COVERED assignment:
an entry of the checkpoint trail carrying `(uip.negate).norm` and the UIP
entry carrying `uip` cannot both hold at a covering assignment.

## FINDING (this file): the coverless case closes by LEVEL, not by coverage

The UIP witness `analyzeStep_uip_on_trail` puts an entry `m` of the branch
trail at the CONFLICT level (`m.literal = uip`, `m.level = cfg.branch.level`)
while the checkpoint's entries sit at level `≤ an.backjumpLevel` (the
checkpoint is a reachable snapshot at the target level, so its trail's
levels are bounded by `CheckpointSnapshot`'s `ReachableState.wf.1`), and
the target STRICTLY descends on recorded sites
(`RestorationCertificate.targetDescends` + `recorded_conflict_level_pos`).
Hence `hfresh` follows from ONE structural property of the branch trail:

  `TrailLevelSeparated an.backjumpLevel cfg.branch.trail`, i.e.
  no entry at level `≤ target` is the normalized negation of an entry
  strictly above `target`

— a purely LEVEL-separated discipline, with no coverage, no inhabitedness
and no frame content. §2 proves the reduction (`hfresh` from the separation
at the site); §3 assembles the honest producer: the `inhabited ∨ coverless`
classification of C2a (`frameCovers_or_coverless`) with the live branch on
the landed semantic route and the coverless branch on §2.

## What is PROVED about the residual (§4, §5)

  * `canonicalTrail_levelSeparated` — the residual HOLDS, kernel-checked,
    for every canonical resume trail (`canonicalTrail orig f`, the trail
    every `stepConsume` installs): with an empty prefix all its entries sit
    at level `0`, with a nonempty prefix none does (`canonicalPins`'
    entries sit at `slot + 1`, the falsifiers at the prefix length), and
    either side of the separation is then vacuous.  * `unitKit_backjumpLevel_eq_zero` — at the unit kit's supported recorded
    sites the analysis target is ALWAYS `0` (the recorded clause is a
    normalized singleton, so the below-list is empty), so the residual is
    exactly `TrailLevelSeparated 0 …` there and §4's canonical lemma
    applies to every pure canonical-resume site;  * `plainConsistent_canonicalTrail_refuted` — the LEVEL-SYMMETRIC
    "no complementary pair" discipline is FALSE, kernel-checked: the
    canonical resume of the coverless bool slot emits the two retiring
    entries at the SAME level (`posBool 0 true` and `posBool 0 false`, both
    at level `0`). The strict level separation is therefore the honest
    shape: it permits exactly the same-level pairs the canonical resume
    produces.
  * `cx5_hfresh_vacuous` / `cx5_trail_levelSeparated` — the C2a-2
    counterexample site (the coverless `cx5`) carries NO checkpoint at the
    analysis target (so `hfresh` is VACUOUS there: the refuted premise's
    witness does not falsify `hfresh`) and its trail satisfies the
    separation at the unit kit's target `0`. A computational class
    exploration (unit kits over small bool/int boxes, constraint lists of
    size ≤ 2, up to 40-60 real `schedulerNext` steps per instance, ~12k
    instances / 44k steps) found NO `hfresh` violation and NO coverless
    recorded site with a checkpoint at the target; exploration only, NOT a
    proof.

RESIDUAL (reported, named, and NOT assumed away): the separation at the
coverless sites that are NOT pure canonical resumes — i.e. after the
`stepConsume` the trail grows by level-0 propagations (an empty-prefix
resume) or by level-≥1 entries (a nonempty-prefix resume, where §4 already
gives the separation). §4's lemmas show the residual is exactly the
"narrowing at level 0 whose literal is later a conflict literal" case.

NO `sorry`, NO custom axiom. Registration owes the umbrella import line
`LeanFzn.Solver.UIP.Proofs.FreshCoverless` in `LeanFzn.Solver/LeanFzn.Solver.UIP.lean` (coordinator).
-/

import LeanFzn.Solver.UIP.Proofs.HdeadCkpt
import LeanFzn.Solver.UIP.Proofs.SiteInhabited
import LeanFzn.Solver.UIP.Proofs.SiteLiveness
import LeanFzn.Solver.UIP.Proofs.UnitRunSupported
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 The level-separation discipline -/

/-- THE LEVEL-SEPARATION DISCIPLINE: no trail entry at level `≤ target` is
the normalized negation of a trail entry strictly above `target`. This is
the exact structural fact the coverless case of `hfresh` needs (§2); it is
strictly weaker than trail consistency (same-level complementary pairs are
permitted, and §5 shows the canonical resume produces them). -/
def TrailLevelSeparated (target : Nat) (trail : List TrailEntry) : Prop :=
  ∀ e₀ ∈ trail, e₀.level ≤ target → ∀ e ∈ trail, target < e.level →
    e₀.literal ≠ e.literal.negate.norm

/-- The separation is vacuous when nothing sits above the target. -/
theorem trailLevelSeparated_of_no_high {target : Nat} {trail : List TrailEntry}
    (h : ∀ e ∈ trail, e.level ≤ target) : TrailLevelSeparated target trail := by
  intro e₀ _ _ e he hlt
  exact absurd (h e he) (by omega)

/-- The separation is vacuous when nothing sits at or below the target. -/
theorem trailLevelSeparated_of_no_low {target : Nat} {trail : List TrailEntry}
    (h : ∀ e ∈ trail, target < e.level) : TrailLevelSeparated target trail := by
  intro e₀ he₀ hle
  exact absurd (h e₀ he₀) (by omega)

/-! ## §2 The reduction: `hfresh` from the level separation

The UIP witness supplies the strictly-above-target entry; the checkpoint
snapshot bounds the checkpoint's levels by the target; the separation kills
the coincidence. `hcertSite` is consumed only for `targetDescends`. -/

/-- **THE COVERLESS-CASE `hfresh` PRODUCER (site form)**: at ONE supported
recorded-evidence site whose selected checkpoint has a snapshot, the level
separation at the site's own target gives the enqueue absence check. No
inhabitedness, no frame coverage: the reduction is purely about levels. -/
theorem supportedHfresh_of_site_separated {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf}
    (hreach : SupportedReach orig original props cfg)
    (hcertSite : ∀ {ev : ConflictEvidence} {an : ConflictAnalysis},
      cfg.conflict = some ev → ev.analysis = some an →
        RestorationCertificate leaf cfg.branch an)
    (hsnapSite : ∀ {ev : ConflictEvidence} {an : ConflictAnalysis}
      {cp : DecisionCheckpoint leaf},
      cfg.conflict = some ev → ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
        CheckpointSnapshot leaf orig cp)
    (hsepSite : ∀ {ev : ConflictEvidence} {an : ConflictAnalysis},
      cfg.conflict = some ev → ev.analysis = some an →
        TrailLevelSeparated an.backjumpLevel cfg.branch.trail) :
    ∀ {ev : ConflictEvidence} {an : ConflictAnalysis} {cp : DecisionCheckpoint leaf},
      cfg.conflict = some ev → ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
        ∀ e ∈ cp.trail, e.literal ≠ an.asserting.norm := by
  intro ev an cp hconf hana hcp e he
  -- the canonical record and its UIP witness on the trail
  obtain ⟨below, uip, hrun, hcanon⟩ :=
    reachable_analysis_success leaf cfg ev an hreach.reachable hconf hana
  have hass : an.asserting.norm = (uip.negate).norm := by
    rw [hcanon, ConflictAnalysis.normalized_asserting,
      ConflictAnalysis.ofUIP_asserting, norm_norm]
  obtain ⟨m, hm, hmlit, hmlev⟩ :=
    analyzeAtAllowance_uip_on_trail hrun
  -- the checkpoint's trail is a prefix of the branch trail
  obtain ⟨hident, -⟩ := identifiesChain_of_reach hreach
  obtain ⟨mid, hmid, -⟩ := hident cp (checkpointAt_mem hcp) |>.2.1
  have he' : e ∈ cfg.branch.trail := by
    rw [hmid]; exact List.mem_append.mpr (Or.inl he)
  -- the checkpoint's entries sit at or below the target (its snapshot)
  obtain ⟨bs', hbs', -, ht, hl⟩ := hsnapSite hconf hana hcp
  have hlevE : e.level ≤ an.backjumpLevel := by
    have h1 : e.level ≤ bs'.level := hbs'.wf.1 e (by rw [ht]; exact he)
    rw [hl, checkpointAt_level hcp] at h1
    exact h1
  -- the UIP entry sits strictly above the target
  have hlt : an.backjumpLevel < cfg.branch.level := by
    have hd := (hcertSite hconf hana).targetDescends
    have hp := recorded_conflict_level_pos hreach.reachable ev hconf
    rcases hd with h0 | h
    · omega
    · exact h
  have hmgt : an.backjumpLevel < m.level := by
    rw [hmlev]; exact hlt
  -- the separation kills the coincidence
  intro hcon
  exact (hsepSite hconf hana e he' hlevE m hm hmgt) (hcon.trans (by rw [hass, ← hmlit]))

/-! ## §3 The honest producer (the C2a classification, live/coverless split)

The `inhabited ∨ coverless` classification of C2a is premise-free
(`frameCovers_or_coverless`); the live branch is the landed semantic
producer (`HdeadCkpt.supportedHfresh_of_site`), the coverless branch is
§2's level reduction. The single residual premise is the level separation
at the COVERLESS sites. -/

/-- **THE `hfresh` FAMILY WITH THE COVERLESS CASE REDUCED TO THE LEVEL
SEPARATION**: at every supported recorded-evidence site, the enqueue
absence check holds, with the frame's inhabitedness produced internally by
the C2a classification. The only premise beyond the run-level producers
(`hbr`, `hcert`, `hsnaps`) is `hsepF` — the level separation at coverless
sites. -/
theorem supportedHfresh_of_reach_coverlessSeparated {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hcert : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an → RestorationCertificate leaf cfg.branch an)
    (hsnaps : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableCpSnapshots leaf orig cfg)
    (hsepF : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an → (∃ d ∈ cfg.branch.frame.1, d = []) →
        TrailLevelSeparated an.backjumpLevel cfg.branch.trail) :
    ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis} {cp : DecisionCheckpoint leaf},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
        ∀ e ∈ cp.trail, e.literal ≠ an.asserting.norm := by
  intro cfg ev an cp hreach hconf hana hcp
  rcases frameCovers_or_coverless cfg.branch.frame with hinhab | hcov
  · exact supportedHfresh_of_site rfl (hbr hreach) hreach hinhab hconf hana hcp
  · refine supportedHfresh_of_site_separated hreach ?_ ?_ ?_ hconf hana hcp
    · intro ev0 an0 hc ha
      exact hcert hreach hc ha
    · intro ev0 an0 cp0 hc ha hcp0
      exact hsnaps hreach cp0 (checkpointAt_mem hcp0)
    · intro ev0 an0 hc ha
      exact hsepF hreach hc ha hcov

/-! ## §4 The residual holds for canonical resume trails

`stepConsume` installs `canonicalTrail orig f` (`resumePending`): the prefix
pins at `slot + 1` and the remaining-slot retirements at the prefix length.
Either the prefix is empty (every entry at level `0`: nothing above the
target) or it is nonempty (no entry at or below `0`): the separation at
target `0` follows both ways. -/

/-- A canonical pin's entry sits at `slot + 1`. -/
theorem canonicalPinEntry_level {slot : Nat} {w : Value} {e : TrailEntry}
    (h : canonicalPinEntry slot w = some e) : e.level = slot + 1 := by
  unfold canonicalPinEntry at h
  cases hv : valueLiteral slot w with
  | none => simp [hv] at h
  | some l =>
      simp [hv] at h
      subst h
      rfl

/-- A canonical retirement's entry sits at the resume level. -/
theorem canonicalRetire_level {level slot : Nat} {w : Value} {e : TrailEntry}
    (h : canonicalRetire level slot w = some e) : e.level = level := by
  unfold canonicalRetire at h
  cases hv : valueLiteral slot w with
  | none => simp [hv] at h
  | some l =>
      simp [hv] at h
      subst h
      rfl

/-- Every canonical pin sits at a positive level. -/
theorem canonicalPins_level_pos {pre : List Value} {e : TrailEntry}
    (he : e ∈ canonicalPins pre) : 0 < e.level := by
  rw [canonicalPins, List.mem_filterMap] at he
  obtain ⟨p, -, hpe⟩ := he
  have := canonicalPinEntry_level hpe
  omega

/-- There are no canonical pins for an empty prefix. -/
theorem canonicalPins_nil {e : TrailEntry} (he : e ∈ canonicalPins ([] : List Value)) :
    False := by
  rw [canonicalPins] at he
  simp at he

/-- Every remaining-slot retirement sits at the frame's prefix length. -/
theorem slotFalsifiers_level {orig : List Domain} {f : BranchFrame} {i : Nat}
    {dom : Domain} {e : TrailEntry} (he : e ∈ slotFalsifiers orig f i dom) :
    e.level = f.2.length := by
  dsimp only [slotFalsifiers] at he
  rw [List.mem_filterMap] at he
  obtain ⟨p, -, hpe⟩ := he
  split at hpe
  · simp at hpe
  · rename_i l hl
    split at hpe
    · simp at hpe
    · split at hpe
      · simp at hpe
      · exact canonicalRetire_level hpe

/-- Every canonical falsifier sits at the frame's prefix length. -/
theorem canonicalFalsifiers_level {orig : List Domain} {f : BranchFrame}
    {e : TrailEntry} (he : e ∈ canonicalFalsifiers orig f) :
    e.level = f.2.length := by
  dsimp only [canonicalFalsifiers] at he
  rw [List.mem_flatten] at he
  obtain ⟨l, hl, hel⟩ := he
  rw [List.mem_map] at hl
  obtain ⟨p, -, rfl⟩ := hl
  exact slotFalsifiers_level hel

/-- **THE RESIDUAL HOLDS FOR CANONICAL RESUME TRAILS**: every
`canonicalTrail` satisfies the level separation at target `0` — the unit
kit's analysis target (`below = []` makes `an.backjumpLevel = 0`). -/
theorem canonicalTrail_levelSeparated {orig : List Domain} {f : BranchFrame} :
    TrailLevelSeparated 0 (canonicalTrail orig f) := by
  obtain ⟨slots, pre⟩ := f
  cases pre with
  | nil =>
      refine trailLevelSeparated_of_no_high ?_
      intro e he
      rw [canonicalTrail] at he
      rcases List.mem_append.mp he with he | he
      · exact absurd he (canonicalPins_nil ·)
      · have hlev := canonicalFalsifiers_level he
        simp at hlev
        omega
  | cons v rest =>
      refine trailLevelSeparated_of_no_low ?_
      intro e he
      rw [canonicalTrail] at he
      rcases List.mem_append.mp he with he | he
      · have := canonicalPins_level_pos he
        omega
      · have hlev := canonicalFalsifiers_level he
        simp at hlev
        omega

/-- **THE UNIT KIT'S ANALYSIS TARGET IS ZERO**: at every supported
recorded-evidence site of the unit kit whose analysis succeeded, the
recorded analysis's `backjumpLevel` is `0` — the recorded clause is a
normalized singleton (N1), so the analyzed below-list is empty
(`analyzeAtAllowance_singleton_uip`). Hence the `hfresh` separation
residual is EXACTLY `TrailLevelSeparated 0 cfg.branch.trail` at the unit
kit's coverless sites, and §4's `canonicalTrail_levelSeparated` covers the
pure canonical-resume sites. -/
theorem unitKit_backjumpLevel_eq_zero {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hgate : UnitKitGate (leaf := leaf) orig original props) :
    ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
        ev.analysis = some an → an.backjumpLevel = 0 := by
  intro cfg ev an hreach hc ha
  obtain ⟨q, hq, -⟩ :=
    (unitRunInvariant_of_supported hprops hSupp hgate hreach).recorded ev hc |>.1
  obtain ⟨below, uip, hrun, heq⟩ :=
    reachable_analysis_success leaf cfg ev an hreach.reachable hc ha
  rw [hq] at hrun
  obtain ⟨hbelow, -⟩ := analyzeAtAllowance_singleton_uip hrun
  rw [heq, ConflictAnalysis.normalized_backjumpLevel,
    ConflictAnalysis.ofUIP_backjumpLevel, hbelow]
  rfl

/-! ## §5 Retained evidence (kernel-checked)

The two facts that shape the honest residual: the level-SYMMETRIC
discipline is refuted (the canonical resume's same-level pair), and the
C2a-2 counterexample site neither falsifies `hfresh` (no checkpoint at its
target) nor the separation. -/

/-- **THE LEVEL-SYMMETRIC DISCIPLINE IS FALSE**: the canonical resume of
the coverless bool slot `[[]]` emits the two retirements of `false` and
`true` — `posBool 0 true` and `posBool 0 false` — at the SAME level `0`.
So "no complementary pair at all" is refuted, while §4's level separation
(which permits same-level pairs) stands. -/
theorem plainConsistent_canonicalTrail_refuted :
    ¬ (∀ e₁ ∈ canonicalTrail [[Value.bool false, Value.bool true]]
          ([[]], ([] : Assignment)),
        ∀ e₂ ∈ canonicalTrail [[Value.bool false, Value.bool true]]
          ([[]], ([] : Assignment)),
          e₁.literal ≠ e₂.literal.negate.norm) := by
  intro h
  have htr : canonicalTrail [[Value.bool false, Value.bool true]]
      ([[]], ([] : Assignment))
      = [{ literal := posBool 0 true, level := 0, reason := none },
         { literal := posBool 0 false, level := 0, reason := none }] := rfl
  have hne := h _ (by rw [htr]; exact List.mem_cons_self ..) _
      (by rw [htr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
  exact hne rfl

/-- **THE C2a-2 SITE DOES NOT FALSIFY `hfresh`**: the counterexample's
recorded configuration `cx5` carries NO checkpoint at all (the consume
empties the list), so the `hfresh` premise `checkpointAt … = some cp` is
unsatisfiable there and the conclusion is vacuous. -/
theorem cx5_hfresh_vacuous {an : ConflictAnalysis}
    {cp : DecisionCheckpoint cxLeaf}
    (hcp : checkpointAt cx5.checkpoints an.backjumpLevel = some cp) :
    ∀ e ∈ cp.trail, e.literal ≠ an.asserting.norm := by
  have hnil : cx5.checkpoints = [] := rfl
  rw [hnil] at hcp
  simp [checkpointAt] at hcp

/-- **THE C2a-2 SITE SATISFIES THE SEPARATION AT THE UNIT-KIT TARGET**:
its canonical trail's entries all sit at level `1`, so the level-`0`
separation holds. -/
theorem cx5_trail_levelSeparated : TrailLevelSeparated 0 cx5.branch.trail := by
  have htr : cx5.branch.trail
      = [{ literal := posBool 0 false, level := 1, reason := none },
         { literal := posBool 1 false, level := 1, reason := none }] := rfl
  refine trailLevelSeparated_of_no_low ?_
  intro e he
  rw [htr] at he
  rcases List.mem_cons.mp he with rfl | he
  · decide
  · rw [List.mem_singleton] at he
    subst he
    decide

end LeanFzn.Solver.UIP

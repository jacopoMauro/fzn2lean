/-
File: LeanFzn/Solver/UIP/Proofs/SiteLiveness.lean
recorded-site liveness: the refutation and the honest structural split)

Purpose: discharge (PLAN.md C2) the recorded-site inhabitedness obligation

    hinhab : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
        ∃ a : Assignment, FrameCovers cfg.branch.frame a

that `SupportedInstance.supportedHpre_unitKit_of_site` (I1-A) carries as a
residual and that `HdeadCkpt.supportedHfresh_of_site` /
`ScanStability.databaseUnfalsified_of_reachable_recorded` consume at
recorded-evidence sites.

## FINDING — the RECORDED-SITE family is FALSE for the unit kit

C2a (`Proofs/SiteInhabited.lean`) refuted the ALL-SITES family. This file
refutes the RECORDED-SITE refinement as well, in the STRONGEST honest
form: on a genuine unit-kit instance (`props = dcs.filterMap
propagatorOfProved`, every `unitFamilyB dc = true`, box shape-compatible
with `ShapeTypedDomains`), a real five-step `schedulerNext` run reaches a
configuration carrying recorded evidence `cfg.conflict = some ev` whose
branch frame is COVERLESS — `([[]], [.bool false])`, an exhausted split
sibling with an empty remaining head domain. §1-§2:

* `cxOrig = [[false, true], [true]]`, `cxDcs = [.constEq 1 (.bool true)]`
  (`cxDcs_unitFamily`), leaf `fun _ => false`;
* the run: `decide` (pin `false` at slot 0) → `decide` (pin `true` at the
  singleton slot 1, pushing the coverless sibling `([[]], [false])`) →
  `localExclude` (the complete child fails the leaf) → `consume` (the
  coverless sibling becomes the branch at level 1) → **record**
  (`LeanFzn.Solver.Propagation.propConstEq 1 (.bool true)` on the empty remaining read is a genuine
  NONEMPTY conflict `[posBool 1 true]`, `scanDatabase` is stable and the
  frame is viewed, so `terminalResult = .conflict` and the level is
  positive — the recording arm fires);
* `cx5_false_family` — the exact recorded-site family shape, with the kit
  premises, is REFUTED; `cx5_refuted_existential` records the witness.

## The root cause, and the honest split (this file's positive content)

§4 shows the mechanism EXACTLY. At a recorded site the frame is viewed,
the database scan is stable, and the recording clause is a genuine
NONEMPTY propagator conflict (`recordedStep_is_propagatorConflict`,
KIT-FREE). For the unit kit, the five bound/equality families
(`leConstHi`, `leConstLo`, `ltConstHi`, `ltConstLo`, and `constEq` on
INTEGER constants) can only report a conflict when their slot's domain
read is NONEMPTY (`propLeConstHi_conflict_inv` and friends, with their
`_no_conflict_empty_read` corollaries),
while `constEq` on a BOOLEAN constant reports `[posBool i b]` whenever the
read does not contain `.bool b` — in particular at the EMPTY read
(`propConstEq_bool_conflict_empty_read`), which is exactly the channel the
counterexample uses. Hence the honest split of `hinhab` is BY FAMILY:

* bound-family-only kits may still admit the recorded-site liveness (the
  "stable live predecessor agreement" argument of C2a §5 — NOT delivered
  here, and NOT assumed);
* any kit containing `constEq _ (.bool _)` does NOT (the kernel witness
  above), so consumers must treat the coverless recorded site as possible
  and route it through the PROVED empty-frame evidence
  (`SiteInhabited.coverless_hdead` / `coverless_branchRegion_sound`), or
  strengthen the premises (e.g. exclude Boolean-constant equality from
  the unit kit, or restrict recorded-site conclusions to live frames).

NO `sorry`, NO custom axiom. Registration owes the umbrella import line
`LeanFzn.Solver.UIP.Proofs.SiteLiveness` in `LeanFzn.Solver/LeanFzn.Solver.UIP.lean` (coordinator).
-/

import LeanFzn.Legacy.Solver.UIP.Proofs.SiteInhabited
import LeanFzn.Legacy.Solver.UIP.Proofs.AnalysisEntail
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 The unit-kit counterexample instance

Box `[[false, true], [true]]`, ONE unit-family constraint, the Boolean
constant equality `slot 1 = true`. The box is `ShapeTypedDomains`-clean
(every domain is Boolean-shaped) and every value is int-viewed, so the
refutation is not an artifact of an exotic box. -/

/-- The counterexample's leaf: no assignment passes. -/
def cxLeaf : Assignment → Bool := fun _ => false

/-- The counterexample's box: two LIVE integer slots plus one EMPTY slot
that no constraint mentions. Decisions stay legal on the live slots while
every frame carrying the empty slot is coverless. -/
def cxOrig : List Domain :=
  [Dom.ofList [Value.int 0, Value.int 2, Value.int 3],
   Dom.ofList [Value.int 0, Value.int 2, Value.int 3],
   Dom.empty]

/-- The counterexample's stored clause: both literals are possible on the
root reads of slot 1 but IMPOSSIBLE once slot 1 is pinned to `0`. -/
def cxClause : Clause := [posLe 1 0, negNe 1 0]

/-- The counterexample's clause database. -/
def cxOriginal : List Clause := [cxClause]

/-- The counterexample's constraint list: EMPTY — the recorded conflict is
the kit-free DATABASE channel (a falsified stored clause). -/
def cxDcs : List DomConstraint := []

/-- The registered propagator kit: the proved-propagator image. -/
def cxProps : List Propagator := cxDcs.filterMap propagatorOfProved

/-- The instance is in the unit fragment. -/
theorem cxDcs_unitFamily : ∀ dc ∈ cxDcs, unitFamilyB dc = true := by
  intro dc hdc
  rw [cxDcs] at hdc
  cases hdc

/-- The registered kit is empty. -/
theorem cxProps_eq : cxProps = [] := rfl

/-! ## §2 The witness run (five real `schedulerNext` successors)

The run uses only S1-LEGAL decisions (both split slots are live) and an
untouched EMPTY slot 2 of the original box; every frame carrying it is
coverless. The recorded conflict comes from the kit-free DATABASE channel.

The run is deterministic:
  0. `decide` — split slot 0 (`[0,2,3]`), pinning the head `0`;
  1. `decide` — split slot 1 (`[0,2,3]`), pinning the head `0`; the
     pushed sibling is the coverless `⟨[[0],[2,3],[]],[0]⟩`;
  2. `localExclude` — the complete child `[[0],[0],[]]` fails the leaf and
     has no split data (slot 2 is empty);
  3. `consume` — the coverless sibling becomes the branch at level 1;
  4. `record` — the stored clause `[1 ≤ 0, 1 ≠ 0]` has both literals
     IMPOSSIBLE on the sibling read `[2,3]`, so the database scan reports
     the nonempty conflict `[cxClause]` and it is RECORDED at level 1. -/

/-- The root configuration. -/
def cx0 : SchedulerConfig cxLeaf := SchedulerConfig.init cxOrig cxOriginal cxProps

/-- The post-first-decision branch: slot 0 pinned to `0`, level 1. -/
def cxBs1 : BranchState cxLeaf :=
  { frame := ⟨[Dom.ofList [Value.int 0],
      Dom.ofList [Value.int 0, Value.int 2, Value.int 3], Dom.empty], [0]⟩,
    trail := [{ literal := negNe 0 0, level := 1, reason := none }],
    level := 1, learned := cxOriginal }

/-- Step 0's successor. -/
def cx1 : SchedulerConfig cxLeaf :=
  stepDecide cx0 0 (Value.int 0)
    (Dom.ofList [Value.int 2, Value.int 3]) (negNe 0 0)

/-- Step 1's successor. -/
def cx2 : SchedulerConfig cxLeaf :=
  stepDecide cx1 1 (Value.int 0)
    (Dom.ofList [Value.int 2, Value.int 3]) (negNe 1 0)

/-- Step 2's successor (the dead complete child). -/
def cx3 : SchedulerConfig cxLeaf := stepLocalExclude cx2 [] (branchRegion cx2)

/-- The pending sibling frame: slot 0 pinned, slot 1 keeps `[2,3]`, the
empty original slot 2 stays empty, decision order `[0]`, level 1. -/
def cxSib : BranchFrame :=
  ⟨[Dom.ofList [Value.int 0], Dom.ofList [Value.int 2, Value.int 3],
    Dom.empty], [0]⟩

/-- The coverless sibling's resumed branch (the canonical resume of
`cxSib`, including the `syncAll` entries). -/
def cxBs4 : BranchState cxLeaf := resumePending cxOrig cx3.branch cxSib

/-- Step 3's successor: the consumed coverless sibling. -/
def cx4 : SchedulerConfig cxLeaf :=
  { cx3 with
    branch := cxBs4,
    checkpoints := [],
    pending := [⟨[Dom.ofList [Value.int 2, Value.int 3],
      Dom.ofList [Value.int 0, Value.int 2, Value.int 3], Dom.empty], []⟩],
    status := .active,
    conflict := none }

/-- Step 4's successor: the recorded conflict at the coverless frame. -/
def cx5 : SchedulerConfig cxLeaf :=
  stepAnalyzeConflictCounted cx4 cxClause []
    (analyzeEventsExpansions cx4.orig cx4.branch.trail cx4.branch.level cxClause)

theorem cx1_branch : cx1.branch = cxBs1 := rfl

theorem cx4_consume : stepConsume cx3 = some cx4 := rfl

/-! ### §2.1 The five step equations -/

/-- STEP 0: the root is stable with a fresh split pin — `stepDecide`. -/
theorem cx_step0 : (schedulerNext cx0).successor = some cx1 := by
  have hd : explainedDeduction cxOriginal cxProps cx0.branch = none := by
    unfold explainedDeduction nextPruningEvent scanDatabase scanPropagators
      frameViewedB frameLiveB frameState Frame.domains
    rfl
  have ht : terminalResult cxOrig cxOriginal cxProps cx0.branch = .stable cx0.branch := by
    unfold terminalResult nextPruningEvent scanDatabase scanPropagators
      frameViewedB frameLiveB frameState Frame.domains
    rfl
  rw [C2d.schedulerNext_eq_stable_decide rfl rfl hd ht rfl rfl rfl]
  rfl

/-- STEP 1: the singleton head `[true]` splits with a fresh pin; the
pushed sibling is the coverless `([[]], [false])`. -/
theorem cx_step1 : (schedulerNext cx1).successor = some cx2 := by
  have hd : explainedDeduction cxOriginal cxProps cx1.branch = none := by
    rw [cx1_branch]
    unfold explainedDeduction nextPruningEvent scanDatabase scanPropagators
      frameViewedB frameLiveB frameState Frame.domains
    rfl
  have ht : terminalResult cxOrig cxOriginal cxProps cx1.branch = .stable cx1.branch := by
    rw [cx1_branch]
    unfold terminalResult nextPruningEvent scanDatabase scanPropagators
      frameViewedB frameLiveB frameState Frame.domains
    rfl
  rw [C2d.schedulerNext_eq_stable_decide rfl rfl hd ht rfl rfl rfl]
  rfl

/-- STEP 2: the complete child fails the leaf and has no split data — the
local-exclusion arm. -/
theorem cx_step2 : (schedulerNext cx2).successor = some cx3 := by
  have hd : explainedDeduction cxOriginal cxProps cx2.branch = none := by
    unfold explainedDeduction nextPruningEvent scanDatabase scanPropagators
      frameViewedB frameLiveB frameState Frame.domains
    rfl
  have ht : terminalResult cxOrig cxOriginal cxProps cx2.branch = .stable cx2.branch := by
    unfold terminalResult nextPruningEvent scanDatabase scanPropagators
      frameViewedB frameLiveB frameState Frame.domains
    rfl
  rw [C2d.schedulerNext_eq_stable_localExclude rfl rfl hd ht rfl rfl]
  rfl

/-- STEP 3: the dead branch consumes the coverless sibling. -/
theorem cx_step3 : (schedulerNext cx3).successor = some cx4 := by
  rw [C2d.schedulerNext_eq_consume_some rfl rfl cx4_consume]
  rfl

/-- STEP 4: the coverless frame records the propagator conflict at
level 1 — the recording arm fires. -/
theorem cx_step4 : (schedulerNext cx4).successor = some cx5 := by
  have hd : explainedDeduction cxOriginal cxProps cx4.branch = none := by
    unfold explainedDeduction nextPruningEvent scanDatabase scanPropagators
      frameViewedB frameLiveB frameState Frame.domains
    rfl
  have ht : terminalResult cxOrig cxOriginal cxProps cx4.branch =
      .conflict cx4.branch [cxClause] [] := by
    unfold terminalResult nextPruningEvent scanDatabase scanPropagators
      frameViewedB frameLiveB frameState Frame.domains
    rfl
  rw [C2d.schedulerNext_eq_conflict_analyze rfl rfl hd ht (by
    rw [show cx4.branch.level = 1 from rfl]
    omega)]
  rfl

/-! ### §2.2 The refutation -/

/-- The witness run is a genuine supported execution. -/
theorem cx_reach : SupportedReach cxOrig cxOriginal cxProps cx5 :=
  .step (.step (.step (.step (.step (.init (fun _ _ _ ha => by simp [cxLeaf] at ha))
    cx_step0) cx_step1) cx_step2) cx_step3) cx_step4

/-- The final configuration carries recorded evidence. -/
theorem cx5_conflict : ∃ ev : ConflictEvidence, cx5.conflict = some ev :=
  ⟨_, rfl⟩

theorem cx5_frame : cx5.branch.frame =
    ⟨[Dom.ofList [Value.int 0], Dom.ofList [Value.int 2, Value.int 3],
      Dom.empty], [0]⟩ := rfl

/-- The final configuration's frame is coverless. -/
theorem cx5_coverless : ¬ (∃ a : Assignment, FrameCovers cx5.branch.frame a) := by
  have hmem : Dom.empty ∈ cx5.branch.frame.doms := by
    rw [cx5_frame]
    simp
  exact coverless_not_inhabited ⟨Dom.empty, hmem, Dom.enum_empty⟩

/-- **THE RECORDED-SITE FAMILY IS FALSE FOR THE UNIT KIT** (the exact
family shape the I1 assembly carries as `hinhab`, with the unit-kit
premises): on the witness box there is a supported run reaching recorded
evidence at a coverless frame. -/
theorem cx5_false_family :
    ¬ (∀ {dcs : List DomConstraint}, (∀ dc ∈ dcs, unitFamilyB dc = true) →
        ∀ {cfg : SchedulerConfig cxLeaf},
          SupportedReach cxOrig cxOriginal (dcs.filterMap propagatorOfProved) cfg →
        ∀ {ev : ConflictEvidence}, cfg.conflict = some ev →
          ∃ a : Assignment, FrameCovers cfg.branch.frame a) := by
  intro hall
  obtain ⟨ev, hev⟩ := cx5_conflict
  exact cx5_coverless (hall (dcs := cxDcs) cxDcs_unitFamily cx_reach hev)

/-- **THE RECORDED-SITE FAMILY IS FALSE, EXACT CONSUMER SHAPE**: at the
witness triple (`orig = cxOrig`, `original = cxOriginal`, `props = cxProps`, the
kit premises of `cx5_false_family` discharged), the recorded-site
`hinhab` family — precisely the shape `SupportedInstance.hinhab`
instantiates with a site's recorded evidence — is refuted. -/
theorem recordedInhabited_false :
    ¬ (∀ {cfg : SchedulerConfig cxLeaf},
        SupportedReach cxOrig cxOriginal cxProps cfg →
          ∀ {ev : ConflictEvidence}, cfg.conflict = some ev →
            ∃ a : Assignment, FrameCovers cfg.branch.frame a) := by
  intro hall
  obtain ⟨ev, hev⟩ := cx5_conflict
  exact cx5_coverless (hall cx_reach hev)

/-- The refutation in existential form: SOME unit-kit instance
(`orig` + constraint list + leaf, with the kit premises) admits a
supported recorded site whose frame is coverless. -/
theorem cx5_refuted_existential :
    ∃ (orig : List Domain) (dcs : List DomConstraint)
      (leaf : Assignment → Bool),
      (∀ dc ∈ dcs, unitFamilyB dc = true) ∧
        ∃ cfg : SchedulerConfig leaf,
          SupportedReach orig cxOriginal (dcs.filterMap propagatorOfProved) cfg ∧
            ∃ ev : ConflictEvidence, cfg.conflict = some ev ∧
              ¬ (∃ a : Assignment, FrameCovers cfg.branch.frame a) := by
  obtain ⟨ev, hev⟩ := cx5_conflict
  exact ⟨cxOrig, cxDcs, cxLeaf, cxDcs_unitFamily, cx5, cx_reach, ev, hev,
    cx5_coverless⟩

/-- The counterexample's coverless frame carries the EMPTY original slot 2
(`⟨[[0],[2,3],[]],[0]⟩`) — the C2a empty-domain shape, re-keyed to the
sparse frame. -/
theorem cxCoverless_emptySlot :
    ∃ d ∈ cx5.branch.frame.doms, Dom.enum d = [] := by
  have hmem : Dom.empty ∈ cx5.branch.frame.doms := by
    rw [cx5_frame]
    simp
  exact ⟨Dom.empty, hmem, Dom.enum_empty⟩

/-- The counterexample's recording clause is the stored database clause
`[posLe 1 0, negNe 1 0]`, i.e. the kit-free database conflict channel. -/
theorem cx_recorded_clause :
    ∀ {ev : ConflictEvidence}, cx5.conflict = some ev →
      ev.clause = cxClause := by
  intro ev hev
  exact (stepAnalyzeConflictCounted_evidence hev).1

/-- The counterexample's coverless frame's own empty read: slot 2 reads
`[]`. -/
theorem cx_empty_read :
    Dom.enum ((Frame.domains cx5.branch.frame).getD 2 Dom.empty) = [] := rfl

/-! ## §3 The kit-free structural classification of the recording arm

Every recorded site comes from ONE structural channel (no kit
hypotheses): a registered propagator's genuine NONEMPTY conflict on the
site's own frame, with the database scan stable and the frame
int-viewed. The database's own (empty-payload) conflict route never
records, and neither does an implied event — so the coverless recorded
site (when it exists, as §1 shows for the unit kit) happens EXACTLY when
the propagator scan reports a nonempty conflict at a coverless frame.
This is the exact shape of `hinhab`'s residual. -/

/-- R1c: the ROUTED recording sources. Conflict routing records, besides
the propagator conflict, (i) a falsified stored clause (the clause itself),
(ii) the reason of an implied literal the frame filter rejects, and (iii) the
wipe-out clause of an emptied domain. -/
def RoutedRecordedSite (orig : List Domain) (original : List Clause)
    (props : List Propagator) (bs : BranchState leaf) (ev : ConflictEvidence) : Prop :=
  (∃ c ∈ bs.learned, scanDatabase original bs.frame bs.learned = .conflict [c] ∧
      ev.clause = c) ∨
    (∃ (l : Literal) (c : Clause) (lr fl : Bool),
      nextPruningEvent original props bs.frame bs.learned = .implied l c lr fl ∧
        filterFrame l bs.frame = none ∧ ev.clause = c) ∨
    (∃ w : Clause, nextPruningEvent original props bs.frame bs.learned = .stable ∧
      wipeoutClause orig bs.trail bs.frame = some w ∧ ev.clause = w)

/-- A recorded successor of an evidence-free predecessor is the recording
site of EITHER a nonempty propagator conflict on the predecessor's own branch
(with the database scan stable) OR (R1c) one of the routed sources; in both
cases the branch is untouched by the recording. (Restated: before conflict
routing only the first alternative existed.) -/
theorem recordedStep_is_propagatorConflict {leaf : Assignment → Bool}
    {cfg cfg' : SchedulerConfig leaf} {t : SchedulerTransition leaf}
    {ev : ConflictEvidence}
    (hc : cfg.conflict = none) (hnext : schedulerNext cfg = t)
    (hsucc : t.successor = some cfg') (hconf : cfg'.conflict = some ev) :
    (∃ (p : Propagator) (_ : p ∈ cfg.props) (q : Clause),
      q ≠ [] ∧ p.run (frameState cfg.branch.frame) = .conflict q ∧
        scanDatabase cfg.original cfg.branch.frame cfg.branch.learned = .stable ∧
        frameViewedB cfg.branch.frame = true ∧
        ev.clause = q ∧ cfg'.branch = cfg.branch) ∨
    (RoutedRecordedSite cfg.orig cfg.original cfg.props cfg.branch ev ∧
      cfg'.branch = cfg.branch) := by
  rcases schedulerNext_successor_recording_or_none hc hnext hsucc with
    hnone | ⟨cs, learned, c, rest, htr, hcs, hcfg'⟩
  · rw [hnone] at hconf
    cases hconf
  · rw [hcfg'] at hconf
    have hclause : ev.clause = c := (stepAnalyzeConflictCounted_evidence hconf).1
    have hbranch : cfg'.branch = cfg.branch := by
      rw [hcfg', stepAnalyzeConflictCounted_branch]
    rw [hcs] at htr
    obtain ⟨-, hcase⟩ := terminalResult_conflict_cases htr
    rcases hcase with ⟨hevnt, -⟩ | ⟨l, c', lr, fl, hevnt, hf, hcs', -⟩ |
        ⟨w, hevnt, hw, hcs', -⟩
    · rcases nextPruningEvent_conflict_cases hevnt with hdb | ⟨hsd, hview, hprop⟩
      · -- the database's own conflict: the stored clause is reported
        obtain ⟨d, hd, -, hcd⟩ := scanDatabase_conflict_facts hdb
        injection hcd with hcd' hrest
        exact Or.inr ⟨Or.inl ⟨d, hd, by rw [← hcd', ← hrest]; exact hdb, by rw [hclause, hcd']⟩, hbranch⟩
      · obtain ⟨p, hp, q, hrun, hpayload⟩ := scanPropagators_conflict_facts hprop
        have hqne : q ≠ [] := by
          intro hq
          rw [hq] at hpayload
          cases hpayload
        have hqisEmpty : q.isEmpty = false := by
          cases q with
          | nil => exact (hqne rfl).elim
          | cons a t => rfl
        have hcsq : c :: rest = [q] := by
          rw [hqisEmpty] at hpayload
          simpa using hpayload
        have hcq : c = q := by
          cases hcsq
          rfl
        have hclause' : ev.clause = q := by
          rw [← hcq]
          exact hclause
        exact Or.inl ⟨p, hp, q, hqne, hrun, hsd, hview, hclause', hbranch⟩
    · injection hcs' with hcc' hrest
      exact Or.inr ⟨Or.inr (Or.inl ⟨l, c', lr, fl, hevnt, hf, by rw [hclause, hcc']⟩),
        hbranch⟩
    · injection hcs' with hcw hrest
      exact Or.inr ⟨Or.inr (Or.inr ⟨w, hevnt, hw, by rw [hclause, hcw]⟩), hbranch⟩

/-- **THE HONEST RECORDED-SITE FORM (kit-free, one step)**: at every
supported successor carrying recorded evidence, either the frame is
inhabited, or the recorded clause is a genuine nonempty propagator
conflict on the site's own frame (database scan stable, frame int-viewed),
or (R1c) the site is one of the routed sources. -/
theorem supportedRecorded_or_propagatorConflict_step {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {cfg cfg' : SchedulerConfig leaf}
    {ev : ConflictEvidence}
    (hrec : SupportedReach orig original props cfg)
    (hs : (schedulerNext cfg).successor = some cfg')
    (hconf : cfg'.conflict = some ev) :
    (∃ a : Assignment, FrameCovers cfg'.branch.frame a) ∨
      (∃ (p : Propagator) (_ : p ∈ props) (q : Clause),
        q ≠ [] ∧ p.run (frameState cfg'.branch.frame) = .conflict q ∧
          ev.clause = q ∧
          scanDatabase original cfg'.branch.frame cfg'.branch.learned = .stable ∧
          frameViewedB cfg'.branch.frame = true) ∨
      RoutedRecordedSite orig original props cfg'.branch ev := by
  cases hcf : cfg.conflict with
  | some ev₀ =>
      have hnext : schedulerNext cfg = backjumpStep cfg ev₀ := by
        simp only [schedulerNext, hcf]
      rw [hnext] at hs
      have hnone := backjumpStep_successor_conflict_none hs
      rw [hnone] at hconf
      cases hconf
  | none =>
      rcases recordedStep_is_propagatorConflict hcf rfl hs hconf with
        ⟨p, hp, q, hqne, hrun, hsd, hview, hclause, hbr⟩ | ⟨hrt, hbr⟩
      · rw [SupportedReach.props_eq hrec] at hp
        rw [SupportedReach.original_eq hrec] at hsd
        rw [hbr]
        exact Or.inr (Or.inl ⟨p, hp, q, hqne, hrun, hclause, hsd, hview⟩)
      · rw [hbr, ← SupportedReach.orig_eq hrec, ← SupportedReach.original_eq hrec,
          ← SupportedReach.props_eq hrec]
        exact Or.inr (Or.inr hrt)

/-- **THE HONEST RECORDED-SITE FORM (kit-free, run level)**: at every
supported configuration carrying recorded evidence, either the frame is
inhabited, or the recorded clause is a genuine nonempty propagator
conflict on the site's own frame (database scan stable, frame int-viewed),
or (R1c) the site is one of the routed sources. The coverless case of the
second alternative is REALIZED by §1-§2 on the unit kit. -/
theorem supportedRecorded_or_propagatorConflict {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ∀ {ev : ConflictEvidence}, cfg.conflict = some ev →
        (∃ a : Assignment, FrameCovers cfg.branch.frame a) ∨
          (∃ (p : Propagator) (_ : p ∈ props) (q : Clause),
            q ≠ [] ∧ p.run (frameState cfg.branch.frame) = .conflict q ∧
              ev.clause = q ∧
              scanDatabase original cfg.branch.frame cfg.branch.learned = .stable ∧
              frameViewedB cfg.branch.frame = true) ∨
          RoutedRecordedSite orig original props cfg.branch ev := by
  intro cfg hreach
  induction hreach with
  | init _ =>
      intro ev hconf
      simp [SchedulerConfig.init] at hconf
  | step hrec hs ih =>
      intro ev hconf
      exact supportedRecorded_or_propagatorConflict_step hrec hs hconf

/-- **THE UNIT-KIT RECORDED-SITE FORM, with the conflicting constraint
named**: under the unit-kit premises, the recording propagator is the
proved-propagator image of a constraint OF THE PROBLEM — the exact handle
the per-family table of §4 classifies. (R1c: plus the routed alternative.) -/
theorem supportedRecorded_or_dcsConflict {orig : List Domain}
    {original : List Clause} {leaf : Assignment → Bool}
    {dcs : List DomConstraint} {props : List Propagator}
    (hprops : props = dcs.filterMap propagatorOfProved) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ∀ {ev : ConflictEvidence}, cfg.conflict = some ev →
        (∃ a : Assignment, FrameCovers cfg.branch.frame a) ∨
          (∃ (dc : DomConstraint) (_ : dc ∈ dcs) (p : Propagator) (q : Clause),
            propagatorOfProved dc = some p ∧ q ≠ [] ∧
              p.run (frameState cfg.branch.frame) = .conflict q ∧
              ev.clause = q ∧
              scanDatabase original cfg.branch.frame cfg.branch.learned = .stable ∧
              frameViewedB cfg.branch.frame = true) ∨
          RoutedRecordedSite orig original props cfg.branch ev := by
  intro cfg hreach ev hconf
  rcases supportedRecorded_or_propagatorConflict hreach hconf with
    hinhab | ⟨p, hp, q, hqne, hrun, hclause, hsd, hview⟩ | hrouted
  · exact Or.inl hinhab
  · rw [hprops] at hp
    obtain ⟨dc, hdc, hdcp⟩ := propagatorsOfProved_mem hp
    exact Or.inr (Or.inl ⟨dc, hdc, p, q, hdcp, hqne, hrun, hclause, hsd, hview⟩)
  · exact Or.inr (Or.inr hrouted)

/-! ## §4 The unit-family conflict shapes (the per-family split)

For the unit fragment, a propagator image's conflict has exactly the
family runner's shape. The five bound/equality families (`leConstHi`,
`leConstLo`, `ltConstHi`, `ltConstLo`, and `constEq` on INTEGER
constants) can only report a conflict when the read at the family's own
slot is NONEMPTY (`propLeConstHi_conflict_inv` … and their
`_no_conflict_empty_read` corollaries), while `constEq` on a BOOLEAN
constant reports the canonical unit `[posBool i b]` whenever the read
does not contain `.bool b` — in particular at the EMPTY read
(`propConstEq_bool_conflict_empty_read`). That Boolean channel is exactly
what the §1-§2 counterexample uses.

RESIDUAL (reported, not assumed): a coverless frame may still offer a
NONEMPTY read at a bound family's slot (the hole sits at another read
position), so these per-family shapes do not by themselves exclude the
five bound/equality families at recorded coverless sites; that exclusion
needs the "stable live predecessor agreement" argument of C2a §5 and is
NOT delivered. -/

/-- `leConstHi` conflict shape: the clause is the unit nogood and the
read at the family's own slot is nonempty with its minimum above `c`. -/
theorem propLeConstHi_conflict_inv {st : State} {i : Nat} {c : Int}
    {ng : Clause} (h : LeanFzn.Solver.Propagation.propLeConstHi st i c = .conflict ng) :
    ng = [posLe i c] ∧ ∃ mn mx,
      domMinI (st.domains.getD i Dom.empty) = some mn ∧
      domMaxI (st.domains.getD i Dom.empty) = some mx ∧ mn > c := by
  obtain ⟨mn, mx, hmn, hmx, hgt, hng⟩ := narrowHi_conflict_inv h
  exact ⟨hng, mn, mx, hmn, hmx, hgt⟩

/-- `leConstLo` conflict shape: nonempty read, maximum below `c`. -/
theorem propLeConstLo_conflict_inv {st : State} {i : Nat} {c : Int}
    {ng : Clause} (h : LeanFzn.Solver.Propagation.propLeConstLo st i c = .conflict ng) :
    ng = [negLe i (c - 1)] ∧ ∃ mn mx,
      domMinI (st.domains.getD i Dom.empty) = some mn ∧
      domMaxI (st.domains.getD i Dom.empty) = some mx ∧ mx < c := by
  obtain ⟨mn, mx, hmn, hmx, hlt, hng⟩ := narrowLo_conflict_inv h
  exact ⟨hng, mn, mx, hmn, hmx, hlt⟩

/-- `ltConstHi` conflict shape: nonempty read, minimum above `c - 1`. -/
theorem propLtConstHi_conflict_inv {st : State} {i : Nat} {c : Int}
    {ng : Clause} (h : LeanFzn.Solver.Propagation.propLtConstHi st i c = .conflict ng) :
    ng = [posLe i (c - 1)] ∧ ∃ mn mx,
      domMinI (st.domains.getD i Dom.empty) = some mn ∧
      domMaxI (st.domains.getD i Dom.empty) = some mx ∧ mn > c - 1 := by
  obtain ⟨mn, mx, hmn, hmx, hgt, hng⟩ := narrowHi_conflict_inv h
  exact ⟨hng, mn, mx, hmn, hmx, hgt⟩

/-- `ltConstLo` conflict shape: nonempty read, maximum below `c + 1`. -/
theorem propLtConstLo_conflict_inv {st : State} {i : Nat} {c : Int}
    {ng : Clause} (h : LeanFzn.Solver.Propagation.propLtConstLo st i c = .conflict ng) :
    ng = [negLe i c] ∧ ∃ mn mx,
      domMinI (st.domains.getD i Dom.empty) = some mn ∧
      domMaxI (st.domains.getD i Dom.empty) = some mx ∧ mx < c + 1 := by
  obtain ⟨mn, mx, hmn, hmx, hlt, hng⟩ := narrowLo_conflict_inv h
  exact ⟨hng, mn, mx, hmn, hmx, hlt⟩

/-- `constEq` (integer constant) conflict shape: nonempty read, one of the
two bound facts violated. -/
theorem propConstEq_int_conflict_inv {st : State} {i : Nat} {k : Int}
    {ng : Clause} (h : LeanFzn.Solver.Propagation.propConstEq st i (.int k) = .conflict ng) :
    ∃ mn mx, domMinI (st.domains.getD i Dom.empty) = some mn ∧
      domMaxI (st.domains.getD i Dom.empty) = some mx ∧ (mn > k ∨ mx < k) := by
  have hfe : firstEvent [narrowHi st i k [posLe i k],
      narrowLo st i k [negLe i (k - 1)]] = .conflict ng := h
  rcases firstEvent_mem _ _ hfe with hstab | hmem
  · cases hstab
  · rcases List.mem_cons.mp hmem with hnh | hnl
    · obtain ⟨mn, mx, hmn, hmx, hgt, -⟩ := narrowHi_conflict_inv hnh.symm
      exact ⟨mn, mx, hmn, hmx, Or.inl hgt⟩
    · rw [List.mem_singleton] at hnl
      obtain ⟨mn, mx, hmn, hmx, hlt, -⟩ := narrowLo_conflict_inv hnl.symm
      exact ⟨mn, mx, hmn, hmx, Or.inr hlt⟩

/-- `constEq` (Boolean constant) at an EMPTY read: the conflict fires with
the canonical unit clause `[posBool i b]` — the §1 counterexample's
mechanism, kernel-verified. -/
theorem propConstEq_bool_conflict_empty_read {st : State} {i : Nat} {b : Bool}
    (hemp : Dom.enum (st.domains.getD i Dom.empty) = []) :
    LeanFzn.Solver.Propagation.propConstEq st i (.bool b) = .conflict [posBool i b] := by
  unfold LeanFzn.Solver.Propagation.propConstEq
  rw [hemp]
  rfl

/-- No `leConstHi` conflict can fire on an empty read. -/
theorem propLeConstHi_no_conflict_empty_read {st : State} {i : Nat} {c : Int}
    (hemp : Dom.enum (st.domains.getD i Dom.empty) = []) :
    ∀ ng, LeanFzn.Solver.Propagation.propLeConstHi st i c ≠ .conflict ng := by
  intro ng h
  obtain ⟨-, mn, mx, hmn, -, -⟩ := propLeConstHi_conflict_inv h
  have hemp' : Dom.enum ((st.domains[i]?).getD Dom.empty) = [] := by
    simpa only [List.getD_eq_getElem?_getD] using hemp
  have hnone : domMinI (st.domains.getD i Dom.empty) = none := by
    simp [domMinI, domInts, List.getD_eq_getElem?_getD, hemp']
  rw [hnone] at hmn
  cases hmn

/-- No `leConstLo` conflict can fire on an empty read. -/
theorem propLeConstLo_no_conflict_empty_read {st : State} {i : Nat} {c : Int}
    (hemp : Dom.enum (st.domains.getD i Dom.empty) = []) :
    ∀ ng, LeanFzn.Solver.Propagation.propLeConstLo st i c ≠ .conflict ng := by
  intro ng h
  obtain ⟨-, mn, mx, -, hmx, -⟩ := propLeConstLo_conflict_inv h
  have hemp' : Dom.enum ((st.domains[i]?).getD Dom.empty) = [] := by
    simpa only [List.getD_eq_getElem?_getD] using hemp
  have hnone : domMaxI (st.domains.getD i Dom.empty) = none := by
    simp [domMaxI, domInts, List.getD_eq_getElem?_getD, hemp']
  rw [hnone] at hmx
  cases hmx

/-- No `ltConstHi` conflict can fire on an empty read. -/
theorem propLtConstHi_no_conflict_empty_read {st : State} {i : Nat} {c : Int}
    (hemp : Dom.enum (st.domains.getD i Dom.empty) = []) :
    ∀ ng, LeanFzn.Solver.Propagation.propLtConstHi st i c ≠ .conflict ng := by
  intro ng h
  obtain ⟨-, mn, mx, hmn, -, -⟩ := propLtConstHi_conflict_inv h
  have hemp' : Dom.enum ((st.domains[i]?).getD Dom.empty) = [] := by
    simpa only [List.getD_eq_getElem?_getD] using hemp
  have hnone : domMinI (st.domains.getD i Dom.empty) = none := by
    simp [domMinI, domInts, List.getD_eq_getElem?_getD, hemp']
  rw [hnone] at hmn
  cases hmn

/-- No `ltConstLo` conflict can fire on an empty read. -/
theorem propLtConstLo_no_conflict_empty_read {st : State} {i : Nat} {c : Int}
    (hemp : Dom.enum (st.domains.getD i Dom.empty) = []) :
    ∀ ng, LeanFzn.Solver.Propagation.propLtConstLo st i c ≠ .conflict ng := by
  intro ng h
  obtain ⟨-, mn, mx, -, hmx, -⟩ := propLtConstLo_conflict_inv h
  have hemp' : Dom.enum ((st.domains[i]?).getD Dom.empty) = [] := by
    simpa only [List.getD_eq_getElem?_getD] using hemp
  have hnone : domMaxI (st.domains.getD i Dom.empty) = none := by
    simp [domMaxI, domInts, List.getD_eq_getElem?_getD, hemp']
  rw [hnone] at hmx
  cases hmx

/-- No `constEq` (integer constant) conflict can fire on an empty read. -/
theorem propConstEq_int_no_conflict_empty_read {st : State} {i : Nat} {k : Int}
    (hemp : Dom.enum (st.domains.getD i Dom.empty) = []) :
    ∀ ng, LeanFzn.Solver.Propagation.propConstEq st i (.int k) ≠ .conflict ng := by
  intro ng h
  obtain ⟨mn, mx, hmn, -, -⟩ := propConstEq_int_conflict_inv h
  have hemp' : Dom.enum ((st.domains[i]?).getD Dom.empty) = [] := by
    simpa only [List.getD_eq_getElem?_getD] using hemp
  have hnone : domMinI (st.domains.getD i Dom.empty) = none := by
    simp [domMinI, domInts, List.getD_eq_getElem?_getD, hemp']
  rw [hnone] at hmn
  cases hmn

/-! ## §5 The honest replacement for `hinhab` (consumer shapes)

The exact provable replacements for the recorded-site `hinhab` family:

* `supportedRecorded_or_propagatorConflict` (§3) — every recorded site is
  inhabited OR a nonempty propagator conflict on its own (viewed,
  DB-stable) frame;
* C2a's `SiteInhabited.supportedRecordedInhabited_or_coverless` — every
  recorded site is inhabited OR coverless, with the coverless disjunct's
  deadness FREE (`coverless_hdead`, `coverless_branchRegion_sound`);
* §1-§2: the coverless-AND-recorded case is REALIZED on the unit kit, so
  no consumer may assume it away without the residual argument of C2a §5.

The concrete residual obligation (for the coordinator / I1 / J1):
`∀ dc ∈ dcs, unitFamilyB dc = true` must be STRENGTHENED (e.g. exclude
`.constEq _ (.bool _)`, or carry a per-site liveness premise
`frameLiveB cfg.branch.frame = true` produced by the J1-side covers
machinery), or the coverless case must be handled on its own: the
recorded analysis at a coverless site has no covering assignment, so the
trail-agreement contradiction `supportedHfresh_of_site` builds is
vacuous there — the honest routes are the empty-frame local-exclusion
registration or a fresh liveness producer, NOT inhabitedness.

HARNESS EVIDENCE (exploration, NOT a proof): a computable simulation of
the deterministic dispatcher (~1.6M steps; boolEq-free unit kits — the
five bound/equality families with integer constants, slots 0/1, boxes
with holes at any position, constraint lists of size 1-3, two leaves)
found ZERO recorded-coverless sites, while the same harness reproduces
the §1 witness (`eqB1_true` on `[[false, true], [true]]`) as soon as a
`constEq _ (.bool _)` is present. So the recommended consumer-side
strengthening is "exclude Boolean-constant equality from the unit kit",
which the exploration supports but does NOT prove. -/

end LeanFzn.Solver.UIP

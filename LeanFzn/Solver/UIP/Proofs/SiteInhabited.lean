/-
File: LeanFzn/Solver/UIP/Proofs/SiteInhabited.lean
inhabitedness, its refutation, and the empty-frame route)

Purpose: discharge (PLAN.md C2, "C2a") the frame-inhabitedness obligation

    hinhab : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ∃ a : Assignment,
        FrameCovers cfg.branch.frame a

that `SupportedInstance.supportedHpre_unitKit_of_site` (I1-A) currently
carries as a residual and that `HdeadCkpt.supportedHfresh_of_site` and
`ScanStability.databaseUnfalsified_of_reachable_recorded` consume at
recorded-evidence sites (`cfg.conflict = some ev`).

## FINDING 1 — the quoted ALL-SITES family is FALSE (kernel-checked)

`FrameCovers` is inhabited exactly when every remaining domain of the
frame is nonempty (`exists_frameCovers_iff`). The all-sites family above
asserts this at EVERY supported configuration. It is REFUTED, on a
genuine unit-kit instance, by §2 below:

* `cexNotAllSites` — `¬ (∀ {cfg}, SupportedReach cexOrig [] [cexProp] cfg →
  ∃ a, FrameCovers cfg.branch.frame a)`.

The witness run takes the single-slot box `[[0, 1]]` with the single
registered unit-family propagator `propagatorOfProved (.leConstHi 0 0)`
(`unitFamilyB (.leConstHi 0 0) = true`, `cexProp_image`) and the empty
clause base. The propagator narrows slot 0 to the singleton `{0}` (a
recorded deduction, `learned = [[posLe 0 0]]`), the fresh-pin guard then
takes the PLAIN `stepDecide` arm (the pin `negNe 0 0` is not the recorded
`posLe 0 0`), whose SIBLING frame is `([[]], [])` — the split slot's
leftover domain is `[]`. Consuming that sibling (a real
`schedulerNext`-successor, `stepConsume`) yields a `SupportedReach`
configuration whose frame is COVERLESS: no assignment covers it. The
mechanism is exactly the B2/`Frontier` documentation: a split of a
singleton head pushes a coverless sibling, and the guard's
`stepDecideSkip` arm does NOT apply because the narrowing literal and the
value pin are different literals. Note the instance is fully supported —
typed/int-viewed box, nonempty domains, a genuine `propagatorOfProved`
image, `original = []` — so the refutation is not an artifact of an
unsupported box.

`cexNotAllSites_emptyOrig` records the degenerate twin at `orig = [[]]`
(the `SupportedReach.init` configuration is coverless before any step).

## FINDING 2 — the honest replacement: site-classified inhabitedness

The exact, premise-free split that remains provable is
`frameLiveB cfg.branch.frame` (the runtime's liveness gate, definitionally
`∀ d ∈ f.1, d ≠ []`):

* `frameInhabited_iff_live` — `(∃ a, FrameCovers f a) ↔ frameLiveB f = true`
  (composing the landed `exists_frameCovers_iff`);
* `supportedInhabited_or_coverless` — at EVERY supported configuration,
  `(∃ a, FrameCovers cfg.branch.frame a) ∨ (∃ d ∈ cfg.branch.frame.1, d = [])`,
  with no run input and no side condition;
* `frameCovers_of_live` / `supportedInhabited_of_live` — the LIVE class
  producer (`hinhab` restricted to `frameLiveB = true` sites, empty
  premise);
* `supportedInhabited_of_liveSites` — the family shape in which the
  consumer supplies liveness per site.

## FINDING 3 — the empty-frame route is already PROVED, and it is free

The second disjunct needs no semantic input at all:

* `coverless_hdead` — at a coverless frame EVERY deadness predicate
  `∀ a, leaf a = true → FrameCovers f a → False` is free
  (`not_frameCovers_of_empty_domain` consumes no leaf fact);
* `coverless_branchRegion_sound` — the runtime's registered region at a
  coverless site, `branchRegion cfg = DeadRegion.byFrame cfg.branch.frame`
  (`SchedulerStep.lean`), is SOUND by the landed
  `emptyFrame_byFrame_sound` (i.e. `DeadRegion.byFrame_sound`), which is
  exactly the route `arm_localExclude_log_sound` consumes at local
  exclusion sites. Hence the coverless branch of the disjunction is
  closed by the PROVED local-exclusion route, never by `hinhab`.

So `hinhab` cannot be delivered as quoted; the exact honest replacement
(documented for the I1-A/coordinator re-pointing) is the disjunction, with
the coverless disjunct routed by §4. The remaining semantic content — "the
recorded site (`cfg.conflict = some ev`) whose frame is coverless does not
arise, or its `hfresh` obligation is discharged on its own" — is a
UNIT-KIT propagator analysis that is NOT delivered here (see the module
footer for the exact residual statement and the reachability argument
sketch that motivates it).

NO `sorry`, NO custom axiom. Registration owes the umbrella import line
`LeanFzn.Solver.UIP.Proofs.SiteInhabited` in `LeanFzn.Solver/LeanFzn.Solver.UIP.lean` (coordinator).
-/

import LeanFzn.Solver.UIP.Proofs.LearnedExplanation
import LeanFzn.Solver.Propagation.Proofs.Propagators
import LeanFzn.Solver.UIP.Proofs.Scheduler
import LeanFzn.Solver.UIP.Proofs.SchedulerStep
import LeanFzn.Solver.UIP.Proofs.SupportedRun
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 Frame inhabitedness ⇔ liveness (the exact classification)

`frameLiveB` (`Pruning.lean`) is the runtime's liveness gate: `.all` over
the remaining domains of `!d.isEmpty`. The landed characterization
`exists_frameCovers_iff` says a frame is covered by some complete
assignment exactly when all its remaining domains are nonempty, so the
two notions coincide — and `frameLiveB` is a COMPUTABLE Bool, which is
what makes the disjunction of §3 decidable and premise-free. -/

/-- The liveness gate in the `∀ d ∈ f.1, d ≠ []` form. -/
theorem frameLiveB_eq_true_iff_ne_nil {f : BranchFrame} :
    frameLiveB f = true ↔ ∀ d ∈ f.1, d ≠ [] := by
  unfold frameLiveB
  rw [List.all_eq_true]
  constructor
  · intro h d hd hnil
    have h' : (!d.isEmpty) = true := h d hd
    rw [hnil] at h'
    exact absurd h' (by decide)
  · intro h d hd
    cases d with
    | nil => exact absurd rfl (h [] hd)
    | cons v vs => rfl

/-- **THE EXACT INHABITATION CHARACTERIZATION, COMPUTABLE FORM**: a frame
covers a complete assignment iff its liveness gate is true. This is
`exists_frameCovers_iff` re-keyed to the runtime's own Bool. -/
theorem frameInhabited_iff_live {f : BranchFrame} :
    (∃ a : Assignment, FrameCovers f a) ↔ frameLiveB f = true :=
  exists_frameCovers_iff.trans frameLiveB_eq_true_iff_ne_nil.symm

/-- The LIVE producer: a frame whose remaining domains are all nonempty is
covered by some complete assignment. -/
theorem frameCovers_of_live {f : BranchFrame} (h : frameLiveB f = true) :
    ∃ a : Assignment, FrameCovers f a :=
  frameInhabited_iff_live.mpr h

/-- The COVERLESS producer: a frame with an empty remaining domain covers
nothing. (Cites the landed `not_frameCovers_of_empty_domain`.) -/
theorem not_frameCovers_of_coverless {f : BranchFrame} {a : Assignment}
    (h : ∃ d ∈ f.1, d = []) : ¬ FrameCovers f a :=
  not_frameCovers_of_empty_domain h

/-- **THE PREMISE-FREE CLASSIFICATION**: every frame is either inhabited
or coverless. No run hypothesis, no side condition — the disjunction is
the honest replacement for the all-sites `hinhab` family (which §2
refutes). -/
theorem frameCovers_or_coverless (f : BranchFrame) :
    (∃ a : Assignment, FrameCovers f a) ∨ (∃ d ∈ f.1, d = []) := by
  by_cases h : ∃ d ∈ f.1, d = []
  · exact Or.inr h
  · exact Or.inl (frameCovers_of_live (frameLiveB_eq_true_iff_ne_nil.mpr
      (fun d hd hnil => h ⟨d, hd, hnil⟩)))

/-- The coverless case has NO inhabited frame: the negation is total (no
`leaf` input, no coherence input). -/
theorem coverless_not_inhabited {f : BranchFrame} (h : ∃ d ∈ f.1, d = []) :
    ¬ ∃ a : Assignment, FrameCovers f a :=
  fun ⟨_, hcov⟩ => not_frameCovers_of_empty_domain h hcov

/-! ## §2 The kernel-checked refutation of the ALL-SITES family

The witness run: box `[[0]]`, clause base `[]`, the single registered
unit-family propagator `propagatorOfProved (.leConstHi 0 0)` (already
satisfied by the box, so no deduction is productive), leaf `fun _ => false`.
(R1d: the earlier box `[[0, 1]]` is no longer a witness — the synchronised
frame/trail records the fixing literal after the propagation, so the
singleton is trail-redundant and never split; the singleton box splits at
the ROOT, before any synchronisation.) Three real `schedulerNext`
successors:

  1. `decide`    — the guarded dispatch's FRESH arm (`negNe 0 0` is not
     recorded), splitting the singleton `{0}`: child `([], [0])`, sibling
     `([[]], [])` — the sibling's remaining head is the EMPTY leftover;
  2. `localExclude (stable site)` — the child is a complete frame failing
     the leaf, `splitData = none`;
  3. `chronologicalFallback (consume)` — the coverless sibling becomes the
     branch frame.

The final configuration is a genuine `SupportedReach` configuration whose
frame is coverless, which refutes the all-sites family. -/

def cexOrig : List Domain := [([Value.int 0] : Domain)]

def cexLeaf : Assignment → Bool := fun _ => false

def cexProp : Propagator := { watches := [.intLe 0 0], run := fun st => LeanFzn.Solver.Propagation.propLeConstHi st 0 0 }

def cexCfg0 : SchedulerConfig cexLeaf :=
  SchedulerConfig.init cexOrig [] [cexProp]

def cexF1 : BranchFrame := ([[Value.int 0]], ([] : Assignment))

def cexF2 : BranchFrame := ([], [Value.int 0])

/-- The instance's propagator is the genuine `propagatorOfProved` image of
the unit-family constraint `leConstHi 0 0`. -/
theorem cexProp_image : propagatorOfProved (.leConstHi 0 0) = some cexProp := rfl

/-- The instance's constraint is in the unit fragment. -/
theorem cexProp_unitFamily : unitFamilyB (.leConstHi 0 0) = true := rfl

/-- The first state is the supported initializer of the witness triple. -/
theorem cexCfg0_eq :
    cexCfg0 = SchedulerConfig.init (leaf := cexLeaf) cexOrig [] [cexProp] := rfl

/-- The root branch (the supported initializer of the witness triple). -/
def cexBs1 : BranchState cexLeaf :=
  { frame := cexF1, trail := [], level := 0, learned := [] }

/-- Step 1's post-state branch (the pinned child frame and the decision
entry at level 1). -/
def cexBs2 : BranchState cexLeaf :=
  { frame := cexF2,
    trail := [{ literal := negNe 0 0, level := 1, reason := none }],
    level := 1, learned := [] }

/-- **THE WITNESS RUN**: a supported (unit-kit image) run reaching a
configuration with a COVERLESS branch frame. -/
theorem cexNotAllSites :
    ¬ (∀ {cfg : SchedulerConfig cexLeaf},
      SupportedReach cexOrig [] [cexProp] cfg →
        ∃ a : Assignment, FrameCovers cfg.branch.frame a) := by
  intro hall
  let cfg1 : SchedulerConfig cexLeaf := cexCfg0
  have hb1 : cfg1.branch = cexBs1 := rfl
  -- STEP 1: the stable fixpoint's FRESH decide on the singleton head {0}
  have hd1 : explainedDeduction [] [cexProp] cfg1.branch = none := by
    rw [hb1]
    unfold explainedDeduction
    rfl
  have ht1 : terminalResult cexOrig [] [cexProp] cfg1.branch = .stable cfg1.branch := by
    rw [hb1]
    unfold terminalResult
    rfl
  have hw1 : leafWitness cexLeaf cfg1 = none := by
    unfold leafWitness
    rw [hb1]
    rfl
  have hs1 : splitData cfg1.branch.frame = some (negNe 0 0, Value.int 0, [], []) := by
    rw [hb1]
    rfl
  have hr1 : TrailRedundant cfg1.branch.trail (negNe 0 0) = false := by
    rw [hb1]
    rfl
  let cfg2 : SchedulerConfig cexLeaf := stepDecide cfg1 (Value.int 0) [] [] (negNe 0 0)
  have hslot1a : (schedulerNext cfg1).successor = some cfg2 := by
    rw [show schedulerNext cfg1 = .decide cfg2 (negNe 0 0) from
      C2d.schedulerNext_eq_stable_decide rfl rfl hd1 ht1 hw1 hs1 hr1]
    rfl
  have hb2 : cfg2.branch = cexBs2 := by
    show { (cfg1.branch.decide (negNe 0 0)) with
      frame := ([], cfg1.branch.frame.2 ++ [Value.int 0]) } = cexBs2
    rw [hb1]
    rfl
  -- STEP 2: the complete child fails the leaf; splitData = none
  have hd2 : explainedDeduction [] [cexProp] cfg2.branch = none := by
    rw [hb2]
    unfold explainedDeduction
    rfl
  have ht2 : terminalResult cexOrig [] [cexProp] cfg2.branch = .stable cfg2.branch := by
    rw [hb2]
    unfold terminalResult
    rfl
  have hw2 : leafWitness cexLeaf cfg2 = none := by
    unfold leafWitness
    rw [hb2]
    rfl
  have hs2 : splitData cfg2.branch.frame = none := by
    rw [hb2]
    rfl
  let cfg3 : SchedulerConfig cexLeaf := stepLocalExclude cfg2 [] (branchRegion cfg2)
  have hslot2a : (schedulerNext cfg2).successor = some cfg3 := by
    rw [show schedulerNext cfg2 = .localExclude cfg3 from
      C2d.schedulerNext_eq_stable_localExclude rfl rfl hd2 ht2 hw2 hs2]
    rfl
  -- STEP 3: consuming the coverless sibling
  obtain ⟨cfg4, hcons4, hframe4⟩ :
      ∃ cfg4 : SchedulerConfig cexLeaf,
        stepConsume cfg3 = some cfg4 ∧
          cfg4.branch.frame = ([[]], cfg1.branch.frame.2) :=
    ⟨_, rfl, rfl⟩
  have hslot3a : (schedulerNext cfg3).successor = some cfg4 := by
    rw [show schedulerNext cfg3 = .chronologicalFallback cfg4 from
      C2d.schedulerNext_eq_consume_some rfl rfl hcons4]
    rfl
  -- the final configuration is supported and its frame is coverless
  have hreach4 : SupportedReach cexOrig [] [cexProp] cfg4 :=
    .step (.step (.step (.init (fun _ hc => absurd hc (List.not_mem_nil))) hslot1a) hslot2a) hslot3a
  have hcov4 : ¬ (∃ a : Assignment, FrameCovers cfg4.branch.frame a) := by
    rw [hframe4]
    exact coverless_not_inhabited ⟨[], List.mem_cons_self .., rfl⟩
  exact hcov4 (hall hreach4)

/-- The degenerate twin: the `SupportedReach.init` configuration of the
box `[[]]` is already coverless (no step needed). Recorded so the
refutation does not depend on the computed run above. -/
theorem cexNotAllSites_emptyOrig :
    ¬ (∀ {cfg : SchedulerConfig cexLeaf},
      SupportedReach [[]] [] [] cfg →
        ∃ a : Assignment, FrameCovers cfg.branch.frame a) := by
  intro hall
  have hreach : SupportedReach ([[]] : List Domain) [] []
      (SchedulerConfig.init (leaf := cexLeaf) [[]] [] []) :=
    .init (fun _ hc => absurd hc (List.not_mem_nil))
  have hcov : ¬ (∃ a : Assignment,
      FrameCovers (SchedulerConfig.init (leaf := cexLeaf) [[]] [] []).branch.frame a) :=
    coverless_not_inhabited ⟨[], List.mem_cons_self .., rfl⟩
  exact hcov (hall hreach)

/-! ## §3 The honest producers (the exact replacement shapes)

`hinhab` as quoted by I1-A cannot be delivered (§2). The premise-free
statements below are what remains, and they are the shapes the consumers
should take instead:

* `supportedInhabited_or_coverless` — the SITE-CLASSIFIED family: every
  supported configuration is inhabited OR coverless, with no run input;
* `supportedInhabited_of_liveSites` / `supportedInhabited_of_liveSite` —
  the LIVE-class family: the exact `hinhab` shape with the liveness
  premise supplied per site;
* `coverless_hdead` / `coverless_branchRegion_sound` (§4) — the coverless
  disjunct is closed by the PROVED local-exclusion route. -/

/-- **THE SITE-CLASSIFIED FAMILY (the honest replacement)**: at every
supported configuration — recorded-evidence site or not — the branch
frame is either inhabited or coverless. No premise beyond the run. -/
theorem supportedInhabited_or_coverless {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator} :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      (∃ a : Assignment, FrameCovers cfg.branch.frame a) ∨
        (∃ d ∈ cfg.branch.frame.1, d = []) :=
  fun _ => frameCovers_or_coverless _

/-- The same classification in the RECORDED-SITE shape (the shape at which
`HdeadCkpt.supportedHfresh_of_site` and
`ScanStability.databaseUnfalsified_of_reachable_recorded` consume
`hinhab`). -/
theorem supportedRecordedInhabited_or_coverless {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
    (_hreach : SupportedReach orig original props cfg) (_hconf : cfg.conflict = some ev) :
    (∃ a : Assignment, FrameCovers cfg.branch.frame a) ∨
      (∃ d ∈ cfg.branch.frame.1, d = []) :=
  frameCovers_or_coverless cfg.branch.frame

/-- **THE LIVE-SITE PRODUCER**: the exact `hinhab` conclusion at a site
whose frame is live (`frameLiveB = true`). Empty premise set beyond the
site's two facts. -/
theorem supportedInhabited_of_liveSite {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {cfg : SchedulerConfig leaf}
    (_hreach : SupportedReach orig original props cfg)
    (hlive : frameLiveB cfg.branch.frame = true) :
    ∃ a : Assignment, FrameCovers cfg.branch.frame a :=
  frameCovers_of_live hlive

/-- **THE LIVE-CLASS FAMILY**: the `hinhab` shape with the liveness
premise supplied per site by the consumer. -/
theorem supportedInhabited_of_liveSites {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    (hlive : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      frameLiveB cfg.branch.frame = true) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ∃ a : Assignment, FrameCovers cfg.branch.frame a :=
  fun hreach => frameCovers_of_live (hlive hreach)

/-! ## §4 The empty-frame route (already proved, and premise-free)

The second disjunct of §3 needs NO semantic input at all: a coverless
frame's deadness is immediate, its registered region (`branchRegion cfg`,
`SchedulerStep.lean`) is sound by the landed `DeadRegion.byFrame_sound`
(`emptyFrame_byFrame_sound`, `LearnedExplanation.lean`), which is exactly
what `arm_localExclude_log_sound` (`Proofs/SchedulerStep.lean`) consumes at
local-exclusion sites. -/

/-- At a coverless frame EVERY `hdead`-shaped obligation is free. -/
theorem coverless_hdead {leaf : Assignment → Bool} {f : BranchFrame}
    (h : ∃ d ∈ f.1, d = []) :
    ∀ a : Assignment, leaf a = true → FrameCovers f a → False :=
  fun _ _ hcov => not_frameCovers_of_empty_domain h hcov

/-- The runtime's registered region at a coverless site is SOUND
(`branchRegion cfg = DeadRegion.byFrame cfg.branch.frame` by `rfl`). -/
theorem coverless_branchRegion_sound {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} (h : ∃ d ∈ cfg.branch.frame.1, d = []) :
    DeadRegion.Sound leaf (branchRegion cfg) :=
  emptyFrame_byFrame_sound h

/-- A frame whose HEAD remaining domain is empty (the exact shape the
kernel counterexample `cexNotAllSites` reaches: `f.1 = [] :: _`) has NO
split data, so the guarded stable dispatch goes to the local-exclusion arm
(`schedulerNext_eq_stable_localExclude`) at its next active step — the
empty-frame route, with `coverless_hdead`/`coverless_branchRegion_sound`
supplying the deadness and the region soundness. -/
theorem splitData_eq_none_of_head_empty {f : BranchFrame} {t : List Domain}
    (h : f.1 = [] :: t) : splitData f = none := by
  obtain ⟨slots, pre⟩ := f
  have h2 : slots = [] :: t := h
  subst h2
  rfl

/-- The counterexample's coverless frame is HEAD-empty, so it is exactly
the PLAN's "head remaining domain is empty" disjunct. -/
theorem cexCoverless_headEmpty :
    ∃ t : List Domain, (([[]], ([] : Assignment)) : BranchFrame).1 = [] :: t :=
  ⟨[], rfl⟩

/-! ## §5 Residual (exactly what is NOT delivered here)

1. `hinhab` as quoted is FALSE (`cexNotAllSites`) — the consumer must take
   `supportedInhabited_or_coverless` (or the live-site family) instead.
2. The RECORDED-SITE refinement "`cfg.conflict = some ev` with a coverless
   frame does not arise (or its `hfresh` obligation is discharged)" is NOT
   proved here. It is a UNIT-KIT propagator analysis: a recorded site with
   a nonempty clause list comes from `scanPropagators` with
   `frameViewedB = true` and `scanDatabase = .stable`
   (`nextPruningEvent_conflict_cases`), and for the unit families
   (`leConstHi`/`leConstLo`/`ltConstHi`/`ltConstLo`/`constEq`) a conflict
   at a coverless frame whose nonempty-domain slots agree with a STABLE
   live predecessor contradicts that predecessor's stability. The
   reachable coverless frames of this kit are created by
   (a) `stepDecide`'s sibling when the split head is a singleton and the
   pin is fresh (`cexNotAllSites`), (b) an empty original domain, or
   (c) transport of (a)/(b); in case (a) the frame's HEAD remaining domain
   is empty, so `splitData = none` and the site's next step is a
   local exclusion (`schedulerNext_eq_stable_localExclude` /
   `schedulerNext_eq_conflict_local`) — the empty-frame route of §4 —
   unless a propagator conflict fires there (case excluded by the
   agreement argument above).
3. Consequently, the honest replacement for the `hinhab` residual of
   `SupportedInstance.supportedHpre_unitKit_of_site` is
   `supportedInhabited_or_coverless`, with the coverless case of
   `supportedHfresh_of_site` (and of the site-form `hdb` producer) still
   needing the unit-kit argument of item 2 — an I1/J1-side obligation, not
   an assumed premise. -/

end LeanFzn.Solver.UIP

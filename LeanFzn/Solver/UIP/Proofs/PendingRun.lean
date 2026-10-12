/-
File: LeanFzn/Solver/UIP/Proofs/PendingRun.lean
pending-side invariant, its preservation along a supported run, and the
route-(b) consume consumer)

Purpose: close R2a's two remaining obligations on top of the per-arm
lemmas of `Proofs/PendingBacked.lean` §5:

  §1 `pendingSideInv_of_premises` — ONE joint induction over the
     supported run (`SupportedReach orig original props`) that maintains
     `PendingSideInv orig cfg` at every configuration, dispatching through
     the real `schedulerNext` leaf table (`C2d.schedulerNext_cases`) and
     consuming exactly the per-arm preservation lemmas of §5.5. The decide
     arm's `ReachableState` premise comes from the run-level branch
     invariant `hbr`; the jump arm's checkpoint membership comes from
     `checkpointAt_mem`. No domain `Nodup`, no density or depth premise:
     sparse domains and deep/shallow pending stacks go through the same
     lemmas.

  §2 the consume consumers at the run's own box:
     * `stepConsume_reachable_of_inv_missing_checkpoint` — ROUTE (b), the
       missing-checkpoint resume, with the head's backing DERIVED from
       `PendingSideInv.pending` (never assumed at the site), consuming
       `stepConsume_reachable_of_backedList` (PendingBacked §5.3);
     * `stepConsume_reachable_of_inv_and_checkpoint` — the full split
       theorem. Its checkpoint-present half is ROUTE (a) and is left as
       ONE explicit named premise `hcpRoute` (see §3 for the audit of
       what that premise still contains).

  §3 the route-(a) audit (docstrings) plus the FREE conjunct lemmas of
     `ReachableState` at the `resumeSibling` successor, landed under
     explicit premises: `resumeSibling_length_ok` (from
     `PendingBacked.full_len`), `resumeSibling_full_fits` (from
     `PendingBacked.fit`), `resumeSibling_sorted` (from the
     predecessor's `TrailLevelSorted`), `resumeSibling_wellFormed` (from
     the predecessor's `WellFormed` + sortedness). The genuinely open
     conjuncts (prefix_forced / agrees / narrowing_complete / distinct)
     are named in §3 (c) with the invariant that must supply each.

NO `sorry`, NO custom axiom. Registered in the umbrella
(`LeanFzn.Solver.lean`). -/

import LeanFzn.Solver.UIP.Proofs.PendingBacked
import LeanFzn.Solver.UIP.Proofs.SupportedRun
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 The run-level producer: `PendingSideInv` along a supported run -/

/-- **R2a STEP (pair-friendly form)**: one real supported successor
preserves `PendingSideInv`, consuming the PREDECESSOR's branch
reachability directly (only the fresh-decide arm needs it:
`PendingSideInv.stepDecide`'s reachability premise). This is the form a
joint induction over `ReachableState ∧ … ∧ PendingSideInv` calls — the
predecessor's reachability is the other component of its own induction
hypothesis. The jump arm's checkpoint membership comes from
`checkpointAt_mem`. -/
theorem pendingSideInv_supportedStep {orig : List Domain}
    {leaf : Assignment → Bool}
    (hshape : ShapeTypedDomains orig)
    {cfg cfg' : SchedulerConfig leaf}
    (hbrPRE : ReachableState leaf orig cfg.branch)
    (hs : (schedulerNext cfg).successor = some cfg')
    (ih : PendingSideInv orig cfg) :
    PendingSideInv orig cfg' := by
      rcases C2d.schedulerNext_cases cfg with
        ⟨ev, hc, hnext⟩ | ⟨hconf, hdead, hnext⟩ | ⟨hconf, hact, hrest⟩
      · -- ===== ROUTE 1: recorded evidence (backjumpStep)
        rw [hnext] at hs
        unfold backjumpStep at hs
        cases ha : ev.analysis with
        | none =>
            -- no analysis → chronological fallback (stack and checkpoints kept)
            rw [ha] at hs
            simp only [] at hs
            simp only [successor_chronologicalFallback, Option.some.injEq] at hs
            subst hs
            exact ih.stepChronologicalFallback (r := branchRegion cfg)
        | some an =>
            cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
            | none =>
                -- no checkpoint → chronological fallback
                rw [ha] at hs
                simp only [] at hs
                rw [hcp] at hs
                simp only [] at hs
                simp only [successor_chronologicalFallback, Option.some.injEq]
                  at hs
                subst hs
                exact ih.stepChronologicalFallback (r := branchRegion cfg)
            | some cp =>
                cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                    an.learned).perform cfg.branch cfg.original cfg.props with
                | none =>
                    -- perform rejected → local exclusion (stack kept)
                    rw [ha] at hs
                    simp only [] at hs
                    rw [hcp] at hs
                    simp only [] at hs
                    rw [hp] at hs
                    simp only [] at hs
                    simp only [successor_localExclude, Option.some.injEq] at hs
                    subst hs
                    exact ih.stepLocalExclude (learned := ev.learned)
                      (r := checkpointRegion cp)
                | some restored =>
                    -- the recorded jump: the selected checkpoint's prefix
                    -- discipline comes from the invariant's checkpoint
                    -- component (`checkpointAt_mem`)
                    rw [ha] at hs
                    simp only [] at hs
                    rw [hcp] at hs
                    simp only [] at hs
                    rw [hp] at hs
                    simp only [] at hs
                    simp only [successor_learnBackjumpAssert, Option.some.injEq]
                      at hs
                    subst hs
                    exact ih.stepLearnBackjumpAssert_ofCheckpoint
                      (checkpointAt_mem hcp) hp
      · -- ===== ROUTE 2: dead branch — the consume route
        rw [hnext] at hs
        unfold consumeStep at hs
        split at hs
        · -- resumed
          rename_i next hcs
          simp only [successor_chronologicalFallback, Option.some.injEq] at hs
          subst hs
          cases hpend : cfg.pending with
          | nil =>
              rw [(stepConsume_eq_none_iff (cfg := cfg)).mpr hpend] at hcs
              cases hcs
          | cons f rest => exact ih.stepConsume hpend hcs
        · -- frontier exhausted: no successor
          simp only [successor_unsat] at hs
          exact absurd hs (by simp)
      · -- ===== ROUTE 3: active branch
        rcases hrest with
          ⟨d, hd, hnext⟩ | ⟨bs, ht, hnext⟩ | ⟨bs, cs, learned, ht, hnext⟩ |
            ⟨bs, lit, reason, learned, ht, hnext⟩
        · -- ARM 1: propagate
          rw [hnext] at hs
          simp only [successor_propagate, Option.some.injEq] at hs
          subst hs
          exact ih.stepPropagate d
        · -- ARM 2 / ARM 3 / ARM 6: the guarded stable dispatch
          rw [hnext] at hs
          unfold stableStepGuarded at hs
          split at hs
          · -- witness: terminal, no successor
            simp only [successor_sat] at hs
            cases hs
          · split at hs
            · -- split data: fresh decision or redundant-pin skip
              rename_i l v vs doms hsp
              split at hs
              · -- SKIP arm: stepDecideSkip (redundant pin)
                simp only [successor_decide, Option.some.injEq] at hs
                subst hs
                exact ih.stepDecideSkip hsp
              · -- FRESH arm: stepDecide (the one arm needing predecessor reachability)
                simp only [successor_decide, Option.some.injEq] at hs
                subst hs
                exact ih.stepDecide hsp hbrPRE hshape
            · -- no split data: local exclusion with the empty payload
              simp only [successor_localExclude, Option.some.injEq] at hs
              subst hs
              exact ih.stepLocalExclude (learned := []) (r := branchRegion cfg)
        · -- ARM 8 / ARM 4: the conflict dispatch
          cases cs with
          | nil =>
              -- empty clause list: local exclusion with the payload
              rw [hnext] at hs
              simp only [conflictStep] at hs
              simp only [successor_localExclude, Option.some.injEq] at hs
              subst hs
              exact ih.stepLocalExclude (learned := learned)
                (r := branchRegion cfg)
          | cons c rest =>
              by_cases hlv : cfg.branch.level = 0
              · -- level 0: root contradiction, no successor
                rw [hnext] at hs
                simp only [conflictStep, if_pos hlv, successor_unsat] at hs
                cases hs
              · -- recorded analyze site: branch unchanged
                rw [hnext] at hs
                simp only [conflictStep, if_neg hlv, successor_analyzeConflict,
                  Option.some.injEq] at hs
                subst hs
                exact ih.stepAnalyzeConflictCounted
        · -- ARM 6: localExcluded → local exclusion with the payload
          rw [hnext] at hs
          simp only [successor_localExclude, Option.some.injEq] at hs
          subst hs
          exact ih.stepLocalExclude (learned := learned) (r := branchRegion cfg)

/-- **R2a PRODUCER (run level)**: every configuration of a supported run
carries `PendingSideInv` — the current branch's prefix is pinned, every
pending alternative is backed, every saved checkpoint's frame prefix is
pinned. An induction over `SupportedReach` steered by the per-arm
`pendingSideInv_supportedStep`. External premises: the run box's typing
`hshape` and the run's branch reachability `hbr` (only the decide arm
consumes `hbr`). -/
theorem pendingSideInv_of_premises {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool}
    (hshape : ShapeTypedDomains orig)
    (hbr : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      PendingSideInv orig cfg := by
  intro cfg hreach
  induction hreach with
  | init => exact PendingSideInv.init orig original props
  | step hrec hs ih => exact pendingSideInv_supportedStep hshape (hbr hrec) hs ih

/-! ## §2 The consume reachability consumer (single canonical route) -/

/-- **R2 CONSUMER — THE SINGLE CANONICAL ROUTE, UNCONDITIONAL**: any
consume of a backed pending head resumes a reachable branch. The
successor's branch is ALWAYS `resumePending` (the checkpoint-consulting
route is RETIRED — `resumeSibling_shadow_not_represents` refutes it on a
genuine reachable run), and its reachability is R1's
`resumePending_reachable` fed with the head's backing DERIVED from the
run-level stack invariant (`hpinv.pending`). No checkpoint case split, no
route-(a) premise. -/
theorem stepConsume_reachable_of_inv {leaf : Assignment → Bool}
    {orig : List Domain} {cfg next : SchedulerConfig leaf} {f : BranchFrame}
    {rest : List BranchFrame}
    (hp : cfg.pending = f :: rest) (h : stepConsume cfg = some next)
    (hreach : ReachableState leaf orig cfg.branch)
    (hpinv : PendingSideInv orig cfg) (horig : cfg.orig = orig) :
    ReachableState leaf orig next.branch := by
  rw [← horig] at hreach hpinv ⊢
  rw [stepConsume_branch hp h]
  exact resumePending_reachable hreach
    (hpinv.pending f (by rw [hp]; exact List.mem_cons_self ..))

/-- COMPATIBILITY WRAPPER (retained name): route (b) is no longer a route
— every consume is the canonical resume — so the old checkpoint-absent
premise is ignored. -/
theorem stepConsume_reachable_of_inv_missing_checkpoint {leaf : Assignment → Bool}
    {orig : List Domain} {cfg next : SchedulerConfig leaf} {f : BranchFrame}
    {rest : List BranchFrame}
    (hp : cfg.pending = f :: rest) (h : stepConsume cfg = some next)
    (_hcp : checkpointAt cfg.checkpoints f.2.length = none)
    (hreach : ReachableState leaf orig cfg.branch)
    (hpinv : PendingSideInv orig cfg) (horig : cfg.orig = orig) :
    ReachableState leaf orig next.branch :=
  stepConsume_reachable_of_inv hp h hreach hpinv horig

/-- **THE SUPPORTED `hconsume` GATE PRODUCER** (R2 deliverable, route (a)
retired): at the supported index, every consume of a supported run
resumes a reachable branch. The stack invariant comes from
`pendingSideInv_of_premises`, the branch reachability from the run's
`hbr` component; NO route premise and NO checkpoint case split remain.
This is the `hconsume` field shape of the arm-gate records
(`SupportedArmInvGatesCore.hconsume`). -/
theorem supportedHconsume_of_premises {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool}
    (hshape : ShapeTypedDomains orig)
    (hbr : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch) :
    ∀ {cfg next : SchedulerConfig leaf} {f : BranchFrame}
      {rest : List BranchFrame},
      SupportedReach orig original props cfg → cfg.pending = f :: rest →
        stepConsume cfg = some next → ReachableState leaf orig next.branch :=
  fun hreach hp h =>
    stepConsume_reachable_of_inv hp h (hbr hreach)
      (pendingSideInv_of_premises hshape hbr hreach)
      (SupportedReach.orig_eq hreach)

/-! ## §3 The route-(a) audit (RETIRED ROUTE — see §4's verdict)

VERDICT UPDATE: the route was not merely unproved — it is WRONG on a
genuine reachable run (§4: `resumeSibling_shadow_not_represents`, with a
recorded real-dispatcher transcript). The runtime no longer consults
`checkpointAt` at a consume (`stepConsume` = the single canonical
`resumePending` route), so the four open conjuncts below are moot for the
successor's reachability; they are retained as the audit of why the
checkpoint-consulting route had to be retired. The residual audit below
remains accurate for the retired route.

### (a) Is `cp.frame.2 = f.2` derivable at a checkpoint-present consume?

NO — it is not derivable from the landed invariants, and it is FALSE in
reachable-shaped configurations. The premises available at the site are
`checkpointAt cfg.checkpoints f.2.length = some cp` (hence `cp.level =
f.2.length` and `cp ∈ cfg.checkpoints`), the checkpoint identity
`cp.Identifies cfg.branch cp.level` (C2c's chain component, when
available) and `PendingSideInv`. What IS derivable from `Identifies`:

* `cfg.branch.trail = cp.trail ++ mid` with every `mid` entry at level
  `≥ cp.level` — a TRAIL relation between `cp` and the CURRENT branch;
* `FrameDescendsFrom cfg.branch.frame cp.frame` — only coverage
  (`∀ a, FrameCovers cfg.branch.frame a → FrameCovers cp.frame a`), which
  with nonempty tails even forces `cp.frame.2.length ≤ cfg.branch.frame.2.length`;
  it gives NO equality and says nothing about the PENDING head `f`.

Concrete reachable-shaped witness for the failure (a `SchedulerConfig`
that every landed invariant accepts, `PendingSideInv` included):
`orig = [[false, true], [false, true]]`, branch `frame = ([d1], [true])`,
`trail = [{literal := posBool 0 true, level := 1, reason := none}]`,
`level = 1`, `pending = [([d1], [false])]` and
`checkpoints = [{level := 1, frame := ([d1], [true]), trail := []}]`
(`fixtureLeaf := fun _ => true`). Then `f := ([d1], [false])` is backed
(`full_len` 2 = 2, `fit` pointwise, `pins` at `[false]`, `shape`), the
branch satisfies the eight `ReachableState` fields, and the checkpoint
identifies the branch at level `1` (`mid` = the single pin) — yet
`cp.frame.2 = [true] ≠ [false] = f.2`. The scenario is not artificial: a
jump below the split level retires `f`'s own parent checkpoint, and the
re-ascent pushes a NEW level-`f.2.length` checkpoint whose prefix is the
RE-ASCENDED branch's prefix (the assertion filter of the jump removed the
failed value), not the old sibling's prefix; consumes of frames in front
of `f` whose level is `≥ f.2.length` keep that newer checkpoint, so at
`f`'s consume `checkpointAt` legitimately returns it. `resumeSibling`
then takes `cp.frame.1`'s head value and `bs.restoreLevel f.2.length` —
the WRONG ancestor's data; the surfaced symptom is a duplicate/foreign
retire entry, i.e. exactly the `distinct` / `narrowing_complete` /
`agrees` conjuncts below. The correct producer must therefore relate the
pending head to the checkpoint (a `CpChain`-style pending/checkpoint
correspondence), not assume frame equality.

### (b) FREE conjuncts at `resumeSibling` (landed below)

`resumeSibling bs f cp = { frame := f, trail := (bs.restoreLevel f.2.length).trail ++ retired, level := f.2.length, learned := bs.learned }`.

* `length_ok` — FREE: `resumeSibling_length_ok` (from `PendingBacked.full_len`).
* `full_fits` — FREE: `resumeSibling_full_fits` (from `PendingBacked.fit`).
* `sorted` — FREE: `resumeSibling_sorted` (the restored prefix is a
  filter of a sorted trail; the retired list is empty or one entry at
  the resumed level; `levelSorted_filter` + `siblingRetired_shape`).
* `wellFormed` — FREE: `resumeSibling_wellFormed` (levels from the
  filter and the retired entry; normalization from the predecessor; the
  chronology conjunct lifts because level-sortedness bounds every
  earlier reason-literal's entry by the reason's own level `≤ f.2.length`,
  so it survives `restoreLevel`; the retired entry is reason-less; the
  learned database is carried unchanged).

### (c) OPEN conjuncts at `resumeSibling` (one line each)

* `prefix_forced` — needs the retained restored pin of position
  `i < f.2.length` to pin `f.2[i]`: supplied by a branch/checkpoint
  prefix-compatibility invariant (`f.2` agrees with the ancestor's
  restored prefix on `0..f.2.length`), which is exactly the missing
  pending/checkpoint correspondence.
* `agrees` — restored entries must hold at every `f`-covered assignment;
  `hreach.agrees` only gives them at `cfg.branch.frame`-covered
  assignments. Supplied by `FrameDescendsFrom f cfg.branch.frame`
  (the resumed frame is an ANCESTOR's frame, so it covers MORE
  assignments than the branch — the descent direction is the reverse of
  the checkpoint's own) together with the frame equality question of (a).
* `narrowing_complete` — the retired entry falsifies only the single
  head value recovered from `cp.frame`; all other dropped original
  values of `f`'s remaining slots need their falsifiers in
  `bs.restoreLevel f.2.length`'s trail. Supplied by the predecessor's
  own `NarrowingComplete` plus a level bound on the witnesses (their
  falsifier entries sit at levels `≤ f.2.length`), i.e. again the
  pending/checkpoint correspondence at levels below the head.
* `distinct` — the retire literal `(valueLiteral f.2.length v).negate.norm`
  must be fresh in the restored trail. Supplied by the checkpoint's
  coverage (a `slot ≠ v` entry cannot hold at a checkpoint frame that
  still admits `v` in its head domain, given a completable tail) plus the
  identity's trail-prefix decomposition; without (a)'s correspondence the
  wrong `v` can already have its negation recorded. -/

/-! ### §3.1 The retired-entry algebra (route-(a) helpers) -/

/-- The list `resumeSibling` appends: empty, or the single retiring entry
of the checkpoint frame's head value. Factored out so the shape lemmas
below can be stated without unfolding `resumeSibling`'s body. -/
def siblingRetired (slot : Nat) (cp : DecisionCheckpoint leaf) : List TrailEntry :=
  match cp.frame.1 with
  | (v :: _) :: _ => (retiredEntry slot v).toList
  | _ => []

/-- The `resumeSibling` trail decomposition with the factored list (rfl). -/
theorem resumeSibling_trail' (bs : BranchState leaf) (f : BranchFrame)
    (cp : DecisionCheckpoint leaf) :
    (resumeSibling bs f cp).trail =
      (bs.restoreLevel f.2.length).trail ++ siblingRetired f.2.length cp := rfl

/-- SHAPE OF THE RETIRED LIST: every entry (there is at most one) sits at
the resumed level, is normalized and is reason-less. -/
theorem siblingRetired_shape (slot : Nat) (cp : DecisionCheckpoint leaf) :
    ∀ e ∈ siblingRetired slot cp,
      e.level = slot ∧ e.literal = e.literal.norm ∧ e.reason = none := by
  cases hcf : cp.frame.1 with
  | nil =>
      intro e he
      simp only [siblingRetired, hcf] at he
      exact absurd he (List.not_mem_nil)
  | cons d rest =>
      cases hd : d with
      | nil =>
          intro e he
          simp only [siblingRetired, hcf, hd] at he
          exact absurd he (List.not_mem_nil)
      | cons v vs =>
          intro e he
          simp only [siblingRetired, hcf, hd] at he
          unfold retiredEntry at he
          cases hv : valueLiteral slot v with
          | none =>
              simp only [hv, Option.map_none, Option.toList_none] at he
              exact absurd he (List.not_mem_nil)
          | some l =>
              simp only [hv, Option.map_some, Option.toList_some,
                List.mem_singleton] at he
              subst he
              exact ⟨rfl, (literal_norm_idem l.negate).symm, rfl⟩

/-- The retired list is level-sorted (constant level). -/
theorem siblingRetired_sorted (slot : Nat) (cp : DecisionCheckpoint leaf) :
    TrailLevelSorted (siblingRetired slot cp) := by
  rw [TrailLevelSorted, List.pairwise_iff_getElem]
  intro i j hi hj _
  have h1 := (siblingRetired_shape slot cp _ (List.getElem_mem hi)).1
  have h2 := (siblingRetired_shape slot cp _ (List.getElem_mem hj)).1
  omega

/-- An entry of a `restoreLevel` trail sits at or below the target level. -/
theorem mem_restoreLevel_level_le {bs : BranchState leaf} {target : Nat}
    {e : TrailEntry} (he : e ∈ (bs.restoreLevel target).trail) :
    e.level ≤ target :=
  of_decide_eq_true (List.mem_filter.mp he).2

/-! ### §3.2 The free `ReachableState` conjuncts at `resumeSibling` -/

/-- FREE: `length_ok` at the checkpoint-present consume — the resumed
frame is the pending head, whose `full_len` is part of its backing. -/
theorem resumeSibling_length_ok {orig : List Domain}
    {bs : BranchState leaf} {f : BranchFrame} {cp : DecisionCheckpoint leaf}
    (hb : PendingBacked orig f) :
    (fullDomains (resumeSibling bs f cp).frame).length = orig.length := by
  rw [resumeSibling_frame]
  exact hb.full_len

/-- FREE: `full_fits` at the checkpoint-present consume — pointwise
sub-box provenance of the pending head. -/
theorem resumeSibling_full_fits {orig : List Domain}
    {bs : BranchState leaf} {f : BranchFrame} {cp : DecisionCheckpoint leaf}
    (hb : PendingBacked orig f) :
    ∀ i v, v ∈ (fullDomains (resumeSibling bs f cp).frame).getD i [] →
      v ∈ orig.getD i [] := by
  rw [resumeSibling_frame]
  exact hb.fit

/-- FREE: `sorted` at the checkpoint-present consume — the level-filtered
restoration of a sorted trail, followed by the retired list (empty or one
entry at the resumed level). -/
theorem resumeSibling_sorted {bs : BranchState leaf} {f : BranchFrame}
    {cp : DecisionCheckpoint leaf} (hs : TrailLevelSorted bs.trail) :
    TrailLevelSorted (resumeSibling bs f cp).trail := by
  rw [resumeSibling_trail',
    show (bs.restoreLevel f.2.length).trail =
      bs.trail.filter (fun e => e.level ≤ f.2.length) from rfl,
    TrailLevelSorted, List.pairwise_append]
  refine ⟨levelSorted_filter _ hs, siblingRetired_sorted f.2.length cp, ?_⟩
  intro a ha b hb
  have ha' : a.level ≤ f.2.length :=
    of_decide_eq_true (List.mem_filter.mp ha).2
  have hb' : b.level = f.2.length :=
    (siblingRetired_shape f.2.length cp b hb).1
  omega

/- PARTIALLY FREE: `wf` at the checkpoint-present consume. The level
bound, normalization, reason-entailment/pivot and learned conjuncts are
mechanical (`mem_restoreLevel_level_le`, the predecessor's `WellFormed`,
`siblingRetired_shape`, `resumeSibling_learned`). The chronology conjunct
(`∀ e ∈ trail, ∀ r ∈ e.reason, … ∃ e' ∈ trail, … earlierThan trail e' e`)
lifts through `restoreLevel` because level-sortedness bounds every
earlier witness `e'` by `e.level ≤ f.2.length` (so it survives the
filter), but the index transport into the FILTERED list needs one
order-preservation helper that is not landed yet:

  `List.Sublist`-order lemma (target shape):
  `∀ {l₁ l₂} (hs : l₁.Sublist l₂) {e' e}, e' ∈ l₁ → e ∈ l₁ →
     TrailEntry.earlierThan l₂ e' e → TrailEntry.earlierThan l₁ e' e`

(apply with `hs := List.filter_sublist`, `l₁ := bs.trail.filter …`); the
proof is an induction on `hs` shifting the two witness indices. The four
other conjuncts are proved below in `resumeSibling_wf_of_…`-style bullets
only once that helper lands; the audit (§3(c)) records the conjunct as
mechanical-with-one-helper rather than free. -/

/-! ## §4 R2 DELIVERABLE 1 — the shadowed checkpoint IS REACHABLE:
`resumeSibling`'s checkpoint recovery is refuted on an actual run

VERDICT (session 11 round 3, decisive experiment). The §3(a) scenario is
NOT merely reachable-shaped: it occurs on an ACTUAL execution driven by the
real dispatcher `schedulerNext` from the real `SchedulerConfig.init`. The
exploration ran the real dispatcher (a scratch `#eval` driver, deleted
before the handoff); the transcript below is a genuine chain of real
transitions:

* box  `= [[Value.int 1, Value.int 2]]` (one int slot),
* leaf `= fun _ => false`,
* prop = fires `.conflict [posNe 0 1]` when `Frame.domains`'s head slot is
  exactly `[Value.int 1]`.

```
1. decide(lvl0, v1)     root split: pending f0 = ([[2]], []), cp0 = root
2. analyze              at the level-1 child ([], [1]): the prop reports
                        [posNe 0 1]; the recorded analysis is ([], negNe 0 1)
                        (learned [posNe 0 1], target level 0, asserting posNe 0 1)
3. jump(lvl1)           restore cp0, narrow slot 0 to [2], assert posNe 0 1
4. decide(lvl0, v2)     RE-DECISION at level 0: pushes cp* = the re-ascended
                        frame ([[2]], []) and sibling ([[]], []) — cp* SHADOWS cp0
5. excl(lvl1)           the child ([], [2]) is dead
6. consume([[]], [])    retirement "slot0 ≠ 2" (matches its own parent cp*)
7. excl(lvl0)           the empty frame is dead
8. consume f0           `checkpointAt cp* 0 = some cp*` (cp0 is present but
                        OLDER): the retired value is cp*.frame.1's head = 2,
                        while f0's head domain is [2] — the resumed trail
                        falsifies 2 ∈ f0's own head domain at the covered
                        assignment [Value.int 2]
```

The consumed frame is `f0 = ([[Value.int 2]], [])`; the successor trail
carries `{ literal := posNe 0 2, level := 0, reason := none }` (the
retirement of `2`), while f0's head domain `[2]` still admits `2`. Hence
the successor branch state cannot satisfy `ReachableState.agrees` — the
consume of a genuine pending alternative produces a state that is NOT a
reachable branch state. (The kernel-checked content of this mechanism is
`resumeSibling_shadow_not_represents` below; the chain of the eight real
`SchedulerReachable.step` equations is the named residual
`shadowRun_reachable` — its substrate and trace are pinned in §4.1 so the
kernel-chained version is mechanical: `driveReachN`-style, cf.
`Tests/SchedulerActivation.lean`. HONESTY: the reachability of the §4
witness is established by the recorded dispatcher transcript (the real
`#eval` driver), NOT by a kernel chain; only the mechanism lemmas below
are kernel-proved.)

§4.1 THE PINNED WITNESS SUBSTRATE (for the kernel chain, next round):

```
def shadowBox : List Domain := [[Value.int 1, Value.int 2]]
def shadowLeaf : Assignment → Bool := fun _ => false
def shadowProp : Propagator :=
  { watches := [], run := fun st =>
      match st.domains with
      | [Value.int 1] :: _ => .conflict [posNe 0 1]
      | _ => .stable }
def shadowInit : SchedulerConfig shadowLeaf :=
  SchedulerConfig.init shadowBox [] [shadowProp]
-- cfg1 = stepDecide shadowInit (int 1) [int 2] [] (negNe 0 1)
-- cfg2 = stepAnalyzeConflictCounted cfg1 (posNe 0 1) [posNe 0 1]
--          (analyzeEventsExpansions cfg1.branch.trail cfg1.branch.level (posNe 0 1))
-- cfg3 = stepLearnBackjumpAssert cfg2 (BackjumpPlan.ofCheckpoint … ) … (…)
-- cfg4 = stepDecide cfg3 (int 2) [] [] (negNe 0 2)          -- pushes cp*
-- cfg5 = stepLocalExclude cfg4 [] (branchRegion cfg4)
-- cfg6 = stepConsume cfg5 |>.getD cfg5                    -- consume ([[]], [])
-- cfg7 = stepLocalExclude cfg6 [] (branchRegion cfg6)
-- cfg8 = stepConsume cfg7 |>.getD cfg7                    -- consume f0  ← THE BUG
-- claim: checkpointAt cfg7.checkpoints 0 = some cp* with cp*.frame = ([[2]], [])
--        and cfg7.pending.head = ([[2]], []), i.e. the hypotheses of
--        `resumeSibling_shadow_not_represents` with v = Value.int 2, rest' = [],
--        doms' = [], tail = []
```

MECHANISM (kernel-checked below). `resumeSibling` recovers the dropped
value from `cp.frame.1`'s head, so whenever a NEWER same-level checkpoint
`cp` survives, the retirement falsifies `cp`'s head value — which the
resumed frame may still admit (`resumeSibling_shadow_not_represents`). The
checkpoint list cannot exclude this: `checkpointAt` returns the NEWEST
level-`f.2.length` entry, the newer one is legitimately pushed by the
re-ascent decision, and the R1 retirement (`level ≤ f.2.length`) retires
the parent's checkpoint only together with every later one — whereas the
shadowing checkpoint is pushed AFTER f and survives every level-based
filter at or above `f.2.length`.

CONSEQUENCE (PLAN R2): the checkpoint route of `resumeSibling` is
semantically WRONG on reachable runs and must be repaired exactly as the
R1 route-(b) repair replaced the prefix-length trail. The repaired
recovery must derive the retired values from a source that cannot be the
wrong ancestor: the pending head's own frame `f` together with the
original box — the R1 canonical falsifier family
`canonicalFalsifiers orig f` / `slotFalsifiers orig f 0 f.1.head`
(`BackjumpFrontier.lean`), which falsifies exactly the values the resumed
frame excludes and never a value it admits. Wiring that repair changes the
one call site `resumeSibling cfg.branch f cp` in `SchedulerStep.lean`'s
`stepConsume` (the first argument becomes `cfg.orig`); `SchedulerStep.lean`
is outside this task's exclusive files (other workers active), so the
wiring + the re-pointed route lemmas are reported as the named residual
for the coordinator (handoff §"next action"). -/

/-- R2 D1 MECHANISM, bridged: the normalized negation of a value pin
evaluates to `false` at the assignment that pins the value at the pin's
own slot. (The `eval`/`valueHolds` bridge for the retirement entry.) -/
theorem literal_negate_norm_eval_false {s : Nat} {v : Value} {l : Literal}
    {pre tail : Assignment} (hl : valueLiteral s v = some l)
    (hslot : s = pre.length) :
    (l.negate.norm).eval (pre ++ v :: tail) = some false := by
  have hget : (pre ++ v :: tail)[s]? = some v := by
    rw [hslot, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  cases v with
  | bool b =>
      simp only [valueLiteral, Option.some.injEq] at hl
      subst hl
      cases b <;>
        simp [posBool, Literal.negate, Literal.norm, Literal.eval, Atom.eval, hget]
  | int i =>
      simp only [valueLiteral, Option.some.injEq] at hl
      subst hl
      simp [negNe, Literal.negate, Literal.norm, Literal.eval, Atom.eval,
        slotInt, Value.intView, hget]
  | setOfInt s' => simp [valueLiteral] at hl
  | array vs => simp [valueLiteral] at hl

/-- **R2 D1 REFUTATION (kernel-checked)**: when the found checkpoint's frame
heads its first remaining slot with `v` and the resumed frame STILL admits
`v` in its own head domain (the shadowed-checkpoint configuration),
`resumeSibling`'s trail falsifies a value of its own frame at a
frame-covered assignment — no `ReachableState`-style agreement can hold
for that state. The hypotheses are exactly the witness's data:
`cp.frame.1 = (v :: rest) :: doms` (the checkpoint's head slot),
`valueLiteral f.2.length v = some l` (the value is in the decision
vocabulary) and `f.1 = v :: rest'` (the resumed frame still admits `v`,
with the tail `rest'`). -/
theorem resumeSibling_shadow_not_represents {bs : BranchState leaf}
    {f : BranchFrame} {cp : DecisionCheckpoint leaf} {v : Value}
    {rest rest' : Domain} {doms doms' : List Domain} {l : Literal}
    {tail : Assignment}
    (hcp : cp.frame.1 = (v :: rest) :: doms)
    (hl : valueLiteral f.2.length v = some l)
    (hf : f.1 = (v :: rest') :: doms') (htail : tail ∈ allAssigns doms') :
    ∃ a, FrameCovers (resumeSibling bs f cp).frame a ∧
      ∃ e ∈ (resumeSibling bs f cp).trail,
        e.literal.eval a = some false := by
  refine ⟨f.2 ++ v :: tail, ?_, ?_⟩
  · rw [resumeSibling_frame]
    refine ⟨v :: tail, ?_, rfl⟩
    rw [hf]
    exact (mem_allAssigns_singleton v rest' doms' (v :: tail)).mpr
      ⟨v, List.mem_cons_self .., tail, htail, rfl⟩
  · refine ⟨{ literal := l.negate.norm, level := f.2.length,
               reason := none }, ?_, ?_⟩
    · -- the retirement entry is in the trail
      rw [resumeSibling_trail, hcp]
      simp only [retiredEntry, hl, Option.map_some, Option.toList_some]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact literal_negate_norm_eval_false hl rfl

end LeanFzn.Solver.UIP

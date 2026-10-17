/-
File: LeanFzn/Solver/UIP/Proofs/BackjumpFrontier.lean

Purpose:
  Proofs for the backjump scheduler:

  * `BackjumpPlan.execute_wellFormed` — exact restoration plus the
    single asserting enqueue preserves the branch invariant, with the
    checkpoint's level law and the asserting entry's obligations as
    explicit premises;
  * forward representation: everything the restored state represented
    and which satisfies the asserting literal is represented
    afterwards — so no still-possible solution is lost;
  * the represented assignments of the executed state satisfy the
    learned clause (restoration never re-admits what the clause
    excludes);
  * the classification's soundness composition: surviving solutions
    remain enumerated, and only proved-clause/exhausted assignments are
    dropped.

Dependencies:
  - LeanFzn.Solver.Propagation.BackjumpFrontier
  - LeanFzn.Solver.Propagation.Proofs.BranchState (`earlierThan_extend`, `trail_mem_append`)

DAG:
  BackjumpFrontier + Proofs.BranchState -> Proofs.BackjumpFrontier
  -> the integrated driver.
-/

import LeanFzn.Solver.Propagation.BackjumpFrontier
import LeanFzn.Solver.Propagation.Proofs.BranchState
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## The executing entry's shape -/

/-- The entry a plan appends. -/
def _root_.LeanFzn.Solver.Propagation.BackjumpPlan.entry (p : BackjumpPlan leaf) : TrailEntry :=
  { literal := p.asserting.norm, level := p.target,
    reason := some { clause := p.learned } }

@[simp] theorem _root_.LeanFzn.Solver.Propagation.BackjumpPlan.entry_literal (p : BackjumpPlan leaf) :
    p.entry.literal = p.asserting.norm := rfl

/-- The executed trail is the checkpoint's trail followed by the single
asserting entry. -/
theorem _root_.LeanFzn.Solver.Propagation.BackjumpPlan.execute_trail' (p : BackjumpPlan leaf)
    (bs : BranchState leaf) :
    (p.execute bs).trail = p.checkpoint.trail ++ p.assertExtra := rfl

/-- Every appended entry is the plan's entry. -/
theorem _root_.LeanFzn.Solver.Propagation.BackjumpPlan.execute_mem' (p : BackjumpPlan leaf)
    (bs : BranchState leaf) {e : TrailEntry} (he : e ∈ (p.execute bs).trail) :
    e ∈ p.checkpoint.trail ∨ e = p.entry :=
  BackjumpPlan.execute_mem p bs he

/-- Either the entry was skipped, or the trail is exactly checkpoint ++ entry. -/
theorem _root_.LeanFzn.Solver.Propagation.BackjumpPlan.execute_trail_cases (p : BackjumpPlan leaf)
    (bs : BranchState leaf) :
    ((p.execute bs).trail = p.checkpoint.trail ∧
      ∃ e ∈ p.checkpoint.trail, e.literal = p.asserting.norm) ∨
    ((p.execute bs).trail = p.checkpoint.trail ++ [p.entry] ∧
      ∀ e ∈ p.checkpoint.trail, e.literal ≠ p.asserting.norm) := by
  unfold BackjumpPlan.execute BackjumpPlan.assertExtra
  split
  · next h =>
    refine Or.inl ⟨by simp, ?_⟩
    simpa only [List.any_eq_true, decide_eq_true_eq] using h
  · next h =>
    refine Or.inr ⟨rfl, fun e he heq => h ?_⟩
    simp only [List.any_eq_true, decide_eq_true_eq]
    exact ⟨e, he, heq⟩

/-! ## Well-formedness preservation -/

/-- Executing a backjump preserves the branch invariant. Premises name
exactly the obligations: the checkpoint is a well-formed state saved at
the target level, the current learned database is entailed, and the
asserting entry's reason is entailed, contains its pivot, and has
earlier falsifiers on the restored trail. -/
theorem _root_.LeanFzn.Solver.Propagation.BackjumpPlan.execute_wellFormed {p : BackjumpPlan leaf}
    {bs : BranchState leaf}
    (hcp : p.checkpoint.WellFormed)
    (hcpLevel : p.checkpoint.level = p.target)
    (hbs : LearnedEntailed leaf bs.learned)
    (hent : LearnedEntailed leaf [p.learned])
    (hpivot : (p.asserting.norm ∈ p.learned) = True)
    (hchron : ∀ q ∈ p.learned, q ≠ p.asserting.norm →
      ∃ e' ∈ p.checkpoint.trail, e'.literal = q.negate) :
    (p.execute bs).WellFormed := by
  obtain ⟨hlev, hnorm, hreason, hchron0, _⟩ := hcp
  refine ⟨?_, ?_, ?_, ?_, hbs⟩
  · -- trail levels are bounded by the target level
    intro e he
    rcases BackjumpPlan.execute_mem' p bs he with he | rfl
    · rw [hcpLevel] at hlev
      exact hlev e he
    · simp only [BackjumpPlan.entry]
      exact Nat.le_refl _
  · -- normalization
    intro e he
    rcases BackjumpPlan.execute_mem' p bs he with he | rfl
    · exact hnorm e he
    · simp only [BackjumpPlan.entry]
      rw [norm_norm]
  · -- reason validity
    intro e he r hr
    rcases BackjumpPlan.execute_mem' p bs he with he | rfl
    · exact hreason e he r hr
    · have hr' : { clause := p.learned } = r := by
        simpa only [BackjumpPlan.entry, Option.mem_some_iff] using hr
      rw [← hr']
      exact ⟨hent, hpivot⟩
  · -- chronology
    intro e he r hr q hq hne
    rcases BackjumpPlan.execute_trail_cases p bs with ⟨htr, -⟩ | ⟨htr, -⟩
    · rw [htr] at he ⊢
      exact hchron0 e he r hr q hq hne
    rw [htr] at he ⊢
    rcases trail_append_entry_mem he with he | rfl
    · obtain ⟨e'', he'', heq, hlt⟩ := hchron0 e he r hr q hq hne
      exact ⟨e'', trail_mem_append he'' _, heq, earlierThan_extend hlt⟩
    · have hr' : { clause := p.learned } = r := by
        simpa only [BackjumpPlan.entry, Option.mem_some_iff] using hr
      rw [← hr'] at hq
      have hne' : q ≠ p.asserting.norm := by
        simpa only [BackjumpPlan.entry] using hne
      obtain ⟨e'', he'', heq⟩ := hchron q hq hne'
      refine ⟨e'', trail_mem_append he'' _, heq, ?_⟩
      exact earlierThan_append_last he''

/-! ## Coverage and exclusion -/

/-- Forward representation: an assignment covered by the checkpoint's
frame, satisfying the restored trail, satisfying the retained learned
database, and satisfying the asserting literal, is represented by the
executed state. No still-possible solution is lost by the jump. -/
theorem _root_.LeanFzn.Solver.Propagation.BackjumpPlan.execute_represents_forward {p : BackjumpPlan leaf}
    {bs : BranchState leaf} {a : Assignment}
    (hframe : FrameCovers p.checkpoint.frame a)
    (htrail : ∀ e ∈ p.checkpoint.trail, e.literal.eval a = some true)
    (hlearn : ∀ c ∈ bs.learned, c.SatisfiedBy a)
    (hassert : p.asserting.norm.eval a = some true) :
    (p.execute bs).Represents a := by
  refine ⟨hframe, ?_, hlearn⟩
  intro e he
  rcases BackjumpPlan.execute_mem' p bs he with he | rfl
  · exact htrail e he
  · simpa only [BackjumpPlan.entry] using hassert

/-- The executed state's represented assignments satisfy the learned
clause: the restored trail carries the asserting literal, whose reason
clause is the learned one and which is a member of it. -/
theorem _root_.LeanFzn.Solver.Propagation.BackjumpPlan.execute_satisfies_learned {p : BackjumpPlan leaf}
    {bs : BranchState leaf} {a : Assignment}
    (hrep : (p.execute bs).Represents a)
    (hpivot : p.asserting.norm ∈ p.learned) :
    p.learned.SatisfiedBy a := by
  obtain ⟨_, htrail, _⟩ := hrep
  refine ⟨p.asserting.norm, hpivot, ?_⟩
  rcases BackjumpPlan.execute_trail_cases p bs with ⟨htr, e, he, hel⟩ | ⟨htr, -⟩
  · have := htrail e (by rw [htr]; exact he)
    rwa [hel] at this
  · have := htrail p.entry (by
      rw [htr]
      exact List.mem_append.mpr (Or.inr (List.mem_singleton_self _)))
    simpa only [BackjumpPlan.entry] using this

/-! ## Classification soundness

The classification's contract (from the interface module) composes into
the two facts the integrated scheduler needs: surviving solutions stay
enumerated, and the next frontier introduces nothing new. -/

/-- Surviving solutions remain enumerated after the transition. -/
theorem classification_retains {leaf : Assignment → Bool}
    {pending next : List BranchFrame} {log : ExhaustionLog}
    {db : List Clause} (h : ClassificationSound (leaf := leaf) pending next log db) :
    ∀ a, leaf a = true → FrontierCovers pending a →
      FrontierCovers next a ∨
      (∃ r ∈ log.regions, r.mem a = true) ∨
      (∃ c ∈ db, ¬ c.SatisfiedBy a) := h.retains

/-- The next frontier only shrinks the enumerated set. -/
theorem classification_noNew {leaf : Assignment → Bool}
    {pending next : List BranchFrame} {log : ExhaustionLog}
    {db : List Clause} (h : ClassificationSound (leaf := leaf) pending next log db) :
    ∀ a, FrontierCovers next a → FrontierCovers pending a := h.noNew

/-! ## C2c — checkpoint identity: composition under restoration

PLAN C2c (a): checkpoint selection identifies the ACTUAL ancestor, and the
identification SURVIVES the restoration/enqueue extension of the trail.
These three lemmas are the pure algebra the `learnBackjumpAssert` and
consume proofs compose; they carry no caller assumption about which
checkpoint exists or at which level it sits. -/

/-- Frame descent is reflexive. -/
theorem FrameDescendsFrom.refl (f : BranchFrame) : FrameDescendsFrom f f :=
  fun _ ha => ha

/-- Frame descent composes: an ancestor's ancestor is an ancestor. This is
what chains "restored frame descends from the branch" with "the branch
descends from the checkpoint" after a jump. -/
theorem FrameDescendsFrom.trans {g f e : BranchFrame}
    (hgf : FrameDescendsFrom g f) (hfe : FrameDescendsFrom f e) :
    FrameDescendsFrom g e :=
  fun a ha => hfe a (hgf a ha)

/-! ### The checkpoint chain (J1 `hident` companion)

`Identifies` relates ONE checkpoint to the CURRENT branch; it gives no
relation BETWEEN saved checkpoints, so the jump's survivors cannot be
identified from their pre-jump identities alone. The chain states exactly
the missing newest-first dominance: levels, trail prefixes and frame
descents from the head to every older checkpoint. It is maintained at the
push sites (`CpChain.of_identifies`) and by the jump/consume filters. -/

/-- Head dominance: the newest checkpoint dominates every older one —
level bound, trail prefix, and frame descent. -/
def CpDominates (cp : DecisionCheckpoint leaf)
    (rest : List (DecisionCheckpoint leaf)) : Prop :=
  ∀ cp' ∈ rest, cp'.level ≤ cp.level ∧
    (∃ mid : List TrailEntry, cp.trail = cp'.trail ++ mid ∧
      ∀ e ∈ mid, cp'.level ≤ e.level) ∧
    FrameDescendsFrom cp.frame cp'.frame

/-- NEWEST-FIRST checkpoint chain. -/
def CpChain : List (DecisionCheckpoint leaf) → Prop
  | [] => True
  | cp :: rest => CpDominates cp rest ∧ CpChain rest

/-- PUSH-site constructor: the branch's own snapshot dominates the whole
existing chain (level bound from `CheckpointsBelow`, trail/descent from
the pre-existing identities — `ofBranch bs`'s trail and frame ARE the
branch's). -/
theorem CpChain.of_identifies {bs : BranchState leaf}
    {cps : List (DecisionCheckpoint leaf)}
    (hchain : CpChain cps)
    (hident : ∀ cp ∈ cps, cp.Identifies bs cp.level)
    (hlevel : ∀ cp ∈ cps, cp.level ≤ bs.level) :
    CpChain (DecisionCheckpoint.ofBranch bs :: cps) :=
  ⟨fun cp' hmem =>
    ⟨hlevel cp' hmem, (hident cp' hmem).2.1, (hident cp' hmem).2.2⟩,
    hchain⟩

/-- Any filter (the jump's `·.level ≤ p.target`, the consume's
`·.level ≤ f.2.length`) preserves the chain. -/
theorem CpChain.filter {cps : List (DecisionCheckpoint leaf)}
    (hchain : CpChain cps) (q : DecisionCheckpoint leaf → Bool) :
    CpChain (cps.filter q) := by
  induction cps with
  | nil => exact trivial
  | cons cp rest ih =>
      by_cases hq : q cp = true
      · rw [List.filter_cons_of_pos hq]
        exact ⟨fun cp' hmem => hchain.1 cp' (List.mem_filter.mp hmem).1,
          ih hchain.2⟩
      · rw [List.filter_cons_of_neg hq]
        exact ih hchain.2

/-- THE PAIR LEMMA: the chain + the front-most lookup relate the selected
checkpoint to every older chain member. `checkpointAt` is front-first, so
a member listed BEFORE the selected one is excluded by the head's level
conjunct (its level would have to both exceed and not be the lookup
target). -/
theorem CpChain.pair_of_checkpointAt {cps : List (DecisionCheckpoint leaf)}
    {t : Nat} {cp cp' : DecisionCheckpoint leaf}
    (hchain : CpChain cps) (h : checkpointAt cps t = some cp)
    (hmem : cp' ∈ cps) (hlev : cp'.level ≤ cp.level) :
    cp'.level ≤ cp.level ∧
      (∃ mid : List TrailEntry, cp.trail = cp'.trail ++ mid ∧
        ∀ e ∈ mid, cp'.level ≤ e.level) ∧
      FrameDescendsFrom cp.frame cp'.frame := by
  induction cps with
  | nil => simp [checkpointAt] at h
  | cons a rest ih =>
      simp only [checkpointAt, List.find?_cons] at h
      rcases List.mem_cons.mp hmem with hcpa | hmem'
      · -- cp' is the head `a`: rewrite it away (do not `subst`, which may
        -- eliminate the head and lose the level facts)
        rw [hcpa] at hlev ⊢
        cases hcd : (a.level == t) with
        | true =>
            rw [hcd] at h
            cases h
            exact ⟨Nat.le_refl _, ⟨[], by simp⟩, FrameDescendsFrom.refl _⟩
        | false =>
            -- the head does not match while cp (in the tail) IS at `t`:
            -- the head's level would both be ≤ and equal to `t` — the
            -- front-most property of `checkpointAt`
            rw [hcd] at h
            exfalso
            have hmemcp : cp ∈ rest := checkpointAt_mem h
            have hdom := hchain.1 cp hmemcp
            have hclev : cp.level = t := checkpointAt_level h
            have hne : a.level ≠ t := by
              intro hc
              rw [hc] at hcd
              simp at hcd
            omega
      · -- cp' is in the tail: the chain's head dominance applies directly
        cases hcd : (a.level == t) with
        | true =>
            rw [hcd] at h
            cases h
            exact hchain.1 cp' hmem'
        | false =>
            rw [hcd] at h
            exact ih hchain.2 h hmem'

/-- Descent transitivity at `Identifies` level: if `cp` identifies `bs` at
`target` and `bs'`'s frame descends from `bs`'s (the assertion filter and
the closure only narrow), then `bs'`'s frame descends from `cp`'s frame —
the frame half of re-established checkpoint identity. -/
theorem _root_.LeanFzn.Solver.Propagation.DecisionCheckpoint.Identifies.descends_trans
    {cp : DecisionCheckpoint leaf} {bs bs' : BranchState leaf} {target : Nat}
    (h : cp.Identifies bs target)
    (hdesc : FrameDescendsFrom bs'.frame bs.frame) :
    FrameDescendsFrom bs'.frame cp.frame :=
  FrameDescendsFrom.trans hdesc h.2.2

/-- Trail-prefix transitivity: prepending `cp.trail` is preserved when the
trail is extended by entries at or above the target level. The restored
trail extends the branch's trail (restoration + the asserting entry +
closure appends), so the checkpoint's prefix witness re-establishes. -/
theorem Identifies_trail_extend {cp : DecisionCheckpoint leaf} {target : Nat}
    {bs bs' : BranchState leaf}
    (h : ∃ mid : List TrailEntry,
      bs.trail = cp.trail ++ mid ∧ ∀ e ∈ mid, target ≤ e.level)
    (hextra : ∃ extra : List TrailEntry,
      bs'.trail = bs.trail ++ extra ∧ ∀ e ∈ extra, target ≤ e.level) :
    ∃ mid : List TrailEntry,
      bs'.trail = cp.trail ++ mid ∧ ∀ e ∈ mid, target ≤ e.level := by
  obtain ⟨mid, hmid, hlev⟩ := h
  obtain ⟨extra, hextra, hlev'⟩ := hextra
  refine ⟨mid ++ extra, ?_, ?_⟩
  · rw [hextra, hmid, List.append_assoc]
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact hlev e he
    · exact hlev' e he

/-- THE RESTORATION-IDENTITY LEMMA: `Identifies` is preserved when the
restored branch extends the trail by target-level-or-higher entries and
its frame descends from the pre-jump frame. This is the exact shape the
`learnBackjumpAssert` transition must discharge for every SURVIVING
checkpoint; the level law is a separate premise because the runtime filter
(`cfg.checkpoints.filter fun cp => cp.level ≤ p.target`) keeps exactly the
checkpoints whose law already holds. -/
theorem _root_.LeanFzn.Solver.Propagation.DecisionCheckpoint.Identifies.restore_extend
    {cp : DecisionCheckpoint leaf} {target : Nat} {bs bs' : BranchState leaf}
    (h : cp.Identifies bs target)
    (hdesc : FrameDescendsFrom bs'.frame bs.frame)
    (hextra : ∃ extra : List TrailEntry,
      bs'.trail = bs.trail ++ extra ∧ ∀ e ∈ extra, target ≤ e.level) :
    cp.Identifies bs' target :=
  ⟨h.1, Identifies_trail_extend h.2.1 hextra,
    DecisionCheckpoint.Identifies.descends_trans h hdesc⟩

/-- Transitivity of sound classifications: composing two justified
transitions is justified, so a run of scheduler steps preserves every
still-possible solution. -/
theorem _root_.LeanFzn.Solver.Propagation.ClassificationSound.trans {leaf : Assignment → Bool}
    {p q r : List BranchFrame} {log : ExhaustionLog} {db : List Clause}
    (h₁ : ClassificationSound (leaf := leaf) p q log db)
    (h₂ : ClassificationSound (leaf := leaf) q r log db) :
    ClassificationSound (leaf := leaf) p r log db := by
  refine ⟨?_, ?_⟩
  · intro a ha hcov
    rcases h₁.retains a ha hcov with h | h | h
    · rcases h₂.retains a ha h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · intro a hcov
    exact h₁.noNew a (h₂.noNew a hcov)

/-! ## S3 — `perform` trail algebra and successor-checkpoint identity

The jump successor's trail is `perform`'s result: the executed plan
(checkpoint trail + the single asserting entry at the target level)
followed by the resumed closure's narrowing entries. The lemmas here are
the trail/identity algebra `Proofs/SchedulerBackjump.lean` composes into
the successor's `hreach`/`hident`; they carry no caller premise.

RESIDUAL NAMED HERE (owner S5, assembled at arm 5): to instantiate
`hident` for a SURVIVING checkpoint, the trail witness must compare the
survivor's trail with the SELECTED checkpoint's trail, which the successor
restores. `Identifies` alone provides only prefix witnesses against the
PRE-jump branch; closing the gap needs the checkpoint-chain invariant
"for `cp₁, cp₂` saved with `cp₁.level ≤ cp₂.level`, `cp₁.trail` is a
prefix of `cp₂.trail` with level bounds" (maintained wherever checkpoints
are pushed, S1/S2/S4; consumed by S5's step theorem). The frame-descent
conjunct needs the same chain data. Neither is assumed here. -/

/-- TRAIL EXTENSION OF THE CLOSURE: `explainedClosure` only APPENDS trail
entries, and every appended entry sits at the input state's own
(unchanged) level. This is the trail algebra the jump consumes: after the
checkpoint restoration and the asserting enqueue, the closure adds only
target-level entries, so the successor's trail extends the executed
trail without disturbing any checkpoint prefix below the target. -/
theorem explainedClosure_trail_extends (orig : List Domain) (original : List Clause)
    (props : List Propagator) (bs : BranchState leaf) :
    ∃ extra : List TrailEntry,
      (explainedClosure orig original props bs).trail = bs.trail ++ extra ∧
        ∀ e ∈ extra, e.level = bs.level := by
  suffices h : ∀ (fuel : Nat) (bs : BranchState leaf),
      Frame.mass bs.frame ≤ fuel →
      ∃ extra : List TrailEntry,
        (explainedClosure orig original props bs).trail = bs.trail ++ extra ∧
          ∀ e ∈ extra, e.level = bs.level from
    h (Frame.mass bs.frame) bs (Nat.le_refl _)
  intro fuel
  induction fuel with
  | zero =>
    intro bs hle
    rw [explainedClosure]
    split
    · exact ⟨[], by simp⟩
    · rename_i d _
      exfalso
      have := d.decreases
      omega
  | succ fuel ih =>
    intro bs hle
    rw [explainedClosure]
    split
    · exact ⟨[], by simp⟩
    · rename_i d _
      have hmass : Frame.mass (stepNarrowSync orig bs d).frame ≤ fuel := by
        simp only [stepNarrowSync_frame]
        have := d.decreases
        omega
      obtain ⟨extra, hextra, hlev⟩ := ih (stepNarrowSync orig bs d) hmass
      obtain ⟨ex, hex, hexl⟩ := stepNarrowSync_trail orig bs d
      refine ⟨{ literal := d.literal.norm, level := bs.level,
                reason := some { clause := d.reason } } :: (ex ++ extra), ?_, ?_⟩
      · rw [hextra, hex]
        simp [List.append_assoc]
      · intro e he
        rcases List.mem_cons.mp he with he | he
        · rw [he]
        · rcases List.mem_append.mp he with he | he
          · exact hexl e he
          · rw [hlev e he]
            simp only [stepNarrowSync_level]

/-- The explained closure only ever REPLACES the frame by a filtered frame:
every assignment still covered after the closure was already covered before
it. Fuel induction mirroring `explainedClosure_level`; the single-step
descent is `filterFrame_refines` on the deduction's own `filtered` call. -/
theorem explainedClosure_frame_descends (orig : List Domain) (original : List Clause)
    (props : List Propagator) (bs : BranchState leaf) :
    FrameDescendsFrom (explainedClosure orig original props bs).frame bs.frame := by
  suffices h : ∀ (fuel : Nat) (bs : BranchState leaf),
      Frame.mass bs.frame ≤ fuel →
      FrameDescendsFrom (explainedClosure orig original props bs).frame bs.frame from
    h (Frame.mass bs.frame) bs (Nat.le_refl _)
  intro fuel
  induction fuel with
  | zero =>
    intro bs hle
    rw [explainedClosure]
    split
    · exact FrameDescendsFrom.refl _
    · rename_i d _
      exfalso
      have := d.decreases
      omega
  | succ fuel ih =>
    intro bs hle
    rw [explainedClosure]
    split
    · exact FrameDescendsFrom.refl _
    · rename_i d _
      have hmass : Frame.mass (stepNarrowSync orig bs d).frame ≤ fuel := by
        simp only [stepNarrowSync_frame]
        have := d.decreases
        omega
      have hstep : FrameDescendsFrom (stepNarrowSync orig bs d).frame bs.frame :=
        fun a hc =>
          filterFrame_refines d.filtered (by simpa only [stepNarrowSync_frame] using hc)
      exact FrameDescendsFrom.trans (ih _ hmass) hstep

/-- SUCCESSOR-CHECKPOINT IDENTITY from its three named parts: the level
law (from the lookup), the restored-trail witness (the checkpoint-chain
residual above) and the frame descent. Exported so that S5's arm
instantiates `Identifies` at the successor without re-deriving the record
shape, and so the precise residual is named at the consumption site
instead of hidden in a hypothesis name. -/
theorem _root_.LeanFzn.Solver.Propagation.DecisionCheckpoint.identifies_of_parts {cp : DecisionCheckpoint leaf}
    {bs : BranchState leaf} {target : Nat}
    (hlev : cp.level = target)
    (hmid : ∃ mid : List TrailEntry,
      bs.trail = cp.trail ++ mid ∧ ∀ e ∈ mid, target ≤ e.level)
    (hdesc : FrameDescendsFrom bs.frame cp.frame) :
    cp.Identifies bs target :=
  ⟨hlev, hmid, hdesc⟩

end LeanFzn.Solver.UIP

/-
File: LeanFzn/Solver/Propagation/RestartProto.lean

Purpose (PLAN task S3 prototype: restarts retaining learned information):

  A STANDALONE, UNWIRED prototype of the S3 restart layer on top of the
  S0/S1 sparse-frame vocabulary (`DecisionProto.lean`) and the L0 clause
  lifecycle (`ClauseLifecycle.lean`). Nothing here is imported by any
  runtime module; no shared file is edited.

  What the prototype models, precisely:

  * the restart POLICY: a finite budget of permitted restarts; while the
    budget is positive a restart fires and the budget strictly decreases;
    once the budget is exhausted restarts are disabled and the transition
    is the monotone no-restart step (`advance`);
  * root restoration: the restarted frame is the ROOT box with the empty
    decision ledger (`order = []`, level `0`), the pending alternatives
    are dropped (the root covers them), and the checkpoint vocabulary is
    consistent (`Checkpoint.identifies_self`);
  * retained CLAUSES: the L0 lifecycle (`Lifecycle.active` /
    `Lifecycle.history`) is restarted with the ACTIVE set as seed
    (`Lifecycle.restart`), so every previously active clause is available
    after the restart and the history only grows; entailment is preserved
    (`wellFormed_restart_seed` derived from L0's `wellFormed_replay`);
  * COVERAGE: the restarted frontier is `[rootFrame]` and covers every
    assignment of the root box; any assignment covered by the pre-restart
    frontier (with frames sub-boxes of the root) is still covered after
    the restart and after every step (`step_frontier_covers`);
  * locked reasons and cached records: the `locked` clause list and the
    optimization-shaped `incumbent`/`bound` fields are carried through the
    restart unchanged;
  * a global lexicographic measure `(budget, (mass, level))` whose order
    is proved well-founded (`rankLt_wf`), strictly decreased by a restart
    (budget) and by a productive no-restart split (mass); after
    `budget` steps the run coincides with the no-restart run
    (`run_after_budget_eq_noRestart`).

  What the prototype does NOT model (stated honestly):

  * trail entries: `DecisionProto` has no `TrailEntry`; the prototype's
    trail/level vocabulary is `Frame.order` (the decision ledger), which a
    restart resets to `[]`; the runtime trail is out of the prototype's
    import cone;
  * propagation and conflict analysis: `advance` is the bare S1 split;
  * clause DELETION at restarts: the prototype retains all active clauses
    (the S3 baseline before the L1 deletion policy); no clause is dropped;
  * heuristic metadata transport: S2's `Meta` is deliberately NOT part of
    the semantic restart state and the restart never touches it (no value
    or clause is removed); runtime wiring keeps `Meta` on the scheduler
    configuration (S2 design §9.1).

  DAG check: `DecisionProto` imports only `FrontierSemantics`;
  `ClauseLifecycle` imports only `BranchState`; neither imports this
  module, so both imports are acyclic. `ActivityProto` is DAG-compatible
  as well but is NOT imported here: its `.olean` is absent in the closed
  build slot (no `lake build` is permitted by this task), and the restart
  layer needs nothing from it beyond the separation fact above.

  No `sorry`/`admit`/`axiom`/`native_decide`, no proof escapes.
-/
import LeanFzn.Legacy.Solver.Propagation.DecisionProto
import LeanFzn.Legacy.Solver.Propagation.ClauseLifecycle

namespace LeanFzn.Solver.Propagation.RestartProto
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DecisionProto

/-! ## §1 The restart policy and the restart state -/

/-- The restart policy and the restart-invariant state: a finite budget of
remaining restarts, the root box snapshot, the L0 clause lifecycle, the
locked reasons (`locked`), and the optimization-shaped incumbent/bound
fields that a restart must preserve. -/
structure RestartConfig where
  /-- remaining permitted restarts (finite budget) -/
  budget : Nat
  /-- the root box snapshot (the frame a restart restores) -/
  root : Frame
  /-- L0 lifecycle: active search database + retained history -/
  life : ClauseLifecycle.Lifecycle
  /-- locked reasons (carried unchanged across a restart) -/
  locked : List Clause
  /-- incumbent assignment (optimization-shaped; carried unchanged) -/
  incumbent : Option Assignment
  /-- incumbent bound (optimization-shaped; carried unchanged) -/
  bound : Option Int

/-- The root frame a restart restores: the root box with the empty decision
ledger (level `0`). -/
def RestartConfig.rootFrame (c : RestartConfig) : Frame :=
  { doms := c.root.doms, order := [] }

/-- The restart state: the policy plus the current frame and the pending
alternatives (the frontier tail). -/
structure RState where
  conf : RestartConfig
  frame : Frame
  pending : List Frame

/-- Remaining restart budget. -/
def RState.budget (st : RState) : Nat := st.conf.budget

/-- The restart gate: `true` exactly while the budget is positive. -/
def RState.canRestart (st : RState) : Bool := decide (0 < st.conf.budget)

/-- The current frontier: the current frame followed by the pending
alternatives. -/
def RState.frontier (st : RState) : List Frame := st.frame :: st.pending

/-- THE RESTART: restore the root frame, drop the pending alternatives, keep
the locked reasons / incumbent / bound and the rest of the policy, spend
one budget unit, and rebuild the L0 lifecycle from its active set (every
previously active clause is retained; the history only grows). -/
def RState.restart (st : RState) : RState :=
  { conf :=
      { st.conf with
        budget := st.conf.budget - 1
        life := ClauseLifecycle.Lifecycle.restart st.conf.life.active st.conf.life }
    frame := st.conf.rootFrame
    pending := [] }

@[simp] theorem RState.restart_frame (st : RState) :
    (st.restart).frame = st.conf.rootFrame := rfl

@[simp] theorem RState.restart_pending (st : RState) :
    (st.restart).pending = [] := rfl

@[simp] theorem RState.restart_budget (st : RState) :
    (st.restart).budget = st.budget - 1 := rfl

@[simp] theorem RState.restart_frontier (st : RState) :
    (st.restart).frontier = [st.conf.rootFrame] := rfl

@[simp] theorem RState.restart_incumbent (st : RState) :
    (st.restart).conf.incumbent = st.conf.incumbent := rfl

@[simp] theorem RState.restart_bound (st : RState) :
    (st.restart).conf.bound = st.conf.bound := rfl

@[simp] theorem RState.restart_locked (st : RState) :
    (st.restart).conf.locked = st.conf.locked := rfl

@[simp] theorem RState.restart_root (st : RState) :
    (st.restart).conf.root = st.conf.root := rfl

/-! ## §2 Root restoration and the checkpoint/level vocabulary -/

theorem RestartConfig.rootFrame_doms (c : RestartConfig) :
    c.rootFrame.doms = c.root.doms := rfl

theorem RestartConfig.rootFrame_order (c : RestartConfig) :
    c.rootFrame.order = [] := rfl

theorem RestartConfig.rootFrame_level (c : RestartConfig) :
    c.rootFrame.level = 0 := rfl

/-- The restarted frame is the root box. -/
theorem RState.restart_frame_doms (st : RState) :
    (st.restart).frame.doms = st.conf.root.doms := rfl

/-- The restarted frame is at level `0`: the decision ledger is empty. -/
theorem RState.restart_level (st : RState) : (st.restart).frame.level = 0 := rfl

/-- The restarted frame's decision order (the prototype's trail vocabulary)
is empty. -/
theorem RState.restart_order (st : RState) : (st.restart).frame.order = [] := rfl

/-- The checkpoint vocabulary is consistent after the restart: the
restarted frame's own checkpoint identifies it. -/
theorem RState.restart_checkpoint_identifies (st : RState) :
    (Checkpoint.ofFrame (st.restart).frame).Identifies (st.restart).frame :=
  Checkpoint.identifies_self _

/-- The restarted checkpoint sits at level `0`. -/
theorem RState.restart_checkpoint_level (st : RState) :
    (Checkpoint.ofFrame (st.restart).frame).level = 0 := rfl

/-- The restarted checkpoint's box is the root box. -/
theorem RState.restart_checkpoint_doms (st : RState) :
    (Checkpoint.ofFrame (st.restart).frame).doms = st.conf.root.doms := rfl

/-! ## §3 The finite-budget policy -/

theorem RState.canRestart_eq_true_iff (st : RState) :
    st.canRestart = true ↔ 0 < st.budget := by
  simp [RState.canRestart, RState.budget]

theorem RState.canRestart_false_of_budget_zero {st : RState} (h : st.budget = 0) :
    st.canRestart = false := by
  simp only [RState.canRestart, RState.budget] at h ⊢
  rw [h]
  rfl

/-- Throwing a restart strictly decreases the budget. -/
theorem RState.restart_budget_lt {st : RState} (h : 0 < st.budget) :
    (st.restart).budget < st.budget := by
  rw [RState.restart_budget]
  exact Nat.sub_lt h Nat.zero_lt_one

/-- A restart from a one-unit budget exhausts it (the tiny-model "fires
once" fact, in general form). -/
theorem RState.restart_budget_eq_zero_of_one {st : RState} (h : st.budget = 1) :
    (st.restart).budget = 0 := by
  rw [RState.restart_budget, h]

/-! ## §4 Retention: the history only grows, active clauses stay available -/

/-- The active-set projection of `Lifecycle.replay` (the companion of the
L0 `Lifecycle.replay_history`): replaying `cs` prepends `cs.reverse`. -/
theorem replay_active (cs : List Clause) (lc : ClauseLifecycle.Lifecycle) :
    (ClauseLifecycle.Lifecycle.replay cs lc).active = cs.reverse ++ lc.active := by
  induction cs generalizing lc with
  | nil => rfl
  | cons c cs ih =>
      rw [ClauseLifecycle.Lifecycle.replay, List.foldl_cons]
      change (ClauseLifecycle.Lifecycle.replay cs
        (ClauseLifecycle.Lifecycle.insert c lc)).active =
        (c :: cs).reverse ++ lc.active
      rw [ih, ClauseLifecycle.Lifecycle.insert_active, List.reverse_cons,
        List.append_assoc, List.singleton_append]

/-- The restarted lifecycle's active set is the seed in reverse order. -/
theorem restart_active_eq (seed : List Clause) (lc : ClauseLifecycle.Lifecycle) :
    (ClauseLifecycle.Lifecycle.restart seed lc).active = seed.reverse := by
  unfold ClauseLifecycle.Lifecycle.restart
  rw [replay_active, List.append_nil]

/-- Membership in a restarted active set is membership in its seed. -/
theorem restart_mem_active_iff {seed : List Clause} {lc : ClauseLifecycle.Lifecycle}
    {c : Clause} : c ∈ (ClauseLifecycle.Lifecycle.restart seed lc).active ↔ c ∈ seed := by
  rw [restart_active_eq, List.mem_reverse]

/-- RETENTION: every clause active before the restart is active after it
and is certified in the restarted history. -/
theorem RState.restart_retains_active {st : RState} {c : Clause}
    (h : c ∈ st.conf.life.active) :
    c ∈ (st.restart).conf.life.active ∧ c ∈ (st.restart).conf.life.history := by
  constructor
  · exact restart_mem_active_iff.mpr h
  · show c ∈ (ClauseLifecycle.Lifecycle.restart st.conf.life.active st.conf.life).history
    rw [ClauseLifecycle.Lifecycle.restart_history]
    exact List.mem_append.mpr (Or.inl (List.mem_reverse.mpr h))

/-- HISTORY GROWTH: the restart's history contains the old history. -/
theorem RState.restart_historyGrowth (st : RState) :
    ClauseLifecycle.Lifecycle.HistoryGrowth st.conf.life (st.restart).conf.life :=
  ClauseLifecycle.Lifecycle.historyGrowth_restart st.conf.life.active st.conf.life

/-- Every clause certified before the restart stays certified after it. -/
theorem RState.restart_history_mem {st : RState} {c : Clause}
    (h : c ∈ st.conf.life.history) : c ∈ (st.restart).conf.life.history :=
  RState.restart_historyGrowth st c h

/-- The generalized L0 restart obligation: restarting with an arbitrary
entailed seed `cs` preserves lifecycle well-formedness (L0's
`wellFormed_replay` with the empty-active base of `Lifecycle.restart`). -/
theorem wellFormed_restart_seed {leaf : Assignment → Bool} {seed : List Clause}
    {lc : ClauseLifecycle.Lifecycle} {cs : List Clause}
    (h : ClauseLifecycle.Lifecycle.WellFormed leaf seed lc)
    (hcs : ∀ c ∈ cs, ∀ a, leaf a = true → c.SatisfiedBy a) :
    ClauseLifecycle.Lifecycle.WellFormed leaf seed
      (ClauseLifecycle.Lifecycle.restart cs lc) := by
  unfold ClauseLifecycle.Lifecycle.restart
  refine ClauseLifecycle.Lifecycle.wellFormed_replay
    (lc := { active := [], history := lc.history }) ⟨?_, h.2.1, h.2.2⟩ hcs
  intro c hc
  cases hc

/-- RESTART WELL-FORMEDNESS: if the lifecycle was well-formed before the
restart, it is well-formed after it (entailment of seed and history is
preserved; the active set is rebuilt from entailed clauses only). -/
theorem RState.restart_wellFormed {st : RState} {leaf : Assignment → Bool}
    {seed : List Clause} (h : ClauseLifecycle.Lifecycle.WellFormed leaf seed st.conf.life) :
    ClauseLifecycle.Lifecycle.WellFormed leaf seed (st.restart).conf.life :=
  wellFormed_restart_seed (cs := st.conf.life.active) h
    (fun c hc a ha => ClauseLifecycle.Lifecycle.wellFormed_active_entailed h c hc a ha)

/-- Every clause active after the restart is entailed by the leaf. -/
theorem RState.restart_active_entailed {st : RState} {leaf : Assignment → Bool}
    {seed : List Clause} (h : ClauseLifecycle.Lifecycle.WellFormed leaf seed st.conf.life) :
    LearnedEntailed leaf (st.restart).conf.life.active :=
  ClauseLifecycle.Lifecycle.wellFormed_active_entailed (RState.restart_wellFormed h)

/-- LOCKED REASONS stay consistent across the jump: the locked list is
unchanged, so any property it had (e.g. membership in the history) still
holds. -/
theorem RState.restart_locked_of {st : RState} {P : Clause → Prop}
    (h : ∀ c ∈ st.conf.locked, P c) : ∀ c ∈ (st.restart).conf.locked, P c := by
  intro c hc
  exact h c hc

/-- Locked reasons recorded in the history stay certified after a
restart. -/
theorem RState.restart_locked_in_history {st : RState}
    (h : ∀ c ∈ st.conf.locked, c ∈ st.conf.life.history) :
    ∀ c ∈ (st.restart).conf.locked, c ∈ (st.restart).conf.life.history :=
  RState.restart_locked_of (fun c hc => RState.restart_history_mem (h c hc))

/-! ## §5 Coverage: the restart loses no covered assignment -/

/-- An assignment is covered by a frontier when some frame of the frontier
covers it. -/
def FrontierCovers (fs : List Frame) (a : Assignment) : Prop :=
  ∃ f ∈ fs, f.Covers a

/-- A frame is a sub-box of a root box: same slot count and pointwise
domain inclusion. -/
def Frame.SubBox (f : Frame) (root : List Domain) : Prop :=
  f.doms.length = root.length ∧
    ∀ i d, f.doms[i]? = some d → ∀ v ∈ d, v ∈ root.getD i Dom.empty

/-- Pointwise monotonicity of `allAssigns`: a pointwise sub-box enumerates
a subset of the root's assignments. -/
theorem allAssigns_mono {ds root : List Domain} (hlen : ds.length = root.length)
    (hsub : ∀ i d, ds[i]? = some d → ∀ v ∈ d, v ∈ root.getD i Dom.empty) :
    ∀ a, a ∈ allAssigns ds → a ∈ allAssigns root := by
  induction ds generalizing root with
  | nil =>
      intro a ha
      cases root with
      | nil => simpa using ha
      | cons r rs => simp at hlen
  | cons d ds ih =>
      intro a ha
      cases root with
      | nil => simp at hlen
      | cons r rs =>
          obtain ⟨v, hv, a', ha', rfl⟩ := mem_allAssigns_cons_iff.mp ha
          rw [mem_allAssigns_cons_iff]
          refine ⟨v, ?_, a', ?_, rfl⟩
          · have h0 := hsub 0 d (by simp) v hv
            simpa using h0
          · apply ih (by simpa using hlen)
            · intro i d' hd' w hw
              have := hsub (i + 1) d' (by simpa using hd') w hw
              simpa using this
            · exact ha'

/-- Every assignment covered by a sub-box of the root lies in the root
box. -/
theorem Frame.SubBox.covers_root {f : Frame} {root : List Domain}
    (h : Frame.SubBox f root) : ∀ a, f.Covers a → a ∈ allAssigns root :=
  allAssigns_mono h.1 h.2

/-- The root frame is a sub-box of the root box. -/
theorem RestartConfig.rootFrame_subBox (c : RestartConfig) :
    Frame.SubBox c.rootFrame c.root.doms := by
  refine ⟨rfl, ?_⟩
  intro i d hd v hv
  have hd' : c.root.doms[i]? = some d := by simpa [RestartConfig.rootFrame] using hd
  rw [List.getD_eq_getElem?_getD, hd']
  exact hv

/-- COVERAGE OF THE WHOLE ROOT BOX: the restarted frontier covers every
assignment of the root box. -/
theorem RState.restart_covers_all {st : RState} {a : Assignment}
    (h : a ∈ allAssigns st.conf.root.doms) :
    FrontierCovers (st.restart).frontier a := by
  refine ⟨st.conf.rootFrame, by simp [RState.restart_frontier], ?_⟩
  simpa [Frame.Covers, RestartConfig.rootFrame] using h

/-- NO COVERED ASSIGNMENT IS LOST: every assignment covered by the
pre-restart frontier (whose frames are sub-boxes of the root) is covered
by the restarted frontier. In particular, no leaf solution of the root box
that was still in the search space disappears. -/
theorem RState.restart_covers_of_frontier {st : RState} {a : Assignment}
    (hsub : ∀ f ∈ st.frontier, Frame.SubBox f st.conf.root.doms)
    (h : FrontierCovers st.frontier a) :
    FrontierCovers (st.restart).frontier a := by
  obtain ⟨f, hf, hc⟩ := h
  exact RState.restart_covers_all ((Frame.SubBox.covers_root (hsub f hf)) a hc)

/-! ## §6 The no-restart step and its coverage -/

/-- The no-restart transition: split the current frame (S1 min-cardinality
split), move to the pinned child, and push the retired sibling. When no
live slot exists the step stutters (the terminal state). -/
def RState.advance (st : RState) : RState :=
  match st.frame.split with
  | none => st
  | some (k, v, vs) =>
      { st with
        frame := st.frame.pin k v
        pending := st.frame.retire k vs :: st.pending }

/-- The shape of an advancing step at a split. -/
theorem RState.advance_eq_of_split {st : RState} {k : Nat} {v : Value} {vs : Domain}
    (h : st.frame.split = some (k, v, vs)) :
    st.advance =
      { st with
        frame := st.frame.pin k v
        pending := st.frame.retire k vs :: st.pending } := by
  unfold RState.advance
  rw [h]

/-- A no-restart step never changes the policy. -/
theorem RState.advance_budget (st : RState) : st.advance.budget = st.budget := by
  unfold RState.advance
  split <;> rfl

/-- ADVANCE COVERAGE: the no-restart split replaces the parent frame by its
two children, so no covered assignment is lost. -/
theorem RState.advance_frontier_covers {st : RState} {a : Assignment}
    (h : FrontierCovers st.frontier a) : FrontierCovers st.advance.frontier a := by
  unfold RState.advance
  cases hs : st.frame.split with
  | none => exact h
  | some p =>
      obtain ⟨k, v, vs⟩ := p
      obtain ⟨f, hf, hc⟩ := h
      rcases List.mem_cons.mp hf with rfl | hf
      · rcases (Frame.split_covers hs a).mp hc with h' | h'
        · exact ⟨st.frame.pin k v, List.mem_cons_self .., h'⟩
        · exact ⟨st.frame.retire k vs,
            List.mem_cons_of_mem _ (List.mem_cons_self ..), h'⟩
      · exact ⟨f, List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ hf), hc⟩

/-! ## §7 The full step: restart while budgeted, then the monotone search -/

/-- The uniform transition: restart while a budget unit remains, otherwise
the no-restart step. -/
def RState.step (st : RState) : RState :=
  if st.canRestart then st.restart else st.advance

theorem RState.step_eq_restart_of_canRestart {st : RState} (h : st.canRestart = true) :
    st.step = st.restart := by
  simp [RState.step, h]

theorem RState.step_eq_advance_of_not_canRestart {st : RState}
    (h : ¬ st.canRestart = true) : st.step = st.advance := by
  simp [RState.step, h]

/-- While the budget is positive the step is a restart (the policy in
general form). -/
theorem RState.step_eq_restart_of_budget_pos {st : RState} (h : 0 < st.budget) :
    st.step = st.restart :=
  RState.step_eq_restart_of_canRestart ((RState.canRestart_eq_true_iff st).mpr h)

/-- THE POLICY DISABLES RESTARTS AFTER THE BUDGET: at budget `0` the step
is exactly the no-restart step. -/
theorem RState.step_eq_advance_of_budget_zero {st : RState} (h : st.budget = 0) :
    st.step = st.advance :=
  RState.step_eq_advance_of_not_canRestart (by
    intro hc
    have hpos := (RState.canRestart_eq_true_iff st).mp hc
    omega)

/-- The full step preserves frontier coverage (the restart covers the
root, the advance covers its parent) whenever the frontier frames are
sub-boxes of the root. -/
theorem RState.step_frontier_covers {st : RState} {a : Assignment}
    (hsub : ∀ f ∈ st.frontier, Frame.SubBox f st.conf.root.doms)
    (h : FrontierCovers st.frontier a) : FrontierCovers st.step.frontier a := by
  unfold RState.step
  by_cases hc : st.canRestart = true
  · rw [if_pos hc]
    exact RState.restart_covers_of_frontier hsub h
  · rw [if_neg hc]
    exact RState.advance_frontier_covers h

/-! ## §8 The global well-founded measure -/

/-- The global rank: `(restart budget, (frame mass, level))`, read
lexicographically. The budget is the most significant component, so every
restart decreases the rank regardless of the frame; once the budget is
spent the existing S1 mass/level measure governs. -/
def RState.rank (st : RState) : Nat × (Nat × Nat) :=
  (st.budget, (st.frame.mass, st.frame.level))

/-- The lexicographic order on `Nat × (Nat × Nat)` used for `RState.rank`. -/
def RankLt (a b : Nat × (Nat × Nat)) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ (a.2.1 < b.2.1 ∨ (a.2.1 = b.2.1 ∧ a.2.2 < b.2.2)))

/-- The lex order is the core product well-founded relation (definitional
identification), so well-foundedness is inherited, not assumed. -/
theorem rankLt_of_inst {a b : Nat × (Nat × Nat)} (h : RankLt a b) :
    (inferInstance : WellFoundedRelation (Nat × (Nat × Nat))).rel a b := by
  have hrel : (inferInstance : WellFoundedRelation (Nat × (Nat × Nat))).rel =
      Prod.Lex (sizeOfWFRel.rel (α := Nat))
        (Prod.Lex (sizeOfWFRel.rel (α := Nat)) (sizeOfWFRel.rel (α := Nat))) := rfl
  rw [hrel]
  show Prod.Lex (sizeOfWFRel.rel (α := Nat))
    (Prod.Lex (sizeOfWFRel.rel (α := Nat)) (sizeOfWFRel.rel (α := Nat)))
    (a.1, a.2) (b.1, b.2)
  rcases h with h | ⟨h1, h | ⟨h2, h3⟩⟩
  · exact Prod.Lex.left (b₁ := a.2) (b₂ := b.2) h
  · rw [← h1]
    exact Prod.Lex.right (a := a.1) (Prod.Lex.left (b₁ := a.2.2) (b₂ := b.2.2) h)
  · rw [← h1]
    show Prod.Lex (sizeOfWFRel.rel (α := Nat))
      (Prod.Lex (sizeOfWFRel.rel (α := Nat)) (sizeOfWFRel.rel (α := Nat)))
      (a.1, (a.2.1, a.2.2)) (a.1, (b.2.1, b.2.2))
    rw [← h2]
    exact Prod.Lex.right (a := a.1) (Prod.Lex.right (a := a.2.1) h3)

/-- The global measure is well-founded. -/
theorem rankLt_wf : WellFounded RankLt :=
  Subrelation.wf (fun {_ _} h => rankLt_of_inst h)
    (inferInstance : WellFoundedRelation (Nat × (Nat × Nat))).wf

/-- A RESTART STRICTLY DECREASES THE RANK (first component: the budget). -/
theorem RState.restart_rank_lt {st : RState} (h : 0 < st.budget) :
    RankLt st.restart.rank st.rank := by
  left
  show (st.restart).budget < st.budget
  exact RState.restart_budget_lt h

/-- A productive no-restart split strictly decreases the rank (second
component: the frame mass). -/
theorem RState.advance_rank_lt {st : RState} {k : Nat} {v : Value} {vs : Domain}
    (h : st.frame.split = some (k, v, vs)) : RankLt st.advance.rank st.rank := by
  right
  refine ⟨?_, Or.inl ?_⟩
  · show (st.advance).budget = st.budget
    exact RState.advance_budget st
  · show (st.advance).frame.mass < st.frame.mass
    rw [RState.advance_eq_of_split h]
    exact (Frame.split_mass_lt h).1

/-- Every productive step decreases the global rank: a restart via the
budget, a split via the mass. -/
theorem RState.step_rank_lt (st : RState)
    (h : st.canRestart = true ∨ ∃ k v vs, st.frame.split = some (k, v, vs)) :
    RankLt st.step.rank st.rank := by
  by_cases hc : st.canRestart = true
  · rw [RState.step_eq_restart_of_canRestart hc]
    exact RState.restart_rank_lt ((RState.canRestart_eq_true_iff st).mp hc)
  · rcases h with h' | ⟨k, v, vs, hs⟩
    · exact absurd h' hc
    · rw [RState.step_eq_advance_of_not_canRestart hc]
      exact RState.advance_rank_lt hs

/-! ## §9 Runs: budget exhaustion and the no-restart regime -/

/-- The full run: `n` steps of `step`. -/
def RState.run (st : RState) : Nat → RState
  | 0 => st
  | n + 1 => (st.run n).step

/-- The no-restart run: `n` steps of `advance`. -/
def RState.runNoRestart (st : RState) : Nat → RState
  | 0 => st
  | n + 1 => (st.runNoRestart n).advance

theorem RState.run_succ (st : RState) (n : Nat) :
    st.run (n + 1) = (st.run n).step := rfl

theorem RState.runNoRestart_succ (st : RState) (n : Nat) :
    st.runNoRestart (n + 1) = (st.runNoRestart n).advance := rfl

/-- Runs compose. -/
theorem RState.run_add (st : RState) (m n : Nat) :
    st.run (m + n) = (st.run m).run n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.add_succ, RState.run_succ, ih, RState.run_succ]

/-- The no-restart run never spends budget. -/
theorem RState.runNoRestart_budget (st : RState) (n : Nat) :
    (st.runNoRestart n).budget = st.budget := by
  induction n with
  | zero => rfl
  | succ n ih => rw [RState.runNoRestart_succ, RState.advance_budget, ih]

/-- After `n` steps the budget is at most `budget - n`. -/
theorem RState.run_budget_le (st : RState) :
    ∀ n, (st.run n).budget ≤ st.budget - n := by
  intro n
  induction n with
  | zero => simp [RState.run]
  | succ n ih =>
      rw [RState.run_succ]
      by_cases hb : (st.run n).budget = 0
      · have hstep : (st.run n).step.budget = 0 := by
          rw [RState.step_eq_advance_of_budget_zero hb, RState.advance_budget, hb]
        rw [hstep]
        exact Nat.zero_le _
      · have hpos : 0 < (st.run n).budget := Nat.pos_of_ne_zero hb
        have hstep : (st.run n).step.budget = (st.run n).budget - 1 := by
          rw [RState.step_eq_restart_of_canRestart
            ((RState.canRestart_eq_true_iff _).mpr hpos)]
          rfl
        rw [hstep]
        have hsub := Nat.sub_le_sub_right ih 1
        have hsub' : st.budget - n - 1 = st.budget - (n + 1) := by omega
        omega

/-- BUDGET EXHAUSTION: after `budget` steps no restart unit remains. -/
theorem RState.run_budget_eq_zero (st : RState) : (st.run st.budget).budget = 0 := by
  have h := RState.run_budget_le st st.budget
  omega

/-- At exhaustion the restart gate is off. -/
theorem RState.run_canRestart_false (st : RState) : (st.run st.budget).canRestart = false :=
  RState.canRestart_false_of_budget_zero (RState.run_budget_eq_zero st)

/-- THE BUDGET-EXHAUSTED REGIME IS THE MONOTONE SEARCH: from a budget-zero
state the full run coincides with the no-restart run, step for step. -/
theorem RState.run_eq_runNoRestart_of_budget_zero {st : RState} (h : st.budget = 0) :
    ∀ n, st.run n = st.runNoRestart n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [RState.run_succ, RState.runNoRestart_succ, ih]
      rw [RState.step_eq_advance_of_budget_zero (by
        rw [RState.runNoRestart_budget]
        exact h)]

/-- THE RESTARTED RUN MATCHES THE NO-RESTART RUN AFTER EXHAUSTION: the
first `budget` steps spend the restarts (each decreasing the rank), and
from there the run is the already-certified monotone no-restart run. -/
theorem RState.run_after_budget_eq_noRestart (st : RState) (n : Nat) :
    st.run (st.budget + n) = (st.run st.budget).runNoRestart n := by
  rw [RState.run_add]
  exact RState.run_eq_runNoRestart_of_budget_zero (RState.run_budget_eq_zero st) n

/-! ## §10 Tiny-model demonstration -/

/-- The tiny root box: a two-value int slot and a two-value bool slot. -/
def tinyRoot : Frame :=
  { doms := [Dom.ofList [Value.int 0, Value.int 1],
      Dom.ofList [Value.bool true, Value.bool false]],
    order := [] }

/-- A retained (learned) clause of the tiny model. -/
def tinyClause : Clause := [posNe 0 1]

/-- The tiny policy: a one-restart budget, one retained/active clause, one
locked reason, and an incumbent/bound pair to preserve. -/
def tinyConf : RestartConfig :=
  { budget := 1
    root := tinyRoot
    life := ClauseLifecycle.Lifecycle.empty.insert tinyClause
    locked := [tinyClause]
    incumbent := some [Value.int 1, Value.bool true]
    bound := some 5 }

/-- A pre-restart state on a narrowed frame (slot 0 pinned, level 1). -/
def tinyState : RState :=
  { conf := tinyConf
    frame := { doms := [Dom.ofList [Value.int 0],
        Dom.ofList [Value.bool true, Value.bool false]], order := [0] }
    pending := [] }

theorem tiny_canRestart : tinyState.canRestart = true := rfl

theorem tiny_restart_budget : tinyState.restart.budget = 0 := rfl

theorem tiny_restart_frame : tinyState.restart.frame = tinyRoot := rfl

theorem tiny_restart_level : tinyState.restart.frame.level = 0 := rfl

theorem tiny_restart_order : tinyState.restart.frame.order = [] := rfl

/-- The first step fires the restart; the second is the no-restart step. -/
theorem tiny_first_step : tinyState.step = tinyState.restart := rfl

theorem tiny_second_step : (tinyState.step).step = (tinyState.step).advance :=
  RState.step_eq_advance_of_budget_zero rfl

/-- One restart fires and the budget is spent: the gate is off afterwards. -/
theorem tiny_restart_once : (tinyState.step).canRestart = false := by
  rw [tiny_first_step]
  exact RState.canRestart_false_of_budget_zero rfl

/-- The restart preserves the incumbent, the bound and the locked reasons. -/
theorem tiny_preserves_opt : (tinyState.restart).conf.incumbent =
    some [Value.int 1, Value.bool true] ∧ (tinyState.restart).conf.bound = some 5 ∧
    (tinyState.restart).conf.locked = [tinyClause] :=
  ⟨rfl, rfl, rfl⟩

/-- RETENTION on the tiny model: the learned clause is active and certified
after the restart. -/
theorem tiny_retained : tinyClause ∈ (tinyState.restart).conf.life.active ∧
    tinyClause ∈ (tinyState.restart).conf.life.history :=
  RState.restart_retains_active (by simp [tinyState, tinyConf])

/-- COVERAGE on the tiny model: the assignment `[0, true]` of the root box
is covered after the restart. -/
theorem tiny_covers :
    FrontierCovers (tinyState.restart).frontier [Value.int 0, Value.bool true] :=
  RState.restart_covers_all (by
    show [Value.int 0, Value.bool true] ∈ allAssigns
      [Dom.ofList [Value.int 0, Value.int 1],
        Dom.ofList [Value.bool true, Value.bool false]]
    rw [mem_allAssigns_cons_iff]
    refine ⟨Value.int 0, by simp, [Value.bool true], ?_, rfl⟩
    rw [mem_allAssigns_cons_iff]
    exact ⟨Value.bool true, by simp, [], by simp [allAssigns], rfl⟩)

/-- The restarted run's split: slot 0 pinned to `0`, sibling `[1]`. -/
theorem tiny_split : (tinyState.step).frame.split =
    some (0, Value.int 0, Dom.ofList [Value.int 1]) := rfl

/-- PROGRESS after the restart: the no-restart split strictly decreases
both the frame mass and the global rank. -/
theorem tiny_advance_progress :
    (tinyState.step).advance.frame.mass < (tinyState.step).frame.mass ∧
    RankLt (tinyState.step).advance.rank (tinyState.step).rank :=
  ⟨(Frame.split_mass_lt tiny_split).1, RState.advance_rank_lt tiny_split⟩

/-- The restart itself strictly decreases the global rank. -/
theorem tiny_restart_rank : RankLt tinyState.restart.rank tinyState.rank :=
  RState.restart_rank_lt (by decide)

/-- THE EXHAUSTED-BUDGET RUN MATCHES THE NO-RESTART RUN on the tiny model. -/
theorem tiny_run_matches (n : Nat) :
    tinyState.run (tinyState.budget + n) =
      (tinyState.run tinyState.budget).runNoRestart n :=
  RState.run_after_budget_eq_noRestart tinyState n

/-- After the budget the gate is off. -/
theorem tiny_run_exhausted : (tinyState.run tinyState.budget).canRestart = false :=
  RState.run_canRestart_false tinyState

end LeanFzn.Solver.Propagation.RestartProto

/-
File: LeanFzn/Solver/Propagation/BackjumpFrontier.lean

Purpose:
  The backjump scheduler for the explained frontier. Frozen interface:

  * `BackjumpPlan` / `BackjumpPlan.execute` — exact restoration of the
    saved branch state at the target level plus a single asserting
    enqueue; globally entailed learned clauses are retained;
  * `BackjumpPlan.perform` (C1, PLAN P1.3 item 3) — the COMPLETE
    learn/backjump/assert transition: insert the learned clause into the
    global database, restore the target frame and trail, narrow by the
    assertion, keep the asserting entry's recorded reason, and resume
    explained propagation. Forward correctness is task C2's obligation;
    this module only fixes the shape;
  * `DecisionCheckpoint` / `DecisionCheckpoint.Identifies` /
    `BackjumpPlan.Identifies` / `checkpointAt` (C1, INTERFACES §2.4):
    checkpoint identity is a theorem about saved state, so the former
    caller premise `hcpLevel : p.checkpoint.level = p.target` is
    discharged by the scheduler and no longer appears in C2's statements;
  * `DeadRegion` / `ExhaustionLog` / `ExhaustionLog.Sound` (C1,
    INTERFACES §2.6): the permanent exhaustion record as *rich regions*
    with semantic soundness — no logged region contains a leaf solution,
    so a region can justify deleting a pending alternative but can never
    be used to "cover" a surviving one;
  * `AlternativeClass` / `classifyAlternatives` — the classification of
    pending alternatives into retained, previously exhausted, and
    clause-excluded, together with the coverage contract that a
    classification must satisfy;
  * `FallbackContract` — chronological continuation when analysis
    cannot produce an asserting result: coverage preservation plus a
    strictly decreasing `frontierCost` (no fuel, no restart counter).

REGION COMPUTABILITY NOTE (C1 report item; RESOLVED by the C2b-int
repair). The classical frame region `DeadRegion.ofFrame`
(`{ mem := fun a => decide (FrameCovers f a) }` under
`Classical.propDecidable`) is not computable: the runtime registration
sites must stay computable because `Tests.UIP.OracleFixtures` evaluates
`conflictStep` in its compiled `main`. This module now ALSO provides
`DeadRegion.byFrame`, a COMPUTABLE frame region: its membership runs the
in-cone structural equality `valueEqBLocal`/`valuesEqBLocal` over the
frame's enumerable assignment list (`DeadRegion.coversB`). The local
soundness proof never leaves the cone. The checker's full equality
soundness theorem `value_eqB_iff` (`LeanFzn/FznSolution.lean`) is the
OUT-OF-CONE original that this in-cone copy replaces; `Value.eqB` itself
is also out of reach here only through that missing soundness lemma.
`byFrame` is SOUND for every frame and EXACT for bool/int-valued frames;
for nested values (`.setOfInt`, `.array`) it conservatively answers
`false`, which can never exclude a live assignment (a completeness gap,
never a soundness one). The literal-based regions (`DeadRegion.byAllTrue`,
`byFalse`, `below`, `above`, `byPrefix`) remain for proof-term use, and
the SOUNDNESS obligation is unchanged: `ExhaustionLog.Sound` plus the
registration lemma `ExhaustionLog.register_sound`.

Dependencies:
  - LeanFzn.Solver.Propagation.ConflictResolution (P1.C): the analysis contract.
  - LeanFzn.Solver.Propagation.Frontier: `frontierCost`, `frontierCost_cons`.
  - LeanFzn.Solver.Propagation.ExplainedPropagation (A2), transitive through
    `ConflictResolution` and imported explicitly here: `narrowState`,
    `explainedClosure`, `valueLiteral`.
  - LeanFzn.Solver.Propagation.FrameFilter: `filterFrame`, `Frame.domains`.

DAG:
  ConflictResolution + Frontier -> BackjumpFrontier
  -> Proofs.BackjumpFrontier -> SchedulerState -> SchedulerStep
  -> the integrated driver.
-/

import LeanFzn.Legacy.Solver.Propagation.ConflictResolution
import LeanFzn.Solver.Propagation.Frontier
import LeanFzn.Legacy.Solver.Propagation.ExplainedPropagation
import LeanFzn.Solver.Propagation.FrameFilter
import LeanFzn.Legacy.Solver.Propagation.FrameSync
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation


open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-! ## Exact restoration and the asserting enqueue -/

/-- A backjump plan: restore the exact state saved at `target`, then
enqueue the learned clause's asserting literal with its reason. The
`checkpoint` is the branch state as it was when level `target` was
current — the saved history that makes restoration exact rather than
reconstructed. -/
structure BackjumpPlan (leaf : Assignment → Bool) where
  /-- the level to restore -/
  target : Nat
  /-- the exact state saved at that level -/
  checkpoint : BranchState leaf
  /-- the literal the learned clause asserts after restoration -/
  asserting : Literal
  /-- the learned clause, used as the reason -/
  learned : Clause

/-- The asserting entry to append: none when the normalized asserting literal is
already the literal of a restored-trail entry (runtime guard keeping the trail
literal-distinct). -/
def BackjumpPlan.assertEntry (p : BackjumpPlan leaf) : TrailEntry :=
  { literal := p.asserting.norm, level := p.target,
    reason := some { clause := p.learned } }

def BackjumpPlan.assertExtra (p : BackjumpPlan leaf) : List TrailEntry :=
  if p.checkpoint.trail.any (fun e => decide (e.literal = p.asserting.norm)) then []
  else [p.assertEntry]

theorem BackjumpPlan.assertExtra_mem (p : BackjumpPlan leaf) {e : TrailEntry}
    (h : e ∈ p.assertExtra) :
    e = { literal := p.asserting.norm, level := p.target,
          reason := some { clause := p.learned } } := by
  unfold BackjumpPlan.assertExtra at h
  split at h
  · cases h
  · simpa [BackjumpPlan.assertEntry] using h

theorem BackjumpPlan.assertExtra_fresh (p : BackjumpPlan leaf)
    {x : TrailEntry} (hx : x ∈ p.assertExtra) :
    ∀ e ∈ p.checkpoint.trail, e.literal ≠ x.literal := by
  have hx' := p.assertExtra_mem hx
  unfold BackjumpPlan.assertExtra at hx
  split at hx
  · cases hx
  · next hn =>
    intro e he heq
    apply hn
    simp only [List.any_eq_true, decide_eq_true_eq]
    refine ⟨e, he, ?_⟩
    rw [heq, hx']

theorem BackjumpPlan.assertExtra_ne_nil_of_fresh (p : BackjumpPlan leaf)
    (h : ∀ e ∈ p.checkpoint.trail, e.literal ≠ p.asserting.norm) :
    p.assertExtra ≠ [] := by
  unfold BackjumpPlan.assertExtra
  split
  · next hn =>
    exfalso
    simp only [List.any_eq_true, decide_eq_true_eq] at hn
    obtain ⟨e, he, heq⟩ := hn
    exact h e he heq
  · simp

theorem BackjumpPlan.assertExtra_cases (p : BackjumpPlan leaf) :
    p.assertExtra = [] ∨ p.assertExtra = [p.assertEntry] := by
  unfold BackjumpPlan.assertExtra
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Execute a plan: the frame, trail and level come from the checkpoint
(exact restoration), the learned database is the *current* one (learned
clauses are global and survive the jump), and exactly one entry — the
asserting consequence — is appended. -/
def BackjumpPlan.execute (p : BackjumpPlan leaf) (bs : BranchState leaf) :
    BranchState leaf :=
  { frame := p.checkpoint.frame
    trail := p.checkpoint.trail ++ p.assertExtra
    level := p.target
    learned := bs.learned }

/-- The executed plan's trail is the restored trail plus the asserting entry
(skipped when its literal is already on the restored trail). -/
theorem BackjumpPlan.execute_trail (p : BackjumpPlan leaf)
    (bs : BranchState leaf) :
    (p.execute bs).trail = p.checkpoint.trail ++ p.assertExtra := rfl

/-- The executed plan's frame is the checkpoint's frame: restoration is
exact, never rebuilt. -/
theorem BackjumpPlan.execute_frame (p : BackjumpPlan leaf)
    (bs : BranchState leaf) :
    (p.execute bs).frame = p.checkpoint.frame := rfl

/-- The executed plan's level is the target level. -/
theorem BackjumpPlan.execute_level (p : BackjumpPlan leaf)
    (bs : BranchState leaf) : (p.execute bs).level = p.target := rfl

/-- Globally entailed learned clauses are retained across the jump: the
executed plan carries the current database unchanged. -/
theorem BackjumpPlan.execute_learned (p : BackjumpPlan leaf)
    (bs : BranchState leaf) : (p.execute bs).learned = bs.learned := rfl

/-- Enqueue only the proved asserting consequence: every trail entry of
the executed state is either a restored checkpoint entry or the single
asserting entry. -/
theorem BackjumpPlan.execute_mem (p : BackjumpPlan leaf)
    (bs : BranchState leaf) {e : TrailEntry} (h : e ∈ (p.execute bs).trail) :
    e ∈ p.checkpoint.trail ∨
      e = { literal := p.asserting.norm, level := p.target,
            reason := some { clause := p.learned } } := by
  simp only [BackjumpPlan.execute, List.mem_append] at h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (p.assertExtra_mem h)

/-! ## The permanent exhaustion record: rich dead regions

The record keeps *dead regions* — decidable sets of assignments that
provably contain no leaf solution (INTERFACES §2.6, PLAN P1.3 item 5). A
prefix list cannot express frame-shaped regions, so the region is the
unit of registration; a region is logical state that no trail
restoration touches, and it can justify deleting a pending alternative
but never "cover" a surviving leaf solution. -/

/-- A region of assignments, decided by `mem`. See the module header for
the computability constraint on `mem`: this layer has no `BEq Value`, so
the region kit below is literal-based (the frame/prefix regions of
INTERFACES §2.6 are not decidable in this import cone). -/
structure DeadRegion where
  /-- decidable membership: `true` means the assignment lies in the region -/
  mem : Assignment → Bool

/-- Semantic soundness of one region: no leaf solution lies in it. This is
the obligation C2 discharges at every registration site; a `Sound` region
can never contain a solution, which is why it must not appear as a
"covered" disjunct of `CoversRemainingLeaves`. -/
def DeadRegion.Sound (leaf : Assignment → Bool) (r : DeadRegion) : Prop :=
  ∀ a, leaf a = true → r.mem a = true → False

/-! ### Computable region combinators -/

/-- Region of assignments satisfying every listed literal. -/
def DeadRegion.byAllTrue (ls : List Literal) : DeadRegion :=
  { mem := fun a => ls.all fun l => l.eval a == some true }

/-- Region of assignments falsifying one literal. -/
def DeadRegion.byFalse (l : Literal) : DeadRegion :=
  { mem := fun a => l.eval a == some false }

/-- Region of assignments whose slot `s` has int view below `lo`. -/
def DeadRegion.below (s : Nat) (lo : Int) : DeadRegion :=
  { mem := fun a => match slotInt a s with
      | some i => decide (i < lo)
      | none => false }

/-- Region of assignments whose slot `s` has int view above `hi`. -/
def DeadRegion.above (s : Nat) (hi : Int) : DeadRegion :=
  { mem := fun a => match slotInt a s with
      | some i => decide (hi < i)
      | none => false }

/-- The value literals of a prefix: one pinning literal per chosen value
(the `valueLiteral` vocabulary of the closure layer, so the region is
computable here). -/
def prefixLiterals (p : Assignment) : List Literal :=
  (p.mapIdx fun s v => (valueLiteral s v).toList).flatten

/-- Prefix region: assignments matching a chosen prefix. This is the
computable refinement of INTERFACES §2.6's prefix embedding (see the
module header); its literal semantics is `prefixLiterals`. -/
def DeadRegion.byPrefix (p : Assignment) : DeadRegion :=
  DeadRegion.byAllTrue (prefixLiterals p)

theorem DeadRegion.byAllTrue_mem_iff {ls : List Literal} {a : Assignment} :
    (DeadRegion.byAllTrue ls).mem a = true ↔
      ∀ l ∈ ls, l.eval a = some true := by
  simp only [DeadRegion.byAllTrue, List.all_eq_true]
  constructor
  · intro h l hl
    exact beq_iff_eq.mp (h l hl)
  · intro h l hl
    exact beq_iff_eq.mpr (h l hl)

theorem DeadRegion.byFalse_mem_iff {l : Literal} {a : Assignment} :
    (DeadRegion.byFalse l).mem a = true ↔ l.eval a = some false :=
  beq_iff_eq

theorem DeadRegion.below_mem_iff {s : Nat} {lo : Int} {a : Assignment} :
    (DeadRegion.below s lo).mem a = true ↔
      ∃ i, slotInt a s = some i ∧ i < lo := by
  simp only [DeadRegion.below]
  cases h : slotInt a s with
  | none => simp
  | some i => simp

theorem DeadRegion.above_mem_iff {s : Nat} {hi : Int} {a : Assignment} :
    (DeadRegion.above s hi).mem a = true ↔
      ∃ i, slotInt a s = some i ∧ hi < i := by
  simp only [DeadRegion.above]
  cases h : slotInt a s with
  | none => simp
  | some i => simp

theorem DeadRegion.byPrefix_mem_iff {p a : Assignment} :
    (DeadRegion.byPrefix p).mem a = true ↔
      ∀ l ∈ prefixLiterals p, l.eval a = some true :=
  DeadRegion.byAllTrue_mem_iff

/-- RICHER REGION (C2b): the assignments still covered by a frame — the
honest dead region of a dead branch. Unlike `byPrefix`, this region is
exactly the set the frame represents (`FrameCovers`), so a dead branch's
region never contains a solution of a *sibling* that extends the same
prefix (the plan's warning: a narrowed frame's failure need not exclude
every extension of its prefix).

`mem` is decided classically (`noncomputable`): this layer has no
`BEq Value`, so `Decidable (FrameCovers _ _)` is only available through
`Classical.propDecidable`. The region is *evidence*, never runtime
filtering — no executable transition calls `mem`, so the region kit stays
sound without adding a `BEq` dependency to the runtime cone. -/
noncomputable def DeadRegion.ofFrame (f : BranchFrame) : DeadRegion :=
  { mem := fun a => by classical exact if FrameCovers f a then true else false }

theorem DeadRegion.ofFrame_mem_iff {f : BranchFrame} {a : Assignment} :
    (DeadRegion.ofFrame f).mem a = true ↔ FrameCovers f a := by
  classical
  unfold DeadRegion.ofFrame
  by_cases h : FrameCovers f a <;> simp [h]

theorem DeadRegion.ofFrame_mem_of_covers {f : BranchFrame} {a : Assignment}
    (h : FrameCovers f a) : (DeadRegion.ofFrame f).mem a = true :=
  DeadRegion.ofFrame_mem_iff.mpr h

/-- REGISTRATION LEMMA (C2b): a dead frame's region is sound. This is the
obligation every `localExclude`/`chronologicalFallback` registration site
must discharge in place of the unsound `byPrefix`-of-a-narrowed-frame
registration: the hypothesis is deadness of the frame itself, not of the
(larger) prefix region. -/
theorem DeadRegion.ofFrame_sound {leaf : Assignment → Bool}
    {f : BranchFrame}
    (hdead : ∀ a, leaf a = true → FrameCovers f a → False) :
    DeadRegion.Sound leaf (DeadRegion.ofFrame f) := by
  intro a hl hm
  exact hdead a hl (DeadRegion.ofFrame_mem_iff.mp hm)

/-- REGISTRATION LEMMA (C2b) for the fact regions: a region of assignments
falsifying an entailed literal contains no leaf solution. -/
theorem DeadRegion.byFalse_sound {leaf : Assignment → Bool} {l : Literal}
    (hent : ∀ a, leaf a = true → l.eval a = some true) :
    DeadRegion.Sound leaf (DeadRegion.byFalse l) := by
  intro a hl hm
  rw [DeadRegion.byFalse_mem_iff] at hm
  rw [hent a hl] at hm
  exact absurd hm (by simp)

/-- REGISTRATION LEMMA (C2b) for the conjunction regions: a region of
assignments satisfying literals, one of which is entailed-FALSE, contains
no leaf solution. Instantiating this at `byPrefix` shows the unsoundness
of registering a narrowed frame's prefix region: the premise needed is
"some pinned prefix literal is falsified by every solution", which a
narrowed frame's failure does not supply (see `Proofs/SchedulerResume`). -/
theorem DeadRegion.byAllTrue_sound {leaf : Assignment → Bool}
    {ls : List Literal}
    (hent : ∀ a, leaf a = true → ∃ l ∈ ls, l.eval a = some false) :
    DeadRegion.Sound leaf (DeadRegion.byAllTrue ls) := by
  intro a hl hm
  obtain ⟨l, hlmem, hfalse⟩ := hent a hl
  have htrue := DeadRegion.byAllTrue_mem_iff.mp hm l hlmem
  rw [htrue] at hfalse
  exact absurd hfalse (by simp)

/-! ### The computable frame region (C2b-int repair)

`DeadRegion.ofFrame` decides `FrameCovers` classically and is therefore
usable in proofs only. The runtime registration sites must stay
COMPUTABLE (`Tests.UIP.OracleFixtures` evaluates `conflictStep` in its
compiled `main`), so this section supplies a computable membership test
with a self-contained in-cone soundness proof. -/

/-- Structural value equality, in-cone and computable, on the two leaf
shapes the finite fragment's frames carry (`.bool`, `.int`); the nested
shapes (`.setOfInt`, `.array`) conservatively compare `false`. Mirrors
`LeanFzn.Semantics.Value.eqB` (`LeanFzn/FznStdLib.lean`) on the shapes it handles;
the checker's full soundness theorem `value_eqB_iff`
(`LeanFzn/FznSolution.lean:value_eqB_iff`) is the OUT-OF-CONE original
this in-cone copy replaces (it would re-introduce a `noncomputable`
dependency). -/
def valueEqBLocal : Value → Value → Bool
  | .bool a, .bool b => a == b
  | .int a, .int b => a == b
  | _, _ => false

/-- `valueEqBLocal` only returns `true` for equal values: the sound
direction of the checker's `value_eqB_iff`, proved inside the cone. -/
theorem valueEqBLocal_sound {a b : Value} (h : valueEqBLocal a b = true) :
    a = b := by
  cases a <;> cases b <;> simp_all [valueEqBLocal, beq_iff_eq]

/-- Pointwise list equality with `valueEqBLocal`. -/
def valuesEqBLocal : List Value → List Value → Bool
  | [], [] => true
  | x :: xs, y :: ys => valueEqBLocal x y && valuesEqBLocal xs ys
  | _, _ => false

/-- `valuesEqBLocal` only returns `true` for equal lists. -/
theorem valuesEqBLocal_sound {xs ys : List Value}
    (h : valuesEqBLocal xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [valuesEqBLocal]
  | cons x xs ih =>
      cases ys with
      | nil => simp [valuesEqBLocal] at h
      | cons y ys =>
          simp only [valuesEqBLocal, Bool.and_eq_true] at h
          rw [valueEqBLocal_sound h.1, ih h.2]

/-- Computable coverage test for a frame: is the assignment one of the
frame's enumerated complete assignments? Sound for every frame; exact
for bool/int-valued frames (nested values conservatively answer
`false`, which can never exclude a live assignment). -/
def DeadRegion.coversB (f : BranchFrame) (a : Assignment) : Bool :=
  (LeanFzn.Solver.Core.allAssigns f.doms).any fun tail =>
    valuesEqBLocal tail a

/-- Membership in the computable coverage test implies coverage. -/
theorem DeadRegion.coversB_sound {f : BranchFrame} {a : Assignment}
    (h : DeadRegion.coversB f a = true) : FrameCovers f a := by
  rw [DeadRegion.coversB, List.any_eq_true] at h
  obtain ⟨tail, htail, heq⟩ := h
  exact (valuesEqBLocal_sound heq) ▸ htail

/-- COMPUTABLE FRAME REGION (C2b-int repair): the assignments covered by
a frame, decided by a computable test (unlike the classical
`DeadRegion.ofFrame`, whose `mem` needs `Classical.choice`). This is the
region the runtime registration sites can use. -/
def DeadRegion.byFrame (f : BranchFrame) : DeadRegion :=
  { mem := fun a => DeadRegion.coversB f a }

/-- The computable region only claims covered assignments: the bridge to
the classical region's `mem` (for consumers written against
`DeadRegion.ofFrame`). -/
theorem DeadRegion.byFrame_ofFrame_mem {f : BranchFrame} {a : Assignment}
    (h : (DeadRegion.byFrame f).mem a = true) :
    (DeadRegion.ofFrame f).mem a = true :=
  DeadRegion.ofFrame_mem_of_covers (DeadRegion.coversB_sound h)

/-- REGISTRATION LEMMA (C2b-int): a dead frame's COMPUTABLE region is
sound. Same obligation shape as `DeadRegion.ofFrame_sound` (deadness of
the frame itself), so consumers can switch to the computable region
without changing their hypothesis. -/
theorem DeadRegion.byFrame_sound {leaf : Assignment → Bool}
    {f : BranchFrame}
    (hdead : ∀ a, leaf a = true → FrameCovers f a → False) :
    DeadRegion.Sound leaf (DeadRegion.byFrame f) :=
  fun a hl hm => hdead a hl (DeadRegion.coversB_sound hm)

/-- The permanent exhaustion record: dead regions that must never be
regenerated. It is logical state that no trail restoration touches. -/
instance : Repr DeadRegion :=
  ⟨fun _ _ => "DeadRegion"⟩

structure ExhaustionLog where
  /-- registered dead regions, newest first -/
  regions : List DeadRegion := []
  deriving Repr

/-- Register a region as permanently exhausted. -/
def ExhaustionLog.register (log : ExhaustionLog) (r : DeadRegion) :
    ExhaustionLog :=
  { regions := r :: log.regions }

/-- Registration is monotone: nothing is ever removed. -/
theorem ExhaustionLog.register_mono {log : ExhaustionLog} {p : DeadRegion}
    {q : DeadRegion} (h : p ∈ log.regions) :
    p ∈ (log.register q).regions :=
  List.mem_cons_of_mem _ h

/-- A registered region stays registered under any further registration —
the "never regenerated" obligation, independent of the restored trail. -/
theorem ExhaustionLog.registered_permanent {log : ExhaustionLog}
    {p : DeadRegion} (h : p ∈ log.regions) (extra : List DeadRegion) :
    p ∈ (extra.foldl ExhaustionLog.register log).regions := by
  induction extra generalizing log with
  | nil => exact h
  | cons q qs ih =>
      simp only [List.foldl_cons]
      exact ih (ExhaustionLog.register_mono h)

/-- Semantic soundness of the log: no leaf solution lies in any registered
region (INTERFACES §2.6). This is the log-level obligation that C2 proves
at every registration site; it is strictly stronger than membership
persistence (`registered_permanent`). -/
def ExhaustionLog.Sound (leaf : Assignment → Bool)
    (log : ExhaustionLog) : Prop :=
  ∀ r ∈ log.regions, DeadRegion.Sound leaf r

/-- Registering a sound region preserves log soundness. This is the
preservation step every registration transition (local exclusion,
chronological fallback) must instantiate — proved here so C2 only has to
discharge the per-region soundness obligation. -/
theorem ExhaustionLog.register_sound {leaf : Assignment → Bool}
    {log : ExhaustionLog} {r : DeadRegion}
    (h : log.Sound leaf) (hr : DeadRegion.Sound leaf r) :
    (log.register r).Sound leaf := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact hr
  · exact h q hq

/-! ## Classification of pending alternatives -/

/-- How a pending alternative fares under a backjump. -/
inductive AlternativeClass where
  /-- kept for later exploration -/
  | retained
  /-- already explored: permanently exhausted, never regenerated -/
  | exhausted
  /-- excluded by a proved clause: the assignment fails the learned
      clause, so it cannot hold any solution -/
  | excluded
  deriving DecidableEq, Repr

/-- A classification is *justified* when no still-possible solution is
deleted: every leaf-passing assignment covered by the pending frontier
either survives in the next frontier or is excluded by a registered
dead region or by a proved clause. "Excluded by a region" means the
region MEMBERSHIP test fires; by `ExhaustionLog.Sound` a region contains
no leaf solution, so this disjunct can justify dropping an alternative
but can never be used to claim a solution is covered. This is the
coverage contract the plan requires; the executable classifier must
satisfy it, and a lower target level alone never justifies dropping
siblings. -/
structure ClassificationSound {leaf : Assignment → Bool}
    (pending next : List BranchFrame) (log : ExhaustionLog)
    (db : List Clause) : Prop where
  /-- surviving solutions are still enumerated -/
  retains : ∀ a, leaf a = true → FrontierCovers pending a →
    FrontierCovers next a ∨
    (∃ r ∈ log.regions, r.mem a = true) ∨
    (∃ c ∈ db, ¬ c.SatisfiedBy a)
  /-- nothing new appears: the next frontier only shrinks the set -/
  noNew : ∀ a, FrontierCovers next a → FrontierCovers pending a

/-! ## Checked progress

The scheduler's measure is `frontierCost` on the explicit pending
stack, exactly as for the chronological driver: every transition either
consumes a frame (`frontierCost_cons`) or expands a strictly cheaper
child (`frontierCost_expand`). No fuel and no restart counter is
involved, and the measure is proof-only. -/

/-- Consuming a pending alternative strictly decreases the frontier
weight: the scheduler's progress step (M4/M5 rank, S0 §3.5). -/
theorem backjump_progress_consume (f : BranchFrame)
    (pending : List BranchFrame) :
    frontierWeight pending < frontierWeight (f :: pending) :=
  frontierWeight_cons f pending

/-- Expanding a split slot strictly decreases the frontier weight when
both children are strictly cheaper (arbitrary slot; the schedule's decide
arm supplies the strict cost decreases). -/
theorem backjump_progress_expand (f : BranchFrame) (k : Nat) (v : Value)
    (vs : Domain) (rest : List BranchFrame)
    (h₁ : Frame.cost (f.pin k v) < Frame.cost f)
    (h₂ : Frame.cost (f.retire k vs) < Frame.cost f) :
    frontierWeight ((f.pin k v) :: (f.retire k vs) :: rest)
      < frontierWeight (f :: rest) := by
  have ha : Frame.cost (f.pin k v) ≤ Frame.cost f - 1 := by omega
  have hb : Frame.cost (f.retire k vs) ≤ Frame.cost f - 1 := by omega
  have h1le : 3 ^ Frame.cost (f.pin k v) ≤ 3 ^ (Frame.cost f - 1) :=
    Nat.pow_le_pow_right (by decide) ha
  have h2le : 3 ^ Frame.cost (f.retire k vs) ≤ 3 ^ (Frame.cost f - 1) :=
    Nat.pow_le_pow_right (by decide) hb
  have hc : Frame.cost f = Frame.cost f - 1 + 1 := by omega
  have hlt : 3 ^ (Frame.cost f - 1) + 3 ^ (Frame.cost f - 1) <
      3 ^ Frame.cost f := by
    rw [hc, Nat.pow_succ]
    calc 3 ^ (Frame.cost f - 1) + 3 ^ (Frame.cost f - 1)
        = 2 * 3 ^ (Frame.cost f - 1) := (Nat.two_mul _).symm
      _ < 3 * 3 ^ (Frame.cost f - 1) :=
          Nat.mul_lt_mul_of_pos_right (by decide) (Nat.pow_pos (by decide))
      _ = 3 ^ (Frame.cost f - 1) * 3 := Nat.mul_comm 3 _
  simp only [frontierWeight, frameWeight, List.map_cons, List.sum_cons]
  omega

/-! ## The fallback contract (C2d-resume: CONCRETE, wrappers retired)

When analysis cannot produce an asserting result, the driver continues
chronologically: it keeps propagation/learning and never loses the
exhaustion record. The REAL transition is the consume step — the head
alternative is dropped and search resumes on the tail (the frontier
projection of the runtime `stepConsume`, taken by both the analysis-`none`
and the missing-checkpoint routes). The theorems below prove the retention
(`ClassificationSound.retains` shape) and progress obligations for THAT
CONCRETE transformation; the only semantic premise is the HEAD's deadness
(the site evidence: registered region or failed clause), never a
re-statement of the conclusion. -/

/-- The consume step on the explicit frontier: drop the head alternative,
resume on the tail. This is the frontier projection of the runtime
`stepConsume` (both its `some` and `none` checkpoint routes). -/
def frontierConsume (pending : List BranchFrame) : List BranchFrame :=
  pending.tail

/-- The consume step drops exactly the head. -/
theorem frontierConsume_cons (f : BranchFrame) (rest : List BranchFrame) :
    frontierConsume (f :: rest) = rest := rfl

/-- The fallback's safety for the CONCRETE consume step: dropping the head
is justified by the head's exclusion evidence — a registered dead region or
a proved clause (by `ExhaustionLog.Sound`, a sound region contains no leaf
solution, so no solution is ever lost). A solution covered by the tail is
retained outright. -/
theorem fallback_retains_consume {leaf : Assignment → Bool}
    {f : BranchFrame} {rest : List BranchFrame} {log : ExhaustionLog}
    {db : List Clause}
    (hdead : ∀ a, leaf a = true → FrameCovers f a →
      (∃ r ∈ log.regions, r.mem a = true) ∨
      (∃ c ∈ db, ¬ c.SatisfiedBy a)) :
    ∀ a, leaf a = true → FrontierCovers (f :: rest) a →
      FrontierCovers rest a ∨
      (∃ r ∈ log.regions, r.mem a = true) ∨
      (∃ c ∈ db, ¬ c.SatisfiedBy a) := by
  rintro a ha ⟨g, hg, hgcover⟩
  rcases List.mem_cons.mp hg with rfl | hg
  · rcases hdead a ha hgcover with ⟨r, hr, hm⟩ | ⟨c, hc, hs⟩
    · exact Or.inr (Or.inl ⟨r, hr, hm⟩)
    · exact Or.inr (Or.inr ⟨c, hc, hs⟩)
  · exact Or.inl ⟨g, hg, hgcover⟩

/-- `ClassificationSound` for the CONCRETE consume step: `retains` is
`fallback_retains_consume` and `noNew` is immediate (the tail is a
sublist). -/
theorem classificationSound_consume {leaf : Assignment → Bool}
    {f : BranchFrame} {rest : List BranchFrame} {log : ExhaustionLog}
    {db : List Clause}
    (hdead : ∀ a, leaf a = true → FrameCovers f a →
      (∃ r ∈ log.regions, r.mem a = true) ∨
      (∃ c ∈ db, ¬ c.SatisfiedBy a)) :
    ClassificationSound (leaf := leaf) (f :: rest) rest log db where
  retains := fallback_retains_consume hdead
  noNew := by
    rintro a ⟨g, hg, hc⟩
    exact ⟨g, List.mem_cons.mpr (Or.inr hg), hc⟩

/-- The fallback's progress for the CONCRETE consume step: the frontier
cost strictly decreases, so the chronological continuation cannot cycle
(fuel-free well-foundedness). -/
theorem fallback_progress_consume (f : BranchFrame)
    (rest : List BranchFrame) :
    frontierWeight rest < frontierWeight (f :: rest) :=
  frontierWeight_cons f rest

/-- RETIRED (C2d-resume): the former premise-returning identity wrapper
`fallback_safe` is replaced by the concrete `fallback_retains_consume`.
This compatibility name denotes that result (same statement) so peer
imports keep resolving; it no longer re-states its own hypothesis. -/
@[deprecated fallback_retains_consume (since := "2026-10-09")]
theorem fallback_safe {leaf : Assignment → Bool}
    {f : BranchFrame} {rest : List BranchFrame} {log : ExhaustionLog}
    {db : List Clause}
    (hdead : ∀ a, leaf a = true → FrameCovers f a →
      (∃ r ∈ log.regions, r.mem a = true) ∨
      (∃ c ∈ db, ¬ c.SatisfiedBy a)) :
    ∀ a, leaf a = true → FrontierCovers (f :: rest) a →
      FrontierCovers rest a ∨
      (∃ r ∈ log.regions, r.mem a = true) ∨
      (∃ c ∈ db, ¬ c.SatisfiedBy a) :=
  fallback_retains_consume hdead

/-- RETIRED (C2d-resume): the former premise-returning identity wrapper
`fallback_progress_wellFounded` is replaced by the concrete
`fallback_progress_consume`. This compatibility name denotes that result
(same statement) so peer imports keep resolving. -/
@[deprecated fallback_progress_consume (since := "2026-10-09")]
theorem fallback_progress_wellFounded (f : BranchFrame)
    (rest : List BranchFrame) :
    frontierWeight rest < frontierWeight (f :: rest) :=
  fallback_progress_consume f rest

/-! ## Checkpoint identity (INTERFACES §2.4, PLAN P1.3 item 1)

A decision checkpoint is the branch state's frame and trail at the moment
decision level `level` was current. Identity is a THEOREM about the saved
state (`Identifies`), not a caller premise: the scheduler maintains its
checkpoint list so that every plan it builds carries `p.Identifies
cfg.branch`, which removes the former `hcpLevel : p.checkpoint.level =
p.target` premise from C2's execution statements. `learned` is
deliberately absent from the checkpoint — the global clause database is
not checkpointed. -/

/-- A decision checkpoint: the branch state's frame and trail at the
moment decision level `level` was current. -/
structure DecisionCheckpoint (leaf : Assignment → Bool) where
  /-- the decision level that was current -/
  level : Nat
  /-- the frame as it was then -/
  frame : BranchFrame
  /-- the trail as it was then -/
  trail : List TrailEntry
  deriving Repr

/-- Semantic frame descent: every assignment covered by `g` was covered
by the ancestor `f`. -/
def FrameDescendsFrom (g f : BranchFrame) : Prop :=
  ∀ a, FrameCovers g a → FrameCovers f a

/-- `cp` identifies the ancestor of `bs` at `target`: same level, the
checkpoint's trail is a prefix of the branch's trail, every later entry
sits at or above the target level, and the frame descends from the
checkpoint's frame.

NOTE (C1): INTERFACES §2.4 prints this with `(∀ e ∈ mid, target ≤
e.level)` as a separate conjunct after `∃ mid, …`, where `mid` escapes its
binder; the only well-formed reading is the nested one below (the `∀`
inside the `∃`), which is the intended "later entries at or above the
target" condition. -/
def DecisionCheckpoint.Identifies (cp : DecisionCheckpoint leaf)
    (bs : BranchState leaf) (target : Nat) : Prop :=
  cp.level = target ∧
  (∃ mid : List TrailEntry,
    bs.trail = cp.trail ++ mid ∧ ∀ e ∈ mid, target ≤ e.level) ∧
  FrameDescendsFrom bs.frame cp.frame

/-- The checkpoint of a state itself: level, frame and trail. -/
def DecisionCheckpoint.ofBranch (bs : BranchState leaf) :
    DecisionCheckpoint leaf :=
  { level := bs.level, frame := bs.frame, trail := bs.trail }

/-- A state's own checkpoint identifies it at its own level (reflexivity
of identity). -/
theorem DecisionCheckpoint.identifies_self (bs : BranchState leaf) :
    (DecisionCheckpoint.ofBranch bs).Identifies bs bs.level := by
  refine ⟨rfl, ⟨[], ?_, ?_⟩, ?_⟩
  · simp [DecisionCheckpoint.ofBranch]
  · intro e he
    cases he
  · intro a h
    exact h

/-- The root checkpoint: the whole original box, empty trail, level 0. -/
def rootCheckpoint (orig : List Domain) : DecisionCheckpoint leaf :=
  { level := 0, frame := ⟨orig, []⟩, trail := [] }

/-- The root checkpoint identifies the initial branch state at level 0. -/
theorem rootCheckpoint_identifies_init (leaf : Assignment → Bool)
    (orig : List Domain) (db : List Clause := []) :
    (rootCheckpoint (leaf := leaf) orig).Identifies
      ({ BranchState.init (leaf := leaf) (⟨orig, []⟩ : BranchFrame) with learned := db }) 0 := by
  refine ⟨rfl, ⟨[], rfl, ?_⟩, ?_⟩
  · intro e he
    cases he
  · intro a h
    exact h

/-- The scheduler's checkpoint lookup: the newest saved ancestor at
`target` (the list is maintained newest first, so `find?` returns the
most recently saved state at that level). -/
def checkpointAt (cps : List (DecisionCheckpoint leaf)) (target : Nat) :
    Option (DecisionCheckpoint leaf) :=
  cps.find? fun cp => cp.level == target

/-- A found checkpoint is a member of the list. -/
theorem checkpointAt_mem {cps : List (DecisionCheckpoint leaf)} {target : Nat}
    {cp : DecisionCheckpoint leaf} (h : checkpointAt cps target = some cp) :
    cp ∈ cps := by
  induction cps with
  | nil => simp [checkpointAt] at h
  | cons cp' rest ih =>
      simp only [checkpointAt, List.find?_cons] at h
      split at h
      · cases h
        exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih h)

/-- A found checkpoint sits exactly at the requested level: the lookup
returns only ancestors at the proved target level. -/
theorem checkpointAt_level {cps : List (DecisionCheckpoint leaf)} {target : Nat}
    {cp : DecisionCheckpoint leaf} (h : checkpointAt cps target = some cp) :
    cp.level = target := by
  induction cps with
  | nil => simp [checkpointAt] at h
  | cons cp' rest ih =>
      simp only [checkpointAt, List.find?_cons] at h
      split at h
      · rename_i hb
        cases h
        exact beq_iff_eq.mp hb
      · exact ih h

/-- `p` identifies `bs`: the plan's checkpoint level law holds, and the
checkpoint identifies the branch at the target level. This is the frozen
replacement for the former caller premise `p.checkpoint.level =
p.target`. -/
def BackjumpPlan.Identifies (p : BackjumpPlan leaf) (bs : BranchState leaf) :
    Prop :=
  p.checkpoint.level = p.target ∧
  DecisionCheckpoint.Identifies
    { level := p.checkpoint.level, frame := p.checkpoint.frame,
      trail := p.checkpoint.trail } bs p.target

/-- The level law of an identifying plan. -/
theorem BackjumpPlan.Identifies.level {p : BackjumpPlan leaf}
    {bs : BranchState leaf} (h : p.Identifies bs) :
    p.checkpoint.level = p.target :=
  h.1

/-- The trail-prefix law of an identifying plan. -/
theorem BackjumpPlan.Identifies.trail_prefix {p : BackjumpPlan leaf}
    {bs : BranchState leaf} (h : p.Identifies bs) :
    ∃ mid : List TrailEntry,
      bs.trail = p.checkpoint.trail ++ mid ∧ ∀ e ∈ mid, p.target ≤ e.level :=
  h.2.2.1

/-- The frame-descent law of an identifying plan. -/
theorem BackjumpPlan.Identifies.frame_descends {p : BackjumpPlan leaf}
    {bs : BranchState leaf} (h : p.Identifies bs) :
    FrameDescendsFrom bs.frame p.checkpoint.frame :=
  h.2.2.2

/-- Build a plan from a checkpoint at the (already proved) target level:
the checkpoint record carries the level law, so the plan identifies the
branch whenever the checkpoint does. This is the constructor the
scheduler uses, and it is why `hcpLevel` disappears from C2's
statements. -/
def BackjumpPlan.ofCheckpoint (cp : DecisionCheckpoint leaf)
    (bs : BranchState leaf) (asserting : Literal) (learned : Clause) :
    BackjumpPlan leaf where
  target := cp.level
  checkpoint :=
    { frame := cp.frame, trail := cp.trail, level := cp.level,
      learned := bs.learned }
  asserting := asserting
  learned := learned

/-- THE IDENTITY THEOREM (INTERFACES §2.4(a)): a plan built from an
identifying checkpoint identifies the branch, with the level law
discharged from the checkpoint record rather than assumed. -/
theorem BackjumpPlan.ofCheckpoint_identifies {cp : DecisionCheckpoint leaf}
    {bs : BranchState leaf} {l : Literal} {c : Clause}
    (h : cp.Identifies bs cp.level) :
    (BackjumpPlan.ofCheckpoint cp bs l c).Identifies bs :=
  ⟨rfl, h⟩

/-! ## The complete learn/backjump/assert transition (PLAN P1.3 item 3)

`BackjumpPlan.execute` restores and appends the asserting entry; the
complete transition additionally inserts the learned clause into the
GLOBAL database, narrows the restored frame by the assertion, keeps the
asserting entry's recorded reason (the learned clause), and resumes
explained propagation. This is the reference implementation of the
transition's shape; its forward correctness (coverage/coherence) is C2's
obligation. -/

/-- Narrow a state's frame to a filtered frame: the frame component of
`narrowState` without the trail append (the asserting entry is already
recorded by `execute`). -/
def BranchState.narrowFrame (bs : BranchState leaf) (g : BranchFrame) :
    BranchState leaf :=
  { bs with frame := g }

/-- The restored-and-narrowed state of a plan: the learned clause is
inserted into the global database, restoration and the single asserting
entry come from `execute`, and the frame is narrowed by the asserting
literal. `none` marks "the asserting literal rejects the restored frame":
the branch is locally dead and C2 must classify it through the
local-exclusion path, never as a jump. -/
def BackjumpPlan.restoreNarrow (p : BackjumpPlan leaf) (bs : BranchState leaf) :
    Option (BranchState leaf) :=
  match filterFrame p.asserting p.checkpoint.frame with
  | none => none
  | some g => some ((p.execute (bs.learnGlobal p.learned)).narrowFrame g)

/-- THE COMPLETE TRANSITION: insertion, restoration, assertion
narrowing, the frame/trail synchronisation of the restored frame, and
resumed (synchronised) explained propagation. -/
def BackjumpPlan.perform (p : BackjumpPlan leaf) (bs : BranchState leaf)
    (orig : List Domain) (original : List Clause) (props : List Propagator) :
    Option (BranchState leaf) :=
  (p.restoreNarrow bs).map fun s => explainedClosure orig original props (syncAll orig s)

/-- The restored-and-narrowed state's level is the target level: the level
law comes from the checkpoint, never from a caller premise. -/
theorem BackjumpPlan.restoreNarrow_level {p : BackjumpPlan leaf}
    {bs : BranchState leaf} {s : BranchState leaf}
    (h : p.restoreNarrow bs = some s) : s.level = p.target := by
  unfold BackjumpPlan.restoreNarrow at h
  split at h
  · cases h
  · next g _ =>
      cases h
      simp only [BranchState.narrowFrame]
      exact BackjumpPlan.execute_level p bs

/-- The restored-and-narrowed state's frame is the assertion-filtered
frame of the checkpoint. -/
theorem BackjumpPlan.restoreNarrow_frame {p : BackjumpPlan leaf}
    {bs : BranchState leaf} {s : BranchState leaf}
    {g : BranchFrame} (hg : filterFrame p.asserting p.checkpoint.frame = some g)
    (h : p.restoreNarrow bs = some s) : s.frame = g := by
  unfold BackjumpPlan.restoreNarrow at h
  rw [hg] at h
  cases h
  rfl

/-- Resuming propagation preserves the level (the closure only appends
trail entries and narrows the frame). -/
theorem explainedClosure_level (orig : List Domain) (original : List Clause)
    (props : List Propagator) (bs : BranchState leaf) :
    (explainedClosure orig original props bs).level = bs.level := by
  suffices h : ∀ (fuel : Nat) (bs : BranchState leaf), Frame.mass bs.frame ≤ fuel →
      (explainedClosure orig original props bs).level = bs.level from
    h (Frame.mass bs.frame) bs (Nat.le_refl _)
  intro fuel
  induction fuel with
  | zero =>
    intro bs hle
    rw [explainedClosure]
    split
    · rfl
    · rename_i d _
      exfalso
      have := d.decreases
      omega
  | succ fuel ih =>
    intro bs hle
    rw [explainedClosure]
    split
    · rfl
    · rename_i d _
      have hmass : Frame.mass (stepNarrowSync orig bs d).frame ≤ fuel := by
        simp only [stepNarrowSync_frame]
        have := d.decreases
        omega
      rw [ih (stepNarrowSync orig bs d) hmass]
      simp only [stepNarrowSync_level]

/-- Resuming propagation never increases the frame mass. -/
theorem explainedClosure_mass (orig : List Domain) (original : List Clause)
    (props : List Propagator) (bs : BranchState leaf) :
    Frame.mass (explainedClosure orig original props bs).frame ≤ Frame.mass bs.frame := by
  suffices h : ∀ (fuel : Nat) (bs : BranchState leaf), Frame.mass bs.frame ≤ fuel →
      Frame.mass (explainedClosure orig original props bs).frame ≤ Frame.mass bs.frame from
    h (Frame.mass bs.frame) bs (Nat.le_refl _)
  intro fuel
  induction fuel with
  | zero =>
    intro bs hle
    rw [explainedClosure]
    split
    · exact Nat.le_refl _
    · rename_i d _
      exfalso
      have := d.decreases
      omega
  | succ fuel ih =>
    intro bs hle
    rw [explainedClosure]
    split
    · exact Nat.le_refl _
    · rename_i d _
      have hmass : Frame.mass (stepNarrowSync orig bs d).frame ≤ fuel := by
        simp only [stepNarrowSync_frame]
        have := d.decreases
        omega
      have h1 := ih (stepNarrowSync orig bs d) hmass
      have h2 := d.decreases
      simp only [stepNarrowSync_frame] at h1 h2 ⊢
      omega

/-- The complete transition's level is the plan's target level. -/
theorem BackjumpPlan.perform_level {p : BackjumpPlan leaf}
    {bs : BranchState leaf} {orig : List Domain} {original : List Clause}
    {props : List Propagator}
    {s : BranchState leaf} (h : p.perform bs orig original props = some s) :
    s.level = p.target := by
  unfold BackjumpPlan.perform at h
  cases hr : p.restoreNarrow bs with
  | none => rw [hr] at h; cases h
  | some t =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq] at h
      rw [← h, explainedClosure_level, syncAll_level]
      exact BackjumpPlan.restoreNarrow_level hr

/-! ## Repaired sibling resume (C2b, PLAN C2b)

`stepConsume` (`SchedulerStep.lean`) resumes a pending alternative `f`
with the trail of the checkpoint found at level `f.2.length`. For a
freshly pushed sibling that checkpoint is the *parent's* level state, and
its trail records the failed child's PIN of the value the sibling
dropped; the resumed trail therefore asserts a value the sibling frame
excludes, and it carries no falsifier for the dropped value. The
counterexample and its consequence for the frozen `ResumeCoherent` are in
`Proofs/SchedulerResume.lean`; this section supplies the repair.

The repaired resume takes the current trail restricted to the sibling's
own level (`restoreLevel`) — the real history at or below that level,
including every level-`≤ f.2.length` propagation — and appends one
*retiring* entry: the negation of the dropped head value's pin, recovered
from the ancestor checkpoint's frame. The entry is a normalized
reason-less branch-structural fact at the sibling's level; it makes the
resumed state's trail falsify the dropped value, which is exactly the
`ResumeCoherent` falsifier conjunct the checkpoint trail cannot supply. -/

/-- The retiring entry for a dropped value at an explicit level: the
negation of the value's decision pin, with no reason (it retires a branch
alternative; it is not a deduction). `none` for values outside the decision
vocabulary (sets/arrays), which the scheduler never splits on (`splitData`). -/
def retiredEntryAt (level slot : Nat) (v : Value) : Option TrailEntry :=
  (valueLiteral slot v).map fun l =>
    { literal := l.negate.norm, level := level, reason := none }

/-- The retired-entry shape of `retiredEntryAt` at level `slot` (kept for
compatibility with the pre-M4 vocabulary). -/
def retiredEntry (slot : Nat) (v : Value) : Option TrailEntry :=
  retiredEntryAt slot slot v

/-- REPAIRED SIBLING RESUME (M4 sparse): restore the current trail by the
sibling's own level `f.level`, take the frame from the pending alternative
`f`, and record the retirement of the dropped value `v` at the split slot
`k`, at the sibling's level. The caller has `(k, v)` from the sibling
construction (`f = parent.retire k vs` with `parent.doms[k]? = some (v :: vs)`),
so the positional checkpoint-head recovery is gone; the sibling's level is
its DECISION count (`f.level`), not a position in a box. -/
def resumeSibling (bs : BranchState leaf) (f : BranchFrame) (k : Nat)
    (v : Value) : BranchState leaf :=
  { frame := f
    trail := (bs.restoreLevel f.level).trail ++ (retiredEntryAt f.level k v).toList
    level := f.level
    learned := bs.learned }

theorem resumeSibling_frame (bs : BranchState leaf) (f : BranchFrame)
    (k : Nat) (v : Value) : (resumeSibling bs f k v).frame = f := rfl

theorem resumeSibling_level (bs : BranchState leaf) (f : BranchFrame)
    (k : Nat) (v : Value) : (resumeSibling bs f k v).level = f.level := rfl

theorem resumeSibling_learned (bs : BranchState leaf) (f : BranchFrame)
    (k : Nat) (v : Value) : (resumeSibling bs f k v).learned = bs.learned := rfl

theorem resumeSibling_trail (bs : BranchState leaf) (f : BranchFrame)
    (k : Nat) (v : Value) :
    (resumeSibling bs f k v).trail = (bs.restoreLevel f.level).trail ++
      (retiredEntryAt f.level k v).toList := rfl

/-! ## The R1 canonical resume (frame-derived trail, no checkpoint)

R1 repair of the missing-checkpoint route: when no saved checkpoint
survives at the pending alternative's level (jumps retire deep
checkpoints but keep the frames), the OLD route restored the *current*
trail by level — history the jump had replaced, so the resumed trail
could disagree with the frame's prefix. The repaired route treats the
pending frame as its own retained snapshot: the trail is reconstructed
CANONICALLY from the frame and the original box — the prefix pins (one
per chosen position, at the level the decision opened) followed by the
remaining-slot falsifiers (each dropped original value retired at the
resumed level). No checkpoint is consulted. -/

/-- The pin entry of a chosen prefix position, at the level the decision
opened (`s + 1`, mirroring `BranchState.decide`). -/
def canonicalPinEntry (slot : Nat) (w : Value) : Option TrailEntry :=
  (valueLiteral slot w).map fun l =>
    { literal := l.norm, level := slot + 1, reason := none }

/-- The retiring entry of a dropped value at the resumed level (the same
shape `retiredEntry` uses; the level is supplied separately so all
remaining-slot falsifiers sit at the resumed level `L`). -/
def canonicalRetire (level slot : Nat) (w : Value) : Option TrailEntry :=
  (valueLiteral slot w).map fun l =>
    { literal := l.negate.norm, level := level, reason := none }

/-- The pin entry of a DECIDED slot at an explicit level (M4: level
`index + 1` over `f.order`, not `slot + 1`). -/
def canonicalPinEntryAt (level slot : Nat) (w : Value) : Option TrailEntry :=
  (valueLiteral slot w).map fun l =>
    { literal := l.norm, level := level, reason := none }

/-- The canonical pins of a frame's decision order: one entry per decided
slot, at level `index + 1`, reading the pinned value from the slot's
singleton (S0 §3.4: `canonicalPins : (f : BranchFrame) → ...`). -/
def canonicalPins (f : BranchFrame) : List TrailEntry :=
  f.order.zipIdx.filterMap fun p =>
    match f.doms[p.1]? with
    | some d =>
        match Dom.enum d with
        | [v] => canonicalPinEntryAt (p.2 + 1) p.1 v
        | _ => none
    | none => none

/-- The per-slot falsifier list of an UNDECIDED slot `k` with domain `dom`:
every original-box value whose decision pin is not among the slot's kept
pins gets its retiring entry at the resumed level `f.level` — emitted at
its FIRST occurrence only (R2a dedup: duplicated original domain entries,
admitted by the accepted `var {..., k, ..., k, ...}` source shape, would
otherwise emit the identical retire entry twice and break the trail's
`Nodup` discipline; a later copy falsifies nothing the first one does). -/
def slotFalsifiers (orig : List Domain) (f : BranchFrame) (k : Nat)
    (dom : Domain) : List TrailEntry :=
  let kept : List Literal := (Dom.enum dom).filterMap (valueLiteral k)
  let ds := Dom.enum (orig.getD k Dom.empty)
  ds.zipIdx.filterMap fun p =>
    match valueLiteral k p.1 with
    | none => none
    | some l =>
        if l ∈ kept then none
        else if l ∈ (ds.take p.2).filterMap (valueLiteral k) then none
        else canonicalRetire f.level k p.1

/-- The canonical falsifiers of the dropped values: one `slotFalsifiers`
list per UNDECIDED slot of the frame (the slots not in the decision
order), concatenated. -/
def canonicalFalsifiers (orig : List Domain) (f : BranchFrame) :
    List TrailEntry :=
  (f.doms.zipIdx.filterMap fun p =>
    if p.2 ∈ f.order then none
    else some (slotFalsifiers orig f p.2 p.1)).flatten

/-- R1 CANONICAL TRAIL: the pending alternative's own history,
reconstructed from the frame and the original box. -/
def canonicalTrail (orig : List Domain) (f : BranchFrame) : List TrailEntry :=
  canonicalPins f ++ canonicalFalsifiers orig f

/-- R1 CANONICAL RESUME (the missing-checkpoint route): the pending frame
is its own retained snapshot; the global learned database is carried. -/
def resumePendingBase (orig : List Domain) (bs : BranchState leaf)
    (f : BranchFrame) : BranchState leaf :=
  { frame := f
    trail := canonicalTrail orig f
    level := f.level
    learned := bs.learned }

/-- R1d: the resumed branch is frame/trail SYNCHRONISED: bounds and fixings
the pending frame implies are recorded as explained trail literals. -/
def resumePending (orig : List Domain) (bs : BranchState leaf)
    (f : BranchFrame) : BranchState leaf :=
  syncAll orig (resumePendingBase orig bs f)

theorem resumePending_frame (orig : List Domain) (bs : BranchState leaf)
    (f : BranchFrame) : (resumePending orig bs f).frame = f := by
  simp [resumePending, resumePendingBase]

theorem resumePending_level (orig : List Domain) (bs : BranchState leaf)
    (f : BranchFrame) : (resumePending orig bs f).level = f.level := by
  simp [resumePending, resumePendingBase]

theorem resumePending_learned (orig : List Domain) (bs : BranchState leaf)
    (f : BranchFrame) : (resumePending orig bs f).learned = bs.learned := by
  simp [resumePending, resumePendingBase]

theorem resumePending_trail (orig : List Domain) (bs : BranchState leaf)
    (f : BranchFrame) :
    ∃ ex, (resumePending orig bs f).trail = canonicalTrail orig f ++ ex ∧
      ∀ e ∈ ex, e.level = f.level := by
  obtain ⟨-, hl, -, ex, hex, hlev⟩ := syncAll_shape orig (resumePendingBase orig bs f)
  exact ⟨ex, hex, hlev⟩

/-- The retired value's pin holds for it: `valueLiteral slot v` accepts
`v` itself. (Boolean pins and integer pins; the decision vocabulary of
`splitData` is exactly `valueLiteral`.) -/
theorem valueLiteral_valueHolds_self {slot : Nat} {v : Value} {l : Literal}
    (h : valueLiteral slot v = some l) : l.valueHolds v = true := by
  cases v with
  | bool b =>
      simp only [valueLiteral, Option.some.injEq] at h
      subst h
      cases b <;> rfl
  | int i =>
      simp only [valueLiteral, Option.some.injEq] at h
      subst h
      simp [Literal.valueHolds, negNe, Value.intView]
  | setOfInt _ => simp [valueLiteral] at h
  | array _ => simp [valueLiteral] at h

/-- The pinned literal's slot is the requested slot. -/
theorem valueLiteral_atom_slot {slot : Nat} {v : Value} {l : Literal}
    (h : valueLiteral slot v = some l) : l.atom.slot = slot := by
  cases v with
  | bool b =>
      simp only [valueLiteral, Option.some.injEq] at h
      subst h
      rfl
  | int i =>
      simp only [valueLiteral, Option.some.injEq] at h
      subst h
      rfl
  | setOfInt _ => simp [valueLiteral] at h
  | array _ => simp [valueLiteral] at h

/-- Negation and normalization preserve the referenced slot. -/
theorem literal_negate_norm_atom_slot (l : Literal) :
    l.negate.norm.atom.slot = l.atom.slot := by
  obtain ⟨atom, positive⟩ := l
  cases atom <;> cases positive <;> rfl

/-- The retirement's literal entry: the pin's negation-and-normalization
falsifies the pinned value (the decision vocabulary has no double
negation issue: the negation of a Boolean or integer pin is a Boolean or
integer falsifier). -/
theorem valueLiteral_negate_norm_valueHolds_false {slot : Nat} {v : Value}
    {l : Literal} (h : valueLiteral slot v = some l) :
    l.negate.norm.valueHolds v = false := by
  cases v with
  | bool b =>
      simp only [valueLiteral, Option.some.injEq] at h
      subst h
      cases b <;> rfl
  | int i =>
      simp only [valueLiteral, Option.some.injEq] at h
      subst h
      simp [Literal.valueHolds, Literal.negate, Literal.norm, negNe,
        Value.intView]
  | setOfInt _ => simp [valueLiteral] at h
  | array _ => simp [valueLiteral] at h

/-- REPAIR CORRECTNESS (the conjunct `stepConsume` cannot supply): when the
dropped value `v` has a decision pin at the split slot `k`, the repaired
resume's trail contains a falsifying entry for `v` at that slot — so the
resumed state represents exactly the sibling alternative, not the failed
child. -/
theorem resumeSibling_retires {bs : BranchState leaf} {f : BranchFrame}
    {k : Nat} {v : Value} {l : Literal}
    (hl : valueLiteral k v = some l) :
    ∃ e ∈ (resumeSibling bs f k v).trail,
      e.literal.atom.slot = k ∧ e.literal.valueHolds v = false := by
  have hmem : { literal := l.negate.norm, level := f.level, reason := none } ∈
      (retiredEntryAt f.level k v).toList := by
    rw [retiredEntryAt, hl]
    exact List.mem_singleton_self _
  refine ⟨{ literal := l.negate.norm, level := f.level, reason := none },
    ?_,
    by rw [literal_negate_norm_atom_slot, valueLiteral_atom_slot hl],
    valueLiteral_negate_norm_valueHolds_false hl⟩
  rw [resumeSibling_trail]
  exact List.mem_append_right _ hmem

end LeanFzn.Solver.Propagation

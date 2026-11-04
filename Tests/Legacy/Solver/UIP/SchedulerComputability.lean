/-
Tests/SchedulerComputability.lean — PLAN X1 prototype
=====================================================

Purpose (PLAN.md gate X1):
  Demonstrate a **compiled, fuel-free, well-founded recursive driver** pattern
  whose decrease evidence is **proof-erased** in runtime data, and which can be
  instantiated with P5's reachable-progress theorem for the real scheduler
  driver (X2).  `noncomputable def` plus an existence theorem is explicitly
  NOT the accepted pattern; this file contains computable `def`s only and the
  driver is actually evaluated at the bottom (temporary `#eval`, removed before
  handoff — the observed output is reported in the X1 handoff).

Contents
  §1  A generic Nat-ranked driver (`NatState`): the minimal shape.
  §2  A lexicographic rank (`Rank`, `Rank.lt`, `Rank.lt_wf`) with an explicit
      `WellFoundedRelation` instance, mirroring the `C3a.RankLt` shape used by
      `LeanFzn.Solver/LCG/Proofs/SchedulerProgress.lean` (same three-component lex
      disjunction, here on an owned structure so that `decreasing_by` sees the
      disjunction itself and does not depend on how the core product instance
      happens to unfold).
  §3  A scheduler-shaped state (`SchedState`) with the phase pattern
      jump / propagate / decide-split / handoff / consume, per-arm strict
      decrease theorems on `rank = (frontier, mass, phase)`, a dispatcher
      `step : SchedState → Option SchedState`, the driver `run` with
      `termination_by rank s` + `decreasing_by`, and the terminal spec
      `run_frontier : (run s).frontier = 0`.

HOW P5 WILL CONSUME THIS (X2 integration contract)
--------------------------------------------------
The real driver is exactly this shape, instantiated with the real scheduler
state and the P5 rank:

  * P5 owns a reachable-progress theorem of the form
        ReachablePhaseProgress :
          ∀ s, SchedulerReachable s → ∃ s', schedulerNext s = some s' ∧
               RankLt (SchedulerRank s') (SchedulerRank s)
    (or the per-arm form currently in `C3a`: `arm_propagate`, `arm_decide`,
    `arm_fallback_composite`, `arm_localExclude_then_consume`, plus the P3/P4
    jump facts).  P5 supplies **the proposition**; it is the only termination
    content needed.
  * X2 writes
        def run (s : SchedulerConfig leaf) : SchedulerConfig leaf :=
          match h : schedulerNext s with
          | none    => s
          | some s' => run s'
        termination_by SchedulerRank s
        decreasing_by <proof from the P5 theorem + the `h : schedulerNext s = some s'` equation>
    — the same `match h : ...` + `decreasing_by` pattern as `SchedState.run`
    below, with `step_decreases` replaced by the reachable-step decrease.
  * The recognizable-obligation shape is `RankLt (rank s') (rank s)`: in this
    file `SchedState.step_decreases` has literally that shape (with `Rank`
    the owned three-component lex rank).  For X2 with `C3a.RankLt` on
    `Nat × (Nat × Nat)`, either (a) declare the instance
        instance : WellFoundedRelation (Nat × (Nat × Nat)) := ⟨RankLt, rankLt_wf⟩
    in X2's module (local instance, so it shadows the core product instance in
    that file only — `rankLt_of_inst` in `SchedulerProgress.lean` proves
    `RankLt a b → Prod.Lex ... a b`, which is exactly the coherence fact an
    instance override needs), or (b) map through a tiny owned structure as in
    §2 below with `rankLt_wf` composed via `Subrelation.wf`/`InvImage.wf`
    exactly as `Rank.lt_wf` is built here from the core product relation.

PROOF ERASURE AND CLASSICAL CHOICE — the X1 analysis
----------------------------------------------------
Runtime data must not carry proof terms.  In this file:

  * the state (`SchedState`), the successor computation
    (`step : SchedState → Option SchedState`), and the measure
    (`rank : SchedState → Rank`, landing in `Nat`-valued fields) contain **no
    proof fields, no subtypes, no existentials, no `Prop`-valued data**;
  * the decrease evidence `step_decreases` is a separate `Prop`-valued theorem.
    It is consumed only by the kernel's well-founded recursion machinery inside
    `termination_by`/`decreasing_by`, where it is erased: the equation compiler
    the equation compiler compiles `run` as the loop "evaluate `step`; on
    `none` return the state; on `some s'` continue", and the `WellFounded.fix` accessibility proof is
    erased by proof irrelevance (Prop).  Consequently `#eval (run s)` returns
    the terminal state (§4) and `#print axioms` shows the runtime functions are
    **axiom-free** while the decrease proofs and `run` depend only on
    `[propext, Quot.sound]` — **no `Classical.choice`** (observed; the two
    disjunctive arm proofs needed explicit `Or` case analysis instead of a bare
    `omega` on a disjunction over equalities, which would introduce
    `Classical.choice`).

Where classical choice would sneak in — and how this pattern avoids it:

  1. **Existential decrease witnesses in runtime data.**  If `step` returned a
     subtype `{s' // rank s' < rank s}` (or `Sigma`-style data with a proof
     field), every step would carry a proof term, and after erasure the kernel
     would still accept it — but the *computation* would only be defined up to
     the choice of witness, and any consumer using `step` to choose among
     alternatives would need `Classical.choice` to extract the successor from
     an existence proof.  Here `step` computes the successor by pattern
     matching on `Nat`s only; the decrease is proven *about* that function.
  2. **`noncomputable def` + existence.**  Proving `∃ s', ...` by classical
     reasoning and then defining the driver through `Classical.choose` (or
     declaring it `noncomputable`) makes the driver non-executable: `#eval`
     fails and no compiled executable exists.  This file is a counter-pattern
     demonstration: everything in the runtime path is computable.
  3. **Well-foundedness proofs from classical logic.**  `WellFounded` proofs
     built with `Classical.choice`/`em` would mark the *definition* as
     noncomputable in Lean 4's analysis (`#print axioms` would show
     `Classical.choice`).  `Rank.lt_wf` below reuses only the core product
     relation's well-foundedness (`InvImage.wf`, `Subrelation.wf`), which is
     classical-free.
  4. **`partition`-style dispatch.**  The dispatcher is a chain of decidable
     `Nat` comparisons (`if s.phase = 3 then ...`), i.e. pure computation; no
     `Classical.decEq`, no `Classical.choice` on propositions.  All `if`s in
     the runtime path have decidable arithmetic conditions.

DAG: prelude only (no imports) -> this module.  Nothing in the runtime path
depends on `LeanFzn.Solver/LCG`; the bridge to the real scheduler is documented above
and is X2's integration step.
-/

namespace Tests.Legacy.Solver.UIP.SchedulerComputability

/-! ## §1 Generic pattern: a Nat-ranked computable driver -/

/-- Minimal state for the generic pattern: a counter that counts down. -/
structure NatState where
  n : Nat
deriving Repr, DecidableEq

namespace NatState

/-- One computable step: `none` at the terminal state `n = 0`, otherwise
decrement.  Pure pattern matching on a `Nat` — no proofs in the data. -/
def step (s : NatState) : Option NatState :=
  if s.n = 0 then none else some ⟨s.n - 1⟩

/-- The decrease evidence for `step`: a `Prop`-valued theorem, proved
constructively (`omega`), consumed only by `decreasing_by` below. -/
theorem step_decreases (s s' : NatState) (h : step s = some s') : s'.n < s.n := by
  by_cases hn : s.n = 0
  · rw [step, if_pos hn] at h
    cases h
  · rw [step, if_neg hn] at h
    have hs' : s' = ⟨s.n - 1⟩ := (Option.some.inj h).symm
    have hn' : 0 < s.n := Nat.pos_of_ne_zero hn
    rw [hs']
    show s.n - 1 < s.n
    omega

/-- The fuel-free driver: recurse on the successor while one exists, stop on
`none`.  `termination_by s.n` uses the state's own field as the measure;
`decreasing_by` discharges the well-foundedness obligation with the erased
`Prop` theorem above.  The `match _h : ...` equation is named `_h` so it is
linter-exempt while still visible to `decreasing_by`. -/
def run (s : NatState) : NatState :=
  match _h : step s with
  | none => s
  | some s' => run s'
termination_by s.n
decreasing_by exact step_decreases s s' _h

/-- The driver returns the state unchanged at a `step`-fixpoint. -/
theorem run_of_step_eq_none (s : NatState) (h : step s = none) : run s = s := by
  rw [run]
  rw [h]

/-- The recursion equation of the driver at a live step. -/
theorem run_of_step_eq_some (s s' : NatState) (h : step s = some s') : run s = run s' := by
  rw [run]
  rw [h]

/-- Functional induction on the compiled driver. -/
theorem run_n_eq_zero (s : NatState) : (run s).n = 0 := by
  induction s using run.induct with
  | case1 s h =>
      rw [run_of_step_eq_none s h]
      by_cases hn : s.n = 0
      · exact hn
      · rw [step, if_neg hn] at h
        cases h
  | case2 s s' h ih =>
      rw [run_of_step_eq_some s s' h]
      exact ih

/-- The result of the run is a fixpoint of the step relation. -/
theorem run_step_eq_none (s : NatState) : step (run s) = none := by
  by_cases hn : (run s).n = 0
  · rw [step, if_pos hn]
  · rw [step, if_neg hn]
    exact absurd (run_n_eq_zero s) hn

end NatState

/-! ## §2 A lexicographic rank with an explicit well-founded instance -/

/-- The three-component measure carrier: mirror of `C3a.SchedulerRank`'s
codomain `Nat × (Nat × Nat)` (`frontierCost`, `Frame.mass`, `branch.level`),
here as an owned structure so the `WellFoundedRelation` instance below is
unambiguous. -/
structure Rank where
  frontier : Nat
  mass : Nat
  phase : Nat
deriving Repr, DecidableEq

namespace Rank

/-- The rank as a nested pair, for the bridge to the core product relation. -/
def toProd (r : Rank) : Nat × (Nat × Nat) := (r.frontier, (r.mass, r.phase))

/-- The lexicographic order, definitionally the same disjunction as
`C3a.RankLt` in `LeanFzn.Solver/LCG/Proofs/SchedulerProgress.lean`. -/
def lt (a b : Rank) : Prop :=
  a.frontier < b.frontier ∨
    (a.frontier = b.frontier ∧ (a.mass < b.mass ∨ (a.mass = b.mass ∧ a.phase < b.phase)))

/-- Bridge: `Rank.lt` implies the core product well-founded relation on
`Nat × (Nat × Nat)` (the pattern is the kernel-checked `rankLt_of_inst` from
`SchedulerProgress.lean`, re-instantiated on the owned structure). -/
theorem lt_of_inst {a b : Rank} (h : Rank.lt a b) :
    (inferInstance : WellFoundedRelation (Nat × (Nat × Nat))).rel (toProd a) (toProd b) := by
  have hrel : (inferInstance : WellFoundedRelation (Nat × (Nat × Nat))).rel =
      Prod.Lex (sizeOfWFRel.rel (α := Nat))
        (Prod.Lex (sizeOfWFRel.rel (α := Nat)) (sizeOfWFRel.rel (α := Nat))) := rfl
  rw [hrel]
  show Prod.Lex (sizeOfWFRel.rel (α := Nat))
    (Prod.Lex (sizeOfWFRel.rel (α := Nat)) (sizeOfWFRel.rel (α := Nat)))
    (a.frontier, (a.mass, a.phase)) (b.frontier, (b.mass, b.phase))
  rcases h with h | ⟨h1, h | ⟨h2, h3⟩⟩
  · exact Prod.Lex.left (b₁ := (a.mass, a.phase)) (b₂ := (b.mass, b.phase)) h
  · rw [← h1]
    exact Prod.Lex.right (a := a.frontier)
      (Prod.Lex.left (b₁ := a.phase) (b₂ := b.phase) h)
  · rw [← h1]
    show Prod.Lex (sizeOfWFRel.rel (α := Nat))
      (Prod.Lex (sizeOfWFRel.rel (α := Nat)) (sizeOfWFRel.rel (α := Nat)))
      (a.frontier, (a.mass, a.phase)) (a.frontier, (b.mass, b.phase))
    rw [← h2]
    exact Prod.Lex.right (a := a.frontier) (Prod.Lex.right (a := a.mass) h3)

/-- Well-foundedness of the lexicographic order: classical-free, obtained by
`InvImage.wf` (the measure `toProd`) from the core product relation. -/
theorem lt_wf : WellFounded Rank.lt :=
  Subrelation.wf (fun {_ _} h => lt_of_inst h)
    (InvImage.wf toProd (inferInstance : WellFoundedRelation (Nat × (Nat × Nat))).wf)

end Rank

/-- The instance `termination_by rank s` picks up for states valued in `Rank`. -/
instance : WellFoundedRelation Rank := ⟨Rank.lt, Rank.lt_wf⟩

/-! ## §3 Scheduler-shaped example: phase pattern with lexicographic decrease -/

/-- Scheduler-shaped state: `frontier` is the remaining work cost (current
frame + pending, cf. `C3a.SchedulerRank`'s first component), `mass` is the
current frame's domain mass (second component), and `phase` is the position in
the jump/decide/consume round (third component). -/
structure SchedState where
  frontier : Nat
  mass : Nat
  phase : Nat
deriving Repr, DecidableEq

namespace SchedState

/-- The lexicographic rank: `(frontier, mass, phase)`. -/
def rank (s : SchedState) : Rank := ⟨s.frontier, s.mass, s.phase⟩

/-- Terminal predicate: no frontier work left. -/
def Terminal (s : SchedState) : Prop := s.frontier = 0

/-! The per-arm successor computations (all pure `Nat` arithmetic). -/

/-- Bounded jump/backjump arm: retreats one frontier unit and restores a unit
of frame mass (phase back to propagate).  Bounded: only fires while
`frontier ≠ 0`, so it strictly decreases the first component. -/
def stepJump (s : SchedState) : SchedState := ⟨s.frontier - 1, s.mass + 1, 2⟩

/-- Propagate arm: removes one unit of domain mass.  Requires `mass > 0`; the
strict decrease is the second lex component. -/
def stepPropagate (s : SchedState) : SchedState := ⟨s.frontier, s.mass - 1, 2⟩

/-- Decide/split arm: the parent frame (cost `frontier + 1`) is replaced by its
children (total cost `frontier`), so the first component strictly decreases;
phase advances to consume.  Requires `frontier ≠ 0`. -/
def stepDecide (s : SchedState) : SchedState := ⟨s.frontier - 1, 1, 1⟩

/-- Handoff arm: a `Prop`-free phase transition (the rank's third component
strictly decreases because the arm discharges phase `1`). -/
def stepHandoff (s : SchedState) : SchedState := ⟨s.frontier, 0, 0⟩

/-- Consume arm: drops one frame; the round restarts at phase `3`, paid for by
the first component's strict decrease.  Requires `frontier ≠ 0`. -/
def stepConsume (s : SchedState) : SchedState := ⟨s.frontier - 1, 1, 3⟩

/-! Per-arm strict-decrease theorems, each with the `RankLt`-style conclusion.
Each proof is by `show`-reduction to the explicit lex disjunction + `omega`
(no classical logic, no `simp` unfolding of the runtime `if`s). -/

theorem jump_decreases (s : SchedState) (hf : s.frontier ≠ 0) :
    Rank.lt (rank (stepJump s)) (rank s) := by
  have hf' : 0 < s.frontier := Nat.pos_of_ne_zero hf
  show s.frontier - 1 < s.frontier ∨
    (s.frontier - 1 = s.frontier ∧
      (s.mass + 1 < s.mass ∨ (s.mass + 1 = s.mass ∧ 2 < s.phase)))
  omega

theorem propagate_decreases (s : SchedState) (hm : 0 < s.mass) :
    Rank.lt (rank (stepPropagate s)) (rank s) := by
  show s.frontier < s.frontier ∨
    (s.frontier = s.frontier ∧
      (s.mass - 1 < s.mass ∨ (s.mass - 1 = s.mass ∧ 2 < s.phase)))
  right
  refine ⟨rfl, ?_⟩
  left
  omega

theorem decide_decreases (s : SchedState) (hf : s.frontier ≠ 0) :
    Rank.lt (rank (stepDecide s)) (rank s) := by
  have hf' : 0 < s.frontier := Nat.pos_of_ne_zero hf
  show s.frontier - 1 < s.frontier ∨
    (s.frontier - 1 = s.frontier ∧
      (1 < s.mass ∨ (1 = s.mass ∧ 1 < s.phase)))
  omega

theorem handoff_decreases (s : SchedState) (h1 : s.phase = 1) :
    Rank.lt (rank (stepHandoff s)) (rank s) := by
  show s.frontier < s.frontier ∨
    (s.frontier = s.frontier ∧
      (0 < s.mass ∨ (0 = s.mass ∧ 0 < s.phase)))
  right
  refine ⟨rfl, ?_⟩
  by_cases hm : s.mass = 0
  · right
    exact ⟨hm.symm, by omega⟩
  · left
    omega

theorem consume_decreases (s : SchedState) (hf : s.frontier ≠ 0) :
    Rank.lt (rank (stepConsume s)) (rank s) := by
  have hf' : 0 < s.frontier := Nat.pos_of_ne_zero hf
  show s.frontier - 1 < s.frontier ∨
    (s.frontier - 1 = s.frontier ∧
      (1 < s.mass ∨ (1 = s.mass ∧ 3 < s.phase)))
  omega

/-- The dispatcher: computable, `Classical`-free (decidable `Nat` comparisons
only).  This is the `schedulerNext` analogue. -/
def arm (s : SchedState) : SchedState :=
  if s.phase = 3 then stepJump s
  else if s.phase = 2 then (if s.mass > 0 then stepPropagate s else stepDecide s)
  else if s.phase = 1 then stepHandoff s
  else stepConsume s

/-- Dispatch-level decrease: any state with nonterminal frontier strictly
decreases under `arm`. -/
theorem arm_decreases (s : SchedState) (hf : s.frontier ≠ 0) :
    Rank.lt (rank (arm s)) (rank s) := by
  unfold arm
  by_cases h3 : s.phase = 3
  · rw [if_pos h3]; exact jump_decreases s hf
  · rw [if_neg h3]
    by_cases h2 : s.phase = 2
    · rw [if_pos h2]
      by_cases hm : s.mass > 0
      · rw [if_pos hm]; exact propagate_decreases s hm
      · rw [if_neg hm]; exact decide_decreases s hf
    · rw [if_neg h2]
      by_cases h1 : s.phase = 1
      · rw [if_pos h1]; exact handoff_decreases s h1
      · rw [if_neg h1]; exact consume_decreases s hf

/-- The transition relation: `none` exactly at terminal states. -/
def step (s : SchedState) : Option SchedState :=
  if s.frontier = 0 then none else some (arm s)

/-- The decrease obligation in the exact shape P5 must supply for the real
transition system: from the runtime equation `step s = some s'`, conclude
`RankLt`-style strict decrease.  No reachability hypothesis is needed here
because the toy `arm` is total-decreasing; the real scheduler will carry
`SchedulerReachable s` as an extra hypothesis (P5). -/
theorem step_decreases (s s' : SchedState) (h : step s = some s') :
    Rank.lt (rank s') (rank s) := by
  by_cases hf : s.frontier = 0
  · rw [step, if_pos hf] at h
    cases h
  · rw [step, if_neg hf] at h
    rw [← Option.some.inj h]
    exact arm_decreases s hf

/-- The compiled driver: fuel-free well-founded recursion on the lexicographic
rank.  The decrease proof `step_decreases` lives only in `decreasing_by` and is
erased from the runtime path (no proof fields in `SchedState`). -/
def run (s : SchedState) : SchedState :=
  match _h : step s with
  | none => s
  | some s' => run s'
termination_by rank s
decreasing_by exact step_decreases s s' _h

/-- `step s = none` iff terminal (`frontier = 0`). -/
theorem step_eq_none_iff (s : SchedState) : step s = none ↔ s.frontier = 0 := by
  unfold step
  by_cases hf : s.frontier = 0
  · rw [if_pos hf]
    exact iff_of_true rfl hf
  · rw [if_neg hf]
    exact iff_of_false (fun h => by cases h) hf

/-- The driver returns the state unchanged at a `step`-fixpoint. -/
theorem run_of_step_eq_none (s : SchedState) (h : step s = none) : run s = s := by
  rw [run]
  rw [h]

/-- The recursion equation of the driver at a live step. -/
theorem run_of_step_eq_some (s s' : SchedState) (h : step s = some s') :
    run s = run s' := by
  rw [run]
  rw [h]

/-- **Spec (the `run_spec` obligation).**  The compiled run reaches a terminal
state: the frontier is `0`.  Proved by the functional induction principle
generated for `run` (`run.induct`), i.e. well-founded induction along the same
lex rank that drives termination. -/
theorem run_frontier (s : SchedState) : (run s).frontier = 0 := by
  induction s using run.induct with
  | case1 s h =>
      rw [run_of_step_eq_none s h]
      exact (step_eq_none_iff s).mp h
  | case2 s s' h ih =>
      rw [run_of_step_eq_some s s' h]
      exact ih

/-- The result of the run is a genuine `step`-fixpoint (the driver stops
because `step` is `none`, not because it ran out of fuel). -/
theorem run_terminal (s : SchedState) : step (run s) = none :=
  (step_eq_none_iff (run s)).mpr (run_frontier s)

theorem run_terminal_iff (s : SchedState) : step (run s) = none ↔ Terminal (run s) :=
  step_eq_none_iff (run s)

end SchedState

/-! ## §4 Observed execution (temporary runner removed)

The temporary `#eval`/`#print axioms` block (removed before handoff) was run
with `lake env lean Tests/SchedulerComputability.lean` (no imports, ~15 s):

```
#eval NatState.run ⟨7⟩                     ==> { n := 0 }
#eval (NatState.run ⟨7⟩).n                 ==> 0
#eval SchedState.run ⟨3, 2, 3⟩             ==> { frontier := 0, mass := 1, phase := 3 }
#eval (SchedState.run ⟨3, 2, 3⟩).frontier  ==> 0
#eval SchedState.run ⟨2, 5, 2⟩             ==> { frontier := 0, mass := 1, phase := 3 }
#eval SchedState.step ⟨2, 1, 2⟩            ==> some { frontier := 2, mass := 0, phase := 2 }
#eval SchedState.step ⟨0, 4, 0⟩            ==> none
```

Axiom audit (`#print axioms`):

* `SchedState.arm`, `SchedState.step`, `Rank.lt_wf`: **no axioms**.
* `step_decreases`, `arm_decreases`, `SchedState.run`, `NatState.run`:
  `[propext, Quot.sound]` only — **no `Classical.choice`**.

This is the executable evidence for the X1 gate: the compiled, fuel-free
driver actually runs and its runtime path carries no proof terms and no
classical axioms.
-/

/-! ## §5 Runnable entry point (added by the integration owner)

Reproduces the §4 evidence as a registered executable:
`lake exe tests_scheduler_computability`. -/

/-- Print the compiled fuel-free runs (X1 gate evidence). -/
def demo : IO Unit := do
  IO.println s!"NatState.run 7 = {(NatState.run ⟨7⟩).n}"
  IO.println s!"SchedState.run (3,2,3): frontier {(SchedState.run ⟨3, 2, 3⟩).frontier}, mass {(SchedState.run ⟨3, 2, 3⟩).mass}, phase {(SchedState.run ⟨3, 2, 3⟩).phase}"
  IO.println s!"SchedState.step (0,4,0) is none: {(SchedState.step ⟨0, 4, 0⟩).isNone}"

end Tests.Legacy.Solver.UIP.SchedulerComputability

/-- Executable root (registered in lakefile.toml). -/
def main : IO Unit := Tests.Legacy.Solver.UIP.SchedulerComputability.demo

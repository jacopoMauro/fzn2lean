/-
File: LeanFzn/Solver/Propagation/Proofs/Theory.lean

Purpose:
  The constructive no-excluded-solution theory for the propagation loop
  (PLAN.md Step 2, Step 2.E items 3–6 groundwork). Proved here:

  * `SolvedBy` — the master invariant (every internal problem solution
    is represented by the state);
  * `negOnTrail_falsifies_entry` — entry-level trail falsification;
  * `enqueueNorm_no_opposing` — the opposing-fact branch of `enqueueNorm`
    is unreachable for a justified enqueue (a literal true at some
    represented solution cannot contradict the trail that the same
    solution satisfies), which retires the origin-lift's tautological
    pair arm for justified enqueues (Step 2.E item 4);
  * `enqueueNorm_solvedBy` — the all-branch enqueue step: under `SolvedBy`
    and literal truth at every internal solution, `enqueueNorm` returns a
    state that again solves-by, and either the conflict slot stays clear
    or no internal solution exists (the vacuous exclusion case);
  * `scanClause_inl_eq` / `scanConflict_excludes` — the scan-arm
    exclusion (Step 2.E item 3): a scan-witnessed conflict is
    trail-falsified at every represented solution;
  * `propSafe_of_conflFalsified` — the bridge from per-family
    conflict-falsification contracts to the sweep's `PropSafe`
    (Step 2.E item 5 packaging);
  * the per-gate inverses (`narrowHi_conflict_inv`,
    `narrowLo_conflict_inv`) and the extrema-coherence bridges
    (`fits_domMaxI_ge`, `fits_domMinI_le`) that the concrete families
    instantiate against.

  Still open here (registered PLAN Step 2.E items 5–7): the concrete
  per-family nogood validity theorems and the sweep/loop fold lift
  (`propagateLoop_excludes`), and the final `EngineSafe` removal.

Dependencies:
  - LeanFzn.Solver.Reference.Engine: `propagateLoop`, `runPropagators`, `enqueueNorm`.
  - LeanFzn.Solver.Propagation.Encoding: literal evaluation algebra.
  - LeanFzn.Solver.Propagation.Invariants: `ProblemSolution`, `State.Represents`.
  - LeanFzn.Solver.Propagation.Proofs.Lift: the firing lemma and the slot-range lemma
    (the Represents-transfer machinery), the scan soundness twins
    (`scanClause_conflict_falsified'`, `scanClause_unit_justified'`).

DAG:
  LeanFzn.Solver.UIP.Engine + LeanFzn.Solver.UIP.Invariants + LeanFzn.Solver.UIP.Proofs.Lift -> LeanFzn.Solver.UIP.Proofs.Theory
  -> LeanFzn.Solver.UIP.Proofs.Search (the leaf arm's SolvedBy premise)
-/

import LeanFzn.Solver.Reference.Engine
import LeanFzn.Solver.Propagation.Encoding
import LeanFzn.Solver.Propagation.Invariants
import LeanFzn.Solver.Propagation.Proofs.Lift


namespace LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Reference
open LeanFzn LeanFzn.Solver.Core

/-! ## The state-transfer propagator contract -/

/-- Propagator soundness at state `st`, phrased for the exclusion
    argument: implied literals are true at every represented internal
    solution; conflict clauses are unsatisfied at every represented
    internal solution. No reason-entailment premise — the reason
    matters for conflict analysis (L0.4), not for exclusion. -/
structure PropSafe (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop)
    (props : List Propagator) (st : State) : Prop where
  impliedTrueAt : ∀ p ∈ props, ∀ l r,
    p.run st = .implied l r →
    ∀ a, (ProblemSolution problem constraintHolds a ∧ st.Represents a) →
      l.eval a = some true
  conflictExcludes : ∀ p ∈ props, ∀ c,
    p.run st = .conflict c →
    ∀ a, (ProblemSolution problem constraintHolds a ∧ st.Represents a) →
      ¬ c.SatisfiedBy a

/-- The contract, universally over observed states: per-family
    propagator soundness in the shape the sweep fold needs (Step 2.2,
    obligation 5 of the PLAN's premise-drop order). -/
def PropSafeUniv (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop)
    (props : List Propagator) : Prop :=
  ∀ st, PropSafe problem constraintHolds props st

/-- The coherence-relativized universal safety: at every
    domain-coherent state (the engine's run invariant), the
    propagators are safe. This is the honest shape for bound
    propagators whose implied literals read order atoms —
    non-coherent states are unreachable from the initial state. -/
def CoherentSafeUniv (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop)
    (props : List Propagator) : Prop :=
  ∀ st, DomainCoherent problem st →
    PropSafe problem constraintHolds props st

/-- Un-relativized safety implies the relativized form. -/
theorem PropSafeUniv_coherent {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {props : List Propagator}
    (h : PropSafeUniv problem constraintHolds props) :
    CoherentSafeUniv problem constraintHolds props :=
  fun st _ => h st


/-- NOGOOD ENTITLEMENT: the refutation-grade propagator contract —
    beyond excluding represented solutions, every reported conflict
    clause is ENTITLED at every internal solution (has a true literal).
    This is what the run-level UNSAT refutation needs: the terminal
    conflict clause itself must be unsatisfiable clause-by-clause, not
    merely at states that happen to represent solutions. -/
def PropEntitled (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop)
    (props : List Propagator) : Prop :=
  ∀ st, ∀ p ∈ props, ∀ c, p.run st = .conflict c →
    ∀ a, ProblemSolution problem constraintHolds a →
      ∃ l ∈ c, l.eval a = some true

/-- enqueueNorm preserves the decision level. -/
theorem enqueueNorm_decisionLevel {st : State} {l0 : Literal}
    {reason : Option Reason} :
    (enqueueNorm st l0 reason).decisionLevel = st.decisionLevel := by
  simp only [enqueueNorm]
  split
  · rfl
  · split
    · rfl
    · rfl

/-- The sweep preserves the decision level. -/
theorem runPropagators_go_decisionLevel : ∀ (props : List Propagator)
    (s : State),
    (runPropagators.go props s).decisionLevel = s.decisionLevel := by
  intro props
  induction props with
  | nil => intro s; rfl
  | cons p rest ih =>
      intro s
      simp only [runPropagators.go]
      split
      · rfl
      · split
        · exact ih s
        · rfl
        · rename_i l r heq
          rw [ih (enqueueNorm s l (some r)), enqueueNorm_decisionLevel]

theorem runPropagators_decisionLevel (props : List Propagator) (st : State) :
    (runPropagators props st).decisionLevel = st.decisionLevel := by
  unfold runPropagators
  exact runPropagators_go_decisionLevel props st

/-- The engine's propagation fuel at a state — the exact expression
    `lcgSearch.go` budgets for one propagation phase (mirrors
    `LeanFzn/Solver/UIP/Engine.lean`'s `lcgSearch.go`). Kept here so the proof
    layer's terminal-shape theorems state the same fuel the executable
    uses. -/
def engineFuel (st : State) : Nat :=
  32 + 8 * st.domains.length + 4 * st.trail.length

/-- THE PROPAGATION LEVEL THEOREM: the loop never changes the decision
    level — so every engine `.unsat` at level 0 arises from a
    pre-propagation iterate that was already at level 0. -/
theorem propagateLoop_decisionLevel (props : List Propagator) :
    ∀ (fuel : Nat) (st : State),
      (propagateLoop fuel props st).decisionLevel = st.decisionLevel := by
  intro fuel
  induction fuel with
  | zero => intro st; rfl
  | succ k ih =>
      intro st
      simp only [propagateLoop]
      split
      · rfl
      · -- the scan verdict governs; case it via the match equation
        rename_i hconf
        cases hscan : scanAll st with
        | none =>
            have hgo : (runPropagators props st).decisionLevel
                = st.decisionLevel := runPropagators_decisionLevel props st
            by_cases hlen : ((runPropagators props st).trail.length ==
                st.trail.length) = true
            · rw [if_pos hlen, hgo]
            · rw [if_neg hlen, ih (runPropagators props st), hgo]
        | some verdict =>
            match verdict with
            | Sum.inl c => rfl
            | Sum.inr w =>
                obtain ⟨l, r⟩ := w
                rw [ih (enqueueNorm st l (some r)), enqueueNorm_decisionLevel]

/-- The represented-solution bundle: every internal problem solution is
    represented by the state. A sound conflict excludes all represented
    solutions — and here ALL internal solutions are represented, so the
    exclusion is unconditional. -/
def SolvedBy (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop)
    (st : State) : Prop :=
  ∀ a, ProblemSolution problem constraintHolds a → st.Represents a

/-! ## Trail falsification -/

/-- If the (canonical) negation of `l` is on the trail, then any
    assignment satisfying the trail makes `l` FALSE. Entry-level: no
    normalization premise on `l` itself. -/
theorem negOnTrail_falsifies_entry {st : State} {l : Literal}
    {a : Assignment}
    (hneg : st.negOnTrail l = true)
    (hsat : st.TrailSatisfied a) :
    l.eval a = some false := by
  unfold State.negOnTrail at hneg
  rw [List.any_eq_true] at hneg
  obtain ⟨e, hem, heb⟩ := hneg
  have hlit : e.literal = l.negate.norm := by
    simpa only [litEqB, decide_eq_true_eq] using heb
  have hev : e.literal.eval a = some true := hsat e hem
  rw [hlit, Literal.norm_eval (l.negate) a, Literal.eval_negate l a] at hev
  cases h : l.eval a with
  | none => rw [h] at hev; simp at hev
  | some b =>
      rw [h] at hev
      cases b <;> simp at hev <;> rfl

/-! ## The enqueueNorm branch algebra

`enqueueNorm st l0 reason` has three branches (see `LeanFzn.Solver.UIP.Engine`):

* skip (`l0.norm` already on trail): the state is returned unchanged;
* opposing fact (`¬l0.norm` on trail): the state's conflict slot is
  set to the pair — under `SolvedBy` and a justified literal this
  branch is UNREACHABLE (below);
* fresh: the trail grows by `l0.norm`, the domains narrow by
  `domOfLit`.

The fresh branch preserves `SolvedBy` (`enqueueNorm_fresh_solvedBy`,
via the firing lemma); the skip branch is the identity; the opposing
branch contradicts the justification. -/

/-- The opposing-fact branch of `enqueueNorm` is unreachable for a
    justified enqueue: if `l0.norm` is true at some internal solution
    represented by `st`, then `st.negOnTrail l0.norm` is false. -/
theorem enqueueNorm_no_opposing
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st : State} {l0 : Literal} {a : Assignment}
    (hsol : ProblemSolution problem constraintHolds a)
    (hrep : st.Represents a)
    (halt : l0.norm.eval a = some true)
    (hneg : st.negOnTrail l0.norm = true) :
    False := by
  obtain ⟨_, htrail, _, _⟩ := hrep
  have hf : l0.norm.eval a = some false :=
    negOnTrail_falsifies_entry hneg htrail
  rw [halt] at hf
  exact absurd hf (by simp)

/-- The fresh branch of `enqueueNorm` preserves `SolvedBy`: the
    enqueued literal is true at every internal solution (so the trail
    gains only justified entries), and the narrowed domains keep every
    fitting solution a fitting one (firing lemma). -/
theorem enqueueNorm_fresh_solvedBy
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st : State} {l0 : Literal} {reason : Option Reason}
    (hnew : st.litOnTrail l0.norm = false)
    (hneg : st.negOnTrail l0.norm = false)
    (hlit : ∀ a, ProblemSolution problem constraintHolds a →
      l0.norm.eval a = some true)
    (hsol : SolvedBy problem constraintHolds st) :
    SolvedBy problem constraintHolds
      (enqueueNorm st l0 reason) := by
  intro a ha
  have hrep := hsol a ha
  obtain ⟨hfit, htrail, hclauses, hlearned⟩ := hrep
  have hal : l0.norm.eval a = some true := hlit a ha
  have hinrange : l0.norm.atom.slot < a.length :=
    eval_lit_some_slot_lt (l := l0.norm) hal
  have hfitN : a.Fits (domOfLit st.domains l0.norm) :=
    firing (doms := st.domains) (l := l0.norm) (a := a) hfit hinrange hal
  have htrailN : (enqueueNorm st l0 reason).TrailSatisfied a :=
    enqueueNorm_fresh_trailSat (st := st) (l0 := l0)
      (reason := reason) hnew hneg ha htrail hal
  unfold enqueueNorm at htrailN ⊢
  simp only [hnew, hneg, Bool.false_eq_true, if_false] at htrailN ⊢
  refine ⟨?_, htrailN, hclauses, hlearned⟩
  have hdom : (enqueue st l0.norm reason).domains = st.domains := rfl
  rw [hdom]; exact hfitN

/-- The fresh branch of `enqueueNorm` (zeta-reduced) has the enqueued
    state's conflict slot: the record only replaces `domains`. -/
theorem freshProj_conflict {st : State} {l : Literal}
    {reason : Option Reason} :
    ({ domains := domOfLit (enqueue st l reason).domains l,
       trail := (enqueue st l reason).trail,
       decisionLevel := (enqueue st l reason).decisionLevel,
       clauses := (enqueue st l reason).clauses,
       learned := (enqueue st l reason).learned,
       queue := (enqueue st l reason).queue,
       conflict := (enqueue st l reason).conflict } : State).conflict
      = (enqueue st l reason).conflict := rfl

/-- ALL-BRANCH enqueue step for a justified literal: under `SolvedBy`
    and literal truth at every internal solution, `enqueueNorm` returns
    a state that again solves-by; additionally, either the conflict slot
    stays clear, or no internal solution exists (the vacuous branch).
    (When a solution exists, the opposing branch is unreachable, so the
    conflict slot genuinely stays clear; when none exists, conflict-none
    is not needed — exclusion is already unconditional.) -/
theorem enqueueNorm_solvedBy
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st : State} {l0 : Literal} {reason : Option Reason}
    (hnone : st.conflict = none)
    (hsol : SolvedBy problem constraintHolds st)
    (hlit : ∀ a, ProblemSolution problem constraintHolds a →
      l0.norm.eval a = some true) :
    ((enqueueNorm st l0 reason).conflict = none ∨
        ¬ ∃ b, ProblemSolution problem constraintHolds b) ∧
      SolvedBy problem constraintHolds (enqueueNorm st l0 reason) := by
  by_cases hsolvable : ∃ b, ProblemSolution problem constraintHolds b
  · -- solutions exist: dispatch on the three branches
    obtain ⟨b, hb⟩ := hsolvable
    refine ⟨Or.inl ?_, ?_⟩
    · simp only [enqueueNorm]
      split
      · exact hnone
      · split
        · exfalso
          rename_i hneg
          exact enqueueNorm_no_opposing (problem := problem)
            (constraintHolds := constraintHolds) (st := st) (l0 := l0)
            (a := b) hb (hsol b hb) (hlit b hb) hneg
        · rw [freshProj_conflict]
          rw [show (enqueue st l0.norm reason).conflict = st.conflict
            from rfl]
          exact hnone
    · simp only [enqueueNorm]
      split
      · exact hsol
      · split
        · exfalso
          rename_i hneg
          exact enqueueNorm_no_opposing (problem := problem)
            (constraintHolds := constraintHolds) (st := st) (l0 := l0)
            (a := b) hb (hsol b hb) (hlit b hb) hneg
        · rename_i hnew hneg
          have hnew' : st.litOnTrail l0.norm = false := by
            cases hb2 : st.litOnTrail l0.norm with
            | true => exact absurd hb2 hnew
            | false => rfl
          have hneg' : st.negOnTrail l0.norm = false := by
            cases hb2 : st.negOnTrail l0.norm with
            | true => exact absurd hb2 hneg
            | false => rfl
          -- the zeta-reduced record IS the fresh-branch enqueueNorm
          have hEq : ((State.mk (domOfLit
                (enqueue st l0.norm reason).domains l0.norm)
              (enqueue st l0.norm reason).trail
              (enqueue st l0.norm reason).decisionLevel
              (enqueue st l0.norm reason).clauses
              (enqueue st l0.norm reason).learned
              (enqueue st l0.norm reason).queue
              (enqueue st l0.norm reason).conflict))
            = (enqueueNorm st l0 reason) := by
            unfold enqueueNorm
            simp only [hnew', hneg', Bool.false_eq_true, if_false]
          rw [hEq]
          exact enqueueNorm_fresh_solvedBy hnew' hneg' hlit hsol
  · -- no internal solution exists: SolvedBy is vacuous; the conflict
    -- shape is covered by the disjunct's right arm.
    refine ⟨Or.inr hsolvable, ?_⟩
    intro a ha
    exact absurd ⟨a, ha⟩ hsolvable

/-! ## Step 2.E item 3: the scan-arm exclusion -/

/-- The scan's conflict verdict reports the scanned clause itself (the
    scan returns its input clause in the `.inl` branch). -/
theorem scanClause_inl_eq {st : State} {c d : Clause}
    (h : scanClause st d = some (Sum.inl c)) : c = d := by
  unfold scanClause at h
  split at h
  · exact absurd h (by simp)
  · rename_i _
    match hh : d.filter (fun l => !st.negOnTrail l) with
    | [] =>
        rw [hh] at h
        cases h
        rfl
    | [l] => rw [hh] at h; exact absurd h (by simp)
    | l1 :: l2 :: rest => rw [hh] at h; exact absurd h (by simp)

/-- THE SCAN EXCLUSION (Step 2.E item 3): from a scan-witnessed conflict
    report, the reported clause is falsified at every represented
    solution of the reporting state — the scan's own conflict verdict
    (`scanClause_conflict_falsified'`) plus the identity
    `scanClause_inl_eq`. -/
theorem scanConflict_excludes
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st : State} {cc : Clause}
    (hreport : ∃ d, scanClause st d = some (Sum.inl cc))
    (hsol : SolvedBy problem constraintHolds st) :
    ∀ a, ProblemSolution problem constraintHolds a →
      ¬ cc.SatisfiedBy a := by
  obtain ⟨d, hd⟩ := hreport
  have hcd : cc = d := scanClause_inl_eq hd
  intro a ha hsat
  have hd2 : scanClause st d = some (Sum.inl d) := by
    rw [show cc = d from hcd] at hd
    exact hd
  -- the trail-satisfaction of a: from the representation
  have htrail : st.TrailSatisfied a := (hsol a ha).2.1
  -- the scan falsified every literal at a:
  have hf : ∀ l ∈ d, l.eval a = some false :=
    scanClause_conflict_falsified' (st := st) (c := d) (a := a) hd2 htrail
  -- but `hsat` needs some literal of cc (:= d) true at a:
  obtain ⟨l, hl, hevl⟩ := hsat
  have hl' : l ∈ d := hcd ▸ hl
  have hfl : l.eval a = some false := hf l hl'
  rw [hevl] at hfl
  simp at hfl

/-! ## Step 2.E item 5: the per-gate inverses and coherence bridges -/

/-- EXTREMA COHERENCE (upper): the domain maximum of slot `s` at `st`
    bounds the slot's integer view above in every fitting assignment. -/
theorem fits_domMaxI_ge {st : State} {a : Assignment} {s : Nat} {mx : Int}
    (hfit : a.Fits st.domains)
    (hmax : domMaxI (st.domains.getD s Dom.empty) = some mx)
    {i : Int} (hslot : slotInt a s = some i) :
    i ≤ mx := by
  obtain ⟨v, hv, hvi, hlt⟩ := slotInt_mem (doms := st.domains) hfit hslot
  exact domMaxI_ge v i hvi (hfit.2 s v hv) hmax

/-- EXTREMA COHERENCE (lower): the domain minimum of slot `s` bounds the
    slot's integer view below in every fitting assignment. -/
theorem fits_domMinI_le {st : State} {a : Assignment} {s : Nat} {mn : Int}
    (hfit : a.Fits st.domains)
    (hmin : domMinI (st.domains.getD s Dom.empty) = some mn)
    {i : Int} (hslot : slotInt a s = some i) :
    mn ≤ i := by
  obtain ⟨v, hv, hvi, hlt⟩ := slotInt_mem (doms := st.domains) hfit hslot
  exact domMinI_le v i hvi (hfit.2 s v hv) hmin

/-- `narrowHi`'s conflict branch: when
    `narrowHi st s hi ng = .conflict c`, the extrema matched with
    `mn > hi` and `c = ng` (the gate's only conflict exit). -/
theorem narrowHi_conflict_inv {st : State} {s : Nat} {hi : Int}
    {ng : Clause} {c : Clause}
    (h : narrowHi st s hi ng = .conflict c) :
    ∃ mn mx, domMinI (st.domains.getD s Dom.empty) = some mn ∧
      domMaxI (st.domains.getD s Dom.empty) = some mx ∧ mn > hi ∧ c = ng := by
  unfold narrowHi at h
  split at h
  · rename_i mn mx hmn hmx
    split at h
    · rename_i hgt
      have hinj : (PropagationResult.conflict ng) =
        (PropagationResult.conflict c) := h
      simp only [PropagationResult.conflict.injEq] at hinj
      exact ⟨mn, mx, hmn, hmx, by simpa using hgt, hinj.symm⟩
    · split at h
      · exact absurd h (by simp)
      · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- `narrowLo`'s conflict branch: when
    `narrowLo st s lo ng = .conflict c`, the extrema matched with
    `mx < lo` and `c = ng` (the gate's only conflict exit). -/
theorem narrowLo_conflict_inv {st : State} {s : Nat} {lo : Int}
    {ng : Clause} {c : Clause}
    (h : narrowLo st s lo ng = .conflict c) :
    ∃ mn mx, domMinI (st.domains.getD s Dom.empty) = some mn ∧
      domMaxI (st.domains.getD s Dom.empty) = some mx ∧ mx < lo ∧ c = ng := by
  unfold narrowLo at h
  split at h
  · rename_i mn mx hmn hmx
    split at h
    · rename_i hlt'
      have hinj : (PropagationResult.conflict ng) =
        (PropagationResult.conflict c) := h
      simp only [PropagationResult.conflict.injEq] at hinj
      exact ⟨mn, mx, hmn, hmx, by simpa using hlt', hinj.symm⟩
    · split at h
      · exact absurd h (by simp)
      · exact absurd h (by simp)
  · exact absurd h (by simp)

/-! ### The leSlot family instance (item 5, first family) -/

/-- THE leSlot GATE EXCLUSION: at a fitting assignment whose slot views
    the leSlot constraint binds (`p ≤ q`), a `narrowHi st i yj` conflict
    (domain minimum of `x` above the domain maximum of `y`) is
    impossible: `mn ≤ p ≤ q ≤ yj < mn`. This is the joint-falsity /
    exclusion kernel of the `int_le` family. -/
theorem leSlot_gate_excludes
    {st : State} {a : Assignment} {i j : Nat} {ng' : Clause}
    (hfit : a.Fits st.domains)
    (yj : Int)
    (hjy : domMaxI (st.domains.getD j Dom.empty) = some yj)
    (hc : narrowHi st i yj [posLe i yj, negLe j yj] = .conflict ng')
    (hle : ∀ (p q : Int), slotInt a i = some p → slotInt a j = some q →
      p ≤ q)
    (hi : Int) (hi' : slotInt a i = some hi)
    (hj : Int) (hj' : slotInt a j = some hj) :
    False := by
  obtain ⟨mn, mx, hmn, hmx, hgt, _⟩ := narrowHi_conflict_inv
    (s := i) (hi := yj) hc
  have hge : mn ≤ hi := fits_domMinI_le hfit hmn hi'
  have hle2 : hj ≤ yj := fits_domMaxI_ge hfit hjy hj'
  have hcon := hle hi hj hi' hj'
  omega

/-! ### The PropSafe packaging bridge (item 5) -/

/-- PER-FAMILY TO SWEEP BRIDGE: per-family `PropSafe` obligations are
    orthogonal — a universal contract over ALL propagators restricts to
    each member, and a family's own exclusion wraps into the universal
    form when the remaining members are irrelevant at the call site
    (their `p.run` outputs are unconstrained; the contract is vacuous
    for them only if we never need to narrow). This theorem records the
    RESTRICTION direction (the universal contract implies each
    member's), which the sweep fold consumes hypothesis-wise. -/
theorem propSafe_restrict
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {props : List Propagator} {p : Propagator}
    (huniv : PropSafeUniv problem constraintHolds props)
    (hp : p ∈ props) (st : State) :
    p.run st = .stable ∨
      (∀ l r, p.run st = .implied l r →
        ∀ a, (ProblemSolution problem constraintHolds a ∧
          st.Represents a) → l.eval a = some true) ∧
      (∀ c, p.run st = .conflict c →
        ∀ a, (ProblemSolution problem constraintHolds a ∧
          st.Represents a) → ¬ c.SatisfiedBy a) := by
  by_cases hrun : p.run st = .stable
  · exact Or.inl hrun
  · refine Or.inr ⟨?_, ?_⟩
    · exact fun l r hres =>
        (huniv st).impliedTrueAt p hp l r hres
    · exact fun c hres =>
        (huniv st).conflictExcludes p hp c hres

/-! ## Step 2.E item 6: the sweep fold, the loop lift, and the master result

All three arm readings (scan-conflict falsification from item 3, scan-unit
justification, sweep-fold transfer) assemble into the constructive UNSAT
half of the engine: a conflict reported by a conflict-free propagation
run over state-universally sound propagators excludes every internal
solution. -/

/-- The enqueue step for a justified literal, with the conflict-clear
    disjunct resolved when solutions exist. -/
theorem enqueueNorm_justified_solvable
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st : State} {l0 : Literal} {reason : Option Reason}
    (hnone : st.conflict = none)
    (hsolvable : ∃ b, ProblemSolution problem constraintHolds b)
    (hrep : SolvedBy problem constraintHolds st)
    (hlit : ∀ a, ProblemSolution problem constraintHolds a →
      l0.norm.eval a = some true) :
    (enqueueNorm st l0 reason).conflict = none ∧
      SolvedBy problem constraintHolds (enqueueNorm st l0 reason) := by
  obtain ⟨hdisj, hsol2⟩ := enqueueNorm_solvedBy (problem := problem)
    (constraintHolds := constraintHolds) (st := st) (l0 := l0)
    (reason := reason) hnone hrep hlit
  refine ⟨?_, hsol2⟩
  rcases hdisj with hclear | hnoplex
  · exact hclear
  · exact absurd hsolvable hnoplex

/-! ## Coherence preservation through the propagation loop -/

/-- The propagator sweep preserves domain coherence (each implied
    literal goes through `enqueueNorm`, which maintains the
    domains-equal-fold equation by construction). -/
theorem runPropagators_go_coherent {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective} :
    ∀ (ps : List Propagator) (st : State),
      DomainCoherent problem st →
      DomainCoherent problem (runPropagators.go ps st) := by
  intro ps
  induction ps with
  | nil => intro st h; exact h
  | cons p rest ih =>
      intro st h
      show DomainCoherent problem
        (if st.conflict.isSome = true then st else
          match p.run st with
          | .stable => runPropagators.go rest st
          | .conflict c => { st with conflict := some c }
          | .implied l r => runPropagators.go rest (enqueueNorm st l (some r)) )
      by_cases hconf : st.conflict.isSome = true
      · rw [if_pos hconf]; exact h
      · rw [if_neg hconf]
        cases hr : p.run st with
        | stable => exact ih st h
        | conflict c => exact h
        | implied l r => exact ih (enqueueNorm st l (some r)) (enqueueNorm_coherent h)

/-- The propagator sweep preserves domain coherence. -/
theorem runPropagators_coherent {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    (props : List Propagator) (st : State)
    (h : DomainCoherent problem st) :
    DomainCoherent problem (runPropagators props st) :=
  runPropagators_go_coherent props st h

/-- The propagation loop preserves domain coherence (each continuing
    arm is an `enqueueNorm` or a sweep, both coherent). -/
theorem propagateLoop_coherent {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {props : List Propagator} :
    ∀ (fuel : Nat) (st : State),
      DomainCoherent problem st →
      DomainCoherent problem (propagateLoop fuel props st) := by
  intro fuel
  induction fuel with
  | zero => intro st h; exact h
  | succ k ih =>
      intro st h
      unfold propagateLoop
      cases hconf : st.conflict.isSome with
      | true => exact h
      | false =>
          simp only [Bool.false_eq_true, if_false]
          cases hscan : scanAll st with
          | none =>
              simp only [hscan]
              have hcoh' : DomainCoherent problem (runPropagators props st) :=
                runPropagators_coherent props st h
              show DomainCoherent problem
                (let st' := runPropagators props st
                if st'.trail.length == st.trail.length then st'
                else propagateLoop k props st')
              by_cases hlen : (runPropagators props st).trail.length
                  == st.trail.length
              · rw [if_pos hlen]; exact hcoh'
              · rw [if_neg hlen]; exact ih _ hcoh'
          | some verdict =>
              cases verdict with
              | inl c => exact h
              | inr w =>
                  obtain ⟨l, r⟩ := w
                  exact ih _ (enqueueNorm_coherent h)

/-! ## The conflict-origin entitlement chain (per-solution form)

Both halves of the terminal refutation are per-solution: exclusion
("no literal of `c` is true at `a`") and entitlement ("some literal of
`c` is true at `a`") apply at the SAME solution, so no uniform witness
is needed. The sweep-level theorem closes the opposing-fact pair arm
through the JUSTIFIED implied literal; the loop-level theorem assembles
the scan arm (database membership), the unit-enqueue arm, and the sweep
arm (quiesce / extend / the conflict fixpoint). -/

/-! ## 1. the sweep origin entitlement (per-a) -/

/-- A sweep conflict clause carries a true literal at every internal
    solution, given per-family entitlement for propagator reports and
    universal soundness for implied literals. -/
theorem runPropagators_conflict_entitled
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {props : List Propagator}
    (hsolvable : ∃ b, ProblemSolution problem constraintHolds b)
    (hsafe : CoherentSafeUniv problem constraintHolds props)
    (hent : ∀ (st : State), DomainCoherent problem st →
      ∀ (p : Propagator), p ∈ props → ∀ (c : Clause),
      p.run st = .conflict c →
        SolvedBy problem constraintHolds st →
        ∀ a, ProblemSolution problem constraintHolds a →
          ∃ l ∈ c, l.eval a = some true)
    (st0 : State) (hnone : st0.conflict = none)
    (hsol : SolvedBy problem constraintHolds st0)
    (hcoh : DomainCoherent problem st0)
    (c : Clause) (hrep : (runPropagators props st0).conflict = some c)
    (a : Assignment) (ha : ProblemSolution problem constraintHolds a) :
    ∃ l ∈ c, l.eval a = some true := by
  have goInv : ∀ (ps : List Propagator) (acc : State),
      (∀ q ∈ ps, q ∈ props) →
      acc.conflict = none →
      SolvedBy problem constraintHolds acc →
      DomainCoherent problem acc →
      ∀ d, (runPropagators.go ps acc).conflict = some d →
        ∃ l ∈ d, l.eval a = some true := by
    intro ps
    induction ps with
    | nil =>
        intro acc _ hacnone _ _ d hgo
        have h1 : (runPropagators.go [] acc).conflict = acc.conflict := rfl
        rw [h1, hacnone] at hgo
        exact absurd hgo (by simp)
    | cons p rest ih =>
        intro acc hmem hacnone hacc hcohacc d hgo
        have hp : p ∈ props := hmem p (List.mem_cons_self)
        have hrest : ∀ q ∈ rest, q ∈ props := fun q hq =>
          hmem q (List.mem_cons_of_mem _ hq)
        simp only [runPropagators.go] at hgo
        split at hgo
        · rename_i his
          rw [hacnone] at his
          exact absurd his (by simp)
        · split at hgo
          · exact ih acc hrest hacnone hacc hcohacc d hgo
          · rename_i c2 heq
            have hc2d : c2 = d := by injection hgo
            rw [hc2d] at heq
            exact hent acc hcohacc p hp d heq hacc a ha
          · rename_i lig rsn hres
            have hjust : ∀ a2, ProblemSolution problem constraintHolds a2 →
                lig.norm.eval a2 = some true := by
              intro a2 ha2
              rw [Literal.norm_eval lig a2]
              exact (hsafe acc hcohacc).impliedTrueAt p hp lig rsn
                hres a2 ⟨ha2, hacc a2 ha2⟩
            cases hb1 : acc.litOnTrail lig.norm with
            | true =>
                have hstate : enqueueNorm acc lig (some rsn) = acc := by
                  simp only [enqueueNorm, hb1, if_true]
                rw [hstate] at hgo
                exact ih acc hrest hacnone hacc hcohacc d hgo
            | false =>
                cases hb2 : acc.negOnTrail lig.norm with
                | true =>
                    have hpair : (enqueueNorm acc lig (some rsn)).conflict
                        = some [lig.norm, lig.norm.negate] := by
                      simp only [enqueueNorm, hb1, Bool.false_eq_true,
                        if_false, hb2, if_true]
                    have hpass : (runPropagators.go rest
                        (enqueueNorm acc lig (some rsn))).conflict
                        = some [lig.norm, lig.norm.negate] :=
                      runPropagators_go_conflict_fixed props rest
                        (enqueueNorm acc lig (some rsn))
                        [lig.norm, lig.norm.negate] hpair
                    rw [hpass] at hgo
                    injection hgo with hgo4
                    refine ⟨lig.norm, ?_, hjust a ha⟩
                    rw [← hgo4]
                    exact List.mem_cons_self
                | false =>
                    have hstate2 : (enqueueNorm acc lig (some rsn)).conflict
                        = none := by
                      simp only [enqueueNorm, hb1, hb2,
                        Bool.false_eq_true, if_false]
                      exact hacnone
                    obtain ⟨_, hsol2⟩ := enqueueNorm_solvedBy
                      (problem := problem) (constraintHolds := constraintHolds)
                      (st := acc) (l0 := lig) (reason := some rsn)
                      hacnone hacc hjust
                    exact ih (enqueueNorm acc lig (some rsn)) hrest
                      hstate2 hsol2 (enqueueNorm_coherent hcohacc) d hgo
  exact goInv props st0 (fun _ hq => hq) hnone hsol hcoh c hrep


/-- THE SWEEP TRANSFER: folding state-universally-sound propagators over
    a solved-by conflict-free state yields either (i) a conflict-free
    state that still solves-by, or (ii) the first reported conflict
    clause — unsatisfiable at every internal solution. -/
theorem sweep_solvedBy
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {props : List Propagator}
    (hsafe : CoherentSafeUniv problem constraintHolds props)
    (hsolvable : ∃ b, ProblemSolution problem constraintHolds b)
    (st0 : State)
    (hsol : SolvedBy problem constraintHolds st0)
    (hcoh0 : DomainCoherent problem st0)
    (hnone : st0.conflict = none) :
    ((runPropagators props st0).conflict = none ∧
      SolvedBy problem constraintHolds (runPropagators props st0)) ∨
    (∃ c, (runPropagators props st0).conflict = some c ∧
      ∀ a, ProblemSolution problem constraintHolds a →
        ¬ c.SatisfiedBy a) := by
  have goInv : ∀ (ps : List Propagator) (acc : State),
      (∀ q ∈ ps, q ∈ props) →
      acc.conflict = none →
      DomainCoherent problem acc →
      SolvedBy problem constraintHolds acc →
        ((runPropagators.go ps acc).conflict = none ∧
          SolvedBy problem constraintHolds (runPropagators.go ps acc)) ∨
        (∃ c, (runPropagators.go ps acc).conflict = some c ∧
          ∀ a, ProblemSolution problem constraintHolds a →
            ¬ c.SatisfiedBy a) := by
    intro ps
    induction ps with
    | nil =>
        intro _ acc hacnone _ hacc
        exact Or.inl ⟨hacnone, hacc⟩
    | cons p rest ih =>
        intro acc hmem hacnone hcohacc hacc
        have hp : p ∈ props := hmem p (List.mem_cons_self)
        have hsafep := hsafe acc hcohacc
        have hrest : ∀ q ∈ rest, q ∈ props := fun q hq =>
          hmem q (List.mem_cons_of_mem _ hq)
        simp only [runPropagators.go]
        split
        · -- guard-true: acc.conflict.isSome, contradicting hacnone
          rename_i his
          rw [hacnone] at his
          exact absurd his (by simp)
        · split
          · -- stable: recurse with acc
            rename_i hres
            rename_i _ _ _
            exact ih acc hrest hacnone hcohacc hacc
          · -- conflict: p's own report wrote it
            rename_i c heq
            refine Or.inr ⟨c, ?_, ?_⟩
            · exact rfl
            · intro a ha
              exact (hsafep.conflictExcludes p hp c heq a ⟨ha, hacc a ha⟩)
          · -- implied: recurse at the enqueued state
            rename_i l rsn hres
            rename_i _ _ _ _ _
            have hlita : ∀ a, ProblemSolution problem constraintHolds a →
              l.norm.eval a = some true := by
              intro a ha
              rw [Literal.norm_eval l a]
              exact (hsafep.impliedTrueAt p hp l rsn hres a ⟨ha, hacc a ha⟩)
            obtain ⟨hconf'⟩ := enqueueNorm_justified_solvable
              (problem := problem) (constraintHolds := constraintHolds)
              (st := acc) (l0 := l) (reason := some rsn)
              hacnone hsolvable hacc hlita
            have hsol2 := (enqueueNorm_solvedBy (problem := problem)
              (constraintHolds := constraintHolds) (st := acc) (l0 := l)
              (reason := some rsn) hacnone hacc hlita).2
            exact ih (enqueueNorm acc l (some rsn)) hrest hconf'
              (enqueueNorm_coherent hcohacc) hsol2
  exact goInv props st0 (fun _ hq => hq) hnone hcoh0 hsol

/-- The scan-unit justification over all internal solutions: the
    reported unit literal is true at every internal solution, given the
    clause's entitlement (membership witness) and the state's
    solved-by. -/
theorem scanUnit_justified_all
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st : State} {c : Clause} {l : Literal} {r : Reason}
    (hunit : scanClause st c = some (.inr (l, r)))
    (hent : ∀ a, ProblemSolution problem constraintHolds a →
      ∃ l2 ∈ c, l2.eval a = some true)
    (hsol : SolvedBy problem constraintHolds st) :
    ∀ a, ProblemSolution problem constraintHolds a →
      (l.norm).eval a = some true := by
  intro a ha
  obtain ⟨_, htrail, _, _⟩ := hsol a ha
  rw [Literal.norm_eval l a]
  exact scanClause_unit_justified' (st := st) (c := c) (l := l) (r := r)
    (a := a) hunit htrail (hent a ha)

/-- `enqueueNorm` preserves the clause list (none of its three branches
    touches it). -/
theorem enqueueNorm_clauses {st : State} {l0 : Literal}
    {reason : Option Reason} :
    (enqueueNorm st l0 reason).clauses = st.clauses := by
  simp only [enqueueNorm]
  split
  · rfl
  · split
    · rfl
    · rfl

/-- The sweep fold preserves the clause list. -/
theorem runPropagators_go_clauses : ∀ (props : List Propagator) (s : State),
    (runPropagators.go props s).clauses = s.clauses := by
  intro props
  induction props with
  | nil => intro s; rfl
  | cons p rest ih =>
      intro s
      simp only [runPropagators.go]
      split
      · rfl
      · split
        · rename_i rr
          exact ih s
        · rename_i cc
          rfl
        · rename_i l r heq
          rw [ih (enqueueNorm s l (some r)), enqueueNorm_clauses]

/-- Inversion on scanAll's CONFLICT verdict: the reported clause is a
    member of the scanned state's database — the entitlement-carrying
    form the conflict refutation needs (the proof-layer twin of the
    pre-existing unit-side `scanAll_inr_inv`). -/
theorem scanAll_inl_full {st : State} {c : Clause}
    (h : scanAll st = some (Sum.inl c)) :
    ∃ d ∈ st.allClauses, scanClause st d = some (Sum.inl c) := by
  unfold scanAll at h
  have walkFun : ∀ (cs : List Clause) (v : Clause ⊕ (Literal × Reason)),
      scanAll.go st cs = some v →
      ∃ d, d ∈ cs ∧ scanClause st d = some v := by
    intro cs
    induction cs with
    | nil => intro v hv; cases hv
    | cons d rest ih =>
        intro v hv
        simp only [scanAll.go] at hv
        match hm2 : scanClause st d, hv with
        | none, hv' =>
            obtain ⟨c2, hc2m, hc2s⟩ := ih v
              (by simpa [scanAll.go, hm2] using hv')
            exact ⟨c2, List.mem_cons_of_mem _ hc2m, hc2s⟩
        | some r0, hv' =>
            exact ⟨d, List.mem_cons_self, by cases hv'; exact hm2⟩
  exact walkFun _ _ h

/-- scanAll's unit verdict inverts to a clause of the scanned state's
    allClauses (original or learned). -/
theorem scanAll_inr_inv {st : State} {l : Literal} {r : Reason}
    (h : scanAll st = some (Sum.inr (l, r))) :
    ∃ c, c ∈ st.allClauses ∧ scanClause st c = some (Sum.inr (l, r)) := by
  unfold scanAll at h
  have walkFun : ∀ (cs : List Clause) (v : Clause ⊕ (Literal × Reason)),
      scanAll.go st cs = some v →
      ∃ c, c ∈ cs ∧ scanClause st c = some v := by
        intro cs
        induction cs with
        | nil => intro v hv; cases hv
        | cons c rest ih =>
            intro v hv
            simp only [scanAll.go] at hv
            match hm2 : scanClause st c, hv with
            | none, hv' =>
                obtain ⟨c2, hc2m, hc2s⟩ := ih v
                  (by simpa [scanAll.go, hm2] using hv')
                exact ⟨c2, List.mem_cons_of_mem _ hc2m, hc2s⟩
            | some r0, hv' =>
                exact ⟨c, List.mem_cons_self, by
                  cases hv'
                  exact hm2⟩
  obtain ⟨c, hcm, hcs⟩ := walkFun _ _ h
  exact ⟨c, hcm, hcs⟩

/-- One-step verdict for the sweep-extend shape: the driver's conflict
    coincides with the sweep's for every fuel (the guard passes a set
    conflict through immediately). -/
theorem sweepStep_verdict (props : List Propagator) (st : State) :
    ∀ (k : Nat) (d : Clause),
      (runPropagators props st).conflict = some d →
      (if ((runPropagators props st).trail.length == st.trail.length) = true
          then runPropagators props st
        else propagateLoop k props (runPropagators props st)).conflict
        = some d := by
  intro k
  induction k with
  | zero =>
      intro d hcc
      split
      · exact hcc
      · rw [show propagateLoop 0 props (runPropagators props st)
            = runPropagators props st from by simp only [propagateLoop]]
        exact hcc
  | succ k ih =>
      intro d hcc
      split
      · exact hcc
      · have hisSome : (runPropagators props st).conflict.isSome = true := by
          rw [hcc]; simp
        have hrec : propagateLoop (k+1) props (runPropagators props st)
            = runPropagators props st := by
          show ((if (runPropagators props st).conflict.isSome = true
            then runPropagators props st
            else _) : State) = runPropagators props st
          rw [if_pos hisSome]
        rw [hrec]; exact hcc

/-- `enqueueNorm` preserves the learned list (none of its three
    branches touches it). -/
theorem enqueueNorm_learned {st : State} {l0 : Literal}
    {reason : Option Reason} :
    (enqueueNorm st l0 reason).learned = st.learned := by
  simp only [enqueueNorm]
  split
  · rfl
  · split
    · rfl
    · rfl

/-- The sweep fold preserves the learned list. -/
theorem runPropagators_go_learned : ∀ (props : List Propagator) (s : State),
    (runPropagators.go props s).learned = s.learned := by
  intro props
  induction props with
  | nil => intro s; rfl
  | cons p rest ih =>
      intro s
      simp only [runPropagators.go]
      split
      · rfl
      · split
        · rename_i rr
          exact ih s
        · rename_i cc
          rfl
        · rename_i l r heq
          rw [ih (enqueueNorm s l (some r)), enqueueNorm_learned]

theorem propagateLoop_excludes
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {props : List Propagator}
    (hsafe : CoherentSafeUniv problem constraintHolds props)
    (hsolvable : ∃ b, ProblemSolution problem constraintHolds b)
    (orig lnd : List Clause)
    (hdb : ∀ c ∈ orig,
      ∀ a, ProblemSolution problem constraintHolds a →
        ∃ l ∈ c, l.eval a = some true)
    (hlearned : ∀ c ∈ lnd,
      ∀ a, ProblemSolution problem constraintHolds a →
        ∃ l ∈ c, l.eval a = some true)
    :
    ∀ (fuel : Nat) (st : State),
      st.conflict = none →
      SolvedBy problem constraintHolds st →
      DomainCoherent problem st →
      st.clauses = orig →
      st.learned = lnd →
      (propagateLoop fuel props st).conflict.isSome = true →
      ∃ c, (propagateLoop fuel props st).conflict = some c ∧
        ∀ a, ProblemSolution problem constraintHolds a →
          ¬ c.SatisfiedBy a := by
  intro fuel
  induction fuel with
  | zero =>
      intro st hc _ _ _ _ hisSome
      simp only [propagateLoop] at hisSome
      rw [hc] at hisSome
      exact absurd hisSome (by simp)
  | succ fuel ih =>
      intro st hc hsol hcoh hclfix hlnfix hisSome
      cases hscan : scanAll st with
      | none =>
          -- the sweep branch: uniform fold transfer + one-step verdict
          have hUnf : propagateLoop (fuel + 1) props st =
              (if ((runPropagators props st).trail.length == st.trail.length)
                = true then runPropagators props st
              else propagateLoop fuel props (runPropagators props st)) := by
            simp [propagateLoop, hc, hscan, Option.isSome_none]
          rw [hUnf] at hisSome ⊢
          rcases sweep_solvedBy hsafe hsolvable st hsol hcoh hc with
            ⟨hnone2, hsol2⟩ | ⟨c, hcc, hexc⟩
          · -- fold quiesced conflict-free: refute or recurse
            split at hisSome
            · rw [hnone2] at hisSome
              exact absurd hisSome (by simp)
            · rename_i hlen
              rw [if_neg hlen]
              -- clauses preserved (sweep/enqueue don't touch clauses):
              have hcl2 : (runPropagators props st).clauses = st.clauses := by
                unfold runPropagators
                exact runPropagators_go_clauses props st
              -- learned preserved (sweep/enqueue don't touch learned):
              have hln2 : (runPropagators props st).learned = st.learned := by
                unfold runPropagators
                exact runPropagators_go_learned props st
              exact ih (runPropagators props st) hnone2 hsol2
                (runPropagators_coherent props st hcoh)
                (by rw [hcl2]; exact hclfix)
                (by rw [hln2]; exact hlnfix) hisSome
          · -- the fold reported c: it IS the driver's verdict
            have hfix := sweepStep_verdict props st fuel c hcc
            refine ⟨c, ?_, hexc⟩
            split
            · exact hcc
            · next hdec => rw [if_neg hdec] at hfix; exact hfix
      | some verdict =>
          cases verdict with
          | inl c =>
              -- scan reported a conflict clause directly
              have hUnf : propagateLoop (fuel + 1) props st
                  = { st with conflict := some c } := by
                simp [propagateLoop, hc, hscan, Option.isSome_none]
              rw [hUnf] at hisSome ⊢
              refine ⟨c, ?_, ?_⟩
              · exact rfl
              · exact scanConflict_excludes (st := st)
                  (scanAll_inl_inv hscan) hsol
          | inr w =>
              obtain ⟨l, r⟩ := w
              -- the loop enqueues and recurses: the unit justification
              -- (entitlement over all allClauses: originals via `hdb`,
              -- learned via `hlearned`) keeps every internal solution
              -- represented
              have hUnf : propagateLoop (fuel + 1) props st
                  = propagateLoop fuel props (enqueueNorm st l (some r)) := by
                simp [propagateLoop, hc, hscan, Option.isSome_none]
              rw [hUnf] at hisSome ⊢
              obtain ⟨c, hcm, hcs⟩ := scanAll_inr_inv hscan
              -- entitlement of the scanned clause:
              have hent : (∀ a, ProblemSolution problem constraintHolds a →
                  ∃ l2 ∈ c, l2.eval a = some true) := by
                -- c is in clauses (hdb) or learned (hlearned):
                rcases List.mem_append.mp hcm with hcl | hln
                · exact hdb c (hclfix ▸ hcl)
                · exact hlearned c (hlnfix ▸ hln)
              have hjustify : ∀ a, ProblemSolution problem constraintHolds a →
                  l.norm.eval a = some true :=
                scanUnit_justified_all hcs hent hsol
              -- the enqueue preserves solved-by and conflict-none:
              obtain ⟨hconf2, hsol2⟩ := enqueueNorm_justified_solvable
                (problem := problem) (constraintHolds := constraintHolds)
                (st := st) (l0 := l) (reason := some r) hc hsolvable hsol
                hjustify
              -- clauses and learned preserved:
              have hcl2 : (enqueueNorm st l (some r)).clauses = st.clauses :=
                enqueueNorm_clauses
              have hln2 : (enqueueNorm st l (some r)).learned = st.learned :=
                enqueueNorm_learned
              exact ih (enqueueNorm st l (some r)) hconf2 hsol2
                (enqueueNorm_coherent hcoh)
                (by rw [hcl2]; exact hclfix)
                (by rw [hln2]; exact hlnfix) hisSome

/-! ### The conflict-free loop transfer (the positive half)

The master result above refutes solutions from a conflict; the polar
companion below carries `SolvedBy` through a run that ends
CONFLICT-FREE. Together they make the propagation loop a total
transfer: whatever the outcome, the resulting state either still
represents every internal solution or the problem has none. This is
the exact invariant fact the engine-arm induction of `Proofs/Search`
consumes at every `st1 = propagateLoop ...` of `lcgSearch.go`. -/

/-- A conflicting state is a fixpoint of the propagation loop at any
    fuel: the zero-fuel case returns the state unchanged, and the
    succ-fuel guard passes a set conflict through immediately. -/
theorem propagateLoop_conflict_fix (props : List Propagator)
    (fuel : Nat) (st : State) (c : Clause)
    (hcc : st.conflict = some c) :
    propagateLoop fuel props st = st := by
  cases fuel with
  | zero => rfl
  | succ k =>
      show ((if st.conflict.isSome = true then st
        else _) : State) = st
      rw [if_pos (by rw [hcc]; simp)]

/-- CONFLICT-FREE LOOP TRANSFER: when the whole propagation loop ends
    conflict-free over a solved-by state with entitled databases, the
    resulting state still solves-by. Fuel induction over the three
    arms: scan-unit enqueue (`enqueueNorm_justified_solvable`), scan
    conflict (contradicts the conflict-free end), and the sweep
    (`sweep_solvedBy` + quiesce guard; a swept conflict is final by
    the fixpoint lemma above). The databases are entry-fixed — the
    exact lists the caller supplies — since neither propagation
    enqueue nor the sweep ever modifies them. -/
theorem propagateLoop_solvedBy
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {props : List Propagator}
    (hsafe : CoherentSafeUniv problem constraintHolds props)
    (hsolvable : ∃ b, ProblemSolution problem constraintHolds b)
    (orig lnd : List Clause)
    (hdb : ∀ c ∈ orig,
      ∀ a, ProblemSolution problem constraintHolds a →
        ∃ l ∈ c, l.eval a = some true)
    (hlearned : ∀ c ∈ lnd,
      ∀ a, ProblemSolution problem constraintHolds a →
        ∃ l ∈ c, l.eval a = some true) :
    ∀ (fuel : Nat) (st : State),
      st.conflict = none →
      SolvedBy problem constraintHolds st →
      DomainCoherent problem st →
      st.clauses = orig →
      st.learned = lnd →
      (propagateLoop fuel props st).conflict = none →
      SolvedBy problem constraintHolds (propagateLoop fuel props st) := by
  intro fuel
  induction fuel with
  | zero => intro st _ hsol _ _ _ _; exact hsol
  | succ fuel ih =>
      intro st hc hsol hcoh hclfix hlnfix hclear
      cases hscan : scanAll st with
      | none =>
          have hUnf : propagateLoop (fuel + 1) props st =
              (if ((runPropagators props st).trail.length == st.trail.length)
                = true then runPropagators props st
              else propagateLoop fuel props (runPropagators props st)) := by
            simp [propagateLoop, hc, hscan, Option.isSome_none]
          rw [hUnf] at hclear ⊢
          -- the same guard drives both: case it once, transport both
          by_cases hlen : ((runPropagators props st).trail.length ==
              st.trail.length) = true
          · -- quiesced: the swept state is the loop's answer
            rw [if_pos hlen] at hclear ⊢
            rcases sweep_solvedBy hsafe hsolvable st hsol hcoh hc with
              ⟨hnone2, hsol2⟩ | ⟨c, hcc, _⟩
            · exact hsol2
            · rw [hcc] at hclear; exact absurd hclear (by simp)
          · -- extended: recurse at the swept state
            rw [if_neg hlen] at hclear ⊢
            rcases sweep_solvedBy hsafe hsolvable st hsol hcoh hc with
              ⟨hnone2, hsol2⟩ | ⟨c, hcc, _⟩
            · have hcl2 : (runPropagators props st).clauses = st.clauses := by
                unfold runPropagators
                exact runPropagators_go_clauses props st
              have hln2 : (runPropagators props st).learned = st.learned := by
                unfold runPropagators
                exact runPropagators_go_learned props st
              exact ih (runPropagators props st) hnone2 hsol2
                (runPropagators_coherent props st hcoh)
                (by rw [hcl2]; exact hclfix)
                (by rw [hln2]; exact hlnfix) hclear
            · -- the swept conflict is final: the recursion passes it through
              rw [propagateLoop_conflict_fix props fuel
                (runPropagators props st) c hcc] at hclear
              rw [hcc] at hclear
              exact absurd hclear (by simp)
      | some verdict =>
          cases verdict with
          | inl c =>
              -- scan reported a conflict: contradicts conflict-free end
              have hUnf : propagateLoop (fuel + 1) props st
                  = { st with conflict := some c } := by
                simp [propagateLoop, hc, hscan, Option.isSome_none]
              rw [hUnf] at hclear
              exact absurd hclear (by simp)
          | inr w =>
              obtain ⟨l, r⟩ := w
              have hUnf : propagateLoop (fuel + 1) props st
                  = propagateLoop fuel props (enqueueNorm st l (some r)) := by
                simp [propagateLoop, hc, hscan, Option.isSome_none]
              rw [hUnf] at hclear ⊢
              obtain ⟨c2, hcm, hcs⟩ := scanAll_inr_inv hscan
              have hent : (∀ a, ProblemSolution problem constraintHolds a →
                  ∃ l2 ∈ c2, l2.eval a = some true) := by
                rcases List.mem_append.mp hcm with hcl | hln
                · exact hdb c2 (hclfix ▸ hcl)
                · exact hlearned c2 (hlnfix ▸ hln)
              have hjustify : ∀ a, ProblemSolution problem constraintHolds a →
                  l.norm.eval a = some true :=
                scanUnit_justified_all hcs hent hsol
              obtain ⟨hconf2, hsol2⟩ := enqueueNorm_justified_solvable
                (problem := problem) (constraintHolds := constraintHolds)
                (st := st) (l0 := l) (reason := some r) hc hsolvable hsol
                hjustify
              have hcl2 : (enqueueNorm st l (some r)).clauses = st.clauses :=
                enqueueNorm_clauses
              have hln2 : (enqueueNorm st l (some r)).learned = st.learned :=
                enqueueNorm_learned
              exact ih (enqueueNorm st l (some r)) hconf2 hsol2
                (enqueueNorm_coherent hcoh)
                (by rw [hcl2]; exact hclfix)
                (by rw [hln2]; exact hlnfix) hclear

/-! ## Phase 1: the repair transfer, level-0 soundness, fuel
exhaustion, and the conflict-origin entitlement chain -/

/-! ## The iterated firing -/

/-- FOLD FITS: folding `domOfLit` over a trail whose entries are ALL
    true at `a` keeps `a` fitting the accumulator — the iterated
    `firing` lemma. `a` fits the seed domains (not merely in length:
    firing preserves full membership), so each step's narrowing keeps
    it fitting. -/
theorem fold_fits : ∀ (trail : List TrailEntry) (a : Assignment)
    (doms : List Domain),
    a.Fits doms →
    (∀ e ∈ trail, e.literal.eval a = some true) →
    a.Fits (trail.foldl (fun acc e => domOfLit acc e.literal) doms) := by
  intro trail
  induction trail with
  | nil =>
      intro a doms hfit _
      exact hfit
  | cons e rest ih =>
      intro a doms hfit htrue
      rw [List.foldl_cons]
      -- slot in range: the truth of e.literal pins its slot below
      -- a.length (the assignment side — firing's premise)
      have hin : e.literal.atom.slot < a.length :=
        eval_lit_some_slot_lt (htrue e (List.mem_cons_self))
      -- the head's narrowing keeps a fitting (firing):
      have hfire : a.Fits (domOfLit doms e.literal) :=
        firing (doms := doms) (l := e.literal) (a := a)
          hfit hin (htrue e (List.mem_cons_self))
      -- tail: iterate
      have htrue' : ∀ e' ∈ rest, e'.literal.eval a = some true := by
        intro e' he'
        exact htrue e' (List.mem_cons_of_mem _ he')
      exact ih a (domOfLit doms e.literal) hfire htrue'

/-! ## The repair field lemmas -/

/-- Repair clears the conflict and sets the level. -/
theorem repair_conflict (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
    (level : Nat) (st : State) :
    (repairAfterBackjump problem level st).conflict = none := rfl

theorem repair_decisionLevel (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
    (level : Nat) (st : State) :
    (repairAfterBackjump problem level st).decisionLevel = level := rfl

theorem repair_clauses (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
    (level : Nat) (st : State) :
    (repairAfterBackjump problem level st).clauses = st.clauses := rfl

theorem repair_learned (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
    (level : Nat) (st : State) :
    (repairAfterBackjump problem level st).learned = st.learned := rfl

/-- The kept subtrail's membership inverts: an entry of the ORIGINAL
    trail at a low enough level survives the repair filter. -/
theorem repair_kept_mem (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
    (level : Nat) (st : State) (e : TrailEntry)
    (he : e ∈ st.trail) (hle : decide (e.level ≤ level) = true) :
    e ∈ (repairAfterBackjump problem level st).trail := by
  unfold repairAfterBackjump
  simp only
  exact List.mem_filter.mpr ⟨he, hle⟩

/-! ## THE REPAIR-TO-ZERO SOLVEDBY -/

/-- Every internal solution satisfies the state's trail — the premise
    supplying the kept-trail soundness below. -/
def Level0TrailSound (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop)
    (st : State) : Prop :=
  ∀ e ∈ st.trail, e.level = 0 →
    ∀ a, ProblemSolution problem constraintHolds a →
      e.literal.eval a = some true

/-- THE REPAIR-TO-ZERO TRANSFER: repairing to level 0 from a state
    whose LEVEL-0 entries are true at every internal solution yields a
    state that solves-by — the kept subtrail (exactly the level-0
    prefix) is sound, so `fold_fits` rebuilds fitting domains, the
    kept trail is satisfied, and both databases are unchanged fields. -/
theorem repair_solvedBy0
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    (st : State)
    (hsound : Level0TrailSound problem constraintHolds st)
    (hclauses : ∀ c ∈ st.clauses, ∀ a, ProblemSolution problem
        constraintHolds a → ∃ l ∈ c, l.eval a = some true)
    (hlearned : ∀ c ∈ st.learned, ∀ a, ProblemSolution problem
        constraintHolds a → ∃ l ∈ c, l.eval a = some true) :
    SolvedBy problem constraintHolds (repairAfterBackjump problem 0 st) := by
  intro a ha
  -- the kept entries are exactly the level-0 ones, each true at a:
  have hkept : ∀ e ∈ (st.trail.filter fun e => decide (e.level ≤ 0)),
      e.literal.eval a = some true := by
    intro e he
    simp only [List.mem_filter, decide_eq_true_eq] at he
    exact hsound e he.1 (by omega) a ha
  -- the rebuilt domains fit a (iterated firing from problem.domains):
  have hfit : a.Fits (repairAfterBackjump problem 0 st).domains := by
    unfold repairAfterBackjump
    show a.Fits ((st.trail.filter fun e => decide (e.level ≤ 0)).foldl
      (fun acc e => domOfLit acc e.literal) problem.domains)
    exact fold_fits (st.trail.filter fun e => decide (e.level ≤ 0)) a
      problem.domains ha.1 hkept
  refine ⟨hfit, ?_, ?_, ?_⟩
  · -- trail satisfaction: each kept entry is true at a
    intro e he
    exact hkept e he
  · -- clauses: the repaired state keeps the original database;
    -- membership transfers, and the witness satisfies
    intro c hc
    have hc2 : c ∈ st.clauses := by
      rw [← repair_clauses problem 0 st]
      exact hc
    obtain ⟨w, hw, hev⟩ := hclauses c hc2 a ha
    exact ⟨w, hw, hev⟩
  · -- learned: the repaired state keeps the learned database
    intro c hc
    have hc2 : c ∈ st.learned := by
      rw [← repair_learned problem 0 st]
      exact hc
    obtain ⟨w, hw, hev⟩ := hlearned c hc2 a ha
    exact ⟨w, hw, hev⟩


/-! ### Level-0 trail soundness through propagation -/

/-- `enqueueNorm` at a LEVEL-0 state preserves level-0 soundness when
    the enqueued literal is true at every internal solution: the only
    new entry is at level 0 carrying the (normalized, eval-equal)
    literal. -/
theorem enqueueNorm_level0_sound
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st : State} {l0 : Literal} {reason : Option Reason}
    (hlevel : st.decisionLevel = 0)
    (hsound : Level0TrailSound problem constraintHolds st)
    (hlit : ∀ a, ProblemSolution problem constraintHolds a →
      l0.norm.eval a = some true) :
    Level0TrailSound problem constraintHolds (enqueueNorm st l0 reason) := by
  intro e he hzero a ha
  -- three enqueueNorm branches; only the fresh one appends
  simp only [enqueueNorm] at he
  split at he
  · -- skip: trail unchanged
    exact hsound e he hzero a ha
  · split at he
    · -- opposing: trail unchanged
      exact hsound e he hzero a ha
    · -- fresh: the new entry is the last one, at level 0
      rename_i hnew hneg
      have htr : (enqueue st l0.norm reason).trail
          = st.trail ++ [TrailEntry.mk l0.norm st.decisionLevel reason] := rfl
      rw [htr, List.mem_append] at he
      rcases he with he | he
      · -- old entry: the old soundness applies (its level is 0)
        exact hsound e he hzero a ha
      · -- the appended entry: level 0 and literal l0.norm
        have heq : e = TrailEntry.mk l0.norm st.decisionLevel reason := by
          simpa using he
        rw [heq, hlevel] at hzero ⊢
        exact hlit a ha

/-! ## 2. Fuel exhaustion -/

/-- Fuel exhaustion reports unknown: the zero-fuel `go` is definitional
    `unknown`, decidably. -/
theorem go_zero_unknown {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHoldsB : Constraint → Assignment → Bool}
    {props : List Propagator} (st : State) :
    lcgSearch.go problem constraintHoldsB props 0 st = .unknown := rfl


/-! ## 2. the loop origin entitlement (per-a) -/

/-- A conflict clause reported by a conflict-free propagation run from
    a solved-by entry state carries a true literal at every internal
    solution — the loop-level origin entitlement assembling the scan
    arm (database membership), the unit-enqueue arm (recursion with
    SolvedBy preserved by the justified enqueue), and the sweep arm
    (quiesce: the sweep theorem; extend: recursion; swept conflict:
    the fixpoint identification). -/
theorem propagateLoop_conflict_entitled
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {props : List Propagator}
    (hsolvable : ∃ b, ProblemSolution problem constraintHolds b)
    (hsafe : CoherentSafeUniv problem constraintHolds props)
    (hent : ∀ (st : State), DomainCoherent problem st →
      ∀ (p : Propagator), p ∈ props → ∀ (c : Clause),
      p.run st = .conflict c →
        SolvedBy problem constraintHolds st →
        ∀ a, ProblemSolution problem constraintHolds a →
          ∃ l ∈ c, l.eval a = some true)
    (orig lnd : List Clause)
    (hdb : ∀ c ∈ orig, ∀ a, ProblemSolution problem constraintHolds a →
        ∃ l ∈ c, l.eval a = some true)
    (hlearned : ∀ c ∈ lnd, ∀ a, ProblemSolution problem constraintHolds a →
        ∃ l ∈ c, l.eval a = some true) :
    ∀ (fuel : Nat) (st : State),
      st.conflict = none →
      SolvedBy problem constraintHolds st →
      DomainCoherent problem st →
      st.clauses = orig →
      st.learned = lnd →
      ∀ c, (propagateLoop fuel props st).conflict = some c →
        ∀ a, ProblemSolution problem constraintHolds a →
          ∃ l ∈ c, l.eval a = some true := by
  intro fuel
  induction fuel with
  | zero =>
      intro st hc _ _ _ _ c hrep
      simp only [propagateLoop] at hrep
      rw [hc] at hrep
      exact absurd hrep (by simp)
  | succ fuel ih =>
      intro st hc hsol hcoh hclfix hlnfix c hrep a ha
      cases hscan : scanAll st with
      | none =>
          have hUnf : propagateLoop (fuel + 1) props st =
              (if ((runPropagators props st).trail.length == st.trail.length)
                = true then runPropagators props st
              else propagateLoop fuel props (runPropagators props st)) := by
            simp [propagateLoop, hc, hscan, Option.isSome_none]
          rw [hUnf] at hrep
          by_cases hlen : ((runPropagators props st).trail.length ==
              st.trail.length) = true
          · -- quiesced: the sweep's own origin entitlement (per-a)
            rw [if_pos hlen] at hrep
            exact runPropagators_conflict_entitled hsolvable hsafe hent
              st hc hsol hcoh c hrep a ha
          · -- extended: recurse at the swept state
            rw [if_neg hlen] at hrep
            have hcl2 : (runPropagators props st).clauses = st.clauses := by
              unfold runPropagators
              exact runPropagators_go_clauses props st
            have hln2 : (runPropagators props st).learned = st.learned := by
              unfold runPropagators
              exact runPropagators_go_learned props st
            rcases sweep_solvedBy hsafe hsolvable st hsol hcoh hc with
              ⟨hnone2, hsol2⟩ | ⟨c2, hcc, _⟩
            · exact ih (runPropagators props st) hnone2 hsol2
                (runPropagators_coherent props st hcoh)
                (by rw [hcl2]; exact hclfix)
                (by rw [hln2]; exact hlnfix) c hrep a ha
            · -- the swept conflict is final (fixpoint): identify and
              -- apply the sweep theorem
              rw [propagateLoop_conflict_fix props fuel
                (runPropagators props st) c2 hcc] at hrep
              have hc2c : c2 = c := by
                rw [hcc] at hrep
                injection hrep
              subst hc2c
              exact runPropagators_conflict_entitled hsolvable hsafe hent
                st hc hsol hcoh c2 hcc a ha
      | some verdict =>
          cases verdict with
          | inl c2 =>
              -- scan conflict: the reported clause is IN the entry database
              have hUnf : propagateLoop (fuel + 1) props st
                  = { st with conflict := some c2 } := by
                simp [propagateLoop, hc, hscan, Option.isSome_none]
              rw [hUnf] at hrep
              injection hrep with hrep2
              subst hrep2
              obtain ⟨d, hdm, hds⟩ := scanAll_inl_full (st := st) (c := c2) hscan
              -- the scanned clause d IS the reported c2
              have hdc : d = c2 := (scanClause_inl_eq (st := st)
                (c := c2) (d := d) hds).symm
              subst hdc
              rcases List.mem_append.mp hdm with hcl | hln
              · exact hdb d (hclfix ▸ hcl) a ha
              · exact hlearned d (hlnfix ▸ hln) a ha
          | inr w =>
              obtain ⟨l, r⟩ := w
              have hUnf : propagateLoop (fuel + 1) props st
                  = propagateLoop fuel props (enqueueNorm st l (some r)) := by
                simp [propagateLoop, hc, hscan, Option.isSome_none]
              rw [hUnf] at hrep
              obtain ⟨c2, hcm, hcs⟩ := scanAll_inr_inv hscan
              have hentc : ∀ a2, ProblemSolution problem constraintHolds a2 →
                  ∃ l2 ∈ c2, l2.eval a2 = some true := by
                rcases List.mem_append.mp hcm with hcl | hln
                · exact hdb c2 (hclfix ▸ hcl)
                · exact hlearned c2 (hlnfix ▸ hln)
              have hjust : ∀ a2, ProblemSolution problem constraintHolds a2 →
                  l.norm.eval a2 = some true :=
                scanUnit_justified_all hcs hentc hsol
              obtain ⟨hconf2, hsol2⟩ := enqueueNorm_justified_solvable
                (problem := problem) (constraintHolds := constraintHolds)
                (st := st) (l0 := l) (reason := some r) hc hsolvable hsol
                hjust
              have hcl2 : (enqueueNorm st l (some r)).clauses = st.clauses :=
                enqueueNorm_clauses
              have hln2 : (enqueueNorm st l (some r)).learned = st.learned :=
                enqueueNorm_learned
              exact ih (enqueueNorm st l (some r)) hconf2 hsol2
                (enqueueNorm_coherent hcoh)
                (by rw [hcl2]; exact hclfix)
                (by rw [hln2]; exact hlnfix) c hrep a ha

/-! ## The level-parameterized repair and the unit justification

The two transfer pieces the analysis arm consumes: repair at ANY
target level `L` preserves representation whenever the kept entries
(levels ≤ L) are all true at every internal solution; and the unit
justification — an entailed clause whose non-pivot literals are
falsified at a solution forces the pivot true there. -/

/-! ## Level-parameterized repair (the analysis arm's transfer) -/

/-- The kept entries of a repair to level L are those at level ≤ L —
    each TRUE at every internal solution given the generalized
    soundness premise (entries atLOW levels are justified). -/
def TrailSoundBelow (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop)
    (st : State) (L : Nat) : Prop :=
  ∀ e ∈ st.trail, e.level ≤ L →
    ∀ a, ProblemSolution problem constraintHolds a →
      e.literal.eval a = some true

/-- REPAIR AT LEVEL L: representation survives the repair given
    trail-soundness below L (kept entries justified at every
    solution) and both DB entitlements. This is repair_solvedBy0
    with 0 generalized to any target level. -/
theorem repair_solvedBy_below
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    (st : State) (L : Nat)
    (hsound : TrailSoundBelow problem constraintHolds st L)
    (hclauses : ∀ c ∈ st.clauses, ∀ a, ProblemSolution problem
        constraintHolds a → ∃ l ∈ c, l.eval a = some true)
    (hlearned : ∀ c ∈ st.learned, ∀ a, ProblemSolution problem
        constraintHolds a → ∃ l ∈ c, l.eval a = some true) :
    SolvedBy problem constraintHolds (repairAfterBackjump problem L st) := by
  intro a ha
  -- the kept entries are those at level ≤ L, each true at a:
  have hkept : ∀ e ∈ (st.trail.filter fun e => decide (e.level ≤ L)),
      e.literal.eval a = some true := by
    intro e he
    simp only [List.mem_filter, decide_eq_true_eq] at he
    exact hsound e he.1 he.2 a ha
  -- the rebuilt domains fit a (iterated firing from problem.domains):
  have hfit : a.Fits (repairAfterBackjump problem L st).domains := by
    unfold repairAfterBackjump
    show a.Fits ((st.trail.filter fun e => decide (e.level ≤ L)).foldl
      (fun acc e => domOfLit acc e.literal) problem.domains)
    exact fold_fits (st.trail.filter fun e => decide (e.level ≤ L)) a
      problem.domains ha.1 hkept
  refine ⟨hfit, ?_, ?_, ?_⟩
  · intro e he
    exact hkept e he
  · intro c hc
    have hc2 : c ∈ st.clauses := by
      rw [← repair_clauses problem L st]
      exact hc
    obtain ⟨w, hw, hev⟩ := hclauses c hc2 a ha
    exact ⟨w, hw, hev⟩
  · intro c hc
    have hc2 : c ∈ st.learned := by
      rw [← repair_learned problem L st]
      exact hc
    obtain ⟨w, hw, hev⟩ := hlearned c hc2 a ha
    exact ⟨w, hw, hev⟩


/-- THE UNIT JUSTIFICATION: if clause cc is entailed, the literal `l`
    is a member of cc, and every OTHER member of cc is FALSE at a
    solution `a`, then `l` is TRUE at `a`. (Resolution's witness
    uniqueness — the per-a form of the reason-builder.) -/
theorem unit_of_entailed_falsified
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    (cc : Clause) (l : Literal)
    (a : Assignment)
    (hent : ∃ w ∈ cc, w.eval a = some true)
    (hmem : l ∈ cc)
    (hothers : ∀ q ∈ cc, q ≠ l → q.eval a = some false) :
    l.eval a = some true := by
  obtain ⟨w, hw, hev⟩ := hent
  by_cases hwl : w = l
  · rw [← hwl]; exact hev
  · exfalso
    have hf := hothers w hw hwl
    rw [hev] at hf
    exact absurd hf (by simp)

/-! ## The decision-free fragment (first certified fragment) -/


/-! ## The executable fragment check -/

/-- The problem's slot domains are all SINGLETONS: the first
    certified fragment — no decisions (bisection needs two values)
    AND the complete assignment is read off the initial domains
    directly. -/
def PropFragment (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective) : Prop :=
  ∀ d ∈ problem.domains, d.length = 1

/-- Decidability of the fragment check. -/
instance (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective) :
    Decidable (PropFragment problem) := by
  unfold PropFragment
  infer_instance

/-- When every domain has at most one int value, decideLiteral is
    none (the bisection needs two distinct extrema). -/
theorem domMinI_of_nil {α : Type} [DomainElems α] {d : α} (h : domInts d = []) :
    domMinI d = none := by
  unfold domMinI
  rw [h]
  rfl

theorem domMaxI_of_nil {α : Type} [DomainElems α] {d : α} (h : domInts d = []) :
    domMaxI d = none := by
  unfold domMaxI
  rw [h]
  rfl

theorem domMinI_of_single {α : Type} [DomainElems α] {d : α} {v : Int}
    (h : domInts d = [v]) : domMinI d = some v := by
  unfold domMinI
  rw [h]
  simp [minI]

theorem domMaxI_of_single {α : Type} [DomainElems α] {d : α} {v : Int}
    (h : domInts d = [v]) : domMaxI d = some v := by
  unfold domMaxI
  rw [h]
  simp [maxI]

theorem decideLiteral_none_of_all_single
    (doms : List Domain)
    (hall : ∀ d ∈ doms, (domInts d).length ≤ 1) :
    decideLiteral.go 0 doms = none := by
  have hgo : ∀ (s : Nat) (ds : List Domain),
      (∀ d ∈ ds, (domInts d).length ≤ 1) →
      decideLiteral.go s ds = none := by
    intro s ds
    induction ds generalizing s with
    | nil => intro _; rfl
    | cons d rest ih =>
        intro hall
        have hd : (domInts d).length ≤ 1 := hall d (List.mem_cons_self)
        have hrest : ∀ d2 ∈ rest, (domInts d2).length ≤ 1 := fun d2 hd2 =>
          hall d2 (List.mem_cons_of_mem _ hd2)
        simp only [decideLiteral.go]
        match hdi : domInts d with
        | [] =>
            have hmn : domMinI d = none := domMinI_of_nil hdi
            have hmx : domMaxI d = none := domMaxI_of_nil hdi
            rw [hmn, hmx]
            exact ih (s + 1) hrest
        | [v] =>
            have hmn : domMinI d = some v := domMinI_of_single hdi
            have hmx : domMaxI d = some v := domMaxI_of_single hdi
            rw [hmn, hmx]
            -- reduce the match on the two somes, then the mn < mx guard
            simp only []
            rw [if_neg (by omega)]
            exact ih (s + 1) hrest
        | v1 :: v2 :: vs =>
            exfalso
            have h2 : (domInts d).length ≥ 2 := by
              rw [hdi]; simp
            omega
  exact hgo 0 doms hall

/-- A singleton domain has at most one integer-viewed value. -/
theorem domInts_le_of_singleton {d : Domain}
    (h : d.length = 1) : (domInts d).length ≤ 1 := by
  unfold domInts
  rw [domElems_eq_enum]
  refine Nat.le_trans (List.length_filterMap_le _ _) ?_
  rw [Dom.length_eq_enum] at h
  omega

/-- THE FRAGMENT DISCIPLINE at the initial state: when the problem's
    domains are all singletons, `decideLiteral` at the initial root
    state returns none. -/
theorem decideLiteral_none_initial
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    (hfrag : PropFragment problem) :
    decideLiteral (initialStateWithRoots problem) = none := by
  unfold decideLiteral
  have hdoms : (initialStateWithRoots problem).domains = problem.domains :=
    initialStateWithRoots_domains problem
  rw [hdoms]
  exact decideLiteral_none_of_all_single problem.domains
    (fun d hd => domInts_le_of_singleton (hfrag d hd))

/-! ## The per-slot ≤1 discipline and the trail-fold (first
fragment machinery) -/



/-- Filtering a ≤1-element list keeps ≤ 1 elements. -/
theorem filter_le_one {α : Type} (p : α → Bool) (l : List α)
    (h : l.length ≤ 1) : (l.filter p).length ≤ 1 := by
  match l with
  | [] => simp
  | [v] =>
      by_cases hp : p v
      · simp [hp]
      · simp [hp]
  | v1 :: v2 :: rest =>
      exfalso
      simp only [List.length_cons] at h
      omega

/-- domFilterInt keeps the ≤ 1 length discipline. -/
theorem domFilterInt_le_one {d : Domain} {keep : Int → Bool}
    (h : d.length ≤ 1) : (domFilterInt keep d).length ≤ 1 := by
  unfold domFilterInt
  dsimp only
  split
  · exact h
  · rename_i hne
    rw [Dom.length_eq_enum, Dom.enum_ofList]
    exact Nat.le_trans (List.length_filter_le _ _)
      (by rwa [Dom.length_eq_enum] at h)

/-! ## The per-slot discipline through getD -/

/-- Length at the SAME in-range index after updateSlot is the image's
    length: updateSlot reads the old slot and replaces it by f of it.
    (Out of range, getD is [] on both sides and f's value on the
    DEFAULT is irrelevant — the discipline only needs in-range.) -/
theorem length_getD_updateSlot_eq : ∀ (doms : List Domain) (s : Nat)
    (f : Domain → Domain),
    s < doms.length →
    ((updateSlot doms s f).getD s Dom.empty).length = (f (doms.getD s Dom.empty)).length := by
  intro doms
  induction doms with
  | nil => intro s f hlt; simp only [List.length_nil] at hlt; exact absurd hlt (by omega)
  | cons d ds ih =>
      intro s f hlt
      cases s with
      | zero => rfl
      | succ s' =>
          simp only [updateSlot, List.getD_cons_succ,
            List.length_cons] at hlt ⊢
          exact ih s' f (by omega)

/-- Length at a DIFFERENT index after updateSlot is unchanged. -/
theorem length_getD_updateSlot_ne : ∀ (doms : List Domain)
    (s s0 : Nat) (f : Domain → Domain),
    s0 ≠ s →
    ((updateSlot doms s f).getD s0 Dom.empty).length = (doms.getD s0 Dom.empty).length := by
  intro doms
  induction doms with
  | nil =>
      intro s s0 f _
      cases s <;> cases s0 <;>
        simp [updateSlot, setSlot, getSlot, List.getD, List.length_nil]
  | cons d ds ih =>
      intro s s0 f hne
      cases s with
      | zero =>
          cases s0 with
          | zero => exact absurd rfl hne
          | succ s0' => rfl
      | succ s' =>
          cases s0 with
          | zero => rfl
          | succ s0' =>
              simp only [updateSlot, List.getD_cons_succ]
              exact ih s' s0' f (by omega)

/-! ## The per-slot discipline -/

/-- THE PER-SLOT DISCIPLINE: if every slot of doms has ≤ 1 value, so
    does every slot of domOfLit doms l — for ANY literal (both
    polarities, both atom kinds). -/
theorem domOfLt_getD_le_one : ∀ (doms : List Domain) (l : Literal),
    (∀ s : Nat, (doms.getD s Dom.empty).length ≤ 1) →
    (∀ s : Nat, ((domOfLit doms l).getD s Dom.empty).length ≤ 1) := by
  intro doms l hall
  cases l with
  | mk atom pos =>
    cases pos with
    | false =>
      cases atom with
      | intLe sl k =>
          -- NEGATIVE int literal: filter p > k at slot sl
          intro s
          show ((domOfLit doms ⟨.intLe sl k, false⟩).getD s Dom.empty).length ≤ 1
          unfold domOfLit
          simp only [Bool.false_eq_true, if_false]
          by_cases hs : s = sl
          · rw [hs]
            by_cases hrange : sl < doms.length
            · rw [length_getD_updateSlot_eq doms sl _ hrange]
              exact domFilterInt_le_one
                (d := doms.getD sl Dom.empty)
                (keep := fun p => decide (p > k))
                (hall sl)
            · have hge : doms.length ≤ sl := Nat.le_of_not_lt hrange
              unfold updateSlot
              rw [List.set_eq_of_length_le hge]
              exact hall sl
          · rw [length_getD_updateSlot_ne doms sl s _ (fun h => hs h)]
            exact hall s
      | boolEq sl b =>
          -- NEGATIVE bool literal: pin to !b at slot sl
          intro s
          show ((domOfLit doms ⟨.boolEq sl b, false⟩).getD s Dom.empty).length ≤ 1
          unfold domOfLit
          simp only [Bool.false_eq_true, if_false]
          by_cases hs : s = sl
          · rw [hs]
            by_cases hrange : sl < doms.length
            · rw [length_getD_updateSlot_eq doms sl _ hrange]
              exact Nat.le_trans (Dom.length_filter_le _ _) (hall sl)
            · have hge : doms.length ≤ sl := Nat.le_of_not_lt hrange
              unfold updateSlot
              rw [List.set_eq_of_length_le hge]
              exact hall sl
          · rw [length_getD_updateSlot_ne doms sl s _ (fun h => hs h)]
            exact hall s
      | intNe sl k =>
          -- NEGATIVE intNe literal: filter p = k at slot sl (a
          -- sub-list, so the ≤ 1 discipline carries over)
          intro s
          show ((domOfLit doms ⟨.intNe sl k, false⟩).getD s Dom.empty).length ≤ 1
          unfold domOfLit
          simp only [Bool.false_eq_true, if_false]
          by_cases hs : s = sl
          · rw [hs]
            by_cases hrange : sl < doms.length
            · rw [length_getD_updateSlot_eq doms sl _ hrange]
              exact domFilterInt_le_one
                (d := doms.getD sl Dom.empty)
                (keep := fun p => decide (p = k))
                (hall sl)
            · have hge : doms.length ≤ sl := Nat.le_of_not_lt hrange
              unfold updateSlot
              rw [List.set_eq_of_length_le hge]
              exact hall sl
          · rw [length_getD_updateSlot_ne doms sl s _ (fun h => hs h)]
            exact hall s
    | true =>
      cases atom with
      | intLe sl k =>
          -- POSITIVE int literal: filter p ≤ k at slot sl
          intro s
          show ((domOfLit doms ⟨.intLe sl k, true⟩).getD s Dom.empty).length ≤ 1
          unfold domOfLit
          simp only [if_true]
          by_cases hs : s = sl
          · rw [hs]
            by_cases hrange : sl < doms.length
            · rw [length_getD_updateSlot_eq doms sl _ hrange]
              exact domFilterInt_le_one
                (d := doms.getD sl Dom.empty)
                (keep := fun p => decide (p ≤ k))
                (hall sl)
            · have hge : doms.length ≤ sl := Nat.le_of_not_lt hrange
              unfold updateSlot
              rw [List.set_eq_of_length_le hge]
              exact hall sl
          · rw [length_getD_updateSlot_ne doms sl s _ (fun h => hs h)]
            exact hall s
      | boolEq sl b =>
          -- POSITIVE bool literal: pin to b at slot sl
          intro s
          show ((domOfLit doms ⟨.boolEq sl b, true⟩).getD s Dom.empty).length ≤ 1
          unfold domOfLit
          simp only [if_true]
          by_cases hs : s = sl
          · rw [hs]
            by_cases hrange : sl < doms.length
            · rw [length_getD_updateSlot_eq doms sl _ hrange]
              exact Nat.le_trans (Dom.length_filter_le _ _) (hall sl)
            · have hge : doms.length ≤ sl := Nat.le_of_not_lt hrange
              unfold updateSlot
              rw [List.set_eq_of_length_le hge]
              exact hall sl
          · rw [length_getD_updateSlot_ne doms sl s _ (fun h => hs h)]
            exact hall s
      | intNe sl k =>
          -- POSITIVE intNe literal: filter p ≠ k at slot sl (a
          -- sub-list, so the ≤ 1 discipline carries over)
          intro s
          show ((domOfLit doms ⟨.intNe sl k, true⟩).getD s Dom.empty).length ≤ 1
          unfold domOfLit
          simp only [if_true]
          by_cases hs : s = sl
          · rw [hs]
            by_cases hrange : sl < doms.length
            · rw [length_getD_updateSlot_eq doms sl _ hrange]
              exact domFilterInt_le_one
                (d := doms.getD sl Dom.empty)
                (keep := fun p => decide (p ≠ k))
                (hall sl)
            · have hge : doms.length ≤ sl := Nat.le_of_not_lt hrange
              unfold updateSlot
              rw [List.set_eq_of_length_le hge]
              exact hall sl
          · rw [length_getD_updateSlot_ne doms sl s _ (fun h => hs h)]
            exact hall s



/-- decideLiteral is none at ANY state with the ≤ 1-per-slot
    discipline: no bisection anywhere. -/
theorem decideLiteral_none_of_le_one (st : State)
    (hall : ∀ s : Nat, (st.domains.getD s Dom.empty).length ≤ 1) :
    decideLiteral st = none := by
  unfold decideLiteral
  have hgo : ∀ (s : Nat) (ds : List Domain),
      (∀ s2 : Nat, (ds.getD s2 Dom.empty).length ≤ 1) →
      decideLiteral.go s ds = none := by
    intro s ds
    induction ds generalizing s with
    | nil => intro _; rfl
    | cons d rest ih =>
        intro hall
        -- the head slot's length ≤ 1 means at most 1 int value
        have hd1 : (d.length ≤ 1) := by
          have := hall 0
          simp only [List.getD_cons_zero] at this
          exact this
        have hdi : (domInts d).length ≤ 1 := by
          unfold domInts
          rw [domElems_eq_enum]
          refine Nat.le_trans (List.length_filterMap_le _ _) ?_
          rw [Dom.length_eq_enum] at hd1
          exact hd1
        have hrest : ∀ s2 : Nat, (rest.getD s2 Dom.empty).length ≤ 1 := by
          intro s2
          have := hall (s2 + 1)
          simp only [List.getD_cons_succ] at this
          exact this
        simp only [decideLiteral.go]
        match hdi2 : domInts d with
        | [] =>
            have hmn : domMinI d = none := domMinI_of_nil hdi2
            have hmx : domMaxI d = none := domMaxI_of_nil hdi2
            rw [hmn, hmx]
            exact ih (s + 1) hrest
        | [v] =>
            have hmn : domMinI d = some v := domMinI_of_single hdi2
            have hmx : domMaxI d = some v := domMaxI_of_single hdi2
            rw [hmn, hmx]
            simp only []
            rw [if_neg (by omega)]
            exact ih (s + 1) hrest
        | v1 :: v2 :: vs =>
            exfalso
            have : (domInts d).length ≥ 2 := by rw [hdi2]; simp
            omega
  exact hgo 0 st.domains hall

/-! ## The go-level fragment discipline -/

/-- The enqueued state's domains after enqueueNorm are either the
    fresh-arm narrowing or the original's. -/
theorem enqueueNorm_domains_cases {st : State} {l : Literal}
    {reason : Option Reason} :
    (enqueueNorm st l reason).domains = domOfLit st.domains l.norm ∨
    (enqueueNorm st l reason).domains = st.domains := by
  unfold enqueueNorm
  cases hb : st.litOnTrail l.norm with
  | true =>
    simp only [hb, if_true]
    exact Or.inr (by simp)
  | false =>
    simp only [hb, Bool.false_eq_true, if_false]
    cases hb2 : st.negOnTrail l.norm with
    | true =>
      simp only [if_true]
      exact Or.inr (by simp)
    | false =>
      simp only [Bool.false_eq_true, if_false]
      exact Or.inl rfl

/-- propagateLoop preserves the ≤1-per-slot discipline: every domain
    change is a domOfLit step (enqueueNorm's fresh arm) or none. -/
theorem propagateLoop_le_one {props : List Propagator} :
    ∀ (fuel : Nat) (st : State),
      (∀ s : Nat, (st.domains.getD s Dom.empty).length ≤ 1) →
      (∀ s : Nat, ((propagateLoop fuel props st).domains.getD s Dom.empty).length ≤ 1) := by
  intro fuel
  induction fuel with
  | zero => intro st hall; exact hall
  | succ k ih =>
      intro st hall
      cases hc : st.conflict with
      | some c =>
          -- a conflicting state is the fixpoint: domains unchanged
          rw [propagateLoop_conflict_fix props (k + 1) st c hc]
          exact hall
      | none =>
          cases hscan : scanAll st with
          | none =>
              have hUnf : propagateLoop (k + 1) props st =
                  (if ((runPropagators props st).trail.length == st.trail.length)
                    = true then runPropagators props st
                  else propagateLoop k props (runPropagators props st)) := by
                simp [propagateLoop, hc, hscan, Option.isSome_none]
              rw [hUnf]
              -- the sweep's own discipline (runPropagators lemma):
              have hgo : ∀ (ps : List Propagator) (acc : State),
                  (∀ s : Nat, (List.getD acc.domains s Dom.empty).length ≤ 1) →
                  (∀ s : Nat, (List.getD
                    (runPropagators.go ps acc).domains
                    s Dom.empty).length ≤ 1) := by
                intro ps
                induction ps with
                | nil => intro acc hall; exact hall
                | cons p rest ihp =>
                    intro acc hall
                    have hstep : ∀ (acc2 : State) (s : Nat),
                        (∀ s : Nat, (List.getD acc2.domains s Dom.empty).length ≤ 1) →
                      (List.getD (runPropagators.go (p :: rest) acc2).domains
                        s Dom.empty).length ≤ 1 := by
                      intro acc2 s hall2
                      simp only [runPropagators.go]
                      split
                      · -- guard-true: acc unchanged
                        exact hall2 s
                      · -- guard-false: three match arms
                        next hgt =>
                        split
                        · -- stable
                          exact ihp acc2 hall2 s
                        · -- conflict: only the conflict field is set
                          next c hconf =>
                            exact hall2 s
                        · -- implied
                          next lig rsn hr =>
                            have hdom : ∀ s2 : Nat, (List.getD
                                (enqueueNorm acc2 lig (some rsn)).domains
                                s2 Dom.empty).length ≤ 1 := by
                              intro s2
                              rcases enqueueNorm_domains_cases (st := acc2)
                                (l := lig) (reason := some rsn) with hd | hd
                              · rw [hd]
                                exact domOfLt_getD_le_one acc2.domains
                                  lig.norm hall2 s2
                              · rw [hd]
                                exact hall2 s2
                            exact ihp (enqueueNorm acc2 lig (some rsn)) hdom s
                    intro s
                    exact hstep acc s hall
              by_cases hlen : ((runPropagators props st).trail.length ==
                  st.trail.length) = true
              · rw [if_pos hlen]
                exact hgo props st hall
              · rw [if_neg hlen]
                exact ih (runPropagators props st) (hgo props st hall)
          | some verdict =>
              cases verdict with
              | inl c =>
                  -- scan conflict: only the conflict field is set
                  show ∀ s : Nat, (List.getD
                    (propagateLoop (k+1) props st).domains
                    s Dom.empty).length ≤ 1
                  rw [show propagateLoop (k+1) props st
                    = { st with conflict := some c } by
                    simp [propagateLoop, hc, hscan, Option.isSome_none]]
                  exact hall
              | inr w =>
                  match w with
                  | (l, r) =>
                      have hUnf : propagateLoop (k + 1) props st
                          = propagateLoop k props (enqueueNorm st l (some r)) := by
                        simp [propagateLoop, hc, hscan, Option.isSome_none]
                      rw [hUnf]
                      -- the enqueued state's discipline (three arms)
                      have hdom : ∀ s : Nat, (List.getD
                          (enqueueNorm st l (some r)).domains
                          s Dom.empty).length ≤ 1 := by
                        intro s
                        rcases enqueueNorm_domains_cases (st := st)
                          (l := l) (reason := some r) with hd | hd
                        · rw [hd]
                          exact domOfLt_getD_le_one st.domains l.norm hall s
                        · rw [hd]
                          exact hall s
                      exact ih (enqueueNorm st l (some r)) hdom

/-! ## The trail-fold invariant (DomFold) and its preservation -/



/-- The carried invariant: the state's domains are the trail fold from
    the problem's — preserved by enqueueNorm's fresh arm, rebuilt this
    exact way by repairAfterBackjump. -/
def DomFold (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective) (st : State) : Prop :=
  st.domains = st.trail.foldl (fun acc e => domOfLit acc e.literal)
    problem.domains

/-- enqueueNorm preserves the fold invariant (the entry's fold gains
    one step for the fresh arm; other arms unchanged). -/
theorem enqueueNorm_trail_cases {st : State} {l : Literal}
    {reason : Option Reason} :
    (enqueueNorm st l reason).trail = st.trail ∨
    (enqueueNorm st l reason).trail
      = st.trail ++ [TrailEntry.mk l.norm st.decisionLevel reason] := by
  unfold enqueueNorm
  cases hb : st.litOnTrail l.norm with
  | true =>
      simp only [hb, if_true]
      exact Or.inl (by simp)
  | false =>
      simp only [hb, Bool.false_eq_true, if_false]
      cases hb2 : st.negOnTrail l.norm with
      | true =>
          simp only [hb2, if_true]
          exact Or.inl (by simp)
      | false =>
          simp only [hb2, Bool.false_eq_true, if_false]
          exact Or.inr rfl

/-- `enqueueNorm` preserves the trail-fold invariant: the fresh arm
    appends exactly one entry whose domOfLit step the fold sees; the
    other arms change nothing. -/
theorem enqueueNorm_domFold {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {st : State} {l : Literal} {reason : Option Reason}
    (hf : DomFold problem st) : DomFold problem (enqueueNorm st l reason) := by
  unfold DomFold at hf ⊢
  unfold enqueueNorm
  cases hb : st.litOnTrail l.norm with
  | true =>
      -- skip arm: state unchanged
      simp only [hb, if_true]
      exact hf
  | false =>
      simp only [hb, Bool.false_eq_true, if_false]
      cases hb2 : st.negOnTrail l.norm with
      | true =>
          -- opposing arm: only the conflict field is set
          simp only [hb2, if_true]
          show st.domains = _
          rw [show st.domains = st.domains from rfl]
          exact hf
      | false =>
          -- fresh arm: the trail appends the entry; the fold sees it
          simp only [hb2, Bool.false_eq_true, if_false]
          show domOfLit (enqueue st l.norm reason).domains l.norm = _
          rw [show (enqueue st l.norm reason).domains = st.domains from rfl]
          show domOfLit st.domains l.norm = _
          rw [show (enqueue st l.norm reason).trail
            = st.trail ++ [TrailEntry.mk l.norm st.decisionLevel reason]
            from rfl]
          rw [hf, List.foldl_append, List.foldl_cons, List.foldl_nil]



/-- Repair rebuilds the domains AS the kept-trail fold — the DomFold
    invariant holds at the repaired state by construction. -/
theorem repair_domFold {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {level : Nat} {st : State} :
    DomFold problem (repairAfterBackjump problem level st) := by
  unfold DomFold repairAfterBackjump
  rfl

/-- newDecisionLevel does not touch domains or trail. -/
theorem newDecisionLevel_domFold {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {st : State} (hf : DomFold problem st) :
    DomFold problem (newDecisionLevel st) := by
  exact hf

/-- Each root fact's domOfLit step is the identity: it pins a bound
    derived from the domain's own extrema. -/
theorem domOfLit_rootFact_id {doms : List Domain}
    : ∀ (ds : List Domain) (s : Nat) (l : Literal),
      (∀ i, ds.getD i Dom.empty = doms.getD (s + i) Dom.empty) →
      l ∈ rootFacts.go s ds → domOfLit doms l = doms := by
  intro ds
  induction ds with
  | nil => intro s l _ hl; simp only [rootFacts.go] at hl; cases hl
  | cons d rest ih =>
      intro s l hcorr hl
      simp only [rootFacts.go] at hl
      have hd : doms.getD s Dom.empty = d := by
        have := hcorr 0
        simpa using this.symm
      have hcorr' : ∀ i, rest.getD i Dom.empty
          = doms.getD (s + 1 + i) Dom.empty := by
        intro i
        have h := hcorr (i + 1)
        simp only [List.getD_cons_succ] at h
        rw [show s + (i + 1) = s + 1 + i from by omega] at h
        exact h
      -- case the two extrema; the head facts fire iff BOTH are some
      cases hmn : domMinI d with
      | some mn =>
          cases hmx : domMaxI d with
          | some mx =>
              rw [hmn, hmx] at hl
              rw [List.mem_cons] at hl
              rcases hl with rfl | hl
              · exact domOfLit_rootFact_neg (by rw [hd]; exact hmn)
              · rw [List.mem_cons] at hl
                rcases hl with rfl | hl
                · exact domOfLit_rootFact_pos (by rw [hd]; exact hmx)
                · exact ih (s + 1) l hcorr' hl
          | none =>
              -- min some, max none: the head arm does NOT fire (the
              -- match needs both); the membership is in the tail —
              -- this requires reading the match once more. The match
              -- on (some mn, none) goes to the ELSE branch.
              rw [hmn, hmx] at hl
              exact ih (s + 1) l hcorr' hl
      | none =>
          cases hmx : domMaxI d with
          | some mx => rw [hmn, hmx] at hl; exact ih (s + 1) l hcorr' hl
          | none => rw [hmn, hmx] at hl; exact ih (s + 1) l hcorr' hl



/-! ## The trail fold, the fragment discipline, and the decision-free fragment theorem

(The Phase 1 closing batch: the initial fold `initial_domFold`, the per-slot
trail-fold discipline bridge, and `go_fragment_no_decide` — at a level-0,
≤1-disciplined entry the engine loop neither decides nor recurses, so
the entry itself is the generating state for every `.unsat` outcome.) -/

/-- The root-fact fold's invariant helper: stated over the FOLD
    RESULT directly to keep the syntax projection-free. -/
def RootFoldInv (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
    (st : State) : Prop :=
  st.domains = problem.domains ∧
    st.domains = (List.foldl (fun acc e => domOfLit acc e.literal)
      problem.domains st.trail)

/-- THE TRAIL-OF-ROOT-FACTS FOLD IS THE PROBLEM'S DOMAINS: each root
    fact's domOfLit step is the identity on `problem.domains`, so any
    trail of root facts folds back to `problem.domains`. -/
theorem rootFact_trail_fold (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective) :
    ∀ (tr : List TrailEntry),
    (∀ e ∈ tr, e.literal ∈ rootFacts problem.domains) →
    (List.foldl (fun acc e => domOfLit acc e.literal) problem.domains tr)
      = problem.domains := by
  intro tr
  induction tr with
  | nil => intro _; rfl
  | cons e rest ih =>
      intro hall
      -- the head's step is the identity; apply it FIRST so the IH's
      -- fold starts from problem.domains again
      have hid : domOfLit problem.domains e.literal = problem.domains :=
        domOfLit_rootFact_id (doms := problem.domains)
          (ds := problem.domains) (s := 0) (l := e.literal)
          (fun i => by
            show problem.domains.getD i Dom.empty =
              problem.domains.getD (0 + i) Dom.empty
            rw [Nat.zero_add])
          (by
            show e.literal ∈ rootFacts problem.domains
            exact hall e (List.mem_cons_self))
      rw [List.foldl_cons, hid,
        ih (fun e2 he2 => hall e2 (List.mem_cons_of_mem _ he2))]

/-- Enqueue-folds never change the domains: `enqueue` only touches the
    trail and the skip arm returns the state unchanged. -/
theorem fold_enqueue_domains :
    ∀ (rs : List Literal) (st : State),
      (List.foldl (fun st l =>
        if st.litOnTrail l then st else enqueue st l none) st rs).domains
        = st.domains := by
  intro rs
  induction rs with
  | nil => intro st; rfl
  | cons l rest ih =>
      intro st
      rw [List.foldl_cons]
      cases hb : st.litOnTrail l with
      | true =>
          simp only [hb, if_true]
          exact ih st
      | false =>
          simp only [hb, Bool.false_eq_true, if_false]
          rw [ih (enqueue st l none)]
          rfl

/-- Every entry of an enqueue-fold's trail either was already on the
    accumulator's trail or carries one of the folded literals. -/
theorem fold_enqueue_trail_mem :
    ∀ (rs : List Literal) (st : State) (e : TrailEntry),
      e ∈ (List.foldl (fun st l =>
        if st.litOnTrail l then st else enqueue st l none) st rs).trail →
      e ∈ st.trail ∨ e.literal ∈ rs := by
  intro rs
  induction rs with
  | nil => intro st e he; exact Or.inl he
  | cons l rest ih =>
      intro st e he
      rw [List.foldl_cons] at he
      cases hb : st.litOnTrail l with
      | true =>
          simp only [hb, if_true] at he
          rcases ih st e he with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)
      | false =>
          simp only [hb, Bool.false_eq_true, if_false] at he
          -- the rest-fold starts from (enqueue st l none), whose trail
          -- is st.trail ++ [fresh]; split the IH's membership on it
          have heq : (enqueue st l none).trail
              = st.trail ++ [TrailEntry.mk l st.decisionLevel none] := rfl
          rcases ih (enqueue st l none) e he with h | h
          · rw [heq, List.mem_append] at h
            rcases h with h | h
            · exact Or.inl h
            · rw [List.mem_singleton] at h
              cases h
              exact Or.inr (List.mem_cons_self)
          · exact Or.inr (List.mem_cons_of_mem _ h)

/-- THE INITIAL FOLD: the initial state's trail carries only root
    facts, so the trail-fold is the problem's domains. -/
theorem initial_domFold (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective) :
    DomFold problem (initialStateWithRoots problem) := by
  unfold DomFold initialStateWithRoots initialState
  rw [fold_enqueue_domains (rootFacts problem.domains)
    { domains := problem.domains, trail := [], decisionLevel := 0,
      clauses := problem.clauses, learned := [], queue := [],
      conflict := none }]
  -- ⊢ problem.domains = fold over the enqueue-fold's trail
  symm
  apply rootFact_trail_fold problem
  intro e he
  rcases fold_enqueue_trail_mem (rootFacts problem.domains)
    { domains := problem.domains, trail := [], decisionLevel := 0,
      clauses := problem.clauses, learned := [], queue := [],
      conflict := none } e he with h | h
  · exact absurd h (by simp)
  · exact h

/-! ## The go-level fragment discipline -/

/-- The trail-fold keeps the ≤ 1-per-slot discipline when the problem's
    domains have it: each fold step is a domOfLit narrowing, and the
    per-slot lemma closes each one. -/
theorem fold_domOfLt_getD_le_one :
    ∀ (doms : List Domain) (tr : List TrailEntry),
    (∀ s : Nat, (doms.getD s Dom.empty).length ≤ 1) →
    (∀ s : Nat, ((tr.foldl (fun acc e => domOfLit acc e.literal)
      doms).getD s Dom.empty).length ≤ 1) := by
  intro doms tr
  induction tr generalizing doms with
  | nil => intro hall; exact hall
  | cons e rest ih =>
      intro hall
      rw [List.foldl_cons]
      exact ih (domOfLit doms e.literal)
        (domOfLt_getD_le_one doms e.literal hall)

/-- The trail-fold identity behind DomFold: a state satisfying DomFold
    inherits the problem's per-slot discipline as the fold's. -/
theorem domFold_le_one {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {st : State} (hf : DomFold problem st)
    (hfrag : ∀ s : Nat, (problem.domains.getD s Dom.empty).length ≤ 1) :
    ∀ s : Nat, (st.domains.getD s Dom.empty).length ≤ 1 := by
  intro s
  rw [hf]
  exact fold_domOfLt_getD_le_one problem.domains st.trail hfrag s

/-! ## The ≤ 1 discipline at the fragment -/

/-- getD splits: in range it is the member, out of range the default. -/
theorem getD_split {L : List Domain} (s : Nat) :
    L.getD s Dom.empty = (if h : s < L.length then L[s] else Dom.empty) := by
  simp only [List.getD]
  split
  · rename_i h
    rw [List.getElem?_eq_some_iff.mpr ⟨h, rfl⟩]
    rfl
  · rename_i h
    rw [List.getElem?_eq_none_iff.mpr (by omega)]
    rfl

/-- The fragment's problem slot discipline: every getD slot has length
    ≤ 1 (in range a singleton member; out of range the empty default) -/
theorem problem_fragment_le_one {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    (hfrag : PropFragment problem) :
    ∀ s : Nat, (problem.domains.getD s Dom.empty).length ≤ 1 := by
  intro s
  rw [getD_split]
  split
  · rename_i h
    have hd : problem.domains[s].length = 1 :=
      hfrag problem.domains[s] (List.getElem_mem h)
    rw [hd]
    exact Nat.le_refl 1
  · rw [Dom.length_eq_enum, Dom.enum_empty]
    exact Nat.zero_le 1

/-- The post-propagation state's discipline inside the fragment: the
    entry satisfies DomFold, so the propagateLoop-from-entry state has
    the ≤1 discipline via propagateLoop_le_one. -/
theorem fragment_entry_le_one {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {props : List Propagator} {st : State}
    (hf : DomFold problem st)
    (hfrag : PropFragment problem) :
    ∀ s : Nat, (List.getD (propagateLoop (engineFuel st) props st).domains
      s Dom.empty).length ≤ 1 :=
  fun s => propagateLoop_le_one (props := props) (engineFuel st) st
    (domFold_le_one hf (problem_fragment_le_one hfrag)) s

/-! ## The decision-free fragment theorem -/

/-- THE DECISION-FREE FRAGMENT THEOREM: at a level-0, slot-disciplined
    entry, `go` NEVER decides and NEVER recurses — every `.unsat`
    outcome arises at THIS state directly, in one of the two
    root-terminal shapes. The three recursion arms are impossible:
    conflicts above 0 and the level->0 retreat need a positive
    post-propagation level (contradicting level preservation from the
    entry's 0), and the decision arm needs `decideLiteral st1 = some l`
    (contradicting the bisection-free discipline at the post state).
    Hence the entry IS the generating state UnsatRun must exhibit. -/
theorem go_fragment_no_decide {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHoldsB : Constraint → Assignment → Bool}
    {props : List Propagator} :
    ∀ (fuel : Nat) (st : State),
      st.decisionLevel = 0 →
      (∀ s : Nat, (st.domains.getD s Dom.empty).length ≤ 1) →
      lcgSearch.go problem constraintHoldsB props fuel st = .unsat →
        ((propagateLoop (engineFuel st) props st).conflict.isSome = true
          ∨
        ((propagateLoop (engineFuel st) props st).conflict = none ∧
          allSingleton (propagateLoop (engineFuel st) props st) = true ∧
          ∃ a, singletonAssignment (propagateLoop (engineFuel st) props st)
            = some a ∧
            ¬ (fitsB problem a &&
                problem.constraints.all (fun c => constraintHoldsB c a)))) := by
  intro fuel
  cases fuel with
  | zero => intro st hlev hdisc h; simp only [lcgSearch.go, lcgSearchGo] at h; cases h
  | succ fuel =>
      intro st hlev hdisc h
      simp only [lcgSearch.go, lcgSearchGo] at h
      -- the discipline at the post-propagation state
      have hdisc1 : ∀ s : Nat, (List.getD
          (propagateLoop (32 + 8 * st.domains.length + 4 * st.trail.length)
            props st).domains s Dom.empty).length ≤ 1 :=
        fun s => propagateLoop_le_one
          (32 + 8 * st.domains.length + 4 * st.trail.length) st hdisc s
      -- the level stays 0 through propagation
      have hlev1 : (propagateLoop (32 + 8 * st.domains.length
          + 4 * st.trail.length) props st).decisionLevel = 0 := by
        rw [propagateLoop_decisionLevel props
          (32 + 8 * st.domains.length + 4 * st.trail.length) st]
        exact hlev
      split at h
      · -- conflict at level 0: TERMINAL, the conflict arm
        next w hw hlev0 =>
          exact Or.inl (by simp only [Option.isSome_iff_exists]; exact ⟨w, hw⟩)
      · -- conflict above 0: IMPOSSIBLE (the level stays 0)
        exfalso
        -- the arm's side condition: the level being 0 would enter the
        -- FIRST (terminal) arm; this arm only fires at a POSITIVE level
        next _ hne0 => exact hne0 hlev1
      · -- no conflict: leaf or decision
        next hnone =>
        split at h
        · next hsingle =>
          split at h
          · split at h
            · cases h
            · split at h
              · next a0 hassign hfail hlev0 =>
                  exact Or.inr ⟨hnone, hsingle, a0, hassign, hfail⟩
              · -- retreat above 0: IMPOSSIBLE (level stays 0)
                exfalso
                -- the arm fires only when the level is NOT 0 (Bool test)
                next _ hne0 =>
                  simp only [beq_iff_eq] at hne0
                  exact hne0 hlev1
          · cases h
        · split at h
          · cases h
          · -- decision arm: IMPOSSIBLE (no bisection at a ≤1
            -- disciplined state: decideLiteral is none)
            next l hl =>
              exfalso
              rw [decideLiteral_none_of_le_one _ hdisc1] at hl
              cases hl

/-- The enqueue-fold preserves the decision level (enqueue does not
    touch it; the skip arm returns the state unchanged). -/
theorem fold_enqueue_level :
    ∀ (rs : List Literal) (st : State),
      (List.foldl (fun st l =>
        if st.litOnTrail l then st else enqueue st l none) st rs).decisionLevel
        = st.decisionLevel := by
  intro rs
  induction rs with
  | nil => intro st; rfl
  | cons l rest ih =>
      intro st
      rw [List.foldl_cons]
      cases hb : st.litOnTrail l with
      | true =>
          simp only [hb, if_true]
          exact ih st
      | false =>
          simp only [hb, Bool.false_eq_true, if_false]
          have hd : (enqueue st l none).decisionLevel = st.decisionLevel := rfl
          rw [ih (enqueue st l none)]
          exact hd.symm

/-- The rooted initial state sits at decision level 0. -/
theorem initialStateWithRoots_level (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective) :
    (initialStateWithRoots problem).decisionLevel = 0 := by
  unfold initialStateWithRoots initialState
  exact fold_enqueue_level (rootFacts problem.domains)
    { domains := problem.domains, trail := [], decisionLevel := 0,
      clauses := problem.clauses, learned := [], queue := [],
      conflict := none }

end LeanFzn.Solver.Propagation

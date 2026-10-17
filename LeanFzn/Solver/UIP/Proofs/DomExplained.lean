/-
File: LeanFzn/Solver/UIP/Proofs/DomExplained.lean

Purpose:
  The CONCRETE evidence for the supported domain fragment of the
  explained closure (PLAN A3; INTERFACES §2.2/§2.8 and the §4
  premise-discharge ledger items 1-8, 28, 30). The exports:

  * `learnedExplained_of_unitLearned` — the learned-database discipline
    `UnitLearned` IMPLIES the per-state explanation obligations
    (`LearnedExplained`, the content of A2's `UnitClauseEvidence`), so
    the supported fragment needs NO caller-supplied evidence function;
  * `propagatorOfProved_unitEvidence` + `propagatorEvidence_unit` — the
    per-propagator explanation hygiene of the supported constant
    families: every explanation is a normalized unit clause whose
    literal is the pivot. Pivot membership, typed-slot range and the
    recorded-falsifier obligation are all DERIVED from the actual `run`
    equations, not assumed;
  * `unitClauseEvidence_of` + `domExplainedContract_of_problem` — the
    exported concrete constructor supplying A2's complete
    `ClosureContract`, with `PropagatorEvidence`/`UnitClauseEvidence`
    INSTANTIATED by the two items above (through A2's own
    `domExplainedContract`; nothing is re-derived);
  * maintenance: `unitLearned_explainedClosure` (the closure's own
    learning keeps the database unit-learned) and
    `unitLearned_excluded_learned` (the conflict row);
  * `stepContract_at` / `literalSound_at` — the per-state slice of the
    contract, usable by consumers (C2) and by the examples;
  * conflict classification: `conflictEvidence_at` (sound per-shape
    payload), `rootConflict_excludes_all` (the ROOT configuration is
    the only place a global UNSAT statement is exported) and
    `localConflict_excluded_only` (the `.local` fallback is branch-only);
  * `domExplainedClosureResult_spec` / `domExplainedConflict_sound` —
    A2's closure coverage/conflict theorems instantiated with the
    concrete constructor;
  * worked examples: a representative actual propagator execution, a
    representative database-unit execution, the `x ≠ y` acceptance case
    (a pivot that is NOT globally true) and the explicit unsupported
    fragment gate.

  The one premise NOT discharged here is the learned-database discipline
  quantified over the full `ReachableState` class (`hDisc`).
  `ClosureContract`'s fields range over ALL coherent branches, while the
  discipline is a property of the branches this driver actually builds.
  The maintenance lemmas below prove the closure's own transitions keep
  it; only `BranchState.learnGlobal` of an arbitrary entailed clause
  breaks it, which is outside the supported driver's contract.

  INTERFACES §4 item 17 (`AnalyzerInput`) is NOT yet in the tree: B1
  owns `AnalysisProgress.lean` and has not landed the `AnalyzerInput`
  type. This module supplies the field-compatible content it can derive
  from a real conflict event — the classification payload
  (`DomConflictEvidence.shape/excluded/entailed`, `conflictEvidence_at`) —
  and reports the exact-falsifier materialization as blocked on B1's
  type plus a frame-traceability discipline.

Dependencies:
  - LeanFzn.Solver.Propagation.DomExplained: the vocabulary this module proves facts about.
  - LeanFzn.Solver.Propagation.Proofs.Propagators: `propagatorOfProved` + its run
    inversion; LeanFzn.Solver.Propagation.Proofs.ConstFamilies: the narrow inversions.

DAG:
  DomExplained + Proofs.Propagators -> Proofs.DomExplained
  -> (B2 / C2 / D1 consumers). No runtime module imports this one.
-/

import LeanFzn.Solver.Propagation.DomExplained
import LeanFzn.Solver.Propagation.Proofs.Propagators
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler

/-! ## Learned-database hygiene -/

/-- The empty database is unit-learned. -/
theorem unitLearned_nil : UnitLearned ([] : List Clause) := by
  intro c hc
  simp at hc

/-- A single normalized literal is a unit-learned clause. -/
theorem unitLearned_singleton {q : Literal} (h : q = q.norm) :
    UnitLearned ([[q]] : List Clause) := by
  intro c hc
  exact ⟨q, List.mem_singleton.mp hc, h⟩

/-- Unit-learned databases are closed under append. -/
theorem unitLearned_append {d₁ d₂ : List Clause} (h₁ : UnitLearned d₁)
    (h₂ : UnitLearned d₂) : UnitLearned (d₁ ++ d₂) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact h₁ c hc
  · exact h₂ c hc

/-- Unit-learned databases are closed under filtering. -/
theorem unitLearned_filter {db : List Clause} (p : Clause → Bool)
    (h : UnitLearned db) : UnitLearned (db.filter p) := by
  intro c hc
  exact h c (List.mem_filter.mp hc).1

/-- The freshness-filtered single clause of a unit reason is unit-learned. -/
theorem unitLearned_if_single {c : Clause} (h : ∃ q, c = [q] ∧ q = q.norm)
    (b : Bool) : UnitLearned (if b then [c] else []) := by
  cases b with
  | true =>
      obtain ⟨q, rfl, hqn⟩ := h
      exact unitLearned_singleton hqn
  | false => exact unitLearned_nil

/-- THE DISCHARGE: a unit-learned database satisfies the per-state
explanation obligations (`LearnedExplained`, i.e. the content of A2's
`UnitClauseEvidence` field-wise). The proof never inspects the frame:
a unit clause that is unit in any frame is ITS OWN unit literal, so the
recorded-falsifier obligation is vacuous. -/
theorem learnedExplained_of_unitLearned {leaf : Assignment → Bool}
    {bs : BranchState leaf} (h : UnitLearned bs.learned) :
    LearnedExplained leaf bs := by
  intro c hc l hunit
  obtain ⟨q, hcq, hqn⟩ := h c hc
  have hunit' : ([q] : Clause).filter
      (fun l => !literalImpossible bs.frame l) = [l] := by
    rw [hcq] at hunit
    exact hunit
  have hmem : l ∈ ([q] : Clause).filter
      (fun l => !literalImpossible bs.frame l) := by
    rw [hunit']
    exact List.mem_singleton_self l
  have hlq : l = q := by
    have := (List.mem_filter.mp hmem).1
    simpa using this
  constructor
  · have hln : l.norm = q := by rw [hlq]; exact hqn.symm
    rw [hln, hcq]
    simp
  · intro q' hq' hne
    rw [hcq] at hq'
    have hq'q : q' = q := by simpa using hq'
    subst hq'q
    exact absurd hqn (by simpa [hlq] using hne)

/-! ## The learned payload of a selected deduction -/

-- NOTE: `explainedDeduction_learned_shape` MOVED DOWN to
-- `LeanFzn/Solver/UIP/ExplainedPropagation.lean` (the closure's unit-payload
-- maintenance needs it below this module in the DAG). The statement is
-- unchanged; this module and its importers see it by import.

/-- The REASON of a selected deduction is a normalized unit clause, given
the propagator kit's unit profile and a unit-learned database (the
database-sourced unit event names a learned clause, which is unit by the
discipline; the propagator-sourced event's reason is the run's
explanation clause, unit by the profile). -/
theorem deduction_reason_unit {original : List Clause}
    {props : List Propagator} {bs : BranchState leaf}
    {d : ProductiveDeduction leaf bs}
    (hProps : UnitRunProfile props) (hdb : UnitLearned bs.learned)
    (h : explainedDeduction original props bs = some d) :
    ∃ q : Literal, d.reason = [q] ∧ q = q.norm := by
  obtain ⟨c, lr, fl, hev, hr, _⟩ := explainedDeduction_learned_shape h
  rcases nextPruningEvent_implied_cases hev with hsrc | ⟨hsd, hview, hprop⟩
  · obtain ⟨hmem, hlr, hunit⟩ := scanDatabase_implied_facts hsrc
    obtain ⟨q, hcq, hqn⟩ := hdb c hmem
    exact ⟨q, by rw [hr, hcq], hqn⟩
  · obtain ⟨p, hpm, r, hrun, hcl, hlr, hfl⟩ :=
      scanPropagators_implied_facts hprop
    obtain ⟨q, hq, hqn⟩ :=
      hProps.1 p hpm (frameState bs.frame) d.literal r hrun
    exact ⟨q, by rw [hr, hcl, hq], hqn⟩

/-- The learned payload of a selected deduction is unit-learned. -/
theorem unitLearned_deduction_learned {original : List Clause}
    {props : List Propagator} {bs : BranchState leaf}
    {d : ProductiveDeduction leaf bs}
    (h : explainedDeduction original props bs = some d)
    (hunit : ∃ q : Literal, d.reason = [q] ∧ q = q.norm) :
    UnitLearned d.learned := by
  obtain ⟨c, lr, fl, hev, hr, hlearned⟩ := explainedDeduction_learned_shape h
  rw [hlearned]
  exact unitLearned_if_single (by rw [← hr]; exact hunit) _

/-- MAINTENANCE: the explained closure's own learning keeps the database
unit-learned, provided the propagator kit has the unit profile. The
recursion learns only the payload of selected deductions (never on
`.conflict` events). -/
theorem unitLearned_explainedClosure (orig : List Domain) (original : List Clause)
    (props : List Propagator) (bs : BranchState leaf)
    (hProps : UnitRunProfile props) (h : UnitLearned bs.learned) :
    UnitLearned (explainedClosure orig original props bs).learned := by
  suffices hmain : ∀ (fuel : Nat) (bs : BranchState leaf),
      Frame.mass bs.frame ≤ fuel → UnitLearned bs.learned →
      UnitLearned (explainedClosure orig original props bs).learned from
    hmain (Frame.mass bs.frame) bs (Nat.le_refl _) h
  intro fuel
  induction fuel with
  | zero =>
      intro bs hle h
      rw [explainedClosure]
      split
      · exact h
      · rename_i d _
        exfalso
        have hdec := d.decreases
        omega
  | succ fuel ih =>
      intro bs hle h
      rw [explainedClosure]
      split
      · exact h
      · rename_i d hd
        have hpay := unitLearned_deduction_learned hd
          (deduction_reason_unit hProps h hd)
        have hnew : UnitLearned (stepNarrowSync orig bs d).learned := by
          rw [stepNarrowSync_learned]
          exact unitLearned_append hpay h
        refine ih (stepNarrowSync orig bs d) ?_ hnew
        have hdec := d.decreases
        simp only [stepNarrowSync_frame]
        omega

/-- MAINTENANCE (conflict row): the learned payload of an `.excluded`
effect (the freshness-filtered conflict clauses) is unit-learned for a
conflict-unit kit; the database-sourced refutation learns nothing. -/
theorem unitLearned_excluded_learned {original : List Clause}
    {props : List Propagator} {bs : BranchState leaf} {cs : List Clause}
    (hProps : UnitRunProfile props)
    (hev : nextPruningEvent original props bs.frame bs.learned = .conflict cs) :
    UnitLearned (cs.filter fun c => !(bs.learned.contains c)) := by
  rcases nextPruningEvent_conflict_cases hev with hsrc | ⟨hsd, hview, hprop⟩
  · obtain ⟨c, hmem, hunit, hcs⟩ := scanDatabase_conflict_facts hsrc
    -- the database conflict clause is already stored: nothing is learned
    have hfilt : [c].filter (fun c => !(bs.learned.contains c)) = [] := by
      simp [List.elem_eq_mem, hmem]
    rw [hcs, hfilt]
    exact unitLearned_nil
  · obtain ⟨p, hpm, c, hrun, hcs⟩ := scanPropagators_conflict_facts hprop
    rw [hcs]
    rcases hProps.2 p hpm (frameState bs.frame) c hrun with hnil | hunit
    · rw [hnil]
      simpa using unitLearned_nil
    · by_cases hempty : c.isEmpty = true
      · rw [if_pos hempty, List.filter_nil]
        exact unitLearned_nil
      · rw [if_neg hempty]
        exact unitLearned_filter _
          (unitLearned_if_single hunit true)

/-- N1 MAINTENANCE (implied row): the learned payload of a non-productive
`.implied` event (the `filterFrame = none` local-exclusion site) is
unit-learned for a unit-profile kit and a unit-learned database — the
database-sourced reason is a learned clause (`hdb`), the propagator-sourced
reason is the run's explanation clause (`hProps`). -/
theorem unitLearned_implied_payload {leaf : Assignment → Bool}
    {original : List Clause} {props : List Propagator} {bs : BranchState leaf}
    {l : Literal} {c : Clause} {lr fl : Bool}
    (hProps : UnitRunProfile props) (hdb : UnitLearned bs.learned)
    (hev : nextPruningEvent original props bs.frame bs.learned
      = .implied l c lr fl) :
    UnitLearned (if lr && !(bs.learned.contains c) then [c] else []) := by
  rcases nextPruningEvent_implied_cases hev with hsrc | ⟨-, -, hprop⟩
  · obtain ⟨hmem, -, -⟩ := scanDatabase_implied_facts hsrc
    obtain ⟨q, hcq, hqn⟩ := hdb c hmem
    exact unitLearned_if_single ⟨q, hcq, hqn⟩ _
  · obtain ⟨p, hpm, r, hrun, hcl, _, _⟩ :=
      scanPropagators_implied_facts hprop
    obtain ⟨q, hq, hqn⟩ := hProps.1 p hpm (frameState bs.frame) l r hrun
    exact unitLearned_if_single ⟨q, by rw [hcl, hq], hqn⟩ _

/-- N1 (implied row, reason): the REASON clause of an `.implied` event is a
normalized unit for a unit-profile kit and a unit-learned database (R1c: a
filter-rejected implied literal is reported as a conflict on this clause). -/
theorem implied_reason_unit {leaf : Assignment → Bool}
    {original : List Clause} {props : List Propagator} {bs : BranchState leaf}
    {l : Literal} {c : Clause} {lr fl : Bool}
    (hProps : UnitRunProfile props) (hdb : UnitLearned bs.learned)
    (hev : nextPruningEvent original props bs.frame bs.learned
      = .implied l c lr fl) :
    ∃ q : Literal, c = [q] ∧ q = q.norm := by
  rcases nextPruningEvent_implied_cases hev with hsrc | ⟨-, -, hprop⟩
  · obtain ⟨hmem, -, -⟩ := scanDatabase_implied_facts hsrc
    exact hdb c hmem
  · obtain ⟨p, hpm, r, hrun, hcl, _, _⟩ :=
      scanPropagators_implied_facts hprop
    obtain ⟨q, hq, hqn⟩ := hProps.1 p hpm (frameState bs.frame) l r hrun
    exact ⟨q, by rw [hcl, hq], hqn⟩

/-! ## N1: the unit profile discharges `hProv` and `hShape` -/

/-- **N1 `hPROV` FROM THE UNIT PROFILE**: a unit-learned database has
insertion provenance for every clause — a unit clause `[q]` with
`q = q.norm` is its own recorded reason (`unit_clause_provenance`). -/
theorem unitLearned_provenance {leaf : Assignment → Bool}
    {bs : BranchState leaf} (h : UnitLearned bs.learned) :
    LearnedProvenance leaf bs :=
  fun c hc => by
    obtain ⟨q, rfl, hqn⟩ := h c hc
    exact unit_clause_provenance hqn

/-- **N1 `hShape` FROM THE UNIT PROFILE**: for a unit-learned database the
`hShape` premise of `unitClauseEvidence_of_provenance` is FREE — no
reachability, no inhabitedness, no liveness is consumed. A remaining
unit clause `[l]` forces `l = q` (the filter cannot change the
singleton), and the pivot is the clause's own literal. -/
theorem hshape_of_unitLearned {leaf : Assignment → Bool}
    {bs : BranchState leaf} (h : UnitLearned bs.learned) :
    ∀ (c : Clause) (l : Literal), c ∈ bs.learned →
      clauseRemaining bs.frame c = [l] →
      frameLiveB bs.frame = true →
      ∃ p : Literal, RecordedWith leaf bs c p ∧ l.norm = p := by
  intro c l hc hrem _
  obtain ⟨q, hcq, hqn⟩ := h c hc
  have hl : l = q := by
    rw [hcq] at hrem
    cases hb : literalImpossible bs.frame q with
    | false => simpa [clauseRemaining, hb] using hrem.symm
    | true => simp [clauseRemaining, hb] at hrem
  refine ⟨q, ⟨⟨hqn, by simp [hcq], ?_⟩, ?_⟩⟩
  · intro q' hq' hne
    rw [hcq] at hq'
    simp at hq'
    exact absurd hq' hne
  · simpa [hl] using hqn.symm

/-! ## The supported propagator kit: per-family explanation evidence

Each supported constant family runs through `narrowHi`/`narrowLo` with a
UNIT nogood whose literal is the implied head, or (for the Boolean
`constEq` case) returns the unit clause directly. The four obligations
below are therefore all derived from the actual `run` equations:
normalized unit reason, pivot membership, typed-slot range (the domain
read by the run determines a nonempty box slot), and the conflict row. -/

/-- The bundled per-propagator obligations of the supported kit. -/
structure UnitEvidence (p : Propagator) : Prop where
  /-- the explanation is a normalized unit clause -/
  reason_unit : ∀ st l r, p.run st = .implied l r →
    ∃ q : Literal, r.clause = [q] ∧ q = q.norm
  /-- the pivot is the clause's own literal -/
  pivot_holds : ∀ st l r, p.run st = .implied l r → (l ∈ r.clause) = True
  /-- the pivot names an in-range slot of the box the run read -/
  in_range : ∀ f, frameViewedB f = true → ∀ l r,
    p.run (frameState f) = .implied l r →
      l.atom.slot < (fullDomains f).length
  /-- conflict explanations are empty or normalized unit clauses -/
  conflict_unit : ∀ st c, p.run st = .conflict c →
    c = [] ∨ ∃ q : Literal, c = [q] ∧ q = q.norm

/-- `narrowHi` on an implied result exposes the domain extrema it read. -/
theorem narrowHi_implied_dom {st : State} {s : Nat} {hi : Int} {ng : Clause}
    {l : Literal} {r : Reason} (h : narrowHi st s hi ng = .implied l r) :
    ∃ mn mx : Int, domMinI (st.domains.getD s []) = some mn ∧
      domMaxI (st.domains.getD s []) = some mx := by
  unfold narrowHi at h
  split at h
  · rename_i mn mx hmn hmx
    exact ⟨mn, mx, hmn, hmx⟩
  · cases h

/-- `narrowLo` on an implied result exposes the domain extrema it read. -/
theorem narrowLo_implied_dom {st : State} {s : Nat} {lo : Int} {ng : Clause}
    {l : Literal} {r : Reason} (h : narrowLo st s lo ng = .implied l r) :
    ∃ mn mx : Int, domMinI (st.domains.getD s []) = some mn ∧
      domMaxI (st.domains.getD s []) = some mx := by
  unfold narrowLo at h
  split at h
  · rename_i mn mx hmn hmx
    exact ⟨mn, mx, hmn, hmx⟩
  · cases h

/-- A domain with a minimum is nonempty. -/
theorem domMinI_ne_nil {d : Domain} {mn : Int} (h : domMinI d = some mn) :
    d ≠ [] := by
  intro hnil
  rw [hnil] at h
  simp [domMinI, domInts] at h

/-- `valueMemB` success exhibits a present value, hence a nonempty list. -/
theorem valueMemB_ne_nil {v : Value} {l : List Value}
    (h : valueMemB v l = true) : l ≠ [] := by
  intro hnil
  rw [hnil] at h
  simp [valueMemB] at h

/-- A nonempty `getD` read names an in-range slot. -/
theorem getD_ne_nil_lt {α : Type} {l : List (List α)} {i : Nat}
    (h : l.getD i [] ≠ []) : i < l.length := by
  by_cases hi : i < l.length
  · exact hi
  · exfalso
    apply h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

/-- The slot-range obligation from the extrema an implied `narrowHi` run
read. -/
theorem slot_lt_of_implied_dom {st : State} {s : Nat} {hi : Int}
    {ng : Clause} {l : Literal} {r : Reason}
    (h : narrowHi st s hi ng = .implied l r) :
    s < st.domains.length := by
  obtain ⟨mn, mx, hmn, hmx⟩ := narrowHi_implied_dom h
  exact getD_ne_nil_lt (domMinI_ne_nil hmn)

/-- The slot-range obligation from the extrema an implied `narrowLo` run
read. -/
theorem slot_lt_of_implied_dom_lo {st : State} {s : Nat} {lo : Int}
    {ng : Clause} {l : Literal} {r : Reason}
    (h : narrowLo st s lo ng = .implied l r) :
    s < st.domains.length := by
  obtain ⟨mn, mx, hmn, hmx⟩ := narrowLo_implied_dom h
  exact getD_ne_nil_lt (domMinI_ne_nil hmn)

/-- In-range transfer from the frame state to the full box. -/
theorem slot_lt_frameState {f : BranchFrame} {s : Nat}
    (h : s < (frameState f).domains.length) :
    s < (fullDomains f).length := by
  simpa [fullDomains, frameState] using h

/-- The `leConstHi` family: unit reason `[posLe i c]`. -/
theorem unitEvidence_leConstHi (i : Nat) (c : Int) :
    UnitEvidence ({ watches := [.intLe i 0], run := fun st => LeanFzn.Solver.Propagation.propLeConstHi st i c } :
      Propagator) where
  reason_unit := by
    intro st l r hrun
    obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (st := st) (s := i) (hi := c)
      (ng := [posLe i c]) hrun
    subst hl
    refine ⟨posLe i c, ?_, posLe_norm i c⟩
    rw [hcl]
  pivot_holds := by
    intro st l r hrun
    obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (st := st) (s := i) (hi := c)
      (ng := [posLe i c]) hrun
    subst hl
    rw [hcl]
    simp
  in_range := by
    intro f _ l r hrun
    obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (st := frameState f) (s := i)
      (hi := c) (ng := [posLe i c]) hrun
    subst hl
    exact slot_lt_frameState
      (slot_lt_of_implied_dom (st := frameState f) (s := i) (hi := c)
        (ng := [posLe i c]) hrun)
  conflict_unit := by
    intro st c' hrun
    simp only [LeanFzn.Solver.Propagation.propLeConstHi, narrowHi] at hrun
    split at hrun
    · rename_i mn mx hmn hmx
      by_cases hgt : mn > c
      · rw [if_pos (by simpa using hgt)] at hrun
        injection hrun with hc
        subst hc
        exact Or.inr ⟨posLe i c, rfl, posLe_norm i c⟩
      · rw [if_neg (by simpa using hgt)] at hrun
        split at hrun <;> cases hrun
    · cases hrun

/-- The `leConstLo` family: unit reason `[negLe i (c−1)]`. -/
theorem unitEvidence_leConstLo (i : Nat) (c : Int) :
    UnitEvidence ({ watches := [.intLe i 0], run := fun st => LeanFzn.Solver.Propagation.propLeConstLo st i c } :
      Propagator) where
  reason_unit := by
    intro st l r hrun
    obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (st := st) (s := i) (lo := c)
      (ng := [negLe i (c - 1)]) hrun
    subst hl
    refine ⟨negLe i (c - 1), ?_, negLe_norm i (c - 1)⟩
    rw [hcl]
  pivot_holds := by
    intro st l r hrun
    obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (st := st) (s := i) (lo := c)
      (ng := [negLe i (c - 1)]) hrun
    subst hl
    rw [hcl]
    simp
  in_range := by
    intro f _ l r hrun
    obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (st := frameState f) (s := i)
      (lo := c) (ng := [negLe i (c - 1)]) hrun
    subst hl
    exact slot_lt_frameState
      (slot_lt_of_implied_dom_lo (st := frameState f) (s := i) (lo := c)
        (ng := [negLe i (c - 1)]) hrun)
  conflict_unit := by
    intro st c' hrun
    simp only [LeanFzn.Solver.Propagation.propLeConstLo, narrowLo] at hrun
    split at hrun
    · rename_i mn mx hmn hmx
      by_cases hlt : mx < c
      · rw [if_pos (by simpa using hlt)] at hrun
        injection hrun with hc
        subst hc
        exact Or.inr ⟨negLe i (c - 1), rfl, negLe_norm i (c - 1)⟩
      · rw [if_neg (by simpa using hlt)] at hrun
        split at hrun <;> cases hrun
    · cases hrun

/-- The `ltConstHi` family: unit reason `[posLe i (c−1)]`. -/
theorem unitEvidence_ltConstHi (i : Nat) (c : Int) :
    UnitEvidence ({ watches := [.intLe i 0], run := fun st => LeanFzn.Solver.Propagation.propLtConstHi st i c } :
      Propagator) where
  reason_unit := by
    intro st l r hrun
    obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (st := st) (s := i) (hi := c - 1)
      (ng := [posLe i (c - 1)]) hrun
    subst hl
    refine ⟨posLe i (c - 1), ?_, posLe_norm i (c - 1)⟩
    rw [hcl]
  pivot_holds := by
    intro st l r hrun
    obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (st := st) (s := i) (hi := c - 1)
      (ng := [posLe i (c - 1)]) hrun
    subst hl
    rw [hcl]
    simp
  in_range := by
    intro f _ l r hrun
    obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (st := frameState f) (s := i)
      (hi := c - 1) (ng := [posLe i (c - 1)]) hrun
    subst hl
    exact slot_lt_frameState
      (slot_lt_of_implied_dom (st := frameState f) (s := i) (hi := c - 1)
        (ng := [posLe i (c - 1)]) hrun)
  conflict_unit := by
    intro st c' hrun
    simp only [LeanFzn.Solver.Propagation.propLtConstHi, narrowHi] at hrun
    split at hrun
    · rename_i mn mx hmn hmx
      by_cases hgt : mn > c - 1
      · rw [if_pos (by simpa using hgt)] at hrun
        injection hrun with hc
        subst hc
        exact Or.inr ⟨posLe i (c - 1), rfl, posLe_norm i (c - 1)⟩
      · rw [if_neg (by simpa using hgt)] at hrun
        split at hrun <;> cases hrun
    · cases hrun

/-- The `ltConstLo` family: unit reason `[negLe i c]` (the implied head is
`negLe i ((c+1)−1)`, the same literal by integer arithmetic). -/
theorem unitEvidence_ltConstLo (i : Nat) (c : Int) :
    UnitEvidence ({ watches := [.intLe i 0], run := fun st => LeanFzn.Solver.Propagation.propLtConstLo st i c } :
      Propagator) where
  reason_unit := by
    intro st l r hrun
    obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (st := st) (s := i) (lo := c + 1)
      (ng := [negLe i c]) hrun
    exact ⟨negLe i c, by rw [hcl], negLe_norm i c⟩
  pivot_holds := by
    intro st l r hrun
    obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (st := st) (s := i) (lo := c + 1)
      (ng := [negLe i c]) hrun
    subst hl
    rw [hcl]
    have heq : c + 1 - 1 = c := by omega
    rw [heq]
    simp
  in_range := by
    intro f _ l r hrun
    obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (st := frameState f) (s := i)
      (lo := c + 1) (ng := [negLe i c]) hrun
    subst hl
    exact slot_lt_frameState
      (slot_lt_of_implied_dom_lo (st := frameState f) (s := i) (lo := c + 1)
        (ng := [negLe i c]) hrun)
  conflict_unit := by
    intro st c' hrun
    simp only [LeanFzn.Solver.Propagation.propLtConstLo, narrowLo] at hrun
    split at hrun
    · rename_i mn mx hmn hmx
      by_cases hlt : mx < c + 1
      · rw [if_pos (by simpa using hlt)] at hrun
        injection hrun with hc
        subst hc
        exact Or.inr ⟨negLe i c, rfl, negLe_norm i c⟩
      · rw [if_neg (by simpa using hlt)] at hrun
        split at hrun <;> cases hrun
    · cases hrun

/-- `firstEvent` of the `constEq` bound arms: membership inversion. -/
theorem narrowHi_or_narrowLo_of_firstEvent {st : State} {s : Nat} {k : Int}
    {l : Literal} {r : Reason}
    (h : firstEvent
        [narrowHi st s k [posLe s k], narrowLo st s k [negLe s (k - 1)]]
        = .implied l r) :
    narrowHi st s k [posLe s k] = .implied l r ∨
      narrowLo st s k [negLe s (k - 1)] = .implied l r := by
  have hmem := firstEvent_mem _ _ h
  rcases hmem with hstab | hmem
  · cases hstab
  · rcases List.mem_cons.mp hmem with h1 | h2
    · exact Or.inl h1.symm
    · exact Or.inr (List.mem_singleton.mp h2).symm

/-- The `constEq` family (integer constants): the firstEvent of the two
bound arms. -/
theorem unitEvidence_constEqInt (i : Nat) (k : Int) :
    UnitEvidence ({ watches := [.intLe i 0], run := fun st => LeanFzn.Solver.Propagation.propConstEq st i (.int k) } :
      Propagator) where
  reason_unit := by
    intro st l r hrun
    rcases narrowHi_or_narrowLo_of_firstEvent hrun with h | h
    · obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (st := st) (s := i) (hi := k)
        (ng := [posLe i k]) h
      subst hl
      refine ⟨posLe i k, ?_, posLe_norm i k⟩
      rw [hcl]
    · obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (st := st) (s := i) (lo := k)
        (ng := [negLe i (k - 1)]) h
      subst hl
      refine ⟨negLe i (k - 1), ?_, negLe_norm i (k - 1)⟩
      rw [hcl]
  pivot_holds := by
    intro st l r hrun
    rcases narrowHi_or_narrowLo_of_firstEvent hrun with h | h
    · obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (st := st) (s := i) (hi := k)
        (ng := [posLe i k]) h
      subst hl
      rw [hcl]
      simp
    · obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (st := st) (s := i) (lo := k)
        (ng := [negLe i (k - 1)]) h
      subst hl
      rw [hcl]
      simp
  in_range := by
    intro f _ l r hrun
    rcases narrowHi_or_narrowLo_of_firstEvent hrun with h | h
    · obtain ⟨hl, _⟩ := narrowHi_implied_inv (st := frameState f) (s := i)
        (hi := k) (ng := [posLe i k]) h
      subst hl
      exact slot_lt_frameState
        (slot_lt_of_implied_dom (st := frameState f) (s := i) (hi := k)
          (ng := [posLe i k]) h)
    · obtain ⟨hl, _⟩ := narrowLo_implied_inv (st := frameState f) (s := i)
        (lo := k) (ng := [negLe i (k - 1)]) h
      subst hl
      exact slot_lt_frameState
        (slot_lt_of_implied_dom_lo (st := frameState f) (s := i) (lo := k)
          (ng := [negLe i (k - 1)]) h)
  conflict_unit := by
    intro st c' hrun
    change LeanFzn.Solver.Propagation.propConstEq st i (.int k) = .conflict c' at hrun
    simp only [LeanFzn.Solver.Propagation.propConstEq] at hrun
    -- a conflict from firstEvent: the bound arms' conflicts
    have hmem := firstEvent_mem _ _ hrun
    rcases hmem with hstab | hmem
    · cases hstab
    · rcases List.mem_cons.mp hmem with h1 | h2
      · -- narrowHi conflict
        have hc : narrowHi st i k [posLe i k] = .conflict c' := h1.symm
        simp only [narrowHi] at hc
        split at hc
        · rename_i mn mx hmn hmx
          by_cases hgt : mn > k
          · rw [if_pos (by simpa using hgt)] at hc
            injection hc with hcEq
            subst hcEq
            exact Or.inr ⟨posLe i k, rfl, posLe_norm i k⟩
          · rw [if_neg (by simpa using hgt)] at hc
            split at hc <;> cases hc
        · cases hc
      · -- narrowLo conflict
        have hc : narrowLo st i k [negLe i (k - 1)] = .conflict c' :=
          (List.mem_singleton.mp h2).symm
        simp only [narrowLo] at hc
        split at hc
        · rename_i mn mx hmn hmx
          by_cases hlt : mx < k
          · rw [if_pos (by simpa using hlt)] at hc
            injection hc with hcEq
            subst hcEq
            exact Or.inr ⟨negLe i (k - 1), rfl, negLe_norm i (k - 1)⟩
          · rw [if_neg (by simpa using hlt)] at hc
            split at hc <;> cases hc
        · cases hc

/-- The `constEq` family (Boolean constants): the direct unit clause
`[posBool i b]`. -/
theorem unitEvidence_constEqBool (i : Nat) (b : Bool) :
    UnitEvidence ({ watches := [.intLe i 0], run := fun st => LeanFzn.Solver.Propagation.propConstEq st i (.bool b) } :
      Propagator) where
  reason_unit := by
    intro st l r hrun
    simp only [LeanFzn.Solver.Propagation.propConstEq] at hrun
    split at hrun
    · split at hrun
      · cases hrun
      · rename_i hne
        injection hrun with hl hr
        refine ⟨posBool i b, ?_, posBool_norm i b⟩
        rw [← hr]
    · cases hrun
  pivot_holds := by
    intro st l r hrun
    simp only [LeanFzn.Solver.Propagation.propConstEq] at hrun
    split at hrun
    · split at hrun
      · cases hrun
      · rename_i hne
        injection hrun with hl hr
        rw [← hr, ← hl]
        simp
    · cases hrun
  in_range := by
    intro f _ l r hrun
    simp only [LeanFzn.Solver.Propagation.propConstEq] at hrun
    split at hrun
    · split at hrun
      · cases hrun
      · rename_i hmem hne
        injection hrun with hl hr
        subst hl
        exact slot_lt_frameState
          (getD_ne_nil_lt (valueMemB_ne_nil hmem))
    · cases hrun
  conflict_unit := by
    intro st c' hrun
    simp only [LeanFzn.Solver.Propagation.propConstEq] at hrun
    split at hrun
    · split at hrun <;> cases hrun
    · rename_i hmem
      injection hrun with hc
      subst hc
      exact Or.inr ⟨posBool i b, rfl, posBool_norm i b⟩

/-- The `constEq` family with a set constant never implies or conflicts. -/
theorem unitEvidence_constEqSet (i : Nat) (x : IntSetValue) :
    UnitEvidence ({ watches := [.intLe i 0], run := fun st => LeanFzn.Solver.Propagation.propConstEq st i (.setOfInt x) } :
      Propagator) where
  reason_unit := by
    intro st l r hrun
    cases hrun
  pivot_holds := by
    intro st l r hrun
    cases hrun
  in_range := by
    intro f _ l r hrun
    cases hrun
  conflict_unit := by
    intro st c' hrun
    cases hrun

/-- The `constEq` family with an array constant never implies or conflicts. -/
theorem unitEvidence_constEqArray (i : Nat) (x : List Value) :
    UnitEvidence
      ({ watches := [.intLe i 0], run := fun st => LeanFzn.Solver.Propagation.propConstEq st i (.array x) } :
      Propagator) where
  reason_unit := by
    intro st l r hrun
    cases hrun
  pivot_holds := by
    intro st l r hrun
    cases hrun
  in_range := by
    intro f _ l r hrun
    cases hrun
  conflict_unit := by
    intro st c' hrun
    cases hrun

/-- CONCRETE DISPATCH: every constraint of the supported fragment
registers a propagator with the unit evidence. -/
theorem propagatorOfProved_unitEvidence (dc : DomConstraint)
    (h : unitFamilyB dc = true) {p : Propagator}
    (hp : propagatorOfProved dc = some p) : UnitEvidence p := by
  cases dc with
  | leConstHi i c =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact unitEvidence_leConstHi i c
  | leConstLo i c =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact unitEvidence_leConstLo i c
  | ltConstHi i c =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact unitEvidence_ltConstHi i c
  | ltConstLo i c =>
      simp only [propagatorOfProved, Option.some.injEq] at hp
      subst hp
      exact unitEvidence_ltConstLo i c
  | constEq i v =>
      cases v with
      | int k =>
          simp only [propagatorOfProved, Option.some.injEq] at hp
          subst hp
          exact unitEvidence_constEqInt i k
      | bool b =>
          simp only [propagatorOfProved, Option.some.injEq] at hp
          subst hp
          exact unitEvidence_constEqBool i b
      | setOfInt x =>
          simp only [propagatorOfProved, Option.some.injEq] at hp
          subst hp
          exact unitEvidence_constEqSet i x
      | array x =>
          simp only [propagatorOfProved, Option.some.injEq] at hp
          subst hp
          exact unitEvidence_constEqArray i x
  | eqSlot i j => simp [unitFamilyB] at h
  | neSlot i j => simp [unitFamilyB] at h
  | leSlot i j => simp [unitFamilyB] at h
  | plusSlot i j k => simp [unitFamilyB] at h
  | allDiff is => simp [unitFamilyB] at h
  | timesSlot i j k => simp [unitFamilyB] at h
  | minSlot i j k => simp [unitFamilyB] at h
  | maxSlot i j k => simp [unitFamilyB] at h
  | absSlot i k => simp [unitFamilyB] at h
  | linEq coeffs is b => simp [unitFamilyB] at h
  | linLe coeffs is b => simp [unitFamilyB] at h
  | linNe coeffs is b => simp [unitFamilyB] at h
  | ltSlot i j => simp [unitFamilyB] at h
  | boolNotSlot i j => simp [unitFamilyB] at h
  | boolAndSlot i j k => simp [unitFamilyB] at h
  | boolOrSlot i j k => simp [unitFamilyB] at h
  | boolClauseSlot ps ns =>
      simp only [propagatorOfProved] at hp
      exact absurd hp (by intro hc; cases hc)
  | arrayBoolAndSlot is k =>
      simp only [propagatorOfProved] at hp
      exact absurd hp (by intro hc; cases hc)
  | bool2intSlot i k =>
      simp only [propagatorOfProved] at hp
      exact absurd hp (by intro hc; cases hc)
  | boolEqSlot i j =>
      simp only [propagatorOfProved] at hp
      exact absurd hp (by intro hc; cases hc)
  | arrayIntElementSlot xs i k =>
      simp only [propagatorOfProved] at hp
      exact absurd hp (by intro hc; cases hc)
  | arrayVarIntElementSlot is i k =>
      simp only [propagatorOfProved] at hp
      exact absurd hp (by intro hc; cases hc)
  | arrayVarBoolElementSlot is i k =>
      simp only [propagatorOfProved] at hp
      exact absurd hp (by intro hc; cases hc)
  | eqReifSlot i j r => simp [unitFamilyB] at h
  | leReifSlot i j r => simp [unitFamilyB] at h
  | neReifSlot i j r => simp [unitFamilyB] at h
  | linEqReif coeffs is b r => simp [unitFamilyB] at h
  | linLeReif coeffs is b r => simp [unitFamilyB] at h
  | linNeReif coeffs is b r => simp [unitFamilyB] at h
  | minPair o₀ o₁ r => simp [unitFamilyB] at h
  | maxPair o₀ o₁ r => simp [unitFamilyB] at h
  | divGen o₁ o₂ r => simp [unitFamilyB] at h
  | modGen o₁ o₂ r => simp [unitFamilyB] at h
  | maxGen os r => simp [unitFamilyB] at h
  | minGen os r => simp [unitFamilyB] at h

/-- THE SUPPORTED KIT'S PROFILE: `dcs.filterMap propagatorOfProved` with
all constraints supported has the unit run profile — every implied
explanation is a normalized unit clause and every conflict explanation is
empty or such a clause. Both halves are DERIVED from the registered
`run` equations. -/
theorem unitRunProfile_proved (dcs : List DomConstraint)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true) :
    UnitRunProfile (dcs.filterMap propagatorOfProved) := by
  constructor
  · intro p hpm st l r hrun
    obtain ⟨dc, hdc, hprop⟩ := propagatorsOfProved_mem hpm
    exact (propagatorOfProved_unitEvidence dc (hSupp dc hdc) hprop).reason_unit
      st l r hrun
  · intro p hpm st c hrun
    obtain ⟨dc, hdc, hprop⟩ := propagatorsOfProved_mem hpm
    exact (propagatorOfProved_unitEvidence dc (hSupp dc hdc) hprop).conflict_unit
      st c hrun

/-- THE EXPORT (propagator half): the supported kit supplies A2's
`PropagatorEvidence` — pivot membership, typed-slot range and recorded
falsifiers all derived from the run equations. -/
theorem propagatorEvidence_unit {leaf : Assignment → Bool}
    (dcs : List DomConstraint)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true) :
    PropagatorEvidence leaf (dcs.filterMap propagatorOfProved) where
  pivot := by
    intro f _ p hpm l r hrun
    obtain ⟨dc, hdc, hprop⟩ := propagatorsOfProved_mem hpm
    have hev := propagatorOfProved_unitEvidence dc (hSupp dc hdc) hprop
    obtain ⟨q, hcq, hqn⟩ := hev.reason_unit (frameState f) l r hrun
    have hmem : (l ∈ r.clause) = True := hev.pivot_holds (frameState f) l r hrun
    have hlq : l = q := by
      have hdt : l ∈ r.clause := hmem.symm ▸ True.intro
      rw [hcq] at hdt
      simpa using hdt
    rw [hlq, hcq, ← hqn]
    simp
  inRange := by
    intro f hview p hpm l r hrun
    obtain ⟨dc, hdc, hprop⟩ := propagatorsOfProved_mem hpm
    exact (propagatorOfProved_unitEvidence dc (hSupp dc hdc) hprop).in_range
      f hview l r hrun
  recorded := by
    intro bs p hpm l r hrun
    obtain ⟨dc, hdc, hprop⟩ := propagatorsOfProved_mem hpm
    have hev := propagatorOfProved_unitEvidence dc (hSupp dc hdc) hprop
    obtain ⟨q, hcq, hqn⟩ := hev.reason_unit (frameState bs.frame) l r hrun
    have hmem : (l ∈ r.clause) = True :=
      hev.pivot_holds (frameState bs.frame) l r hrun
    have hlq : l = q := by
      have hdt : l ∈ r.clause := hmem.symm ▸ True.intro
      rw [hcq] at hdt
      simpa using hdt
    intro q' hq' hne
    rw [hcq] at hq'
    have hq'q : q' = q := by simpa using hq'
    subst hq'q
    exact absurd hqn (by simpa [hlq] using hne)

/-! ## The export: A2's complete contract, instantiated -/

/-! ## N1: the supported conflict payload is a normalized unit clause -/

/-- **N1 CONFLICT-UNIT LEMMA**: for the supported fragment, every ANALYZED
conflict of the closure carries a NORMALIZED UNIT clause: a database
conflict reports the stored clause itself (R1c routing), which is a
normalized unit under the unit-learned database discipline `hdb`; a
propagator conflict's payload is exactly the singleton of the propagator's
conflict clause — and the `UnitRunProfile` of the supported kit makes that
clause a normalized unit. -/
theorem supported_conflict_clause_unit {leaf : Assignment → Bool}
    {dcs : List DomConstraint}
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    {original : List Clause} {bs : BranchState leaf} {c : Clause}
    {rest : List Clause} (hdb : UnitLearned bs.learned)
    (hev : nextPruningEvent original (dcs.filterMap propagatorOfProved)
        bs.frame bs.learned = .conflict (c :: rest)) :
    rest = [] ∧ ∃ q : Literal, c = [q] ∧ q = q.norm := by
  rcases nextPruningEvent_conflict_cases hev with hsd | ⟨-, -, hprop⟩
  · -- DATABASE conflict: the payload is the stored (unit) clause
    obtain ⟨d, hd, -, hcs⟩ := scanDatabase_conflict_facts hsd
    injection hcs with hcd hrest
    obtain ⟨q, hdq, hqn⟩ := hdb d hd
    exact ⟨hrest, q, by rw [hcd, hdq], hqn⟩
  · -- PROPAGATOR conflict: the payload is `if c'.isEmpty then [] else [c']`
    obtain ⟨p, hpm, c', hrun, hcs⟩ := scanPropagators_conflict_facts hprop
    cases hb : c'.isEmpty with
    | true =>
        rw [hb] at hcs
        simp at hcs
    | false =>
        rw [hb] at hcs
        injection hcs with hcc hrest
        rcases (unitRunProfile_proved dcs hSupp).2 p hpm (frameState bs.frame) c'
            hrun with hnil | ⟨q, hcq, hqn⟩
        · rw [hnil] at hb
          simp at hb
        · exact ⟨hrest, q, by rw [hcc, hcq], hqn⟩

/-- The learned-database discipline instantiates A2's
`UnitClauseEvidence` field-wise. -/
theorem unitClauseEvidence_of {leaf : Assignment → Bool} {orig : List Domain}
    (h : ∀ bs : BranchState leaf, ReachableState leaf orig bs →
      UnitDB bs.learned →
      ∀ c ∈ bs.learned, ∀ l, clauseRemaining bs.frame c = [l] →
        (l.norm ∈ c) = True ∧ DomReasonRecorded leaf bs l c) :
    UnitClauseEvidence leaf orig where
  pivot := fun bs hreach hu c hc l hunit _ => (h bs hreach hu c hc l hunit).1
  recorded := fun bs hreach hu c hc l hunit _ => (h bs hreach hu c hc l hunit).2

/-- THE EXPORTED CONCRETE CONSTRUCTOR: A2's complete `ClosureContract` for
the supported fragment. Every `PropagatorEvidence` field is supplied by
the caller's already-proved `hEvidence` (for the concrete kit:
`propagatorEvidence_unit`), every `UnitClauseEvidence` field by the
learned-database discipline. No `hLit`/`hEnt`/`hPiv`/`hRec`/`hRange`
function is asked of the caller. -/
theorem domExplainedContract_units
    {leaf : Assignment → Bool} {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    (hOriginal : ∀ c ∈ original, ∀ a, leaf a = true → c.SatisfiedBy a)
    (hViewed : ∀ d ∈ orig, IntViewedDomain d)
    (hSorts : DomsShapeTyped orig)
    (hLeafFits : ∀ a, leaf a = true → a.Fits orig)
    (hp : PropagationContract leaf props)
    (hEvidence : PropagatorEvidence leaf props)
    (hDisc : ∀ bs : BranchState leaf, ReachableState leaf orig bs →
      UnitDB bs.learned → LearnedExplained leaf bs) :
    ClosureContract leaf orig original props :=
  domExplainedContract hOriginal hViewed hSorts hLeafFits hp hEvidence
    (unitClauseEvidence_of hDisc)

/-- THE EXPORTED CONCRETE CONSTRUCTOR at the problem level: the supported
fragment's kit. `hp` is the certified propagator contract (discharged for
the concrete problem by `domPropagationContract`); `hOriginal` is the
compiled-database entailment (the existing certified path's `hdb`
premise); `hDisc` is the learned-database discipline. Everything else is
derived by this module. -/
theorem domExplainedContract_of_problem
    {leaf : Assignment → Bool} (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit)
    (hp : PropagationContract leaf
      (problem.constraints.filterMap propagatorOfProved))
    (hSupp : ∀ dc ∈ problem.constraints, unitFamilyB dc = true)
    (hOriginal : ∀ c ∈ problem.clauses, ∀ a, leaf a = true → c.SatisfiedBy a)
    (hViewed : ∀ d ∈ problem.domains, IntViewedDomain d)
    (hSorts : DomsShapeTyped problem.domains)
    (hLeafFits : ∀ a, leaf a = true → a.Fits problem.domains)
    (hDisc : ∀ bs : BranchState leaf, ReachableState leaf problem.domains bs →
      UnitDB bs.learned → LearnedExplained leaf bs) :
    ClosureContract leaf problem.domains problem.clauses
      (problem.constraints.filterMap propagatorOfProved) :=
  domExplainedContract_units hOriginal hViewed hSorts hLeafFits hp
    (propagatorEvidence_unit problem.constraints hSupp) hDisc

/-- The same constructor with the WEAKER, purely syntactic discipline:
a unit-learned database (`UnitLearned`) discharges the per-state
obligations via `learnedExplained_of_unitLearned`. -/
theorem domExplainedContract_of_problem_unitLearned
    {leaf : Assignment → Bool} (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit)
    (hp : PropagationContract leaf
      (problem.constraints.filterMap propagatorOfProved))
    (hSupp : ∀ dc ∈ problem.constraints, unitFamilyB dc = true)
    (hOriginal : ∀ c ∈ problem.clauses, ∀ a, leaf a = true → c.SatisfiedBy a)
    (hViewed : ∀ d ∈ problem.domains, IntViewedDomain d)
    (hSorts : DomsShapeTyped problem.domains)
    (hLeafFits : ∀ a, leaf a = true → a.Fits problem.domains)
    (hDisc : ∀ bs : BranchState leaf, ReachableState leaf problem.domains bs →
      UnitLearned bs.learned) :
    ClosureContract leaf problem.domains problem.clauses
      (problem.constraints.filterMap propagatorOfProved) :=
  domExplainedContract_of_problem problem hp hSupp hOriginal hViewed hSorts hLeafFits
    (fun bs hreach _ => learnedExplained_of_unitLearned (hDisc bs hreach))

/-! ## Per-state slices and the closure coverage/conflict theorems -/

/-- The per-state slice of A2's contract: every obligation `StepContract`
asks of ONE state is the corresponding `ClosureContract` field at that
state, so consumers do not re-derive field by field. -/
theorem stepContract_at {orig : List Domain} {original : List Clause}
    {props : List Propagator} (hc : ClosureContract leaf orig original props)
    {bs : BranchState leaf} (hreach : ReachableState leaf orig bs)
    (hu : UnitDB bs.learned) :
    StepContract leaf original props bs where
  conflictExcludes := fun cs hev => hc.conflictExcludes bs hreach cs hev
  conflictEntailed := fun cs hev => hc.conflictEntailed bs hreach cs hev
  impliedEntailed := fun l c lr fl hev =>
    hc.reasonEntailed bs hreach l c lr fl hev
  impliedPivot := fun l c lr fl hev => hc.pivot bs hreach hu l c lr fl hev
  impliedChronology := fun l c lr fl hev =>
    hc.chronology bs hreach hu l c lr fl hev
  impliedInRange := fun l c lr fl hev => hc.inRange bs hreach l c lr fl hev

/-- BRANCH-RELATIVE implication of the SELECTED deduction event at one
reachable state — the `x ≠ y` discipline: no global pivot truth. -/
theorem literalSound_at {orig : List Domain} {original : List Clause}
    {props : List Propagator} (hc : ClosureContract leaf orig original props)
    {bs : BranchState leaf} (hreach : ReachableState leaf orig bs)
    {l : Literal} {c : Clause} {lr fl : Bool}
    (hev : nextPruningEvent original props bs.frame bs.learned
      = .implied l c lr fl)
    {a : Assignment} (hleaf : leaf a = true) (hrep : bs.Represents a) :
    l.norm.eval a = some true :=
  hc.literalSound bs hreach l c lr fl hev a hleaf hrep

/-! ## Conflict classification and the root/local discipline -/

/-- An assignment fitting a domain box is enumerated by `allAssigns`. -/
theorem fits_mem_allAssigns {a : Assignment} {ds : List Domain}
    (h : a.Fits ds) : a ∈ allAssigns ds :=
  mem_allAssigns_of_getElem? ds a h.1 h.2

/-- The root state represents every fitting assignment of the original
box: its frame is the whole box with an empty prefix. -/
theorem root_init_represents {a : Assignment} {orig : List Domain}
    {leaf : Assignment → Bool} (hfit : a.Fits orig) :
    (BranchState.init (orig, []) : BranchState leaf).Represents a := by
  have hcov : FrameCovers ((orig, []) : BranchFrame) a :=
    ⟨a, fits_mem_allAssigns hfit, by simp⟩
  refine ⟨?_, ?_, ?_⟩
  · exact hcov
  · intro e he
    simp [BranchState.init] at he
  · intro c hc'
    simp [BranchState.init] at hc'

/-- The sound payload of one ACTUAL conflict event, derived from the
contract: the frozen shape classification plus the two branch-relative
soundness facts. `.local` carries no global claim. (A `def` because
`DomConflictEvidence` carries the shape as data.) -/
def conflictEvidence_at {orig : List Domain} {original : List Clause}
    {props : List Propagator} (hc : ClosureContract leaf orig original props)
    {bs : BranchState leaf} (hreach : ReachableState leaf orig bs)
    {cs : List Clause}
    (hev : nextPruningEvent original props bs.frame bs.learned = .conflict cs) :
    DomConflictEvidence leaf bs cs where
  shape := classifyConflict bs.level cs
  shape_eq := rfl
  excluded := hc.conflictExcludes bs hreach cs hev
  entailed := hc.conflictEntailed bs hreach cs hev

/-- THE ROOT EXPORT: a conflict selected at the ROOT configuration
excludes EVERY original leaf solution — the only global statement this
kit exports. Derived from the branch-relative `conflictExcludes` at the
reachable root state plus the fits/`allAssigns` bridge, never from a
classification tag alone. -/
theorem rootConflict_excludes_all {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    (hc : ClosureContract leaf orig original props) {cs : List Clause}
    (hev : nextPruningEvent original props (orig, []) [] = .conflict cs) :
    ∀ a, leaf a = true → a.Fits orig → False := by
  intro a hleaf hfit
  exact hc.conflictExcludes (BranchState.init (orig, []))
    (reachable_init leaf orig) cs hev a hleaf (root_init_represents hfit)

/-- The ROOT classification composes with the root configuration: a
`.root`-classified conflict at the root state is nonempty and yields
the global exclusion. The tag alone is never enough — the state must BE
the root state, which is what makes the global claim sound. -/
theorem rootConflict_excludes_all_of_shape {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    (hc : ClosureContract leaf orig original props) {cs : List Clause}
    (hev : nextPruningEvent original props (orig, []) [] = .conflict cs)
    (hshape : classifyConflict 0 cs = ConflictShape.root) :
    cs ≠ [] ∧ (∀ a, leaf a = true → a.Fits orig → False) := by
  refine ⟨?_, rootConflict_excludes_all hc hev⟩
  intro hnil
  rw [hnil] at hshape
  exact absurd hshape (by decide)

/-- THE LOCAL FALLBACK: a `.local`-shaped conflict yields exactly the
branch-exclusion field (and keeps its tag). Stated so consumers cannot
read a global UNSAT out of a local shape: the only global export is
`rootConflict_excludes_all`, which needs the root configuration. -/
theorem localConflict_excluded_only {leaf : Assignment → Bool}
    {bs : BranchState leaf} {cs : List Clause}
    {ev : DomConflictEvidence leaf bs cs}
    (hlocal : ev.shape = ConflictShape.local) :
    ev.shape = ConflictShape.local ∧
      (∀ a, leaf a = true → bs.Represents a → False) :=
  ⟨hlocal, ev.excluded⟩

/-! ## The closure coverage/conflict theorems at the supported problem -/

/-- THE CLOSURE COVERAGE/CONFLICT THEOREM for the supported fragment
(INTERFACES §2.2 `explainedClosureResult_spec`, instantiated with the
concrete constructor): every run of the result-returning closure driven
by the supported kit stays coherent, learns only entailed clauses, and
covers — resp. branch-excludes — every leaf solution the input state
represented. -/
theorem domExplainedClosureResult_spec {leaf : Assignment → Bool}
    (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit)
    (hp : PropagationContract leaf
      (problem.constraints.filterMap propagatorOfProved))
    (hSupp : ∀ dc ∈ problem.constraints, unitFamilyB dc = true)
    (hOriginal : ∀ c ∈ problem.clauses, ∀ a, leaf a = true → c.SatisfiedBy a)
    (hViewed : ∀ d ∈ problem.domains, IntViewedDomain d)
    (hSorts : DomsShapeTyped problem.domains)
    (hLeafFits : ∀ a, leaf a = true → a.Fits problem.domains)
    (hDisc : ∀ bs : BranchState leaf, ReachableState leaf problem.domains bs →
      UnitDB bs.learned → LearnedExplained leaf bs)
    (hpay : UnitPayload problem.clauses
      (problem.constraints.filterMap propagatorOfProved))
    {bs : BranchState leaf} (hreach : ReachableState leaf problem.domains bs)
    (hu : UnitDB bs.learned) :
    ClosureResult.Spec leaf problem.domains bs
      (explainedClosureResult problem.domains problem.clauses
        (problem.constraints.filterMap propagatorOfProved) bs) :=
  explainedClosureResult_spec
    (domExplainedContract_of_problem problem hp hSupp hOriginal hViewed hSorts hLeafFits hDisc)
    bs hpay hreach hu

/-- The conflict-classification corollary at the supported problem: every
conflict event of the kit's closure yields the sound classification
payload (branch-relative exclusion + global entailment). -/
def domExplainedConflict_sound {leaf : Assignment → Bool}
    (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit)
    (hp : PropagationContract leaf
      (problem.constraints.filterMap propagatorOfProved))
    (hSupp : ∀ dc ∈ problem.constraints, unitFamilyB dc = true)
    (hOriginal : ∀ c ∈ problem.clauses, ∀ a, leaf a = true → c.SatisfiedBy a)
    (hViewed : ∀ d ∈ problem.domains, IntViewedDomain d)
    (hSorts : DomsShapeTyped problem.domains)
    (hLeafFits : ∀ a, leaf a = true → a.Fits problem.domains)
    (hDisc : ∀ bs : BranchState leaf, ReachableState leaf problem.domains bs →
      UnitDB bs.learned → LearnedExplained leaf bs)
    {bs : BranchState leaf} (hreach : ReachableState leaf problem.domains bs)
    {cs : List Clause}
    (hev : nextPruningEvent problem.clauses
      (problem.constraints.filterMap propagatorOfProved) bs.frame bs.learned
        = .conflict cs) :
    DomConflictEvidence leaf bs cs :=
  conflictEvidence_at
    (domExplainedContract_of_problem problem hp hSupp hOriginal hViewed hSorts hLeafFits hDisc)
    hreach hev

/-! ## Worked examples (PLAN A3 done criteria) -/

/-- Slot 0's original domain: `{0, 1, 2}`. -/
private def exOrig : List Domain := [[.int 0, .int 1, .int 2]]

/-- The root frame of the example: the whole box, empty prefix. -/
private def exFrame : BranchFrame := (exOrig, [])

/-- The example's leaf semantics: slot 0 is at most 1. -/
private def exLeaf : Assignment → Bool := fun a =>
  match slotInt a 0 with
  | some i => decide (i ≤ 1)
  | none => false

/-- The registered supported kit of `leConstHi 0 1`. -/
private def exProps : List Propagator :=
  [DomConstraint.leConstHi 0 1].filterMap propagatorOfProved

/-- The example's clause database: empty (the propagator carries the
explanation). -/
private def exOriginal : List Clause := []

/-- The root state of the propagator example. -/
private def exState : BranchState exLeaf := BranchState.init exFrame

/-- Every leaf solution of the example satisfies `x ≤ 1`. -/
private theorem exLeaf_posLe {a : Assignment} (h : exLeaf a = true) :
    (posLe 0 1).eval a = some true := by
  cases hs : slotInt a 0 with
  | none => simp [exLeaf, hs] at h
  | some i =>
      have hi : i ≤ 1 := of_decide_eq_true (by simpa [exLeaf, hs] using h)
      exact (eval_posLe_iff a 0 1).mpr ⟨i, hs, hi⟩

/-- The kit's explanation is entailed by the leaf semantics. -/
private theorem exClause_entailed : LearnedEntailed exLeaf [[posLe 0 1]] := by
  intro c hc a hleaf
  rw [List.mem_singleton] at hc
  rw [hc]
  exact ⟨posLe 0 1, List.mem_singleton_self _, exLeaf_posLe hleaf⟩

/-- A unit reason whose literal is its own normalized pivot has no
non-pivot literals: the recorded-falsifier obligation is vacuous. -/
theorem stepChronology_singleton_self {bs : BranchState leaf} {l : Literal}
    (hnorm : l = l.norm) : StepChronology bs l [l] := by
  intro q hq hne
  rw [List.mem_singleton] at hq
  subst hq
  exact absurd hnorm hne

/-- The kit's per-propagator evidence for the example list, derived from
the actual `run` equations. -/
private theorem exEvidence : PropagatorEvidence exLeaf exProps :=
  propagatorEvidence_unit [DomConstraint.leConstHi 0 1] (by
    intro dc hdc
    rw [List.mem_singleton] at hdc
    subst hdc
    rfl)

/-- The actual propagator run, as selected by `nextPruningEvent` on the
root state: `narrowHi` reads `[0,2]` from `{0,1,2}` and reports the
tightening `x ≤ 1` with the unit nogood as its explanation. -/
private theorem exEvent :
    nextPruningEvent exOriginal exProps exFrame [] =
      .implied (posLe 0 1) [posLe 0 1] true false := rfl

/-- The deduction selected by the event, with its narrowed frame. -/
private theorem exDeduction :
    ∃ d : ProductiveDeduction exLeaf exState,
      explainedDeduction exOriginal exProps exState = some d ∧
        d.literal = posLe 0 1 ∧ d.reason = [posLe 0 1] ∧
        d.frame = ([[.int 0, .int 1]], []) :=
  ⟨_, rfl, rfl, rfl, rfl⟩

/-- The fields of ANY selected deduction at the example state (the event
is the only possible one). -/
private theorem exDeduction_fields
    (d : ProductiveDeduction exLeaf exState)
    (hd : explainedDeduction exOriginal exProps exState = some d) :
    d.literal = posLe 0 1 ∧ d.reason = [posLe 0 1] ∧
      d.frame = ([[.int 0, .int 1]], []) := by
  obtain ⟨d₀, hd₀, hl₀, hr₀, hf₀⟩ := exDeduction
  have heq : d = d₀ := Option.some.inj (hd.symm.trans hd₀)
  subst heq
  exact ⟨hl₀, hr₀, hf₀⟩

/-- REPRESENTATIVE ACTUAL PROPAGATOR EXECUTION (PLAN A3 item 5): the
supported `leConstHi 0 1` propagator is registered; its run is selected
by `nextPruningEvent`; the kit's `run`-equation evidence gives the
normalized pivot membership; the branch-relative implication holds at
every represented leaf solution; and the recorded narrowing is reachable
and covers every represented leaf solution. Every premise is derived —
the `PropagatorEvidence` of the kit is produced by
`propagatorEvidence_unit` (see `exEvidence`). -/
example :
    nextPruningEvent exOriginal exProps exFrame []
        = .implied (posLe 0 1) [posLe 0 1] true false ∧
    (∃ d : ProductiveDeduction exLeaf exState,
      explainedDeduction exOriginal exProps exState = some d ∧
        d.literal = posLe 0 1 ∧ d.reason = [posLe 0 1] ∧
        d.frame = ([[.int 0, .int 1]], [])) ∧
    ((posLe 0 1).norm ∈ [posLe 0 1]) = True ∧
    (∀ a, exLeaf a = true → exState.Represents a →
      (posLe 0 1).norm.eval a = some true) ∧
    (∀ d : ProductiveDeduction exLeaf exState,
      explainedDeduction exOriginal exProps exState = some d →
      ReachableState exLeaf exOrig
          (narrowState exState d.frame d.literal d.reason d.learned) ∧
      (∀ a, exLeaf a = true → exState.Represents a →
        (narrowState exState d.frame d.literal d.reason d.learned).Represents
          a)) := by
  have hpivot := (unitEvidence_leConstHi 0 1).pivot_holds (frameState exFrame)
    (posLe 0 1) ({ clause := [posLe 0 1] } : Reason) rfl
  refine ⟨exEvent, exDeduction, hpivot, ?_, ?_⟩
  · intro a hleaf _
    rw [Literal.norm_eval]
    exact exLeaf_posLe hleaf
  · intro d hd
    obtain ⟨hl, hr, _⟩ := exDeduction_fields d hd
    have hentReason : LearnedEntailed exLeaf [d.reason] := by
      rw [hr]
      exact exClause_entailed
    have hentLearned := explainedDeduction_learned_entailed hd hentReason
    have hpivot' : (d.literal.norm ∈ d.reason) = True := by
      rw [hl, hr]
      exact hpivot
    have hin : d.literal.atom.slot
        < (fullDomains exState.frame).length := by
      rw [hl]
      decide
    have hchron : StepChronology exState d.literal d.reason := by
      rw [hl, hr]
      exact stepChronology_singleton_self (posLe_norm 0 1)
    refine ⟨explainedStep_narrow_reachable (reachable_init exLeaf exOrig)
        d.filtered (explainedDeduction_fresh hd) hin hentLearned hentReason
        hpivot' hchron, ?_⟩
    intro a hleaf hrep
    exact explainedStep_narrow_coverage d.filtered hentLearned a hleaf hrep
      (by rw [hl, Literal.norm_eval]; exact exLeaf_posLe hleaf)

/-- The database-unit state: the root state that has learned the entailed
unit clause `x ≤ 1` — the learning policy of the supported fragment. -/
private def exUnitState : BranchState exLeaf :=
  (BranchState.init exFrame : BranchState exLeaf).learnGlobal [posLe 0 1]

/-- The learned unit clause is in the state's database. -/
private theorem exUnit_mem : [posLe 0 1] ∈ exUnitState.learned := by
  simp [exUnitState, BranchState.learnGlobal, BranchState.init]

/-- The learned-unit state is reachable (A1's `reachable_learnGlobal`). -/
private theorem exUnitState_reachable :
    ReachableState exLeaf exOrig exUnitState :=
  reachable_learnGlobal (reachable_init exLeaf exOrig) exClause_entailed

/-- The database unit event: `scanDatabase` finds `x ≤ 1` unit in the
frame and reports it as a learned deduction. -/
private theorem exUnitEvent :
    nextPruningEvent exOriginal [] exUnitState.frame exUnitState.learned =
      .implied (posLe 0 1) [posLe 0 1] false true := rfl

/-- The learned unit clause is unit in the unit-state's frame. -/
private theorem exUnit_remaining :
    clauseRemaining exUnitState.frame [posLe 0 1] = [posLe 0 1] := by
  decide

/-- REPRESENTATIVE DATABASE-UNIT EXECUTION (PLAN A3 item 5): the learned
unit clause is selected by the database scan; the deduction it yields is
justified exactly by the route the concrete constructor uses for
database events (`clauseRemaining_singleton_implies` at the represented
solution, with `ReachableState.wf` carrying the clause's entailment),
while the pivot membership and the (vacuous) recorded-falsifier
obligation are the unit-shape facts of the supported fragment. -/
example :
    nextPruningEvent exOriginal [] exUnitState.frame exUnitState.learned
        = .implied (posLe 0 1) [posLe 0 1] false true ∧
    clauseRemaining exUnitState.frame [posLe 0 1] = [posLe 0 1] ∧
    (∃ d : ProductiveDeduction exLeaf exUnitState,
      explainedDeduction exOriginal [] exUnitState = some d ∧
        d.literal = posLe 0 1 ∧ d.reason = [posLe 0 1]) ∧
    ((posLe 0 1).norm ∈ [posLe 0 1]) = True ∧
    DomReasonRecorded exLeaf exUnitState (posLe 0 1) [posLe 0 1] ∧
    (∀ a, exLeaf a = true → exUnitState.Represents a →
      (posLe 0 1).norm.eval a = some true) := by
  refine ⟨exUnitEvent, exUnit_remaining, ⟨_, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · decide
  · intro q hq hne
    rw [List.mem_singleton] at hq
    subst hq
    exact absurd (posLe_norm 0 1).symm hne
  · intro a hleaf hrep
    have hent : Clause.SatisfiedBy [posLe 0 1] a :=
      hrep.2.2 [posLe 0 1] exUnit_mem
    have hlit := clauseRemaining_singleton_implies hrep.1 hent exUnit_remaining
    rwa [Literal.norm_eval]

/-! ### The `x ≠ y` acceptance example (PLAN A3 item 3) -/

/-- Two Boolean slots `{true, false}` — the `x ≠ y` example box. -/
private def xyOrig : List Domain :=
  [[.bool true, .bool false], [.bool true, .bool false]]

/-- The decided frame: slot 0 pinned to `false`, slot 1 still free. -/
private def xyFrame : BranchFrame :=
  ([[.bool true, .bool false]], [.bool false])

/-- The `x ≠ y` leaf semantics (non-Boolean readings are no solution). -/
private def xyLeaf : Assignment → Bool := fun a =>
  match (a[0]? : Option Value) with
  | some (.bool x) =>
      match (a[1]? : Option Value) with
      | some (.bool y) => x != y
      | _ => false
  | _ => false

/-- The globally entailed reason `¬(x = false) ∨ y = true`. -/
private def xyClause : Clause :=
  [({ atom := .boolEq 0 false, positive := false } : Literal),
   ({ atom := .boolEq 1 true, positive := true } : Literal)]

/-- The explained state: the decided child that learned the reason. -/
private def xyState : BranchState xyLeaf :=
  { (BranchState.init xyFrame : BranchState xyLeaf) with
    learned := [xyClause] }

/-- The learned reason is in the state's database. -/
private theorem xyClause_mem : xyClause ∈ xyState.learned := by
  simp [xyState, BranchState.init]

/-- The database-unit shape at the `x ≠ y` state: the learned reason is
unit in the decided frame and its remaining literal is `y = true`. -/
private theorem xy_clauseRemaining :
    clauseRemaining xyState.frame xyClause = [posBool 1 true] := by
  decide

/-- The reason's non-pivot literal `¬(x = false)` has NO recorded
falsifier at the `x ≠ y` state (the trail is empty): the state is
outside the supported unit-learned fragment, and the kit routes it to
local handling instead of claiming the pivot globally. -/
private theorem xy_not_recorded :
    ¬ DomReasonRecorded xyLeaf xyState (posBool 1 true) xyClause := by
  intro h
  have hmem : ({ atom := .boolEq 0 false, positive := false } : Literal) ∈
      xyClause := by decide
  have hne : ({ atom := .boolEq 0 false, positive := false } : Literal) ≠
      (posBool 1 true).norm := by decide
  obtain ⟨e, he, _⟩ :=
    List.mem_map.mp (h _ hmem hne)
  exact absurd he (by simp [xyState, BranchState.init])

/-- THE `x ≠ y` ACCEPTANCE EXAMPLE (PLAN A3 item 3; INTERFACES repair
§5(a)): the selected database-unit pivot `y = true` is NOT globally true
— the leaf solution `x = true, y = false` falsifies it — yet it IS
branch-relative true at every leaf solution the decided state
represents. The conclusion is derived exactly by the concrete
constructor's database-unit route (`clauseRemaining_singleton_implies`
at the represented solution); no global pivot-truth assumption is used
or available. The state's reason has no recorded falsifier for
`¬(x = false)`, which is why the disciplined fragment excludes it. -/
example :
    (∃ a : Assignment, xyLeaf a = true ∧
      (posBool 1 true).eval a = some false) ∧
    (∀ a, xyLeaf a = true → xyState.Represents a →
      (posBool 1 true).norm.eval a = some true) ∧
    ¬ DomReasonRecorded xyLeaf xyState (posBool 1 true) xyClause := by
  refine ⟨⟨([.bool true, .bool false] : Assignment), ?_, ?_⟩, ?_,
    xy_not_recorded⟩
  · decide
  · decide
  · intro a hleaf hrep
    have hent : Clause.SatisfiedBy xyClause a :=
      hrep.2.2 xyClause xyClause_mem
    have hlit := clauseRemaining_singleton_implies hrep.1 hent
      xy_clauseRemaining
    rwa [Literal.norm_eval]

/-- Unsupported constraints are EXPLICIT: `unitFamilyB` rejects the
disequality family (the `x ≠ y` shape), so the supported constructor is
not applicable and the local fallback governs. -/
example : unitFamilyB (DomConstraint.neSlot 0 1) = false := rfl

end LeanFzn.Solver.UIP

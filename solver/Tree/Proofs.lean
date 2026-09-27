/-
File: solver/Tree/Proofs.lean

Purpose:
  Discharges the foundational proof obligations for classical tree-search
  state: the initial state is well-formed, in-domain decisions preserve
  well-formedness, and deciding an in-domain value keeps exactly the
  represented assignments that match the decision.

  Statement strengthening (C0.1 audit finding): the forward direction of
  `decide_represents_iff` requires the decision value to be in the
  current slot domain. A decided state may carry a decision singleton
  `[v]` with `v` foreign to the original slot domain, and a fitting
  assignment then witnesses `v` in the narrowed domain only — nothing
  places `v` in the original domain. The scaffolded statement without
  this hypothesis is falsifiable; the theorem below states the fixpoint
  property in the form the search layer actually needs.

Dependencies:
  - solver.Tree.Invariants: tree-search logical contracts
    (`ProblemWellFormed`, `StateWellFormed`, `Represents`) and, through
    it, solver.Tree.Operations (`initialState`, `decide`,
    `Decision.Matches`).

DAG:
  solver.Tree.Invariants -> solver.Tree.Proofs -> tree adapters
-/

import solver.Tree.Invariants

namespace LeanFzn.Solver.Tree

open LeanFzn LeanFzn.Solver.Core

/-! ## Structural equations of `decide` -/

/-- The domains of a decided state are the old domains with the decision
    slot replaced by the decision singleton. -/
theorem decide_domains (state : State) (decision : Decision) :
    (decide state decision).domains
      = state.domains.set decision.slot [decision.value] := rfl

/-- The NoGoods of a decided state are unchanged. -/
theorem decide_nogoods (state : State) (decision : Decision) :
    (decide state decision).nogoods = state.nogoods := rfl

/-- A decided state excludes exactly what the old state excludes. -/
theorem decide_excludes_iff (state : State) (decision : Decision)
    (a : Assignment) :
    (decide state decision).Excludes a ↔ state.Excludes a := by
  rw [State.Excludes, decide_nogoods, State.Excludes]

/-! ## The initial state -/

/-- The initial state is aligned with every structurally well-formed
    problem: its domains literally are the problem domains. -/
theorem initialState_wellFormed {problem : Problem Constraint Objective}
    (hproblem : ProblemWellFormed problem) :
    StateWellFormed problem (initialState problem) := by
  have h1 : (initialState problem).domains = problem.domains := rfl
  have h2 : (initialState problem).domains.length = problem.domains.length :=
    h1 ▸ rfl
  refine ⟨h2, ?_⟩
  intro slot value hmem
  rw [h1] at hmem
  exact hmem

/-! ## Decisions preserve well-formedness -/

/-- The singleton membership lemma for the narrowed decision slot. -/
private theorem mem_of_getD_set_self {doms : List Domain}
    {slot : Nat} {v value : Value}
    (hslot : slot < doms.length)
    (hmem : value ∈ (doms.set slot [v]).getD slot []) :
    value = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hslot] at hmem
  exact List.mem_singleton.mp hmem

/-- A well-formed in-domain decision preserves structural state validity. -/
theorem decide_wellFormed {problem : Problem Constraint Objective}
    {state : State} (hstate : StateWellFormed problem state)
    {decision : Decision}
    (hslot : decision.slot < state.domains.length)
    (hvalue : decision.value ∈ state.domains.getD decision.slot []) :
    StateWellFormed problem (decide state decision) := by
  obtain ⟨hlen, hsub⟩ := hstate
  have hvalue' := hsub decision.slot decision.value hvalue
  have hlen' : (decide state decision).domains.length
      = problem.domains.length := by
    rw [decide_domains, List.length_set]
    exact hlen
  refine ⟨hlen', ?_⟩
  intro slot value hmem
  show value ∈ problem.domains.getD slot []
  rw [decide_domains, List.getD_eq_getElem?_getD] at hmem
  by_cases hs : slot = decision.slot
  · subst hs
    have hve := mem_of_getD_set_self (doms := state.domains)
      (slot := decision.slot) (by omega) hmem
    subst hve
    exact hvalue'
  · rw [List.getElem?_set_ne (by omega)] at hmem
    exact hsub slot value hmem

/-! ## Decisions and represented assignments -/

/-- Helper: a fitting assignment of a decided state matches the
    decision, because the narrowed slot is the decision singleton. -/
theorem decide_fits_match {state : State} {decision : Decision}
    (hslot : decision.slot < state.domains.length) {a : Assignment}
    (hfitn : a.Fits (decide state decision).domains) :
    decision.Matches a := by
  have hlen : a.length = (decide state decision).domains.length := hfitn.1
  have hsle : decision.slot < (decide state decision).domains.length := by
    rw [decide_domains, List.length_set]
    exact hslot
  have hale : decision.slot < a.length := by
    rw [hlen]
    exact hsle
  have hq : a[decision.slot]? = some a[decision.slot] :=
    List.getElem?_eq_getElem hale
  have hmem : a[decision.slot] ∈
      (decide state decision).domains.getD decision.slot [] :=
    hfitn.2 decision.slot a[decision.slot] hq
  have hmem' : a[decision.slot] ∈ (state.domains.set decision.slot
      [decision.value]).getD decision.slot [] := by
    rw [← decide_domains]
    exact hmem
  have hve := mem_of_getD_set_self (doms := state.domains)
    (slot := decision.slot) (by omega) hmem'
  show decision.Matches a
  unfold Decision.Matches
  rw [hq, hve]

/-- Helper: a fitting assignment of a decided state fits the original
    domains, provided the decision is in-domain. -/
theorem fits_decide_of_fits {state : State} {decision : Decision}
    (hslot : decision.slot < state.domains.length)
    (hvalue : decision.value ∈ state.domains.getD decision.slot [])
    {a : Assignment} (hfitn : a.Fits (decide state decision).domains) :
    a.Fits state.domains := by
  have hlen : a.length = (decide state decision).domains.length := hfitn.1
  have hlen' : a.length = state.domains.length := by
    rw [hlen, decide_domains, List.length_set]
  refine ⟨hlen', ?_⟩
  intro slot value hmem
  -- `hmem : a[slot]? = some value`; use Fits to witness the value in
  -- the narrowed domain, then transfer to the original domain.
  have hnarrow : value ∈ (decide state decision).domains.getD slot [] :=
    hfitn.2 slot value hmem
  rw [decide_domains, List.getD_eq_getElem?_getD] at hnarrow
  show value ∈ state.domains.getD slot []
  rw [List.getD_eq_getElem?_getD]
  by_cases hs : slot = decision.slot
  · subst hs
    have hve := mem_of_getD_set_self (doms := state.domains)
      (slot := decision.slot) (by omega) hnarrow
    subst hve
    exact hvalue
  · rw [List.getElem?_set_ne (by omega)] at hnarrow
    exact hnarrow

/-- Deciding an in-domain value keeps exactly the previously represented
    assignments that match that decision. -/
theorem decide_represents_iff {state : State} {decision : Decision}
    (hslot : decision.slot < state.domains.length)
    (hvalue : decision.value ∈ state.domains.getD decision.slot [])
    {assignment : Assignment} :
    Represents (decide state decision) assignment ↔
      Represents state assignment ∧ decision.Matches assignment := by
  constructor
  · intro hrep
    obtain ⟨hfitn, hexcl⟩ := hrep
    have hmatch := decide_fits_match hslot hfitn
    have hfits : assignment.Fits state.domains :=
      fits_decide_of_fits hslot hvalue hfitn
    have hexcl' : ¬ state.Excludes assignment := fun h =>
      hexcl ((decide_excludes_iff state decision assignment).mpr h)
    exact ⟨⟨hfits, hexcl'⟩, hmatch⟩
  · rintro ⟨⟨hfitO, hexclO⟩, hmatch⟩
    -- `hfitO : assignment.Fits state.domains`, `hexclO : ¬Excludes`
    obtain ⟨hlen, hmem⟩ := hfitO
    have hlen' : assignment.length = (decide state decision).domains.length := by
      rw [decide_domains, List.length_set]
      exact hlen
    have hexclN : ¬ (decide state decision).Excludes assignment := fun h =>
      hexclO ((decide_excludes_iff state decision assignment).mp h)
    refine ⟨⟨hlen', ?_⟩, hexclN⟩
    intro slot value hval
    show value ∈ (decide state decision).domains.getD slot []
    -- membership flows from the original domain and the match
    have horig : value ∈ state.domains.getD slot [] := hmem slot value hval
    rw [decide_domains, List.getD_eq_getElem?_getD]
    rw [List.getD_eq_getElem?_getD] at horig
    by_cases hs : slot = decision.slot
    · subst hs
      rw [List.getElem?_set_self (by omega)]
      -- value = decision.value via the match
      have hq2 : assignment[decision.slot]? = some decision.value := hmatch
      rw [hval] at hq2
      have hve : value = decision.value := by injection hq2
      rw [hve]
      exact List.Mem.head _
    · rw [List.getElem?_set_ne (by omega)]
      exact horig

end LeanFzn.Solver.Tree

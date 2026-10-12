/-
File: LeanFzn/Solver/Propagation/Proofs/Fam/AllDiff.lean

Purpose:
  The LCG propagator and proof package for the `allDiff` family
  (`all_different` over a sub-list of slots), as a CONFLICT-ONLY
  propagator. `propAllDiffLCG` mirrors the domain-level `propAllDiff`
  (LeanFzn.Solver/Propagators.lean): `.contradiction` when the number of
  in-range slots exceeds the number of distinct union values — the
  pigeonhole count — reported as the EMPTY conflict clause
  `.conflict []` (`propNe`'s discipline, LeanFzn/Solver/UIP/Propagate.lean);
  `.stable` otherwise. No `.implied` emissions: value-removal
  deductions would need L0.6 literals (out of scope).

  Why conflict-only is SOUND and USEFUL: the empty conflict clause
  routes to the engine's fallback-nogood learning arm
  (LeanFzn/Solver/UIP/Engine.lean's `match st1.conflict with | some [] =>`),
  and the certified machinery of PLAN §5 items 4-5
  (`fallbackNogood_entailed` + `propagateLoop_conflict_nofit_empty`,
  Proofs/Fallback.lean + Proofs/FallbackFit.lean) handles empty
  conflicts from propagators; the pigeonhole exclusion proven here is
  exactly the fits-exclusion (`hfitexcl`) that front door needs.

  Definitional note: `propAllDiff`'s counting helpers
  (`inRangeSlots`, `distinctUnionVals`) are PRIVATE to
  LeanFzn.Solver.Propagation.DomainConstraints, so the counting condition is reached through
  `propAllDiff` itself: `propAllDiffLCG` matches on
  `propAllDiff is st.domains`, which keeps the correspondence with the
  domain-level propagator DEFINITIONAL (its `.contradiction` arm is
  exactly the pigeonhole count, its `.narrowed` arm the stable case).

The package (mirroring the sibling families, Proofs/Propagators.lean's
`propNe_safe` for the empty-conflict discipline and Fam/Bool.lean's
standalone registration for the packaging):

  * `propAllDiffLCG` — the propagator (empty-clause conflict / stable);
  * `propAllDiffLCG_never_implied` — the emission inversion for
    `.implied` (vacuous: the propagator never implies);
  * `propAllDiffLCG_conflict_clause_empty` — every conflict clause is
    `[]` (the cc ≠ []-gated assemblies refute allDiff with it, the
    `propNe_conflict_clause_empty` treatment of Reason.lean);
  * `propAllDiffLCG_conflict_nofit` — THE PIGEONHOLE EXCLUSION: no
    assignment fitting the state's domains and satisfying `allDiff is`
    exists when the conflict fires (via `propAllDiff_preserves`'s
    `contradicts` conjunct + `fits_mem_allAssigns`, the
    Fits-to-allAssigns bridge);
  * `propAllDiffLCG_safe` — the three-conjunct safe triple
    (implied-literal truth VACUOUS / conflict exclusion / conflict
    entitlement via the VACUITY mechanism: the exclusion makes the
    entitlement's hypotheses contradictory, so the empty clause's
    missing literal is irrelevant — ex falso, exactly how
    `propNe_safe`'s third conjunct is discharged);
  * `propAllDiffLCG_entitled` — the state-free conflict entitlement in
    the `propagatorOf_leSlot_entitled` shape (SolvedBy-derived fits)
    that `propagatorsOfProved_entitled`'s neSlot arm pattern consumes;
  * `propAllDiffLCG_fitexcl` — the problem-level fits-exclusion in the
    `hfitexcl` shape `propagatorsOfProved_fitexcl` (FallbackFit.lean)
    consumes per family;
  * `propAllDiffLCG_reason_valid` — the vacuous reason-validity (never
    implies; the `propNe_reason_valid` treatment);
  * `propagatorOfProvedBA` + `propagatorOfProvedBA_mem` +
    `propagatorOfProvedBA_run` — the standalone registration of
    exactly this family (in the integrated registration
    `propagatorOfProved` these are arms).

Dependencies:
  - LeanFzn.Solver.Propagation.Proofs.ConstFamilies: the sibling-family module
    conventions (transitively Theory — SolvedBy, ProblemSolution;
    Propagate — State, PropagationResult, the DomConstraint layer;
    Invariants — Reason.Valid).
  - LeanFzn.Compiler.Proofs.Compile: `fits_mem_allAssigns`, the
    Fits-to-allAssigns bridge the pigeonhole reuse needs. No import
    cycle: the Direct proof layer depends only on the core/compile
    stack, never on LeanFzn.Solver.*

DAG:
  LeanFzn.Solver.UIP.Proofs.ConstFamilies + LeanFzn.Compiler.Proofs.Compile
    -> LeanFzn.Solver.UIP.Proofs.Fam.AllDiff (this module; a leaf)

Verification: `timeout 700 env LEAN_NUM_THREADS=4 lake env lean
LeanFzn/Solver/UIP/Proofs/Fam/AllDiff.lean` — zero errors.
-/

import LeanFzn.Solver.Propagation.Proofs.ConstFamilies
import LeanFzn.Compiler.Proofs.Compile
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Reference


open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Reference

/-! ## The propagator

Conflict-only: the pigeonhole count of the domain-level `propAllDiff`
(`.contradiction` when #(in-range slots) > #(distinct union values))
becomes the EMPTY conflict clause (the engine's fallback-nogood arm
consumes it); everything else is `.stable`. No `.implied` emissions
(value-removal deductions would need L0.6 literals). -/

/-- **The all-different propagator, LCG version** (`all_different`
style over a sub-list of slots), conflict-only: the domain-level
`propAllDiff`'s pigeonhole contradiction reported as the empty
conflict clause; `.stable` otherwise. The counting lives inside
`propAllDiff` (its helpers are private there), so the match keeps the
correspondence definitional. -/
def propAllDiffLCG (st : State) (is : List Nat) : PropagationResult :=
  match propAllDiff is st.domains with
  | .contradiction => .conflict []
  | .narrowed _ => .stable

/-! ## The emission inversions -/

/-- `propAllDiffLCG` never reports `.implied` (only the pigeonhole
conflict or `.stable`). -/
theorem propAllDiffLCG_never_implied {st : State} {is : List Nat}
    {l : Literal} {r : Reason}
    (hrun : propAllDiffLCG st is = .implied l r) : False := by
  unfold propAllDiffLCG at hrun
  split at hrun
  · exact absurd hrun (by simp)
  · exact absurd hrun (by simp)

/-- The conflict-report inversion: a conflict means the domain-level
    pigeonhole fired, and the reported clause is EMPTY. -/
private theorem propAllDiffLCG_conflict_inv {st : State} {is : List Nat}
    {c : Clause} (hrun : propAllDiffLCG st is = .conflict c) :
    propAllDiff is st.domains = PropResult.contradiction ∧ c = [] := by
  unfold propAllDiffLCG at hrun
  split at hrun
  · next h => exact ⟨h, (PropagationResult.conflict.inj hrun).symm⟩
  · exact absurd hrun (by simp)

/-- `propAllDiffLCG`'s conflict report is the empty clause (so its
    nonempty-clause entitlement is vacuous — and its unconstrained
    form is FALSE, which is why the cc ≠ []-gated assemblies REFUTE the
    allDiff arm with this lemma, the `propNe_conflict_clause_empty`
    treatment). -/
theorem propAllDiffLCG_conflict_clause_empty {st : State} {is : List Nat}
    {c : Clause} (hrun : propAllDiffLCG st is = .conflict c) : c = [] :=
  (propAllDiffLCG_conflict_inv hrun).2

/-! ## The pigeonhole exclusion

The heart of the package: when the conflict fires, NO assignment
fitting the state's domains satisfies `allDiff is`. This is
`propAllDiff_preserves`'s `contradicts` conjunct (no assignment of the
domains makes the slots pairwise distinct — via `allDiff_pigeonhole`)
instantiated at `st.domains`, with `fits_mem_allAssigns` bridging
`Fits` to the `allAssigns` membership the preservation contract is
stated over. -/

/-- **The pigeonhole fits-exclusion**: a conflict report of
    `propAllDiffLCG` excludes every assignment that fits the state's
    domains and satisfies `allDiff is`. -/
theorem propAllDiffLCG_conflict_nofit {st : State} {is : List Nat}
    {c : Clause}
    (hrun : propAllDiffLCG st is = .conflict c)
    (a : Assignment) (hfit : Core.Assignment.Fits st.domains a)
    (hcons : (DomConstraint.allDiff is).SatisfiedBy a) : False := by
  obtain ⟨hpd, _hc⟩ := propAllDiffLCG_conflict_inv hrun
  -- the fitting assignment is in the domain-level candidate space
  have hmem : a ∈ allAssigns st.domains :=
    LeanFzn.Compiler.fits_mem_allAssigns st.domains a hfit
  -- the domain-level preservation contract's contradiction arm
  exact (propAllDiff_preserves is).contradicts hpd a hmem hcons

/-! ## The safe triple

The three-conjunct discipline of `propNe_safe` (the empty-conflict
template): implied-literal truth (VACUOUS — never implies), conflict
exclusion (the pigeonhole), and conflict entitlement — the latter via
the VACUITY mechanism: the exclusion makes the entitlement's
hypotheses (`Fits` + `SatisfiedBy`) contradictory, so the empty
clause's missing true literal is supplied by ex falso. -/

/-- `propAllDiffLCG` soundness over `allDiff is`: implied literals
    never occur, the pigeonhole conflict excludes every fitting
    satisfying assignment, and the (empty) conflict clause carries no
    entitlement obligation beyond the exclusion itself. -/
theorem propAllDiffLCG_safe (st : State) (is : List Nat) :
    (∀ l r, propAllDiffLCG st is = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.allDiff is).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ c, propAllDiffLCG st is = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.allDiff is).SatisfiedBy a → False) ∧
    (∀ c, propAllDiffLCG st is = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.allDiff is).SatisfiedBy a →
        ∃ l ∈ c, l.eval a = some true) := by
  refine ⟨?_, ?_, ?_⟩
  · -- implied: propAllDiffLCG never returns .implied
    intro l r hrun a hfit hcons
    exact (propAllDiffLCG_never_implied hrun).elim
  · -- conflict soundness: the pigeonhole exclusion
    intro c hrun a hfit hcons
    exact propAllDiffLCG_conflict_nofit hrun a hfit hcons
  · -- entitlement: the exclusion makes the hypotheses contradictory
    intro c hrun a hfit hcons
    exact (propAllDiffLCG_conflict_nofit hrun a hfit hcons).elim

/-! ## State-free conflict entitlement

The `propagatorOf_leSlot_entitled` / neSlot-arm shape: every conflict
clause carries a true literal at every internal solution that (via
`SolvedBy`) fits the state's domains — here by the vacuity mechanism
above (a solution both fitting `st.domains` and satisfying the
problem's `allDiff is` would contradict the pigeonhole). -/

/-- The per-family entitlement: for an `allDiff is` constraint in the
    problem, the propagator's (empty) conflict clause carries a true
    literal at every internal problem solution that fits the state's
    domains — the shape `propagatorsOfProved_entitled`'s neSlot arm
    consumes (`(hsol a ha).1` supplying the fits). -/
theorem propAllDiffLCG_entitled
    {problem : Problem DomConstraint Unit}
    {st : State} {is : List Nat} {c : Clause}
    (hprob : DomConstraint.allDiff is ∈ problem.constraints)
    (hrun : propAllDiffLCG st is = .conflict c)
    (hsol : SolvedBy problem DomConstraint.SatisfiedBy st)
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ c, l.eval a = some true :=
  (propAllDiffLCG_safe st is).2.2 c hrun a (hsol a ha).1 (ha.2 _ hprob)

/-! ## The fits-exclusion bridge (the `hfitexcl` shape)

The problem-level form FallbackFit.lean's
`propagatorsOfProved_fitexcl` assembly dispatches to per family: a
conflict report excludes every assignment fitting the state's domains
from the internal problem solutions (the assignment would satisfy the
problem's own `allDiff is`, contradicting the pigeonhole). No
`DomainCoherent` premise is needed — the exclusion is state-local. -/

/-- THE allDiff FITS-EXCLUSION: at every state, a conflict reported by
    `propAllDiffLCG` excludes every assignment fitting the state's
    domains from the internal problem solutions. -/
theorem propAllDiffLCG_fitexcl {problem : Problem DomConstraint Unit}
    {is : List Nat} {c : Clause}
    (hprob : DomConstraint.allDiff is ∈ problem.constraints)
    (st : State)
    (hrun : propAllDiffLCG st is = .conflict c)
    (a : Assignment) (hfit : Core.Assignment.Fits st.domains a) :
    ¬ ProblemSolution problem DomConstraint.SatisfiedBy a := by
  intro ha
  exact propAllDiffLCG_conflict_nofit hrun a hfit (ha.2 _ hprob)

/-! ## Reason validity (vacuous)

The propagator never implies, so the `ReasonSafeUniv` obligation is
discharged by the emission inversion (the `propNe_reason_valid`
treatment). -/

/-- The state-free reason-validity lemma for the `allDiff` family:
    vacuous (the propagator never implies). -/
theorem propAllDiffLCG_reason_valid
    {problem : Problem DomConstraint Unit}
    {st : State} {is : List Nat} {l : Literal} {r : Reason}
    (hrun : propAllDiffLCG st is = .implied l r) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l ∧
      (∀ q ∈ r.clause, q = q.norm) :=
  absurd hrun propAllDiffLCG_never_implied

/-! ## The standalone registration

A self-contained registration of exactly this family, in the shape of
Propagators.lean's `propagatorOfProved` packaging (where the allDiff
arm would be `| .allDiff is => some { watches := [], run := ... }`). -/

/-- The propagator of this module's family: `allDiff is`. -/
def propagatorOfProvedBA : DomConstraint → Option Propagator
  | .allDiff is =>
      some { watches := [], run := fun st => propAllDiffLCG st is }
  | _ => none

/-- Membership inversion for the registration (the
    `propagatorsOfProved_mem` shape). -/
theorem propagatorOfProvedBA_mem {dcs : List DomConstraint}
    {p : Propagator} (hp : p ∈ dcs.filterMap propagatorOfProvedBA) :
    ∃ dc ∈ dcs, propagatorOfProvedBA dc = some p := by
  induction dcs with
  | nil => cases hp
  | cons dc rest ih =>
      cases hpdc : propagatorOfProvedBA dc with
      | none =>
          simp only [List.filterMap_cons, hpdc] at hp
          obtain ⟨dc2, hdc2mem, hdc2⟩ := ih hp
          exact ⟨dc2, List.mem_cons_of_mem _ hdc2mem, hdc2⟩
      | some p0 =>
          simp only [List.filterMap_cons, hpdc] at hp
          rcases List.mem_cons.mp hp with hp2 | hp2
          · rw [hp2]
            exact ⟨dc, List.mem_cons_self, hpdc⟩
          · obtain ⟨dc2, hdc2mem, hdc2⟩ := ih hp2
            exact ⟨dc2, List.mem_cons_of_mem _ hdc2mem, hdc2⟩

/-- Emission inversion for the registration (the
    `propagatorOfProved_run` shape): a run of a BA-registered
    propagator reduces to this family's propagator at the same
    parameters. -/
theorem propagatorOfProvedBA_run {dc : DomConstraint} {p : Propagator}
    {st : State} {res : PropagationResult}
    (hprop : propagatorOfProvedBA dc = some p)
    (hrun : p.run st = res) :
    ∃ is, dc = .allDiff is ∧ propAllDiffLCG st is = res := by
  match hdc : dc with
  | .allDiff is =>
      simp only [propagatorOfProvedBA] at hprop
      refine ⟨is, rfl, ?_⟩
      rw [(Option.some.inj hprop).symm] at hrun
      exact hrun
  | .eqSlot i j
  | .neSlot i j | .leSlot i j | .constEq i v
  | .plusSlot i j k
  | .leConstHi i c | .leConstLo i c
  | .ltSlot i j | .ltConstHi i c | .ltConstLo i c
  | .timesSlot i j k | .minSlot i j k | .maxSlot i j k | .absSlot i k2
  | .linEq coeffs is b | .linLe coeffs is b
  | .boolNotSlot i j | .boolAndSlot i j k | .boolOrSlot i j k =>
      exfalso
      simp only [propagatorOfProvedBA] at hprop
      exact absurd hprop (by intro hc; cases hc)

/-! ## Axiom checks -/

#print axioms propAllDiffLCG
#print axioms propAllDiffLCG_never_implied
#print axioms propAllDiffLCG_conflict_clause_empty
#print axioms propAllDiffLCG_conflict_nofit
#print axioms propAllDiffLCG_safe
#print axioms propAllDiffLCG_entitled
#print axioms propAllDiffLCG_fitexcl
#print axioms propAllDiffLCG_reason_valid
#print axioms propagatorOfProvedBA
#print axioms propagatorOfProvedBA_mem
#print axioms propagatorOfProvedBA_run

/-! ## Smoke tests

Concrete small states exercising both emission shapes (kernel
reduction by `rfl`; no `native_decide`). -/

/-- The test state: empty trail and databases. -/
private def allDiffTestState (doms : List (List Value)) : State where
  domains := doms
  trail := []
  decisionLevel := 0
  clauses := []
  learned := []
  queue := []
  conflict := none

/-- Smoke: the pigeonhole FIRES — three in-range slots over a union
of two distinct values (3 > 2) — reported as the empty conflict. -/
theorem propAllDiffLCG_smoke_conflict :
    propAllDiffLCG
        (allDiffTestState [[.int 1, .int 2], [.int 1, .int 2],
          [.int 1, .int 2]]) [0, 1, 2] =
      .conflict [] := by rfl

/-- Smoke: three in-range slots over a union of three distinct values
(3 > 3 is false) — the propagator stays stable. -/
theorem propAllDiffLCG_smoke_stable :
    propAllDiffLCG
        (allDiffTestState [[.int 1, .int 2, .int 3], [.int 1, .int 2],
          [.int 2, .int 3]]) [0, 1, 2] =
      .stable := by rfl

#print axioms propAllDiffLCG_smoke_conflict
#print axioms propAllDiffLCG_smoke_stable

end LeanFzn.Solver.Propagation

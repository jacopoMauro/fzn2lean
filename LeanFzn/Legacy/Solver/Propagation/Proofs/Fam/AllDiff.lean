/-
File: LeanFzn/Solver/Propagation/Proofs/Fam/AllDiff.lean

Purpose:
  The LCG propagator and proof package for the `allDiff` family
  (`all_different` over a sub-list of slots). `propAllDiffLCG` emits two
  shapes (PLAN L8):

  * the PIGEONHOLE CONFLICT, mirroring the domain-level `propAllDiff`
    (LeanFzn/Solver/Propagation/DomainConstraints.lean): `.contradiction`
    when the number of slots of `is` with a nonempty current domain exceeds
    the number of distinct union values - the pigeonhole count - reported as
    the EXPLAINED Hall clause
    `hallClause` (per such slot, "this slot takes a value outside its
    current domain", written with `s ≤ lo-1`, `s > hi` and `s = hole`
    literals over the slot's integer view);
  * VALUE ELIMINATION for a fixed slot: when slot `i` of `is` is fixed to
    a raw integer `c` (its current domain is exactly `[.int c]`), the
    value `c` is removed from every OTHER slot `j` of `is` whose domain
    still holds `.int c`, is int-viewed, and satisfies the `domNeGate`
    raw-correspondence (every value of it viewing `c` IS the raw `.int
    c`) - reported as the implied literal `x_j ≠ c` with the
    `propNe`-shaped reason `allDiffElimClause i j c` (the pivot plus the
    two adjacent bounds of the fixed slot and the two Boolean-shape
    disjuncts that certify the mixed-sort case).

  The clause is read from the state's current domains alone (a propagator
  sees no original box), so it generalises the hull of each slot's CURRENT
  domain.  Slots of `is` whose current domain is empty are dropped by
  `inRangeSlots` (they read no value in any assignment); a nonempty slot
  whose hull is wider than `hallHullCap` or not int-viewed makes the report
  fall back to the empty (local) clause.

  Why the explained clause is SOUND and USEFUL: it is entailed by the
  constraint at every assignment faithful to the domains it was read from
  (`propAllDiffLCG_conflict_entailed`: if no literal were true, every slot
  would read a value of its own domain, and the pigeonhole bound
  `allDiff_pigeonhole_of_mem` would contradict the count) and every literal
  is false at every assignment fitting those domains
  (`propAllDiffLCG_conflict_falsified`, the evidence form of the Boolean
  families' `falsifier_pin`), so it feeds the conflict analyzer.

The package (mirroring the sibling families, Proofs/Propagators.lean's
`propNe_safe` for the empty-conflict discipline and Fam/Bool.lean's
standalone registration for the packaging):

  * `propAllDiffLCG` — the propagator (pigeonhole conflict, value
    elimination, or stable);
  * `propAllDiffLCG_implied_inv` — the emission inversion for
    `.implied`: the emitted literal is `posNe j c` with the reason
    `allDiffElimClause i j c`, and the elimination scan selected the pair
    (`allDiffElimFirst`);
  * `propAllDiffLCG_conflict_inv` — every conflict clause is
    `hallClause` of the state's domains;
  * `propAllDiffLCG_conflict_falsified` / `propAllDiffLCG_conflict_entailed`
    — the Hall clause is false at every fitting assignment and true at
    every faithful `allDiff` solution (when non-empty);
  * `propAllDiffLCG_conflict_nofit` — THE PIGEONHOLE EXCLUSION: no
    assignment fitting the state's domains and satisfying `allDiff is`
    exists when the conflict fires (via `propAllDiff_preserves`'s
    `contradicts` conjunct + `fits_mem_allAssigns`, the
    Fits-to-allAssigns bridge);
  * `allDiff_elim_true_of_fits` / `allDiff_nogood_true` — the two
    semantic readings of the elimination: the implied literal is TRUE at
    every fitting solution of the pairwise-distinctness, and the reason
    clause is TRUE at every satisfying read pair with views (the
    state-free `Reason.Valid` shape);
  * `propAllDiffLCG_safe` — the three-conjunct safe triple (implied
    literals true at fitting solutions of the constraint / conflict
    exclusion / conflict entitlement via the VACUITY mechanism: the
    exclusion makes the entitlement's hypotheses contradictory, so the
    empty clause's missing literal is irrelevant — ex falso, exactly how
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

Two emission shapes. The pigeonhole count of the domain-level `propAllDiff`
(`.contradiction` when #(slots of `is` with a nonempty current domain) >
#(distinct union values)) becomes
the EXPLAINED conflict `hallClause`: for every such slot, the disjunction
"this slot's value lies outside its current domain" written with
order/value-removal literals over the slot's integer view (below the domain's
minimum, above its maximum, or equal to one of its holes). Otherwise, when
some slot of `is` is FIXED to a raw integer `c` (its current domain is
exactly `[.int c]`), the first eligible other slot `j` of `is` reports the
implied value removal `x_j ≠ c`. Otherwise `.stable`. -/

/-- Cap on the width of a slot's hull for which holes are enumerated; wider
slots fall back to the empty (local) conflict clause. -/
def hallHullCap : Nat := 1024

/-- The "slot `s` takes a value outside `d`" literals of one in-range slot:
`s ≤ lo-1`, `s > hi`, and `s = h` for every hole `h` of `d` strictly between
its extrema. `none` when `d` is empty, has a value without an integer view,
or has a hull wider than `hallHullCap`. Every literal is in normal form and
is FALSE at every value of `d`. -/
def slotHall (s : Nat) (d : Domain) : Option Clause :=
  match (Dom.enum d).filterMap Value.intView with
  | [] => none
  | v0 :: vs =>
    if (v0 :: vs).length != (Dom.enum d).length then none else
    let lo := vs.foldl min v0
    let hi := vs.foldl max v0
    if (hi - lo + 1).toNat > hallHullCap then none else
    let holes := ((List.range (hi - lo + 1).toNat).map
      (fun k : Nat => lo + (k : Int))).filter (fun h => !((v0 :: vs).contains h))
    some (posLe s (lo - 1) :: negLe s hi :: holes.map (negNe s))

/-- The concatenated per-slot literals over a slot list (`none` if some slot
has none). -/
def hallClauses (doms : List Domain) : List Nat → Option Clause
  | [] => some []
  | s :: ss =>
      match slotHall s (doms.getD s Dom.empty), hallClauses doms ss with
      | some c1, some c2 => some (c1 ++ c2)
      | _, _ => none

/-- **The Hall / pigeonhole conflict clause** of an `all_different` over the
slots `is`: some slot of `is` with a nonempty current domain takes a value
outside its current domain.
It is entailed by the constraint (`propAllDiffLCG_conflict_entailed`: the
slots' domains would otherwise hold a pairwise-distinct value per slot) and
falsified by the domains it was read from
(`propAllDiffLCG_conflict_falsified`). The empty clause is reported only when
a slot's hull is unusable (`slotHall = none`). -/
def hallClause (doms : List Domain) (is : List Nat) : Clause :=
  match hallClauses doms (inRangeSlots (doms.map Dom.enum) is) with
  | some c => c
  | none => []

/-- **The reason clause of a value-elimination emission** (the
`propNe`-shaped value-removal nogood): the pivot `x_j ≠ c` plus the four
causes pinning `x_i = c` — the two adjacent bounds of the fixed slot
(`x_i ≤ c−1`, `x_i > c`, both false at a slot whose domain is `[.int c]`)
and the two Boolean-shape disjuncts `x_i = B` / `x_j = B` (`B` the Boolean
viewing to `c`, harmless duplicates of the second bound when `c ∉ {0, 1}`),
which certify the clause at mixed-sort reads. -/
def allDiffElimClause (i j : Nat) (c : Int) : Clause :=
  [posNe j c, posLe i (c - 1), negLe i c, neBoolLit i i c, neBoolLit i j c]

/-- The elimination gate of the pair (fixed slot `i` with value `c`, target
slot `j`): `j ≠ i` is in range, its domain is int-viewed (so a fitting read
there HAS an integer view), every value of it viewing `c` is the raw
`.int c` (the `domNeGate` raw-correspondence — the value being removed is
exactly the one the fixed slot reads), and it still contains `.int c` (so
the removal is productive). -/
def allDiffElimB (doms : List Domain) (i j : Nat) (c : Int) : Bool :=
  decide (j ≠ i) && decide (j < doms.length) &&
    (Dom.enum (doms.getD j Dom.empty)).all (fun v => v.intView != none) &&
    domNeGate (.int c) c (Dom.enum (doms.getD j Dom.empty)) &&
    valueMemB (.int c) (Dom.enum (doms.getD j Dom.empty))

/-- The first elimination target of the fixed slot `i` (fixed to `c`): the
first slot `j` of `is` passing `allDiffElimB doms i j c`. -/
def allDiffElimTarget (doms : List Domain) (is : List Nat) (i : Nat)
    (c : Int) : Option Nat :=
  match is with
  | [] => none
  | j :: js =>
      if allDiffElimB doms i j c then some j
      else allDiffElimTarget doms js i c

/-- The first value elimination of an `all_different` over `is`: the first
slot `i` of `is` whose current (raw) domain is the integer singleton
`[.int c]` and which has an eligible target slot. -/
def allDiffElimFirst (doms : List Domain) (is : List Nat) :
    Option (Nat × Nat × Int) :=
  match is with
  | [] => none
  | i :: is' =>
      match Dom.enum (doms.getD i Dom.empty) with
      | [.int c] =>
          match allDiffElimTarget doms is i c with
          | some j => some (i, j, c)
          | none => allDiffElimFirst doms is'
      | _ => allDiffElimFirst doms is'

/-- **The all-different propagator, LCG version** (`all_different`
style over a sub-list of slots): the domain-level `propAllDiff`'s
pigeonhole contradiction reported as the explained `hallClause`; otherwise
the first value elimination of a fixed slot (`allDiffElimFirst`) reported
as the implied value removal `x_j ≠ c`; `.stable` otherwise. The counting
lives inside `propAllDiff`, so the match keeps the correspondence
definitional. -/
def propAllDiffLCG (st : State) (is : List Nat) : PropagationResult :=
  match propAllDiff is (st.domains.map Dom.enum) with
  | .contradiction => .conflict (hallClause st.domains is)
  | .narrowed _ =>
      match allDiffElimFirst st.domains is with
      | some (i, j, c) =>
          .implied (posNe j c) { clause := allDiffElimClause i j c }
      | none => .stable

/-! ## The elimination gate: specification of the scan -/

/-- The five components of the elimination gate. -/
theorem allDiffElimB_eq {doms : List Domain} {i j : Nat} {c : Int}
    (h : allDiffElimB doms i j c = true) :
    j ≠ i ∧ j < doms.length ∧
      (Dom.enum (doms.getD j Dom.empty)).all (fun v => v.intView != none) = true ∧
      domNeGate (.int c) c (Dom.enum (doms.getD j Dom.empty)) = true ∧
      valueMemB (.int c) (Dom.enum (doms.getD j Dom.empty)) = true := by
  unfold allDiffElimB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- A target reported by the scan passes the gate and lies in `is`. -/
theorem allDiffElimTarget_spec {doms : List Domain} {is : List Nat}
    {i : Nat} {c : Int} {j : Nat}
    (h : allDiffElimTarget doms is i c = some j) :
    j ∈ is ∧ allDiffElimB doms i j c = true := by
  induction is with
  | nil => exact absurd h (by intro hc; simp [allDiffElimTarget] at hc)
  | cons k ks ih =>
      unfold allDiffElimTarget at h
      split at h
      · rename_i hcond
        rw [Option.some.injEq] at h
        subst h
        exact ⟨List.mem_cons_self, hcond⟩
      · obtain ⟨hmem, hb⟩ := ih h
        exact ⟨List.mem_cons_of_mem _ hmem, hb⟩

/-- A surviving value elimination: the fixed slot is a raw integer
singleton, both slots lie in `is`, and the pair passes the gate. -/
theorem allDiffElimFirst_spec {doms : List Domain} {is : List Nat}
    {i j : Nat} {c : Int}
    (h : allDiffElimFirst doms is = some (i, j, c)) :
    i ∈ is ∧ Dom.enum (doms.getD i Dom.empty) = [.int c] ∧ j ∈ is ∧
      allDiffElimB doms i j c = true := by
  induction is with
  | nil => exact absurd h (by intro hc; simp [allDiffElimFirst] at hc)
  | cons k ks ih =>
      unfold allDiffElimFirst at h
      split at h
      · rename_i c0 hget
        split at h
        · rename_i j0 htarget
          rw [Option.some.injEq] at h
          simp only [Prod.mk.injEq] at h
          obtain ⟨h1, h2, h3⟩ := h
          subst h1
          subst h2
          subst h3
          obtain ⟨hmem, hb⟩ := allDiffElimTarget_spec htarget
          exact ⟨List.mem_cons_self, hget, hmem, hb⟩
        · obtain ⟨hmem, hget', hmem', hb⟩ := ih h
          exact ⟨List.mem_cons_of_mem _ hmem, hget',
            List.mem_cons_of_mem _ hmem', hb⟩
      · obtain ⟨hmem, hget', hmem', hb⟩ := ih h
        exact ⟨List.mem_cons_of_mem _ hmem, hget',
          List.mem_cons_of_mem _ hmem', hb⟩

/-- Every literal of an elimination clause sits on the fixed slot or on the
target slot. -/
theorem allDiffElimClause_slot {i j : Nat} {c : Int} {q : Literal}
    (hq : q ∈ allDiffElimClause i j c) :
    q.atom.slot = i ∨ q.atom.slot = j := by
  simp only [allDiffElimClause, List.mem_cons, List.mem_nil_iff,
    or_false] at hq
  rcases hq with hq | hq | hq | hq | hq
  · exact Or.inr (by rw [hq]; rfl)
  · exact Or.inl (by rw [hq]; rfl)
  · exact Or.inl (by rw [hq]; rfl)
  · unfold neBoolLit at hq
    split at hq
    · rw [hq]; exact Or.inl rfl
    · rw [hq]; exact Or.inl rfl
  · unfold neBoolLit at hq
    split at hq
    · rw [hq]; exact Or.inr rfl
    · rw [hq]; exact Or.inl rfl

/-! ## The emission inversions -/

/-- `propAllDiffLCG`'s implied emissions are exactly the value
eliminations: the scan selected the pair, the literal is the removal of the
fixed value from the target slot, and the reason is the
`propNe`-shaped nogood. -/
theorem propAllDiffLCG_implied_inv {st : State} {is : List Nat}
    {l : Literal} {r : Reason}
    (hrun : propAllDiffLCG st is = .implied l r) :
    ∃ i j c, allDiffElimFirst st.domains is = some (i, j, c) ∧
      l = posNe j c ∧ r = { clause := allDiffElimClause i j c } := by
  unfold propAllDiffLCG at hrun
  split at hrun
  · exact absurd hrun (by simp)
  · split at hrun
    · rename_i i j c hf
      injection hrun with h1 h2
      exact ⟨i, j, c, hf, h1.symm, h2.symm⟩
    · exact absurd hrun (by simp)

/-- The conflict-report inversion: a conflict means the domain-level
    pigeonhole fired, and the reported clause is the Hall clause. -/
theorem propAllDiffLCG_conflict_inv {st : State} {is : List Nat}
    {c : Clause} (hrun : propAllDiffLCG st is = .conflict c) :
    propAllDiff is (st.domains.map Dom.enum) = PropResult.contradiction ∧
      c = hallClause st.domains is := by
  unfold propAllDiffLCG at hrun
  split at hrun
  · next h => exact ⟨h, (PropagationResult.conflict.inj hrun).symm⟩
  · split at hrun
    · exact absurd hrun (by simp)
    · exact absurd hrun (by simp)

/-- The enumeration of the mapped frame is the candidate space of the
    compact frame (`allAssigns` commutes with the slot-wise enumeration). -/
theorem allAssigns_map_enum (doms : List Domain) :
    allAssigns (doms.map Dom.enum) = allAssigns doms := by
  induction doms with
  | nil => rfl
  | cons d ds ih =>
      simp only [List.map_cons, allAssigns]
      rw [ih]
      simp only [DomainElems.elems_list, domElems_eq_enum]

/-- `getD` of the enumerated slot list is the enumeration of the compact
    slot domain (both outside the range and inside it). -/
theorem getD_map_enum (doms : List Domain) (s : Nat) :
    (doms.map Dom.enum).getD s ([] : List Value) = Dom.enum (doms.getD s Dom.empty) := by
  induction doms generalizing s with
  | nil => cases s <;> simp [Dom.enum_empty]
  | cons d ds ih =>
      cases s with
      | zero => rfl
      | succ k => exact ih k

/-- A compact frame fit is a fit of the slot-wise enumeration. -/
theorem fits_map_enum {doms : List Domain} {a : Assignment}
    (h : Core.Assignment.Fits doms a) :
    Core.Assignment.Fits (doms.map Dom.enum) a := by
  obtain ⟨hlen, hmem⟩ := h
  refine ⟨by simpa using hlen, ?_⟩
  intro s v hv
  have hdv : v ∈ doms.getD s Dom.empty := hmem s v hv
  have hget := getD_map_enum doms s
  show v ∈ (doms.map Dom.enum).getD s ([] : List Value)
  rw [hget]
  exact (DomainLike.mem_iff _ _).mp hdv

/-- `getSlot` of the enumerated slot list is the enumeration of the read
    compact domain. -/
theorem getSlot_map_enum : ∀ (doms : List Domain) (i : Nat),
    getSlot (doms.map Dom.enum) i = Dom.enum (doms.getD i Dom.empty)
  | [], i => by cases i <;> rfl
  | _ :: _, 0 => rfl
  | _ :: ds, k + 1 => getSlot_map_enum ds k

/-! ## The Dom-native structural layer

The reference definitions above read the state through
`st.domains.map Dom.enum`, materialising the enumeration of EVERY domain
in the state.  The pigeonhole test, however, only inspects the slots of
`is`, and its filter only needs each slot's NONEMPTINESS, which the
compact carrier answers with the cardinality test `Dom.isEmpty` (no
enumeration).  The definitions below are the same decision on the
compact `Dom` carrier; the equality lemmas identify them with the
reference definitions, and the `@[implemented_by]` seam at the end of
this section swaps only the COMPILED call of `propAllDiffLCG`. -/

/-- Nonempty slots of `is`, read structurally: `Dom.isEmpty` is the
    cardinality test, so this never enumerates a domain. -/
def inRangeSlotsD (doms : List Domain) (is : List Nat) : List Nat :=
  is.filter (fun i => !(doms.getD i Dom.empty).isEmpty)

/-- The structural filter is the reference filter on the enumerated
    frame: `Dom.isEmpty` agrees with the emptiness of `Dom.enum`, and
    `getSlot` of the mapped frame is the enumerated compact slot
    (`getSlot_map_enum`). -/
theorem inRangeSlotsD_eq (doms : List Domain) (is : List Nat) :
    inRangeSlotsD doms is = inRangeSlots (doms.map Dom.enum) is := by
  unfold inRangeSlotsD inRangeSlots
  apply List.filter_congr
  intro i _
  rw [getSlot_map_enum]
  have hlist : ((Dom.enum (doms.getD i Dom.empty)).isEmpty = true) ↔
      Dom.enum (doms.getD i Dom.empty) = [] := by
    cases Dom.enum (doms.getD i Dom.empty) <;> simp
  have h : (doms.getD i Dom.empty).isEmpty =
      (Dom.enum (doms.getD i Dom.empty)).isEmpty := by
    rw [Bool.eq_iff_iff, Dom.isEmpty_eq_true_iff, hlist]
  rw [h]

/-- The deduplicated union of the enumerated domains of the slots `is`,
    read from the compact carrier: only the slots of `is` are
    enumerated. -/
def distinctUnionValsD (doms : List Domain) (is : List Nat) : List Value :=
  dedupVals (is.flatMap fun i => Dom.enum (doms.getD i Dom.empty))

/-- The structural union is the reference union on the enumerated
    frame, slot by slot (`getSlot_map_enum`). -/
theorem distinctUnionValsD_eq (doms : List Domain) (is : List Nat) :
    distinctUnionValsD doms is = distinctUnionVals (doms.map Dom.enum) is := by
  unfold distinctUnionValsD distinctUnionVals
  congr 1
  induction is with
  | nil => rfl
  | cons i is ih =>
      simp only [List.flatMap_cons, getSlot_map_enum, ih]

/-- The pigeonhole decision on the compact carrier: `propAllDiff`'s test
    with the structural filter and union.  The narrowed arm keeps the
    enumerated frame, so the payload is exactly the reference payload. -/
def propAllDiffD (is : List Nat) (doms : List Domain) : PropResult :=
  if (inRangeSlotsD doms is).length > (distinctUnionValsD doms is).length then
    .contradiction
  else
    .narrowed (doms.map Dom.enum)

/-- The structural pigeonhole decision is the reference decision. -/
theorem propAllDiffD_eq (is : List Nat) (doms : List Domain) :
    propAllDiffD is doms = propAllDiff is (doms.map Dom.enum) := by
  unfold propAllDiffD propAllDiff
  rw [inRangeSlotsD_eq, distinctUnionValsD_eq]

/-- The Hall clause on the compact carrier: the reference clause with
    the structural nonempty-slot filter. -/
def hallClauseD (doms : List Domain) (is : List Nat) : Clause :=
  match hallClauses doms (inRangeSlotsD doms is) with
  | some c => c
  | none => []

/-- The structural Hall clause is the reference Hall clause. -/
theorem hallClauseD_eq (doms : List Domain) (is : List Nat) :
    hallClauseD doms is = hallClause doms is := by
  unfold hallClauseD hallClause
  rw [inRangeSlotsD_eq]

/-- Compiled Dom-native twin of `propAllDiffLCG`: the pigeonhole test,
    the Hall filter and the conflict clause run on the compact carrier
    (`propAllDiffD` / `hallClauseD`) instead of enumerating every state
    domain.  The logical body of `propAllDiffLCG` is unchanged; the
    `@[implemented_by]` seam below swaps only the compiled call. -/
def propAllDiffLCGFast (st : State) (is : List Nat) : PropagationResult :=
  match propAllDiffD is st.domains with
  | .contradiction => .conflict (hallClauseD st.domains is)
  | .narrowed _ =>
      match allDiffElimFirst st.domains is with
      | some (i, j, c) =>
          .implied (posNe j c) { clause := allDiffElimClause i j c }
      | none => .stable

/-- The compiled twin computes exactly `propAllDiffLCG`. -/
theorem propAllDiffLCGFast_eq (st : State) (is : List Nat) :
    propAllDiffLCGFast st is = propAllDiffLCG st is := by
  unfold propAllDiffLCGFast propAllDiffLCG
  rw [propAllDiffD_eq, hallClauseD_eq]

attribute [implemented_by propAllDiffLCGFast] propAllDiffLCG


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
  -- the fitting assignment is in the enumerated candidate space
  have hmem : a ∈ allAssigns (st.domains.map Dom.enum) :=
    LeanFzn.Compiler.fits_mem_allAssigns (st.domains.map Dom.enum) a
      (fits_map_enum hfit)
  -- the domain-level preservation contract's contradiction arm
  exact (propAllDiff_preserves is).contradicts hpd a hmem hcons

/-! ## The Hall clause: spec, falsification, entailment -/

private theorem foldl_min_le (vs : List Int) :
    ∀ (v0 : Int), ∀ w ∈ v0 :: vs, vs.foldl min v0 ≤ w := by
  induction vs with
  | nil => intro v0 w hw; simp at hw; subst hw; exact Int.le_refl _
  | cons a as ih =>
      intro v0 w hw
      simp only [List.foldl_cons]
      have h1 := ih (min v0 a) (min v0 a) (List.mem_cons_self ..)
      rcases List.mem_cons.mp hw with rfl | hw
      · have := Int.min_le_left w a; omega
      · rcases List.mem_cons.mp hw with rfl | hw
        · have := Int.min_le_right v0 w; omega
        · exact ih (min v0 a) w (List.mem_cons_of_mem _ hw)

private theorem le_foldl_max (vs : List Int) :
    ∀ (v0 : Int), ∀ w ∈ v0 :: vs, w ≤ vs.foldl max v0 := by
  induction vs with
  | nil => intro v0 w hw; simp at hw; subst hw; exact Int.le_refl _
  | cons a as ih =>
      intro v0 w hw
      simp only [List.foldl_cons]
      have h1 := ih (max v0 a) (max v0 a) (List.mem_cons_self ..)
      rcases List.mem_cons.mp hw with rfl | hw
      · have := Int.le_max_left w a; omega
      · rcases List.mem_cons.mp hw with rfl | hw
        · have := Int.le_max_right v0 w; omega
        · exact ih (max v0 a) w (List.mem_cons_of_mem _ hw)

private theorem filterMap_len_eq {l : List Value}
    (h : (l.filterMap Value.intView).length = l.length) :
    ∀ x ∈ l, Value.intView x ≠ none := by
  induction l with
  | nil => intro x hx; cases hx
  | cons y t ih =>
      intro x hx
      have hle : (t.filterMap Value.intView).length ≤ t.length :=
        List.length_filterMap_le _ _
      cases hy : Value.intView y with
      | none =>
          simp only [List.filterMap_cons, hy, List.length_cons] at h
          omega
      | some w =>
          simp only [List.filterMap_cons, hy, List.length_cons] at h
          rcases List.mem_cons.mp hx with rfl | hx
          · simp [hy]
          · exact ih (by omega) x hx

/-- The specification of `slotHall`. -/
theorem slotHall_spec {s : Nat} {d : Domain} {cl : Clause}
    (h : slotHall s d = some cl) :
    (∀ x ∈ d, Value.intView x ≠ none) ∧
    ∃ (lo hi : Int) (holes : List Int),
      cl = posLe s (lo - 1) :: negLe s hi :: holes.map (negNe s) ∧
      (∀ x ∈ d, ∀ w, Value.intView x = some w → lo ≤ w ∧ w ≤ hi) ∧
      (∀ hh ∈ holes, ∀ x ∈ d, Value.intView x ≠ some hh) ∧
      (∀ w, lo ≤ w → w ≤ hi → w ∉ holes → ∃ x ∈ d, Value.intView x = some w) := by
  unfold slotHall at h
  split at h
  · exact absurd h (by simp)
  · rename_i v0 vs hL
    split at h
    · exact absurd h (by simp)
    · rename_i hlen
      dsimp only at h
      split at h
      · exact absurd h (by simp)
      · rename_i hcap
        have hlen' : (v0 :: vs).length = (Dom.enum d).length := by
          simpa using hlen
        have hmemL : ∀ w, w ∈ v0 :: vs ↔ ∃ x ∈ d, Value.intView x = some w := by
          intro w
          rw [← hL, List.mem_filterMap]
          simp [DomainLike.mem_iff]
        refine ⟨?_, ?_⟩
        · intro x hx
          have hxE : x ∈ Dom.enum d := (DomainLike.mem_iff _ _).mp hx
          exact filterMap_len_eq (l := Dom.enum d) (by rw [hL]; exact hlen') x hxE
        · refine ⟨vs.foldl min v0, vs.foldl max v0, _, (Option.some.inj h).symm,
            ?_, ?_, ?_⟩
          · intro x hx w hw
            have hw' : w ∈ v0 :: vs := (hmemL w).2 ⟨x, hx, hw⟩
            exact ⟨foldl_min_le vs v0 w hw', le_foldl_max vs v0 w hw'⟩
          · intro hh hhm x hx hxv
            have hmem := List.mem_filter.mp hhm
            have hc : (v0 :: vs).contains hh = false := by
              simpa using hmem.2
            have : hh ∈ v0 :: vs := (hmemL hh).2 ⟨x, hx, hxv⟩
            have := List.contains_iff_mem.mpr this
            simp_all
          · intro w hlo hhi hnh
            refine Classical.byContradiction fun hno => ?_
            apply hnh
            apply List.mem_filter.mpr
            refine ⟨List.mem_map.mpr ⟨(w - vs.foldl min v0).toNat,
              List.mem_range.mpr (by omega), by omega⟩, ?_⟩
            have : w ∉ v0 :: vs := fun hw => hno ((hmemL w).1 hw)
            have hc : (v0 :: vs).contains w = false := by
              cases hh : (v0 :: vs).contains w
              · rfl
              · exact absurd (List.contains_iff_mem.mp hh) this
            rw [hc]; rfl

/-- Every literal of a slot's Hall literals is FALSE at every value of the
slot's domain. -/
theorem slotHall_falsified {s : Nat} {d : Domain} {cl : Clause}
    (h : slotHall s d = some cl) {a : Assignment} {v : Value}
    (hv : a[s]? = some v) (hmem : v ∈ d) :
    ∀ q ∈ cl, q.eval a = some false := by
  obtain ⟨hviews, lo, hi, holes, hcl, hbd, hholes, _⟩ := slotHall_spec h
  obtain ⟨w, hw⟩ : ∃ w, Value.intView v = some w := by
    cases hh : Value.intView v with
    | none => exact absurd hh (hviews v hmem)
    | some w => exact ⟨w, rfl⟩
  have hsl : slotInt a s = some w := by simp [slotInt, hv, hw]
  obtain ⟨hlo, hhi⟩ := hbd v hmem w hw
  intro q hq
  rw [hcl] at hq
  rcases List.mem_cons.mp hq with rfl | hq
  · simp [posLe, Literal.eval, Atom.eval, hsl]; omega
  rcases List.mem_cons.mp hq with rfl | hq
  · simp [negLe, Literal.eval, Atom.eval, hsl]; omega
  obtain ⟨hh, hhm, rfl⟩ := List.mem_map.mp hq
  have hne : w ≠ hh := fun he => hholes hh hhm v hmem (by rw [hw, he])
  simp [negNe, Literal.eval, Atom.eval, hsl, hne]

/-- If no literal of a slot's Hall literals is true at `a`, and `a` reads at
the slot a value of the domain's sort with an integer view, then that value is
in the domain. -/
theorem slotHall_entailed {s : Nat} {d : Domain} {cl : Clause}
    (h : slotHall s d = some cl) {a : Assignment} {y : Value}
    (hy : a[s]? = some y) (hyv : Value.intView y ≠ none)
    (hsort : ∀ x ∈ d, SortAgree x y)
    (hno : ∀ q ∈ cl, q.eval a ≠ some true) : y ∈ d := by
  obtain ⟨hviews, lo, hi, holes, hcl, hbd, hholes, hcov⟩ := slotHall_spec h
  obtain ⟨w, hw⟩ : ∃ w, Value.intView y = some w := by
    cases hh : Value.intView y with
    | none => exact absurd hh hyv
    | some w => exact ⟨w, rfl⟩
  have hsl : slotInt a s = some w := by simp [slotInt, hy, hw]
  have h1 := hno (posLe s (lo - 1)) (by rw [hcl]; simp)
  have h2 := hno (negLe s hi) (by rw [hcl]; simp)
  simp [posLe, Literal.eval, Atom.eval, hsl] at h1
  simp [negLe, Literal.eval, Atom.eval, hsl] at h2
  have hwhole : w ∉ holes := by
    intro hm
    apply hno (negNe s w) (by rw [hcl]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨w, hm, rfl⟩)))
    simp [negNe, Literal.eval, Atom.eval, hsl]
  obtain ⟨x, hx, hxw⟩ := hcov w (by omega) (by omega) hwhole
  -- same sort and equal view: raw equal
  have hxy : x = y := by
    simp only [Value.intView] at hxw hw
    rcases hsort x hx with ⟨⟨k, hk⟩, ⟨k2, hk2⟩⟩ | ⟨⟨b, hk⟩, ⟨b2, hk2⟩⟩
    · subst hk hk2
      simp only [Value.intView] at hxw hw
      have e1 := Option.some.inj hxw
      have e2 := Option.some.inj hw
      rw [e1, e2]
    · subst hk hk2
      simp only [Value.intView] at hxw hw
      have e1 := Option.some.inj hxw
      have e2 := Option.some.inj hw
      cases b <;> cases b2 <;> first | rfl | (exfalso; simp at e1 e2; omega)
  rw [← hxy]; exact hx

/-- The Hall clause is FALSE at every assignment fitting the domains it was
read from: each literal evaluates to `some false`. (The evidence form of the
Boolean families' `falsifier_pin` consequences.) -/
theorem hallClause_falsified {doms : List Domain} {is : List Nat}
    {a : Assignment} (hfit : Core.Assignment.Fits doms a) :
    ∀ q ∈ hallClause doms is, q.eval a = some false := by
  have key : ∀ (ss : List Nat), (∀ s ∈ ss, s < doms.length) →
      ∀ c, hallClauses doms ss = some c → ∀ q ∈ c, q.eval a = some false := by
    intro ss
    induction ss with
    | nil =>
        intro _ c hc q hq
        simp [hallClauses] at hc; subst hc; simp at hq
    | cons s ss ih =>
        intro hlt c hc q hq
        simp only [hallClauses] at hc
        split at hc
        · rename_i c1 c2 h1 h2
          have hc' := Option.some.inj hc
          subst hc'
          rcases List.mem_append.mp hq with hq | hq
          · have hs : s < doms.length := hlt s List.mem_cons_self
            have hread : ∃ v, a[s]? = some v := by
              have : s < a.length := by rw [hfit.1]; exact hs
              exact ⟨a[s], List.getElem?_eq_getElem this⟩
            obtain ⟨v, hv⟩ := hread
            exact slotHall_falsified h1 hv (hfit.2 s v hv) q hq
          · exact ih (fun t ht => hlt t (List.mem_cons_of_mem _ ht)) c2 h2 q hq
        · exact absurd hc (by simp)
  intro q hq
  unfold hallClause at hq
  split at hq
  · rename_i c hc
    refine key (inRangeSlots (doms.map Dom.enum) is) ?_ c hc q hq
    intro s hs
    have := lt_length_of_mem_inRangeSlots hs
    simpa using this
  · simp at hq

/-- **THE HALL CLAUSE IS ENTAILED**: at every assignment that satisfies
`allDiff is` and is FAITHFUL to the domains of a pigeonhole conflict (it reads
a value of the domain's sort, with an integer view, at every slot), a non-empty
Hall clause has a true literal. -/
theorem hallClause_entailed {doms : List Domain} {is : List Nat}
    (hpd : propAllDiff is (doms.map Dom.enum) = PropResult.contradiction)
    {a : Assignment}
    (hsat : (DomConstraint.allDiff is).SatisfiedBy a)
    (hfaith : FrameFaithful doms a) (hne : hallClause doms is ≠ []) :
    ∃ l ∈ hallClause doms is, l.eval a = some true := by
  refine Classical.byContradiction fun hcon => ?_
  have hno : ∀ q ∈ hallClause doms is, q.eval a ≠ some true := by
    intro q hq hqt
    exact hcon ⟨q, hq, hqt⟩
  -- the clause is the concatenation of the per-slot literals
  unfold hallClause at hne hno
  split at hne
  · rename_i c hc
    rw [hc] at hno
    -- every in-range slot reads a value of the enumerated union
    have hpig : ∀ ss : List Nat, ∀ c', hallClauses doms ss = some c' →
        (∀ q ∈ c', q.eval a ≠ some true) →
        ∀ s ∈ ss, s < doms.length →
          a[s]! ∈ Dom.enum (doms.getD s Dom.empty) := by
      intro ss
      induction ss with
      | nil => intro c' _ _ s hs; cases hs
      | cons t ts ih =>
          intro c' hc' hno' s hs hslt
          simp only [hallClauses] at hc'
          split at hc'
          · rename_i c1 c2 h1 h2
            have hc'' := Option.some.inj hc'
            subst hc''
            rcases List.mem_cons.mp hs with rfl | hs
            · obtain ⟨y, hy, hyv, hsort⟩ := hfaith s hslt
              have hmem := slotHall_entailed h1 hy hyv hsort
                (fun q hq => hno' q (List.mem_append_left _ hq))
              have hay : a[s]! = y := by simp [hy]
              rw [hay]
              exact (DomainLike.mem_iff _ _).mp hmem
            · exact ih c2 h2 (fun q hq => hno' q (List.mem_append_right _ hq)) s hs hslt
          · exact absurd hc' (by simp)
    have hmemU : ∀ i ∈ inRangeSlots (doms.map Dom.enum) is,
        a[i]! ∈ distinctUnionVals (doms.map Dom.enum) is := by
      intro i hi
      have hilt : i < doms.length := by
        have := lt_length_of_mem_inRangeSlots hi
        simpa using this
      have hin := mem_inRangeSlots_left hi
      have hd := hpig (inRangeSlots (doms.map Dom.enum) is) c hc hno i hi hilt
      unfold distinctUnionVals
      exact (mem_dedupVals _ _).mpr
        (List.mem_flatMap.mpr ⟨i, hin, by rw [getSlot_map_enum]; exact hd⟩)
    have hle := allDiff_pigeonhole_of_mem hsat hmemU
    simp only [propAllDiff] at hpd
    split at hpd
    · rename_i hgt; omega
    · exact absurd hpd (by simp)
  · exact absurd rfl hne

/-- The Hall clause of a pigeonhole conflict report, as facts about the
reported clause. -/
theorem propAllDiffLCG_conflict_falsified {st : State} {is : List Nat}
    {c : Clause} (hrun : propAllDiffLCG st is = .conflict c)
    {a : Assignment} (hfit : Core.Assignment.Fits st.domains a) :
    ∀ q ∈ c, q.eval a = some false := by
  obtain ⟨_, hc⟩ := propAllDiffLCG_conflict_inv hrun
  rw [hc]
  exact hallClause_falsified hfit

/-- **Entailment of the reported Hall clause** (nonempty reports). -/
theorem propAllDiffLCG_conflict_entailed {st : State} {is : List Nat}
    {c : Clause} (hrun : propAllDiffLCG st is = .conflict c)
    (hne : c ≠ []) {a : Assignment}
    (hsat : (DomConstraint.allDiff is).SatisfiedBy a)
    (hfaith : FrameFaithful st.domains a) :
    ∃ l ∈ c, l.eval a = some true := by
  obtain ⟨hpd, hc⟩ := propAllDiffLCG_conflict_inv hrun
  subst hc
  exact hallClause_entailed hpd hsat hfaith hne

/-! ## The two semantic readings of the elimination

The implied literal `x_j ≠ c` is true at every fitting solution of the
pairwise-distinctness (the fixed slot reads `.int c`; a target read with
view `c` would be the raw `.int c` — the `domNeGate` correspondence — and
the distinctness forbids the raw collision), and the reason clause is true
at every satisfying read pair with views (the state-free `Reason.Valid`
shape; the mixed-sort cases close by the two `neBoolLit` disjuncts — the
same case analysis as `ne_nogood_true` for the raw disequality). -/

/-- From a `Nodup` mapped list: distinct members map to distinct values. -/
private theorem map_nodup_ne : ∀ (l : List Nat) (f : Nat → Value),
    (l.map f).Nodup →
    ∀ {i j : Nat}, i ∈ l → j ∈ l → i ≠ j → f i ≠ f j := by
  intro l
  induction l with
  | nil => intro f h i j hi; exact absurd hi (by simp)
  | cons k ks ih =>
      intro f h i j hi hj hij
      simp only [List.map_cons, List.nodup_cons] at h
      obtain ⟨hk, hks⟩ := h
      rcases List.mem_cons.mp hi with hik | hiks
      · rcases List.mem_cons.mp hj with hjk | hjks
        · subst hik; subst hjk; exact absurd rfl hij
        · subst hik
          intro heq
          exact hk (List.mem_map.mpr ⟨j, hjks, heq.symm⟩)
      · rcases List.mem_cons.mp hj with hjk | hjks
        · subst hjk
          intro heq
          exact hk (List.mem_map.mpr ⟨i, hiks, heq⟩)
        · exact ih f hks hiks hjks hij

/-- **The pairwise-distinctness is raw-distinctness of the reads**: slots
`i ≠ j` of `is` read different raw values under every satisfying
assignment. -/
theorem allDiff_read_ne {a : Assignment} {is : List Nat}
    (hcons : (DomConstraint.allDiff is).SatisfiedBy a)
    {i j : Nat} (hi : i ∈ is) (hj : j ∈ is) (hij : i ≠ j) :
    a[i]! ≠ a[j]! :=
  map_nodup_ne is (fun k => a[k]!)
    (by simpa only [DomConstraint.SatisfiedBy] using hcons) hi hj hij

/-- The bang read of an existing read. -/
private theorem bang_eq_of_getElem? {l : List Value} {i : Nat} {v : Value}
    (h : l[i]? = some v) : l[i]! = v := by
  have hlt : i < l.length := (List.getElem?_eq_some_iff.mp h).1
  rw [getElem!_pos l i hlt]
  exact Option.some.inj (List.getElem?_eq_getElem hlt ▸ h)

/-- A fitting read in a raw integer singleton domain IS the singleton. -/
theorem intSingleton_read {doms : List Domain} {a : Assignment} {i : Nat}
    {c : Int} (hsi : Dom.enum (doms.getD i Dom.empty) = [.int c])
    (hfit : Core.Assignment.Fits doms a) : a[i]? = some (.int c) := by
  have hilt : i < doms.length := by
    by_cases hlt : i < doms.length
    · exact hlt
    · exfalso
      have hnil : Dom.enum (doms.getD i Dom.empty) = [] := by
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (Nat.le_of_not_lt hlt)]
        exact Dom.enum_empty
      rw [hnil] at hsi
      exact absurd hsi (by simp)
  have hialt : i < a.length := by rw [hfit.1]; exact hilt
  have hread : a[i]? = some a[i] := List.getElem?_eq_getElem hialt
  have hmem : a[i] ∈ doms.getD i Dom.empty := hfit.2 i _ hread
  have hmemE : a[i] ∈ Dom.enum (doms.getD i Dom.empty) :=
    (DomainLike.mem_iff _ _).mp hmem
  rw [hsi] at hmemE
  rw [hread, List.mem_singleton.mp hmemE]

/-- **The elimination implied literal is TRUE at fitting solutions of the
pairwise-distinctness**: the fixed slot reads `.int c`; the target slot's
domain is int-viewed (so its fitting read HAS a view) and the `domNeGate`
forces any value of it viewing `c` to BE `.int c` — raw-equal to the fixed
slot's read, which the distinctness forbids. Hence the target's view
differs from `c` and `x_j ≠ c` holds. -/
theorem allDiff_elim_true_of_fits {doms : List Domain} {is : List Nat}
    {a : Assignment} {i j : Nat} {c : Int}
    (hi : i ∈ is) (hj : j ∈ is) (hne : i ≠ j)
    (hsi : Dom.enum (doms.getD i Dom.empty) = [.int c])
    (hjlt : j < doms.length)
    (hviewj : (Dom.enum (doms.getD j Dom.empty)).all
      (fun v => v.intView != none) = true)
    (hgate : domNeGate (.int c) c (Dom.enum (doms.getD j Dom.empty)) = true)
    (hfit : Core.Assignment.Fits doms a)
    (hcons : (DomConstraint.allDiff is).SatisfiedBy a) :
    (posNe j c).eval a = some true := by
  -- the target read exists and has a view
  have hlen : j < a.length := by rw [hfit.1]; exact hjlt
  have hread : a[j]? = some a[j] := List.getElem?_eq_getElem hlen
  have hmemj : a[j] ∈ doms.getD j Dom.empty := hfit.2 j _ hread
  have hmemjE : a[j] ∈ Dom.enum (doms.getD j Dom.empty) :=
    (DomainLike.mem_iff _ _).mp hmemj
  obtain ⟨w, hw⟩ : ∃ w, Value.intView a[j] = some w := by
    have hv := List.all_eq_true.mp hviewj _ hmemjE
    cases hh : Value.intView a[j] with
    | none => rw [hh] at hv; exact absurd hv (by simp)
    | some w => exact ⟨w, rfl⟩
  -- the fixed read is `.int c`; a target view `c` would be a raw collision
  have hai : a[i]? = some (.int c) := intSingleton_read hsi hfit
  have hdist : a[i]! ≠ a[j]! := allDiff_read_ne hcons hi hj hne
  have hwc : w ≠ c := by
    intro hwc
    have hall := List.all_eq_true.mp hgate (a[j]) hmemjE
    have hraw : a[j] = .int c :=
      value_eqB_iff.mp (by simpa [hw, hwc] using hall)
    exact hdist (by
      rw [bang_eq_of_getElem? hai, bang_eq_of_getElem? hread, hraw])
  rw [eval_posNe_iff]
  refine ⟨w, ?_, hwc⟩
  show (a[j]?.bind Value.intView) = some w
  rw [hread]
  exact hw

/-- **The elimination nogood is TRUE at every satisfying read pair with
views**: under the pairwise-distinctness of `is`, at every assignment whose
reads at `i` and `j` (both in `is`, `i ≠ j`) carry integer views, one of the
five disjuncts of `allDiffElimClause i j c` is true. The same case analysis
as the `neSlot` family's `ne_nogood_true` (the raw-distinctness conflict),
with the raw disequality replaced by the all-different distinctness of the
two reads. -/
theorem allDiff_nogood_true {a : Assignment} {i j : Nat} {is : List Nat}
    {c : Int}
    (hcons : (DomConstraint.allDiff is).SatisfiedBy a)
    (hi : i ∈ is) (hj : j ∈ is) (hij : i ≠ j)
    (hxi : ∃ x, slotInt a i = some x)
    (hyj : ∃ y, slotInt a j = some y) :
    ∃ l ∈ allDiffElimClause i j c, l.eval a = some true := by
  obtain ⟨x, hx⟩ := hxi
  obtain ⟨y, hy⟩ := hyj
  -- the raw reads
  obtain ⟨p, hp⟩ : ∃ p, a[i]? = some p := by
    cases ha : a[i]? with
    | none =>
        exfalso
        rw [slotInt, ha] at hx
        simp at hx
    | some p => exact ⟨p, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, a[j]? = some q := by
    cases ha : a[j]? with
    | none =>
        exfalso
        rw [slotInt, ha] at hy
        simp at hy
    | some q => exact ⟨q, rfl⟩
  -- the views come from the raw reads
  have hviewi : Value.intView p = some x := by
    rw [slotInt, hp] at hx
    exact hx
  have hviewj : Value.intView q = some y := by
    rw [slotInt, hq] at hy
    exact hy
  -- the raw reads are distinct (the all-different distinctness)
  have hpq : p ≠ q := by
    have hd := allDiff_read_ne hcons hi hj hij
    rw [bang_eq_of_getElem? hp, bang_eq_of_getElem? hq] at hd
    exact hd
  have mem1 : posNe j c ∈ allDiffElimClause i j c := by
    simp [allDiffElimClause]
  have mem3 : negLe i c ∈ allDiffElimClause i j c := by
    simp [allDiffElimClause]
  have mem4 : neBoolLit i i c ∈ allDiffElimClause i j c := by
    simp [allDiffElimClause]
  have mem5 : neBoolLit i j c ∈ allDiffElimClause i j c := by
    simp [allDiffElimClause]
  by_cases hxeq : x = c
  · -- x's view is c: the two bound causes are false; the raw shapes close
    cases hp2 : p with
    | int p2 =>
        have hpc : p2 = x := by
          rw [hp2] at hviewi
          exact Option.some.inj hviewi
        cases hq2 : q with
        | int q2 =>
            have hqx : q2 = y := by
              rw [hq2] at hviewj
              exact Option.some.inj hviewj
            by_cases hyc : y = c
            · -- both reads are `.int c` — raw-equal, contradicting the
              -- distinctness
              exfalso
              exact hpq (by rw [hp2, hq2, hpc, hqx, hxeq, hyc])
            · exact ⟨posNe j c, mem1, by
                rw [eval_posNe_iff]; exact ⟨y, hy, hyc⟩⟩
        | bool b2 =>
            by_cases hbc : (if b2 then 1 else 0) = c
            · -- q is the Boolean viewing to c: the y = B disjunct is true
              have hbdec : b2 = decide (c = 1) := by
                cases b2 with
                | true =>
                    have hc1 : c = 1 := by
                      have h1 : (1 : Int) = c := by simpa using hbc
                      omega
                    rw [decide_eq_true hc1]
                | false =>
                    have hc0 : c = 0 := by
                      have h0 : (0 : Int) = c := by simpa using hbc
                      omega
                    rw [decide_eq_false (by omega : c ≠ 1)]
              have hc01 : c = 0 ∨ c = 1 := by
                cases b2 with
                | true => right; simpa using hbc.symm
                | false => left; simpa using hbc.symm
              exact ⟨neBoolLit i j c, mem5, by
                rw [neBoolLit, if_pos hc01, eval_posBool_iff, ← hbdec,
                  hq, hq2]⟩
            · exact ⟨posNe j c, mem1, by
                rw [eval_posNe_iff]
                refine ⟨(if b2 then 1 else 0), ?_, hbc⟩
                show (a[j]?.bind Value.intView) =
                  some (if b2 then 1 else 0)
                rw [hq]
                rw [hq2]
                rfl⟩
        | setOfInt s =>
            rw [hq2] at hviewj
            exact absurd hviewj (by simp [Value.intView])
        | array s =>
            rw [hq2] at hviewj
            exact absurd hviewj (by simp [Value.intView])
    | bool bi =>
        -- p is the bool viewing to c (x = c): the x = B disjunct is true
        have hxc : (if bi then 1 else 0) = x := by
          rw [hp2] at hviewi
          exact Option.some.inj hviewi
        have hxc' : (if bi then 1 else 0) = c := by omega
        have hbdec : bi = decide (c = 1) := by
          cases bi with
          | true =>
              have hc1 : c = 1 := by
                have h1 : (1 : Int) = c := by simpa using hxc'
                omega
              rw [decide_eq_true hc1]
          | false =>
              have hc0 : c = 0 := by
                have h0 : (0 : Int) = c := by simpa using hxc'
                omega
              rw [decide_eq_false (by omega : c ≠ 1)]
        have hc01 : c = 0 ∨ c = 1 := by
          cases bi with
          | true => right; simpa using hxc'.symm
          | false => left; simpa using hxc'.symm
        exact ⟨neBoolLit i i c, mem4, by
          rw [neBoolLit, if_pos hc01, eval_posBool_iff, ← hbdec,
            hp, hp2]⟩
    | setOfInt s =>
        rw [hp2] at hviewi
        exact absurd hviewi (by simp [Value.intView])
    | array s =>
        rw [hp2] at hviewi
        exact absurd hviewi (by simp [Value.intView])
  · -- x's view differs from c: one of the two bound causes is true
    by_cases hxlt : x < c
    · exact ⟨posLe i (c - 1), by simp [allDiffElimClause], by
        rw [eval_posLe_iff]; exact ⟨x, hx, by omega⟩⟩
    · exact ⟨negLe i c, mem3, by
        rw [eval_negLe_iff]; exact ⟨x, hx, by omega⟩⟩

/-- Every literal of an elimination clause is in normal form. -/
theorem allDiffElimClause_norm {i j : Nat} {c : Int} {q : Literal}
    (hq : q ∈ allDiffElimClause i j c) : q = q.norm := by
  simp only [allDiffElimClause, List.mem_cons, List.mem_nil_iff,
    or_false] at hq
  rcases hq with hq | hq | hq | hq | hq
  · rw [hq]; rfl
  · rw [hq]; rfl
  · rw [hq]; rfl
  · rw [hq]
    unfold neBoolLit
    split <;> rfl
  · rw [hq]
    unfold neBoolLit
    split <;> rfl

/-! ## The safe triple

The three-conjunct discipline of `propNe_safe` (the empty-conflict
template): implied-literal truth (VACUOUS — never implies), conflict
exclusion (the pigeonhole), and conflict entitlement — the latter via
the VACUITY mechanism: the exclusion makes the entitlement's
hypotheses (`Fits` + `SatisfiedBy`) contradictory, so the empty
clause's missing true literal is supplied by ex falso. -/

/-- `propAllDiffLCG` soundness over `allDiff is`: the implied value
    eliminations are true at every fitting satisfying assignment (a fixed
    slot's value is removed from the other slots), the pigeonhole conflict
    excludes every fitting satisfying assignment, and the conflict clause
    carries no entitlement obligation beyond the exclusion itself. -/
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
  · -- implied: the value elimination read off the scan
    intro l r hrun a hfit hcons
    obtain ⟨i, j, c, hf, hl, _⟩ := propAllDiffLCG_implied_inv hrun
    obtain ⟨hi, hsi, hj, hb⟩ := allDiffElimFirst_spec hf
    obtain ⟨hne, hjlt, hviewj, hgate, _⟩ := allDiffElimB_eq hb
    subst hl
    exact allDiff_elim_true_of_fits hi hj (fun hij => hne hij.symm) hsi hjlt
      hviewj hgate hfit hcons
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

/-! ## Reason validity

The state-free reason-validity obligation for the value-elimination
emissions: the clause `allDiffElimClause i j c` is entailed at EVERY
internal solution (not only the ones fitting the state) and the pivot is a
member. The two extra premises come from the compiled problem's box: `i` and
`j` are in range of `problem.domains` (the compiler-side operand-range gate,
mirroring the `linLeReif` family's `hreif`), so an internal solution's reads
at `i`/`j` exist (it fits the box) and carry integer views (the box is
int-viewed), which is exactly the premise of `allDiff_nogood_true`. -/

/-- The state-free reason-validity lemma for the `allDiff` family's value
    eliminations: the reported nogood is valid under the constraint at
    every internal solution. -/
theorem propAllDiffLCG_reason_valid
    {problem : Problem DomConstraint Unit}
    (hview : IntViewedDoms problem.domains)
    {st : State} {is : List Nat} {l : Literal} {r : Reason}
    (hprob : DomConstraint.allDiff is ∈ problem.constraints)
    (hlad : ∀ i ∈ is, i < problem.domains.length)
    (hrun : propAllDiffLCG st is = .implied l r) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  obtain ⟨i, j, c, hf, hl, hr⟩ := propAllDiffLCG_implied_inv hrun
  obtain ⟨hi, hsi, hj, hb⟩ := allDiffElimFirst_spec hf
  obtain ⟨hne, hjlt, hviewj, hgate, hmem⟩ := allDiffElimB_eq hb
  subst hl
  subst hr
  refine ⟨⟨?_, by simp [allDiffElimClause]⟩, fun q hq =>
    allDiffElimClause_norm hq⟩
  intro a ha
  have hcons : (DomConstraint.allDiff is).SatisfiedBy a := ha.2 _ hprob
  -- the two reads exist (both slots are in range of the box the
  -- solution fits) and carry views (the box is int-viewed)
  have hreads : (∀ s ∈ is, ∃ x, slotInt a s = some x) := by
    intro s hs
    have hslt : s < problem.domains.length := hlad s hs
    have hsalt : s < a.length := by rw [ha.1.1]; exact hslt
    have hread : a[s]? = some a[s] := List.getElem?_eq_getElem hsalt
    have hmem : a[s] ∈ problem.domains.getD s Dom.empty := ha.1.2 s _ hread
    have hmemd : problem.domains.getD s Dom.empty ∈ problem.domains :=
      getD_mem_of_lt hslt
    have hv : Value.intView a[s] ≠ none := hview _ hmemd _ hmem
    obtain ⟨w, hw⟩ : ∃ w, Value.intView a[s] = some w := by
      cases hh : Value.intView a[s] with
      | none => exact absurd hh hv
      | some w => exact ⟨w, rfl⟩
    exact ⟨w, by
      show (a[s]?.bind Value.intView) = some w
      rw [hread]
      exact hw⟩
  exact allDiff_nogood_true hcons hi hj (fun hij => hne hij.symm)
    (hreads i hi) (hreads j hj)

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
#print axioms inRangeSlotsD_eq
#print axioms distinctUnionValsD_eq
#print axioms propAllDiffD_eq
#print axioms hallClauseD_eq
#print axioms propAllDiffLCGFast_eq
#print axioms propAllDiffLCG_implied_inv
#print axioms propAllDiffLCG_conflict_inv
#print axioms propAllDiffLCG_conflict_entailed
#print axioms propAllDiffLCG_conflict_falsified
#print axioms propAllDiffLCG_conflict_nofit
#print axioms allDiffElimB_eq
#print axioms allDiffElimTarget_spec
#print axioms allDiffElimFirst_spec
#print axioms allDiffElimClause_slot
#print axioms allDiffElimClause_norm
#print axioms allDiff_read_ne
#print axioms intSingleton_read
#print axioms allDiff_elim_true_of_fits
#print axioms allDiff_nogood_true
#print axioms propAllDiffLCG_safe
#print axioms propAllDiffLCG_entitled
#print axioms propAllDiffLCG_fitexcl
#print axioms propAllDiffLCG_reason_valid
#print axioms propagatorOfProvedBA
#print axioms propagatorOfProvedBA_mem
#print axioms propagatorOfProvedBA_run

/-! ## Smoke tests

Concrete small states exercising the three emission shapes (kernel
reduction by `rfl`; no `native_decide`). -/

/-- The test state: empty trail and databases. -/
private def allDiffTestState (doms : List (List Value)) : State where
  domains := doms.map Dom.ofList
  trail := []
  decisionLevel := 0
  clauses := []
  learned := []
  queue := []
  conflict := none

/-- Smoke: the pigeonhole FIRES — three in-range slots over a union
of two distinct values (3 > 2) — reported as its Hall clause (each slot: below 1 or above 2). -/
theorem propAllDiffLCG_smoke_conflict :
    propAllDiffLCG
        (allDiffTestState [[.int 1, .int 2], [.int 1, .int 2],
          [.int 1, .int 2]]) [0, 1, 2] =
      .conflict [posLe 0 0, negLe 0 2, posLe 1 0, negLe 1 2,
        posLe 2 0, negLe 2 2] := by rfl

/-- Smoke: three in-range slots over a union of three distinct values
(3 > 3 is false) and all domains multi-valued — the propagator stays
stable. -/
theorem propAllDiffLCG_smoke_stable :
    propAllDiffLCG
        (allDiffTestState [[.int 1, .int 2, .int 3], [.int 1, .int 2],
          [.int 2, .int 3]]) [0, 1, 2] =
      .stable := by rfl

/-- Smoke: the value elimination FIRES — slot 0 is pinned to `1`, so
`1` is removed from slot 1 (which still contains it). -/
theorem propAllDiffLCG_smoke_elim :
    propAllDiffLCG
        (allDiffTestState [[.int 1], [.int 1, .int 2]]) [0, 1] =
      .implied (posNe 1 1) { clause := allDiffElimClause 0 1 1 } := by rfl

/-- Smoke: the elimination respects the `domNeGate` — slot 1 holds a
BOOLEAN viewing to `1` as well as the integer `1`, so the raw
correspondence fails and nothing is emitted. -/
theorem propAllDiffLCG_smoke_elim_gate :
    propAllDiffLCG
        (allDiffTestState [[.int 1], [.bool true, .int 1]]) [0, 1] =
      .stable := by rfl

/-- Smoke: a fixed Boolean slot is NOT an elimination source (the raw
singleton must be an integer), so nothing is emitted. -/
theorem propAllDiffLCG_smoke_elim_bool :
    propAllDiffLCG
        (allDiffTestState [[.bool true], [.bool true, .int 1]]) [0, 1] =
      .stable := by rfl

/-- Smoke: the elimination does not fire on out-of-range targets. -/
theorem propAllDiffLCG_smoke_elim_range :
    propAllDiffLCG
        (allDiffTestState [[.int 1], [.int 1, .int 2]]) [0, 5] =
      .stable := by rfl

#print axioms propAllDiffLCG_smoke_conflict
#print axioms propAllDiffLCG_smoke_stable
#print axioms propAllDiffLCG_smoke_elim
#print axioms propAllDiffLCG_smoke_elim_gate
#print axioms propAllDiffLCG_smoke_elim_bool
#print axioms propAllDiffLCG_smoke_elim_range

end LeanFzn.Solver.Propagation

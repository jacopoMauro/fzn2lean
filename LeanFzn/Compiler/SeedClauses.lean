/-
File: LeanFzn/Compiler/SeedClauses.lean

Purpose:
  The original-clause emission of the `bool_clause` fragment (PLAN C2).
  A compiled `boolClauseSlot` constraint has NO propagator; the compiled
  LCG problem's clause database is instead SEEDED with the corresponding
  original clause `∨_{i∈ps} (x_i = true) ∨ ∨_{j∈ns} (x_j = false)`, so
  the engine can propagate it from the database. This file defines the
  seed and proves the facts the LCG layer consumes: the seed is implied
  by the constraint's own leaf semantics (every seed clause is satisfied
  on `satisfiedB`-true assignments), and every seed literal is a
  normal-form positive pin (the pool-alignment half lives one layer up,
  with the literal pool).

Dependencies:
  - LeanFzn.Compiler.Compile: the executable compiler (`DomConstraint`).
  - LeanFzn.Solver.Propagation.Encoding: positive-pin literal evaluation.
DAG: compiler + propagation types -> this file -> Integration.Lcg seed.
-/

import LeanFzn.Compiler.Compile
import LeanFzn.Solver.Propagation.Encoding

namespace LeanFzn.Compiler
open LeanFzn.Semantics LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

/-! ## §1 The seed -/

/-- The original clause of one `bool_clause(pos, neg)` constraint:
    `∨_{i∈ps} (x_i = true) ∨ ∨_{j∈ns} (x_j = false)`. Every literal is a
    POSITIVE Boolean pin, i.e. already in normal form (`Literal.norm` is
    the identity on it). -/
def boolClauseSeed (ps ns : List Nat) : Clause :=
  ps.map (fun i => posBool i true) ++ ns.map (fun j => posBool j false)

/-- The seeded original-clause database of a compiled constraint list:
    one clause per `bool_clause` (`boolClauseSlot`) constraint, in
    constraint order. Constraints of every other family contribute no
    clause (they run through their registered propagators instead). -/
def seedClauses (dcs : List DomConstraint) : List Clause :=
  dcs.filterMap fun dc =>
    match dc with
    | .boolClauseSlot ps ns => some (boolClauseSeed ps ns)
    | _ => none

/-! ## §2 Members, inversions and normal form -/

/-- A literal of the seed is a positive pin of one of the two sides. -/
theorem mem_boolClauseSeed {ps ns : List Nat} {q : Literal} :
    q ∈ boolClauseSeed ps ns ↔
      (∃ i, i ∈ ps ∧ q = posBool i true) ∨
      (∃ j, j ∈ ns ∧ q = posBool j false) := by
  simp only [boolClauseSeed, List.mem_append, List.mem_map]
  constructor
  · rintro (⟨i, hi, he⟩ | ⟨j, hj, he⟩)
    · exact Or.inl ⟨i, hi, he.symm⟩
    · exact Or.inr ⟨j, hj, he.symm⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr ⟨j, hj, rfl⟩

/-- A seed clause is one of the emitted `boolClauseSeed` clauses, from
    a constraint of the compiled list. -/
theorem seedClauses_mem_inv {dcs : List DomConstraint} {c : Clause}
    (h : c ∈ seedClauses dcs) :
    ∃ ps ns, DomConstraint.boolClauseSlot ps ns ∈ dcs ∧
      c = boolClauseSeed ps ns := by
  rw [seedClauses] at h
  rcases List.mem_filterMap.mp h with ⟨dc, hdc, hf⟩
  cases dc with
  | boolClauseSlot ps ns =>
      simp only at hf
      exact ⟨ps, ns, hdc, by simpa using hf.symm⟩
  | _ => simp at hf

/-- Seed literals are in normal form. -/
theorem boolClauseSeed_norm {ps ns : List Nat} {q : Literal}
    (h : q ∈ boolClauseSeed ps ns) : q.norm = q := by
  rcases mem_boolClauseSeed.mp h with ⟨i, -, rfl⟩ | ⟨j, -, rfl⟩ <;> rfl

/-- Every clause of the seed has only normal-form literals. -/
theorem seedClauses_norm {dcs : List DomConstraint} {c : Clause}
    (hc : c ∈ seedClauses dcs) : ∀ q ∈ c, q.norm = q := by
  obtain ⟨ps, ns, -, rfl⟩ := seedClauses_mem_inv hc
  intro q hq
  exact boolClauseSeed_norm hq

/-! ## §3 The semantic half: every seed clause is entailed by the leaf -/

/-- A true `slotIsBoolB` read yields the Boolean at the slot. -/
theorem slotIsBoolB_some {a : List Value} {i : Nat} {b : Bool}
    (h : slotIsBoolB a i b = true) : a[i]? = some (.bool b) := by
  cases hv : a[i]? with
  | none => simp [slotIsBoolB, hv] at h
  | some v =>
      cases v with
      | bool c =>
          have hc : (c == b) = true := by
            simpa [slotIsBoolB, hv, Value.eqB] using h
          rw [Option.some.injEq, Value.bool.injEq]
          exact beq_iff_eq.mp hc
      | int _ => simp [slotIsBoolB, hv, Value.eqB] at h
      | setOfInt _ => simp [slotIsBoolB, hv, Value.eqB] at h
      | array _ => simp [slotIsBoolB, hv, Value.eqB] at h

/-- The seed clause of a satisfied `boolClauseSlot` is satisfied. -/
theorem boolClauseSeed_entailed {ps ns : List Nat} {a : List Value}
    (h : DomConstraint.satisfiedB (.boolClauseSlot ps ns) a = true) :
    Clause.SatisfiedBy (boolClauseSeed ps ns) a := by
  have h' : (ps.any (fun i => slotIsBoolB a i true)) = true ∨
      (ns.any (fun j => slotIsBoolB a j false)) = true := by
    simpa only [DomConstraint.satisfiedB, Bool.or_eq_true] using h
  rcases h' with hp | hn
  · obtain ⟨i, hi, hib⟩ := List.any_eq_true.mp hp
    exact ⟨posBool i true,
      List.mem_append_left _
        (List.mem_map_of_mem (f := fun i => posBool i true) hi),
      (eval_posBool_iff a i true).mpr (slotIsBoolB_some hib)⟩
  · obtain ⟨j, hj, hjb⟩ := List.any_eq_true.mp hn
    exact ⟨posBool j false,
      List.mem_append_right _
        (List.mem_map_of_mem (f := fun j => posBool j false) hj),
      (eval_posBool_iff a j false).mpr (slotIsBoolB_some hjb)⟩

/-- **THE ENTAILMENT HALF**: every seed clause is satisfied at every
    assignment whose `satisfiedB` leaf check passes (the constraint's
    own semantics supplies it; no propagator is involved). -/
theorem seedClauses_entailed {dcs : List DomConstraint} {a : List Value}
    (h : ∀ dc ∈ dcs, dc.satisfiedB a = true) :
    ∀ c ∈ seedClauses dcs, Clause.SatisfiedBy c a := by
  intro c hc
  obtain ⟨ps, ns, hmem, rfl⟩ := seedClauses_mem_inv hc
  exact boolClauseSeed_entailed (h _ hmem)

/-- The declarative-semantics twin of `seedClauses_entailed`: every seed
    clause is satisfied at every assignment satisfying every compiled
    constraint's `SatisfiedBy` semantics (the chronological fallback's
    database-entailment premise). -/
theorem seedClauses_satisfiedBy {dcs : List DomConstraint} {a : List Value}
    (h : ∀ dc ∈ dcs, dc.SatisfiedBy a) :
    ∀ c ∈ seedClauses dcs, ∃ l ∈ c, l.eval a = some true :=
  seedClauses_entailed
    (fun dc hdc => (DomConstraint.satisfiedB_iff dc a).mpr (h dc hdc))

/-- The `Clause.SatisfiedBy` of a clause is its executable all-any
    check (the shape `chronologicalLeaf` consumes). -/
theorem clause_any_iff (c : Clause) (a : List Value) :
    (c.any (fun l => decide (l.eval a = some true))) = true ↔
      Clause.SatisfiedBy c a := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨l, hl, he⟩
    exact ⟨l, hl, of_decide_eq_true he⟩
  · rintro ⟨l, hl, he⟩
    exact ⟨l, hl, decide_eq_true he⟩

/-- The executable leaf check of every seed clause on a
    `satisfiedB`-true assignment. -/
theorem seedClauses_any_satisfiedB {dcs : List DomConstraint}
    {a : List Value}
    (h : ∀ dc ∈ dcs, dc.satisfiedB a = true) :
    ∀ c ∈ seedClauses dcs,
      (c.any (fun l => decide (l.eval a = some true))) = true :=
  fun c hc => (clause_any_iff c a).mpr (seedClauses_entailed h c hc)

end LeanFzn.Compiler

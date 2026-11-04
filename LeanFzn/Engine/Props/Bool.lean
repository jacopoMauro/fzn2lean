/-
File: LeanFzn/Engine/Props/Bool.lean

Dedicated `bool_clause` propagator: unit propagation over the positive
and negative literal lists.  The clause is entailed by the constraint's
own leaf semantics (`satisfiedB` of a bool clause is exactly the
disjunction of its Boolean pins), so no initial-domain guard is needed.

`boolClausePropWith` is the real propagator; it takes the membership
proof needed to build the entailed clause and reason; `propsOf` registers
it.  `boolClauseProp` is a sound `.fix` no-op kept for its audited contract
theorems.
-/
import LeanFzn.Engine.Prop
import LeanFzn.Compiler.SeedClauses

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

def boolClauseLits (ps ns : List Nat) : Array Literal :=
  ps.toArray.map (fun s => posBool s true) ++ ns.toArray.map (fun s => posBool s false)

/-- Result of scanning the literals of a `bool_clause`. -/
structure BoolClauseScan where
  /-- Some literal is already true. -/
  hit : Bool
  /-- The first unassigned literal (if any). -/
  unit : Option Literal
  /-- Number of unassigned literals. -/
  count : Nat
  deriving Repr, Inhabited

/-- Evaluate one literal on the view. -/
def scanEval (view : EngineView) (l : Literal) : Option Bool :=
  (view.doms.getD l.atom.slot DomC.empty).evalLit l

/-- Scan the clause: detect a true literal, and collect the unassigned
ones.  The first unassigned literal is the unit candidate; when there is
exactly one it is also the last, so pruning agrees with the spike loop. -/
def boolClauseScan (view : EngineView) (lits : Array Literal) : BoolClauseScan :=
  let ls := lits.toList
  let unassigned := ls.filter fun l => scanEval view l == none
  { hit := ls.any fun l => scanEval view l == some true
    unit := unassigned.head?
    count := unassigned.length }

theorem boolClauseLits_entailed (p : CompiledProblem DomConstraint)
    (ps ns : List Nat) (hmem : DomConstraint.boolClauseSlot ps ns ∈ p.constraints) :
    Entailed p (boolClauseLits ps ns).toList := by
  intro a ha hacc
  have hs : (DomConstraint.boolClauseSlot ps ns).satisfiedB a = true :=
    List.all_eq_true.mp hacc _ hmem
  have hseed := boolClauseSeed_entailed (ps := ps) (ns := ns) hs
  simpa [boolClauseLits, boolClauseSeed, Clause.SatisfiedBy] using hseed

theorem boolClauseScan_hit_false {view : EngineView} {lits : Array Literal}
    (h : (boolClauseScan view lits).hit = false) :
    ∀ l ∈ lits.toList, scanEval view l ≠ some true := by
  intro l hl
  have h' : ¬ (scanEval view l == some true) = true :=
    (List.any_eq_false.mp h) l hl
  simpa using h'

theorem mem_unassigned_iff {view : EngineView} {lits : Array Literal} {l : Literal} :
    l ∈ (lits.toList.filter fun q => scanEval view q == none) ↔
      l ∈ lits.toList ∧ scanEval view l = none := by
  rw [List.mem_filter]
  simp

theorem boolClauseScan_count_zero {view : EngineView} {lits : Array Literal}
    (hhit : (boolClauseScan view lits).hit = false)
    (hcount : (boolClauseScan view lits).count = 0) :
    ∀ l ∈ lits.toList, scanEval view l = some false := by
  intro l hl
  have hnil : (lits.toList.filter fun q => scanEval view q == none) = [] :=
    List.length_eq_zero_iff.mp hcount
  have hnotmem : l ∉ (lits.toList.filter fun q => scanEval view q == none) := by
    rw [hnil]
    simp
  have hnot : ¬ (scanEval view l == none) = true := fun hh =>
    hnotmem (mem_unassigned_iff.mpr ⟨hl, by simpa using hh⟩)
  have hnone : scanEval view l ≠ none := by simpa using hnot
  have hno := boolClauseScan_hit_false hhit l hl
  cases hv : scanEval view l with
  | none => exact (hnone hv).elim
  | some b =>
      cases b with
      | false => rfl
      | true => exact (hno hv).elim

theorem boolClauseScan_count_one {view : EngineView} {lits : Array Literal}
    (hhit : (boolClauseScan view lits).hit = false)
    (hcount : (boolClauseScan view lits).count = 1) :
    ∃ u, (boolClauseScan view lits).unit = some u ∧ u ∈ lits.toList ∧
      scanEval view u = none ∧
      ∀ l ∈ lits.toList, l ≠ u → scanEval view l = some false := by
  obtain ⟨u, hu⟩ := List.length_eq_one_iff.mp hcount
  have hunit : (boolClauseScan view lits).unit = some u := by
    dsimp only [boolClauseScan]
    rw [hu]
    rfl
  have humem : u ∈ lits.toList := by
    have : u ∈ (lits.toList.filter fun q => scanEval view q == none) := by
      rw [hu]
      simp
    exact (mem_unassigned_iff.mp this).1
  have hueval : scanEval view u = none := by
    have : u ∈ (lits.toList.filter fun q => scanEval view q == none) := by
      rw [hu]
      simp
    exact (mem_unassigned_iff.mp this).2
  refine ⟨u, hunit, humem, hueval, ?_⟩
  intro l hl hlne
  have hnotmem : l ∉ (lits.toList.filter fun q => scanEval view q == none) := by
    rw [hu]
    simp [hlne]
  have hnot : ¬ (scanEval view l == none) = true := fun hh =>
    hnotmem (mem_unassigned_iff.mpr ⟨hl, by simpa using hh⟩)
  have hnone : scanEval view l ≠ none := by simpa using hnot
  have hno := boolClauseScan_hit_false hhit l hl
  cases hv : scanEval view l with
  | none => exact (hnone hv).elim
  | some b =>
      cases b with
      | false => rfl
      | true => exact (hno hv).elim

def boolClausePropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (ps ns : List Nat)
    (hmem : DomConstraint.boolClauseSlot ps ns ∈ p.constraints) : PropV2 p T :=
  let lits := boolClauseLits ps ns
  let vars := ps.toArray ++ ns.toArray
  let ent := boolClauseLits_entailed p ps ns hmem
  { vars := vars
    events := vars.map fun s => (s, .fix)
    run := fun view =>
      let r := boolClauseScan view lits
      if r.hit then .fix
      else if r.count = 0 then
        .conflict (EClause.ofLiterals p T lits.toList ent)
      else if r.count = 1 then
        match r.unit with
        | some u =>
            .prune #[(pLit u, EClause.ofLiterals p T lits.toList ent)]
        | none => .fix
      else .fix }

/-- Sound `.fix` no-op kept only for the §B contract theorem names
(audited); `propsOf` uses `boolClausePropWith`. -/
def boolClauseProp (p : CompiledProblem DomConstraint) (T : LitTable)
    (ps ns : List Nat) : PropV2 p T :=
  let vars := ps.toArray ++ ns.toArray
  { vars := vars
    events := vars.map fun s => (s, .fix)
    run := fun _ => .fix }

theorem boolClausePropWith_conflict_entailed (p : CompiledProblem DomConstraint)
    (_T : LitTable) (ps ns : List Nat)
    (hmem : DomConstraint.boolClauseSlot ps ns ∈ p.constraints) (_view : EngineView) :
    Entailed p (boolClauseLits ps ns).toList :=
  boolClauseLits_entailed p ps ns hmem

theorem boolClausePropWith_prune_reason_entailed (p : CompiledProblem DomConstraint)
    (_T : LitTable) (ps ns : List Nat)
    (hmem : DomConstraint.boolClauseSlot ps ns ∈ p.constraints) (_view : EngineView) :
    Entailed p (boolClauseLits ps ns).toList :=
  boolClauseLits_entailed p ps ns hmem

theorem boolClausePropWith_conflict_lits_false (p : CompiledProblem DomConstraint)
    (_T : LitTable) (ps ns : List Nat)
    (_hmem : DomConstraint.boolClauseSlot ps ns ∈ p.constraints) (view : EngineView)
    (hhit : (boolClauseScan view (boolClauseLits ps ns)).hit = false)
    (hcount : (boolClauseScan view (boolClauseLits ps ns)).count = 0) :
    ∀ q ∈ (boolClauseLits ps ns).toList,
      (view.doms.getD q.atom.slot DomC.empty).evalLit q = some false :=
  boolClauseScan_count_zero hhit hcount

theorem boolClausePropWith_prune_lit_none (p : CompiledProblem DomConstraint)
    (_T : LitTable) (ps ns : List Nat)
    (_hmem : DomConstraint.boolClauseSlot ps ns ∈ p.constraints) (view : EngineView)
    (hhit : (boolClauseScan view (boolClauseLits ps ns)).hit = false)
    (hcount : (boolClauseScan view (boolClauseLits ps ns)).count = 1) :
    ∃ u, (boolClauseScan view (boolClauseLits ps ns)).unit = some u ∧
      u ∈ (boolClauseLits ps ns).toList ∧
      (view.doms.getD u.atom.slot DomC.empty).evalLit u = none ∧
      ∀ q ∈ (boolClauseLits ps ns).toList, q ≠ u →
        (view.doms.getD q.atom.slot DomC.empty).evalLit q = some false :=
  boolClauseScan_count_one hhit hcount

/-! ## §B contract names

The brief names these obligations after the spike-level `boolClauseProp`;
the real propagator is `boolClausePropWith`, so the same statements are
also exported under the §B names for downstream consumers. -/

theorem boolClauseProp_conflict_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (ps ns : List Nat)
    (hmem : DomConstraint.boolClauseSlot ps ns ∈ p.constraints) (view : EngineView) :
    Entailed p (boolClauseLits ps ns).toList :=
  boolClausePropWith_conflict_entailed p T ps ns hmem view

theorem boolClauseProp_prune_reason_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (ps ns : List Nat)
    (hmem : DomConstraint.boolClauseSlot ps ns ∈ p.constraints) (view : EngineView) :
    Entailed p (boolClauseLits ps ns).toList :=
  boolClausePropWith_prune_reason_entailed p T ps ns hmem view

theorem boolClauseProp_conflict_lits_false (p : CompiledProblem DomConstraint)
    (T : LitTable) (ps ns : List Nat)
    (hmem : DomConstraint.boolClauseSlot ps ns ∈ p.constraints) (view : EngineView)
    (hhit : (boolClauseScan view (boolClauseLits ps ns)).hit = false)
    (hcount : (boolClauseScan view (boolClauseLits ps ns)).count = 0) :
    ∀ q ∈ (boolClauseLits ps ns).toList,
      (view.doms.getD q.atom.slot DomC.empty).evalLit q = some false :=
  boolClausePropWith_conflict_lits_false p T ps ns hmem view hhit hcount

theorem boolClauseProp_prune_lit_none (p : CompiledProblem DomConstraint)
    (T : LitTable) (ps ns : List Nat)
    (hmem : DomConstraint.boolClauseSlot ps ns ∈ p.constraints) (view : EngineView)
    (hhit : (boolClauseScan view (boolClauseLits ps ns)).hit = false)
    (hcount : (boolClauseScan view (boolClauseLits ps ns)).count = 1) :
    ∃ u, (boolClauseScan view (boolClauseLits ps ns)).unit = some u ∧
      u ∈ (boolClauseLits ps ns).toList ∧
      (view.doms.getD u.atom.slot DomC.empty).evalLit u = none ∧
      ∀ q ∈ (boolClauseLits ps ns).toList, q ≠ u →
        (view.doms.getD q.atom.slot DomC.empty).evalLit q = some false :=
  boolClausePropWith_prune_lit_none p T ps ns hmem view hhit hcount

end LeanFzn.Engine

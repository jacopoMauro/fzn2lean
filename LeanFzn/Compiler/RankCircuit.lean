/-
File: LeanFzn/Compiler/RankCircuit.lean

Purpose:
  The T2 rank-decomposition front end (PLAN.md phase 5).  Gecode
  flattens `circuit` into an element row over a rank array plus reified
  successor rows.  This module separates an UNTRUSTED recognizer
  (`recognizeRankCircuit`) from a VERIFIED checker
  (`checkRankCircuit`): the recognizer proposes a `RankCert`, and the
  checker replays it against the compiled `DomConstraint` rows.  Soundness
  proofs live in `LeanFzn/Engine/Proofs/RankCircuit.lean`.

  The certificate records, for every node `i` (0-based), the predecessor
  slot and the result slot of the element row, and for non-folded nodes
  the three reification slots.  A folded node (the `rank = 1` entry that
  Gecode constant-folds) is checked by its singleton domains instead.

  The checker's condition is a plain `Prop` (`RankCert.WellFormed`) and
  `checkRankCircuit` is `decide` of it, so the proof layer can consume the
  condition directly.

Dependencies:
  - LeanFzn.Compiler.Compile: `CompiledProblem`, `DomConstraint`, `Dom`.

DAG:
  LeanFzn.Compiler.Compile -> LeanFzn.Compiler.RankCircuit
-/
import LeanFzn.Compiler.Compile
import LeanFzn.Solver.Propagation.Encoding

namespace LeanFzn.Compiler
open LeanFzn.Semantics
open LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

/-! ## Certificates -/

/-- One unit of a Gecode rank decomposition.  `folded` marks the
    constant-folded entry: its rank and result slots are pinned by
    singleton domains instead of the reified rows. -/
structure RankUnit where
  /-- The predecessor slot (`pred_i`). -/
  pred : Nat
  /-- The per-row pin slot carrying the constant `rank[1] = 1`. -/
  pin : Nat
  /-- The result slot of the element row (`rank[pred_i]`). -/
  y : Nat
  /-- Reification slot of `rank_i = n`. -/
  b1 : Nat
  /-- Reification slot of `y_i = 1`. -/
  b2 : Nat
  /-- Reification slot of `y_i - rank_i = 1`. -/
  b3 : Nat
  /-- `true` for the constant-folded entry. -/
  folded : Bool
  deriving Repr, DecidableEq, Inhabited

/-- A proposed rank decomposition: `n` nodes, the rank-slot array and
    the `n` units in node order. -/
structure RankCert where
  /-- Number of nodes. -/
  n : Nat
  /-- Rank slots, in node order. -/
  ranks : List Nat
  /-- One unit per node, in node order. -/
  units : List RankUnit
  deriving Repr, DecidableEq, Inhabited

/-! ## Domain predicates -/

/-- Every integer in the domain is in `1..n`.  A domain with a
    non-integer value fails. -/
def domInRange1B (n : Nat) (d : Dom) : Bool :=
  d.enum.all fun v =>
    match v with
    | .int k => decide (1 ≤ k ∧ k ≤ (n : Int))
    | _ => false

/-- The domain is the singleton `{k}`. -/
def domIsIntB (d : Dom) (k : Int) : Bool :=
  decide (d.enum = [.int k])

theorem domInRange1B_spec {n : Nat} {d : Dom}
    (h : domInRange1B n d = true) {v : Value} (hv : v ∈ d) :
    ∃ k : Int, v = .int k ∧ 1 ≤ k ∧ k ≤ (n : Int) := by
  have hvenum : v ∈ d.enum := (DomainLike.mem_iff d v).mp hv
  have hall := List.all_eq_true.mp h v hvenum
  cases v with
  | int k =>
      exact ⟨k, rfl, of_decide_eq_true hall⟩
  | bool _ => simp at hall
  | setOfInt _ => simp at hall
  | array _ => simp at hall

theorem domIsIntB_spec {d : Dom} {k : Int}
    (h : domIsIntB d k = true) {v : Value} (hv : v ∈ d) : v = .int k := by
  have hvenum : v ∈ d.enum := (DomainLike.mem_iff d v).mp hv
  have heq : d.enum = [.int k] := of_decide_eq_true h
  rw [heq] at hvenum
  exact List.mem_singleton.mp hvenum

/-! ## The checker -/

/-- The local condition of one unit.  The first component is the rank
    slot's `1..n` domain restriction; the second is the element row.  A
    folded unit is checked by its two singleton pins; every other unit
    by the five reified rows. -/
abbrev RankUnit.OK (p : CompiledProblem DomConstraint) (n : Nat)
    (ranks : List Nat) (i : Nat) (u : RankUnit) : Prop :=
  ranks[i]! < p.domains.length ∧
  u.pred < p.domains.length ∧
  u.pin < p.domains.length ∧
  u.y < p.domains.length ∧
  domInRange1B n (p.domains.getD (ranks[i]!) Dom.empty) = true ∧
  domIsIntB (p.domains.getD u.pin Dom.empty) 1 = true ∧
  (DomConstraint.arrayVarIntElementSlot (u.pin :: ranks.tail) u.pred u.y ∈ p.constraints) ∧
  (u.folded = true →
    domIsIntB (p.domains.getD (ranks[i]!) Dom.empty) 1 = true ∧
    domIsIntB (p.domains.getD u.y Dom.empty) 2 = true) ∧
  (u.folded = false →
    DomConstraint.linEqReif [1] [ranks[i]!] (n : Int) u.b1 ∈ p.constraints ∧
    DomConstraint.linEqReif [1] [u.y] 1 u.b2 ∈ p.constraints ∧
    DomConstraint.linEqReif [1, -1] [u.y, ranks[i]!] 1 u.b3 ∈ p.constraints ∧
    DomConstraint.boolClauseSlot [u.b2] [u.b1] ∈ p.constraints ∧
    DomConstraint.boolClauseSlot [u.b1, u.b3] [] ∈ p.constraints)

/-- The checked certificate condition.  `n > 2` is the range in which
    the two-cycle exclusion is needed; the rank circuit's own models all
    have far more nodes.  The predecessor slots must be pairwise
    distinct: this rejects a model in which one element row was
    retargeted to an existing predecessor slot, which would otherwise be
    re-recognized as a different (but well-formed) rank decomposition. -/
abbrev RankCert.WellFormed (p : CompiledProblem DomConstraint) (c : RankCert) : Prop :=
  2 < c.n ∧
  c.ranks.length = c.n ∧
  c.units.length = c.n ∧
  c.ranks[0]! = (c.units[0]!).pin ∧
  (List.range c.n).all
    (fun i => decide (RankUnit.OK p c.n c.ranks i c.units[i]!)) = true ∧
  (c.units.map (fun u => u.pred)).Nodup

/-- The verified replay of a proposed rank decomposition. -/
def checkRankCircuit (p : CompiledProblem DomConstraint) (c : RankCert) : Bool :=
  decide (c.WellFormed p)

theorem checkRankCircuit_spec {p : CompiledProblem DomConstraint} {c : RankCert}
    (h : checkRankCircuit p c = true) : c.WellFormed p :=
  of_decide_eq_true h

/-- Per-unit extraction from the checked certificate. -/
theorem checkRankCircuit_unit {p : CompiledProblem DomConstraint} {c : RankCert}
    (h : checkRankCircuit p c = true) {i : Nat} (hi : i ∈ List.range c.n) :
    RankUnit.OK p c.n c.ranks i c.units[i]! := by
  have hwf := checkRankCircuit_spec h
  exact of_decide_eq_true (List.all_eq_true.mp hwf.2.2.2.2.1 i hi)

theorem checkRankCircuit_n {p : CompiledProblem DomConstraint} {c : RankCert}
    (h : checkRankCircuit p c = true) : 2 < c.n :=
  (checkRankCircuit_spec h).1

theorem checkRankCircuit_ranks_length {p : CompiledProblem DomConstraint} {c : RankCert}
    (h : checkRankCircuit p c = true) : c.ranks.length = c.n :=
  (checkRankCircuit_spec h).2.1

theorem checkRankCircuit_units_length {p : CompiledProblem DomConstraint} {c : RankCert}
    (h : checkRankCircuit p c = true) : c.units.length = c.n :=
  (checkRankCircuit_spec h).2.2.1

theorem checkRankCircuit_align {p : CompiledProblem DomConstraint} {c : RankCert}
    (h : checkRankCircuit p c = true) : c.ranks[0]! = (c.units[0]!).pin :=
  (checkRankCircuit_spec h).2.2.2.1

/-- The checked certificate's predecessor slots are pairwise distinct. -/
theorem checkRankCircuit_preds_nodup {p : CompiledProblem DomConstraint} {c : RankCert}
    (h : checkRankCircuit p c = true) :
    (c.units.map (fun u => u.pred)).Nodup :=
  (checkRankCircuit_spec h).2.2.2.2.2

/-! ## The untrusted recognizer -/

/-- The distinct element-row tails (the elements after the pinned
    `rank[1]` entry) appearing in the compiled problem, in reverse
    constraint order.  The compiler rewrites each occurrence of the
    literal `rank[1] = 1` to a fresh pinned aux slot, so the rows differ
    in their head slot but share the tail. -/
def rankTails (p : CompiledProblem DomConstraint) : List (List Nat) :=
  p.constraints.foldl
    (fun acc dc =>
      match dc with
      | .arrayVarIntElementSlot is _ _ =>
          let tail := is.tail
          if tail.isEmpty || acc.contains tail then acc else tail :: acc
      | _ => acc) []

/-- The element rows whose tail is exactly `tail`, in constraint order,
    together with each row's pinned head slot. -/
def elemRowsFor (p : CompiledProblem DomConstraint) (tail : List Nat) :
    List (Nat × Nat × Nat) :=
  p.constraints.filterMap fun dc =>
    match dc with
    | .arrayVarIntElementSlot is' x y =>
        if is'.tail = tail then
          match is'.head? with
          | some pin => some (pin, x, y)
          | none => none
        else none
    | _ => none

/-- Find the reification slot of `rank_i = n`. -/
def findB1 (p : CompiledProblem DomConstraint) (r : Nat) (n : Nat) : Option Nat :=
  p.constraints.findSome? fun dc =>
    match dc with
    | .linEqReif [1] [r'] b rslot =>
        if r' = r && b = (n : Int) then some rslot else none
    | _ => none

/-- Find the reification slot of `y_i = 1`. -/
def findB2 (p : CompiledProblem DomConstraint) (y : Nat) : Option Nat :=
  p.constraints.findSome? fun dc =>
    match dc with
    | .linEqReif [1] [y'] b rslot =>
        if y' = y && b = 1 then some rslot else none
    | _ => none

/-- Find the reification slot of `y_i - rank_i = 1`. -/
def findB3 (p : CompiledProblem DomConstraint) (y r : Nat) : Option Nat :=
  p.constraints.findSome? fun dc =>
    match dc with
    | .linEqReif [1, -1] [y', r'] b rslot =>
        if y' = y && r' = r && b = 1 then some rslot else none
    | _ => none

/-- Build the units from the element rows, in row order.  The first row
    is treated as the constant-folded unit; recognition is untrusted, so
    a wrong guess is simply refused by the checker. -/
def unitsOf (p : CompiledProblem DomConstraint) (n : Nat) (ranks : List Nat)
    (rows : List (Nat × Nat × Nat)) : List RankUnit :=
  rows.mapIdx fun i rxy =>
    let pin := rxy.1
    let x := rxy.2.1
    let y := rxy.2.2
    if i = 0 then
      ⟨x, pin, y, 0, 0, 0, true⟩
    else
      let r := ranks[i]!
      ⟨x, pin, y, (findB1 p r n).getD 0, (findB2 p y).getD 0,
        (findB3 p y r).getD 0, false⟩

/-- The untrusted recognizer.  It only proposes; `checkRankCircuit` decides. -/
def recognizeRankCircuit (p : CompiledProblem DomConstraint) : Option RankCert :=
  (rankTails p).findSome? fun tail =>
    let n := tail.length + 1
    if 2 < n then
      let rows := elemRowsFor p tail
      match rows with
      | [] => none
      | (pin, _, _) :: _ =>
          let ranks := pin :: tail
          if decide ranks.Nodup &&
              ranks.all (fun r => domInRange1B n (p.domains.getD r Dom.empty)) then
            if rows.length = n then
              some ⟨n, ranks, unitsOf p n ranks rows⟩
            else none
          else none
    else none

/-! ## Seed clauses -/

/-- Every pair of distinct nodes contributes the binary clause
    `pred_i ≠ j ∨ pred_j ≠ i`, excluding the 2-cycle `i ↔ j`. -/
def rankCircuitClauses (c : RankCert) : List Clause :=
  (List.range c.n).flatMap fun i =>
    ((List.range c.n).filter (fun j => decide (i < j))).map fun j =>
      [posNe (c.units[i]!).pred (((j + 1 : Nat) : Int)),
       posNe (c.units[j]!).pred (((i + 1 : Nat) : Int))]

/-- The clauses contributed by a checked rank decomposition, or none. -/
def rankCircuitSeeds (p : CompiledProblem DomConstraint) : List Clause :=
  match recognizeRankCircuit p with
  | some c => if checkRankCircuit p c then rankCircuitClauses c else []
  | none => []

/-- Membership inversion for the generated clauses. -/
theorem rankCircuitClauses_mem_inv {c : RankCert} {cl : Clause}
    (h : cl ∈ rankCircuitClauses c) :
    ∃ i j, i ∈ List.range c.n ∧ j ∈ List.range c.n ∧ i < j ∧
      cl = [posNe (c.units[i]!).pred ((j : Int) + 1),
            posNe (c.units[j]!).pred ((i : Int) + 1)] := by
  unfold rankCircuitClauses at h
  rw [List.mem_flatMap] at h
  obtain ⟨i, hi, hmap⟩ := h
  rw [List.mem_map] at hmap
  obtain ⟨j, hj, rfl⟩ := hmap
  rw [List.mem_filter] at hj
  exact ⟨i, j, hi, hj.1, of_decide_eq_true hj.2, rfl⟩

/-- Membership inversion for the seed list: either the recognizer failed
    or its proposal passed the checker. -/
theorem rankCircuitSeeds_mem_inv {p : CompiledProblem DomConstraint} {cl : Clause}
    (h : cl ∈ rankCircuitSeeds p) :
    ∃ c : RankCert, recognizeRankCircuit p = some c ∧
      checkRankCircuit p c = true ∧ cl ∈ rankCircuitClauses c := by
  unfold rankCircuitSeeds at h
  split at h
  · rename_i c hrec
    split at h
    · rename_i hchk
      exact ⟨c, hrec, hchk, h⟩
    · simp at h
  · simp at h

end LeanFzn.Compiler

/-
Purpose: the two search-frame representations.

  * `PrefixFrame` — the positional frame `(remaining domains, chosen prefix)`;
    the chronological/reference cone keeps this representation (M2 rename).
  * `BranchFrame` — the sparse scheduled frame (S0-decision-design.md §3.1):
    the full per-slot box `doms` plus the decision order `order`; the
    scheduled cone uses this representation (M2 switch).

Dependencies: Core.Types supplies domains, assignments and verdicts.
DAG: Core.Types -> Frontier -> Engine; Proofs.Frontier proves coverage/progress.
-/
import LeanFzn.Solver.Core.Types
open LeanFzn.Semantics


namespace LeanFzn.Solver.Propagation
open LeanFzn.Solver.Core
open LeanFzn LeanFzn.Solver.Core

/-! ## The positional frame (chronological/reference cone)

`PrefixFrame` is the `(remaining, chosen)` pair: the pending domains of a
subtree and the already selected prefix, in problem slot order. It is the
representation of `frontierSolve` below and of the chronological/reference
search; the scheduled cone moved to the sparse `BranchFrame` (M2). -/

abbrev PrefixFrame := List Domain × Assignment

/-! ## The decreasing measure

`branchCost` counts the transitions needed to exhaust a frame when no
leaf succeeds; `frontierCost` sums it over the pending stack. Every
nonterminal transition of the positional chronological traversal decreases
`frontierCost` by exactly one, which is the well-founded measure of the
fuel-free driver below. The measure lives only in the termination
proof; the executable never computes it. -/

/-- Number of transitions needed to exhaust a frame when no leaf succeeds. -/
def branchCost : List Domain → Nat
  | [] => 1
  | d :: rest => 1 + d.length * (branchCost rest + 1)

/-- A finite measure of all pending positional work. Every nonterminal
    transition decreases it by exactly one, including consuming an exhausted
    sibling. -/
def frontierCost (pending : List PrefixFrame) : Nat :=
  (pending.map fun f => branchCost f.1).sum

/-- Every frame has a positive cost. -/
theorem branchCost_pos (slots : List Domain) : 0 < branchCost slots := by
  cases slots <;> simp [branchCost]; omega

/-- Popping a frame strictly decreases the frontier cost. -/
theorem frontierCost_cons (f : PrefixFrame) (pending : List PrefixFrame) :
    frontierCost pending < frontierCost (f :: pending) := by
  have hp := branchCost_pos f.1
  simp only [frontierCost, List.map_cons, List.sum_cons]
  omega

/-- The expansion transition of a nonempty next domain: pushing the
    selected child's frame and the sibling frame costs exactly one more
    than the parent frame it replaces.  The sibling is the compact
    domain of the remaining enumeration `vs`. -/
theorem frontierCost_expand (v : Value) (vs : List Value) (d : Domain)
    (hd : d.enum = v :: vs) (rest : List Domain)
    (chosen : Assignment) (pending : List PrefixFrame) :
    frontierCost ((rest, chosen ++ [v]) :: (Dom.ofList vs :: rest, chosen) :: pending) + 1
      = frontierCost ((d :: rest, chosen) :: pending) := by
  simp only [frontierCost, List.map_cons, List.sum_cons]
  have h1 : branchCost (Dom.ofList vs :: rest) = 1 + vs.length * (branchCost rest + 1) := by
    simp [branchCost, Dom.length, Dom.card_eq_length_enum, Dom.enum_ofList]
  have h2 : branchCost (d :: rest) = 1 + (vs.length + 1) * (branchCost rest + 1) := by
    simp [branchCost, Dom.length, Dom.card_eq_length_enum, hd]
  rw [h1, h2]
  have hpos : 0 < branchCost rest + 1 := by omega
  have hsplit : (vs.length + 1) * (branchCost rest + 1)
      = vs.length * (branchCost rest + 1) + (branchCost rest + 1) := by
    rw [Nat.succ_mul]
  omega

/-! ## The fuel-free positional traversal

`frontierSolve` is the total, kernel-checked chronological traversal.
Termination is by `frontierCost pending`; the measure is proof-only
(erased in compiled code), so the executable carries no search budget,
default fuel, timeout or iteration counter. The result is an internal
two-constructor verdict: a satisfying assignment, or `unsat`. -/

/-- The internal verdict of the fuel-free traversal: either a witness
    that passed the leaf predicate, or exhaustion of the whole frontier
    (no represented assignment satisfies the leaf). -/
inductive FrontierResult where
  /-- A complete assignment that passed the leaf predicate. -/
  | sat (a : Assignment)
  /-- Every represented assignment failed the leaf predicate. -/
  | unsat

/-- The fuel-free chronological traversal of the pending-positional stack.
    Empty stack: UNSAT. Complete prefix: test the leaf. Empty next
    domain: drop the exhausted frame. Nonempty next domain: explore the
    selected value's child, then the unused siblings, then the tail. -/
def frontierSolve (leaf : Assignment → Bool) (pending : List PrefixFrame) :
    FrontierResult :=
  match pending with
  | [] => .unsat
  | (slots, chosen) :: rest =>
      match slots with
      | [] => if leaf chosen then .sat chosen else frontierSolve leaf rest
      | d :: doms =>
          match hd : d.enum with
          | [] => frontierSolve leaf rest
          | v :: vs =>
              frontierSolve leaf
                ((doms, chosen ++ [v]) :: (Dom.ofList vs :: doms, chosen) :: rest)
termination_by frontierCost pending
decreasing_by
  · -- popping a frame
    simp_wf
    exact frontierCost_cons _ _
  · -- dropping an exhausted frame
    simp_wf
    exact frontierCost_cons _ _
  · -- expansion: the two pushed frames cost one more than the parent
    simp_wf
    have h := frontierCost_expand v vs d hd doms chosen rest
    omega

/-- The historical fuel-bounded traversal, retained as an explicitly
    named diagnostic reference. It is NOT the driver: the public path
    uses `frontierSolve`. Fuel exhaustion reports `unknown`. -/
def frontierSearch (leaf : Assignment → Bool) : Nat → List PrefixFrame → SearchResult
  | _, [] => .unsat
  | 0, _ :: _ => .unknown
  | fuel + 1, (slots, chosen) :: pending =>
      match slots with
      | [] => if leaf chosen then .sat chosen else frontierSearch leaf fuel pending
      | d :: rest =>
          match d.enum with
          | [] => frontierSearch leaf fuel pending
          | v :: vs =>
              frontierSearch leaf fuel
                ((rest, chosen ++ [v]) :: (Dom.ofList vs :: rest, chosen) :: pending)

/-! ## The sparse scheduled frame (S0 §3.1, §3.3)

`BranchFrame` is the S0 arbitrary-slot frame: the full per-slot box (`doms`,
indexed by the ORIGINAL slot number; decided slots hold their singleton) and
the decision order (`order`, decided slots oldest-first; level `L` decided
`order[L-1]`). The scheduled cone uses this representation from M2 on; the
prototype `DecisionProto.Frame` aliases this structure, so the S0/S1 theorems
apply to it directly. -/

/-- The S0 sparse search frame. -/
structure BranchFrame where
  /-- Full per-slot box; decided slots hold their singleton domain. -/
  doms : List Domain
  /-- Decided slots, oldest first; level `L` decided `order[L-1]`. -/
  order : List Nat
deriving Repr, Inhabited, BEq

/-- The frame's current decision level: the number of decisions. -/
def BranchFrame.level (f : BranchFrame) : Nat := f.order.length

/-- Pin the selected slot `k` to `v`: the decision child. -/
def BranchFrame.pin (f : BranchFrame) (k : Nat) (v : Value) : BranchFrame :=
  { doms := f.doms.set k (Dom.ofList [v]), order := f.order ++ [k] }

/-- Retire the value `v` from slot `k`: the sibling alternative. -/
def BranchFrame.retire (f : BranchFrame) (k : Nat) (vs : Domain) : BranchFrame :=
  { f with doms := f.doms.set k vs }

@[simp] theorem BranchFrame.pin_doms (f : BranchFrame) (k : Nat) (v : Value) :
    (f.pin k v).doms = f.doms.set k (Dom.ofList [v]) := rfl

@[simp] theorem BranchFrame.pin_order (f : BranchFrame) (k : Nat) (v : Value) :
    (f.pin k v).order = f.order ++ [k] := rfl

@[simp] theorem BranchFrame.retire_doms (f : BranchFrame) (k : Nat) (vs : Domain) :
    (f.retire k vs).doms = f.doms.set k vs := rfl

@[simp] theorem BranchFrame.retire_order (f : BranchFrame) (k : Nat) (vs : Domain) :
    (f.retire k vs).order = f.order := rfl

/-- A decision opens exactly one new level. -/
theorem BranchFrame.level_pin (f : BranchFrame) (k : Nat) (v : Value) :
    (f.pin k v).level = f.level + 1 := by
  simp [BranchFrame.level, BranchFrame.pin]

/-- A retirement keeps the level. -/
theorem BranchFrame.level_retire (f : BranchFrame) (k : Nat) (vs : Domain) :
    (f.retire k vs).level = f.level := rfl

/-! ## The read-back of a fully decided box (S0 §3.6) -/

private def assignmentAux : List Domain → Option Assignment
  | [] => some []
  | d :: rest =>
      match d.enum with
      | [] => none
      | [v] => (assignmentAux rest).map fun pre => v :: pre
      | _ => none

/-- RUNTIME READ-BACK (S0 §3.6): the complete assignment of a fully decided
    box — every singleton domain read at its own (original) index; `none` when
    some domain is not a (nonempty) singleton. -/
def BranchFrame.assignment? (f : BranchFrame) : Option Assignment :=
  assignmentAux f.doms

private theorem assignmentAux_eq_some_iff (l : List Domain) (pre : Assignment) :
    assignmentAux l = some pre ↔ l.map Dom.enum = pre.map (fun v => [v]) := by
  induction l generalizing pre with
  | nil =>
      simp only [assignmentAux, List.map_nil]
      constructor
      · intro h; simpa using h
      · intro h; simpa using h.symm
  | cons d rest ih =>
      cases hd : d.enum with
      | nil =>
          simp only [assignmentAux, hd, List.map_cons]
          constructor
          · intro h; cases h
          · intro h
            cases pre with
            | nil => simp at h
            | cons p ps => simp at h
      | cons v vs =>
          cases vs with
          | nil =>
              simp only [assignmentAux, hd, List.map_cons,
                Option.map_eq_some_iff]
              constructor
              · rintro ⟨pre', hpre', hpre⟩
                rw [← hpre, (ih pre').mp hpre']
                rfl
              · intro h
                cases pre with
                | nil => simp at h
                | cons p ps =>
                    simp only [List.map_cons, List.cons.injEq, List.nil_eq,
                      and_true] at h
                    obtain ⟨hp, hps⟩ := h
                    subst hp
                    exact ⟨ps, (ih ps).mpr hps, rfl⟩
          | cons w ws =>
              simp only [assignmentAux, hd]
              constructor
              · intro h; cases h
              · intro h
                cases pre with
                | nil => simp at h
                | cons p ps =>
                    simp only [List.map_cons, List.map_nil, List.cons.injEq,
                      List.nil_eq, and_true] at h
                    rw [hd] at h
                    simp at h

/-- Exact characterization of the read-back: a frame reads back the exact
assignment when the enumeration of every domain is its singleton. -/
theorem BranchFrame.assignment?_eq_some_iff (f : BranchFrame) (w : Assignment) :
    f.assignment? = some w ↔ f.doms.map Dom.enum = w.map (fun v => [v]) :=
  assignmentAux_eq_some_iff f.doms w

/-- S0 §3.1 `PinsAgree`: a (covered) assignment reads the recorded value at
every singleton slot — in particular at every decided slot. This replaces
the positional `f.2 <+: a` prefix test in the scheduled cone. -/
def Frame.PinsAgree (f : BranchFrame) (a : Assignment) : Prop :=
  ∀ (k : Nat) (v : Value), f.doms[k]?.map Dom.enum = some [v] → a[k]? = some v

/-! ## Sparse progress measures (S0 §3.5)

The scheduled cone's termination measure: `Frame.cost` (the shared
`branchCost` read on the full box), the per-frame weight `3 ^ cost` and the
frontier weight summing it over the pending stack. These replace the
positional `frontierCost` in the scheduled rank; the strict decrease on
splits is `frontierWeight_split_lt` (M5). -/

/-- Sparse frame cost: the shared `branchCost` read on the full box. -/
def Frame.cost (f : BranchFrame) : Nat := branchCost f.doms

/-- Per-frame frontier weight (S0 §3.5): `3 ^ cost`. -/
def frameWeight (f : BranchFrame) : Nat := 3 ^ Frame.cost f

/-- Frontier weight (S0 §3.5): the sum of the per-frame weights. -/
def frontierWeight (pending : List BranchFrame) : Nat :=
  (pending.map frameWeight).sum

/-- Every frame has positive weight. -/
theorem frameWeight_pos (f : BranchFrame) : 0 < frameWeight f :=
  show 0 < 3 ^ Frame.cost f from
    Nat.pow_pos (a := 3) (n := Frame.cost f) (by decide)

/-- Pushing a frame strictly increases the frontier weight. -/
theorem frontierWeight_cons (f : BranchFrame) (pending : List BranchFrame) :
    frontierWeight pending < frontierWeight (f :: pending) := by
  simp only [frontierWeight, List.map_cons, List.sum_cons]
  exact Nat.lt_add_of_pos_left (frameWeight_pos f)

end LeanFzn.Solver.Propagation

/-
File: LeanFzn/Solver/Chronological/AnalysisDriver.lean

Purpose:
  The integrated driver. It extends the certified chronological
  frontier with *nonchronological pruning of survivors*: after a branch
  completes (excluded by a conflict, exhausted, or failing the leaf
  test) the remaining pending frames are filtered against the learned
  clause database, dropping exactly those whose chosen prefix already
  falsifies an entailed clause.

  This is the plan's preferred termination design — "schedule surviving
  existing frames and prune them with the new clause" — chosen over
  ancestor reconstruction because it keeps the measure
  `frontierCost` strictly decreasing: a completed frame is dropped
  (`frontierCost_cons`), a split child is strictly cheaper
  (`frontierCost_expand`), and pruning only removes frames, so it never
  increases the measure. No fuel and no restart counter is involved.

  The pruning test is the P1.C/P1.D exclusion contract made
  executable: a frame is refuted when every literal whose slot the
  chosen prefix decides is false there — the coordinates on which the
  clause is *already* falsified. Undecided slots leave the frame
  retained, so pruning never guesses.

Dependencies:
  - LeanFzn.Solver.Chronological.Pruned: the certified kit interface and `Refinement`.
  - LeanFzn.Solver.Propagation.FrameFilter: `Literal.valueHolds`, `PrefixCovers`.
  - LeanFzn.Solver.Propagation.FrontierSemantics: `PrefixCovers`, frame splitting.

DAG:
  Pruned + FrameFilter + FrontierSemantics -> AnalysisDriver
  -> Proofs.AnalysisDriver -> public certification.
-/

import LeanFzn.Legacy.Solver.Chronological.Pruned
import LeanFzn.Legacy.Solver.Propagation.ClausePropagation
open LeanFzn.Semantics LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological


namespace LeanFzn.Solver.Chronological
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-! ## Prefix refutation -/

/-- Does the chosen prefix alone falsify `clause`? A literal whose slot
is already decided is checked at its chosen value; a literal whose slot
is still open cannot refute, so the frame is retained. -/
def refutedBy (clause : Clause) (f : PrefixFrame) : Bool :=
  clause.all fun l =>
    match f.2[l.atom.slot]? with
    | some v => !l.valueHolds v
    | none => false

/-- Does any clause of the database refute the frame? -/
def refutedByDB (db : List Clause) (f : PrefixFrame) : Bool :=
  db.any fun c => refutedBy c f

/-- Drop the pending frames already refuted by the learned database.
This is the nonchronological step: it needs no trail restoration and no
ancestor reconstruction, and it only deletes frames that cannot carry a
leaf solution (see `pruneFrames_preserves`). -/
def pruneFrames (db : List Clause) (pending : List PrefixFrame) :
    List PrefixFrame :=
  pending.filter fun f => !refutedByDB db f

/-! ## The integrated driver -/

/-- `frontierCost` is monotone in the pending tail. -/
theorem frontierCost_append_le {xs ys zs : List PrefixFrame}
    (h : frontierCost ys ≤ frontierCost zs) :
    frontierCost (xs ++ ys) ≤ frontierCost (xs ++ zs) := by
  induction xs with
  | nil => simpa using h
  | cons f rest ih =>
      simp only [List.cons_append, frontierCost, List.map_cons, List.sum_cons]
      exact Nat.add_le_add_left ih _

/-- Pruning never increases the frontier cost: it only removes frames. -/
theorem frontierCost_prune_le (db : List Clause)
    (pending : List PrefixFrame) :
    frontierCost (pruneFrames db pending) ≤ frontierCost pending := by
  induction pending with
  | nil => simp [pruneFrames]
  | cons f rest ih =>
      by_cases h : refutedByDB db f = true
      · have hfilter : pruneFrames db (f :: rest) = pruneFrames db rest :=
          List.filter_cons_of_neg (p := fun x => !refutedByDB db x)
            (a := f) (l := rest) (by simp [h])
        rw [hfilter]
        have hrest : frontierCost (pruneFrames db rest) ≤ frontierCost rest := ih
        simp only [frontierCost, List.map_cons, List.sum_cons] at hrest ⊢
        have hpos := branchCost_pos f.1
        omega
      · have hp : ((fun x => !refutedByDB db x) f) = true := by
          cases href : refutedByDB db f <;> simp_all
        have hfilter : pruneFrames db (f :: rest)
            = f :: pruneFrames db rest :=
          List.filter_cons_of_pos (p := fun x => !refutedByDB db x)
            (a := f) (l := rest) hp
        rw [hfilter]
        have hrest : frontierCost (pruneFrames db rest) ≤ frontierCost rest := ih
        simp only [frontierCost, List.map_cons, List.sum_cons] at hrest ⊢
        omega

/-- The split step with pruning still strictly decreases the measure:
the two children are pushed in front of the *pruned* survivors, whose
cost is at most the unpruned tail's. -/
theorem frontierCost_prune_expand (db : List Clause) (f : PrefixFrame)
    (v : Value) (vs : List Value) (d : Domain) (hd : d.enum = v :: vs)
    (doms : List Domain) (chosen : Assignment)
    (rest : List PrefixFrame)
    (h : branchCost (d :: doms) ≤ branchCost f.1) :
    frontierCost ((doms, chosen ++ [v]) ::
        (Dom.ofList vs :: doms, chosen) :: pruneFrames db rest)
      < frontierCost (f :: rest) := by
  have hmono := frontierCost_append_le (ys := pruneFrames db rest)
    (zs := rest) (xs := [(doms, chosen ++ [v]), (Dom.ofList vs :: doms, chosen)])
    (frontierCost_prune_le db rest)
  have hlt := refined_expand_lt f v vs d hd doms chosen rest h
  exact Nat.lt_of_le_of_lt hmono hlt

/-- The analysed driver: `prunedSolve` with the surviving-prefix prune
applied after every completed branch. Every recursive call is
measure-checked by `frontierCost`; the prune only removes frames, so it
never increases the measure and the driver remains fuel-free. -/
def analyzedSolve (leaf : Assignment → Bool) (kit : PruningKit leaf)
    (pending : List PrefixFrame) (db : List Clause) (stats : SearchStats) :
    FrontierResult × SearchStats :=
  match pending with
  | [] => (.unsat, stats)
  | f :: rest =>
    let r := kit.run f db
    let nextStats := stats.add r.stats
    let nextDB := r.learned ++ db
    let survivors := pruneFrames nextDB rest
    match hg : r.frame with
    | none => analyzedSolve leaf kit survivors nextDB nextStats
    | some p =>
      let slots := p.1
      let chosen := p.2
      match hs : slots with
      | [] =>
        let checked := nextStats.add { checkedLeaves := 1 }
        if leaf chosen then (.sat chosen, checked)
        else analyzedSolve leaf kit survivors nextDB checked
      | d :: doms =>
        match hd : d.enum with
        | [] => analyzedSolve leaf kit survivors nextDB nextStats
        | v :: vs =>
          analyzedSolve leaf kit
            ((doms, chosen ++ [v]) :: (Dom.ofList vs :: doms, chosen) :: survivors)
            nextDB (nextStats.add { decisions := if vs.isEmpty then 0 else 1 })
termination_by frontierCost pending
decreasing_by
  · exact Nat.lt_of_le_of_lt (frontierCost_prune_le nextDB rest)
      (frontierCost_cons f rest)
  · exact Nat.lt_of_le_of_lt (frontierCost_prune_le nextDB rest)
      (frontierCost_cons f rest)
  · exact Nat.lt_of_le_of_lt (frontierCost_prune_le nextDB rest)
      (frontierCost_cons f rest)
  · exact frontierCost_prune_expand nextDB f v vs d hd doms chosen rest
      (by rw [← hs]; exact kit.cost_le f db p hg)

end LeanFzn.Solver.Chronological

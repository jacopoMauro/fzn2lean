/-
Purpose: Fuel-free search with coverage-preserving refinement and a shared entailed clause database.
Dependencies: FrontierSemantics supplies coverage; Operations supplies clause semantics.
DAG: frame semantics -> Pruned -> Proofs.Pruned -> public search proofs.
-/
import LeanFzn.Legacy.Solver.Propagation.PruningTypes
open LeanFzn.Semantics LeanFzn.Solver.Propagation

namespace LeanFzn.Solver.Chronological
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-- Propagation and entailed learning refine each selected branch before its
    chronological split. Exhausted siblings remain in the explicit frontier. -/
def prunedSolve (leaf : Assignment → Bool) (kit : PruningKit leaf)
    (pending : List PrefixFrame) (db : List Clause) (stats : SearchStats) :
    FrontierResult × SearchStats :=
  match pending with
  | [] => (.unsat, stats)
  | f :: rest =>
    let r := kit.run f db
    let nextStats := stats.add r.stats
    let nextDB := r.learned ++ db
    match hg : r.frame with
    | none => prunedSolve leaf kit rest nextDB nextStats
    | some p =>
      let slots := p.1
      let chosen := p.2
      match hs : slots with
      | [] =>
        let checked := nextStats.add { checkedLeaves := 1 }
        if leaf chosen then (.sat chosen, checked)
        else prunedSolve leaf kit rest nextDB checked
      | d :: doms =>
        match hd : d.enum with
        | [] => prunedSolve leaf kit rest nextDB nextStats
        | v :: vs =>
          prunedSolve leaf kit
            ((doms, chosen ++ [v]) :: (Dom.ofList vs :: doms, chosen) :: rest)
            nextDB (nextStats.add { decisions := if vs.isEmpty then 0 else 1 })
termination_by frontierCost pending
decreasing_by
  · exact frontierCost_cons _ _
  · exact frontierCost_cons _ _
  · exact frontierCost_cons _ _
  · exact refined_expand_lt f v vs d hd doms chosen rest
      (by rw [← hs]; exact kit.cost_le f db p hg)

/-- Unrefined traversal, used for generic callers without a specialized kit. -/
def identityPruningKit (leaf : Assignment → Bool) : PruningKit leaf where
  run f _ := { frame := some f }
  cost_le _ _ _ h := by cases h; exact Nat.le_refl _
  preserves f _ _ _ _ hc := ⟨f,rfl,hc⟩
  learns _ _ _ := by intro c hc; cases hc

end LeanFzn.Solver.Chronological

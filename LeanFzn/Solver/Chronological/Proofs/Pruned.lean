/-
Purpose: Prove SAT soundness, UNSAT exclusion and completeness for the pruned frontier.
Dependencies: Pruned supplies the driver and its refinement contracts.
DAG: frame semantics -> Pruned -> Proofs.Pruned -> public search proofs.
-/
import LeanFzn.Solver.Chronological.Pruned
import LeanFzn.Solver.Propagation.Proofs.PruningTypes
open LeanFzn.Semantics LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological

namespace LeanFzn.Solver.Chronological
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core LeanFzn.Solver

theorem prunedSolve_sat_leaf (leaf : Assignment → Bool) (kit : PruningKit leaf)
    (pending : List BranchFrame) (db : List Clause) (stats : SearchStats)
    (a : Assignment) (h : (prunedSolve leaf kit pending db stats).1 = .sat a) :
    leaf a = true := by
  induction pending, db, stats using prunedSolve.induct (leaf := leaf) (kit := kit) <;>
    rw [prunedSolve] at h
  all_goals first | cases h | skip
  all_goals split at h
  all_goals simp_all +zetaDelta
  all_goals rcases (show _ ∧ _ from by assumption) with ⟨hs, hc⟩
  all_goals subst_vars
  all_goals simp_all +zetaDelta

theorem refined_coverage (leaf : Assignment → Bool) (kit : PruningKit leaf)
    (f : BranchFrame) (rest : List BranchFrame) (db : List Clause) (a : Assignment)
    (he : EntailedDB leaf db) (ha : leaf a = true) (hc : FrontierCovers (f::rest) a) :
    (∃ g, (kit.run f db).frame = some g ∧ FrameCovers g a) ∨ FrontierCovers rest a := by
  obtain ⟨g, hg, hcov⟩ := hc
  rcases List.mem_cons.mp hg with rfl | hg
  · exact Or.inl (kit.preserves g db he a ha hcov)
  · exact Or.inr ⟨g,hg,hcov⟩

theorem refined_none_coverage (leaf : Assignment → Bool) (kit : PruningKit leaf)
    (f : BranchFrame) (rest : List BranchFrame) (db : List Clause) (a : Assignment)
    (he : EntailedDB leaf db) (ha : leaf a = true) (hc : FrontierCovers (f::rest) a)
    (hg : (kit.run f db).frame = none) : FrontierCovers rest a := by
  rcases refined_coverage leaf kit f rest db a he ha hc with ⟨g,hg',_⟩ | hc
  · rw [hg] at hg'; cases hg'
  · exact hc

theorem refined_some_coverage (leaf : Assignment → Bool) (kit : PruningKit leaf)
    (f g : BranchFrame) (rest : List BranchFrame) (db : List Clause) (a : Assignment)
    (he : EntailedDB leaf db) (ha : leaf a = true) (hc : FrontierCovers (f::rest) a)
    (hg : (kit.run f db).frame = some g) : FrameCovers g a ∨ FrontierCovers rest a := by
  rcases refined_coverage leaf kit f rest db a he ha hc with ⟨g',hg',hc⟩ | hc
  · rw [hg] at hg'; cases hg'; exact Or.inl hc
  · exact Or.inr hc

theorem prunedSolve_unsat_excludes (leaf : Assignment → Bool) (kit : PruningKit leaf)
    (pending : List BranchFrame) (db : List Clause) (stats : SearchStats)
    (he : EntailedDB leaf db) (h : (prunedSolve leaf kit pending db stats).1 = .unsat) :
    ∀ a, FrontierCovers pending a → leaf a = false := by
  suffices hx : ∀ a, leaf a = true → FrontierCovers pending a → False by
    intro a hc
    cases ha : leaf a
    · rfl
    · exact False.elim (hx a ha hc)
  intro a ha hc
  induction pending, db, stats using prunedSolve.induct (leaf := leaf) (kit := kit) with
  | case1 => obtain ⟨f,hf,_⟩ := hc; cases hf
  | case2 db stats f rest r ns nd hg ih =>
    have hcov := refined_none_coverage leaf kit f rest db a he ha hc hg
    have hn := EntailedDB.append (kit.learns f db he) he
    apply ih hn _ hcov
    rw [prunedSolve] at h
    split at h <;> simp_all +zetaDelta
  | case3 db stats f rest r chosen hg hg' hl =>
    rw [prunedSolve] at h
    split at h <;> simp_all +zetaDelta
    all_goals rcases (show _ ∧ _ from by assumption) with ⟨hs,hc⟩
    all_goals subst_vars
    all_goals simp_all +zetaDelta
  | case4 db stats f rest r ns nd chosen hg checked hl hg' ih =>
    have hcov := refined_some_coverage leaf kit f ([],chosen) rest db a he ha hc hg
    have hrest : FrontierCovers rest a := by
      rcases hcov with ⟨tail,ht,heq⟩ | hc
      · simp [allAssigns] at ht
        subst tail
        simp at heq
        subst a
        exact False.elim (hl ha)
      · exact hc
    apply ih (EntailedDB.append (kit.learns f db he) he) _ hrest
    rw [prunedSolve] at h
    split at h <;> simp_all +zetaDelta
    all_goals rcases (show _ ∧ _ from by assumption) with ⟨hs,hc⟩
    all_goals subst_vars
    all_goals simp_all +zetaDelta
  | case5 db stats f rest r ns nd chosen tail hg hg' ih =>
    have hcov := refined_some_coverage leaf kit f ([]::tail,chosen) rest db a he ha hc hg
    have hrest : FrontierCovers rest a := by
      rcases hcov with ⟨suffix,ht,_⟩ | hc
      · simp [allAssigns] at ht
      · exact hc
    apply ih (EntailedDB.append (kit.learns f db he) he) _ hrest
    rw [prunedSolve] at h
    split at h <;> simp_all +zetaDelta
    all_goals rcases (show _ ∧ _ from by assumption) with ⟨hs,hc⟩
    all_goals subst_vars
    all_goals simp_all +zetaDelta
  | case6 db stats f rest r ns nd chosen v vs doms hg hg' ih =>
    have hcov := refined_some_coverage leaf kit f ((v::vs)::doms,chosen) rest db a he ha hc hg
    have hnext : FrontierCovers ((doms,chosen++[v])::(vs::doms,chosen)::rest) a := by
      rcases hcov with hc | ⟨g,hg,hc⟩
      · rcases (covers_split v vs doms chosen a).mp hc with hc | hc
        · exact ⟨_,List.mem_cons_self,hc⟩
        · exact ⟨_,List.mem_cons_of_mem _ List.mem_cons_self,hc⟩
      · exact ⟨g,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg),hc⟩
    apply ih (EntailedDB.append (kit.learns f db he) he) _ hnext
    rw [prunedSolve] at h
    split at h <;> simp_all +zetaDelta
    all_goals rcases (show _ ∧ _ from by assumption) with ⟨hs,hc⟩
    all_goals subst_vars
    all_goals simp_all +zetaDelta

/-- Every represented satisfying assignment guarantees a SAT verdict. The
    returned witness may differ from the witness supplied to this theorem. -/
theorem prunedSolve_complete (leaf : Assignment → Bool) (kit : PruningKit leaf)
    (pending : List BranchFrame) (db : List Clause) (stats : SearchStats)
    (he : EntailedDB leaf db) (a : Assignment)
    (hc : FrontierCovers pending a) (ha : leaf a = true) :
    ∃ b, (prunedSolve leaf kit pending db stats).1 = .sat b ∧ leaf b = true := by
  cases hr : (prunedSolve leaf kit pending db stats).1 with
  | sat b => exact ⟨b,rfl,prunedSolve_sat_leaf leaf kit pending db stats b hr⟩
  | unsat =>
    have hf := prunedSolve_unsat_excludes leaf kit pending db stats he hr a hc
    rw [ha] at hf
    cases hf

end LeanFzn.Solver.Chronological

/-
Purpose: Prove SAT soundness, UNSAT exclusion and completeness for the pruned frontier.
Dependencies: Pruned supplies the driver and its refinement contracts.
DAG: frame semantics -> Pruned -> Proofs.Pruned -> public search proofs.
-/
import LeanFzn.Legacy.Solver.Chronological.Pruned
import LeanFzn.Legacy.Solver.Propagation.Proofs.PruningTypes
open LeanFzn.Semantics LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological

namespace LeanFzn.Solver.Chronological
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core LeanFzn.Solver

theorem prunedSolve_sat_leaf (leaf : Assignment → Bool) (kit : PruningKit leaf)
    (pending : List PrefixFrame) (db : List Clause) (stats : SearchStats)
    (a : Assignment) (h : (prunedSolve leaf kit pending db stats).1 = .sat a) :
    leaf a = true := by
  induction pending, db, stats using prunedSolve.induct (leaf := leaf) (kit := kit) with
  | case1 =>
    rw [prunedSolve] at h
    cases h
  | case2 db stats f rest r ns nd hg ih =>
    rw [prunedSolve] at h
    rw [hg] at h
    simp only at h
    exact ih h
  | case3 db stats f rest r p hg slots chosen hs hl =>
    rw [prunedSolve] at h
    rw [hg] at h
    simp only at h
    rw [show p.fst = [] from hs] at h
    simp only at h
    rw [show leaf p.snd = true from hl] at h
    simp at h
    subst h
    exact hl
  | case4 db stats f rest r ns nd p hg slots chosen hs checked hl ih =>
    rw [prunedSolve] at h
    rw [hg] at h
    simp only at h
    rw [show p.fst = [] from hs] at h
    simp only at h
    rw [if_neg (show ¬ leaf p.snd = true from hl)] at h
    exact ih h
  | case5 db stats f rest r ns nd p hg slots d doms hs hd ih =>
    rw [prunedSolve] at h
    rw [hg] at h
    simp only at h
    rw [show p.fst = d :: doms from hs] at h
    simp only at h
    rw [show Dom.enum d = [] from hd] at h
    simp only at h
    exact ih h
  | case6 db stats f rest r ns nd p hg slots chosen d doms hs v vs hd ih =>
    rw [prunedSolve] at h
    rw [hg] at h
    simp only at h
    rw [show p.fst = d :: doms from hs] at h
    simp only at h
    rw [show Dom.enum d = v :: vs from hd] at h
    simp only at h
    exact ih h

theorem refined_coverage (leaf : Assignment → Bool) (kit : PruningKit leaf)
    (f : PrefixFrame) (rest : List PrefixFrame) (db : List Clause) (a : Assignment)
    (he : EntailedDB leaf db) (ha : leaf a = true) (hc : PrefixFrontierCovers (f::rest) a) :
    (∃ g, (kit.run f db).frame = some g ∧ PrefixCovers g a) ∨ PrefixFrontierCovers rest a := by
  obtain ⟨g, hg, hcov⟩ := hc
  rcases List.mem_cons.mp hg with rfl | hg
  · exact Or.inl (kit.preserves g db he a ha hcov)
  · exact Or.inr ⟨g,hg,hcov⟩

theorem refined_none_coverage (leaf : Assignment → Bool) (kit : PruningKit leaf)
    (f : PrefixFrame) (rest : List PrefixFrame) (db : List Clause) (a : Assignment)
    (he : EntailedDB leaf db) (ha : leaf a = true) (hc : PrefixFrontierCovers (f::rest) a)
    (hg : (kit.run f db).frame = none) : PrefixFrontierCovers rest a := by
  rcases refined_coverage leaf kit f rest db a he ha hc with ⟨g,hg',_⟩ | hc
  · rw [hg] at hg'; cases hg'
  · exact hc

theorem refined_some_coverage (leaf : Assignment → Bool) (kit : PruningKit leaf)
    (f g : PrefixFrame) (rest : List PrefixFrame) (db : List Clause) (a : Assignment)
    (he : EntailedDB leaf db) (ha : leaf a = true) (hc : PrefixFrontierCovers (f::rest) a)
    (hg : (kit.run f db).frame = some g) : PrefixCovers g a ∨ PrefixFrontierCovers rest a := by
  rcases refined_coverage leaf kit f rest db a he ha hc with ⟨g',hg',hc⟩ | hc
  · rw [hg] at hg'; cases hg'; exact Or.inl hc
  · exact Or.inr hc

theorem prunedSolve_unsat_excludes (leaf : Assignment → Bool) (kit : PruningKit leaf)
    (pending : List PrefixFrame) (db : List Clause) (stats : SearchStats)
    (he : EntailedDB leaf db) (h : (prunedSolve leaf kit pending db stats).1 = .unsat) :
    ∀ a, PrefixFrontierCovers pending a → leaf a = false := by
  suffices hx : ∀ a, leaf a = true → PrefixFrontierCovers pending a → False by
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
    rw [hg] at h
    simp only at h
    exact h
  | case3 db stats f rest r p hg slots chosen hs hl =>
    rw [prunedSolve] at h
    rw [hg] at h
    simp only at h
    rw [show p.fst = [] from hs] at h
    simp only at h
    rw [show leaf p.snd = true from hl] at h
    simp at h
  | case4 db stats f rest r ns nd p hg slots chosen hs checked hl ih =>
    have hcov := refined_some_coverage leaf kit f p rest db a he ha hc hg
    have hrest : PrefixFrontierCovers rest a := by
      rcases hcov with ⟨tail,ht,heq⟩ | hc
      · rw [show p.fst = [] from hs] at ht
        simp [allAssigns] at ht
        subst tail
        simp at heq
        subst a
        exact False.elim (hl (by simpa [chosen] using ha))
      · exact hc
    apply ih (EntailedDB.append (kit.learns f db he) he) _ hrest
    rw [prunedSolve] at h
    rw [hg] at h
    simp only at h
    rw [show p.fst = [] from hs] at h
    simp only at h
    rw [if_neg (show ¬ leaf p.snd = true from hl)] at h
    exact h
  | case5 db stats f rest r ns nd p hg slots d doms hs hd ih =>
    have hcov := refined_some_coverage leaf kit f p rest db a he ha hc hg
    have hrest : PrefixFrontierCovers rest a := by
      rcases hcov with ⟨suffix,ht,_⟩ | hc
      · rw [show p.fst = d :: doms from hs] at ht
        have hemp : allAssigns (d :: doms) = [] :=
          allAssigns_cons_eq_nil (d := d) (rest := doms)
            (by rw [domElems_eq_enum]; exact hd)
        rw [hemp] at ht
        cases ht
      · exact hc
    apply ih (EntailedDB.append (kit.learns f db he) he) _ hrest
    rw [prunedSolve] at h
    rw [hg] at h
    simp only at h
    rw [show p.fst = d :: doms from hs] at h
    simp only at h
    rw [show Dom.enum d = [] from hd] at h
    simp only at h
    exact h
  | case6 db stats f rest r ns nd p hg slots chosen d doms hs v vs hd ih =>
    have hcov := refined_some_coverage leaf kit f p rest db a he ha hc hg
    have hnext : PrefixFrontierCovers
        ((doms, chosen ++ [v]) :: (Dom.ofList vs :: doms, chosen) :: rest) a := by
      rcases hcov with hc | ⟨g,hg',hc⟩
      · have hc' : PrefixCovers (d :: doms, p.snd) a := by
          rcases hc with ⟨tail, ht, rfl⟩
          exact ⟨tail, by simpa [show p.fst = d :: doms from hs] using ht, rfl⟩
        rcases (prefix_covers_split_list hd doms p.snd a).mp hc' with hc | hc
        · exact ⟨_,List.mem_cons_self,hc⟩
        · exact ⟨_,List.mem_cons_of_mem _ List.mem_cons_self,hc⟩
      · exact ⟨g,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg'),hc⟩
    apply ih (EntailedDB.append (kit.learns f db he) he) _ hnext
    rw [prunedSolve] at h
    rw [hg] at h
    simp only at h
    rw [show p.fst = d :: doms from hs] at h
    simp only at h
    rw [show Dom.enum d = v :: vs from hd] at h
    simp only at h
    exact h

/-- Every represented satisfying assignment guarantees a SAT verdict. The
    returned witness may differ from the witness supplied to this theorem. -/
theorem prunedSolve_complete (leaf : Assignment → Bool) (kit : PruningKit leaf)
    (pending : List PrefixFrame) (db : List Clause) (stats : SearchStats)
    (he : EntailedDB leaf db) (a : Assignment)
    (hc : PrefixFrontierCovers pending a) (ha : leaf a = true) :
    ∃ b, (prunedSolve leaf kit pending db stats).1 = .sat b ∧ leaf b = true := by
  cases hr : (prunedSolve leaf kit pending db stats).1 with
  | sat b => exact ⟨b,rfl,prunedSolve_sat_leaf leaf kit pending db stats b hr⟩
  | unsat =>
    have hf := prunedSolve_unsat_excludes leaf kit pending db stats he hr a hc
    rw [ha] at hf
    cases hf

end LeanFzn.Solver.Chronological

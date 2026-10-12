/-
File: LeanFzn/Solver/Chronological/Proofs/AnalysisDriver.lean

Purpose:
  Certification of the analysed driver's pruning step and of the driver
  itself:

  * `refutedBy_sound` — a frame whose chosen prefix refutes an entailed
    clause cannot carry a leaf solution;
  * `pruneFrames_preserves` — pruning preserves every leaf solution
    (the plan's "no still-possible solution is deleted");
  * `pruneFrames_cost_le` — pruning never increases the frontier cost
    (the measure half, restated for clients);
  * `analyzedSolve_sat_leaf` / `analyzedSolve_unsat_excludes` — the
    driver's verdicts are sound and complete, by the same induction as
    the chronological driver with the pruning step inserted.

Dependencies:
  - LeanFzn.Solver.Chronological.AnalysisDriver
  - LeanFzn.Solver.Propagation.FrameFilter (`valueHolds_read`), LeanFzn.Solver.Chronological.Pruned

DAG:
  AnalysisDriver + FrameFilter -> Proofs.AnalysisDriver.
-/

import LeanFzn.Solver.Chronological.AnalysisDriver
import LeanFzn.Solver.Chronological.Proofs.Pruned
open LeanFzn.Semantics LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological


namespace LeanFzn.Solver.Chronological
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-! ## Prefix refutation -/

/-- A literal checked at an already-decided slot evaluates at the
chosen value. -/
theorem refutedBy_lit_false {c : Clause} {f : BranchFrame}
    {l : Literal} (hl : l ∈ c) (h : refutedBy c f = true) :
    ∃ v, f.2[l.atom.slot]? = some v ∧ l.valueHolds v = false := by
  have hb := List.all_eq_true.mp h l hl
  cases hget : f.2[l.atom.slot]? with
  | none => rw [hget] at hb; simp at hb
  | some v =>
      refine ⟨v, rfl, ?_⟩
      rw [hget] at hb
      simpa using hb

/-- A refuted, entailed clause is false at every covered assignment:
pruning a frame on such a clause cannot delete a leaf solution. -/
theorem refutedBy_not_leaf {leaf : Assignment → Bool} {c : Clause}
    {f : BranchFrame} {a : Assignment}
    (hent : ∀ a', leaf a' = true → c.SatisfiedBy a')
    (hrep : FrameCovers f a) (h : refutedBy c f = true) :
    leaf a ≠ true := by
  intro hleaf
  obtain ⟨tail, htail, rfl⟩ := hrep
  obtain ⟨l, hl, hltrue⟩ := hent (f.2 ++ tail) hleaf
  obtain ⟨v, hv, hvfalse⟩ := refutedBy_lit_false hl h
  have hslot : l.atom.slot < f.2.length := by
    by_cases hlt : l.atom.slot < f.2.length
    · exact hlt
    · rw [List.getElem?_eq_none (by omega)] at hv
      simp at hv
  have hread : (f.2 ++ tail)[l.atom.slot]? = some v :=
    List.getElem?_append_left hslot ▸ hv
  have hvh : l.valueHolds v = true := (valueHolds_read hread).mpr hltrue
  rw [hvfalse] at hvh
  simp at hvh

/-- Pragmatic variant of the above used by the driver: the clause is in
an entailed database. -/
theorem refutedByDB_not_leaf {leaf : Assignment → Bool} {db : List Clause}
    {f : BranchFrame} {a : Assignment}
    (hdb : ∀ c ∈ db, ∀ a', leaf a' = true → c.SatisfiedBy a')
    (hrep : FrameCovers f a) (h : refutedByDB db f = true) :
    leaf a ≠ true := by
  obtain ⟨c, hc, href⟩ := List.any_eq_true.mp h
  exact refutedBy_not_leaf (hdb c hc) hrep href

/-- PRUNING PRESERVES SOLUTIONS: every leaf-passing assignment covered
by the pending frontier is still covered after pruning, provided the
database is entailed. -/
theorem pruneFrames_preserves {leaf : Assignment → Bool}
    {db : List Clause} {pending : List BranchFrame}
    (hdb : ∀ c ∈ db, ∀ a', leaf a' = true → c.SatisfiedBy a') :
    ∀ a, leaf a = true → FrontierCovers pending a →
      FrontierCovers (pruneFrames db pending) a := by
  intro a hleaf ⟨f, hf, hcov⟩
  -- the frame survives: it cannot be refuted
  have hsurvive : f ∈ pruneFrames db pending := by
    rw [pruneFrames]
    refine List.mem_filter.mpr ⟨hf, ?_⟩
    cases hb : refutedByDB db f with
    | false => rfl
    | true => exact absurd hleaf (refutedByDB_not_leaf hdb hcov hb)
  exact ⟨f, hsurvive, hcov⟩

/-- Pruning never increases the frontier cost (measure restatement). -/
theorem pruneFrames_cost_le (db : List Clause)
    (pending : List BranchFrame) :
    frontierCost (pruneFrames db pending) ≤ frontierCost pending :=
  frontierCost_prune_le db pending

/-! ## Driver verdicts -/

theorem analyzedSolve_sat_leaf (leaf : Assignment → Bool)
    (kit : PruningKit leaf) (pending : List BranchFrame)
    (db : List Clause) (stats : SearchStats) (a : Assignment)
    (h : (analyzedSolve leaf kit pending db stats).1 = .sat a) :
    leaf a = true := by
  induction pending, db, stats using analyzedSolve.induct (leaf := leaf)
    (kit := kit) <;>
    rw [analyzedSolve] at h
  all_goals first | cases h | skip
  all_goals split at h
  all_goals simp_all +zetaDelta
  all_goals rcases (show _ ∧ _ from by assumption) with ⟨hs, hc⟩
  all_goals subst_vars
  all_goals simp_all +zetaDelta

theorem analyzedSolve_unsat_excludes (leaf : Assignment → Bool)
    (kit : PruningKit leaf) (pending : List BranchFrame)
    (db : List Clause) (stats : SearchStats)
    (hdb : EntailedDB leaf db)
    (h : (analyzedSolve leaf kit pending db stats).1 = .unsat) :
    ∀ a, FrontierCovers pending a → leaf a = false := by
  suffices hx : ∀ a, leaf a = true → FrontierCovers pending a → False by
    intro a hc
    cases hl : leaf a with
    | false => rfl
    | true => exact False.elim (hx a hl hc)
  intro a ha hc
  induction pending, db, stats using analyzedSolve.induct (leaf := leaf)
    (kit := kit) with
  | case1 => obtain ⟨f, hf, _⟩ := hc; cases hf
  | case2 db stats f rest r ns nd survivors hframe ih =>
      have hcov := refined_none_coverage leaf kit f rest db a hdb ha hc hframe
      have hn := EntailedDB.append (kit.learns f db hdb) hdb
      have hcov' := pruneFrames_preserves (leaf := leaf) (db := nd)
        (pending := rest) hn a ha hcov
      apply ih hn _ hcov'
      rw [analyzedSolve] at h
      split at h <;> simp_all +zetaDelta
  | case3 db stats f rest r chosen hg hl hg' =>
      rw [analyzedSolve] at h
      split at h <;> simp_all +zetaDelta
      all_goals rcases (show _ ∧ _ from by assumption) with ⟨hs, hc⟩
      all_goals subst_vars
      all_goals simp_all +zetaDelta
  | case4 db stats f rest r ns nd survivors chosen hg checked hl hg2 ih =>
      have hcov := refined_some_coverage leaf kit f ([], chosen) rest db a
        hdb ha hc hg
      have hrest : FrontierCovers rest a := by
        rcases hcov with ⟨tail, ht, heq⟩ | hc
        · simp [allAssigns] at ht
          subst tail
          simp at heq
          subst a
          exact absurd ha hl
        · exact hc
      have hn := EntailedDB.append (kit.learns f db hdb) hdb
      have hcov' := pruneFrames_preserves (leaf := leaf) (db := nd)
        (pending := rest) hn a ha hrest
      apply ih hn _ hcov'
      rw [analyzedSolve] at h
      split at h <;> simp_all +zetaDelta
      all_goals rcases (show _ ∧ _ from by assumption) with ⟨hs, hc⟩
      all_goals subst_vars
      all_goals simp_all +zetaDelta
  | case5 db stats f rest r ns nd survivors chosen tail hg hg1 ih =>
      have hcov := refined_some_coverage leaf kit f ([] :: tail, chosen) rest db a
        hdb ha hc hg
      have hrest : FrontierCovers rest a := by
        rcases hcov with ⟨suffix, ht, _⟩ | hc
        · simp [allAssigns] at ht
        · exact hc
      have hn := EntailedDB.append (kit.learns f db hdb) hdb
      have hcov' := pruneFrames_preserves (leaf := leaf) (db := nd)
        (pending := rest) hn a ha hrest
      apply ih hn _ hcov'
      rw [analyzedSolve] at h
      split at h <;> simp_all +zetaDelta
      all_goals rcases (show _ ∧ _ from by assumption) with ⟨hs, hc⟩
      all_goals subst_vars
      all_goals simp_all +zetaDelta
  | case6 db stats f rest r ns nd survivors chosen v vs doms hg hg2 ih =>
      have hcov := refined_some_coverage leaf kit f ((v :: vs) :: doms, chosen)
        rest db a hdb ha hc hg
      have hn := EntailedDB.append (kit.learns f db hdb) hdb
      have hnext : FrontierCovers
          ((doms, chosen ++ [v]) :: (vs :: doms, chosen) ::
            pruneFrames nd rest) a := by
        rcases hcov with hc | ⟨g, hg1, hc⟩
        · rcases (covers_split v vs doms chosen a).mp hc with hc | hc
          · exact ⟨_, List.mem_cons_self, hc⟩
          · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hc⟩
        · have hcovg : FrontierCovers rest a := ⟨g, hg1, hc⟩
          obtain ⟨g', hg', hc'⟩ := pruneFrames_preserves (leaf := leaf)
            (db := nd) (pending := rest) hn a ha hcovg
          exact ⟨g', List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg'), hc'⟩
      apply ih hn _ hnext
      rw [analyzedSolve] at h
      split at h <;> simp_all +zetaDelta
      all_goals rcases (show _ ∧ _ from by assumption) with ⟨hs, hc⟩
      all_goals subst_vars
      all_goals simp_all +zetaDelta

end LeanFzn.Solver.Chronological

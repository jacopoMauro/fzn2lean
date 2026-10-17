/-
File: LeanFzn/Solver/UIP/Proofs/LcgEvidence.lean

Conditional evidence contract for the LCG runtime.

`LcgRunInv.evidence` (LcgContract.lean) demands that EVERY recorded conflict clause is
semantically falsified by the trail. That is false along real runs
(`LcgRunInv.evidence_refuted`): an emptied-slot database clause is recorded without any
falsifying trail entry, and its recorded analysis is `none`.

The analyzer-level truth is conditional: a recorded analysis that SUCCEEDS implies that the
conflict clause is semantically falsified (every conflict literal is either false at the root
or has an admissible falsifier on the trail). This module proves that:

  * `analysis_some_conflict_semFalsified` (analyzer level, by induction on the loop fuel);
  * `EvidenceRun'` (the conditional form along supported runs), proved unconditionally from
    `evidenceProvenance_of_reachable` and the analyzer lemma;
  * `LcgRunInv'` (the bundle with the conditional evidence field) and
    `lcgRunInvCond_of_residual` (the assembly without the refuted premise `hev`);
  * `evidence_witness_analysis_none`: the refutation witness has no recorded analysis, so
    the conditional form does not contradict it.
-/
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantFinal
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantEvidenceFalse
import LeanFzn.Solver.UIP.Proofs.SchedulerReachable
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP.LcgClamp
open LeanFzn.Solver.UIP.ClampPool LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgRunInv

namespace LeanFzn.Solver.UIP.LcgEvidence

/-! ## 1. Analyzer level -/

/-- The root drop is invariant under normalization. -/
theorem litFalseAtRoot_norm (orig : List Domain) (q : Literal) :
    litFalseAtRoot orig q.norm = litFalseAtRoot orig q := by
  obtain ⟨atom, pos⟩ := q
  cases atom with
  | boolEq s b =>
      cases pos
      · unfold litFalseAtRoot
        congr 1
        funext v
        cases v <;> cases b <;> simp [Literal.norm, Atom.evalAtValue]
      · rfl
  | intLe s k => rfl
  | intNe s k => rfl

/-- A semantic falsifier of the normalized literal is one of the literal itself. -/
theorem semFalsifiedBefore_of_norm {orig : List Domain} {pre : List TrailEntry} {q : Literal}
    (h : LcgContract.SemFalsifiedBefore orig pre q.norm) :
    LcgContract.SemFalsifiedBefore orig pre q := by
  rcases h with h | ⟨e, he, hi⟩
  · exact Or.inl ((litFalseAtRoot_norm orig q) ▸ h)
  · refine Or.inr ⟨e, he, ?_⟩
    rwa [norm_negate_norm] at hi

/-- A successful mark makes the (normalized) literal semantically falsified. -/
theorem markLitAt_sem {orig : List Domain} {trail : List TrailEntry} {lvl : Nat}
    {bound : Option Nat} {marks m' : List Nat} {learnt l' : List (Literal × Nat)}
    {q0 : Literal} (h : markLitAt orig trail lvl bound marks learnt q0 = some (m', l')) :
    LcgContract.SemFalsifiedBefore orig trail q0.norm := by
  rcases markLitAt_spec h with ⟨hr, -, -⟩ | ⟨i, e, he, hp, -, -⟩
  · exact Or.inl hr
  · exact Or.inr ⟨e, List.mem_of_getElem? he, hp⟩

/-- One successful expansion-free step on a non-empty head clause: the successor keeps the
skip and the rest of the worklist, and the head literal is semantically falsified (or
skipped). -/
theorem analyzeNext_cons_next {orig : List Domain} {trail : List TrailEntry} {lvl : Nat}
    {skip : Option Literal} {bound : Option Nat} {marks : List Nat}
    {learnt : List (Literal × Nat)} {q0 : Literal} {qs : Clause} {cs : List Clause}
    {st' : AnalyzerState}
    (hn : analyzeNext orig trail lvl
      { work := (q0 :: qs) :: cs, skip := skip, bound := bound, marks := marks,
        learnt := learnt } = AnalyzerStep.next st') :
    st'.work = qs :: cs ∧ st'.skip = skip ∧
      (skipEq skip q0.norm = true ∨ LcgContract.SemFalsifiedBefore orig trail q0.norm) := by
  simp only [analyzeNext] at hn
  split at hn
  · rename_i hsk
    cases hn
    exact ⟨rfl, rfl, Or.inl hsk⟩
  · split at hn
    · cases hn
    · rename_i mp hm
      cases hn
      exact ⟨rfl, rfl, Or.inr (by have := markLitAt_sem hm; rwa [norm_norm] at this)⟩

/-- INVARIANT OF THE LOOP: if the loop succeeds from `st`, every literal of every pending
clause is either skipped (the pivot) or semantically falsified by the trail. -/
theorem analyzeLoop_sem {orig : List Domain} {trail : List TrailEntry} {lvl : Nat} :
    ∀ (fuel : Nat) (st : AnalyzerState) (below : List (Literal × Nat)) (uip : Literal),
      analyzeLoop orig trail lvl fuel st = some (below, uip) →
      ∀ cl ∈ st.work, ∀ q ∈ cl,
        skipEq st.skip q.norm = true ∨ LcgContract.SemFalsifiedBefore orig trail q.norm := by
  intro fuel
  induction fuel with
  | zero => intro st below uip h; simp [analyzeLoop] at h
  | succ fuel ih =>
      intro st below uip h
      obtain ⟨work, skip, bound, marks, learnt⟩ := st
      cases work with
      | nil => intro cl hcl; cases hcl
      | cons cl0 cs =>
          cases cl0 with
          | nil =>
              have hn : analyzeNext orig trail lvl ⟨[] :: cs, skip, bound, marks, learnt⟩ =
                  AnalyzerStep.next ⟨cs, skip, bound, marks, learnt⟩ := rfl
              have h' := h
              simp only [analyzeLoop, hn] at h'
              intro cl hcl q hq
              rcases List.mem_cons.mp hcl with rfl | hcl
              · cases hq
              · exact ih _ below uip h' cl hcl q hq
          | cons q0 qs =>
              intro cl hcl q hq
              cases hn : analyzeNext orig trail lvl
                  { work := (q0 :: qs) :: cs, skip := skip, bound := bound, marks := marks,
                    learnt := learnt } with
              | done r =>
                  simp only [analyzeLoop, hn] at h
                  subst h
                  exact absurd (analyzeNext_done_some hn).1 (by simp)
              | next st' =>
                  obtain ⟨hw', hs', hq0⟩ := analyzeNext_cons_next hn
                  have h' : analyzeLoop orig trail lvl fuel st' = some (below, uip) := by
                    simp only [analyzeLoop, hn] at h
                    exact h
                  rcases List.mem_cons.mp hcl with rfl | hcl
                  · rcases List.mem_cons.mp hq with rfl | hq
                    · exact hq0
                    · have := ih st' below uip h' qs (by rw [hw']; exact List.mem_cons_self) q hq
                      rw [hs'] at this
                      exact this
                  · have := ih st' below uip h' cl (by rw [hw']; exact List.mem_cons_of_mem _ hcl)
                      q hq
                    rw [hs'] at this
                    exact this

/-- ANALYZER-LEVEL CONFLICT FALSIFICATION: a successful analysis of the conflict clause `c`
implies that every literal of `c` is semantically falsified by the trail (root or
falsifier). -/
theorem analysis_some_conflict_semFalsified {orig : List Domain} {trail : List TrailEntry}
    {lvl : Nat} {c : Clause} {below : List (Literal × Nat)} {uip : Literal}
    (h : analyzeAtAllowance orig trail lvl c = some (below, uip)) :
    LcgContract.ClauseSemFalsifiedR orig trail c := by
  unfold analyzeAtAllowance at h
  have hall := analyzeLoop_sem _ _ below uip h c (by simp [initAnalysisState])
  intro q hq
  rcases hall q hq with hs | hs
  · simp [initAnalysisState, skipEq] at hs
  · exact semFalsifiedBefore_of_norm hs

/-! ## 2. Scheduler level: the conditional evidence residual -/

/-- **EvidenceRun'** (conditional form of the evidence premise): along every supported
configuration, a recorded conflict clause whose recorded analysis is `some` is semantically
falsified by the branch trail. -/
def EvidenceRun' (orig : List Domain) (original : List Clause) (props : List Propagator)
    (leaf : Assignment → Bool) : Prop :=
  ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
    ∀ ev, cfg.conflict = some ev → ∀ an, ev.analysis = some an →
      LcgContract.ClauseSemFalsifiedR cfg.orig cfg.branch.trail ev.clause

/-- `EvidenceRun'` holds unconditionally: the recorded analysis is the analyzer's output on
the branch trail (`evidenceProvenance_of_reachable`), and a successful analyzer run
falsifies the conflict clause (`analysis_some_conflict_semFalsified`). -/
theorem evidenceRunCond_holds (orig : List Domain) (original : List Clause)
    (props : List Propagator) (leaf : Assignment → Bool) :
    EvidenceRun' orig original props leaf := by
  intro cfg hreach ev hconf an hana
  obtain ⟨below, uip, hmap, -⟩ :=
    reachable_analysis_success leaf cfg ev an hreach.reachable hconf hana
  exact analysis_some_conflict_semFalsified hmap

/-! ## 3. The bundle with the conditional evidence field -/

/-- `LcgRunInv` with the evidence field in conditional form: only RECORDED ANALYSES
(`ev.analysis = some an`) must be semantically falsified. -/
structure LcgRunInv' {leaf : Assignment → Bool} (cfg : SchedulerConfig leaf) : Prop where
  entailed : LearnedEntailed leaf cfg.branch.learned
  reasons : TrailSem cfg.orig cfg.branch.trail
  evidence : ∀ ev an, cfg.conflict = some ev → ev.analysis = some an →
    LcgContract.ClauseSemFalsifiedR cfg.orig cfg.branch.trail ev.clause
  wipe : WipeoutOk cfg
  closure : (∃ n m, schedulerNext cfg = .decide n m) → DbSemUnfalsified cfg.orig cfg.branch

/-- The assembly of `lcgRunInv_of_residual` with the conditional evidence: the same premises
minus the refuted `hev`. 
VACUOUS on non-unit LCG instances (hbr_refuted); use *_of_kit (LcgKitFinal). -/
theorem lcgRunInvCond_of_residual {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (hraw : raw = dcs.filterMap propagatorOfProved)
    (hprops : props = clampProps orig raw)
    (hfam : ∀ dc ∈ dcs, lcgFamB dc = true)
    (hint : AllIntBox orig) (hnd : ∀ d ∈ orig, d.Nodup)
    (htyped : ClampPool.EmissionTyped orig raw)
    (horig : DatabaseAligned orig original)
    (hfit : ∀ a, leaf a = true → a.Fits orig)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hA : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → AssertingSem cfg)
    (hent : EntailedRun orig original props leaf)
    (hlive : DecideLive orig original props leaf) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg → LcgRunInv' cfg := by
  intro cfg hreach
  have hT := LeanFzn.Solver.UIP.LcgRunInv.trailRun_of_supportedRun hraw hprops hfam hint hnd
    htyped horig hbr hA hreach
  have hF := LeanFzn.Solver.UIP.LcgRunInv.frameRun_of_supportedRun hint hnd
    (LeanFzn.Solver.UIP.LcgRunInv.shape_of_allInt hint) hbr hreach
  have hor : cfg.orig = orig := SupportedReach.orig_eq hreach
  exact
    { entailed := hent hreach
      reasons := hT.branch
      evidence := fun ev an h1 h2 => evidenceRunCond_holds orig original props leaf hreach ev h1 an h2
      wipe := LeanFzn.Solver.UIP.LcgRunInv.wipeoutOk_of_fits hfit cfg hor
      closure := fun hdec =>
        LeanFzn.Solver.UIP.LcgRunInv.closure_at_decide (by rw [hor]; exact hint) hF.branch
          (hlive hreach hdec) hdec }

/-! ## 4. The refutation witness under the conditional form -/

/-- The old refutation witness is still a witness: the refuted recorded conflict has NO
recorded analysis, so `EvidenceRun'` does not contradict it. -/
theorem evidence_witness_analysis_none :
    ∃ cfg : SchedulerConfig LeanFzn.Solver.UIP.LcgRunInv.evLeaf,
      SupportedReach LeanFzn.Solver.UIP.LcgRunInv.evBox LeanFzn.Solver.UIP.LcgRunInv.evOriginal
        [] cfg ∧
      ∃ ev, cfg.conflict = some ev ∧ ev.analysis = none ∧
        ¬ LcgContract.ClauseSemFalsifiedR cfg.orig cfg.branch.trail ev.clause := by
  obtain ⟨cfg, hreach, ev, hev, hnot⟩ := LeanFzn.Solver.UIP.LcgRunInv.evidence_refuted
  refine ⟨cfg, hreach, ev, hev, ?_, by rw [SupportedReach.orig_eq hreach]; exact hnot⟩
  cases han : ev.analysis with
  | none => rfl
  | some an =>
      have hf := evidenceRunCond_holds _ _ _ _ hreach ev hev an han
      rw [SupportedReach.orig_eq hreach] at hf
      exact absurd hf hnot

/-- The unconditional refutation still holds: `EvidenceRun` stays false, `EvidenceRun'` is
true, and both are consistent with the witness. -/
example : ¬ LeanFzn.Solver.UIP.LcgRunInv.EvidenceRun LeanFzn.Solver.UIP.LcgRunInv.evBox
    LeanFzn.Solver.UIP.LcgRunInv.evOriginal [] LeanFzn.Solver.UIP.LcgRunInv.evLeaf :=
  LeanFzn.Solver.UIP.LcgRunInv.evidenceRun_refuted

end LeanFzn.Solver.UIP.LcgEvidence

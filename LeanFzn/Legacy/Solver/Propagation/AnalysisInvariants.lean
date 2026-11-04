/-
File: LeanFzn/Solver/Propagation/AnalysisInvariants.lean

Purpose:
  B2 — the analyzer's FALSIFIER invariants, derived from the analyzer's
  own output instead of assumed.

  The branch-level `TrailFalsifies` obligation (every learned literal is
  the negation of a trail entry) was previously a premise the caller had
  to supply. It is a consequence of what `markLit` and `nextPivot`
  actually do, and this module proves it:

  * `BelowFalsified` — each recorded below-level pair names a literal
    whose normalized negation is a trail entry. `markLit` establishes it
    from the very `findEntryOf` call that selected the falsifier, so this
    is the derivation the plan asks for ("normalization and order-literal
    upgrades must preserve both entailment and falsifier lookup").
  * `MarksOnTrail` / `MarksCurrentLevel` — every mark is a trail entry,
    and every mark sits at the analysis level. These two are what make
    the returned first UIP a *current-level* trail literal, hence the
    asserting literal's falsifier is at the conflict level.
  * `analyzeStep_uip_on_trail` — a successful analysis returns a UIP that
    is the literal of a trail entry at the analysis level. The witness is
    the MARK that matched the pivot, not a re-lookup, so no trail-literal
    uniqueness is needed.

Dependencies:
  - LeanFzn.Solver.Propagation.Proofs.Analyze: `findEntryOf_literal`,
    `nextPivot_trail_mem` (the lookups' specification lemmas).

DAG:
  Proofs/Analyze -> LeanFzn.Solver.UIP.AnalysisInvariants -> LeanFzn.Solver.Propagation.RestorationCertificate
-/

import LeanFzn.Solver.Propagation.Proofs.Analyze
open LeanFzn.Semantics LeanFzn.Solver.Propagation



namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-! ## Lookup specification -/

/-- `findEntryOf` returns a trail entry. -/
theorem findEntryOf_mem (trail : List TrailEntry) (l : Literal) (e : TrailEntry)
    (h : findEntryOf trail l = some e) : e ∈ trail := by
  unfold findEntryOf at h
  obtain ⟨_, as, bs, hrw, _⟩ := List.find?_eq_some_iff_append.mp h
  have hmem : e ∈ trail.reverse := by
    rw [hrw, List.mem_append]
    exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
  exact List.mem_reverse.mp hmem

/-- `nextPivot` matches a MARK: the entry it returns has the same literal
as some marked entry. This is the witness the UIP lemma cites — no
re-lookup and no uniqueness assumption. -/
theorem nextPivot_mark (trail : List TrailEntry) (marks : List TrailEntry)
    (e : TrailEntry) (h : nextPivot trail marks = some e) :
    ∃ m ∈ marks, m.literal = e.literal := by
  unfold nextPivot at h
  obtain ⟨hp, _, _, _, _⟩ := List.find?_eq_some_iff_append.mp h
  rw [List.any_eq_true] at hp
  obtain ⟨m, hm, hmatch⟩ := hp
  exact ⟨m, hm, by simpa only [litEqB, decide_eq_true_eq] using hmatch⟩

/-! ## The three analyzer invariants -/

/-- Every recorded below-level pair names a literal whose NORMALIZED
negation is a trail entry. The normalization is not a weakening: trail
literals are stored normalized, and `orderUpgrade` may replace the
scanned literal by a weaker one, so the lookup is exact on the
normalized form.

The pair also records WHICH entry was found (`findEntryOf`, i.e. the
LATEST match) and that entry's level. Those two extra facts are what make
the certificate's uniqueness and maximality conjuncts provable: because
the recorded entry is the last falsifier on the trail, no later entry can
falsify the literal, and level-sortedness then forces every OTHER
falsifier to sit below it. -/
def BelowFalsified (trail : List TrailEntry)
    (learnt : List (Literal × Nat)) : Prop :=
  ∀ p ∈ learnt, ∃ e, findEntryOf trail (p.1.negate) = some e ∧
    e.literal = (p.1.negate).norm ∧ e.level = p.2

/-- Every mark is a trail entry. -/
def MarksOnTrail (trail : List TrailEntry) (marks : List TrailEntry) : Prop :=
  ∀ m ∈ marks, m ∈ trail


/-- Every mark sits at the analysis level: `markLit` only marks entries
whose level equals the analysis level. -/
def MarksCurrentLevel (lvl : Nat) (marks : List TrailEntry) : Prop :=
  ∀ m ∈ marks, m.level = lvl

/-- The three analyzer invariants bundled: they always travel together, and
each transition preserves all three. -/
def AnalyzerInvariant (trail : List TrailEntry) (lvl : Nat)
    (marks : List TrailEntry) (learnt : List (Literal × Nat)) : Prop :=
  BelowFalsified trail learnt ∧ MarksOnTrail trail marks ∧
    MarksCurrentLevel lvl marks

/-! ## Preservation by `markLit`

`markLit` has three productive outcomes — already marked, already learnt,
and falsifier found — and the falsifier branch splits again on the
falsifier's level. Each branch is handled by the invariant it needs, and
the newly recorded pair cites the very entry `findEntryOf` returned. -/

/-- The falsifier-found branch of `markLit`: a trail entry `e` falsifies the
selected literal `q'`, and the branch either drops it (root level), marks
it (analysis level) or records the pair `(q', e.level)`. The recorded pair
cites `e` itself, which is why no trail-literal uniqueness is needed. -/
theorem markLit_falsifier_branch {trail : List TrailEntry} {lvl : Nat}
    {marks : List TrailEntry} {learnt : List (Literal × Nat)} {q' : Literal}
    {e : TrailEntry} {marks' : List TrailEntry} {learnt' : List (Literal × Nat)}
    (hbelow : BelowFalsified trail learnt) (hon : MarksOnTrail trail marks)
    (hcur : MarksCurrentLevel lvl marks)
    (hf : findEntryOf trail q'.negate = some e)
    (h : (if (e.level == 0) = true then some (marks, learnt)
          else if (e.level == lvl) = true then some (e :: marks, learnt)
          else some (marks, (q', e.level) :: learnt)) = some (marks', learnt')) :
    BelowFalsified trail learnt' ∧ MarksOnTrail trail marks' ∧
      MarksCurrentLevel lvl marks' := by
  have hlit : e.literal = (q'.negate).norm := findEntryOf_literal trail _ e hf
  have hemem : e ∈ trail := findEntryOf_mem trail _ e hf
  by_cases h0 : (e.level == 0) = true
  · rw [if_pos h0] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hbelow, hon, hcur⟩
  · rw [if_neg h0] at h
    by_cases hl : (e.level == lvl) = true
    · rw [if_pos hl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨hbelow, ?_, ?_⟩
      · intro m hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hemem
        · exact hon m hm
      · intro m hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact beq_iff_eq.mp hl
        · exact hcur m hm
    · rw [if_neg hl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, hon, hcur⟩
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · -- the recorded pair cites the very entry the lookup returned, with its level
        exact ⟨e, hf, hlit, rfl⟩
      · exact hbelow p hp

theorem markLit_invariants (trail : List TrailEntry) (lvl : Nat)
    (marks : List TrailEntry) (learnt : List (Literal × Nat)) (q0 : Literal)
    (marks' : List TrailEntry) (learnt' : List (Literal × Nat))
    (hbelow : BelowFalsified trail learnt) (hon : MarksOnTrail trail marks)
    (hcur : MarksCurrentLevel lvl marks)
    (h : markLit trail lvl marks learnt q0 = some (marks', learnt')) :
    BelowFalsified trail learnt' ∧ MarksOnTrail trail marks' ∧
      MarksCurrentLevel lvl marks' := by
  -- the two dedup checks, then the falsifier lookup; each outcome is
  -- pinned by an explicit `simp` on the unfolded body
  by_cases h1 : (marks.any fun m => litEqB m.literal (q0.norm).negate.norm) = true
  · have hres : markLit trail lvl marks learnt q0 = some (marks, learnt) := by
      simp [markLit, h1]
    rw [hres] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hbelow, hon, hcur⟩
  · by_cases h2 : (learnt.any fun p => litEqB p.1 q0.norm) = true
    · have hres : markLit trail lvl marks learnt q0 = some (marks, learnt) := by
        simp [markLit, h1, h2]
      rw [hres] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hbelow, hon, hcur⟩
    · -- the falsifier lookup selects `q0.norm` or its order upgrade
      cases hf : findEntryOf trail (q0.norm).negate with
      | none =>
          -- the exact match failed, so the order upgrade decides `q'`
          cases hf2 : findEntryOf trail (orderUpgrade trail (q0.norm)).negate with
          | none =>
              have hres : markLit trail lvl marks learnt q0 = none := by
                simp [markLit, h1, h2, hf, hf2]
              rw [hres] at h
              simp at h
          | some e =>
              have hval : markLit trail lvl marks learnt q0 =
                  (if (e.level == 0) = true then some (marks, learnt)
                   else if (e.level == lvl) = true then some (e :: marks, learnt)
                   else some (marks, (orderUpgrade trail (q0.norm), e.level) :: learnt)) := by
                simp [markLit, h1, h2, hf, hf2]
              rw [hval] at h
              exact markLit_falsifier_branch hbelow hon hcur hf2 h
      | some e =>
          -- the exact match succeeded, so `q' = q0.norm`
          have hval : markLit trail lvl marks learnt q0 =
              (if (e.level == 0) = true then some (marks, learnt)
               else if (e.level == lvl) = true then some (e :: marks, learnt)
               else some (marks, (q0.norm, e.level) :: learnt)) := by
            simp [markLit, h1, h2, hf]
          rw [hval] at h
          exact markLit_falsifier_branch hbelow hon hcur hf h

/-! ## Preservation by the whole analyzer loop

The invariants hold initially (empty marks, empty learnt list) and each
transition either keeps the recorded data or extends it with entries the
invariants cover: the marks shrink by a filter, the learnt list is only
touched by `markLit`, and the worklist moves literals between its clauses
without touching either. -/

theorem analyzeStep_invariants (trail : List TrailEntry) (lvl : Nat) :
    ∀ (fuel : Nat) (cs : List Clause) (skip : Option Literal)
      (marks : List TrailEntry) (learnt : List (Literal × Nat)),
    AnalyzerInvariant trail lvl marks learnt →
    ∀ (below : List (Literal × Nat)) (uip : Literal),
      analyzeStep trail lvl fuel cs skip marks learnt = some (below, uip) →
      BelowFalsified trail below := by
  intro fuel
  induction fuel with
  | zero =>
      intro cs skip marks learnt _ below uip h
      simp [analyzeStep] at h
  | succ fuel ih =>
      intro cs skip marks learnt hinv below uip h
      cases cs with
      | nil =>
          -- expose the transition, then name the pivot lookup so that `cases`
          -- substitutes it and the surrounding match reduces
          simp only [analyzeStep] at h
          generalize hnp : nextPivot trail marks = np at h
          cases np with
          | none => simp at h
          | some e =>
              by_cases hq : (marks.filter fun m => !litEqB m.literal e.literal).isEmpty = true
              · -- the last mark: the analysis finishes, recording nothing new
                simp [hq, Prod.mk.injEq] at h
                exact h.1 ▸ hinv.1
              · cases hr : e.reason with
                | none => simp [hnp, hq, hr, Prod.mk.injEq] at h
                | some r =>
                    simp only [hq, hr] at h
                    exact ih [r.clause] (some e.literal)
                      (marks.filter fun m => !litEqB m.literal e.literal) learnt
                      ⟨hinv.1,
                       fun m hm => hinv.2.1 m (List.mem_filter.mp hm).1,
                       fun m hm => hinv.2.2 m (List.mem_filter.mp hm).1⟩
                      below uip h
      | cons c cs =>
          cases c with
          | nil =>
              rw [analyzeStep] at h
              exact ih cs skip marks learnt hinv below uip h
          | cons q0 qs =>
              by_cases hs : skipEq skip q0.norm
              · rw [analyzeStep, if_pos hs] at h
                exact ih (qs :: cs) skip marks learnt hinv below uip h
              · cases hm : markLit trail lvl marks learnt q0.norm with
                | none => simp [analyzeStep, if_neg hs, hm] at h
                | some mp =>
                    have hinv' := markLit_invariants trail lvl marks learnt q0.norm
                      mp.1 mp.2 hinv.1 hinv.2.1 hinv.2.2 hm
                    exact ih (qs :: cs) skip mp.1 mp.2 hinv' below uip (by
                      rw [analyzeStep, if_neg hs, hm] at h
                      exact h)

/-! ## The returned first UIP is a current-level trail literal

The witness is the MARK that matched the pivot: it is a trail entry at the
analysis level by the two mark invariants. No re-lookup is involved, so no
trail-literal uniqueness assumption is needed. -/

theorem analyzeStep_uip_on_trail (trail : List TrailEntry) (lvl : Nat) :
    ∀ (fuel : Nat) (cs : List Clause) (skip : Option Literal)
      (marks : List TrailEntry) (learnt : List (Literal × Nat)),
    AnalyzerInvariant trail lvl marks learnt →
    ∀ (below : List (Literal × Nat)) (uip : Literal),
      analyzeStep trail lvl fuel cs skip marks learnt = some (below, uip) →
      ∃ m ∈ trail, m.literal = uip ∧ m.level = lvl := by
  intro fuel
  induction fuel with
  | zero =>
      intro cs skip marks learnt _ below uip h
      simp [analyzeStep] at h
  | succ fuel ih =>
      intro cs skip marks learnt hinv below uip h
      cases cs with
      | nil =>
          simp only [analyzeStep] at h
          generalize hnp : nextPivot trail marks = np at h
          cases np with
          | none => simp at h
          | some e =>
              by_cases hq : (marks.filter fun m => !litEqB m.literal e.literal).isEmpty = true
              · simp [hq, Prod.mk.injEq] at h
                obtain ⟨m, hm, hmlit⟩ := nextPivot_mark trail marks e hnp
                exact ⟨m, hinv.2.1 m hm, hmlit.trans h.2, hinv.2.2 m hm⟩
              · cases hr : e.reason with
                | none => simp [hnp, hq, hr, Prod.mk.injEq] at h
                | some r =>
                    simp only [hq, hr] at h
                    exact ih [r.clause] (some e.literal)
                      (marks.filter fun m => !litEqB m.literal e.literal) learnt
                      ⟨hinv.1,
                       fun m hm => hinv.2.1 m (List.mem_filter.mp hm).1,
                       fun m hm => hinv.2.2 m (List.mem_filter.mp hm).1⟩
                      below uip h
      | cons c cs =>
          cases c with
          | nil =>
              rw [analyzeStep] at h
              exact ih cs skip marks learnt hinv below uip h
          | cons q0 qs =>
              by_cases hs : skipEq skip q0.norm
              · rw [analyzeStep, if_pos hs] at h
                exact ih (qs :: cs) skip marks learnt hinv below uip h
              · cases hm : markLit trail lvl marks learnt q0.norm with
                | none => simp [analyzeStep, if_neg hs, hm] at h
                | some mp =>
                    have hinv' := markLit_invariants trail lvl marks learnt q0.norm
                      mp.1 mp.2 hinv.1 hinv.2.1 hinv.2.2 hm
                    exact ih (qs :: cs) skip mp.1 mp.2 hinv' below uip (by
                      rw [analyzeStep, if_neg hs, hm] at h
                      exact h)

/-! ## The executable entry point

`analyzeTrail` starts with empty marks and an empty learnt list, so the
invariant holds initially and the two theorems above apply directly. These
are the corollaries B2's certificate consumes. -/

/-- The initial analyzer state satisfies the invariant. -/
theorem analyzerInvariant_init (trail : List TrailEntry) (lvl : Nat) :
    AnalyzerInvariant trail lvl [] [] :=
  ⟨by intro p hp; simp at hp, by intro m hm; simp at hm,
   by intro m hm; simp at hm⟩

/-- Every below-level pair the executable analysis records is trail-falsified
(in the normalized form the trail stores). -/
theorem analyzeTrail_belowFalsified {trail : List TrailEntry} {lvl : Nat}
    {c : Clause} {below : List (Literal × Nat)} {uip : Literal}
    (h : analyzeTrail trail lvl c = some (below, uip)) :
    BelowFalsified trail below := by
  unfold analyzeTrail at h
  exact analyzeStep_invariants trail lvl _ _ _ _ _ (analyzerInvariant_init trail lvl)
    below uip h

/-- The returned first UIP is the literal of a trail entry at the analysis
level: this is what makes the asserting literal's falsifier sit at the
conflict decision level. -/
theorem analyzeTrail_uip_on_trail {trail : List TrailEntry} {lvl : Nat}
    {c : Clause} {below : List (Literal × Nat)} {uip : Literal}
    (h : analyzeTrail trail lvl c = some (below, uip)) :
    ∃ m ∈ trail, m.literal = uip ∧ m.level = lvl := by
  unfold analyzeTrail at h
  exact analyzeStep_uip_on_trail trail lvl _ _ _ _ _ (analyzerInvariant_init trail lvl)
    below uip h

end LeanFzn.Solver.Propagation

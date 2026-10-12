/-
File: LeanFzn/Solver/Propagation/RestorationCertificate.lean

Purpose:
  B2 — ONE restoration-ready analysis certificate.

  The plan requires a single certificate, accepted directly by the C1
  scheduler, whose conjuncts are DERIVED from the analyzer's own output
  and the reachable-state invariant rather than assumed:

  1. the asserting literal belongs to the learned clause;
  2. the learned clause is globally entailed;
  3. the learned clause is falsified at the conflict state (normalized
     form, which is exactly what the analyzer guarantees);
  4. the asserting literal's falsifier sits at the conflict level;
  5. every OTHER learned literal is falsified below the target, and NO
     trail entry at the conflict level falsifies it — the "precisely one
     current-level falsifier" conjunct;
  6. the target level is legal and strictly descends;
  7. the target is the HIGHEST required surviving falsifier level;
  8. after restoration the asserting literal is not falsified;
  9. the UNIT property, stated in propagation's own literal semantics:
     every leaf solution satisfying the surviving trail satisfies the
     assertion;
 10. CONSERVATION: learning, restoration and assertion preserve every
     leaf solution represented by the restored checkpoint.

  The uniqueness (5) and maximality (7) conjuncts are where the two
  enabling invariants pay off: `BelowFalsified` (AnalysisInvariants)
  records WHICH entry the analyzer's lookup returned, and
  `ReachableState.sorted` (level-sortedness) turns "the recorded entry is
  the last falsifier" into "every other falsifier is lower". No separate
  trail-literal uniqueness assumption is needed.

Dependencies:
  - LeanFzn.Solver.Propagation.AnalysisInvariants: `analyzeTrail_belowFalsified`,
    `analyzeTrail_uip_on_trail`.
  - LeanFzn.Solver.Propagation.Proofs.BranchState: `ReachableState` (incl. `sorted`).
  - LeanFzn.Solver.Propagation.Proofs.Analyze: `analyzeTrail_belowStrict`.

DAG:
  AnalysisInvariants + Proofs/BranchState -> LeanFzn.Solver.Propagation.RestorationCertificate
-/

import LeanFzn.Solver.Propagation.AnalysisInvariants
import LeanFzn.Solver.Propagation.Proofs.BranchState
import LeanFzn.Solver.Propagation.AnalysisProgress
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation


open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-! ## Fold-max arithmetic for the target level -/

/-- The fold-max never drops below its accumulator. -/
theorem foldl_max_ge : ∀ (below : List (Literal × Nat)) (acc : Nat),
    acc ≤ below.foldl (fun a p => max a p.2) acc
  | [], acc => Nat.le_refl acc
  | p :: rest, acc => by
      rw [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left acc p.2) (foldl_max_ge rest (max acc p.2))

/-- Every member's level is at most the fold-max: this is the "target is
the HIGHEST required falsifier level" half of the certificate. -/
theorem foldl_max_mem_le : ∀ (below : List (Literal × Nat)) (acc : Nat),
    ∀ p ∈ below, p.2 ≤ below.foldl (fun a q => max a q.2) acc
  | [], _, p, hp => absurd hp (by simp)
  | h :: rest, acc, p, hp => by
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hp with rfl | hp
      · exact Nat.le_trans (Nat.le_max_right acc p.2) (foldl_max_ge rest (max acc p.2))
      · exact foldl_max_mem_le rest (max acc h.2) p hp

/-- EXACTNESS half of the fold-max: the value is ATTAINED by the
accumulator or by a member of the list. This is the witness that the
certificate's target level is an actual recorded level, not merely an
upper bound. -/
theorem foldl_max_attained : ∀ (below : List (Literal × Nat)) (acc : Nat),
    below.foldl (fun a p => max a p.2) acc = acc ∨
    ∃ p ∈ below, p.2 = below.foldl (fun a p => max a p.2) acc
  | [], acc => Or.inl rfl
  | p :: rest, acc => by
      rw [List.foldl_cons]
      rcases foldl_max_attained rest (max acc p.2) with h | ⟨q, hq, hqv⟩
      · by_cases hle : acc ≤ p.2
        · refine Or.inr ⟨p, List.mem_cons_self .., ?_⟩
          have hmax : max acc p.2 = p.2 := by omega
          rw [h, hmax]
        · have hlt : p.2 ≤ acc := Nat.le_of_lt (Nat.lt_of_not_le hle)
          refine Or.inl ?_
          have hmax : max acc p.2 = acc := by omega
          rw [h, hmax]
      · exact Or.inr ⟨q, List.mem_cons_of_mem p hq, hqv⟩

/-- Attainment in the form the certificate uses: a nonzero fold-max is
attained by a member of the list. -/
theorem foldl_max_attained_mem {below : List (Literal × Nat)} {acc : Nat}
    (h : below.foldl (fun a p => max a p.2) acc ≠ acc) :
    ∃ p ∈ below, p.2 = below.foldl (fun a p => max a p.2) acc := by
  rcases foldl_max_attained below acc with h' | h'
  · exact absurd h' h
  · exact h'

/-! ## Normalization algebra (used by the canonical-record transfer) -/

/-- Normalization commutes with negation in the form the lookup needs. -/
theorem norm_negate_norm_local (l : Literal) :
    (l.norm).negate.norm = l.negate.norm := by
  cases l with
  | mk atom positive =>
      cases atom with
      | intLe s k => cases positive <;> rfl
      | boolEq s b => cases positive <;> cases b <;> rfl
      | intNe s k => cases positive <;> rfl

/-! ## Problem-level entailment transfer (the D1 bridge shape)

The certificate's only semantic premise is the leaf-level entailment of
the analyzer's learned clause. This section provides the transfer from
the PROBLEM-level statement (`Clause.EntailedBy`, the vocabulary the
audited analyzer theorems produce) into the leaf-level one, under the
explicit, problem-level bridge premise that every leaf solution is an
internal problem solution. The bridge premise is D1's (INTERFACES §4
item 16): only D1 can instantiate it on the compiled leaf
(`chronologicalLeaf problem constraintHoldsB`), where it is
`DomPruning.domLeaf_solution`'s statement. -/

/-- THE D1 BRIDGE (problem -> leaf entailment): a clause entailed by the
internal problem is entailed at every leaf solution, provided every leaf
solution is an internal problem solution. This is the only place the
problem semantics enters the certificate. -/
theorem learnedEntailed_of_entailedBy {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {leaf : Assignment → Bool} {c : Clause}
    (h : Clause.EntailedBy problem constraintHolds c)
    (hLeafSol : ∀ a, leaf a = true → ProblemSolution problem constraintHolds a) :
    LearnedEntailed leaf [c] := by
  intro c₀ hc₀ a hleaf
  rw [List.mem_singleton] at hc₀
  subst hc₀
  exact h a (hLeafSol a hleaf)

/-- Normalization of a clause's literals preserves problem entailment:
`Literal.norm_eval` makes every normalized literal interchangeable with
the original. This is what lets the analyzer's normalized pending
worklist be seeded from a raw conflict clause. -/
theorem entailedBy_map_norm {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop} {c : Clause}
    (h : Clause.EntailedBy problem constraintHolds c) :
    Clause.EntailedBy problem constraintHolds (c.map Literal.norm) := by
  intro a ha
  obtain ⟨l, hl, hev⟩ := h a ha
  exact ⟨l.norm, List.mem_map_of_mem (f := Literal.norm) hl, by
    rw [Literal.norm_eval]
    exact hev⟩

/-- Clause satisfaction transfers along a permutation: the analyzer's
tracked disjunction and its final record list the same literals in
different orders. -/
theorem satisfiedBy_of_perm {c c' : Clause} (hp : List.Perm c c')
    {a : Assignment} (h : c.SatisfiedBy a) : c'.SatisfiedBy a := by
  obtain ⟨l, hl, hev⟩ := h
  exact ⟨l, hp.subset hl, hev⟩

/-! ## The certificate -/

/-- The single certificate the scheduler consumes. Every field is a fact
about the analyzer's own output; none is a scheduler-supplied assumption. -/
structure RestorationCertificate (leaf : Assignment → Bool)
    (bs : BranchState leaf) (an : ConflictAnalysis) : Prop where
  /-- 1. the asserting literal belongs to the learned clause -/
  assertingMem : an.asserting ∈ an.learned
  /-- 2. the learned clause is globally entailed (supplied by the audited
      `analyzeStep_tracked` bridge, in the closure's own vocabulary) -/
  learnedEntailed : LearnedEntailed leaf [an.learned]
  /-- 3. every learned literal is falsified at the conflict state -/
  learnedFalsified : ∀ q ∈ an.learned,
    ∃ e ∈ bs.trail, e.literal = (q.negate).norm
  /-- 4. the asserting literal's falsifier is at the conflict level -/
  assertingAtConflict : ∃ e ∈ bs.trail,
    e.literal = (an.asserting.negate).norm ∧ e.level = bs.level
  /-- 5. every OTHER learned literal is falsified below the target, and no
      conflict-level entry falsifies it -/
  othersBelow : ∀ q ∈ an.learned, q ≠ an.asserting →
    (∃ e ∈ bs.trail, e.level ≤ an.backjumpLevel ∧ e.literal = (q.negate).norm) ∧
    (∀ e ∈ bs.trail, e.level = bs.level → e.literal ≠ (q.negate).norm)
  /-- 6. the target level is legal -/
  targetLegal : an.backjumpLevel ≤ bs.level
  /-- 7. a positive branch level strictly descends -/
  targetDescends : bs.level = 0 ∨ an.backjumpLevel < bs.level
  /-- 8. the target is the highest required surviving falsifier level -/
  targetMaximal : ∀ q ∈ an.learned, q ≠ an.asserting → ∀ e ∈ bs.trail,
    e.literal = (q.negate).norm → e.level ≤ an.backjumpLevel
  /-- 9. after restoration the asserting literal is not falsified -/
  assertingSurvives : ∀ e ∈ bs.trail, e.level ≤ an.backjumpLevel →
    e.literal ≠ (an.asserting.negate).norm
  /-- 10. the UNIT property in propagation's literal semantics: every leaf
      solution satisfying the surviving trail satisfies the assertion -/
  unitAfterRestore : ∀ a, leaf a = true →
    (∀ e ∈ bs.trail, e.level ≤ an.backjumpLevel → e.literal.eval a = some true) →
    an.asserting.eval a = some true
  /-- 11. CONSERVATION: every leaf solution represented by the restored
      checkpoint satisfies the whole learned clause -/
  conservation : ∀ a, leaf a = true →
    (∀ e ∈ bs.trail, e.level ≤ an.backjumpLevel → e.literal.eval a = some true) →
    ∀ q ∈ an.learned, q.eval a = some true ∨
      ∃ q' ∈ an.learned, q'.eval a = some true
  /-- 12. EXACT TARGET ATTAINMENT (the witness form of maximality): either
      the target is the root level, or some trail entry AT the target level
      falsifies a learned literal. The target is therefore an ACTUAL
      recorded level, not merely an upper bound: the scheduler can look up
      a checkpoint at it (`checkpointAt`). -/
  targetAttained : an.backjumpLevel = 0 ∨
    ∃ e ∈ bs.trail, e.level = an.backjumpLevel ∧
      ∃ q ∈ an.learned, e.literal = (q.negate).norm

/-! ## Derivation of the semantic conjuncts

The unit and conservation fields follow from entailment plus the surviving
falsifiers: every non-asserting learned literal is FALSE at a leaf
solution that satisfies the surviving trail, so the entailed clause's
satisfying literal must be the asserting one. -/

/-- A surviving trail entry falsifying `q` makes `q` false at any
assignment satisfying the trail. -/
theorem eval_false_of_surviving {bs : BranchState leaf} {q : Literal}
    {a : Assignment} {lvl : Nat}
    (h : ∃ e ∈ bs.trail, e.level ≤ lvl ∧ e.literal = (q.negate).norm)
    (htrail : ∀ e ∈ bs.trail, e.level ≤ lvl → e.literal.eval a = some true) :
    q.eval a = some false := by
  obtain ⟨e, he, hlev, hlit⟩ := h
  have hev := htrail e he hlev
  rw [hlit, Literal.norm_eval] at hev
  exact (Literal.eval_negate_false_iff q a).mp hev

/-- A leaf solution satisfying the surviving trail satisfies the learned
clause's asserting literal — the unit property, derived. -/
theorem asserting_of_entailed {an : ConflictAnalysis} {a : Assignment}
    (hent : LearnedEntailed leaf [an.learned])
    (_hmem : an.asserting ∈ an.learned)
    (hfalse : ∀ q ∈ an.learned, q ≠ an.asserting → q.eval a = some false)
    (hleaf : leaf a = true) :
    an.asserting.eval a = some true := by
  obtain ⟨q, hq, hqtrue⟩ := hent an.learned (List.mem_singleton_self _) a hleaf
  by_cases hqeq : q = an.asserting
  · rwa [hqeq] at hqtrue
  · exact absurd (hfalse q hq hqeq) (by rw [hqtrue]; simp)

/-! ## `findEntryOf` returns the LAST match

Everything the uniqueness and maximality conjuncts need follows from one
structural fact about the lookup: the entries returned by `findEntryOf`
are the LAST matching ones on the trail, so the trail splits around them.
With a level-sorted trail that pins every other falsifier BELOW them. -/

/-- `findEntryOf`'s trail decomposes around the returned entry: everything
after it (in `as.reverse`) is a NON-match. -/
theorem findEntryOf_last_match {trail : List TrailEntry} {l : Literal}
    {e : TrailEntry} (h : findEntryOf trail l = some e) :
    ∃ (as bs : List TrailEntry), trail = bs.reverse ++ e :: as.reverse ∧
      (∀ (a : TrailEntry), a ∈ as → litEqB a.literal l.norm = false) := by
  unfold findEntryOf at h
  obtain ⟨_, as, bs, hrw, hno⟩ := List.find?_eq_some_iff_append.mp h
  refine ⟨as, bs, ?_, ?_⟩
  · have hsq := congrArg List.reverse hrw
    simpa using hsq
  · intro a ha
    have hh := hno a ha
    cases hb : litEqB a.literal l.norm with
    | true => simp [hb] at hh
    | false => rfl

/-- MAXIMALITY: with a level-sorted trail, a lookup that returned an entry
at level `k` forces EVERY falsifier of that literal to have level at most
`k`. A falsifier after the returned entry would be a later match, which
`findEntryOf` cannot return; a falsifier before it is lower by
level-sortedness. -/
theorem falsifier_level_le {trail : List TrailEntry} {l : Literal}
    {e e₂ : TrailEntry} {k : Nat} (hs : TrailLevelSorted trail)
    (h : findEntryOf trail l = some e) (hlev : e.level = k)
    (hmem : e₂ ∈ trail) (hmatch : litEqB e₂.literal l.norm = true) :
    e₂.level ≤ k := by
  obtain ⟨as, bs, hrev, hno⟩ := findEntryOf_last_match h
  have hsorted : List.Pairwise (fun a b : TrailEntry => a.level ≤ b.level)
      (bs.reverse ++ e :: as.reverse) := by
    rw [← hrev]
    exact hs
  obtain ⟨_, _, hcross⟩ := List.pairwise_append.mp hsorted
  have hm : e₂ ∈ bs.reverse ++ e :: as.reverse := hrev ▸ hmem
  rcases List.mem_append.mp hm with hb | he
  · have hle := hcross e₂ hb e (List.mem_cons.mpr (Or.inl rfl))
    omega
  · rcases List.mem_cons.mp he with hEq | ha
    · rw [hEq]
      omega
    · exact absurd (hno e₂ (List.mem_reverse.mp ha)) (by rw [hmatch]; simp)

/-! ## The one driver condition the certificate names

"Precisely one learned literal is falsified at the current level" and "the
asserting literal is absent from the restored trail" both need the trail
to carry each literal at most once. That is NOT a consequence of the
current reachable-state invariant: a decision may pin a literal that an
earlier entry already recorded (deciding a forced value), which duplicates
it. The condition is therefore named here and taken as an explicit
hypothesis — the same condition B1's pivot-round bound needs, since a
duplicated literal is exactly what lets `markLit` re-mark a consumed pivot
and spin the worklist. -/

-- NOTE: `TrailLiteralsDistinct` now lives in `LeanFzn/Solver/UIP/BranchState.lean`
-- (moved by task A1, which promoted it to an eighth `ReachableState` field,
-- discharged at the construction sites). It is imported here; this duplicate
-- definition was removed by the coordinator to restore the build.

/-- The fold-max is strictly below `lvl` when every recorded level is. -/
theorem foldl_max_lt : ∀ (below : List (Literal × Nat)) (acc lvl : Nat),
    (∀ p ∈ below, p.2 < lvl) → acc < lvl →
      below.foldl (fun a p => max a p.2) acc < lvl
  | [], _, _, _, hacc => hacc
  | p :: rest, acc, lvl, hall, hacc => by
      rw [List.foldl_cons]
      refine foldl_max_lt rest (max acc p.2) lvl
        (fun q hq => hall q (List.mem_cons_of_mem p hq)) ?_
      have h1 : p.2 < lvl := hall p (List.mem_cons_self ..)
      rw [Nat.max_def]
      split <;> omega

/-! ## The below-level conjuncts for ONE recorded pair

The uniqueness and maximality facts come from `falsifier_level_le`
applied to the pair's own lookup: because the lookup returned the LAST
match, every other falsifier of the literal lies before it, hence — by
level-sortedness — at most at its level. -/

theorem below_pair_facts {leaf : Assignment → Bool} {bs : BranchState leaf}
    {below : List (Literal × Nat)} {lvl target : Nat} {p : Literal × Nat}
    (hbf : BelowFalsified bs.trail below) (hsorted : TrailLevelSorted bs.trail)
    (hstrict : ∀ p ∈ below, p.2 < lvl) (hmaxLe : ∀ p ∈ below, p.2 ≤ target)
    (hp : p ∈ below) :
    (∃ e ∈ bs.trail, e.level ≤ target ∧ e.literal = (p.1.negate).norm) ∧
    (∀ e₂ ∈ bs.trail, e₂.level = lvl → e₂.literal ≠ (p.1.negate).norm) ∧
    (∀ e₂ ∈ bs.trail, e₂.literal = (p.1.negate).norm → e₂.level ≤ target) := by
  obtain ⟨e, hfe, helit, hlevp⟩ := hbf p hp
  have hemem : e ∈ bs.trail := findEntryOf_mem _ _ _ hfe
  have hple : p.2 < lvl := hstrict p hp
  refine ⟨⟨e, hemem, Nat.le_trans (by omega) (hmaxLe p hp), helit⟩, ?_, ?_⟩
  · intro e₂ he₂ hlev₂ hlit₂
    have hm : litEqB e₂.literal (p.1.negate).norm = true := by
      rw [hlit₂]; simp [litEqB]
    have hfl := falsifier_level_le hsorted hfe hlevp he₂ hm
    omega
  · intro e₂ he₂ hlit₂
    have hm : litEqB e₂.literal (p.1.negate).norm = true := by
      rw [hlit₂]; simp [litEqB]
    exact Nat.le_trans (falsifier_level_le hsorted hfe hlevp he₂ hm) (hmaxLe p hp)

/-! ## THE certificate constructor

Every conjunct below is either read off the analyzer's output or derived
from the reachable-state invariant. The branch level must be positive
(the plan's "successful NON-ROOT result").

The constructor is stated on ANY successful `analyzeStep` run from the
initial worklist (`[c] none [] []`), so both entry points instantiate it:

* `analyzeTrail_certificate` — the historical constant allowance, kept as
  the reference (and for the axiom audit);
* `analyzeAtAllowance_certificate` — the COMPUTED allowance the scheduler
  actually runs (INTERFACES §1/§4 item 14, repair (d)).

The previously caller-supplied premises are DERIVED here:

* `TrailLiteralsDistinct bs.trail` from `hreach.distinct` (A1's eighth
  `ReachableState` field; `reachable_distinct` is FORM 2 of §2.1);
* `∀ p ∈ below, p.2 < bs.level` from `analyzeStep_preserves` applied to
  the run, whose trail-level boundedness is `hreach.wf.1`
  (`Proofs/Analyze.lean` records each fresh below-level pair at a level
  that is neither 0 nor the analysis level);
* the falsifier invariant `BelowFalsified` and the UIP-on-trail witness
  from `analyzeStep_invariants`/`analyzeStep_uip_on_trail` (B2's
  `AnalysisInvariants.lean`) at the initial invariant.

The only remaining premises are the equations tying `an` to the run's
`(below, uip)` pair and the LEAF-LEVEL entailment `hent`, which is D1's
problem→leaf bridge (ledger item 16) — never a per-deduction assumption. -/

theorem analyzeStep_certificate {leaf : Assignment → Bool} {orig : List Domain}
    {bs : BranchState leaf} {c : Clause} {an : ConflictAnalysis}
    {below : List (Literal × Nat)} {uip : Literal} {fuel : Nat}
    (hreach : ReachableState leaf orig bs)
    (hpos : 0 < bs.level)
    (h : analyzeStep bs.trail bs.level fuel [c] none [] [] = some (below, uip))
    (hanL : an.learned = uip.negate :: below.map (fun p => p.1))
    (hanA : an.asserting = uip.negate)
    (hanB : an.backjumpLevel = below.foldl (fun a p => max a p.2) 0)
    (hent : LearnedEntailed leaf [an.learned]) :
    RestorationCertificate leaf bs an := by
  have hbf : BelowFalsified bs.trail below :=
    analyzeStep_invariants bs.trail bs.level fuel [c] none [] []
      (analyzerInvariant_init bs.trail bs.level) below uip h
  obtain ⟨m, hmMem, hmLit, hmLev⟩ :=
    analyzeStep_uip_on_trail bs.trail bs.level fuel [c] none [] []
      (analyzerInvariant_init bs.trail bs.level) below uip h
  have hbelowStrict : ∀ p ∈ below, p.2 < bs.level :=
    (analyzeStep_preserves bs.trail bs.level fuel hreach.wf.1 [c] none [] []
      (by intro p hp; cases hp) (by intro p hp; cases hp) below uip h).2
  have hdistinct : TrailLiteralsDistinct bs.trail := hreach.distinct
  have hnorm : ∀ e ∈ bs.trail, e.literal = e.literal.norm := hreach.wf.2.1
  have huipnorm : uip = uip.norm := by
    rw [← hmLit]
    exact hnorm m hmMem
  have hass : m.literal = (an.asserting.negate).norm := by
    rw [hanA, Literal.negate_negate, ← huipnorm]
    exact hmLit
  have hmaxLe : ∀ p ∈ below, p.2 ≤ an.backjumpLevel := by
    intro p hp
    rw [hanB]
    exact foldl_max_mem_le below 0 p hp
  have hlg : an.asserting ∈ an.learned := by
    rw [hanL, hanA]
    exact List.mem_cons_self ..
  refine
    { assertingMem := hlg
      learnedEntailed := hent
      learnedFalsified := ?_
      assertingAtConflict := ?_
      othersBelow := ?_
      targetLegal := ?_
      targetDescends := ?_
      targetMaximal := ?_
      assertingSurvives := ?_
      unitAfterRestore := ?_
      conservation := ?_
      targetAttained := ?_ }
  · intro q hq
    rw [hanL] at hq
    rcases List.mem_cons.mp hq with hEq | hq
    · refine ⟨m, hmMem, ?_⟩
      rw [hEq, Literal.negate_negate, ← huipnorm]
      exact hmLit
    · obtain ⟨p, hp, hpq⟩ := List.mem_map.mp hq
      obtain ⟨e, hfe, helit, _⟩ := hbf p hp
      exact ⟨e, findEntryOf_mem _ _ _ hfe, by rw [← hpq]; exact helit⟩
  · exact ⟨m, hmMem, hass, hmLev⟩
  · intro q hq hne
    rw [hanL] at hq
    rcases List.mem_cons.mp hq with hEq | hq
    · exact absurd (by rw [hEq, hanA]) hne
    · obtain ⟨p, hp, hpq⟩ := List.mem_map.mp hq
      obtain ⟨hf1, hf2, _⟩ :=
        below_pair_facts hbf hreach.sorted hbelowStrict hmaxLe hp
      refine ⟨?_, ?_⟩
      · obtain ⟨e, he, hlev, hlit⟩ := hf1
        exact ⟨e, he, hlev, by rw [← hpq]; exact hlit⟩
      · intro e₂ he₂ hlev₂ hlit₂
        rw [← hpq] at hlit₂
        exact hf2 e₂ he₂ hlev₂ hlit₂
  · rw [hanB]
    have := below_max_strict below bs.level hbelowStrict
    omega
  · rw [hanB]
    exact Or.inr (foldl_max_lt below 0 bs.level hbelowStrict hpos)
  · intro q hq hne e₂ he₂ hlit₂
    rw [hanL] at hq
    rcases List.mem_cons.mp hq with hEq | hq
    · exact absurd (by rw [hEq, hanA]) hne
    · obtain ⟨p, hp, hpq⟩ := List.mem_map.mp hq
      rw [← hpq] at hlit₂
      exact (below_pair_facts hbf hreach.sorted hbelowStrict hmaxLe hp).2.2
        e₂ he₂ hlit₂
  . -- 9. the UIP entry does not survive: distinct trail literals
    intro e he hlevel hlit
    have hsame : e.literal = m.literal := hlit.trans hass.symm
    have heq : e = m := hdistinct.1 m hmMem e he (hsame.trans (hnorm m hmMem))
    rw [heq] at hlevel
    rw [hmLev] at hlevel
    have hlt : an.backjumpLevel < bs.level := by
      rw [hanB]
      rcases Nat.eq_zero_or_pos bs.level with h0 | hbb
      · omega
      · exact foldl_max_lt below 0 bs.level hbelowStrict hbb
    omega
  . -- 10. the unit property
    intro a hleaf htrail
    refine asserting_of_entailed (an := an) hent hlg ?_ hleaf
    intro q hq hne
    rw [hanL] at hq
    rcases List.mem_cons.mp hq with hEq | hq
    · exact absurd (by rw [hEq, hanA]) hne
    · obtain ⟨p, hp, hpq⟩ := List.mem_map.mp hq
      obtain ⟨⟨e, he, hlev, hlit⟩, _, _⟩ :=
        below_pair_facts hbf hreach.sorted hbelowStrict hmaxLe hp
      exact eval_false_of_surviving
        ⟨e, he, hlev, by rw [← hpq]; exact hlit⟩ htrail
  . -- 11. conservation
    intro a hleaf _ q hq
    obtain ⟨q', hq', hq'true⟩ := hent an.learned (List.mem_singleton_self _) a hleaf
    exact Or.inr ⟨q', hq', hq'true⟩
  . -- 12. exact target attainment: the fold-max is attained by a pair
    rcases Nat.eq_zero_or_pos an.backjumpLevel with h0 | hposT
    · exact Or.inl h0
    · have hne : below.foldl (fun a p => max a p.2) 0 ≠ 0 := by
        rw [← hanB]
        omega
      obtain ⟨p, hp, hpv⟩ := foldl_max_attained_mem hne
      obtain ⟨e, hfe, helit, hlevp⟩ := hbf p hp
      refine Or.inr ⟨e, findEntryOf_mem _ _ _ hfe, ?_, p.1, ?_, helit⟩
      · rw [hlevp, hpv, hanB]
      · rw [hanL]
        refine List.mem_cons_of_mem _ ?_
        exact List.mem_map_of_mem (f := fun p : Literal × Nat => p.1) hp

/-- The certificate at the historical constant allowance (the reference
entry point; the axiom audit cites it). The formerly caller-supplied
distinctness and strictness premises are derived by
`analyzeStep_certificate`. -/
theorem analyzeTrail_certificate {leaf : Assignment → Bool} {orig : List Domain}
    {bs : BranchState leaf} {c : Clause} {an : ConflictAnalysis}
    {below : List (Literal × Nat)} {uip : Literal}
    (hreach : ReachableState leaf orig bs)
    (hpos : 0 < bs.level)
    (h : analyzeTrail bs.trail bs.level c = some (below, uip))
    (hanL : an.learned = uip.negate :: below.map (fun p => p.1))
    (hanA : an.asserting = uip.negate)
    (hanB : an.backjumpLevel = below.foldl (fun a p => max a p.2) 0)
    (hent : LearnedEntailed leaf [an.learned]) :
    RestorationCertificate leaf bs an :=
  analyzeStep_certificate (fuel := 4 * bs.trail.length * bs.trail.length + 256)
    hreach hpos h hanL hanA hanB hent

/-- THE COMPUTED-ALLOWANCE CERTIFICATE (INTERFACES §1/§4 item 14, repair
(d)): the certificate is produced from the ACTUAL success equation of
`analyzeAtAllowance` — the entry point that consumes `analysisFuel` —
never from the historical `analyzeTrail` result. -/
theorem analyzeAtAllowance_certificate {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf} {c : Clause}
    {an : ConflictAnalysis} {below : List (Literal × Nat)} {uip : Literal}
    (hreach : ReachableState leaf orig bs)
    (hpos : 0 < bs.level)
    (h : analyzeAtAllowance bs.trail bs.level c = some (below, uip))
    (hanL : an.learned = uip.negate :: below.map (fun p => p.1))
    (hanA : an.asserting = uip.negate)
    (hanB : an.backjumpLevel = below.foldl (fun a p => max a p.2) 0)
    (hent : LearnedEntailed leaf [an.learned]) :
    RestorationCertificate leaf bs an :=
  analyzeStep_certificate (fuel := analysisFuel bs.trail c)
    hreach hpos h hanL hanA hanB hent

/-- The same certificate at the run's own record `ConflictAnalysis.ofRun`,
whose `hanL`/`hanA`/`hanB` equations hold by `rfl`: this is the form the
classified success case and the `analyzeWithAllowance` entry point
consume. -/
theorem analyzeAtAllowance_certificate_ofRun {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf} {c : Clause}
    {below : List (Literal × Nat)} {uip : Literal}
    (hreach : ReachableState leaf orig bs)
    (hpos : 0 < bs.level)
    (h : analyzeAtAllowance bs.trail bs.level c = some (below, uip))
    (hent : LearnedEntailed
      leaf [(ConflictAnalysis.ofRun below uip).learned]) :
    RestorationCertificate leaf bs (ConflictAnalysis.ofRun below uip) :=
  analyzeAtAllowance_certificate hreach hpos h rfl rfl rfl hent

/-- THE SINGLE CONCRETE THEOREM the scheduler's learn/backjump/assert
transition consumes: from a REACHABLE, non-root branch and the ACTUAL
success equation of the computed-allowance entry point
(`BranchState.analyzeWithAllowance`), the certificate of the returned
`ConflictAnalysis` is produced. No separate `hanL`/`hanA`/`hanB`, no
distinctness, no strictness, no falsifier hypothesis: the equations are
`rfl` and every other conjunct is derived.

`hent` is the ONLY semantic premise and is problem-level (D1's bridge,
ledger item 16): the leaf-level entailment of the analysis's learned
clause. It is never per-deduction. -/
theorem analyzeWithAllowance_certificate {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf} {c : Clause}
    {an : ConflictAnalysis}
    (hreach : ReachableState leaf orig bs)
    (hpos : 0 < bs.level)
    (h : bs.analyzeWithAllowance c = some an)
    (hent : LearnedEntailed leaf [an.learned]) :
    RestorationCertificate leaf bs an := by
  unfold BranchState.analyzeWithAllowance at h
  cases hA : analyzeAtAllowance bs.trail bs.level c with
  | none => rw [hA] at h; simp at h
  | some p =>
      obtain ⟨below, uip⟩ := p
      rw [hA] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      exact analyzeAtAllowance_certificate_ofRun hreach hpos hA hent

/-! ## THE problem-level certificate (ledger item 16: the D1 bridge)

The certificate constructors above take the leaf-level entailment
`LearnedEntailed leaf [an.learned]` as their only semantic premise. This
section DERIVES it from the audited analyzer-entailment lift
`analyzeStep_tracked` (`Proofs/Analyze.lean`), whose conclusion is the
PROBLEM-level `Clause.EntailedBy`. The remaining premises are all
problem-level and belong to D1 (INTERFACES §4 item 16):

* `hconf` — the conflict clause is entailed by the internal problem
  (A3's `conflictEntailed` provides the leaf-level form; the
  problem-level origin is D1's clause provenance);
* `hleafSol` — every leaf solution is an internal problem solution (the
  `chronologicalLeaf`/`domLeaf_solution` bridge);
* `hreasons` — every trail reason is problem-valid for its pivot (A3's
  `boxPropagators_reasons` at the supported kit, lifted by D1);
* `hrootFacts` — level-0 trail entries hold at every internal solution;
* `hrnorm` — reason clauses consist of normalized literals (the reason
  construction discipline; A3/D1).

Nothing here is per-deduction: all five are properties of the problem,
the kit and the trail, discharged once per configuration. -/

/-- The initial worklist of the executed analysis is the conflict clause
in normalized form: the tracked-disjunction seed of `analyzeStep_tracked`
follows from problem entailment of the conflict clause. -/
theorem pendingLits_singleton (c : Clause) :
    pendingLits [c] none = c.map Literal.norm := by
  unfold pendingLits
  simp [skipEq]

/-- `Tracked` holds at the analyzer's initial state whenever the conflict
clause is problem-entailed. -/
theorem tracked_init {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop} {c : Clause}
    (hconf : Clause.EntailedBy problem constraintHolds c) :
    Tracked problem constraintHolds [c] none [] [] := by
  unfold Tracked marksNegs learntLits
  rw [pendingLits_singleton]
  simpa using entailedBy_map_norm hconf

/-- THE PROBLEM-LEVEL CERTIFICATE CONSTRUCTOR: the certificate of the
run's own record is produced from ANY successful `analyzeStep` run — in
particular the computed-allowance one — with the learned-clause
entailment DERIVED from the audited problem-level lift instead of
assumed. `hdistinct`, `hbelowStrict` and the falsifier invariants are
derived internally from `ReachableState` (A1/B1), exactly as in
`analyzeStep_certificate`. -/
theorem analyzeStep_certificate_of_problem {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {leaf : Assignment → Bool} {orig : List Domain} {bs : BranchState leaf}
    {c : Clause} {below : List (Literal × Nat)} {uip : Literal} {fuel : Nat}
    (hreach : ReachableState leaf orig bs)
    (hpos : 0 < bs.level)
    (h : analyzeStep bs.trail bs.level fuel [c] none [] [] = some (below, uip))
    (hconf : Clause.EntailedBy problem constraintHolds c)
    (hleafSol : ∀ a, leaf a = true → ProblemSolution problem constraintHolds a)
    (hreasons : ∀ e ∈ bs.trail, ∀ r ∈ e.reason,
      Reason.Valid problem constraintHolds r e.literal)
    (hrootFacts : RootFacts problem constraintHolds bs.trail)
    (hrnorm : ∀ e ∈ bs.trail, ∀ r ∈ e.reason, ∀ l ∈ r.clause, l = l.norm) :
    RestorationCertificate leaf bs (ConflictAnalysis.ofRun below uip) := by
  have htracked := analyzeStep_tracked (problem := problem)
    (constraintHolds := constraintHolds) bs.trail bs.level hreasons hrootFacts
    hrnorm fuel [c] none [] [] (tracked_init hconf)
    (by intro e he; cases he) below uip h
  have hent : LearnedEntailed leaf [(ConflictAnalysis.ofRun below uip).learned] := by
    intro c₀ hc₀ a hleaf
    rw [List.mem_singleton] at hc₀
    subst hc₀
    obtain ⟨l, hl, hev⟩ := htracked a (hleafSol a hleaf)
    have hmem := (List.perm_middle (l₁ := learntLits below) (a := uip.negate)
      (l₂ := [])).mem_iff.mp hl
    exact ⟨l, by simpa [learntLits, ConflictAnalysis.ofRun_learned] using hmem,
      hev⟩
  exact analyzeStep_certificate (an := ConflictAnalysis.ofRun below uip)
    hreach hpos h rfl rfl rfl hent

/-- THE COMPUTED-ALLOWANCE PROBLEM-LEVEL CERTIFICATE: the plan's target
theorem. The success equation is `analyzeAtAllowance`'s — the entry
point the scheduler runs — and the learned-clause entailment is derived
from the problem-level lift, so the only remaining premises are D1's
problem/kit bridges (ledger item 16). -/
theorem analyzeAtAllowance_certificate_of_problem {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {leaf : Assignment → Bool} {orig : List Domain} {bs : BranchState leaf}
    {c : Clause} {below : List (Literal × Nat)} {uip : Literal}
    (hreach : ReachableState leaf orig bs)
    (hpos : 0 < bs.level)
    (h : analyzeAtAllowance bs.trail bs.level c = some (below, uip))
    (hconf : Clause.EntailedBy problem constraintHolds c)
    (hleafSol : ∀ a, leaf a = true → ProblemSolution problem constraintHolds a)
    (hreasons : ∀ e ∈ bs.trail, ∀ r ∈ e.reason,
      Reason.Valid problem constraintHolds r e.literal)
    (hrootFacts : RootFacts problem constraintHolds bs.trail)
    (hrnorm : ∀ e ∈ bs.trail, ∀ r ∈ e.reason, ∀ l ∈ r.clause, l = l.norm) :
    RestorationCertificate leaf bs (ConflictAnalysis.ofRun below uip) :=
  analyzeStep_certificate_of_problem (fuel := analysisFuel bs.trail c)
    hreach hpos h hconf hleafSol hreasons hrootFacts hrnorm

/-- The single concrete theorem of the plan's B2 surface, with the
entailment derived: from `BranchState.analyzeWithAllowance`'s success
(the scheduler's entry point) and the problem-level bridges, the
certificate of the returned record. -/
theorem analyzeWithAllowance_certificate_of_problem
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {leaf : Assignment → Bool} {orig : List Domain} {bs : BranchState leaf}
    {c : Clause} {an : ConflictAnalysis}
    (hreach : ReachableState leaf orig bs)
    (hpos : 0 < bs.level)
    (h : bs.analyzeWithAllowance c = some an)
    (hconf : Clause.EntailedBy problem constraintHolds c)
    (hleafSol : ∀ a, leaf a = true → ProblemSolution problem constraintHolds a)
    (hreasons : ∀ e ∈ bs.trail, ∀ r ∈ e.reason,
      Reason.Valid problem constraintHolds r e.literal)
    (hrootFacts : RootFacts problem constraintHolds bs.trail)
    (hrnorm : ∀ e ∈ bs.trail, ∀ r ∈ e.reason, ∀ l ∈ r.clause, l = l.norm) :
    RestorationCertificate leaf bs an := by
  unfold BranchState.analyzeWithAllowance at h
  cases hA : analyzeAtAllowance bs.trail bs.level c with
  | none => rw [hA] at h; simp at h
  | some p =>
      obtain ⟨below, uip⟩ := p
      rw [hA] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      exact analyzeAtAllowance_certificate_of_problem hreach hpos hA hconf
        hleafSol hreasons hrootFacts hrnorm

/-! ## B2 — the classified results (success / root / unsupported)

INTERFACES §2.3 requires the three outcomes of `analyzeClassified` to
produce SEPARATE results, so no consumer can read a global claim out of a
`none`:

* `.success below uip` — the restoration certificate of the run's own
  record (`ConflictAnalysis.ofRun below uip`), from the actual success
  equation of the computed allowance;
* `.rootContradiction` — a level-0 falsified, entailed clause excludes
  every assignment satisfying the trail (hence every REPRESENTED leaf
  solution); the completed-trace witness that this is a SEMANTIC stop
  rather than a fuel cut-off lives downstream of this module
  (`Proofs/ConflictResolution.lean`, which can import B1's
  `analyzeTrace` theorems);
* `.unsupported` — no asserting result above the root: NO analysis record
  exists at all (`analyzeWithAllowance = none`), so the
  learn/backjump/assert transition is impossible and the scheduler must
  take the fallback; NEVER an UNSAT verdict.

The verdicts are tied to the frozen `ConflictShape` classification
(`ConflictResolution.lean`): success is a non-local analysable/root
shape, `.rootContradiction` is `.root`, `.unsupported` is `.analyzable`. -/

/-- Inversion of the success verdict: it is exactly the computed-allowance
success equation. (B1's `AnalysisCompletion` owns its own iff; this file
is upstream of it and re-derives the direction it needs.) -/
theorem analyzeClassified_success_imp {trail : List TrailEntry} {lvl : Nat}
    {c : Clause} {below : List (Literal × Nat)} {uip : Literal}
    (h : analyzeClassified trail lvl c = .success below uip) :
    analyzeAtAllowance trail lvl c = some (below, uip) := by
  unfold analyzeClassified at h
  generalize hA : analyzeAtAllowance trail lvl c = y at h
  cases y with
  | none =>
      by_cases h0 : lvl = 0 <;> simp [h0] at h
  | some p =>
      obtain ⟨b, u⟩ := p
      simp only [AnalysisOutcome.success.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl

/-- Inversion of the root verdict: `none` at level 0. -/
theorem analyzeClassified_root_imp {trail : List TrailEntry} {lvl : Nat}
    {c : Clause} (h : analyzeClassified trail lvl c = .rootContradiction) :
    analyzeAtAllowance trail lvl c = none ∧ lvl = 0 := by
  unfold analyzeClassified at h
  generalize hA : analyzeAtAllowance trail lvl c = y at h
  cases y with
  | none =>
      by_cases h0 : lvl = 0
      · exact ⟨rfl, h0⟩
      · simp [h0] at h
  | some p =>
      simp at h

/-- Inversion of the unsupported verdict: `none` above the root. -/
theorem analyzeClassified_unsupported_imp {trail : List TrailEntry} {lvl : Nat}
    {c : Clause} (h : analyzeClassified trail lvl c = .unsupported) :
    analyzeAtAllowance trail lvl c = none ∧ lvl ≠ 0 := by
  unfold analyzeClassified at h
  generalize hA : analyzeAtAllowance trail lvl c = y at h
  cases y with
  | none =>
      by_cases h0 : lvl = 0
      · simp [h0] at h
      · exact ⟨rfl, h0⟩
  | some p =>
      simp at h

/-- The success verdict IS the allowance success (forward direction). -/
theorem analyzeClassified_success_of_allowance {trail : List TrailEntry}
    {lvl : Nat} {c : Clause} {below : List (Literal × Nat)} {uip : Literal}
    (h : analyzeAtAllowance trail lvl c = some (below, uip)) :
    analyzeClassified trail lvl c = .success below uip := by
  simp only [analyzeClassified, h]

/-- SUCCESS: the classified success case produces the certificate of the
run's own record — the `hanL`/`hanA`/`hanB` equations hold by `rfl`. The
only semantic premise is the leaf-level entailment (D1's bridge shape;
`analyzeClassified_success_certificate_of_problem` derives it from the
problem-level lift). -/
theorem analyzeClassified_success_certificate {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf} {c : Clause}
    {below : List (Literal × Nat)} {uip : Literal}
    (hreach : ReachableState leaf orig bs)
    (hpos : 0 < bs.level)
    (hcl : analyzeClassified bs.trail bs.level c = .success below uip)
    (hent : LearnedEntailed
      leaf [(ConflictAnalysis.ofRun below uip).learned]) :
    RestorationCertificate leaf bs (ConflictAnalysis.ofRun below uip) :=
  analyzeAtAllowance_certificate_ofRun hreach hpos
    (analyzeClassified_success_imp hcl) hent

/-- SUCCESS (problem-level): the classified success case produces the
certificate with the learned-clause entailment DERIVED from the
problem-level lift. Every premise named here is a D1 bridge (ledger item
16); none is an analysis-result assumption. -/
theorem analyzeClassified_success_certificate_of_problem
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {leaf : Assignment → Bool} {orig : List Domain} {bs : BranchState leaf}
    {c : Clause} {below : List (Literal × Nat)} {uip : Literal}
    (hreach : ReachableState leaf orig bs)
    (hpos : 0 < bs.level)
    (hcl : analyzeClassified bs.trail bs.level c = .success below uip)
    (hconf : Clause.EntailedBy problem constraintHolds c)
    (hleafSol : ∀ a, leaf a = true → ProblemSolution problem constraintHolds a)
    (hreasons : ∀ e ∈ bs.trail, ∀ r ∈ e.reason,
      Reason.Valid problem constraintHolds r e.literal)
    (hrootFacts : RootFacts problem constraintHolds bs.trail)
    (hrnorm : ∀ e ∈ bs.trail, ∀ r ∈ e.reason, ∀ l ∈ r.clause, l = l.norm) :
    RestorationCertificate leaf bs (ConflictAnalysis.ofRun below uip) :=
  analyzeAtAllowance_certificate_of_problem hreach hpos
    (analyzeClassified_success_imp hcl) hconf hleafSol hreasons hrootFacts hrnorm

/-- A nonempty clause has `isEmpty = false` — the gate that keeps a
classified conflict out of the local shape. -/
theorem isEmpty_eq_false {c : Clause} (h : 1 ≤ c.length) : c.isEmpty = false := by
  cases hb : c.isEmpty with
  | false => rfl
  | true =>
      exfalso
      have hnil : c = [] := List.isEmpty_iff.mp hb
      have hlen : c.length = 0 := by rw [hnil]; rfl
      omega

/-- The success verdict is never the LOCAL shape: the conflict clause is
nonempty (`AnalyzerInput.nonempty`), so `ConflictShape.ofConflict` is
`.root` or `.analyzable` — the case the learn/backjump/assert transition
may consume. -/
theorem conflictShape_of_analyzeClassified_success {leaf : Assignment → Bool}
    {bs : BranchState leaf} (hin : AnalyzerInput leaf bs)
    {below : List (Literal × Nat)} {uip : Literal}
    (_hcl : analyzeClassified bs.trail bs.level hin.conflict = .success below uip) :
    ConflictShape.ofConflict bs.level hin.conflict ≠ .local := by
  have hne : hin.conflict.isEmpty = false := isEmpty_eq_false hin.nonempty
  rw [ConflictShape.ofConflict, hne]
  by_cases h0 : bs.level = 0 <;> simp [h0]

/-- ROOT CONTRADICTION (separate result, trace-free core): at level 0 a
falsified, entailed clause is a proof of contradiction — every assignment
satisfying the trail (hence every represented leaf solution) is excluded,
the shape is `.root`, and no analysis record exists. The completed-trace
witness that the stop is semantic (not a fuel cut-off) is
`Proofs/ConflictResolution.analyzeClassified_root_semanticStop`. -/
theorem analyzeClassified_root_contradiction {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf}
    (hin : AnalyzerInput leaf bs) (_hreach : ReachableState leaf orig bs)
    (hroot : analyzeClassified bs.trail bs.level hin.conflict
      = .rootContradiction) :
    bs.level = 0 ∧
    analyzeAtAllowance bs.trail bs.level hin.conflict = none ∧
    ConflictShape.ofConflict bs.level hin.conflict = .root ∧
    (∀ a, leaf a = true →
      (∀ e ∈ bs.trail, e.literal.eval a = some true) → False) ∧
    (∀ a, leaf a = true → bs.Represents a → False) := by
  obtain ⟨hA, hlvl0⟩ := analyzeClassified_root_imp hroot
  have hexcl : ∀ a, leaf a = true →
      (∀ e ∈ bs.trail, e.literal.eval a = some true) → False := by
    intro a hleaf htrail
    obtain ⟨q, hq, hqtrue⟩ :=
      hin.entailed hin.conflict (List.mem_singleton_self _) a hleaf
    obtain ⟨e, he, hlit⟩ := hin.falsified q hq
    have hev := htrail e he
    rw [hlit] at hev
    have hqfalse := (Literal.eval_negate_false_iff q a).mp hev
    rw [hqtrue] at hqfalse
    exact absurd hqfalse (by simp)
  have hshape : ConflictShape.ofConflict bs.level hin.conflict = .root := by
    have hne : hin.conflict.isEmpty = false := isEmpty_eq_false hin.nonempty
    simp [ConflictShape.ofConflict, hne, hlvl0]
  exact ⟨hlvl0, hA, hshape, hexcl,
    fun a hleaf hrep => hexcl a hleaf hrep.2.1⟩

/-- UNSUPPORTED LOCAL EXPLANATION (separate result, trace-free core):
above the root, a `none` result means no asserting analysis exists —
`analyzeWithAllowance` returns `none`, the shape is `.analyzable`, and
no learn/backjump/assert transition can be taken. NEVER an UNSAT verdict.
The completed-trace witness is the downstream
`analyzeClassified_unsupported_semanticStop`. -/
theorem analyzeClassified_unsupported_local {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf}
    (hin : AnalyzerInput leaf bs) (_hreach : ReachableState leaf orig bs)
    (huns : analyzeClassified bs.trail bs.level hin.conflict
      = .unsupported) :
    bs.level ≠ 0 ∧
    analyzeAtAllowance bs.trail bs.level hin.conflict = none ∧
    bs.analyzeWithAllowance hin.conflict = none ∧
    ConflictShape.ofConflict bs.level hin.conflict = .analyzable := by
  obtain ⟨hnone, hlvl⟩ := analyzeClassified_unsupported_imp huns
  have hana : bs.analyzeWithAllowance hin.conflict = none := by
    unfold BranchState.analyzeWithAllowance
    rw [hnone]
    rfl
  have hshape : ConflictShape.ofConflict bs.level hin.conflict = .analyzable := by
    have hne : hin.conflict.isEmpty = false := isEmpty_eq_false hin.nonempty
    rw [ConflictShape.ofConflict, hne]
    by_cases h0 : bs.level = 0
    · exact absurd h0 hlvl
    · simp [h0]
  exact ⟨hlvl, hnone, hana, hshape⟩

/-! ## B2 — normalization: the form whose enqueue obligations are structural

The analyzer's raw record stores the UNNORMALIZED negation of the UIP as
its learned clause's head (`uip.negate`), while the enqueue sites append
the NORMALIZED asserting literal (`BackjumpPlan.execute` appends
`p.asserting.norm`). For a positive Boolean UIP the two differ:
`(posBool s b).negate.norm = posBool s (!b)` (`boolUip_norm_gap` below),
so the structural membership obligation
`(asserting.norm ∈ learned) = True` is NOT a consequence of the raw
record. The canonical record (`ConflictAnalysis.normalized`) makes it one
without changing any semantics (`Literal.norm_eval`), and the transfer
lemma `RestorationCertificate.normalized` lifts every certificate to the
canonical form — this is the shape the scheduler's plan should use. -/

/-- The canonical record carries a certificate whenever the raw one does:
normalization preserves evaluation and commutes with negation for the
certificate's falsifier lookups (`norm_negate_norm_local`). -/
theorem RestorationCertificate.normalized {leaf : Assignment → Bool}
    {bs : BranchState leaf} {an : ConflictAnalysis}
    (h : RestorationCertificate leaf bs an) :
    RestorationCertificate leaf bs an.normalized := by
  have hL : an.normalized.learned = an.learned.map Literal.norm := rfl
  have hA : an.normalized.asserting = an.asserting.norm := rfl
  refine
    { assertingMem := List.mem_map_of_mem (f := Literal.norm) h.assertingMem
      learnedEntailed := ?_
      learnedFalsified := ?_
      assertingAtConflict := ?_
      othersBelow := ?_
      targetLegal := h.targetLegal
      targetDescends := h.targetDescends
      targetMaximal := ?_
      assertingSurvives := ?_
      unitAfterRestore := ?_
      conservation := ?_
      targetAttained := ?_ }
  · -- 2. the normalized learned clause is entailed
    intro c hc a hleaf
    rw [List.mem_singleton] at hc
    subst hc
    rw [hL]
    obtain ⟨q, hq, hqtrue⟩ :=
      h.learnedEntailed an.learned (List.mem_singleton_self _) a hleaf
    exact ⟨q.norm, List.mem_map_of_mem (f := Literal.norm) hq, by
      rw [Literal.norm_eval]
      exact hqtrue⟩
  · -- 3. falsifiers transfer through `norm_negate_norm_local`
    intro q hq
    rw [hL, List.mem_map] at hq
    obtain ⟨q₀, hq₀, rfl⟩ := hq
    obtain ⟨e, he, hlit⟩ := h.learnedFalsified q₀ hq₀
    exact ⟨e, he, by simpa [norm_negate_norm_local] using hlit⟩
  · -- 4. the asserting literal's falsifier is unchanged up to `norm`
    obtain ⟨e, he, hlit, hlev⟩ := h.assertingAtConflict
    rw [hA]
    exact ⟨e, he, by simpa [norm_negate_norm_local] using hlit, hlev⟩
  · -- 5. below-level conjuncts
    intro q hq hne
    rw [hL, List.mem_map] at hq
    obtain ⟨q₀, hq₀, rfl⟩ := hq
    have hne₀ : q₀ ≠ an.asserting := fun hc => hne (by rw [hc]; rfl)
    obtain ⟨h1, h2⟩ := h.othersBelow q₀ hq₀ hne₀
    refine ⟨?_, ?_⟩
    · obtain ⟨e, he, hlev, hlit⟩ := h1
      exact ⟨e, he, hlev, by simpa [norm_negate_norm_local] using hlit⟩
    · intro e he hlevel hlit
      exact h2 e he hlevel (by simpa [norm_negate_norm_local] using hlit)
  · -- 8. target maximality
    intro q hq hne e he hlit
    rw [hL, List.mem_map] at hq
    obtain ⟨q₀, hq₀, rfl⟩ := hq
    have hne₀ : q₀ ≠ an.asserting := fun hc => hne (by rw [hc]; rfl)
    exact h.targetMaximal q₀ hq₀ hne₀ e he
      (by simpa [norm_negate_norm_local] using hlit)
  · -- 9. the asserting literal still does not survive
    intro e he hlev hlit
    exact h.assertingSurvives e he hlev
      (by simpa [ConflictAnalysis.normalized_asserting,
        norm_negate_norm_local] using hlit)
  · -- 10. the unit property is evaluation-only
    intro a hleaf htrail
    rw [hA, Literal.norm_eval]
    exact h.unitAfterRestore a hleaf htrail
  · -- 11. conservation
    intro a hleaf htrail q hq
    rw [hL, List.mem_map] at hq
    obtain ⟨q₀, hq₀, rfl⟩ := hq
    rcases h.conservation a hleaf htrail q₀ hq₀ with hq' | ⟨q', hq', hq'true⟩
    · exact Or.inl (by rw [Literal.norm_eval]; exact hq')
    · exact Or.inr ⟨q'.norm, List.mem_map_of_mem (f := Literal.norm) hq',
        by rw [Literal.norm_eval]; exact hq'true⟩
  · -- 12. the target stays attained
    rcases h.targetAttained with h0 | ⟨e, he, hlev, q, hq, hlit⟩
    · exact Or.inl h0
    · exact Or.inr ⟨e, he, hlev, q.norm,
        List.mem_map_of_mem (f := Literal.norm) hq,
        by simpa [norm_negate_norm_local] using hlit⟩

/-- The structural membership obligation `(asserting.norm ∈ learned) = True`
follows from the certificate plus normalization-stability of the asserting
literal. The canonical record satisfies the stability by
`ConflictAnalysis.normalized_asserting_norm`, so the canonical certificate
discharges the obligation unconditionally. -/
theorem RestorationCertificate.asserting_norm_mem_of_stable
    {leaf : Assignment → Bool} {bs : BranchState leaf} {an : ConflictAnalysis}
    (h : RestorationCertificate leaf bs an)
    (hstable : an.asserting.norm = an.asserting) :
    (an.asserting.norm ∈ an.learned) = True := by
  rw [hstable]
  exact eq_true h.assertingMem

/-- THE DOCUMENTED INTERFACE GAP: for a positive Boolean UIP the analyzer's
learned-clause head is NOT its own normal form, so the raw record's
asserting literal does not normalize into the raw clause. The scheduler's
enqueue appends the normalized literal (`BackjumpPlan.execute`), so C2's
`(p.asserting.norm ∈ p.learned) = True` premise is not derivable from the
raw record; using the canonical record (or restating the premise up to
`norm`) is required. The proof is a concrete computation. -/
theorem boolUip_norm_gap :
    ((posBool 0 false).negate).norm = posBool 0 true ∧
    ((posBool 0 false).negate).norm ≠ (posBool 0 false).negate := by
  refine ⟨rfl, ?_⟩
  intro h
  exact absurd h (by decide)

/-- The canonical record makes the membership obligation hold by
`ConflictAnalysis.normalized_asserting_norm`. -/
theorem RestorationCertificate.normalized_asserting_norm_mem
    {leaf : Assignment → Bool} {bs : BranchState leaf} {an : ConflictAnalysis}
    (h : RestorationCertificate leaf bs an) :
    (an.normalized.asserting.norm ∈ an.normalized.learned) = True :=
  (h.normalized).asserting_norm_mem_of_stable
    (ConflictAnalysis.normalized_asserting_norm an)

/-- NEGATION-STABILITY GUARD for the enqueue's chronology obligation,
WHOLE-CLAUSE (REFUTED AS STATED; retained for compatibility only): every
learned literal's negation is a normal form. This is the same discipline
`StepChronology`/`DomReasonRecorded` impose on reason clauses
(INTERFACES §2.2): a reason's non-pivot literals must have exact trail
falsifiers, and the trail stores normal forms.

J1 ROUND 2 FINDING (kernel-checked): as a statement about a WHOLE clause
this form is FALSE for canonical Boolean learned literals:
`posBool s b` IS a normal form while its negation is not
(`(posBool s b).negate.norm = posBool s (!b)`, `boolUip_norm_gap`), so
`¬ NegStable [posBool 0 true]` (Proofs/HdeadCkpt.lean,
`negStable_posBool_refuted`). The consumers only ever apply the guard at
a literal `q` with `q ≠ an.asserting` in hand, because the asserting
literal's falsifier is handled by the certificate's own
`assertingSurvives`/`othersBelow` conjuncts. The honest family is
therefore `NegStableAvoiding an.asserting an.learned` below; the
restated chronology lemmas consume it. -/
def NegStable (c : Clause) : Prop := ∀ q ∈ c, (q.negate).norm = q.negate

/-- THE HONEST NEGATION-STABILITY FAMILY (J1 round 2): negation-stability
is only required of the NON-asserting learned literals. This is exactly
the discipline the restoration chain consumes: `othersBelow` supplies the
falsifier of every `q ≠ an.asserting` (the asserting literal's own
falsifier is the conflict-level entry dropped by the jump), and
`restore_chronology_of_certificate` / `restore_filter_chronology_of_certificate`
apply the guard at such a `q` only. The whole-clause form `NegStable` is
kept above as the (refuted) strong variant and transfers into this one by
`NegStable.avoiding`.

The condition is VACUOUSLY true for a unit-fragment learned clause
(`an.learned = [an.asserting]`): see
`negStableAvoiding_of_learned_eq_singleton`. -/
def NegStableAvoiding (l : Literal) (c : Clause) : Prop :=
  ∀ q ∈ c, q ≠ l → (q.negate).norm = q.negate

/-- The refuted whole-clause form still implies the honest family (drop
the extra hypothesis). -/
theorem NegStable.avoiding {l : Literal} {c : Clause} (h : NegStable c) :
    NegStableAvoiding l c :=
  fun q hq _ => h q hq

/-- A learned clause that IS the singleton of the asserting literal has an
EMPTY non-asserting part, so the honest guard holds vacuously. This is the
unit fragment's shape (`an.learned = [an.asserting]`; see
`Proofs.HdeadCkpt.supportedLearned_eq_asserting_of_unitRun`). -/
theorem negStableAvoiding_of_learned_eq_singleton {an : ConflictAnalysis}
    (h : an.learned = [an.asserting]) :
    NegStableAvoiding an.asserting an.learned := by
  intro q hq hne
  rw [h] at hq
  rw [List.mem_singleton] at hq
  exact absurd hq hne

/-- A normalized literal whose atom is not a Boolean equation is
negation-stable: the one non-stable case is exactly the positive Boolean
literal (which normalizes to the opposite pin). -/
theorem negate_norm_eq_of_norm_not_bool {l : Literal} (hnorm : l = l.norm)
    (hnot : ∀ s b, l ≠ posBool s b) : (l.negate).norm = l.negate := by
  cases l with
  | mk atom positive =>
      cases atom with
      | intLe s k => cases positive <;> rfl
      | intNe s k => cases positive <;> rfl
      | boolEq s b =>
          cases positive with
          | true =>
              exact absurd rfl (hnot s b)
          | false =>
              exfalso
              have hb : (false : Bool) = true := congrArg Literal.positive hnorm
              cases hb

/-! ## B2 — the justified enqueue and typed filtering

The certificate's content is used here to discharge the obligations of the
ACTUAL restoration/enqueue shape. The shape is
`BranchState.restoreAssert`: the checkpoint's frame and trail, the target
level, the current global database, and EXACTLY ONE appended entry whose
literal is the (normalized) asserting literal and whose reason is the
learned clause. `BackjumpPlan.execute` is this shape with the plan's own
fields, so the bridge theorems apply to it by `rfl` and C2 does not have
to re-derive anything: the enqueue is JUSTIFIED (the reason is entailed,
the pivot is a member, the side literals have earlier falsifiers), not
merely asserted. -/

/-- The restored (pre-assertion) branch state of a backjump: the
checkpoint's frame and trail, the target level, and the CURRENT global
database (learned clauses are global and survive the jump). -/
def BranchState.restoreFrame (bs : BranchState leaf) (f : BranchFrame)
    (cpTrail : List TrailEntry) (target : Nat) : BranchState leaf :=
  { frame := f, trail := cpTrail, level := target, learned := bs.learned }

/-- The restore-then-assert state: `restoreFrame` followed by the single
justified entry. This is `BackjumpPlan.execute`'s shape. -/
def BranchState.restoreAssert (bs : BranchState leaf) (f : BranchFrame)
    (cpTrail : List TrailEntry) (target : Nat) (l : Literal) (c : Clause) :
    BranchState leaf :=
  (bs.restoreFrame f cpTrail target).recordImplied l { clause := c }

@[simp] theorem BranchState.restoreAssert_trail (bs : BranchState leaf)
    (f : BranchFrame) (cpTrail : List TrailEntry) (target : Nat)
    (l : Literal) (c : Clause) :
    (bs.restoreAssert f cpTrail target l c).trail
      = cpTrail ++ [{ literal := l.norm, level := target,
                      reason := some { clause := c } }] := rfl

@[simp] theorem BranchState.restoreAssert_frame (bs : BranchState leaf)
    (f : BranchFrame) (cpTrail : List TrailEntry) (target : Nat)
    (l : Literal) (c : Clause) :
    (bs.restoreAssert f cpTrail target l c).frame = f := rfl

@[simp] theorem BranchState.restoreAssert_level (bs : BranchState leaf)
    (f : BranchFrame) (cpTrail : List TrailEntry) (target : Nat)
    (l : Literal) (c : Clause) :
    (bs.restoreAssert f cpTrail target l c).level = target := rfl

@[simp] theorem BranchState.restoreAssert_learned (bs : BranchState leaf)
    (f : BranchFrame) (cpTrail : List TrailEntry) (target : Nat)
    (l : Literal) (c : Clause) :
    (bs.restoreAssert f cpTrail target l c).learned = bs.learned := rfl

/-- ENQUEUE WELL-FORMEDNESS BRIDGE: the restored-and-asserted state is well
formed whenever the restored PRE-state is, the asserting literal is a
member of the learned clause, and the non-asserting learned literals have
exact falsifiers on the restored trail. The reason clause's entailment is
the CERTIFICATE's, not a caller premise (C2's `execute_wellFormed`
`hent`/`hpivot`/`hchron` premises are therefore discharged from the
certificate plus the two named residuals). -/
theorem restoreAssert_wellFormed_of_certificate {leaf : Assignment → Bool}
    {bs : BranchState leaf} {an : ConflictAnalysis} {f : BranchFrame}
    {cpTrail : List TrailEntry} {target : Nat}
    (hpre : (bs.restoreFrame f cpTrail target).WellFormed)
    (hcert : RestorationCertificate leaf bs an)
    (hmem : (an.asserting.norm ∈ an.learned) = True)
    (hchron : ∀ q ∈ an.learned, q ≠ an.asserting.norm →
      ∃ e' ∈ cpTrail, e'.literal = q.negate) :
    (bs.restoreAssert f cpTrail target an.asserting an.learned).WellFormed :=
  BranchState.recordImplied_wellFormed hpre hcert.learnedEntailed hmem hchron

/-- CHRONOLOGY BRIDGE (J1 ROUND 2: RESTATED to the honest
`NegStableAvoiding` family): the enqueue's chronology obligation follows
from the certificate's `othersBelow` conjunct whenever (i) the surviving
falsifiers are checkpoint entries (`hsurv` — C2's
`Identifies`/restoration property) and (ii) the NON-ASSERTING learned
literals are negation-stable. No per-deduction entailment is asked of the
caller. The former `NegStable an.learned` hypothesis is REFUTED as a
whole-clause statement (`negStable_posBool_refuted`,
Proofs/HdeadCkpt.lean) and was never needed: this lemma applies the guard
at `q` only after deriving `q ≠ an.asserting` — the very hypothesis its
conclusion carries. The legacy whole-clause entry point is retained as
`restore_chronology_of_NegStable` below (thin wrapper, for callers that
still hold the strong form). -/
theorem restore_chronology_of_certificate_avoiding {leaf : Assignment → Bool}
    {bs : BranchState leaf} {an : ConflictAnalysis} {cpTrail : List TrailEntry}
    (hcert : RestorationCertificate leaf bs an)
    (hstable : an.asserting.norm = an.asserting)
    (hsurv : ∀ e ∈ bs.trail, e.level ≤ an.backjumpLevel → e ∈ cpTrail)
    (hneg : NegStableAvoiding an.asserting an.learned) :
    ∀ q ∈ an.learned, q ≠ an.asserting.norm →
      ∃ e' ∈ cpTrail, e'.literal = q.negate := by
  intro q hq hne
  have hne' : q ≠ an.asserting := by
    intro hc
    exact hne (by rw [hc, hstable])
  obtain ⟨⟨e, he, hlev, hlit⟩, -⟩ := hcert.othersBelow q hq hne'
  exact ⟨e, hsurv e he hlev, hlit.trans (hneg q hq hne')⟩

/-- COMPATIBILITY WRAPPER (legacy signature): the refuted whole-clause
`NegStable` form still yields the restated conclusion. Retained solely so
the out-of-scope caller `BackjumpPlan.execute_wellFormed_of_certificate`
(Proofs/ConflictResolution.lean) keeps compiling; new sites must use
`restore_chronology_of_certificate_avoiding`. -/
theorem restore_chronology_of_NegStable {leaf : Assignment → Bool}
    {bs : BranchState leaf} {an : ConflictAnalysis} {cpTrail : List TrailEntry}
    (hcert : RestorationCertificate leaf bs an)
    (hstable : an.asserting.norm = an.asserting)
    (hsurv : ∀ e ∈ bs.trail, e.level ≤ an.backjumpLevel → e ∈ cpTrail)
    (hneg : NegStable an.learned) :
    ∀ q ∈ an.learned, q ≠ an.asserting.norm →
      ∃ e' ∈ cpTrail, e'.literal = q.negate :=
  restore_chronology_of_certificate_avoiding hcert hstable hsurv
    hneg.avoiding

/-- CHRONOLOGY BRIDGE — RESTATED NAME (J1): alias of
`restore_chronology_of_certificate_avoiding` under the historical name.
The signature is the honest one; the legacy `NegStable`-typed entry point
is `restore_chronology_of_NegStable`. -/
theorem restore_chronology_of_certificate {leaf : Assignment → Bool}
    {bs : BranchState leaf} {an : ConflictAnalysis} {cpTrail : List TrailEntry}
    (hcert : RestorationCertificate leaf bs an)
    (hstable : an.asserting.norm = an.asserting)
    (hsurv : ∀ e ∈ bs.trail, e.level ≤ an.backjumpLevel → e ∈ cpTrail)
    (hneg : NegStableAvoiding an.asserting an.learned) :
    ∀ q ∈ an.learned, q ≠ an.asserting.norm →
      ∃ e' ∈ cpTrail, e'.literal = q.negate :=
  restore_chronology_of_certificate_avoiding hcert hstable hsurv hneg

/-! ## Restoration by level: skipping entries preserves reason availability

`BackjumpPlan.execute` restores the checkpoint's trail and appends the
asserting entry; `BranchState.restoreLevel` restores by filtering the
current trail at the target level. This section proves the fact the
filtered shape needs: SKIPPING the above-target entries keeps every
surviving entry's reason resolvable — each non-pivot reason literal
still has an exact falsifier among the RESTORED entries. The
`WellFormed` chronology invariant supplies an earlier falsifier, and
level-sortedness (`ReachableState.sorted`) places every earlier entry at
a level no higher than its consumer's, hence inside the filter. -/

/-- The trail restored at a target level: exactly the entries at or below
the target (`BranchState.restoreLevel`'s filter). -/
def BranchState.restoredTrail (bs : BranchState leaf) (target : Nat) :
    List TrailEntry :=
  bs.trail.filter fun e => e.level ≤ target

@[simp] theorem BranchState.restoredTrail_def (bs : BranchState leaf)
    (target : Nat) :
    bs.restoredTrail target = bs.trail.filter (fun e => e.level ≤ target) := rfl

/-- A strictly earlier entry never sits at a higher level on a
level-sorted trail: the ordering fact that puts every surviving falsifier
inside the restored prefix. -/
theorem earlierThan_level_le {trail : List TrailEntry}
    (hs : TrailLevelSorted trail) {e' e : TrailEntry}
    (h : TrailEntry.earlierThan trail e' e) : e'.level ≤ e.level := by
  obtain ⟨i, j, hi, hj, hie, hje, hij⟩ := h
  have hpair := (List.pairwise_iff_getElem.mp hs) i j hi hj hij
  rw [hie, hje] at hpair
  exact hpair

/-- SKIPPING REDUNDANT ENTRIES PRESERVES REASON AVAILABILITY: every entry
that survives the level filter has an exact falsifier on the RESTORED
trail for each non-pivot reason literal. -/
theorem restore_filter_reason_available {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf} (target : Nat)
    (hreach : ReachableState leaf orig bs) :
    ∀ e ∈ bs.restoredTrail target, ∀ r ∈ e.reason, ∀ q ∈ r.clause,
      q ≠ e.literal →
      ∃ e' ∈ bs.restoredTrail target, e'.literal = q.negate := by
  intro e he r hr q hq hne
  obtain ⟨hemem, hlev⟩ := List.mem_filter.mp he
  have hlev' : e.level ≤ target := of_decide_eq_true hlev
  obtain ⟨e', he', heq, hlt⟩ := hreach.wf.2.2.2.1 e hemem r hr q hq hne
  refine ⟨e', List.mem_filter.mpr ⟨he', decide_eq_true ?_⟩, heq⟩
  exact Nat.le_trans (earlierThan_level_le hreach.sorted hlt) hlev'

/-- The restored trail is duplicate-safe (A1's discipline survives the
filter). -/
theorem restore_filter_distinct {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf} (target : Nat)
    (hreach : ReachableState leaf orig bs) :
    TrailLiteralsDistinct (bs.restoredTrail target) :=
  TrailLiteralsDistinct.filter _ hreach.distinct

/-- THE JUSTIFIED ENQUEUE KEEPS THE TRAIL DISCIPLINE: restoring by level
and appending the normalized asserting entry is duplicate-safe, via A1's
`TrailLiteralsDistinct.enqueue` — given exactly the two local premises
the enqueue site owns (entries are stored normalized; the absence check
`hfresh`, the branching-pin policy A1's `decide_duplicates` shows to be
necessary). The absence check is NOT derivable from the certificate,
whose `assertingSurvives` speaks about the asserting literal's
NEGATION. -/
theorem restore_filter_enqueue_distinct {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf} {an : ConflictAnalysis}
    (hreach : ReachableState leaf orig bs)
    (hfresh : ∀ e ∈ bs.restoredTrail an.backjumpLevel,
      e.literal ≠ an.asserting.norm) :
    TrailLiteralsDistinct
      (bs.restoredTrail an.backjumpLevel ++
        [{ literal := an.asserting.norm, level := an.backjumpLevel,
           reason := some { clause := an.learned } }]) := by
  refine TrailLiteralsDistinct.enqueue
    (TrailLiteralsDistinct.filter _ hreach.distinct) ?_ hfresh
  intro e he
  exact hreach.wf.2.1 e (List.mem_filter.mp he).1

/-- RESTORATION CHRONOLOGY AT THE FILTERED TRAIL (the certificate form,
J1 ROUND 2: RESTATED to `NegStableAvoiding`): every non-asserting learned
literal has its exact falsifier on the restored trail — feeding
`restoreAssert_wellFormed_of_certificate`'s `hchron` premise from the
certificate plus the two trail disciplines. This variant needs NO `hsurv`
premise: the filter keeps EVERY entry at level at or below the target,
which is exactly `othersBelow`'s level bound. -/
theorem restore_filter_chronology_of_certificate_avoiding
    {leaf : Assignment → Bool}
    {bs : BranchState leaf} {an : ConflictAnalysis}
    (hcert : RestorationCertificate leaf bs an)
    (hstable : an.asserting.norm = an.asserting)
    (hneg : NegStableAvoiding an.asserting an.learned) :
    ∀ q ∈ an.learned, q ≠ an.asserting.norm →
      ∃ e' ∈ bs.restoredTrail an.backjumpLevel, e'.literal = q.negate := by
  intro q hq hne
  have hne' : q ≠ an.asserting := by
    intro hc
    exact hne (by rw [hc, hstable])
  obtain ⟨⟨e, he, hlev, hlit⟩, -⟩ := hcert.othersBelow q hq hne'
  exact ⟨e, List.mem_filter.mpr ⟨he, decide_eq_true hlev⟩,
    hlit.trans (hneg q hq hne')⟩

/-- COMPATIBILITY WRAPPER (legacy signature) for
`restore_filter_chronology_of_certificate_avoiding`; no in-tree caller of
the whole-clause form remains, it is retained for interface stability
only. -/
theorem restore_filter_chronology_of_NegStable {leaf : Assignment → Bool}
    {bs : BranchState leaf} {an : ConflictAnalysis}
    (hcert : RestorationCertificate leaf bs an)
    (hstable : an.asserting.norm = an.asserting)
    (hneg : NegStable an.learned) :
    ∀ q ∈ an.learned, q ≠ an.asserting.norm →
      ∃ e' ∈ bs.restoredTrail an.backjumpLevel, e'.literal = q.negate :=
  restore_filter_chronology_of_certificate_avoiding hcert hstable hneg.avoiding

/-- RESTATED NAME (J1): alias of
`restore_filter_chronology_of_certificate_avoiding` under the historical
name. -/
theorem restore_filter_chronology_of_certificate {leaf : Assignment → Bool}
    {bs : BranchState leaf} {an : ConflictAnalysis}
    (hcert : RestorationCertificate leaf bs an)
    (hstable : an.asserting.norm = an.asserting)
    (hneg : NegStableAvoiding an.asserting an.learned) :
    ∀ q ∈ an.learned, q ≠ an.asserting.norm →
      ∃ e' ∈ bs.restoredTrail an.backjumpLevel, e'.literal = q.negate :=
  restore_filter_chronology_of_certificate_avoiding hcert hstable hneg

/-- THE SEMANTIC PIVOT FACT: the entry's literal (the asserting literal's
normal form) evaluates exactly like a member of the learned clause. This
is the strongest pivot statement the raw record supports, and it is what
the reason discipline is used for semantically (the normalized record
additionally gets structural membership). -/
theorem RestorationCertificate.asserting_norm_eval_mem
    {leaf : Assignment → Bool} {bs : BranchState leaf} {an : ConflictAnalysis}
    (h : RestorationCertificate leaf bs an) :
    ∃ q ∈ an.learned, ∀ a, (an.asserting.norm).eval a = q.eval a :=
  ⟨an.asserting, h.assertingMem, fun a => Literal.norm_eval an.asserting a⟩

/-- TYPED FILTERING, REJECTION CASE: if narrowing the restored frame by the
asserting literal fails, then NO leaf solution satisfying the surviving
trail is covered by the restored frame — the unit property makes every
such solution satisfy the assertion, while a failing filter refuses every
covered assignment. This is the soundness of C1's `restoreNarrow = none` →
local-exclusion path. -/
theorem filterFrame_none_excludes {l : Literal} {f : BranchFrame}
    {a : Assignment} (hnone : filterFrame l f = none)
    (hcov : FrameCovers f a) : l.eval a ≠ some true := by
  intro hev
  obtain ⟨g, hg, -⟩ := filterFrame_preserves hcov hev
  rw [hnone] at hg
  cases hg

/-- TYPED FILTERING, REJECTION CASE (certificate form). -/
theorem restoreAssert_filterFrame_none_excludes {leaf : Assignment → Bool}
    {bs : BranchState leaf} {an : ConflictAnalysis} {f : BranchFrame}
    (hcert : RestorationCertificate leaf bs an)
    (hnone : filterFrame an.asserting f = none) :
    ∀ a, leaf a = true →
      (∀ e ∈ bs.trail, e.level ≤ an.backjumpLevel → e.literal.eval a = some true) →
      FrameCovers f a → False := by
  intro a hleaf htrail hcov
  exact filterFrame_none_excludes hnone hcov
    (hcert.unitAfterRestore a hleaf htrail)

/-- TYPED FILTERING, ACCEPTANCE CASE: a leaf solution that survives
restoration (satisfies the checkpoint frame and the surviving trail) is
still covered after the assertion narrows the frame. The literal's truth
is the certificate's unit property and the coverage transfer is
`filterFrame_preserves` — the assertion is a NARROWING, never a loss. -/
theorem restoreAssert_filterFrame_covers {leaf : Assignment → Bool}
    {bs : BranchState leaf} {an : ConflictAnalysis} {f g : BranchFrame}
    (hcert : RestorationCertificate leaf bs an)
    (hfilter : filterFrame an.asserting f = some g) :
    ∀ a, leaf a = true →
      (∀ e ∈ bs.trail, e.level ≤ an.backjumpLevel → e.literal.eval a = some true) →
      FrameCovers f a → FrameCovers g a := by
  intro a hleaf htrail hcov
  obtain ⟨g', hg', hcov'⟩ :=
    filterFrame_preserves hcov (hcert.unitAfterRestore a hleaf htrail)
  rw [hfilter] at hg'
  cases hg'
  exact hcov'

/-- RESTORATION FORWARD (representational form): the restore-then-assert
state represents every assignment covered by the restored frame that
satisfies the restored trail, the retained global database and the
asserting literal. No still-possible solution is lost by the jump. -/
theorem restoreAssert_represents {leaf : Assignment → Bool}
    {bs : BranchState leaf} {f : BranchFrame} {cpTrail : List TrailEntry}
    {target : Nat} {l : Literal} {c : Clause} {a : Assignment}
    (hframe : FrameCovers f a)
    (htrail : ∀ e ∈ cpTrail, e.literal.eval a = some true)
    (hlearn : ∀ cl ∈ bs.learned, cl.SatisfiedBy a)
    (hassert : l.norm.eval a = some true) :
    (bs.restoreAssert f cpTrail target l c).Represents a :=
  BranchState.recordImplied_preserves ⟨hframe, htrail, hlearn⟩ hassert

/-- THE ASSERTION IS JUSTIFIED, NOT ASSERTED: every leaf solution that
survives restoration (checkpoint frame + surviving trail + retained
database) satisfies the asserting literal — the certificate's unit
property, whose hypothesis is fed by `hsurv` (each restored entry is a
surviving original entry) — and is therefore represented by the
restored-and-asserted state. -/
theorem restoreAssert_represents_of_certificate {leaf : Assignment → Bool}
    {bs : BranchState leaf} {an : ConflictAnalysis} {f : BranchFrame}
    {cpTrail : List TrailEntry} {target : Nat} {a : Assignment}
    (hcert : RestorationCertificate leaf bs an)
    (hsurv : ∀ e ∈ bs.trail, e.level ≤ an.backjumpLevel → e ∈ cpTrail)
    (htrail : ∀ e ∈ cpTrail, e.literal.eval a = some true)
    (hlearn : ∀ cl ∈ bs.learned, cl.SatisfiedBy a)
    (hframe : FrameCovers f a)
    (hleaf : leaf a = true) :
    (bs.restoreAssert f cpTrail target an.asserting an.learned).Represents a := by
  have hsurvTrail : ∀ e ∈ bs.trail, e.level ≤ an.backjumpLevel →
      e.literal.eval a = some true :=
    fun e he hlev => htrail e (hsurv e he hlev)
  refine restoreAssert_represents hframe htrail hlearn ?_
  rw [Literal.norm_eval]
  exact hcert.unitAfterRestore a hleaf hsurvTrail

/-! ## B1 — the pivot frontier

The pivot-round bound needs one analytic fact: when the analyzer resolves a
pivot against its reason, every literal it marks lies AT OR BEFORE the
pivot on the trail, so the pivot position cannot advance and the number of
rounds is bounded by the trail length.

`findEntryOf`-based marking makes this provable from distinctness alone: the
lookup returns the LAST falsifier, so if chronology puts a falsifier before
the pivot then the lookup cannot return one after it, and distinctness
identifies the returned entry with the chronology witness. -/

/-- B1 FRONTIER STEP: the falsifier the lookup returns for a reason literal
other than the pivot is never AFTER the pivot, provided every reason literal
has an earlier normalized falsifier. -/
theorem findEntryOf_not_after_pivot {trail : List TrailEntry} {r : Clause}
    {piv : TrailEntry} {q : Literal} {e₂ : TrailEntry}
    (hdist : TrailLiteralsDistinct trail)
    (hnorm : ∀ e' ∈ trail, e'.literal = e'.literal.norm)
    (hchron : ∀ l ∈ r, l ≠ piv.literal.norm → ∃ e' ∈ trail,
      e'.literal = (l.negate).norm ∧ ¬ TrailEntry.earlierThan trail piv e')
    (hqr : q ∈ r) (hne : q ≠ piv.literal.norm)
    (h : findEntryOf trail q.negate = some e₂) :
    ¬ TrailEntry.earlierThan trail piv e₂ := by
  obtain ⟨e', he', hlit', hnot⟩ := hchron q hqr hne
  have he₂mem : e₂ ∈ trail := findEntryOf_mem trail _ e₂ h
  have he₂lit : e₂.literal = (q.negate).norm := findEntryOf_literal trail _ e₂ h
  have heq : e₂ = e' := hdist.1 e' he' e₂ he₂mem
    (he₂lit.trans (hlit'.symm.trans (hnorm e' he')))
  rw [heq]
  exact hnot

/-- B1 CONDITION (`PivotFrontier`): the named property that closes the round
bound. It is the frontier step for BOTH marking paths, plus distinctness.

The version proved above covers the exact-match path (`findEntryOf` succeeds
on the scanned literal). The remaining path is `orderUpgrade`, where the
analyzer replaces the scanned literal by a WEAKER bound read off the trail;
its falsifier is the trail entry that established that bound, and nothing in
`WellFormed`'s chronology orders it against the pivot. Closing B1 therefore
needs either this condition maintained as a driver invariant, or an analyzer
change that materializes the upgrade's bound entry before citing it — the
plan's own "if a needed falsifier is a derived bound, materialize its
justified trail entry before using it in a later reason". -/
def PivotFrontier (trail : List TrailEntry) (lvl : Nat) : Prop :=
  TrailLiteralsDistinct trail ∧
  ∀ (e : TrailEntry) (r : Reason), e ∈ trail → e.reason = some r →
    e.level = lvl →
      ∀ q ∈ r.clause, q ≠ e.literal.norm →
        ∀ e₂ ∈ trail, e₂.literal = (q.negate).norm →
          ¬ TrailEntry.earlierThan trail e e₂

/-- `PivotFrontier` makes the pivot strictly non-advancing: the rounds of the
analyzer are bounded by `trail.length`. This is the accounting B1 asks for —
"each trail entry is marked at most once" — now proved from the named
condition rather than assumed. -/
theorem pivotFrontier_no_advance {trail : List TrailEntry} {lvl : Nat}
    (hf : PivotFrontier trail lvl) {e e₂ : TrailEntry} {r : Reason}
    (he : e ∈ trail) (hr : e.reason = some r) (hlev : e.level = lvl)
    {q : Literal} (hq : q ∈ r.clause) (hne : q ≠ e.literal.norm)
    (he₂ : e₂ ∈ trail) (hlit : e₂.literal = (q.negate).norm) :
    ¬ TrailEntry.earlierThan trail e e₂ :=
  hf.2 e r he hr hlev q hq hne e₂ he₂ hlit

/-! ## B1 — the reason-scan frontier, completed

The remaining half of the frontier argument: on a REASON clause the exact
lookup always succeeds (chronology supplies an exact falsifier, and trail
literals are stored normalized), so the `orderUpgrade` path is never taken
there. Composed with `findEntryOf_not_after_pivot` this gives the frontier
step in the form the round accounting consumes.

The only place the upgrade path CAN fire is the initial conflict-clause
scan, which runs with `marks = []` — before any pivot exists — so it cannot
advance the frontier. -/

/-- A trail entry with the normalized target's literal makes `findEntryOf`
succeed. -/
theorem findEntryOf_isSome {trail : List TrailEntry} {l : Literal}
    {e : TrailEntry} (hmem : e ∈ trail) (hlit : e.literal = l.norm) :
    ∃ e₂, findEntryOf trail l = some e₂ := by
  cases hf : findEntryOf trail l with
  | none =>
      exfalso
      unfold findEntryOf at hf
      rw [List.find?_eq_none] at hf
      exact hf e (List.mem_reverse.mpr hmem)
        (by simp only [litEqB, decide_eq_true_eq]; exact hlit)
  | some e₂ => exact ⟨e₂, rfl⟩

/-- `earlierThan` is irreflexive on a trail whose ENTRIES are distinct. -/
theorem earlierThan_irrefl {trail : List TrailEntry} (hnd : List.Nodup trail)
    {e : TrailEntry} : ¬ TrailEntry.earlierThan trail e e := by
  intro h
  obtain ⟨i, j, hi, hj, hie, hje, hij⟩ := h
  have hsame : trail[i] = trail[j] := by rw [hie, hje]
  have : i = j := (List.getElem_inj (h₀ := hi) (h₁ := hj) hnd).mp hsame
  omega

/-- `earlierThan` is asymmetric on a trail whose entries are distinct. -/
theorem earlierThan_asymm {trail : List TrailEntry} (hnd : List.Nodup trail)
    {a b : TrailEntry} :
    ¬ (TrailEntry.earlierThan trail a b ∧ TrailEntry.earlierThan trail b a) := by
  rintro ⟨⟨i, j, hi, hj, hia, hjb, hij⟩, ⟨k, l, hk, hl, hkb, hla, hkl⟩⟩
  have hjk : j = k := (List.getElem_inj (h₀ := hj) (h₁ := hk) hnd).mp (by rw [hjb, hkb])
  have hil : i = l := (List.getElem_inj (h₀ := hi) (h₁ := hl) hnd).mp (by rw [hia, hla])
  omega

/-- ANTI-RE-MARKING: a reason clause never contains the negation of its own
pivot (in normalized form). Chronology puts a falsifier of every other reason
literal strictly before the pivot; if that literal were the pivot's negation,
distinctness would identify the falsifier with the pivot itself, contradicting
irreflexivity. This is exactly what stops `markLit` from re-marking a
consumed pivot, so the marks can never grow back into already-resolved
entries. -/
theorem reason_not_negate_pivot {trail : List TrailEntry} {piv : TrailEntry}
    {r : Reason}
    (hdist : TrailLiteralsDistinct trail)
    (hnorm : ∀ e ∈ trail, e.literal = e.literal.norm)
    (hpiv : piv ∈ trail)
    (hchron : ∀ a ∈ r.clause, a ≠ piv.literal →
      ∃ e' ∈ trail, e'.literal = a.negate ∧ TrailEntry.earlierThan trail e' piv)
    {a : Literal} (ha : a ∈ r.clause) (hne : a ≠ piv.literal) :
    a.negate.norm ≠ piv.literal.norm := by
  intro hcontra
  obtain ⟨e', he'mem, he'lit, hbefore⟩ := hchron a ha hne
  have hchain : e'.literal = piv.literal.norm :=
    (hnorm e' he'mem).trans ((congrArg Literal.norm he'lit).trans hcontra)
  have heq : e' = piv := hdist.1 piv hpiv e' he'mem hchain
  rw [heq] at hbefore
  exact earlierThan_irrefl hdist.2 hbefore

/-- THE FRONTIER STEP FOR REASON SCANS: for a non-skipped literal of a pivot's
reason clause, the falsifier the analyzer's lookup returns is never after the
pivot — and the lookup cannot fail, so this is the only path taken. -/
theorem reason_falsifier_not_after_pivot {trail : List TrailEntry}
    {piv : TrailEntry} {r : Reason} {l : Literal}
    (hdist : TrailLiteralsDistinct trail)
    (hnorm : ∀ e ∈ trail, e.literal = e.literal.norm)
    (hpiv : piv ∈ trail)
    (hchron : ∀ a ∈ r.clause, a ≠ piv.literal →
      ∃ e' ∈ trail, e'.literal = a.negate ∧ TrailEntry.earlierThan trail e' piv)
    (hl : l ∈ r.clause) (hne : l.norm ≠ piv.literal)
    {e₂ : TrailEntry} (h : findEntryOf trail l.norm.negate = some e₂) :
    ¬ TrailEntry.earlierThan trail piv e₂ := by
  -- the exact lookup succeeds, so the upgrade path is not consulted
  have hlne : l ≠ piv.literal := fun hh => hne (by rw [hh]; exact (hnorm piv hpiv).symm)
  obtain ⟨e', he'mem, he'lit, hbefore⟩ := hchron l hl hlne
  have heq : e₂ = e' := hdist.1 e' he'mem e₂ (findEntryOf_mem trail _ e₂ h)
    ((findEntryOf_literal trail _ e₂ h).trans
      ((norm_negate_norm_local l).trans (congrArg Literal.norm he'lit).symm))
  rw [heq]
  exact fun hh => earlierThan_asymm hdist.2 ⟨hh, hbefore⟩

/-! ## B1 — the fuel accounting

The two things the analyzer's transitions consume are exactly the two things
`analysisAllowance` charges for: one unit per worklist literal EVER held (the
conflict clause plus every reason clause reached — and the frontier above
shows each trail entry reseeds at most one reason), and one unit per pivot
round (bounded by the trail length). The bound is therefore

  `reasonBudget trail c + trail.length`,

and this section proves that the executable fuel covers it. -/

/-- The analyzer's transition budget: every worklist literal ever held plus
one unit per pivot round. -/
def transitionBudget (trail : List TrailEntry) (c : Clause) : Nat :=
  reasonBudget trail c + trail.length

/-- The computed allowance covers the transition budget. This is the
arithmetic that makes the formula `(budget + 1) * (len + 1) + 1` the right
shape: it is exactly the lexicographic bound `rounds x (worklist + 1)`. -/
theorem transitionBudget_le_analysisAllowance (trail : List TrailEntry)
    (c : Clause) : transitionBudget trail c ≤ analysisAllowance trail c := by
  rw [transitionBudget, analysisAllowance, Nat.mul_succ]
  have hmul : trail.length ≤ (reasonBudget trail c + 1) * trail.length := by
    have h : 1 * trail.length ≤ (reasonBudget trail c + 1) * trail.length :=
      Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.zero_le _))
    simpa using h
  omega

/-- The EXECUTABLE fuel (`analysisFuel`, the allowance actually passed to
`analyzeStep`) covers the transition budget. -/
theorem transitionBudget_le_analysisFuel (trail : List TrailEntry) (c : Clause) :
    transitionBudget trail c ≤ analysisFuel trail c :=
  Nat.le_trans (transitionBudget_le_analysisAllowance trail c)
    (analysisAllowance_le_analysisFuel trail c)

/-! ## B1 status

The analytic content is proved:

* every reason-scan mark lies AT OR BEFORE the pivot
  (`reason_falsifier_not_after_pivot`), so the pivot position cannot advance
  within a round;
* a consumed pivot can never be re-marked
  (`reason_not_negate_pivot`), so the marks cannot grow back into resolved
  entries;
* the transition budget is covered by the executable fuel
  (`transitionBudget_le_analysisFuel`).

What remains is the loop-level induction that threads the frontier through
`analyzeStep` and concludes `analyzeStep ... (analysisFuel trail c) [c] none
[] []` does not run out of fuel. The invariant it needs is stated below, so
the remaining work is a single preservation induction rather than a design
question. -/

/-- B1 LOOP INVARIANT: the marks all lie strictly before the current pivot
frontier, and every clause still in the worklist is a suffix of the reason
clause of the pivot that seeded it (so the exact lookup is the only path
taken on it). `analyzeStep` preserves this, and the frontier strictly
decreases at every pivot round — which is why the rounds are bounded by the
trail length and why `transitionBudget` pays for every transition. -/
def FrontierInvariant (trail : List TrailEntry) (lvl : Nat)
    (cs : List Clause) (marks : List TrailEntry) : Prop :=
  (∀ m ∈ marks, m ∈ trail) ∧
  (∀ m ∈ marks, m.level = lvl) ∧
  (∀ m ∈ marks, ∀ fron ∈ trail, ¬ TrailEntry.earlierThan trail fron m) ∧
  (∀ c ∈ cs, ∃ e ∈ trail, ∃ r ∈ e.reason, c <:+ r.clause) ∧
  List.Nodup trail

end LeanFzn.Solver.Propagation

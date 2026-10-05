/-
File: solver/LCG/Proofs/Analyze.lean

Purpose:
  L0.4 conflict-analysis correctness, level half: every (literal,
  level) pair recorded by the 1-UIP analysis comes from a trail entry at
  that level (`analyzeTrail_belowFromTrail` via `markLit_preserves` and
  `analyzeStep_preserves`), which bounds the computed `backjumpLevel` by
  the state's decision level under structural well-formedness
  (`analyzeConflict_level`).

Dependencies:
  - solver.LCG.TrailEval (through Operations): the executable 1-UIP
    analysis (`analyzeTrail`, `analyzeStep`, `markLit`).
  - solver.LCG.Operations: `analyzeConflict` over the state.
  - solver.LCG.Invariants: `State.WellFormed` (trail-level bound).

DAG:
  TrailEval + Operations + Invariants -> Proofs/Analyze
  -> LCG.Proofs.Transitions (analyzeConflict_correct, level conjunct)
-/

import solver.LCG.Operations
import solver.LCG.Invariants
import solver.LCG.Encoding

namespace LeanFzn.Solver.LCG

open LeanFzn LeanFzn.Solver.Core

/-! ## Trail membership of found entries -/

/-- An entry located by `findEntryOf` is a trail entry. -/
theorem findEntry_mem (trail : List TrailEntry) (l : Literal)
    (e : TrailEntry) (h : findEntryOf trail l = some e) :
    e ∈ trail := by
  unfold findEntryOf at h
  obtain ⟨_, as, bs, hrw, _⟩ := List.find?_eq_some_iff_append
    (xs := trail.reverse)
    (p := fun (x : TrailEntry) => litEqB x.literal l.norm) |>.mp h
  have hmem : e ∈ trail.reverse := by
    rw [hrw, List.mem_append]
    exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
  exact List.mem_reverse.mp hmem

/-! ## The below-level invariant -/

/-- Every recorded below-level pair comes from a trail entry at the
    recorded level. -/
def BelowFromTrail (trail : List TrailEntry)
    (learnt : List (Literal × Nat)) : Prop :=
  ∀ p ∈ learnt, ∃ e ∈ trail, p.2 = e.level

/-- `markLit` preserves the below-level invariant. -/
theorem markLit_preserves (trail : List TrailEntry) (lvl : Nat)
    (marks : List TrailEntry) (learnt : List (Literal × Nat))
    (q0 : Literal) (hinv : BelowFromTrail trail learnt)
    (marks' : List TrailEntry) (learnt' : List (Literal × Nat))
    (h : markLit trail lvl marks learnt q0 = some (marks', learnt')) :
    BelowFromTrail trail learnt' := by
  unfold markLit at h
  by_cases hA : (marks.any fun m => litEqB m.literal q0.norm.negate.norm)
  · rw [if_pos hA] at h
    cases h; exact hinv
  by_cases hB : (learnt.any fun p => litEqB p.1 q0.norm)
  · rw [if_neg hA, if_pos hB] at h
    cases h; exact hinv
  rw [if_neg hA, if_neg hB] at h
  cases hfind : findEntryOf trail q0.norm.negate with
  | none =>
    rw [hfind] at h
    simp only [] at h
    cases hup : findEntryOf trail (orderUpgrade trail q0.norm).negate with
    | none =>
      rw [hup] at h
      simp at h
    | some e =>
      rw [hup] at h
      simp only [] at h
      by_cases h0 : e.level == 0
      · rw [if_pos h0] at h; cases h; exact hinv
      by_cases hl : e.level == lvl
      · rw [if_neg h0, if_pos hl] at h; cases h; exact hinv
      rw [if_neg h0, if_neg hl] at h
      cases h
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨e, findEntry_mem trail (orderUpgrade trail q0.norm).negate e
          hup, rfl⟩
      · exact hinv p hp
  | some e =>
    rw [hfind] at h
    simp only [] at h
    rw [hfind] at h
    simp only [] at h
    by_cases h0 : e.level == 0
    · rw [if_pos h0] at h; cases h; exact hinv
    by_cases hl : e.level == lvl
    · rw [if_neg h0, if_pos hl] at h; cases h; exact hinv
    rw [if_neg h0, if_neg hl] at h
    cases h
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨e, findEntry_mem trail q0.norm.negate e hfind, rfl⟩
    · exact hinv p hp

/-- One step of the analysis worklist preserves both below-level
    invariants: membership in the trail (`BelowFromTrail`) and the strict
    level bound. Strictness is discharged for the one pair freshly
    recorded by `markLit` (a recorded level is neither `0` nor the
    analysis level, hence strictly below it); pre-existing pairs inherit
    the caller's hypothesis. -/
theorem analyzeStep_preserves (trail : List TrailEntry) (lvl : Nat)
    (fuel : Nat)
    (hbnd : ∀ e : TrailEntry, e ∈ trail → e.level ≤ lvl) :
    ∀ (cs : List Clause) (skip : Option Literal)
      (marks : List TrailEntry) (learnt : List (Literal × Nat)),
    BelowFromTrail trail learnt →
    (∀ p ∈ learnt, p.2 < lvl) →
    ∀ (below : List (Literal × Nat)) (uip : Literal),
      analyzeStep trail lvl fuel cs skip marks learnt
        = some (below, uip) →
      BelowFromTrail trail below ∧ (∀ p ∈ below, p.2 < lvl) := by
  induction fuel with
  | zero =>
      intro cs skip marks learnt _ _ below uip h
      rw [analyzeStep] at h
      simp at h
  | succ fuel ih =>
    intro cs skip marks learnt hinv hstrict below uip h
    cases cs with
    | nil =>
      rw [analyzeStep] at h
      cases hpivot : nextPivot trail marks with
      | none =>
        rw [hpivot] at h
        simp at h
      | some e =>
        rw [hpivot] at h
        simp only [] at h
        by_cases hempty : (marks.filter fun m =>
            !litEqB m.literal e.literal).isEmpty
        · rw [if_pos hempty] at h
          cases h
          exact ⟨hinv, hstrict⟩
        · rw [if_neg hempty] at h
          cases hreason : e.reason with
          | none =>
            rw [hreason] at h
            simp at h
          | some r =>
            rw [hreason] at h
            exact ih [r.clause] (some e.literal)
              (marks.filter fun m => !litEqB m.literal e.literal) learnt
              hinv hstrict below uip h
    | cons c cs' =>
      cases c with
      | nil =>
        rw [analyzeStep] at h
        exact ih cs' skip marks learnt hinv hstrict below uip h
      | cons q0 qs =>
        rw [analyzeStep] at h
        by_cases hskip : skipEq skip q0.norm
        · rw [if_pos hskip] at h
          exact ih (qs :: cs') skip marks learnt hinv hstrict below uip h
        · rw [if_neg hskip] at h
          cases hmark : markLit trail lvl marks learnt q0.norm with
          | none =>
            rw [hmark] at h
            simp at h
          | some res =>
            obtain ⟨marks', learnt'⟩ := res
            rw [hmark] at h
            have hpres := markLit_preserves trail lvl marks learnt q0.norm
              hinv marks' learnt' hmark
            -- Strictness of the pair list after this `markLit`: a fresh
            -- pair records `e.level` with `e.level ≠ 0`, `e.level ≠ lvl`;
            -- a pre-existing pair inherits `hstrict`.
            have hstrict' : ∀ p ∈ learnt', p.2 < lvl := by
              intro p hp
              unfold markLit at hmark
              simp only [] at hmark
              by_cases hA : (marks.any fun m =>
                litEqB m.literal q0.norm.norm.negate.norm)
              · rw [if_pos hA] at hmark; cases hmark
                exact hstrict p hp
              by_cases hB : (learnt.any fun pp => litEqB pp.1 q0.norm.norm)
              · rw [if_neg hA, if_pos hB] at hmark; cases hmark
                exact hstrict p hp
              rw [if_neg hA, if_neg hB] at hmark
              cases hfind : findEntryOf trail q0.norm.norm.negate with
              | none =>
                rw [hfind] at hmark
                simp only [] at hmark
                cases hup : findEntryOf trail
                    (orderUpgrade trail q0.norm.norm).negate with
                | none => rw [hup] at hmark; simp at hmark
                | some e =>
                  rw [hup] at hmark
                  simp only [] at hmark
                  by_cases h0 : e.level == 0
                  · rw [if_pos h0] at hmark; cases hmark; exact hstrict p hp
                  by_cases hl : e.level == lvl
                  · rw [if_neg h0, if_pos hl] at hmark; cases hmark
                    exact hstrict p hp
                  rw [if_neg h0, if_neg hl] at hmark
                  cases hmark
                  rcases List.mem_cons.mp hp with rfl | hp
                  · have hb := hbnd e (findEntry_mem trail
                      (orderUpgrade trail q0.norm.norm).negate e hup)
                    simp only [beq_iff_eq] at h0 hl
                    omega
                  · exact hstrict p hp
              | some e =>
                rw [hfind] at hmark
                simp only [] at hmark
                rw [hfind] at hmark
                simp only [] at hmark
                by_cases h0 : e.level == 0
                · rw [if_pos h0] at hmark; cases hmark; exact hstrict p hp
                by_cases hl : e.level == lvl
                · rw [if_neg h0, if_pos hl] at hmark; cases hmark
                  exact hstrict p hp
                rw [if_neg h0, if_neg hl] at hmark
                cases hmark
                rcases List.mem_cons.mp hp with rfl | hp
                · have hb := hbnd e (findEntry_mem trail q0.norm.norm.negate e
                    hfind)
                  simp only [beq_iff_eq] at h0 hl
                  omega
                · exact hstrict p hp
            exact ih (qs :: cs') skip marks' learnt'
              hpres hstrict' below uip h

/-- The below-level pairs produced by a successful trail analysis all
    come from the trail. -/
theorem analyzeTrail_belowFromTrail (trail : List TrailEntry) (lvl : Nat)
    (conflict : Clause) (below : List (Literal × Nat)) (uip : Literal)
    (hbnd : ∀ e : TrailEntry, e ∈ trail → e.level ≤ lvl)
    (h : analyzeTrail trail lvl conflict = some (below, uip)) :
    BelowFromTrail trail below := by
  unfold analyzeTrail at h
  exact (analyzeStep_preserves trail lvl
    (4 * trail.length * trail.length + 256)
    hbnd
    [conflict] none [] []
    (by intro p hp; cases hp) (by intro p hp; cases hp) below uip h).1

/-- The below-level pairs produced by a successful trail analysis all
    carry levels strictly below the analysis level (given trail-level
    boundedness, which `State.WellFormed` supplies at the state level). -/
theorem analyzeTrail_belowStrict (trail : List TrailEntry) (lvl : Nat)
    (conflict : Clause) (below : List (Literal × Nat)) (uip : Literal)
    (hbnd : ∀ e : TrailEntry, e ∈ trail → e.level ≤ lvl)
    (h : analyzeTrail trail lvl conflict = some (below, uip)) :
    ∀ p ∈ below, p.2 < lvl := by
  unfold analyzeTrail at h
  exact (analyzeStep_preserves trail lvl
    (4 * trail.length * trail.length + 256)
    hbnd
    [conflict] none [] []
    (by intro p hp; cases hp) (by intro p hp; cases hp) below uip h).2

/-- Strict fold-max bound: when every recorded level is strictly below
    `lvl`, the fold-max is strictly below `lvl`. -/
theorem below_max_strict (below : List (Literal × Nat)) (lvl : Nat)
    (hall : ∀ p ∈ below, p.2 < lvl) :
    below.foldl (fun acc p => max acc p.2) 0 < lvl + 1 := by
  have hfold : ∀ acc, acc < lvl + 1 →
      below.foldl (fun a p => max a p.2) acc < lvl + 1 := by
    intro acc hacc
    induction below generalizing acc with
    | nil => exact hacc
    | cons p rest ihrest =>
        have hp1 : p.2 < lvl + 1 :=
          Nat.lt_succ_of_lt (hall p (List.mem_cons_self ..))
        have ih' := ihrest (fun q hq => hall q (List.mem_cons_of_mem _ hq))
        simp only [List.foldl_cons]
        exact ih' (max acc p.2) (by omega)
  exact hfold 0 (by omega)

/-- The `backjumpLevel` of a successful conflict analysis is bounded by
    the state's decision level: every recorded below level is a trail
    level, and trail levels never exceed the decision level. -/
theorem analyzeConflict_level {state : State} {analysis : ConflictAnalysis}
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    (hstate : state.WellFormed problem constraintHolds)
    (hanalyze : analyzeConflict state = some analysis) :
    analysis.backjumpLevel ≤ state.decisionLevel := by
  unfold analyzeConflict at hanalyze
  cases hconf : state.conflict with
  | none =>
    rw [hconf] at hanalyze
    simp at hanalyze
  | some conflictClause =>
    rw [hconf] at hanalyze
    simp only [] at hanalyze
    cases hres : analyzeTrail state.trail state.decisionLevel conflictClause with
    | none =>
      rw [hres] at hanalyze
      simp at hanalyze
    | some res =>
      obtain ⟨below, uip⟩ := res
      rw [hres] at hanalyze
      simp only [] at hanalyze
      -- invert `some {record} = some analysis` and read the level field
      have hblevel : analysis.backjumpLevel
          = below.foldl (fun acc p => max acc p.2) 0 := by
        injection hanalyze with hinj
        cases hinj
        rfl
      rw [hblevel]
      obtain ⟨_, hlevels, _⟩ := hstate
      have hbelow : BelowFromTrail state.trail below :=
        analyzeTrail_belowFromTrail state.trail state.decisionLevel
          conflictClause below uip hlevels hres
      have hall : ∀ p ∈ below, p.2 ≤ state.decisionLevel := by
        intro p hp
        obtain ⟨e, hetrail, hlevel⟩ := hbelow p hp
        rw [hlevel]
        exact hlevels e hetrail
      have hfold : ∀ (below : List (Literal × Nat)),
          (∀ p ∈ below, p.2 ≤ state.decisionLevel) →
          ∀ acc, acc ≤ state.decisionLevel →
            below.foldl (fun a p => max a p.2) acc ≤ state.decisionLevel := by
        intro below hallbelow acc hacc
        induction below generalizing acc with
        | nil => exact hacc
        | cons p rest ihrest =>
            have hp : p.2 ≤ state.decisionLevel :=
              hallbelow p (List.mem_cons_self ..)
            have ih' := ihrest (fun q hq =>
              hallbelow q (List.mem_cons_of_mem _ hq))
            simp only [List.foldl_cons] at ih' ⊢
            exact ih' (max acc p.2) (by omega)
      exact hfold below hall 0 (Nat.zero_le _)

/-! ## Entailment of the learned clause

The learned clause `uip.negate :: below.map (·.1)` is entailed by the
internal problem. The heart is the *resolution lemma* below in the
shape the analyzer provides. At the resolution point, the working
clause contains the negation `pivot.negate` of the pivot entry's
literal (`pivot` is the trail entry being resolved against, so its
exact negation appears in every clause that caused it to be marked),
the reason clause contains the pivot itself, and every other reason
literal is falsified by the trail (reason applicability). The classic
semantic resolution rule `(A ∨ p) ∧ (R ∨ ¬p) ⊨ (A ∨ R)` then applies
with the polarity pair `pivot` (reason) / `pivot.negate` (work). We
cast the working clause in the accessing form the analyzer maintains:
it is *falsified by the trail* — every one of its literals is
trail-false — and stays falsified under every assignment agreeing with
the trail. Relative-truth invariant: for every internal solution `a`,
either some working literal is true at `a`, or `a` is trail-consistent
on the mentioned literals. Resolution preserves the invariant; the UIP
step discharges the last current-level literal; below-level literals
are kept as-is. Root-falsified literals drop soundly because `RootFacts`
makes them true in every internal solution.

Formal chain (all proved; no axioms beyond `propext`/`Quot.sound`/
`Classical.choice`):

1. `resolve_step` — one resolution step preserves entailment, with the
   polarity pair stated exactly as above;
2. `dropRootFalsified` — deleting tracker entries whose witnessing
   entry is at level 0 preserves entailment (nonempty covered case);
3. `analyzeStep_entailed` — a fuel-inductive statement of the analyzer:
   whenever the worklist starts from entailed clauses and all trail
   reasons are valid and applicable as recorded, a successful
   `analyzeStep` result satisfies the invariant's conclusion.
-/


/-- One semantic resolution step: with the pivot literal in the reason,
    the pivot's negation in the working clause, both clauses entailed,
    the resolvent — working clause minus `pivot.negate`, plus reason
    minus `pivot` — is entailed. -/
theorem resolve_step
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    (work reason : Clause) (pivot : Literal)
    (hwork : Clause.EntailedBy problem constraintHolds work)
    (hreason : Clause.EntailedBy problem constraintHolds reason) :
    (Clause.EntailedBy problem constraintHolds
      ((work.filter (fun l => !litEqB l pivot.negate))
        ++ (reason.filter (fun l => !litEqB l pivot)))) := by
  intro a ha
  obtain ⟨lw, hlwm, hevw⟩ := hwork a ha
  by_cases hlwp : litEqB lw pivot.negate
  · -- the work witness is the pivot's negation; use the reason's
    -- witness, which cannot also be the pivot: pivot and pivot.negate
    -- cannot both evaluate to true at `a` (`eval_negate` case split).
    obtain ⟨lr, hlrm, hevr⟩ := hreason a ha
    by_cases hlrp : litEqB lr pivot
    · -- `lr = pivot` from exact-match equality
      have hlr_eq : lr = pivot := by
        simp only [litEqB, decide_eq_true_eq] at hlrp
        exact hlrp
      -- the reason's witness is the pivot: pivot true at `a`
      have h1 : pivot.eval a = some true := by
        rw [hlr_eq] at hevr
        exact hevr
      -- the work witness `lw` equals `pivot.negate` (hlwp true)
      have hlw_eq : lw = pivot.negate := by
        simp only [litEqB, decide_eq_true_eq] at hlwp
        exact hlwp
      have h2 : pivot.negate.eval a = some true := by
        rw [hlw_eq] at hevw
        exact hevw
      rw [show pivot.negate.eval a = (pivot.eval a).map (! ·) from
        Literal.eval_negate pivot a] at h2
      rw [h1] at h2
      simp at h2
    · exact ⟨lr, List.mem_append.mpr (Or.inr
        (List.mem_filter.mpr ⟨hlrm, by simpa [litEqB] using hlrp⟩)), hevr⟩
  · exact ⟨lw, List.mem_append.mpr (Or.inl
      (List.mem_filter.mpr ⟨hlwm, by simpa [litEqB] using hlwp⟩)), hevw⟩

/-! ### The resolution lift through the analyzer

The executable loop maintains two resources: a *falsified working
disjunction* (the pending clauses plus the negations of the marked
current-level entries and the learned-so-far literals) and the
*learned-so-far record* (`learnt`). The truth invariant:

    `Clause.EntailedBy problem constraintHolds
       (learnt.map (·.1) ++ marks.map (fun e => e.literal.negate))`

— every internal solution satisfies the learned-so-far record or
contradicts one marked entry's literal (via its exact negation).

That invariant holds initially (empty learnt, marks = []): vacuous? No —
the conflict clause itself is entailed, so the initial worklist seeding
is handled *outside* this invariant: we seed marks from the conflict
clause's falsified literals, whose negation-disjunction is precisely the
conflict clause (up to root drops and order upgrades). The lift then
needs the invariant only for the loop's own steps. -/

/-- Marked-list negation disjunction. -/
def marksNegs (marks : List TrailEntry) : Clause :=
  marks.map fun e => e.literal.negate

/-- Learned-so-far literals. -/
def learntLits (learnt : List (Literal × Nat)) : Clause :=
  learnt.map fun p => p.1

/-- One loop resolution keeps the truth invariant — resolving the
    marked pivot entry against its reason. The seed truth
    `marksNegs marks ++ learntLits learnt` is pivot-NEGATIVE (the
    pivot's negation is one of the marked negations); the reason clause
    is pivot-POSITIVE. Direct proof: an internal solution `a` satisfies
    the seed; if its witness is not the pivot's negation, that witness
    survives the filter and lands in the goal; if it IS the pivot's
    negation, `a` satisfies the goal through the reason's witness
    (`Clause.EntailedBy`), which cannot also be the pivot itself, so it
    survives the reason-side filter. -/
theorem analyzeStep_resolve
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    (learnt : List (Literal × Nat)) (marks : List TrailEntry)
    (pivot : TrailEntry) (reason : Clause)
    (hpv : pivot ∈ marks)
    (hseed : Clause.EntailedBy problem constraintHolds
      (marksNegs marks ++ learntLits learnt))
    (hrv : Clause.EntailedBy problem constraintHolds reason)
    (hpv_in : pivot.literal ∈ reason) :
    Clause.EntailedBy problem constraintHolds
      ((marksNegs marks ++ learntLits learnt).filter
          (fun l => !litEqB l pivot.literal.negate)
        ++ (reason.filter (fun l => !litEqB l pivot.literal))) := by
  intro a ha
  obtain ⟨lw, hlwm, hevw⟩ := hseed a ha
  by_cases hlwp : litEqB lw pivot.literal.negate
  · -- witness is the pivot's negation; fall to the reason's witness
    obtain ⟨lr, hlrm, hevr⟩ := hrv a ha
    by_cases hlrp : litEqB lr pivot.literal
    · -- both pivots true at a: contradiction via eval_negate
      have hlr_eq : lr = pivot.literal := by
        simp only [litEqB, decide_eq_true_eq] at hlrp; exact hlrp
      have h1 : pivot.literal.eval a = some true := by
        rw [hlr_eq] at hevr; exact hevr
      -- lw = pivot.literal.negate from hlwp
      have hlw_eq : lw = pivot.literal.negate := by
        simp only [litEqB, decide_eq_true_eq] at hlwp; exact hlwp
      -- lw's membership: in marksNegs marks side (pivot's own)
      have h2 : pivot.literal.negate.eval a = some true := by
        rw [hlw_eq] at hevw; exact hevw
      rw [show pivot.literal.negate.eval a
            = (pivot.literal.eval a).map (! ·) from
          Literal.eval_negate pivot.literal a] at h2
      rw [h1] at h2
      simp at h2
    · exact ⟨lr, List.mem_append.mpr (Or.inr
        (List.mem_filter.mpr ⟨hlrm, by simpa [litEqB] using hlrp⟩)), hevr⟩
  · -- witness survives the work-side filter
    refine ⟨lw, List.mem_append.mpr (Or.inl ?_), hevw⟩
    exact List.mem_filter.mpr ⟨hlwm, by simpa [litEqB] using hlwp⟩

/-! ### The fuel-inductive entailment lift

The lifting invariant over `analyzeStep fuel cs skip marks learnt`:

* **I1 (worklist truth):** every pending clause in `cs` is entailed by
  the problem — maintained because markLit/scan consume pending clauses
  literally (no clause transformation), and resolution pushes only the
  pivot's reason clause, which is entailed by `Reason.Valid`;
* **I2 (disjunction truth):** `marksNegs marks ++ learntLits learnt` is
  entailed by the problem — initially the conflict clause
  (`[conflict]` seeded via the marks of its falsified literals) — hmm:
  in fact the analyzer's seeds come *from* the conflict clause, one
  mark per non-root falsified literal. The invariant I2 in its clean
  form is exactly: entailed. It is maintained by
  `analyzeStep_resolve`-shaped steps and by *dropping* marks — but
  markLit also *appends* to `learnt` (below-level records), which
  keeps I2 (conjunct grows); and drops root-level marks (a root
  literal's negation leaves the disjunction — justified by RootFacts:
  a root-truth literal is true in every internal solution, so its
  negation never was the sole witness).

I2's maintenance under mark bookskeeping is a separate obligation from
I1 because markLit both narrows and grows the tracked lists. The full
lift below threads both. -/

/-- pending-clause truth (I1) — trivially threaded, stated for reuse. -/
def PendingOk (problem : Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop)
    (cs : List Clause) : Prop :=
  ∀ cl ∈ cs, Clause.EntailedBy problem constraintHolds cl

/-! #### I2 bookkeeping lemmas

`markLit` transforms the tracked pair (marks, learnt) in three ways:
growth of learnt (recording a below pair), growth of marks (marking a
current-level literal), and shrink of marks (dropping a root-level or
duplicate literal). Growth reuses witnesses; shrink of a root literal
is justified by `RootFacts` (its negation never witnesses). -/

/-- Growth of the learnt record keeps I2. -/
theorem learntGrow_preserves
    {marks : List TrailEntry} {p : Literal × Nat}
    (hI2 : Clause.EntailedBy problem constraintHolds
      (marksNegs marks ++ learntLits learnt)) :
    Clause.EntailedBy problem constraintHolds
      (marksNegs marks ++ learntLits (p :: learnt)) := by
  intro a ha
  unfold learntLits at hI2 ⊢
  obtain ⟨l, hl, hev⟩ := hI2 a ha
  rcases List.mem_append.mp hl with h | h
  · exact ⟨l, List.mem_append.mpr (Or.inl h), hev⟩
  · exact ⟨l, List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ h)), hev⟩

/-- Growth of the marks keeps I2. -/
theorem markGrow_preserves
    {marks : List TrailEntry} {e : TrailEntry}
    (hI2 : Clause.EntailedBy problem constraintHolds
      (marksNegs marks ++ learntLits learnt)) :
    Clause.EntailedBy problem constraintHolds
      (marksNegs (e :: marks) ++ learntLits learnt) := by
  intro a ha
  unfold marksNegs at hI2 ⊢
  obtain ⟨l, hl, hev⟩ := hI2 a ha
  rcases List.mem_append.mp hl with h | h
  · exact ⟨l, List.mem_append.mpr (Or.inl (List.mem_cons_of_mem _ h)), hev⟩
  · exact ⟨l, List.mem_append.mpr (Or.inr h), hev⟩

/-- Shrink of a mark whose literal is root-true keeps I2: the removed
    negation can never be the sole witness of an internal solution. -/
theorem markShrinkRoot_preserves
    {marks : List TrailEntry} {e : TrailEntry}
    (hI2 : Clause.EntailedBy problem constraintHolds
      (marksNegs (e :: marks) ++ learntLits learnt))
    (hfac : ∀ a, ProblemSolution problem constraintHolds a →
      e.literal.eval a = some true) :
    Clause.EntailedBy problem constraintHolds
      (marksNegs marks ++ learntLits learnt) := by
  intro a ha
  obtain ⟨l, hl, hev⟩ := hI2 a ha
  unfold marksNegs at hl ⊢
  rcases List.mem_append.mp hl with h | h
  · -- witness lives on the marked side; the removed `e` is the cons head
    rcases List.mem_cons.mp h with rfl | h
    · -- witness is the dropped mark's negation: impossible at a
      have hneg : e.literal.negate.eval a = some true := hev
      rw [show e.literal.negate.eval a = (e.literal.eval a).map (! ·) from
        Literal.eval_negate e.literal a, hfac a ha] at hneg
      simp at hneg
    · refine ⟨l, List.mem_append.mpr (Or.inl ?_), hev⟩
      simpa using h
  · exact ⟨l, List.mem_append.mpr (Or.inr h), hev⟩


/-- All marks equal to `e` (filter-empty invariant) with I2 gives the
    UIP finalization entailment: if `a` falsified
    `learntLits learnt ++ [e.literal.negate]`, then `a` falsifies every
    marks-side literal (each equal to `e.literal.negate`) and every
    learnt-side literal, contradicting I2. -/
theorem UIP_finalize_entailed
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {marks : List TrailEntry} {e : TrailEntry}
    {learnt : List (Literal × Nat)}
    (hempty : (marks.filter fun m => !litEqB m.literal e.literal).isEmpty)
    (hI2 : Clause.EntailedBy problem constraintHolds
      (marksNegs marks ++ learntLits learnt)) :
    Clause.EntailedBy problem constraintHolds
      (learntLits learnt ++ [e.literal.negate]) := by
  intro a ha
  obtain ⟨l, hl, hev⟩ := hI2 a ha
  unfold marksNegs learntLits at hl
  rcases List.mem_append.mp hl with hm | hl'
  · -- m's literal is ≡ e.literal (filter-empty argument)
    obtain ⟨m, hmem, hmap⟩ := List.mem_map.mp hm
    by_cases hb : litEqB m.literal e.literal
    · have hliteq : m.literal = e.literal := by
        simpa only [litEqB, decide_eq_true_eq] using hb
      have hleq : l = e.literal.negate := by
        rw [← hmap]
        exact congrArg Literal.negate hliteq
      subst hleq
      have hmem : e.literal.negate ∈ learntLits learnt ++
          [e.literal.negate] :=
        List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
      exact ⟨e.literal.negate, hmem, hev⟩
    · -- m would survive the filter: contradiction with emptiness
      exfalso
      have : m ∈ (marks.filter fun mm => !litEqB mm.literal e.literal) :=
        List.mem_filter.mpr ⟨hmem, by simp [hb]⟩
      rw [List.isEmpty_iff.mp hempty] at this
      exact absurd this List.not_mem_nil
  -- the learnt-side witness is retained verbatim in the goal clause
  · exact ⟨l, List.mem_append.mpr (Or.inl hl'), hev⟩

/-! #### The worklist lift (L0.4 step 5)

`analyzeStep`'s worklist evolves by *suffixing*: a scanned clause
`(q0 :: qs)` recurses on `qs :: cs` — the pending elements are clause
suffixes, not whole clauses. The invariant therefore tracks the
pending suffix literals explicitly inside the tracked disjunction:

    pendingLits cs skip ++ marksNegs marks ++ learntLits learnt

is entailed; a scanned literal `q0` moves to `marks` (current-level
falsifier), to `learnt` (below-level falsifier), or drops (root-level
falsifier, justified by `RootFacts` via the evaluation chain below).
Resolution (empty worklist, nonlast marked pivot) consumes the pivot's
mark and re-seeds its reason clause minus the pivot, exactly the
resolution rule. UIP finalization emits `uip.negate` above the below
record.

Everything is proved by witness transfer: an internal solution `a`
satisfies the tracked disjunction through some literal; each branch
maps that witness into the successor disjunction (identity, norm, or
`orderUpgrade` weakening), or refutes the dropped witness outright
(root falsifiers, opposing-pivot reasons). -/

/-- The pending-suffix literals in normalized form: every literal of
    every pending clause, normalized, minus the resolution skip. -/
def pendingLits (cs : List Clause) (skip : Option Literal) : Clause :=
  ((cs.flatMap id).map Literal.norm).filter fun l => !skipEq skip l

/-- The tracked-disjunction invariant of the analysis worklist. -/
def Tracked (problem : Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop)
    (cs : List Clause) (skip : Option Literal)
    (marks : List TrailEntry) (learnt : List (Literal × Nat)) : Prop :=
  Clause.EntailedBy problem constraintHolds
    (pendingLits cs skip ++ marksNegs marks ++ learntLits learnt)

/-! ##### Auxiliary evaluation lemmas -/

/-- Normalization is a fixed point of itself and of literal negation:
    `(l.negate).norm.negate.norm = l.norm`, so the negation of a trail
    entry that falsifies `l` evaluates exactly like `l`. -/
theorem negate_norm_square (l : Literal) :
    l.negate.norm.negate.norm = l.norm := by
  cases l with
  | mk atom positive =>
    cases atom with
    | intLe s k => cases positive <;> rfl
    | boolEq s b =>
        cases positive with
        | true =>
            show (Literal.mk (Atom.boolEq s b) false).norm.negate.norm
                 = (Literal.mk (Atom.boolEq s b) true).norm
            simp [Literal.norm, Literal.negate]
        | false =>
            show (Literal.mk (Atom.boolEq s b) false).negate.norm.negate.norm
                 = (Literal.mk (Atom.boolEq s b) false).norm
            simp [Literal.norm, Literal.negate]
    | intNe s k => cases positive <;> rfl

/-- Normalization is idempotent. -/
theorem norm_norm (l : Literal) : l.norm.norm = l.norm := by
  cases l with
  | mk atom positive =>
    cases atom with
    | intLe s k => cases positive <;> rfl
    | boolEq s b =>
        cases positive with
        | true => rfl
        | false =>
            show (Literal.mk (Atom.boolEq s (!b)) true).norm.norm
                 = (Literal.mk (Atom.boolEq s b) false).norm
            simp only [Literal.norm]
            cases b <;> rfl
    | intNe s k => cases positive <;> rfl

/-- `findEntryOf` returns an entry whose literal is exactly the
    normalized target. -/
theorem findEntryOf_literal (trail : List TrailEntry) (l : Literal)
    (e : TrailEntry) (h : findEntryOf trail l = some e) :
    e.literal = l.norm := by
  unfold findEntryOf at h
  obtain ⟨hp, _, _, _, _⟩ := List.find?_eq_some_iff_append.mp h
  simpa only [litEqB, decide_eq_true_eq] using hp

/-- `nextPivot`'s found entry is a trail entry. -/
theorem nextPivot_trail_mem (trail : List TrailEntry)
    (marks : List TrailEntry) (e : TrailEntry)
    (h : nextPivot trail marks = some e) :
    e ∈ trail := by
  unfold nextPivot at h
  obtain ⟨hp, as, bs, hrw, _⟩ := List.find?_eq_some_iff_append.mp h
  have hmem : e ∈ trail.reverse := by
    rw [hrw, List.mem_append]
    exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
  exact List.mem_reverse.mp hmem

/-! ##### Order-upgrade and evaluation-transfer lemmas -/

/-- The order upgrade produces a *weaker* literal: whenever `l` holds
    at an assignment, so does its upgrade. (An upgrade fires only when
    the trail bound is beyond `l`'s own bound, which makes the
    upgraded bound at least as permissive.) -/
theorem orderUpgrade_weaken (trail : List TrailEntry) (l : Literal)
    (a : Assignment) (hl : l.eval a = some true) :
    (orderUpgrade trail l).eval a = some true := by
  cases l with
  | mk atom positive =>
    cases atom with
    | intLe s k =>
        cases positive with
        | true =>
            simp only [orderUpgrade, if_pos]
            cases hlo : trailLoOf trail s with
            | none => exact hl
            | some lo =>
              simp only []
              by_cases hfire : lo > k
              · rw [if_pos hfire]
                have hl' : (posLe s k).eval a = some true := hl
                rw [eval_posLe_iff] at hl'
                rw [eval_posLe_iff]
                obtain ⟨i, hi, hik⟩ := hl'
                exact ⟨i, hi, by omega⟩
              · rw [if_neg hfire]; exact hl
        | false =>
            simp only [orderUpgrade, Bool.not_eq_true, if_neg]
            cases hhi : trailHiOf trail s with
            | none => exact hl
            | some hi =>
              simp only []
              by_cases hfire : hi ≤ k
              · rw [if_pos hfire]
                have hl' : (negLe s k).eval a = some true := hl
                rw [eval_negLe_iff] at hl'
                rw [eval_negLe_iff]
                obtain ⟨i, hi2, hik⟩ := hl'
                exact ⟨i, hi2, by omega⟩
              · rw [if_neg hfire]; exact hl
    | boolEq s b =>
        cases positive with
        | true =>
            cases b with
            | true =>
                cases hhi : trailHiOf trail s with
                | none =>
                    simp only [orderUpgrade, posBool, hhi, if_true, reduceIte]
                    exact hl
                | some hi =>
                    simp only [orderUpgrade, posBool, hhi, if_true, reduceIte]
                    by_cases hfire : hi ≤ 0
                    · simp only [if_pos hfire, reduceIte]
                      -- a reads s as true (integer view 1); the
                      -- weakened literal "s > hi" holds since hi ≤ 0
                      have hs : a[s]? = some (.bool true) := by
                        have hl2 : (posBool s true).eval a = some true :=
                          hl
                        rw [eval_posBool_iff] at hl2
                        exact hl2
                      rw [eval_negLe_iff]
                      exact ⟨1, by rw [slotInt, hs]; rfl, by omega⟩
                    · simp only [if_neg hfire]; exact hl
            | false =>
                cases hlo : trailLoOf trail s with
                | none =>
                    simp only [orderUpgrade, posBool, hlo, if_true, reduceIte]
                    exact hl
                | some lo =>
                    simp only [orderUpgrade, posBool, hlo, if_neg,
                      Bool.false_eq_true, reduceIte]
                    by_cases hfire : 1 ≤ lo
                    · simp only [if_pos hfire, reduceIte]
                      -- a reads s as false (integer view 0); the
                      -- weakened literal "s ≤ lo−1" holds since lo ≥ 1
                      have hs : a[s]? = some (.bool false) := by
                        have hl2 : (posBool s false).eval a = some true :=
                          hl
                        rw [eval_posBool_iff] at hl2
                        exact hl2
                      rw [eval_posLe_iff]
                      exact ⟨0, by rw [slotInt, hs]; rfl, by omega⟩
                    · simp only [if_neg hfire]; exact hl
        | false =>
            -- a NEGATIVE Boolean literal is never the normalized
            -- upgrade input (markLit norm-normalizes first); the
            -- hypothesis is preserved unchanged
            simp only [orderUpgrade]
            exact hl
    | intNe s k =>
        -- value-removal literals have no order upgrade: the exact
        -- falsifier entry `intNe s k` matches by negation directly
        simp only [orderUpgrade]
        exact hl

/-- A trail entry found as the falsifier of `q'` (its literal is the
    normalized negation of `q'`) has its own negation *true* exactly
    when `q'` is false. In particular, if some witness made `q'`'s
    coverage necessary, the mark-side literal `e.literal.negate` cannot
    be true simultaneously at a trail-consistent assignment — the
    mark side covers the falsification regime, the pending side the
    satisfaction regime. -/
theorem falsifier_negation_eval (q' : Literal) (e : TrailEntry)
    (he : e.literal = q'.negate.norm) (a : Assignment) :
    e.literal.negate.eval a = some true ∨
      q'.eval a = some false ∨ q'.eval a = none := by
  match h : q'.eval a with
  | some true =>
      left
      rw [he]
      rw [show (q'.negate.norm).negate.eval a
            = ((q'.negate.norm).eval a).map (! ·) from
          Literal.eval_negate _ a]
      rw [show (q'.negate.norm).eval a = q'.negate.eval a from
        Literal.norm_eval _ a]
      rw [Literal.eval_negate q' a, h]
      simp
  | some false => exact Or.inr (Or.inl rfl)
  | none => exact Or.inr (Or.inr rfl)

/-- Witness-map monotonicity: if every literal of an entailed
    clause has an eval-equal counterpart in the target clause, the
    target clause is entailed. -/
theorem norm_transfer {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop} {C C' : Clause}
    (hsub : ∀ l ∈ C, ∃ l' ∈ C', l'.eval = l.eval)
    (h : Clause.EntailedBy problem constraintHolds C) :
    Clause.EntailedBy problem constraintHolds C' := by
  intro a ha
  obtain ⟨l, hl, hev⟩ := h a ha
  obtain ⟨l', hl', hlev⟩ := hsub l hl
  exact ⟨l', hl', hlev ▸ hev⟩

/-- Entailment is monotone in the clause: a superclause of an
    entailed clause is entailed. -/
theorem entailed_mono {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop} {C C' : Clause}
    (hsub : ∀ l ∈ C, l ∈ C') :
    (Clause.EntailedBy problem constraintHolds C) →
    (Clause.EntailedBy problem constraintHolds C') := by
  intro hent a ha
  obtain ⟨l, hl, hev⟩ := hent a ha
  exact ⟨l, hsub l hl, hev⟩

/-- Normalization is eval-preserving, so an entailment of the
    normalized clause lifts back to the original literal list. -/
theorem entailed_of_normMap {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop} (C : Clause) :
    (Clause.EntailedBy problem constraintHolds (C.map Literal.norm)) →
    (Clause.EntailedBy problem constraintHolds C) := by
  intro hent a ha
  obtain ⟨l1, hl1, hev⟩ := hent a ha
  obtain ⟨l0, hl0, hmap⟩ := List.mem_map.mp hl1
  have hev0 : l0.eval a = some true := by
    rw [← Literal.norm_eval l0 a, hmap]
    exact hev
  exact ⟨l0, hl0, hev0⟩

-- (helper lemma inserted before the lift)

/-! ##### `markLit` shape inversion and falsifier evaluation -/

/-- `List.any` hit extraction for the marks duplicate check. -/
theorem any_marks_mem {marks : List TrailEntry} {X : Literal}
    (h : (marks.any fun m => litEqB m.literal X) = true) :
    ∃ m ∈ marks, m.literal = X := by
  rw [List.any_eq_true] at h
  obtain ⟨m, hm, hb⟩ := h
  refine ⟨m, hm, ?_⟩
  simpa only [litEqB, decide_eq_true_eq] using hb

/-- `List.any` hit extraction for the learnt duplicate check. -/
theorem any_learnt_mem {learnt : List (Literal × Nat)} {X : Literal}
    (h : (learnt.any fun p => litEqB p.1 X) = true) :
    ∃ p ∈ learnt, p.1 = X := by
  rw [List.any_eq_true] at h
  obtain ⟨p, hp, hb⟩ := h
  refine ⟨p, hp, ?_⟩
  simpa only [litEqB, decide_eq_true_eq] using hb

/-- A member's negated literal belongs to the marks disjunction. -/
theorem mem_marksNegs_of_mem {e : TrailEntry} {marks : List TrailEntry}
    (h : e ∈ marks) : e.literal.negate ∈ marksNegs marks := by
  unfold marksNegs
  exact List.mem_map_of_mem h

/-- A recorded literal belongs to the learnt disjunction. -/
theorem mem_learntLits_of_mem {p : Literal × Nat}
    {learnt : List (Literal × Nat)} (h : p ∈ learnt) :
    p.1 ∈ learntLits learnt := by
  unfold learntLits
  exact List.mem_map_of_mem h

/-- Marks-disjunction membership survives growth by a fresh mark. -/
theorem marksNegs_cons_sub {e : TrailEntry} {marks : List TrailEntry}
    {l : Literal} (h : l ∈ marksNegs marks) :
    l ∈ marksNegs (e :: marks) := by
  unfold marksNegs at h ⊢
  exact List.mem_cons_of_mem _ h

/-- The fresh mark's negation heads the grown marks disjunction. -/
theorem marksNegs_cons_head (e : TrailEntry) (marks : List TrailEntry) :
    e.literal.negate ∈ marksNegs (e :: marks) := by
  unfold marksNegs
  exact List.mem_cons_self

/-- Learnt-disjunction membership survives growth by a fresh pair. -/
theorem learntLits_cons_sub {p : Literal × Nat}
    {learnt : List (Literal × Nat)} {l : Literal}
    (h : l ∈ learntLits learnt) : l ∈ learntLits (p :: learnt) := by
  unfold learntLits at h ⊢
  exact List.mem_cons_of_mem _ h

/-- The fresh record's literal heads the grown learnt disjunction. -/
theorem learntLits_cons_head (p : Literal × Nat)
    (learnt : List (Literal × Nat)) :
    p.1 ∈ learntLits (p :: learnt) := by
  unfold learntLits
  exact List.mem_cons_self

/-- The entry found as the falsifier of `q'` has its own negation true
    exactly where `q'` itself is true (the found literal is the
    normalized negation of `q'`, so flipping it twice returns `q'`'s
    truth value). -/
theorem falsifier_neg_true {q' : Literal} {e : TrailEntry}
    (he : e.literal = q'.negate.norm) (a : Assignment)
    (hq : q'.eval a = some true) :
    e.literal.negate.eval a = some true := by
  rw [he, Literal.eval_negate (q'.negate.norm) a,
    Literal.norm_eval (q'.negate) a, Literal.eval_negate q' a, hq]
  rfl

/-- A root-level falsifier contradicts the cover premise: its own
    literal is true at every internal solution (`RootFacts`), but it
    is the normalized negation of `q'`, so `q'` would have to be false
    there — contradicting `q'` true. -/
theorem root_drop_refutes {q' : Literal} {e : TrailEntry}
    (he : e.literal = q'.negate.norm) (a : Assignment)
    (hrootv : e.literal.eval a = some true)
    (hq : q'.eval a = some true) : False := by
  rw [he, Literal.norm_eval (q'.negate) a,
    Literal.eval_negate q' a, hq] at hrootv
  simp at hrootv

/-- `markLit` shape inversion: a successful call is exactly one of —
    the literal already marked, already learnt, freshly marked at the
    current level, freshly recorded below the current level, or dropped
    because its falsifier sits at the root. Each disjunct carries the
    witness entries, the resulting `(marks', learnt')` shapes, and the
    falsifier's literal identity `e.literal = q'.negate.norm` with
    `q'` either the scanned literal itself or its order upgrade. -/
theorem markLit_inv (trail : List TrailEntry) (lvl : Nat)
    (marks : List TrailEntry) (learnt : List (Literal × Nat))
    (q0 : Literal) (marks' : List TrailEntry)
    (learnt' : List (Literal × Nat))
    (h : markLit trail lvl marks learnt q0 = some (marks', learnt')) :
    (∃ m ∈ marks, m.literal = q0.norm.negate.norm ∧
        marks' = marks ∧ learnt' = learnt) ∨
    (∃ p ∈ learnt, p.1 = q0.norm ∧
        marks' = marks ∧ learnt' = learnt) ∨
    (∃ e ∈ trail, ∃ q', (q' = q0.norm ∨ q' = orderUpgrade trail q0.norm) ∧
        e.literal = q'.negate.norm ∧
        marks' = e :: marks ∧ learnt' = learnt ∧ e.level = lvl) ∨
    (∃ e ∈ trail, ∃ q', (q' = q0.norm ∨ q' = orderUpgrade trail q0.norm) ∧
        e.literal = q'.negate.norm ∧
        marks' = marks ∧ learnt' = (q', e.level) :: learnt ∧
        e.level ≠ 0 ∧ e.level ≠ lvl) ∨
    (∃ e ∈ trail, ∃ q', (q' = q0.norm ∨ q' = orderUpgrade trail q0.norm) ∧
        e.literal = q'.negate.norm ∧
        marks' = marks ∧ learnt' = learnt ∧ e.level = 0) := by
  unfold markLit at h
  simp only [] at h
  by_cases hA : (marks.any fun m =>
      litEqB m.literal q0.norm.negate.norm) = true
  · rw [if_pos hA] at h
    cases h
    obtain ⟨m, hm, hmlit⟩ := any_marks_mem hA
    exact Or.inl ⟨m, hm, hmlit, rfl, rfl⟩
  rw [if_neg hA] at h
  by_cases hB : (learnt.any fun p => litEqB p.1 q0.norm) = true
  · rw [if_pos hB] at h
    cases h
    obtain ⟨p, hp, hp1⟩ := any_learnt_mem hB
    exact Or.inr (Or.inl ⟨p, hp, hp1, rfl, rfl⟩)
  rw [if_neg hB] at h
  cases hf1 : findEntryOf trail q0.norm.negate with
  | some val =>
      rw [hf1] at h
      simp only [] at h
      cases hf2 : findEntryOf trail q0.norm.negate with
      | none => rw [hf2] at h; simp at h
      | some e =>
          rw [hf2] at h
          simp only [] at h
          have helit := findEntryOf_literal trail q0.norm.negate e hf2
          by_cases h0 : (e.level == 0) = true
          · rw [if_pos h0] at h
            cases h
            have hroot0 : e.level = 0 := by
              simp only [beq_iff_eq] at h0
              exact h0
            exact Or.inr (Or.inr (Or.inr (Or.inr
              ⟨e, findEntry_mem trail _ e hf2, q0.norm, Or.inl rfl,
                helit, rfl, rfl, hroot0⟩)))
          rw [if_neg h0] at h
          by_cases hl : (e.level == lvl) = true
          · rw [if_pos hl] at h
            cases h
            have hlvl : e.level = lvl := by
              simp only [beq_iff_eq] at hl
              exact hl
            exact Or.inr (Or.inr (Or.inl
              ⟨e, findEntry_mem trail _ e hf2, q0.norm, Or.inl rfl,
                helit, rfl, rfl, hlvl⟩))
          rw [if_neg hl] at h
          cases h
          have he0 : e.level ≠ 0 := by
            simp only [beq_iff_eq] at h0
            exact fun he => h0 he
          have helv : e.level ≠ lvl := by
            simp only [beq_iff_eq] at hl
            exact fun he => hl he
          exact Or.inr (Or.inr (Or.inr (Or.inl
            ⟨e, findEntry_mem trail _ e hf2, q0.norm, Or.inl rfl,
              helit, rfl, rfl, he0, helv⟩)))
  | none =>
      rw [hf1] at h
      simp only [] at h
      cases hf2 : findEntryOf trail
          (orderUpgrade trail q0.norm).negate with
      | none => rw [hf2] at h; simp at h
      | some e =>
          rw [hf2] at h
          simp only [] at h
          have helit := findEntryOf_literal trail
            (orderUpgrade trail q0.norm).negate e hf2
          by_cases h0 : (e.level == 0) = true
          · rw [if_pos h0] at h
            cases h
            have hroot0 : e.level = 0 := by
              simp only [beq_iff_eq] at h0
              exact h0
            exact Or.inr (Or.inr (Or.inr (Or.inr
              ⟨e, findEntry_mem trail _ e hf2,
                orderUpgrade trail q0.norm, Or.inr rfl,
                helit, rfl, rfl, hroot0⟩)))
          rw [if_neg h0] at h
          by_cases hl : (e.level == lvl) = true
          · rw [if_pos hl] at h
            cases h
            have hlvl : e.level = lvl := by
              simp only [beq_iff_eq] at hl
              exact hl
            exact Or.inr (Or.inr (Or.inl
              ⟨e, findEntry_mem trail _ e hf2,
                orderUpgrade trail q0.norm, Or.inr rfl,
                helit, rfl, rfl, hlvl⟩))
          rw [if_neg hl] at h
          cases h
          have he0 : e.level ≠ 0 := by
            simp only [beq_iff_eq] at h0
            exact fun he => h0 he
          have helv : e.level ≠ lvl := by
            simp only [beq_iff_eq] at hl
            exact fun he => hl he
          exact Or.inr (Or.inr (Or.inr (Or.inl
            ⟨e, findEntry_mem trail _ e hf2,
              orderUpgrade trail q0.norm, Or.inr rfl,
              helit, rfl, rfl, he0, helv⟩)))

theorem tracked_markDrop
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {qs : Clause} {cs : List Clause} {skip : Option Literal}
    {marks marks' : List TrailEntry}
    {learnt learnt' : List (Literal × Nat)}
    {p0 : Literal}
    (hside : ∀ l, l ∈ marksNegs marks ++ learntLits learnt →
      ∃ l', l' ∈ marksNegs marks' ++ learntLits learnt' ∧
        l'.eval = l.eval)
    (hcover : ∀ a, ProblemSolution problem constraintHolds a →
      p0.norm.eval a = some true →
      (marksNegs marks' ++ learntLits learnt').SatisfiedBy a)
    (htrack : Tracked problem constraintHolds ((p0 :: qs) :: cs) skip
      marks learnt) :
    Tracked problem constraintHolds (qs :: cs) skip marks' learnt' := by
  unfold Tracked
  intro a ha
  obtain ⟨l, hl, hev⟩ := htrack a ha
  -- Convert the goal into the RIGHT-ASSOC append form ONCE, then all
  -- splits are uniform (outer: pending vs sides; inner: marks vs
  -- learnt):
  refine ?_
  rw [show pendingLits (qs :: cs) skip ++ marksNegs marks' ++
      learntLits learnt'
    = pendingLits (qs :: cs) skip ++ (marksNegs marks' ++
      learntLits learnt') from List.append_assoc _ _ _]
  -- goal: witness ∈ P ++ (M' ++ L')
  have memL {x : Literal} (hx : x ∈ marksNegs marks' ++
      learntLits learnt') :
      x ∈ pendingLits (qs :: cs) skip ++ (marksNegs marks' ++
        learntLits learnt') :=
    List.mem_append.mpr (Or.inr hx)
  have memP {x : Literal} (hx : x ∈ List.filter
      (fun lx => !skipEq skip lx)
      (List.map Literal.norm (qs ++ cs.flatMap id))) :
      x ∈ pendingLits (qs :: cs) skip ++ (marksNegs marks' ++
        learntLits learnt') := by
    unfold pendingLits
    simp only [List.flatMap_cons, List.append_nil, id_eq,
      List.map_cons, List.mem_append]
    exact Or.inl hx
  -- hypothesis side: use List.mem_append on hl directly after
  -- folding through append_assoc (via the reverse direction):
  have hlr : l ∈ pendingLits ((p0 :: qs) :: cs) skip ++
      (marksNegs marks ++ learntLits learnt) := by
    rw [List.append_assoc] at hl
    exact hl
  unfold pendingLits at hlr
  simp only [List.flatMap_cons, List.append_nil, id_eq, List.map_cons,
    List.filter_cons, List.cons_append, List.mem_append,
    List.mem_cons] at hlr
  by_cases hcond : (!skipEq skip p0.norm) = true
  · rw [if_pos hcond] at hlr
    -- hlr is fully decomposed: 3-way Or
    rcases hlr with hp | hsides
    · rcases List.mem_cons.mp hp with heq | hf
      · rw [heq] at hev
        obtain ⟨w, hwm, hwev⟩ := hcover a ha hev
        exact ⟨w, memL hwm, hwev⟩
      · exact ⟨l, memP hf, hev⟩
    · rcases hsides with hm2 | hl2
      · obtain ⟨l', hl'', hlev⟩ := hside l
          (List.mem_append.mpr (Or.inl hm2))
        exact ⟨l', memL hl'', hlev ▸ hev⟩
      · obtain ⟨l', hl'', hlev⟩ := hside l
          (List.mem_append.mpr (Or.inr hl2))
        exact ⟨l', memL hl'', hlev ▸ hev⟩
  · rw [if_neg hcond] at hlr
    rcases hlr with hp | hsides
    · exact ⟨l, memP hp, hev⟩
    · rcases hsides with hm2 | hl2
      · obtain ⟨l', hl'', hlev⟩ := hside l
          (List.mem_append.mpr (Or.inl hm2))
        exact ⟨l', memL hl'', hlev ▸ hev⟩
      · obtain ⟨l', hl'', hlev⟩ := hside l
          (List.mem_append.mpr (Or.inr hl2))
        exact ⟨l', memL hl'', hlev ▸ hev⟩


/-! ##### The markLit branch of the worklist lift

One scanned pending literal `q0` drops from the pending side; the
five `markLit` shapes relocate its coverage into the successor's
tracked disjunction (identity, monotone growth, or refutation). -/

/-- The markLit step of the analysis worklist: given the tracked
    disjunction before scanning `q0` and the `markLit` result shapes,
    produce the successor worklist's tracked disjunction and the
    trail-membership of the successor marks. This is the full
    five-shape case analysis over `markLit_inv`:

    * already marked — identity transfer, cover via the duplicate's
      negation (`falsifier_neg_true`, the mark's literal is the
      normalized negation of the dropped literal);
    * already learnt — identity transfer, cover via the record;
    * fresh mark at the current level — monotone transfer, cover via
      the fresh mark's negation (falsifier identity, possibly through
      the order upgrade's weakening);
    * fresh below-level record — monotone transfer (the learnt list
      grows), cover via the recorded literal (`orderUpgrade_weaken`
      when it is the upgrade);
    * root drop — identity transfer with the cover premise refuted:
      the falsifying entry sits at the root, so `RootFacts` makes its
      literal true at every internal solution, contradicting the
      dropped literal being true there. -/
theorem markLit_branch {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    (trail : List TrailEntry) (lvl : Nat)
    (hroot : RootFacts problem constraintHolds trail)
    (qs : Clause) (cs : List Clause) (skip : Option Literal)
    (marks : List TrailEntry) (learnt : List (Literal × Nat))
    (q0 : Literal) (marks' : List TrailEntry)
    (learnt' : List (Literal × Nat))
    (hmark : markLit trail lvl marks learnt q0.norm = some (marks', learnt'))
    (htrack : Tracked problem constraintHolds ((q0 :: qs) :: cs) skip
      marks learnt)
    (hmarks : ∀ e ∈ marks, e ∈ trail) :
    (Tracked problem constraintHolds (qs :: cs) skip marks' learnt') ∧
    (∀ m ∈ marks', m ∈ trail) := by
  obtain hinv := markLit_inv trail lvl marks learnt q0.norm marks' learnt' hmark
  rcases hinv with
    ⟨m0, hm0, hmlit0, hmm, hlm⟩ |
    ⟨p0, hp0, hp1_0, hmm, hlm⟩ |
    ⟨e, hetr, q', hq'0, helit, hmm, hlm, hlvl⟩ |
    ⟨e, hetr, q', hq'0, helit, hmm, hlm, he0, helv⟩ |
    ⟨e, hetr, q', hq'0, helit, hmm, hlm, hroot0⟩
  · -- SHAPE 1 (already marked): identity side transfer; the cover is
    -- the existing mark's negation — its literal is the normalized
    -- negation of the dropped literal's normalized form, so its
    -- negation evaluates exactly like it.
    rw [hmm, hlm]
    refine ⟨?_, hmarks⟩
    refine tracked_markDrop (hside := ?_) (hcover := ?_) htrack
    · intro l hlmem
      exact ⟨l, hlmem, rfl⟩
    · intro a ha hev
      refine ⟨m0.literal.negate, ?_, ?_⟩
      · exact List.mem_append.mpr (Or.inl (mem_marksNegs_of_mem hm0))
      · exact falsifier_neg_true hmlit0 a
          (by rw [Literal.norm_eval (q0.norm) a]; exact hev)
  · -- SHAPE 2 (already learnt): identity side transfer; the cover is
    -- the recorded literal itself (eval-equal through norm).
    rw [hmm, hlm]
    refine ⟨?_, hmarks⟩
    refine tracked_markDrop (hside := ?_) (hcover := ?_) htrack
    · intro l hlmem
      exact ⟨l, hlmem, rfl⟩
    · intro a ha hev
      refine ⟨p0.1, ?_, ?_⟩
      · exact List.mem_append.mpr (Or.inr (mem_learntLits_of_mem hp0))
      · rw [hp1_0, Literal.norm_eval (q0.norm) a]
        exact hev
  · -- SHAPE 3 (fresh mark at the current level): monotone side
    -- transfer; the cover is the fresh mark's negation, eval-equal to
    -- the dropped literal through the falsifier identity.
    rw [hmm, hlm]
    refine ⟨?_, ?_⟩
    · refine tracked_markDrop (hside := ?_) (hcover := ?_) htrack
      · intro l hlmem
        refine ⟨l, ?_, rfl⟩
        rcases List.mem_append.mp hlmem with h | h
        · exact List.mem_append.mpr (Or.inl (marksNegs_cons_sub h))
        · exact List.mem_append.mpr (Or.inr h)
      · intro a ha hev
        refine ⟨e.literal.negate, ?_, ?_⟩
        · exact List.mem_append.mpr (Or.inl (marksNegs_cons_head e marks))
        · exact falsifier_neg_true helit a
            (by
              rcases hq'0 with hA | hA
              · rw [hA, Literal.norm_eval (q0.norm) a]
                exact hev
              · rw [hA]
                exact orderUpgrade_weaken trail (q0.norm.norm) a
                  (by rw [Literal.norm_eval (q0.norm) a]; exact hev))
    · intro m hm
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact hetr
      · exact hmarks m hm'
  · -- SHAPE 4 (fresh below-level record): monotone side transfer
    -- (the learnt list grows); the cover is the recorded literal,
    -- either the dropped literal's normalized form or its order
    -- upgrade (implied by it).
    rw [hmm, hlm]
    refine ⟨?_, hmarks⟩
    refine tracked_markDrop (hside := ?_) (hcover := ?_) htrack
    · intro l hlmem
      refine ⟨l, ?_, rfl⟩
      rcases List.mem_append.mp hlmem with h | h
      · exact List.mem_append.mpr (Or.inl h)
      · exact List.mem_append.mpr (Or.inr (learntLits_cons_sub h))
    · intro a ha hev
      refine ⟨q', ?_, ?_⟩
      · exact List.mem_append.mpr (Or.inr
          (learntLits_cons_head (q', e.level) learnt))
      · rcases hq'0 with hA | hA
        · rw [hA, Literal.norm_eval (q0.norm) a]
          exact hev
        · rw [hA]
          exact orderUpgrade_weaken trail (q0.norm.norm) a
            (by rw [Literal.norm_eval (q0.norm) a]; exact hev)
  · -- SHAPE 5 (root drop): identity side transfer; the cover premise
    -- is refuted — the falsifying entry sits at the root, so its
    -- literal is true at every internal solution (RootFacts), yet it
    -- is the normalized negation of the dropped literal, which the
    -- cover premise makes true: contradiction.
    rw [hmm, hlm]
    refine ⟨?_, hmarks⟩
    refine tracked_markDrop (hside := ?_) (hcover := ?_) htrack
    · intro l hlmem
      exact ⟨l, hlmem, rfl⟩
    · intro a ha hev
      exfalso
      rcases hq'0 with hA | hA
      · rw [hA] at helit
        exact root_drop_refutes helit a (hroot e hetr hroot0 a ha)
          (by rw [Literal.norm_eval (q0.norm) a]; exact hev)
      · rw [hA] at helit
        exact root_drop_refutes helit a (hroot e hetr hroot0 a ha)
          (orderUpgrade_weaken trail (q0.norm.norm) a
            (by rw [Literal.norm_eval (q0.norm) a]; exact hev))

/-! ##### The worklist lift

Every step of the analysis preserves the tracked disjunction. The
proof is witness transfer: an internal solution `a` satisfies the
tracked disjunction via some witness literal; each branch relocates
that witness in the successor's tracked disjunction, or refutes it.

The five `analyzeStep` shapes:

* `[]` pending (nil-clause): recursing drops the (empty) clause from
  the join — a subset step, so membership in the smaller join implies
  membership in the bigger one;
* `skipEq skip q`: the skipped literal is the pivot of the current
  resolution round — already covered by the reason-scan that follows
  (its mark was consumed into `[r.clause]` in the resolution branch);
  the skip filter removes exactly that copy;
* `markLit` unchanged: the scanned literal was already covered;
* fresh mark: the literal moves from the pending side to the marked
  side — `markGrow` shape;
* fresh below pair: the literal moves to the learnt record —
  `learntGrow` shape;
* root drop: the falsifier's level is 0 — `RootFacts` makes the
  negation of the found entry's literal false at every internal
  solution... specifically, the found entry `e`'s literal is `q.negate`
  (it falsifies `q`), so `q` itself never witnesses and the drop is
  sound;
* resolution with `marks'` nonempty: `resolve_step` on the pivot's
  marked negation against the reason clause;
* UIP finalization: `UIP_finalize_entailed`. -/
theorem analyzeStep_tracked (trail : List TrailEntry) (lvl : Nat)
    (hreasons : ∀ e ∈ trail, ∀ r ∈ e.reason,
      Reason.Valid problem constraintHolds r e.literal)
    (hroot : RootFacts problem constraintHolds trail)
    -- reachability premise: every reason clause consists of
    -- normalized literals (reasons are built from trail facts and
    -- order literals, both normalized); needed for the resolution
    -- branch's degenerate corner (raw l with l.norm = pivot)
    (hrnorm : ∀ e ∈ trail, ∀ r ∈ e.reason, ∀ l ∈ r.clause, l = l.norm) :
    ∀ (fuel : Nat) (cs : List Clause) (skip : Option Literal)
      (marks : List TrailEntry) (learnt : List (Literal × Nat)),
    Tracked problem constraintHolds cs skip marks learnt →
    (∀ e ∈ marks, e ∈ trail) →
    ∀ (below : List (Literal × Nat)) (uip : Literal),
      analyzeStep trail lvl fuel cs skip marks learnt
        = some (below, uip) →
      Clause.EntailedBy problem constraintHolds
        (learntLits below ++ [uip.negate]) := by
  intro fuel
  induction fuel with
  | zero =>
      intro cs skip marks learnt _ _ below uip h
      rw [analyzeStep] at h; simp at h
  | succ fuel ih =>
      intro cs skip marks learnt htrack hmarks below uip h
      cases cs with
      | nil =>
          rw [analyzeStep] at h
          cases hpivot : nextPivot trail marks with
          | none => rw [hpivot] at h; simp at h
          | some e =>
              rw [hpivot] at h
              simp only [] at h
              have hmem : e ∈ trail := nextPivot_trail_mem trail marks e hpivot
              by_cases hempty : (marks.filter fun m =>
                  !litEqB m.literal e.literal).isEmpty
              · rw [if_pos hempty] at h
                cases h
                -- UIP finalization: the pending side is empty, so the
                -- tracked disjunction IS the `UIP_finalize_entailed`
                -- precondition shape.
                exact UIP_finalize_entailed hempty (by
                  have := htrack
                  unfold Tracked pendingLits at this
                  simpa [List.flatMap_nil] using this)
              · rw [if_neg hempty] at h
                cases hreason : e.reason with
                | none => rw [hreason] at h; simp at h
                | some r =>
                    rw [hreason] at h
                    -- Resolution step: the pivot's mark is consumed,
                    -- the reason clause re-seeded with skip = pivot.
                    -- Derive the successor's Tracked by an explicit
                    -- resolution (resolve_step) between the tracked
                    -- disjunction (which contains e.literal.negate
                    -- via e ∈ marks) and the entailed reason clause.
                    have hrm : r ∈ e.reason := by
                      rw [hreason]
                      exact Option.mem_some_iff.mpr rfl
                    obtain ⟨hrv, _⟩ := hreasons e hmem r hrm
                    have hbt : Tracked problem constraintHolds
                        [r.clause] (some e.literal)
                        (marks.filter fun m => !litEqB m.literal e.literal)
                        learnt := by
                      -- The seed disjunction (pending empty):
                      --   marksNegs marks ++ learntLits learnt
                      -- contains the pivot's negation (e ∈ marks).
                      -- resolve_step against the entailed reason yields
                      -- the resolvent
                      --   (seed ∖ e.literal.negate) ++ (r.clause ∖ e.literal)
                      -- which is a subclause of the successor's
                      -- tracked disjunction: its reason-side literals
                      -- (normalized, skip-filtered) are pending, and its
                      -- seed-side literals survive the mark filter.
                      have hseed : Clause.EntailedBy problem
                          constraintHolds
                          (marksNegs marks ++ learntLits learnt) := by
                        have := htrack
                        unfold Tracked pendingLits at this
                        simpa [List.flatMap_nil] using this
                      have hres : Clause.EntailedBy problem
                          constraintHolds
                          ((marksNegs marks ++ learntLits learnt).filter
                              (fun l => !litEqB l e.literal.negate)
                            ++ (r.clause.filter
                                (fun l => !litEqB l e.literal))) :=
                        resolve_step
                          (marksNegs marks ++ learntLits learnt)
                          r.clause e.literal hseed hrv
                      -- Norm-aware containment: every resolvent
                      -- literal's normalized form lives in the successor
                      -- tracked disjunction — seed-side survivors keep
                      -- their normalized selves (they already are
                      -- normalized marksNegs/learntLits members), and
                      -- reason-side survivors' normalized forms are
                      -- pending. The one degenerate corner (raw l with
                      -- l.norm = pivot but l ≠ pivot) is eval-harmless:
                      -- norm_eval makes the two witnesses
                      -- interchangeable, so the successor remains
                      -- entailed via `norm_transfer`.
                      have hsubn : ∀ l ∈ ((marksNegs marks ++
                            learntLits learnt).filter
                              (fun l => !litEqB l e.literal.negate)
                          ++ (r.clause.filter
                              (fun l => !litEqB l e.literal))),
                          ∃ l' ∈ (pendingLits [r.clause]
                              (some e.literal)
                            ++ marksNegs (marks.filter fun m =>
                              !litEqB m.literal e.literal)
                            ++ learntLits learnt),
                            l'.eval = l.eval := by
                        intro l hl
                        unfold pendingLits marksNegs learntLits
                        simp only [List.flatMap_cons, List.flatMap_nil,
                          List.append_nil, id_eq, List.mem_append]
                        rcases List.mem_append.mp hl with h | h
                        · -- seed-side survivor: kept by the pivot
                          -- filter; it is a marksNegs or learntLits
                          -- member. The successor keeps the underlying
                          -- mark m whenever m.literal differs from the
                          -- pivot's literal (else l would be the
                          -- pivot's own negation, filtered out), and
                          -- keeps the learnt side unchanged.
                          rcases List.mem_filter.mp h with ⟨hl', hfil⟩
                          rcases List.mem_append.mp hl' with hm | hle
                          · unfold marksNegs at hm
                            obtain ⟨m, hmm, hmap⟩ := List.mem_map.mp hm
                            -- l = m.literal.negate; m.literal ≠ pivot
                            have hkeep2 : (!litEqB m.literal
                                e.literal) = true := by
                              by_cases hcase :
                                litEqB m.literal e.literal
                              · exfalso
                                have hleq : m.literal = e.literal := by
                                  simpa only [litEqB, decide_eq_true_eq]
                                    using hcase
                                have hll : l = e.literal.negate := by
                                  rw [← hmap, hleq]
                                rw [hll] at hfil
                                exact absurd hfil (by
                                  simp [litEqB])
                              · simpa [litEqB] using hcase
                            refine ⟨l, Or.inl (Or.inr ?_), rfl⟩
                            have hfmem : m ∈ marks.filter
                                (fun mx => !litEqB mx.literal e.literal) :=
                              List.mem_filter.mpr ⟨hmm, hkeep2⟩
                            rw [← hmap]
                            exact List.mem_map_of_mem (a := m)
                              (f := fun (mx : TrailEntry) =>
                                mx.literal.negate) hfmem
                          · -- learnt-side: unchanged list
                            refine ⟨l, Or.inr ?_, rfl⟩
                            exact hle
                        · -- reason-side survivor: its normalized form
                          -- is pending; eval transfers via norm_eval
                          rcases List.mem_filter.mp h with ⟨hl', hfil⟩
                          refine ⟨l.norm, Or.inl (Or.inl ?_),
                            funext fun a => Literal.norm_eval l a⟩
                          refine List.mem_filter.mpr ⟨?_, ?_⟩
                          · exact List.mem_map_of_mem (a := l)
                              (f := Literal.norm) hl'
                          · -- normalized witness: l = l.norm, so the
                            -- reason-side keep-condition is the skip
                            -- condition
                            have hlnorm : l = l.norm :=
                              hrnorm e hmem r hrm l hl'
                            rw [← hlnorm]
                            exact hfil
                      exact norm_transfer hsubn hres
                    exact ih [r.clause] (some e.literal)
                      (marks.filter fun m => !litEqB m.literal e.literal)
                      learnt hbt (fun m hm => hmarks m
                        ((List.mem_filter.mp hm).1 : m ∈ marks))
                      below uip h
      | cons c cs' =>
          cases c with
          | nil =>
              rw [analyzeStep] at h
              exact ih cs' skip marks learnt htrack hmarks below uip h
          | cons q0 qs =>
              rw [analyzeStep] at h
              by_cases hskip : skipEq skip q0.norm
              · rw [if_pos hskip] at h
                -- the skip filter drops the pivot's pending copy on
                -- BOTH sides, so the tracked disjunction is unchanged
                have htrack' : Tracked problem constraintHolds
                    (qs :: cs') skip marks learnt := by
                  have heq :
                    (List.filter (fun l => !skipEq skip l)
                      (List.map Literal.norm
                        (List.flatMap id ((q0 :: qs) :: cs'))))
                      = List.filter (fun l => !skipEq skip l)
                        (List.map Literal.norm
                          (List.flatMap id (qs :: cs'))) := by
                    simp only [List.flatMap_cons, List.map_cons,
                      List.filter_cons, List.cons_append, id_eq]
                    rw [show (!skipEq skip q0.norm) = false from by
                      rw [hskip]; rfl]
                    rfl
                  unfold Tracked pendingLits at htrack ⊢
                  rw [heq] at htrack
                  exact htrack
                exact ih (qs :: cs') skip marks learnt htrack' hmarks
                  below uip h
              · rw [if_neg hskip] at h
                cases hmark : markLit trail lvl marks learnt q0.norm with
                | none => rw [hmark] at h; simp at h
                | some res =>
                    obtain ⟨marks', learnt'⟩ := res
                    rw [hmark] at h
                    -- The successor Tracked: derive by witness transfer
                    -- over markLit's shape (any-hit / fresh mark / below /
                    -- root drop), using PendingOk-style unchanged cases
                    -- plus the eval identities proved above.
                    -- markLit's four shapes transfer the tracked
                    -- disjunction; the fresh-below pair records the
                    -- UPGRADED literal q' whose eval is implied by the
                    -- dropped pending literal (orderUpgrade_weaken),
                    -- the fresh mark covers via the falsifier's
                    -- negation (norm-square identity), and the
                    -- unchanged/root-drop shapes only shrink the
                    -- pending side by literals that either already
                    -- appear on the marks/learnt side or are false at
                    -- every internal solution (RootFacts).
                    -- The five markLit shapes (already-marked /
                    -- already-learnt / fresh mark / fresh below record /
                    -- root drop) each transfer the tracked
                    -- disjunction to the successor worklist. The
                    -- statement is the conjunction the recursive call
                    -- needs: the successor `Tracked` plus marks' trail
                    -- membership. Each shape is closed through
                    -- `tracked_markDrop`: identity or monotone side
                    -- transfer, and a cover witness for the dropped
                    -- pending literal `q0.norm` (the duplicate's
                    -- negation via `falsifier_neg_true`, the record
                    -- itself, the fresh mark's negation, the record via
                    -- `orderUpgrade_weaken`, or the `RootFacts`
                    -- refutation for the root drop).
                    obtain ⟨htr', hmarks'⟩ :=
                      markLit_branch trail lvl hroot qs cs' skip marks
                        learnt q0 marks' learnt' hmark htrack hmarks
                    exact ih (qs :: cs') skip marks' learnt' htr'
                      hmarks' below uip h

end LeanFzn.Solver.LCG

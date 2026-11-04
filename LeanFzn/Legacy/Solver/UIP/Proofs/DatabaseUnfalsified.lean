/-
File: LeanFzn/Solver/UIP/Proofs/DatabaseUnfalsified.lean

Purpose (Prem2 of P2/P4 — the `hdb` premise):
  `LearningNovelty.DatabaseUnfalsified bs` states that NO stored learned
  clause is norm-trail-falsified:
      ∀ c ∈ bs.learned, ¬ FalsifiedByTrailNorm bs c.
  P4's `phaseLt_stepLearnBackjumpAssert` consumes it to exclude the
  repeated-clause case. This file settles its TRUTH status:

  * KERNEL WITNESS (this file, `databaseUnfalsified_stored_falsified_witness`):
    the statement is FALSE for arbitrary `BranchState`s whose stored
    database contains a clause falsified by their own trail — i.e. it is
    NOT a structural consequence of `BranchState`. At a DB-conflict state
    the conflict scan has found a stored clause falsified by the trail
    (that is how the scan reports a conflict), so the unqualified form
    cannot hold at every pre-jump config for exactly that reason.

  * REFINEMENT (this file, `DatabaseUnfalsifiedExcept`): the precise
    repairable form — "no stored clause OTHER THAN the recorded conflict
    clause is falsified" — with `not_jumpRepeated_of_except`: the
    repeated-case exclusion goes through under the refinement plus ONE
    named non-degeneracy side condition
    (`AnalysisDiffersFromConflict`: the analysis clause's canonical form
    differs from the recorded conflict clause's). `conflict ∉ learned`
    reduces the refinement to the original invariant
    (`databaseUnfalsified_of_except_not_mem`), and the original invariant
    trivially implies the refinement
    (`databaseUnfalsifiedExcept_of_unfalsified`), so every P4 consumer
    keeps a drop-in replacement.

  * REACHABLE DISCHARGE (§3, PROVED): since R1c's conflict routing a
    DATABASE conflict is reported as `.conflict [c]` with the stored clause
    `c` and is ANALYZED; there the unfalsifiedness claim is NOT made (the
    stored conflict clause is frame-refuted, and later stored clauses may
    be too). At a PROPAGATOR-reported analyzed site `scanDatabase` is
    `.stable`. At a reachable inhabited branch the
    stable scan REFUTES norm-falsification of every stored clause
    (`clauseRemaining_eq_nil_of_normFalsified`), so the UNQUALIFIED
    `DatabaseUnfalsified bs` holds at the analyzed site — stronger than
    the refinement, no exemption, no `AnalysisDiffersFromConflict`.

  * SIDE CONDITION WITNESS (§4): `AnalysisDiffersFromConflict` is NOT a
    theorem in general — `analysisDiffersFromConflict_refutation_witness`
    exhibits an equal-canonical-form case. It is only needed on the
    exemption route (`DatabaseUnfalsifiedExcept`); the stable-scan route
    of §3 bypasses it.

Dependencies:
  - LeanFzn.Solver.UIP.Proofs.LearningNovelty: `DatabaseUnfalsified`,
    `JumpRepeated`, `falsifiedByTrailNorm_of_canonicalClause_eq`.
  - LeanFzn.Solver.Propagation.TrailEval: `Literal.norm`, `posLe`, `negLe`.
  - LeanFzn.Solver.Propagation.ExplainedPropagation: `scanDatabase_conflict_facts`.
  - LeanFzn.Solver.UIP.Proofs.LearnedExplanation: `frame_realizes_value`.

DAG:
  Proofs.LearningNovelty + ExplainedPropagation + Proofs.LearnedExplanation
    -> Proofs.DatabaseUnfalsified
-/

import LeanFzn.Legacy.Solver.UIP.Proofs.LearningNovelty
import LeanFzn.Solver.Propagation.TrailEval
import LeanFzn.Legacy.Solver.Propagation.ExplainedPropagation
import LeanFzn.Legacy.Solver.UIP.Proofs.LearnedExplanation
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.Core

/-! ## §1 The refinement: falsification allowed only at the conflict clause -/

/-- Refined invariant: no stored clause OTHER THAN the recorded conflict
    clause is norm-trail-falsified. This is the strongest form the
    conflict-scan argument can establish (the stored conflict clause is
    itself falsified by definition of the scan). -/
def DatabaseUnfalsifiedExcept {leaf : Assignment → Bool}
    (bs : BranchState leaf) (conflict : Clause) : Prop :=
  ∀ c ∈ bs.learned, c ≠ conflict → ¬ FalsifiedByTrailNorm bs c

/-- Drop-in: the original invariant implies the refinement (any conflict
    clause may be named; it is then exempt, which loses nothing). -/
theorem databaseUnfalsifiedExcept_of_unfalsified {leaf : Assignment → Bool}
    {bs : BranchState leaf} {conflict : Clause}
    (h : DatabaseUnfalsified bs) : DatabaseUnfalsifiedExcept bs conflict :=
  fun c hc _ => h c hc

/-- If the conflict clause is NOT stored, the refinement is exactly the
    original invariant — the refinement is not a weakening along the
    hunted route. -/
theorem databaseUnfalsified_of_except_not_mem {leaf : Assignment → Bool}
    {bs : BranchState leaf} {conflict : Clause}
    (h : DatabaseUnfalsifiedExcept bs conflict) (hn : conflict ∉ bs.learned) :
    DatabaseUnfalsified bs :=
  fun c hc => h c hc (fun he => hn (he ▸ hc))

/-- The named non-degeneracy side condition for the exclusion: the
    recorded conflict clause and the analysis clause differ canonically.
    (If they were equal, the analysis would have re-derived the conflict
    clause itself, and the exemption would swallow the match.) -/
def AnalysisDiffersFromConflict (conflict : Clause) (an : ConflictAnalysis) : Prop :=
  Clause.canonicalClause conflict ≠ Clause.canonicalClause an.learned

/-- **REPEATED-CASE EXCLUSION UNDER THE REFINEMENT**: the exact analogue of
    P2's `not_jumpRepeated_of_unfalsified`, with `DatabaseUnfalsified`
    replaced by its repairable form. The stored clause whose canonical
    form matches `an.learned` is falsified by canonical transfer; the
    side condition keeps it out of the conflict-clause exemption. -/
theorem not_jumpRepeated_of_except {leaf : Assignment → Bool}
    {bs : BranchState leaf} {an : ConflictAnalysis} {conflict : Clause}
    (hdb : DatabaseUnfalsifiedExcept bs conflict)
    (hfals : FalsifiedByTrailNorm bs an.learned)
    (hside : AnalysisDiffersFromConflict conflict an) :
    ¬ JumpRepeated bs.learned an := by
  intro hrep
  obtain ⟨c, hc, hceq⟩ := List.mem_map.mp hrep
  have hne : c ≠ conflict := fun he => hside (he ▸ hceq)
  exact hdb c hc hne
    (falsifiedByTrailNorm_of_canonicalClause_eq hceq hfals)

/-- Collapsed form: under the refinement and the side condition, the jump
    classification is forced to the NEW case (the P4-shaped export). -/
theorem jumpNovelty_of_except {leaf : Assignment → Bool}
    {bs : BranchState leaf} {an : ConflictAnalysis} {conflict : Clause}
    (hdb : DatabaseUnfalsifiedExcept bs conflict)
    (hfals : FalsifiedByTrailNorm bs an.learned)
    (hside : AnalysisDiffersFromConflict conflict an) :
    JumpNovelty bs.learned an :=
  not_jumpRepeated_iff_jumpNovelty bs.learned an |>.mp
    (not_jumpRepeated_of_except hdb hfals hside)

/-! ## §2 Kernel witness: the unqualified form is false for general
branch states -/

/-- A concrete branch state: one trail entry `s0 ≤ 3` (positive `intLe`
    literal, normalization is the identity on `intLe`), and a stored
    clause consisting of its negation `¬(s0 ≤ 3)`, hence falsified by the
    trail. This is the shape the database scan produces at a conflict, so
    no structural argument can make the unqualified invariant true. -/
private def falsifiedStoreExample : BranchState (fun _ : Assignment => true) :=
  { frame := (⟨[], []⟩ : BranchFrame)
    trail := [{ literal := posLe 0 3, level := 0, reason := none }]
    level := 0
    learned := [[negLe 0 3]] }

/-- **KERNEL WITNESS**: `DatabaseUnfalsified` fails at
    `falsifiedStoreExample`; its stored clause `[¬(s0 ≤ 3)]` is falsified
    by its own trail entry. This refutes the unqualified invariant as a
    theorem of `BranchState` (reachability of such a state through the
    real conflict scan is a separate, OPEN obligation — owner S4/S5). -/
theorem databaseUnfalsified_stored_falsified_witness :
    ¬ DatabaseUnfalsified falsifiedStoreExample := by
  intro hdb
  have hf : FalsifiedByTrailNorm falsifiedStoreExample [negLe 0 3] := by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact ⟨_, List.mem_singleton_self _, rfl⟩
  exact hdb [negLe 0 3] (List.mem_singleton_self _) hf

/-- The same state satisfies the REFINED invariant when the falsified
    stored clause is named as the conflict clause (the refinement is the
    sharp repair, not vacuous). -/
theorem databaseUnfalsifiedExcept_witness :
    DatabaseUnfalsifiedExcept falsifiedStoreExample [negLe 0 3] := by
  intro c hc hne
  simp only [falsifiedStoreExample, List.mem_singleton] at hc
  exact absurd hc hne

/-! ## §3 Reachable discharge: a stable scan hides no falsified clause

`scanDatabase` reports a conflict exactly when some stored clause has
empty `clauseRemaining`, and `.stable` when no stored clause is empty in
the frame (and no singleton is productive). At a REACHABLE INHABITED
branch, norm-trail-falsification is STRONGER than frame-emptiness: every
literal whose normalized negation is recorded holds at every
frame-covered assignment (`ReachableState.agrees`), so no frame value can
satisfy it (`frame_realizes_value` reads the surviving value at a covered
assignment). Hence a stable scan refutes norm-falsification of EVERY
stored clause — the unqualified `DatabaseUnfalsified`, with no exemption
and no side condition.

Honest scope: the two premises are the standard branch-level ones. The
inhabited-frame residual is the NAMED per-state premise
`ReachableFrameInhabited` (`Proofs/LearnedExplanation.lean`), not a
universal claim; empty-domain frames are handled by PROVED frame
exclusion, not by this path. -/

/-- A stable scan never sees an empty remaining clause. -/
theorem scanDatabase_stable_clauseRemaining {original : List Clause}
    {f : BranchFrame} {db : List Clause}
    (h : scanDatabase original f db = .stable) :
    ∀ c ∈ db, clauseRemaining f c ≠ [] := by
  induction db with
  | nil => intro c hc; cases hc
  | cons d rest ih =>
      intro c hc
      cases hrem : clauseRemaining f d with
      | nil =>
          simp only [scanDatabase, hrem] at h
          cases h
      | cons l t =>
          cases t with
          | nil =>
              simp only [scanDatabase, hrem] at h
              by_cases hp : productive l f = true
              · rw [if_pos hp] at h
                cases h
              · rw [if_neg hp] at h
                rw [List.mem_cons] at hc
                rcases hc with rfl | hc
                · intro heq
                  rw [hrem] at heq
                  cases heq
                · exact ih h c hc
          | cons l2 t2 =>
              simp only [scanDatabase, hrem] at h
              rw [List.mem_cons] at hc
              rcases hc with rfl | hc
              · intro heq
                rw [hrem] at heq
                cases heq
              · exact ih h c hc

/-- **THE TRAIL/FRAME BRIDGE**: at a reachable inhabited branch, a
    norm-trail-falsified clause has EVERY literal frame-impossible, so
    its remaining clause is empty and the database scan would report a
    conflict on it. -/
theorem clauseRemaining_eq_nil_of_normFalsified {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf}
    (hreach : ReachableState leaf orig bs)
    (hinhab : ∃ a, FrameCovers bs.frame a)
    {c : Clause} (hfals : FalsifiedByTrailNorm bs c) :
    clauseRemaining bs.frame c = [] := by
  rw [clauseRemaining, List.filter_eq_nil_iff]
  intro l hl hfilter
  have htrue : literalImpossible bs.frame l = true := by
    rw [literalImpossible, List.all_eq_true]
    intro v hv
    cases hvh : l.valueHolds v with
    | false => rfl
    | true =>
        exfalso
        obtain ⟨e, he, helit⟩ := hfals l hl
        obtain ⟨a', hcov', hread⟩ := frame_realizes_value (slot := l.atom.slot) (v := v) hinhab
          ((DomainLike.mem_iff _ _).mpr (by simpa [domElems_eq_enum] using hv))
        have hev := hreach.agrees e he a' hcov'
        rw [helit, Literal.norm_eval] at hev
        have hfalse : l.eval a' = some false :=
          (Literal.eval_negate_false_iff l a').mp hev
        have htrue' : l.eval a' = some true := (valueHolds_read hread).mp hvh
        rw [hfalse] at htrue'
        exact Bool.false_ne_true (Option.some.inj htrue')
  have : (!literalImpossible bs.frame l) = false := by
    rw [htrue]
    rfl
  rw [this] at hfilter
  cases hfilter

/-- **REACHABLE DATABASE UNFALSIFIED (unqualified)**: at a reachable
    inhabited branch whose database scan is stable, NO stored clause is
    norm-trail-falsified. -/
theorem databaseUnfalsified_of_scanDatabase_stable {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf}
    (hreach : ReachableState leaf orig bs)
    (hinhab : ∃ a, FrameCovers bs.frame a)
    {original : List Clause}
    (hstable : scanDatabase original bs.frame bs.learned = .stable) :
    DatabaseUnfalsified bs :=
  fun c hc hfals =>
    scanDatabase_stable_clauseRemaining hstable c hc
      (clauseRemaining_eq_nil_of_normFalsified hreach hinhab hfals)

/-- Drop-in for the P2/P4 `hdb` premise, reachable form: under a stable
    scan the REFINEMENT holds with the conflict clause exempted for free
    (in fact the unqualified invariant holds). -/
theorem databaseUnfalsifiedExcept_of_scanDatabase_stable
    {leaf : Assignment → Bool} {orig : List Domain} {bs : BranchState leaf}
    (hreach : ReachableState leaf orig bs)
    (hinhab : ∃ a, FrameCovers bs.frame a)
    {original : List Clause}
    (hstable : scanDatabase original bs.frame bs.learned = .stable)
    (conflict : Clause) :
    DatabaseUnfalsifiedExcept bs conflict :=
  databaseUnfalsifiedExcept_of_unfalsified
    (databaseUnfalsified_of_scanDatabase_stable hreach hinhab hstable)

/-- The ANALYZED conflict shape (R1c routing): a nonempty reported clause
    list comes EITHER from `scanPropagators` (then the database scan is
    stable) OR from the database scan itself, which reports exactly the
    first stored clause with no remaining literal. -/
theorem scanDatabase_stable_or_dbConflict_of_nextPruningEvent_conflict_cons
    {original : List Clause} {props : List Propagator} {f : BranchFrame}
    {db : List Clause} {c : Clause} {rest : List Clause}
    (h : nextPruningEvent original props f db = .conflict (c :: rest)) :
    scanDatabase original f db = .stable ∨
      (scanDatabase original f db = .conflict [c] ∧ rest = [] ∧ c ∈ db ∧
        clauseRemaining f c = []) := by
  rcases nextPruningEvent_conflict_cases h with hsd | ⟨hsd, -, -⟩
  · obtain ⟨d, hd, hrem, hcs⟩ := scanDatabase_conflict_facts hsd
    injection hcs with hcd hrest
    subst hcd hrest
    exact Or.inr ⟨hsd, rfl, hd, hrem⟩
  · exact Or.inl hsd

/-- The PROPAGATOR-sourced analyzed conflict forces the database scan
    stable. RESTATED by R1c: before the conflict routing a database conflict
    reported `.conflict []`, so every analyzed (`c :: rest`) event had a
    stable database scan; now a database conflict reports its own clause,
    so the conclusion needs the explicit premise that the database scan
    did not report a conflict (`hndb`). -/
theorem scanDatabase_stable_of_nextPruningEvent_conflict_cons
    {original : List Clause} {props : List Propagator} {f : BranchFrame}
    {db : List Clause} {c : Clause} {rest : List Clause}
    (h : nextPruningEvent original props f db = .conflict (c :: rest))
    (hndb : ∀ cs, scanDatabase original f db ≠ .conflict cs) :
    scanDatabase original f db = .stable := by
  rcases scanDatabase_stable_or_dbConflict_of_nextPruningEvent_conflict_cons h with
    hsd | ⟨hsd, -⟩
  · exact hsd
  · exact absurd hsd (hndb _)

/-- **EVENT-LEVEL EXPORT**: at a reachable inhabited branch, whenever the
    closure event is an ANALYZED PROPAGATOR conflict (`c :: rest` with the
    database scan not in conflict — premise `hndb`, added by R1c), the
    refinement (in fact the unqualified invariant) holds for the reported
    clause. At a DATABASE conflict the stored conflict clause is itself
    frame-refuted and other stored clauses may be too, so no
    unfalsifiedness claim is made there. -/
theorem databaseUnfalsifiedExcept_of_nextPruningEvent_conflict_cons
    {leaf : Assignment → Bool} {orig : List Domain} {bs : BranchState leaf}
    (hreach : ReachableState leaf orig bs)
    (hinhab : ∃ a, FrameCovers bs.frame a)
    {original : List Clause} {props : List Propagator} {c : Clause}
    {rest : List Clause}
    (h : nextPruningEvent original props bs.frame bs.learned
      = .conflict (c :: rest))
    (hndb : ∀ cs, scanDatabase original bs.frame bs.learned ≠ .conflict cs) :
    DatabaseUnfalsifiedExcept bs c :=
  databaseUnfalsifiedExcept_of_scanDatabase_stable hreach hinhab
    (scanDatabase_stable_of_nextPruningEvent_conflict_cons h hndb) c

/-! ## §4 The side condition is not a theorem

The stable-scan route needs no `AnalysisDiffersFromConflict`. On the
EXEMPTION route the condition is genuine extra data: with `below = []`
the analysis clause is exactly `uip.negate :: []`, and taking the
conflict clause as that very clause makes the canonical forms equal — so
`AnalysisDiffersFromConflict conflict an` is REFUTABLE in general (a
kernel witness, not a failed proof attempt). -/

/-- **KERNEL WITNESS**: the side condition FAILS when the recorded
    conflict clause equals the analysis output (`below = []`, `uip` the
    clause literal's positive form): both canonical forms are
    `[negLe 0 3]`. Hence `AnalysisDiffersFromConflict` cannot be proved
    unconditionally; it is genuinely a side condition. -/
theorem analysisDiffersFromConflict_refutation_witness :
    ¬ AnalysisDiffersFromConflict [negLe 0 3]
      (ConflictAnalysis.ofUIP [] (posLe 0 3)) :=
  fun h => h rfl

end LeanFzn.Solver.UIP

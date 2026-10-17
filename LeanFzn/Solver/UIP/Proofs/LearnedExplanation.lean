/-
File: LeanFzn/Solver/UIP/Proofs/LearnedExplanation.lean

Purpose:
  The E1 learned-clause explanation discipline. A3's
  `domExplainedContract_of_problem` requires the per-state discipline
  `LearnedExplained` for ALL `ReachableState`s, and its `UnitLearned`
  specialization only covers unit clauses. This module replaces that
  broad premise with `LearnedProvenance` (`DomExplained.lean`), an
  invariant of ACTUAL reachable execution, and proves:

  * `recordedWith_evidence` / `recordedWith_stepChronology` — clause-unit
    explanations, normalized pivot membership and chronological
    falsifiers for MULTI-LITERAL learned clauses (the scan-facing
    obligations of `ClosureContract.pivot`/`chronology`, derived from
    provenance, never assumed);
  * preservation (`learnedProvenance_init`, `_learnGlobal`,
    `_narrow_of_members`, `_restoreFrame`, `_restoreAssert`) under
    globally entailed clause insertion, narrowing and the restoration
    operations of `RestorationCertificate` consumed by C2c;
  * `domExplainedContract_of_provenance` — the contract constructor whose
    learned half is the invariant (NOT `UnitLearned`, NOT a
    caller-supplied explanation function): the semantic content (pivot
    membership + falsifiers) is derived, only the unit-shape scope
    condition `hShape` remains, and it is C2c's restoration identity;
  * a component example with a REAL two-literal learned clause
    propagating through the `explainedDeduction` / `narrowState` API.

Dependencies:
  - LeanFzn.Solver.Propagation.DomExplained: `ClauseProvenance`, `LearnedProvenance`,
    `RecordedWith`, `PropagatorEvidence`, `UnitClauseEvidence`.
  - LeanFzn.Solver.Propagation.ExplainedPropagation: `ClosureContract`,
    `domExplainedContract`, `narrowState`, `explainedDeduction`.
  - LeanFzn.Solver.Propagation.Proofs.BranchState: `ReachableState`, `reachable_init`,
    `reachable_decide_of_second_value`, `reachable_learnGlobal`.
  - LeanFzn.Solver.Propagation.RestorationCertificate: `RestorationCertificate`,
    `restore_chronology_of_certificate`, `restoreAssert`.

DAG:
  DomExplained + ExplainedPropagation + Proofs.BranchState
    + RestorationCertificate -> Proofs.LearnedExplanation
  -> (C2c / C2a / E3 consumers). No runtime module imports this one.
-/

import LeanFzn.Solver.Propagation.DomExplained
import LeanFzn.Solver.Propagation.Proofs.BranchState
import LeanFzn.Solver.Propagation.RestorationCertificate
import LeanFzn.Solver.Propagation.BackjumpFrontier
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## The scan-facing evidence of a provenanced clause -/

/-- CLAUSE-UNIT EXPLANATIONS for multi-literal learned clauses: a clause
recorded at pivot `p` has `p` as a (normalized) member and every other
member's exact negation on the trail — the chronological falsifiers.
This is the content `ClosureContract.pivot`/`chronology` consumes; it is
DERIVED from provenance, never assumed. -/
theorem recordedWith_evidence {leaf : Assignment → Bool}
    {bs : BranchState leaf} {c : Clause} {p : Literal}
    (h : RecordedWith leaf bs c p) :
    (p ∈ c) = True ∧ (∀ q ∈ c, q ≠ p →
      ∃ e ∈ bs.trail, e.literal = q.negate) :=
  ⟨h.2.1, fun q hq hne => List.mem_map.mp (h.2.2 q hq hne)⟩

/-- The same evidence in the `StepChronology` shape, given that the
scan's unit literal is the recorded pivot up to normalization. -/
theorem recordedWith_stepChronology {leaf : Assignment → Bool}
    {bs : BranchState leaf} {c : Clause} {p : Literal}
    (h : RecordedWith leaf bs c p) {l : Literal} (hl : l.norm = p) :
    (l.norm ∈ c) = True ∧ StepChronology bs l c := by
  refine ⟨?_, ?_⟩
  · rw [hl]
    exact h.2.1
  · intro q hq hne
    have hne' : q ≠ p := by rwa [hl] at hne
    exact (recordedWith_evidence h).2 q hq hne'

/-- The database-scan form: a learned clause of a state whose database
carries `LearnedProvenance`, selected as a unit deduction at a recorded
pivot, satisfies the contract obligations. -/
theorem learnedProvenance_evidence {leaf : Assignment → Bool}
    {bs : BranchState leaf} {c : Clause} {p l : Literal}
    (_hprov : LearnedProvenance leaf bs) (_hmem : c ∈ bs.learned)
    (hp : RecordedWith leaf bs c p) (hshape : l.norm = p) :
    (l.norm ∈ c) = True ∧ StepChronology bs l c :=
  recordedWith_stepChronology hp hshape

/-! ## Provenance constructors, from the actual execution sites -/

/-- A clause recorded by an explained step gets provenance from the step's
OWN obligations (`ClosureContract.pivot`/`chronology` at the selected
event) — no caller-supplied evidence function is involved. -/
theorem clauseProvenance_of_recorded {leaf : Assignment → Bool}
    {bs : BranchState leaf} {l : Literal} {c : Clause}
    (hpivot : (l.norm ∈ c) = True) (hchron : StepChronology bs l c) :
    ClauseProvenance leaf (bs.recordImplied l { clause := c }) c :=
  ⟨l.norm, (norm_norm l).symm, hpivot, by
    intro q hq hne
    obtain ⟨e, he, heq⟩ := hchron q hq hne
    refine List.mem_map.mpr ⟨e, ?_, heq⟩
    simp only [BranchState.recordImplied]
    exact List.mem_append.mpr (Or.inl he)⟩

/-- The same constructor at a selected deduction event of a
`ClosureContract`-governed reachable state: the two obligations are the
contract's own fields for the event `nextPruningEvent` actually picked. -/
theorem clauseProvenance_of_contract {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    (hc : ClosureContract leaf orig original props) {bs : BranchState leaf}
    (hreach : ReachableState leaf orig bs) (hu : UnitDB bs.learned)
    {l : Literal} {c : Clause}
    {lr fl : Bool}
    (hev : nextPruningEvent original props bs.frame bs.learned
      = .implied l c lr fl) :
    ClauseProvenance leaf (bs.recordImplied l { clause := c }) c :=
  clauseProvenance_of_recorded (hc.pivot bs hreach hu l c lr fl hev)
    (hc.chronology bs hreach hu l c lr fl hev)

/-- Trail-extension monotonicity: provenance only depends on the trail,
and recorded falsifiers stay recorded when entries are appended. -/
theorem recordedWith_mono_trail {leaf : Assignment → Bool}
    {bs bs' : BranchState leaf} {c : Clause} {p : Literal}
    (h : RecordedWith leaf bs c p)
    (hmem : ∀ e ∈ bs.trail, e ∈ bs'.trail) :
    RecordedWith leaf bs' c p :=
  ⟨h.1, h.2.1, fun q hq hne =>
    let ⟨e, he, heq⟩ := List.mem_map.mp (h.2.2 q hq hne)
    List.mem_map.mpr ⟨e, hmem e he, heq⟩⟩

/-! ## The invariant: root witness and preservation -/

/-- Non-vacuous root witness: the empty learned database carries the
invariant trivially. -/
theorem learnedProvenance_init (leaf : Assignment → Bool) (f : BranchFrame) :
    LearnedProvenance leaf (BranchState.init f : BranchState leaf) := by
  intro c hc
  simp [BranchState.init] at hc

/-- PRESERVATION — globally entailed clause insertion: adding a clause
that carries provenance of its own insertion site keeps the invariant
(the old database's records are untouched). -/
theorem learnedProvenance_learnGlobal {leaf : Assignment → Bool}
    {bs : BranchState leaf} {c : Clause} (h : LearnedProvenance leaf bs)
    (hnew : ClauseProvenance leaf (bs.learnGlobal c) c) :
    LearnedProvenance leaf (bs.learnGlobal c) := by
  intro c' hc'
  have hc'' : c' ∈ c :: bs.learned := hc'
  rcases List.mem_cons.mp hc'' with rfl | hc'
  · exact hnew
  · obtain ⟨p, hp⟩ := h c' hc'
    exact ⟨p, recordedWith_mono_trail hp (fun e he => by
      simp only [BranchState.learnGlobal]
      exact he)⟩

/-- PRESERVATION — the narrowing step: the narrowed state's database is
the step's learned payload appended to the old one. Clauses of the old
database keep their provenance (the trail only grew); clauses newly
learned by this step are exactly the step's reason, whose provenance is
derived from the step's own pivot/chronology obligations. -/
theorem learnedProvenance_narrow_of_members {leaf : Assignment → Bool}
    {bs : BranchState leaf} {g : BranchFrame} {l : Literal} {c : Clause}
    {learned : List Clause} (h : LearnedProvenance leaf bs)
    (hpivot : (l.norm ∈ c) = True) (hchron : StepChronology bs l c)
    (hmembers : ∀ c' ∈ learned, c' = c) :
    LearnedProvenance leaf (narrowState bs g l c learned) := by
  intro c' hc'
  have hc'' : c' ∈ learned ++ bs.learned := hc'
  rcases List.mem_append.mp hc'' with hc' | hc'
  · rw [hmembers c' hc']
    exact clauseProvenance_of_recorded hpivot hchron
  · obtain ⟨p, hp⟩ := h c' hc'
    exact ⟨p, recordedWith_mono_trail hp
      (fun e he => List.mem_append.mpr (Or.inl he))⟩

/-- PRESERVATION — restoration by checkpoint trail: `restoreFrame` keeps
the database and replaces the trail by `cpTrail`; provenance survives
whenever every recorded falsifier survives (the whole-trail case is
`reachable_restoreLevel`'s identity filter; the level-filtered case is
the certificate-driven `learnedProvenance_restoreAssert` below). -/
theorem learnedProvenance_restoreFrame {leaf : Assignment → Bool}
    {bs : BranchState leaf} {f : BranchFrame} {cpTrail : List TrailEntry}
    {target : Nat} (h : LearnedProvenance leaf bs)
    (hsurv : ∀ e ∈ bs.trail, e ∈ cpTrail) :
    LearnedProvenance leaf (bs.restoreFrame f cpTrail target) := by
  intro c' hc'
  obtain ⟨p, hp⟩ := h c' hc'
  exact ⟨p, recordedWith_mono_trail hp (fun e he => by
    simp only [BranchState.restoreFrame]
    exact hsurv e he)⟩

/-- The clause inserted by the restoration-and-assertion operation gets
provenance from the certificate: its pivot is the (normalized) asserting
literal, a member by `asserting_norm_mem_of_stable`, and every other
learned literal's exact falsifier survives on `cpTrail` by the
certificate's `othersBelow` (`restore_chronology_of_certificate`).

J1 ROUND 2: the guard is the honest `NegStableAvoiding an.asserting
an.learned` (the whole-clause `NegStable` is refuted for canonical
Boolean learned literals); the lemma only ever applies it at the
non-asserting `q` its conclusion already quantifies over. -/
theorem clauseProvenance_restoreAssert_of_certificate
    {leaf : Assignment → Bool} {bs : BranchState leaf} {an : ConflictAnalysis}
    {f : BranchFrame} {cpTrail : List TrailEntry} {target : Nat}
    (hcert : RestorationCertificate leaf bs an)
    (hstable : an.asserting.norm = an.asserting)
    (hsurv : ∀ e ∈ bs.trail, e.level ≤ an.backjumpLevel → e ∈ cpTrail)
    (hneg : NegStableAvoiding an.asserting an.learned) :
    ClauseProvenance leaf (bs.restoreAssert f cpTrail target
      an.asserting an.learned) an.learned :=
  ⟨an.asserting.norm, (norm_norm an.asserting).symm,
    hcert.asserting_norm_mem_of_stable hstable, by
    intro q hq hne
    obtain ⟨e, he, heq⟩ :=
      restore_chronology_of_certificate hcert hstable hsurv hneg q hq hne
    refine List.mem_map.mpr ⟨e, ?_, heq⟩
    rw [BranchState.restoreAssert_trail]
    exact List.mem_append.mpr (Or.inl he)⟩

/-- PRESERVATION — the restore-and-assert operation C2c consumes: the
retained database keeps provenance when its falsifiers survive the
restoration. (`restoreAssert` appends only a trail entry; the clause it
asserts enters the database through the certificate-driven constructor
`clauseProvenance_restoreAssert_of_certificate` plus
`learnedProvenance_learnGlobal`.) -/
theorem learnedProvenance_restoreAssert {leaf : Assignment → Bool}
    {bs : BranchState leaf} {f : BranchFrame} {cpTrail : List TrailEntry}
    {target : Nat} {l : Literal} {c : Clause}
    (h : LearnedProvenance leaf bs)
    (hsurv : ∀ e ∈ bs.trail, e ∈ cpTrail) :
    LearnedProvenance leaf (bs.restoreAssert f cpTrail target l c) := by
  intro c' hc'
  rw [BranchState.restoreAssert_learned] at hc'
  obtain ⟨p, hp⟩ := h c' hc'
  exact ⟨p, recordedWith_mono_trail hp (by
    intro e he
    rw [BranchState.restoreAssert_trail]
    exact List.mem_append.mpr (Or.inl (hsurv e he)))⟩

/-! ## E1 continuation: the unit-shape residual (`unit_shape_pivot`)

The one scope condition `domExplainedContract_of_provenance` still takes
(`hShape`) is a THEOREM of reachable execution, not an extra discipline:
provenance plus an inhabited frame force the scan's remaining literal to
BE the recorded pivot, up to normalization. The E1 resume note's
suggested contradiction (a frame-refuted non-pivot member with its
negation recorded) is CONSISTENT and yields nothing — frame-refutation of
`q` is exactly `q.negate` holding on the whole slot. The working
argument contradicts the SURVIVING literal instead: its negation is on
the trail (so `ReachableState.agrees` falsifies it at every
frame-covered assignment), yet it is frame-possible, and every possible
value is realized by a covered assignment of an inhabited frame.
Without reachability the statement is FALSE — see
`unit_shape_pivot_needs_reachability` below. -/

/-- REALIZATION (list half): in a box with at least one complete
assignment, every value of every slot's domain is realized by some
complete assignment of the box (swap the witnessing value into the
inhabiting assignment's tail). -/
private theorem allAssigns_realize :
    ∀ (ds : List Domain) (base : Assignment), base ∈ allAssigns ds →
    ∀ (j : Nat) (v : Value), v ∈ ds.getD j [] →
      ∃ tail ∈ allAssigns ds, tail[j]? = some v := by
  intro ds
  induction ds with
  | nil =>
      intro _base _hbase j v hv
      have hnil : ([] : List Domain).getD j [] = [] := rfl
      rw [hnil] at hv
      cases hv
  | cons d rest ih =>
      intro base hbase j v hv
      cases d with
      | nil => simp [allAssigns] at hbase
      | cons x xs =>
          obtain ⟨w, hw, base', hbase', rfl⟩ :=
            (mem_allAssigns_singleton x xs rest base).mp hbase
          cases j with
          | zero =>
              rw [List.getD_cons_zero] at hv
              exact ⟨v :: base', allAssigns_cons_of_mem hv hbase', by simp⟩
          | succ j =>
              rw [List.getD_cons_succ] at hv
              obtain ⟨rest', hrest', hget⟩ := ih base' hbase' j v hv
              exact ⟨w :: rest', allAssigns_cons_of_mem hw hrest',
                by simpa using hget⟩

/-- REALIZATION (frame half): in an INHABITED frame, every value of every
slot's domain — a chosen-prefix singleton or a remaining-domain member —
is read by some frame-covered assignment. This is the bridge that turns
frame-POSSIBILITY of a literal into its TRUTH at a covered assignment;
it is what makes the unit shape sit at the recorded pivot. -/
theorem frame_realizes_value {f : BranchFrame} {slot : Nat} {v : Value}
    (hinhab : ∃ a, FrameCovers f a)
    (hv : v ∈ (Frame.domains f).getD slot []) :
    ∃ a, FrameCovers f a ∧ a[slot]? = some v := by
  obtain ⟨a₀, tail, htail, rfl⟩ := hinhab
  by_cases hslot : slot < f.2.length
  · -- a chosen-prefix slot: every covered assignment reads the pin
    have hv2 : v ∈ (fullDomains f).getD slot [] := hv
    rw [List.getD_eq_getElem?_getD, fullDomains_prefix f slot hslot] at hv2
    have hvv : v = f.2[slot] := by simpa using hv2
    exact ⟨f.2 ++ tail, ⟨tail, htail, rfl⟩, by
      rw [hvv, List.getElem?_append_left hslot]
      exact List.getElem?_eq_getElem hslot⟩
  · -- a remaining-domain slot: swap the witnessing value into the tail
    have hj : slot = f.2.length + (slot - f.2.length) := by omega
    have hrem : v ∈ f.1.getD (slot - f.2.length) [] := by
      have hv2 : v ∈ (fullDomains f).getD slot [] := hv
      rw [hj, fullDomains_getD_remaining] at hv2
      exact hv2
    obtain ⟨tail', htail', hget⟩ :=
      allAssigns_realize f.1 tail htail _ _ hrem
    exact ⟨f.2 ++ tail', ⟨tail', htail', rfl⟩, by
      rw [hj, List.getElem?_append_right (by omega)]
      simpa using hget⟩

/-- E1's residual, DISCHARGED: the unit shape of a learned clause sits at
its recorded pivot. Given reachability (the `agrees` field is the one
semantic premise), provenance of the learned database, and an inhabited
frame, the database scan's remaining literal IS the clause's recorded
pivot up to normalization.

Proof. If the recorded pivot `p` is the surviving literal `l`, both are
normalized and `l.norm = p` is immediate. Otherwise `l ≠ p`, so
`l.negate` is on the trail by provenance and `agrees` falsifies `l` at
every frame-covered assignment — but `l` survives `clauseRemaining`, so
some slot value satisfies it, and `frame_realizes_value` reads that value
at a covered assignment of the inhabited frame: `l` is both true and
false there. -/
theorem unit_shape_pivot {leaf : Assignment → Bool} {orig : List Domain}
    {bs : BranchState leaf}
    (hreach : ReachableState leaf orig bs)
    (hprov : ∀ c ∈ bs.learned, ∃ p, RecordedWith leaf bs c p)
    (hinhab : ∃ a, FrameCovers bs.frame a)
    {c : Clause} {l : Literal}
    (hmem : c ∈ bs.learned) (hrem : clauseRemaining bs.frame c = [l]) :
    ∃ p : Literal, RecordedWith leaf bs c p ∧ l.norm = p := by
  obtain ⟨p, hp⟩ := hprov c hmem
  refine ⟨p, hp, ?_⟩
  -- the surviving literal is a clause member and is frame-possible
  have hl0 : l ∈ clauseRemaining bs.frame c := by
    rw [hrem]
    exact List.mem_singleton_self _
  have hmf : l ∈ c.filter (fun x => !literalImpossible bs.frame x) := hl0
  have hlmem : l ∈ c := (List.mem_filter.mp hmf).1
  have hposs : literalImpossible bs.frame l = false := by
    have h2 := (List.mem_filter.mp hmf).2
    simpa using h2
  by_cases hpl : p = l
  · -- the pivot IS the surviving literal: normalization identifies them
    subst hpl
    exact hp.1.symm
  · -- otherwise the surviving literal's negation is recorded on the trail
    exfalso
    obtain ⟨e, he, helit⟩ := List.mem_map.mp (hp.2.2 l hlmem (Ne.symm hpl))
    -- some slot value satisfies the surviving literal
    have hexv : ∃ v ∈ (Frame.domains bs.frame).getD l.atom.slot [],
        l.valueHolds v = true := by
      rcases Classical.em (∃ v ∈ (Frame.domains bs.frame).getD
          l.atom.slot [], l.valueHolds v = true) with hpos | hcon
      · exact hpos
      · exfalso
        have hall : (((Frame.domains bs.frame).getD l.atom.slot []).all
            fun v => !l.valueHolds v) = true :=
          List.all_eq_true.mpr fun v hv => by
            cases hb : l.valueHolds v with
            | true => exact absurd ⟨v, hv, hb⟩ hcon
            | false => rfl
        have heq : literalImpossible bs.frame l
            = (((Frame.domains bs.frame).getD l.atom.slot []).all
                fun v => !l.valueHolds v) := rfl
        rw [heq, hall] at hposs
        exact Bool.noConfusion hposs
    obtain ⟨v, hvdom, hvholds⟩ := hexv
    -- realize that value at a frame-covered assignment
    obtain ⟨a', hcov', hread⟩ := frame_realizes_value hinhab hvdom
    -- the recorded entry falsifies the surviving literal everywhere covered
    have hfalse : l.eval a' = some false :=
      (Literal.eval_negate_false_iff l a').mp (by
        rw [← helit]
        exact hreach.agrees e he a' hcov')
    -- but the realized value makes it true there
    have htrue : l.eval a' = some true := (valueHolds_read hread).mp hvholds
    rw [hfalse] at htrue
    exact Bool.noConfusion (Option.some.inj htrue)

/-! ### The reachability premise is necessary

Without `ReachableState` (specifically its `agrees` field) the statement
is FALSE: a trail entry need not hold at covered assignments, so the
surviving literal can be falsified by a trail entry while being
frame-possible, and the pivot can be any frame-impossible member. -/

/-- The counterexample's leaf (no leaf solutions — irrelevant, since
neither provenance nor the unit shape consults the leaf). -/
private def ctrLeaf : Assignment → Bool := fun _ => false

/-- Slot 0 keeps both Boolean values; slot 1 admits only `false`. -/
private def ctrFrame : BranchFrame :=
  ([[.bool true, .bool false], [.bool false]], [])

/-- The pivot `p = (1 = true)` — frame-IMPOSSIBLE (slot 1 has no
`true`). -/
private def ctrP : Literal := posBool 1 true

/-- The surviving literal `l = (0 = true)` — frame-POSSIBLE. -/
private def ctrL : Literal := posBool 0 true

/-- The learned clause `[p, l]`, unit on `l`. -/
private def ctrC : Clause := [ctrP, ctrL]

/-- The trail: exactly `l.negate = ¬(0 = true)`, a decision entry. The
state is NOT reachable — `agrees` would force `¬(0 = true)` to hold at
the covered assignment `x = true` — but nothing in
provenance/inhabitedness/unit-shape rules it out. -/
private def ctrEntry : TrailEntry :=
  { literal := ctrL.negate, level := 0, reason := none }

/-- The (unreachable) branch state: the frame above, the trail above,
and the learned database `[c]`. -/
private def ctrBs : BranchState ctrLeaf :=
  { frame := ctrFrame, trail := [ctrEntry], level := 0, learned := [ctrC] }

private theorem ctr_prov : ∃ p, RecordedWith ctrLeaf ctrBs ctrC p := by
  refine ⟨ctrP, rfl, by decide, ?_⟩
  intro q hq hne
  have hq' : q ∈ [ctrP, ctrL] := hq
  rcases List.mem_cons.mp hq' with rfl | hq''
  · exact absurd rfl hne
  · have hql : q = ctrL := by simpa using hq''
    subst hql
    refine List.mem_map.mpr ⟨ctrEntry, ?_, rfl⟩
    show ctrEntry ∈ [ctrEntry]
    exact List.mem_singleton_self _

private theorem ctr_hprov :
    ∀ c ∈ ctrBs.learned, ∃ p, RecordedWith ctrLeaf ctrBs c p := by
  intro c hc
  have hcl : ctrBs.learned = [ctrC] := rfl
  rw [hcl] at hc
  have hcc : c = ctrC := List.mem_singleton.mp hc
  subst hcc
  exact ctr_prov

private theorem ctr_hinhab : ∃ a, FrameCovers ctrBs.frame a := by
  refine ⟨[Value.bool true, Value.bool false],
    ⟨[Value.bool true, Value.bool false], ?_, rfl⟩⟩
  show [Value.bool true, Value.bool false] ∈
    allAssigns ([[Value.bool true, Value.bool false], [Value.bool false]]
      : List Domain)
  exact allAssigns_cons_of_mem List.mem_cons_self
    (allAssigns_cons_of_mem List.mem_cons_self (by simp [allAssigns]))

private theorem ctr_mem : ctrC ∈ ctrBs.learned := by
  have hcl : ctrBs.learned = [ctrC] := rfl
  rw [hcl]
  exact List.mem_singleton_self _

private theorem ctr_remaining : clauseRemaining ctrBs.frame ctrC = [ctrL] := by
  decide

private theorem ctr_conclusion_false :
    ¬ ∃ p, RecordedWith ctrLeaf ctrBs ctrC p ∧ ctrL.norm = p := by
  rintro ⟨p, hp, hnorm⟩
  by_cases hcP : p = ctrP
  · subst hcP
    exact absurd hnorm (by decide)
  · have hfals := hp.2.2 ctrP (by decide) (Ne.symm hcP)
    have hmap : ctrBs.trail.map TrailEntry.literal = [ctrL.negate] := rfl
    rw [hmap] at hfals
    exact absurd hfals (by decide)

/-- THE E1 FINDING, as a refutation: the statement of
`unit_shape_pivot` WITHOUT the reachability premise is FALSE —
provenance, an inhabited frame and the unit shape hold below, yet the
surviving literal is no recorded pivot (the only candidate pivot is the
frame-impossible member, which is not it, and the surviving literal
lacks its co-member's falsifier on the trail). -/
theorem unit_shape_pivot_needs_reachability :
    ¬ ∀ (leaf : Assignment → Bool) (bs : BranchState leaf),
      (∀ c ∈ bs.learned, ∃ p, RecordedWith leaf bs c p) →
      (∃ a, FrameCovers bs.frame a) →
      ∀ (c : Clause) (l : Literal), c ∈ bs.learned →
        clauseRemaining bs.frame c = [l] →
        ∃ p, RecordedWith leaf bs c p ∧ l.norm = p := by
  intro h
  exact ctr_conclusion_false
    (h ctrLeaf ctrBs ctr_hprov ctr_hinhab ctrC ctrL ctr_mem ctr_remaining)

/-! ## The contract constructor: the broad discipline premise replaced

`domExplainedContract_of_provenance` removes `hDisc` (and `UnitLearned`):
the learned half of `ClosureContract` is built from
`UnitClauseEvidence` assembled from provenance. `hShape` names the one
scope condition that is NOT explanation content — the scan's unit
literal is SOME recorded pivot, up to normalization. It is a per-event
shape fact (C2c's restoration identity / `clauseRemaining` shrink), not
an explanation witness: the membership and the falsifiers are DERIVED by
`recordedWith_stepChronology`. -/

/-- The learned-database discipline of the supported fragment, assembled
from provenance: a unit learned clause's normalized pivot membership and
recorded falsifiers come from its insertion provenance. -/
theorem unitClauseEvidence_of_provenance {leaf : Assignment → Bool}
    {orig : List Domain}
    (hShape : ∀ (bs : BranchState leaf), ReachableState leaf orig bs →
      UnitDB bs.learned →
      ∀ (c : Clause) (l : Literal), c ∈ bs.learned →
        clauseRemaining bs.frame c = [l] →
        frameLiveB bs.frame = true →
        ∃ p : Literal, RecordedWith leaf bs c p ∧ l.norm = p) :
    UnitClauseEvidence leaf orig where
  pivot := by
    intro bs hreach hu c hc l hunit hlive
    obtain ⟨p, hp, hl⟩ := hShape bs hreach hu c l hc hunit hlive
    have := (recordedWith_evidence hp).1
    rwa [hl]
  recorded := by
    intro bs hreach hu c hc l hunit hlive q hq hne
    obtain ⟨p, hp, hl⟩ := hShape bs hreach hu c l hc hunit hlive
    obtain ⟨e, he, heq⟩ :=
      (recordedWith_evidence hp).2 q hq (by rwa [hl] at hne)
    exact List.mem_map.mpr ⟨e, he, heq⟩

/-- THE E1 CONTRACT CONSTRUCTOR: A2's complete `ClosureContract` for a
concrete problem, with the learned half supplied by the
reachable-execution invariant `LearnedProvenance` — never by
`UnitLearned` and never by a caller-supplied explanation function. The
phrasing of `hShape` is the unit-shape scope condition explained above.
`hEvidence` is A3's `propagatorEvidence_unit` for the supported fragment
(or E2's evidence for extended families). -/
theorem domExplainedContract_of_provenance {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    (hOriginal : ∀ c ∈ original, ∀ a, leaf a = true → c.SatisfiedBy a)
    (hViewed : ∀ d ∈ orig, IntViewedDomain d)
    (hSorts : DomsShapeTyped orig)
    (hLeafFits : ∀ a, leaf a = true → a.Fits orig)
    (hp : PropagationContract leaf props)
    (hEvidence : PropagatorEvidence leaf props)
    (hShape : ∀ (bs : BranchState leaf), ReachableState leaf orig bs →
      UnitDB bs.learned →
      ∀ (c : Clause) (l : Literal), c ∈ bs.learned →
        clauseRemaining bs.frame c = [l] →
        frameLiveB bs.frame = true →
        ∃ p : Literal, RecordedWith leaf bs c p ∧ l.norm = p) :
    ClosureContract leaf orig original props :=
  domExplainedContract hOriginal hViewed hSorts hLeafFits hp hEvidence
    (unitClauseEvidence_of_provenance hShape)

/-- Inhabitedness of a list of nonempty domains: the covering tail
(constructed directly, before `exists_mem_allAssigns` is available). -/
private theorem exists_mem_allAssigns' {ds : List Domain}
    (h : ∀ d ∈ ds, d ≠ []) : ∃ tail, tail ∈ allAssigns ds := by
  induction ds with
  | nil => exact ⟨[], List.mem_singleton_self _⟩
  | cons d ds ih =>
      obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil d (h d (List.mem_cons_self ..))
      obtain ⟨tail, htail⟩ := ih (fun d' hd' => h d' (List.mem_cons_of_mem _ hd'))
      exact ⟨v :: tail, allAssigns_cons_of_mem hv htail⟩

/-- THE LIVENESS BRIDGE (P1 S1′): a live frame (all remaining domains
nonempty) covers some assignment — the inhabitedness the unit-shape
producer needs, now derivable at every site where a deduction event was
SELECTED (the event gate forces liveness). -/
theorem frameLiveB_covers {f : BranchFrame} (h : frameLiveB f = true) :
    ∃ a, FrameCovers f a := by
  have hne : ∀ d ∈ f.1, d ≠ [] := by
    intro d hd hnil
    have hd' : (!d.isEmpty) = true := List.all_eq_true.mp h d hd
    rw [hnil] at hd'
    exact absurd hd' (by simp)
  obtain ⟨tail, htail⟩ := exists_mem_allAssigns' hne
  exact ⟨f.2 ++ tail, ⟨tail, htail, rfl⟩⟩

/-- The `hShape` premise of `unitClauseEvidence_of_provenance` /
`domExplainedContract_of_provenance`, DISCHARGED from the reachable
invariant and the EVENT GATE: every reachable state SELECTING a unit
learned clause as its deduction event is live (`frameLiveB`), hence
inhabited, hence `unit_shape_pivot` applies. The liveness premise is not
an extra assumption: it is what the restated `hShape` shape takes, and the
event gate (`nextPruningEvent_dbImplied_live`) supplies it at every
selection site. -/
theorem unitShape_of_provenance {leaf : Assignment → Bool} {orig : List Domain}
    (hprov : ∀ (bs : BranchState leaf), ReachableState leaf orig bs →
      LearnedProvenance leaf bs) :
    ∀ (bs : BranchState leaf), ReachableState leaf orig bs →
      UnitDB bs.learned →
      ∀ (c : Clause) (l : Literal), c ∈ bs.learned →
        clauseRemaining bs.frame c = [l] →
        frameLiveB bs.frame = true →
        ∃ p : Literal, RecordedWith leaf bs c p ∧ l.norm = p :=
  fun bs hreach _ c l hmem hrem hlive =>
    unit_shape_pivot hreach (hprov bs hreach) (frameLiveB_covers hlive) hmem hrem

/-- THE E1 CONTRACT CONSTRUCTOR WITHOUT THE SHAPE PREMISE: the same
contract as `domExplainedContract_of_provenance` with `hShape` DISCHARGED
by `unit_shape_pivot` — the two reachable-state premises it needs are
the invariant E1 already maintains (`hprov` — `LearnedProvenance`, see
the preservation lemmas above) and frame inhabitedness (`hinhab`), the
residual consumers must supply for states whose remaining box has an
empty domain. -/
theorem domExplainedContract_of_provenance' {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    (hOriginal : ∀ c ∈ original, ∀ a, leaf a = true → c.SatisfiedBy a)
    (hViewed : ∀ d ∈ orig, IntViewedDomain d)
    (hSorts : DomsShapeTyped orig)
    (hLeafFits : ∀ a, leaf a = true → a.Fits orig)
    (hp : PropagationContract leaf props)
    (hEvidence : PropagatorEvidence leaf props)
    (hprov : ∀ (bs : BranchState leaf), ReachableState leaf orig bs →
      LearnedProvenance leaf bs) :
    ClosureContract leaf orig original props :=
  domExplainedContract_of_provenance hOriginal hViewed hSorts hLeafFits hp hEvidence
    (unitShape_of_provenance hprov)

/-! ## The component example: a real two-literal learned clause

Two Boolean slots `x` (slot 0) and `y` (slot 1), leaf semantics
`x ≠ y`, the globally entailed TWO-literal clause
`¬(x = false) ∨ y = true` learned into the database, and the decided
child `x = false`. The database scan selects the clause as the unit
`y = true`; provenance gives the pivot membership and the chronological
falsifier (the decision entry), so the narrowed state is reachable,
covers every represented leaf solution and keeps the invariant — with no
`UnitLearned` and no witness function. -/

/-- The signed negation of a Boolean equality: `¬(slot = b)`. -/
private def negBool (s : Nat) (b : Bool) : Literal := ⟨.boolEq s b, false⟩

/-- Two Boolean slots, both admitting `true` and `false`. -/
private def exOrig : List Domain :=
  [[.bool true, .bool false], [.bool true, .bool false]]

/-- A Boolean slot reading with default `false`. -/
private def exValue (a : Assignment) (s : Nat) (b : Bool) : Bool :=
  match a[s]? with
  | some (.bool actual) => actual == b
  | _ => false

/-- The `x ≠ y` leaf semantics. -/
private def exLeaf : Assignment → Bool := fun a =>
  (exValue a 0 true && exValue a 1 false) ||
  (exValue a 0 false && exValue a 1 true)

/-- The globally entailed TWO-LITERAL reason clause
`¬(x = false) ∨ y = true`. -/
private def exClause : Clause := [negBool 0 false, posBool 1 true]

/-- The decision entry: literal `x = false`, recorded at level 1. -/
private def exDecision : TrailEntry :=
  { literal := posBool 0 false, level := 1, reason := none }

/-- The root state of the example. -/
private def exRoot : BranchState exLeaf := BranchState.init (exOrig, [])

/-- The DECIDED child: slot 0 pinned to `false`. -/
private def exChild : BranchState exLeaf :=
  { exRoot.decide (BranchState.pinLiteral 0 false) with
    frame := ([[.bool true, .bool false]], [.bool false]) }

/-- The example state: the child learned the entailed two-literal clause. -/
private def exState : BranchState exLeaf := exChild.learnGlobal exClause

private theorem exChild_trail : exChild.trail = [exDecision] := rfl

/-- A Boolean slot reading is `true` exactly at the named Boolean value. -/
private theorem exValue_eq_true {a : Assignment} {s : Nat} {b : Bool} :
    exValue a s b = true ↔ a[s]? = some (.bool b) := by
  cases b with
  | true =>
      cases h : a[s]? with
      | none => simp [exValue, h]
      | some val => cases val <;> simp [exValue, h]
  | false =>
      cases h : a[s]? with
      | none => simp [exValue, h]
      | some val => cases val <;> simp [exValue, h]

/-- `¬(slot = b)` holds exactly at the other Boolean value. -/
private theorem negBool_eval_true_iff {s : Nat} {b : Bool} {a : Assignment} :
    (negBool s b).eval a = some true ↔ a[s]? = some (.bool (!b)) := by
  cases b with
  | true =>
      cases h : a[s]? with
      | none => simp [negBool, Literal.eval, Atom.eval, h]
      | some val => cases val <;> simp [negBool, Literal.eval, Atom.eval, h]
  | false =>
      cases h : a[s]? with
      | none => simp [negBool, Literal.eval, Atom.eval, h]
      | some val => cases val <;> simp [negBool, Literal.eval, Atom.eval, h]

private theorem exPinLiteral_norm :
    (BranchState.pinLiteral 0 false).norm = posBool 0 false := rfl

/-- The decision is a genuine branching pin: the child is reachable. -/
private theorem exChild_reachable : ReachableState exLeaf exOrig exChild := by
  have h := reachable_decide_of_second_value (leaf := exLeaf)
    (reachable_init exLeaf exOrig)
    (d := [.bool true, .bool false]) (rest := [[.bool true, .bool false]])
    (w := .bool false) (l := BranchState.pinLiteral 0 false)
    rfl (by simp) ⟨.bool true, by simp, fun h => by cases h⟩
    (fun a => by
      show (BranchState.pinLiteral 0 false).norm.eval a = some true ↔
        a[0]? = some (.bool false)
      rw [exPinLiteral_norm]
      exact eval_posBool_iff a 0 false)
    ⟨[.bool true], by simp [allAssigns]⟩
  exact h

/-- The two-literal clause is globally entailed by `x ≠ y`. -/
private theorem exClause_entailed : LearnedEntailed exLeaf [exClause] := by
  intro c hc a ha
  rw [List.mem_singleton] at hc
  rw [hc]
  have ha' : (exValue a 0 true = true ∧ exValue a 1 false = true) ∨
      (exValue a 0 false = true ∧ exValue a 1 true = true) := by
    simpa only [exLeaf, Bool.or_eq_true, Bool.and_eq_true] using ha
  rcases ha' with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have hx : a[0]? = some (.bool true) := exValue_eq_true.mp h0
    refine ⟨negBool 0 false, by simp [exClause], ?_⟩
    exact negBool_eval_true_iff.mpr hx
  · have hy : a[1]? = some (.bool true) := exValue_eq_true.mp h1
    refine ⟨posBool 1 true, by simp [exClause], ?_⟩
    exact (eval_posBool_iff a 1 true).mpr hy

/-- The example state is reachable. -/
private theorem exState_reachable : ReachableState exLeaf exOrig exState :=
  reachable_learnGlobal exChild_reachable exClause_entailed

/-- PROVENANCE of the two-literal clause: recorded at pivot `y = true`,
and the only other member's negation `x = false` is exactly the decision
entry. -/
private theorem exRecorded : RecordedWith exLeaf exState exClause
    (posBool 1 true) := by
  refine ⟨rfl, by decide, ?_⟩
  intro q hq hne
  have hq' : q ∈ [negBool 0 false, posBool 1 true] := hq
  rcases List.mem_cons.mp hq' with rfl | hq'
  · exact List.mem_map.mpr ⟨exDecision, by
      show exDecision ∈ exChild.trail
      rw [exChild_trail]
      exact List.mem_singleton_self _, by
      simp [exDecision, negBool, Literal.negate, posBool]⟩
  · have hq'' : q = posBool 1 true := by simpa using hq'
    exact absurd hq'' hne

/-- The example clause carries the invariant's provenance. -/
private theorem exProvenance : ClauseProvenance exLeaf exState exClause :=
  ⟨posBool 1 true, exRecorded⟩

/-- The example database carries the invariant. -/
private theorem exLearnedProvenance : LearnedProvenance exLeaf exState := by
  intro c hc
  have hc' : c ∈ exClause :: exChild.learned := hc
  rcases List.mem_cons.mp hc' with rfl | hc'
  · exact exProvenance
  · simp [exChild, exRoot, BranchState.decide, BranchState.init] at hc'

/-- The selected event at the example state: the TWO-literal database
clause is unit on `y = true`. -/
private theorem ex_event : nextPruningEvent [] [] exState.frame exState.learned
    = .implied (posBool 1 true) exClause false true := rfl

/-- The deduction is selected. -/
private theorem ex_deduction :
    ∃ d : ProductiveDeduction exLeaf exState,
      explainedDeduction [] [] exState = some d :=
  ⟨_, rfl⟩

/-- The selected deduction's literal and reason are the expected ones. -/
private theorem ex_deduction_fields
    (e : ProductiveDeduction exLeaf exState)
    (he : explainedDeduction [] [] exState = some e) :
    e.literal = posBool 1 true ∧ e.reason = exClause := by
  obtain ⟨lr, fl, h2⟩ := explainedDeduction_event he
  rw [ex_event] at h2
  constructor
  · injection h2 with h1 _ _ _
    exact h1.symm
  · injection h2 with _ h2' _ _
    exact h2'.symm

/-- Every member of a selected deduction's learned payload is its reason:
the payload is the freshness-filtered singleton of the reason clause or
empty (the same inversion `Proofs/DomExplained.lean` performs, restated
here so E1 does not depend on E2's module). -/
private theorem ex_deduction_learned_members
    (e : ProductiveDeduction exLeaf exState)
    (he : explainedDeduction [] [] exState = some e) :
    ∀ c', c' ∈ e.learned → c' = e.reason := by
  have hshape : ∃ (c : Clause) (lr fl : Bool),
      nextPruningEvent [] [] exState.frame exState.learned
          = .implied e.literal c lr fl ∧
        e.reason = c ∧
        e.learned = (if lr && !(exState.learned.contains c) then [c] else []) := by
    cases hev : nextPruningEvent [] [] exState.frame exState.learned with
    | stable => simp only [explainedDeduction, hev] at he; cases he
    | conflict cs => simp only [explainedDeduction, hev] at he; cases he
    | implied l c lr fl =>
        simp only [explainedDeduction] at he
        rw [hev] at he
        by_cases ht : TrailRedundant exState.trail l = true
        · simp only [ht] at he; cases he
        · have hred : TrailRedundant exState.trail l = false := by
            cases hb : TrailRedundant exState.trail l
            · rfl
            · exact absurd hb ht
          simp only [hred] at he
          split at he
          · simp at he
          · rename_i g hf
            split at he
            · rename_i hm
              have hd := Option.some.inj he
              have hl : e.literal = l := by rw [← hd]
              have hr : e.reason = c := by rw [← hd]
              have hle : e.learned =
                  (if lr && !(exState.learned.contains c) then [c] else []) := by
                rw [← hd]
              exact ⟨c, lr, fl, by rw [hl], hr, hle⟩
            · simp at he
  obtain ⟨c, lr, fl, hev, hr, hle⟩ := hshape
  have hlrf : lr = false := by
    rw [ex_event] at hev
    injection hev with _ _ h3 _
    exact h3.symm
  intro c' hc'
  rw [hle, hlrf] at hc'
  simp at hc'

/-- BRANCH-RELATIVE pivot truth for the example: the two-literal clause's
pivot `y = true` holds at every leaf solution the decided state
represents. The trail pins `x = false`; the learned clause then forces
`y = true` (its other member `¬(x = false)` is falsified). -/
private theorem ex_pivot_branch_relative {a : Assignment}
    (_hleaf : exLeaf a = true) (hrep : exState.Represents a) :
    (posBool 1 true).norm.eval a = some true := by
  obtain ⟨-, htrail, hlearned⟩ := hrep
  have hdec : (posBool 0 false).eval a = some true := by
    have h := htrail exDecision (by
      show exDecision ∈ exChild.trail
      rw [exChild_trail]
      exact List.mem_singleton_self _)
    simpa [exDecision] using h
  have hx : a[0]? = some (.bool false) := (eval_posBool_iff a 0 false).mp hdec
  have hsat := hlearned exClause (by
    show exClause ∈ exClause :: exChild.learned
    exact List.mem_cons_self ..)
  obtain ⟨l, hl, hleval⟩ := hsat
  have hl' : l ∈ [negBool 0 false, posBool 1 true] := hl
  rcases List.mem_cons.mp hl' with rfl | hl''
  · exfalso
    have hx' : a[0]? = some (.bool true) := negBool_eval_true_iff.mp hleval
    rw [hx] at hx'
    cases hx'
  · have hl2 : l = posBool 1 true := by simpa using hl''
    rw [hl2] at hleval
    rwa [Literal.norm_eval]

/-- E1 ACCEPTANCE (component): a REAL two-literal learned clause
propagates through the explained-propagation API. The database scan
selects it as a unit deduction; its provenance (not `UnitLearned`, not a
witness function) yields the pivot membership and the chronological
falsifier; the narrowing row applies and the narrowed state remains
reachable, keeps `LearnedProvenance`, and covers every leaf solution the
example state represented. -/
example :
    -- a genuine multi-literal learned clause is selected and propagates
    (∃ d : ProductiveDeduction exLeaf exState,
      explainedDeduction [] [] exState = some d ∧
      d.reason = exClause ∧ 2 ≤ d.reason.length ∧
      d.literal = posBool 1 true) ∧
    -- its provenance is the invariant (no `UnitLearned`, no witness fn)
    LearnedProvenance exLeaf exState ∧
    (∀ d : ProductiveDeduction exLeaf exState,
      explainedDeduction [] [] exState = some d →
      ReachableState exLeaf exOrig
        (narrowState exState d.frame d.literal d.reason d.learned) ∧
      LearnedProvenance exLeaf
        (narrowState exState d.frame d.literal d.reason d.learned) ∧
      (∀ a, exLeaf a = true → exState.Represents a →
        (narrowState exState d.frame d.literal d.reason d.learned).Represents a)) := by
  obtain ⟨d, hd⟩ := ex_deduction
  have hfields := ex_deduction_fields d hd
  refine ⟨⟨d, hd, hfields.2, ?_, hfields.1⟩, exLearnedProvenance, ?_⟩
  · rw [hfields.2]
    decide
  · intro d' hd'
    have hfields' := ex_deduction_fields d' hd'
    have hev := recordedWith_stepChronology exRecorded (l := d'.literal) (by
      rw [hfields'.1]
      rfl)
    have hpivot : (d'.literal.norm ∈ d'.reason) = True := by
      rw [hfields'.2]
      simpa [hfields'.1] using hev.1
    have hchron : StepChronology exState d'.literal d'.reason := by
      intro q hq hne
      exact hev.2 q (by rwa [hfields'.2] at hq) (by
        rw [hfields'.1] at hne ⊢
        exact hne)
    have hentReason : LearnedEntailed exLeaf [d'.reason] := by
      rw [hfields'.2]
      exact exClause_entailed
    have hentLearned := explainedDeduction_learned_entailed hd' hentReason
    have hin : d'.literal.atom.slot < (fullDomains exState.frame).length := by
      rw [hfields'.1]
      decide
    refine ⟨explainedStep_narrow_reachable exState_reachable d'.filtered
        (explainedDeduction_fresh hd') hin hentLearned hentReason hpivot hchron,
      learnedProvenance_narrow_of_members exLearnedProvenance hpivot hchron
        (ex_deduction_learned_members d' hd'), ?_⟩
    intro a hleaf hrep
    exact explainedStep_narrow_coverage d'.filtered hentLearned a hleaf hrep (by
      rw [hfields'.1]
      exact ex_pivot_branch_relative hleaf hrep)

/-! ## L1 on reachable execution (PLAN L1 gate: instantiation layer)

This section instantiates the provenance-based explanation results on the
ACTUAL executable scheduler execution of R1. Division of labour, stated
explicitly:

* PROVED here — the ONE-STEP provenance components: (a) the successor
  database-shape transfer `learnedProvenance_learned_prepend` (the real jump
  step's branch is `{ restored with learned := ev.learned ++ restored.learned }`
  — `SchedulerStep.stepLearnBackjumpAssert_branch` — so the transfer is
  exactly what its preservation consumes); (b) the INSERTED-clause
  provenance of a performed plan (`clauseProvenance_execute_of_certificate`,
  `clauseProvenance_restoreNarrow_of_certificate`), consuming the
  `RestorationCertificate` fields — the clause `perform` puts into the
  global database via `learnGlobal` carries `ClauseProvenance`;
  (c) the empty-frame routing to PROVED exclusion
  (`emptyFrame_byFrame_sound`), so empty frames never reach the
  inhabited-frame lemmas.
* CONDITIONAL / DEFERRED — the FULL reachable invariant
  `ReachableLearnedProvenance` (all steps, including the
  `explainedClosure` transfer and the closure payload's own provenance):
  owner S1/S5, per PLAN.md; R1's `EvidenceProvenance`/
  `ReachableAnalysisSuccess` (PROVED) is the recorded-evidence half it
  consumes. No universal claim is made here about arbitrary
  `ReachableState`s or about unhypothesized frames.
* COORDINATOR NOTE (2026-10-09, L1): the R1 module
  `LeanFzn.Solver.UIP.Proofs.SchedulerReachable` does NOT currently build — a
  pre-existing import cycle (`SchedulerBackjump` -> `SchedulerForward`,
  `Scheduler` -> `SchedulerProgress`/`SchedulerStepO2` -> `SchedulerStep`)
  in the C2/S1-S5 cone. The named interfaces below are therefore stated
  over a BRANCH-level reachability predicate, which the R1/S1 owner
  instantiates with the driver reachability once the cycle is repaired
  (e.g. `fun bs => ∃ cfg, SchedulerReachable cfg ∧ cfg.branch = bs`).
  Nothing else in this file depends on that instantiation. -/

/-- THE NAMED INTERFACE of the L1 instantiation layer: provenance of the
ACTUAL learned database along reachable execution, at BRANCH level. Its
preservation by every real step is the S1/S5 invariant obligation (the
one-step components are proved below; the composite is conditional).
The R1 instantiation is `Reachable := fun bs => ∃ cfg, SchedulerReachable
cfg ∧ cfg.branch = bs`. -/
def ReachableLearnedProvenance (leaf : Assignment → Bool)
    (Reachable : BranchState leaf → Prop) : Prop :=
  ∀ bs : BranchState leaf, Reachable bs → LearnedProvenance leaf bs

/-- The per-state inhabited-frame residual, named so no consumer can
treat it as universal: `hinhab` must be SUPPLIED PER STATE (S1 rejects
inhabiting merely because init domains are nonempty). States whose frame
has an empty remaining domain are excluded by PROVED frame exclusion —
`emptyFrame_byFrame_sound` below (which is what
`arm_localExclude_log_sound`, `Proofs/SchedulerStep.lean:362`, consumes at
the registration sites) — not by this predicate. -/
def ReachableFrameInhabited (leaf : Assignment → Bool)
    (Reachable : BranchState leaf → Prop) : Prop :=
  ∀ bs : BranchState leaf, Reachable bs → ∃ a, FrameCovers bs.frame a

/-- EMPTY-DOMAIN SUPPORT LEMMA: a frame with an empty remaining domain
covers no complete assignment, so its leaf-exclusion is discharged by
PROVED exclusion rather than by inhabited-frame reasoning. -/
theorem allAssigns_eq_nil_of_mem_nil {ds : List Domain}
    (h : ∃ d ∈ ds, d = []) : allAssigns ds = [] := by
  induction ds with
  | nil =>
      obtain ⟨d, hd, -⟩ := h
      cases hd
  | cons d rest ih =>
      obtain ⟨e, he, heq⟩ := h
      rw [List.mem_cons] at he
      cases d with
      | nil => rfl
      | cons v vs =>
          rcases he with rfl | he
          · exact absurd heq (List.cons_ne_nil v vs)
          · simp [allAssigns, ih ⟨e, he, heq⟩]

/-- EMPTY-FRAME ROUTING: an empty-domain frame covers nothing (the
`allAssigns` of any list containing `[]` is `[]`). -/
theorem not_frameCovers_of_empty_domain {f : BranchFrame} {a : Assignment}
    (h : ∃ d ∈ f.1, d = []) : ¬ FrameCovers f a := by
  rintro ⟨tail, htail, -⟩
  rw [allAssigns_eq_nil_of_mem_nil h] at htail
  cases htail

/-- CONVERSE CONSTRUCTION: a domain list all of whose members are nonempty
admits at least one choice tail. -/
theorem exists_mem_allAssigns {ds : List Domain}
    (h : ∀ d ∈ ds, d ≠ []) : ∃ tail, tail ∈ allAssigns ds := by
  induction ds with
  | nil => exact ⟨[], by simp [allAssigns]⟩
  | cons d rest ih =>
      obtain ⟨tail, htail⟩ :=
        ih fun e he => h e (List.mem_cons_of_mem d he)
      cases hd : d with
      | nil => exact absurd hd (h d (List.mem_cons_self ..))
      | cons v vs =>
          exact ⟨v :: tail,
            allAssigns_cons_of_mem (List.mem_cons_self ..) htail⟩

/-- **THE EXACT FRAME-INHABITATION CHARACTERIZATION (B2)**: a frame covers a
complete assignment iff every one of its remaining domains is nonempty.
This is the precise content of `ReachableFrameInhabited` and the reason it
cannot be strengthened into a reachability-only premise: a reachable pending
sibling may carry an EMPTY head domain (a split whose remaining sibling
domain `vs` is `[]`, pushed by `stepDecide`), and such a frame covers
nothing — those states must take the proved local-exclusion route
(`emptyFrame_byFrame_sound`), not the inhabited-frame premises of the
closure. -/
theorem exists_frameCovers_iff {f : BranchFrame} :
    (∃ a, FrameCovers f a) ↔ ∀ d ∈ f.1, d ≠ [] := by
  constructor
  · rintro ⟨a, tail, htail, -⟩ d hd hnil
    rw [allAssigns_eq_nil_of_mem_nil ⟨d, hd, hnil⟩] at htail
    cases htail
  · rintro h
    obtain ⟨tail, htail⟩ := exists_mem_allAssigns h
    exact ⟨f.2 ++ tail, ⟨tail, htail, rfl⟩⟩

/-- **`ReachableFrameInhabited` IS UNINHABITABLE IN GENERAL (B2 evidence).**
The initialized branch state of the box `[[]]` (one slot whose domain is
empty) is `ReachableState` — `reachable_init` — and its frame covers nothing
(`exists_frameCovers_iff`). Hence the per-state inhabitedness premise of the
closure producers is FALSE on real reachable states; it cannot be
discharged, and the producers must instead take the proved local-exclusion
route on empty frames (`emptyFrame_byFrame_sound`). This kernel-checked
refutation is the reason B2 restates the unit-shape chain instead of
proving inhabitedness. -/
theorem not_reachableFrameInhabited_emptyDomain :
    ¬ ReachableFrameInhabited (fun _ : Assignment => true)
        (ReachableState (fun _ : Assignment => true) ([[]] : List Domain)) := by
  intro h
  obtain ⟨a, hcov⟩ := h (BranchState.init (([[]] : List Domain), []))
    (reachable_init (fun _ : Assignment => true) ([[]] : List Domain))
  exact not_frameCovers_of_empty_domain ⟨[], List.mem_cons_self .., rfl⟩ hcov

/-- EMPTY-FRAME ROUTING, registration form: the computable frame region
of an empty-domain frame is SOUND — this is the exclusion route
(`DeadRegion.byFrame` / `DeadRegion.byFrame_sound`, cited not re-proved)
that `arm_localExclude_log_sound` (`Proofs/SchedulerStep.lean:362`)
consumes at every local-exclusion site, so an empty frame is handled by
PROVED exclusion and never by the inhabited-frame premises
(`hinhab`) of `unitShape_of_provenance`. -/
theorem emptyFrame_byFrame_sound {leaf : Assignment → Bool} {f : BranchFrame}
    (h : ∃ d ∈ f.1, d = []) :
    DeadRegion.Sound leaf (DeadRegion.byFrame f) :=
  DeadRegion.byFrame_sound fun a _ hcov => not_frameCovers_of_empty_domain h hcov

/-- ONE-STEP DATABASE-SHAPE TRANSFER: the real jump step's branch is
`{ restored with learned := ev.learned ++ restored.learned }`
(`SchedulerStep.stepLearnBackjumpAssert`), i.e. the closure payload
prepended to the restored database. Prepending payload clauses that carry
provenance in the restored state keeps the invariant; old clauses keep
theirs (the trail is unchanged by the payload prepend). The payload half
is EXACTLY the conditional component the S1/S5 reachable invariant must
supply (closure-entailed clauses have no per-clause falsifier
provenance); the transfer itself is proved. -/
theorem learnedProvenance_learned_prepend {leaf : Assignment → Bool}
    {bs : BranchState leaf} {clauses : List Clause}
    (h : LearnedProvenance leaf bs)
    (hp : ∀ c ∈ clauses, ClauseProvenance leaf bs c) :
    LearnedProvenance leaf { bs with learned := clauses ++ bs.learned } := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨p, hp'⟩ := hp c hc
    exact ⟨p, recordedWith_mono_trail hp' fun e he => he⟩
  · obtain ⟨p, hp'⟩ := h c hc
    exact ⟨p, recordedWith_mono_trail hp' fun e he => he⟩

/-- ONE-STEP PRESERVATION, dispatch shape without the (currently
non-building) `SchedulerConfig` layer: the jump successor's database under
the proven-predecessor hypothesis and payload provenance. -/
theorem learnedProvenance_jumpSuccessor_of_payload {leaf : Assignment → Bool}
    {restored : BranchState leaf} {payload : List Clause}
    (h : LearnedProvenance leaf restored)
    (hpayload : ∀ c ∈ payload, ClauseProvenance leaf restored c) :
    LearnedProvenance leaf
      { restored with learned := payload ++ restored.learned } :=
  learnedProvenance_learned_prepend h hpayload

/-- THE INSERTED CLAUSE of a performed plan: `perform` first inserts
`pl.learned` into the global database through `learnGlobal`
(`BackjumpPlan.restoreNarrow`'s `bs.learnGlobal pl.learned`) and appends
exactly the asserting entry (`BackjumpPlan.execute`). Given the
certificate facts R1/the S3 owner establishes for the recorded analysis —
pivot membership (`asserting_norm_mem_of_stable`), normalization stability
and the honest negation-stability guard (`NegStableAvoiding`, J1 round 2),
level-filtered falsifier survival into the checkpoint trail (`othersBelow`
+ `hsurv`) — the inserted clause carries
`ClauseProvenance` in the executed (restored) state. The execution
entry's own content is irrelevant: the falsifiers live on the checkpoint
trail, which restoration reproduces exactly. -/
theorem clauseProvenance_execute_of_certificate {leaf : Assignment → Bool}
    {bs : BranchState leaf} {an : ConflictAnalysis} {pl : BackjumpPlan leaf}
    {cpTrail : List TrailEntry}
    (hcert : RestorationCertificate leaf bs an)
    (hstable : an.asserting.norm = an.asserting)
    (hneg : NegStableAvoiding an.asserting an.learned)
    (hsurv : ∀ e ∈ bs.trail, e.level ≤ an.backjumpLevel → e ∈ cpTrail)
    (htrail : pl.checkpoint.trail = cpTrail) :
    ClauseProvenance leaf (pl.execute bs) an.learned := by
  refine ⟨an.asserting, hstable.symm, ?_, ?_⟩
  · rw [← hstable]
    exact hcert.asserting_norm_mem_of_stable hstable
  · intro q hq hne
    obtain ⟨⟨e, he, hlev, hlit⟩, -⟩ := hcert.othersBelow q hq hne
    refine List.mem_map.mpr ⟨e, ?_, ?_⟩
    · rw [BackjumpPlan.execute_trail, htrail]
      exact List.mem_append.mpr (Or.inl (hsurv e he hlev))
    · rw [hneg q hq hne] at hlit
      exact hlit

/-- The same fact at `BackjumpPlan.restoreNarrow`, i.e. the state
`perform` hands to the resumed closure: narrowing only replaces the
frame, so the executed state's provenance transfers. -/
theorem clauseProvenance_restoreNarrow_of_certificate {leaf : Assignment → Bool}
    {bs : BranchState leaf} {an : ConflictAnalysis} {pl : BackjumpPlan leaf}
    {cpTrail : List TrailEntry} {g : BranchFrame} {s : BranchState leaf}
    (hcert : RestorationCertificate leaf bs an)
    (hstable : an.asserting.norm = an.asserting)
    (hneg : NegStableAvoiding an.asserting an.learned)
    (hsurv : ∀ e ∈ bs.trail, e.level ≤ an.backjumpLevel → e ∈ cpTrail)
    (htrail : pl.checkpoint.trail = cpTrail)
    (hg : filterFrame pl.asserting pl.checkpoint.frame = some g)
    (h : pl.restoreNarrow bs = some s) :
    ClauseProvenance leaf s an.learned := by
  obtain ⟨pivot, hp'⟩ :=
    clauseProvenance_execute_of_certificate hcert hstable hneg hsurv htrail
  unfold BackjumpPlan.restoreNarrow at h
  rw [hg] at h
  cases h
  exact ⟨pivot, recordedWith_mono_trail hp' fun e he => he⟩

end LeanFzn.Solver.UIP

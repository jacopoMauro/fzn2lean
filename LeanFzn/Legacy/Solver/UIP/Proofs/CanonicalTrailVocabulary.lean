/-
File: LeanFzn/Solver/UIP/Proofs/CanonicalTrailVocabulary.lean
trail vocabulary; owner C1)

Purpose: the C1 canonical-trail vocabulary. The R1 canonical resume
(`LeanFzn/Solver/UIP/BackjumpFrontier.lean`: `canonicalPinEntry`/`canonicalRetire`/
`canonicalPins`/`slotFalsifiers`/`canonicalFalsifiers`/`canonicalTrail`/
`resumePending`) rebuilds the pending alternative's trail from the frame and
the ORIGINAL box; this module proves that every entry's normalized literal
lies in the box's literal pool — the `TrailVocabulary` input that
`recordedAnalysis_learned_poolAligned` (SupportedDatabaseFacts §2) consumes
at recorded sites of the resumed branch. Also exports the
`resumePending`-shaped branch vocabulary and the recorded-analysis payload
alignment AT a canonical resume.

The only frame-side input is R2a's `PendingBacked` (read-only import; its
`full_len` gives the prefix bound and its `fit` gives the chosen-prefix
values' original provenance). Membership inversions are reused from
`Proofs/PendingBacked.lean` §3 (`mem_canonicalPins`,
`mem_canonicalFalsifiers`, `mem_zipIdx_iff'`, `literal_norm_idem`).

NO `sorry`, NO custom axiom. Registration owes the umbrella import line
`LeanFzn.Solver.UIP.Proofs.CanonicalTrailVocabulary` in `LeanFzn.Solver/LeanFzn.Solver.UIP.lean`.
-/

import LeanFzn.Legacy.Solver.UIP.Proofs.PendingBacked
import LeanFzn.Legacy.Solver.UIP.Proofs.SupportedDatabaseFacts
import LeanFzn.Legacy.Solver.UIP.Proofs.SyncVocabulary
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 The value-literal pool bridges -/

/-- **THE RETIRE-LITERAL POOL BRIDGE**: the retirement literal of such a
pin (`l.negate.norm` — the falsifier form the canonical trail stores)
normalizes into the pool. -/
theorem valueLiteral_negate_norm_mem_litPool {orig : List Domain} {s : Nat}
    {v : Value} {l : Literal} (hs : s < orig.length)
    (hv : v ∈ orig.getD s Dom.empty) (hl : valueLiteral s v = some l) :
    l.negate.norm ∈ litPool orig := by
  have hslot : orig.getD s Dom.empty = orig[s] := getD_eq_getElem_of_lt hs
  rw [hslot] at hv
  cases v with
  | bool b =>
      have hb : l = posBool s b := by simpa [valueLiteral] using hl.symm
      subst hb
      have ha : Atom.boolEq s (!b) ∈ slotAtomPool s (orig.getD s Dom.empty) := by
        rw [hslot]
        exact boolEq_mem_slotAtomPool s (orig[s]) (!b)
      show posLit (Atom.boolEq s (!b)) ∈ litPool orig
      exact posLit_mem (List.mem_append_left _
        (slotAtomPool_mem_atomPoolBase hs ha))
  | int i =>
      have hi : l = negNe s i := by simpa [valueLiteral] using hl.symm
      subst hi
      have hvE : Value.int i ∈ Dom.enum orig[s] :=
        (DomainLike.mem_iff _ _).mp hv
      have ha : Atom.intNe s i ∈ slotAtomPool s (orig.getD s Dom.empty) := by
        rw [hslot]
        exact intNe_mem_slotAtomPool
          (List.mem_filterMap.mpr ⟨Value.int i, hvE, rfl⟩)
      show posLit (Atom.intNe s i) ∈ litPool orig
      exact posLit_mem (List.mem_append_left _
        (slotAtomPool_mem_atomPoolBase hs ha))
  | setOfInt _ => simp [valueLiteral] at hl
  | array _ => simp [valueLiteral] at hl

/-! ## §2 The canonical trail's vocabulary -/

/-- A `PendingBacked` frame's decided value is an original value at its
slot (`fit` at the decided position). -/
theorem PendingBacked.decided_value_mem {orig : List Domain} {f : BranchFrame}
    (hb : PendingBacked orig f) {k : Nat} {v : Value}
    (hv : f.doms[k]?.map Dom.enum = some [v]) :
    v ∈ orig.getD k Dom.empty := by
  apply hb.fit k v
  exact mem_getD_of_enum_singleton hv

/-- The canonical pins are pooled (`PendingBacked` supplies the decided
values' provenance). -/
theorem canonicalPins_vocabulary {orig : List Domain} {f : BranchFrame}
    (hb : PendingBacked orig f) :
    TrailVocabulary orig (canonicalPins f) := by
  intro e he
  obtain ⟨p, hp, v, l, hv, hl, rfl⟩ := mem_canonicalPins.mp he
  obtain ⟨d, hd, hde⟩ := exists_dom_of_enum_singleton hv
  have hs : p.1 < orig.length := by
    have hlt : p.1 < f.doms.length := (List.getElem?_eq_some_iff.mp hd).1
    have hlen : f.doms.length = orig.length := by
      rw [← fullDomains_length (f := f)]
      exact hb.full_len
    omega
  have hmem : v ∈ orig.getD p.1 Dom.empty := hb.decided_value_mem hv
  have hthis := valueLiteral_norm_mem_litPool (orig := orig) (s := p.1)
    (v := v) (l := l) hs hmem hl
  show (l.norm).norm ∈ litPool orig
  simpa only [literal_norm_idem] using hthis

/-- The canonical falsifiers are pooled (their values come from the
ORIGINAL box, so no frame input is needed). -/
theorem canonicalFalsifiers_vocabulary {orig : List Domain} {f : BranchFrame} :
    TrailVocabulary orig (canonicalFalsifiers orig f) := by
  intro e he
  obtain ⟨p, hp, hkundec, q, hq, l, hv, hkeep, htk, rfl⟩ :=
    mem_canonicalFalsifiers.mp he
  obtain ⟨hqlt, hqval⟩ := mem_zipIdx_iff'.mp hq
  have hqmem : q.1 ∈ orig.getD p.2 Dom.empty := by
    refine (DomainLike.mem_iff _ _).mpr ?_
    rw [domElems_eq_enum]
    rw [← hqval]
    exact List.getElem_mem hqlt
  have hs : p.2 < orig.length := by
    rcases Nat.lt_or_ge p.2 orig.length with h | h
    · exact h
    · exfalso
      have hnil : orig.getD p.2 Dom.empty = Dom.empty := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
        rfl
      rw [hnil] at hqmem
      exact absurd hqmem (by simp)
  have hthis := valueLiteral_negate_norm_mem_litPool (orig := orig) (s := p.2)
    (v := q.1) (l := l) hs hqmem hv
  show (l.negate.norm).norm ∈ litPool orig
  simpa only [literal_norm_idem] using hthis

/-- **THE C1 CANONICAL RESUME TRAIL VOCABULARY**: every entry of
`canonicalTrail orig f` normalizes into the box's literal pool. -/
theorem canonicalTrail_vocabulary {orig : List Domain} {f : BranchFrame}
    (hb : PendingBacked orig f) :
    TrailVocabulary orig (canonicalTrail orig f) := by
  intro e he
  rw [canonicalTrail] at he
  rcases List.mem_append.mp he with he | he
  · exact canonicalPins_vocabulary hb e he
  · exact canonicalFalsifiers_vocabulary e he

/-- The pending resume's branch-level vocabulary (definitional). -/
theorem resumePending_branchTrailVocabulary {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf} {f : BranchFrame}
    (hb : PendingBacked orig f) :
    BranchTrailVocabulary orig (resumePending orig bs f) :=
  syncAll_trail_vocab (orig := orig) _ (P := litPool orig) (fun l hl => hl)
    (canonicalTrail_vocabulary hb)

/-- The pending resume carries the input database verbatim (`learned :=
bs.learned` is definitional), so database alignment transports through the
resume — the DATABASE half of the consume-route payload discipline. -/
theorem resumePending_databaseAligned {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf} {f : BranchFrame}
    (h : DatabaseAligned orig bs.learned) :
    DatabaseAligned orig (resumePending orig bs f).learned := by
  rw [resumePending_learned]
  exact h

/-! ## §3 The recorded-analysis jump payload at a canonical resume -/

/-- **THE C1 JUMP-PAYLOAD ALIGNMENT AT THE CANONICAL RESUME**: at a branch
resumed by `resumePending` (missing-checkpoint consume route), the recorded
analysis's learned clause is pool-aligned — `recordedAnalysis_learned_poolAligned`
fed with the canonical-trail vocabulary. This is the consume-then-record
chain C2 needs for the supported run's evidence sites. -/
theorem recordedAnalysis_learned_poolAligned_of_resumePending
    {leaf : Assignment → Bool} {orig : List Domain} {cfg : SchedulerConfig leaf}
    {bs : BranchState leaf} {f : BranchFrame} {ev : ConflictEvidence}
    {an : ConflictAnalysis}
    (hpb : PendingBacked orig f) (hb : cfg.branch = resumePending orig bs f)
    (hreach : ReachableState leaf orig cfg.branch)
    (hcfg : SchedulerReachable cfg) (hconf : cfg.conflict = some ev)
    (hana : ev.analysis = some an) :
    ∀ q ∈ an.learned, q.norm ∈ litPool orig :=
  recordedAnalysis_learned_poolAligned hb (hb ▸ hreach) hcfg hconf hana
    (resumePending_branchTrailVocabulary (bs := bs) hpb)

/-! ## C1 round-2 pointer (session 11)

The run-level producers that consume this canonical-resume bridge live in
`Proofs/TrailVocabularyProducers.lean`:
`branchTrailVocabulary_supportedRun_evidenceSites` (§5, with the recorded
recording-site premise `hrec` documented there), the closure/restoration
trail producers (§4) and the pooled emission-vocabulary producer
`unitEmissionVocabulary_proved_of_thresholds` in
`Proofs/EmissionVocabulary.lean` §3. No declaration of this file changed. -/

end LeanFzn.Solver.UIP

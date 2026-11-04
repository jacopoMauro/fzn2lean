/-
File: LeanFzn/Solver/UIP/Proofs/TrailSlotRange.lean
run-wide trail slot range along actual runs; owner C2b)

Purpose: the SLOT-RANGE half of the trail vocabulary, proved along every
actual dispatcher run with NO vocabulary/emission premise and NO branch
reachability premise, for ANY registered propagator list.

The landed `hrange` producers (`CheckpointPrefix.supportedHrange_of_premises`,
`HdeadCkpt.supportedHrange_of_site`) derived the recorded asserting literal's
slot range from the ORIGINAL-pool trail vocabulary `BranchTrailVocabulary
orig` (`hv`) plus `litPool_slot_lt`. That vocabulary is REFUTED along actual
runs of registered unit instances (`ExtendedPoolProducers`
§5 `branchTrailVocabulary_refuted_on_run`): the bound families emit their
constraint's own constant, which need not be an original-pool threshold. The
extended pool `litPoolExt orig dcs` carries those literals, but its
constraint atoms are NOT slot-ranged in general (`leConstHi 100 5` names slot
100 whatever the box), so slot range cannot come from pool membership alone.

It comes from the runtime instead: every trail entry is pushed by
  * a PRODUCTIVE filter (`ProductiveDeduction.decreases`): a literal whose
    slot is outside the remaining slots filters nothing, so a strict mass
    decrease pins the slot inside the full box
    (`filterFrame_productive_slot_lt`);
  * a decision pin `valueLiteral pre.length v` of the head remaining slot;
  * the asserting entry, whose literal is the negated first UIP — itself a
    trail literal of the predecessor (`analyzeStep_uip_on_trail`);
  * the canonical resume (`canonicalPins`/`canonicalFalsifiers`), indexed
    by the pending frame's own prefix/remaining slots.
Frame lengths are preserved by every filter/split, so the full-box length
of the branch, of every saved checkpoint and of every pending frame stays
`cfg.orig.length` (`TrailSlotInv`).

  * §1 frame-filter slot facts;
  * §2 the closure law (`explainedClosure_trailSlots`);
  * §3 the joint invariant `TrailSlotInv`, its one-step law over the real
    dispatcher (`trailSlotInv_step`) and the run law over raw reachability
    (`trailSlotInv_of_reachable`) — no `props` shape is used, so the same
    statement covers future non-unit emission families (U1b);
  * §4 the exports: the recorded asserting literal's slot range at a site
    (`recordedAsserting_slot_lt`) and its supported-run family
    (`supportedHrange_of_run`), both premise-free.

NO `sorry`, NO custom axiom.
-/

import LeanFzn.Legacy.Solver.UIP.Proofs.SupportedRun
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerStep
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerReachable
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 Frame-filter slot facts -/

/-- A strict mass decrease of `filterSlots` pins the literal's slot inside
the filtered window `[offset, offset + slots.length)`. -/
theorem filterSlots_mass_lt_slot (l : Literal) :
    ∀ (offset : Nat) (slots : List Domain),
      ((filterSlots l offset slots).map Dom.length).sum
          < (slots.map Dom.length).sum →
        offset ≤ l.atom.slot ∧ l.atom.slot < offset + slots.length
  | offset, [], h => by simp [filterSlots] at h
  | offset, d :: rest, h => by
      by_cases hs : offset = l.atom.slot
      · subst hs
        exact ⟨Nat.le_refl _, by simp⟩
      · have hrest : ((filterSlots l (offset + 1) rest).map Dom.length).sum
            < (rest.map Dom.length).sum := by
          simp only [filterSlots, if_neg hs, List.map_cons, List.sum_cons] at h
          omega
        obtain ⟨h1, h2⟩ := filterSlots_mass_lt_slot l (offset + 1) rest hrest
        simp only [List.length_cons]
        omega

/-- **PRODUCTIVE FILTERS ARE IN RANGE**: a literal whose filter strictly
decreases the frame mass names a slot of the full box. -/
theorem filterFrame_productive_slot_lt {l : Literal} {f g : BranchFrame}
    (h : filterFrame l f = some g) (hlt : Frame.mass g < Frame.mass f) :
    l.atom.slot < (fullDomains f).length := by
  unfold filterFrame at h
  split at h
  · -- out of range: the frame is unchanged, mass cannot decrease
    cases h
    exact absurd hlt (Nat.lt_irrefl _)
  · rename_i d hd
    split at h
    · cases h
    · cases h
      exact (List.getElem?_eq_some_iff.mp hd).1

/-- Filtering preserves the full-box length. -/
theorem filterFrame_fullDomains_length {l : Literal} {f g : BranchFrame}
    (h : filterFrame l f = some g) :
    (fullDomains g).length = (fullDomains f).length :=
  filterFrame_rem_length h

/-- A selected productive deduction names a slot of the full box. -/
theorem productiveDeduction_slot_lt {leaf : Assignment → Bool}
    {bs : BranchState leaf} (d : ProductiveDeduction leaf bs) :
    d.literal.atom.slot < (fullDomains bs.frame).length :=
  filterFrame_productive_slot_lt d.filtered d.decreases

/-- A selected productive deduction keeps the full-box length. -/
theorem productiveDeduction_fullDomains_length {leaf : Assignment → Bool}
    {bs : BranchState leaf} (d : ProductiveDeduction leaf bs) :
    (fullDomains d.frame).length = (fullDomains bs.frame).length :=
  filterFrame_fullDomains_length d.filtered

/-! ## §2 The trail slot predicate and the closure law -/

/-- Every trail entry names a slot below `n`. -/
def TrailSlotsBelow (n : Nat) (trail : List TrailEntry) : Prop :=
  ∀ e ∈ trail, e.literal.atom.slot < n

theorem trailSlotsBelow_nil (n : Nat) : TrailSlotsBelow n [] := by
  intro e he
  cases he

theorem trailSlotsBelow_append_entry {n : Nat} {trail : List TrailEntry}
    {e : TrailEntry} (h : TrailSlotsBelow n trail)
    (he : e.literal.atom.slot < n) : TrailSlotsBelow n (trail ++ [e]) := by
  intro e' he'
  rcases List.mem_append.mp he' with h1 | h1
  · exact h e' h1
  · rcases List.mem_singleton.mp h1
    exact he

/-- **THE CLOSURE LAW**: the explained closure keeps the full-box length and
appends only in-range entries (every appended entry is a productive
deduction's normalized literal). -/
theorem explainedClosure_trailSlots {leaf : Assignment → Bool}
    (orig : List Domain) (original : List Clause) (props : List Propagator)
    (bs : BranchState leaf)
    (hs : TrailSlotsBelow (fullDomains bs.frame).length bs.trail) :
    (fullDomains (explainedClosure orig original props bs).frame).length
        = (fullDomains bs.frame).length ∧
      TrailSlotsBelow (fullDomains bs.frame).length
        (explainedClosure orig original props bs).trail := by
  suffices hmain : ∀ (fuel : Nat) (bs : BranchState leaf),
      Frame.mass bs.frame ≤ fuel →
      TrailSlotsBelow (fullDomains bs.frame).length bs.trail →
      (fullDomains (explainedClosure orig original props bs).frame).length
          = (fullDomains bs.frame).length ∧
        TrailSlotsBelow (fullDomains bs.frame).length
          (explainedClosure orig original props bs).trail from
    hmain (Frame.mass bs.frame) bs (Nat.le_refl _) hs
  intro fuel
  induction fuel with
  | zero =>
      intro bs hle hs
      rw [explainedClosure]
      split
      · exact ⟨rfl, hs⟩
      · rename_i d _
        exfalso
        have hdec := d.decreases
        omega
  | succ fuel ih =>
      intro bs hle hs
      rw [explainedClosure]
      split
      · exact ⟨rfl, hs⟩
      · rename_i d hd
        have hlen := productiveDeduction_fullDomains_length d
        have hn : TrailSlotsBelow (fullDomains bs.frame).length
            (narrowState bs d.frame d.literal d.reason d.learned).trail := by
          show TrailSlotsBelow (fullDomains bs.frame).length (bs.trail ++
            [{ literal := d.literal.norm, level := bs.level,
               reason := some { clause := d.reason } }])
          refine trailSlotsBelow_append_entry hs ?_
          show d.literal.norm.atom.slot < _
          rw [norm_atom_slot]
          exact productiveDeduction_slot_lt d
        have hs' : TrailSlotsBelow
            (fullDomains (stepNarrowSync orig bs d).frame).length
            (stepNarrowSync orig bs d).trail := by
          rw [stepNarrowSync_frame, hlen]
          exact syncSlot_trail_prop orig _ d.literal.atom.slot
            (Q := fun l => l.atom.slot < (fullDomains bs.frame).length)
            (fun lit hlit => by
              show lit.norm.atom.slot < _
              rw [norm_atom_slot, syncCands_slot lit hlit]
              exact productiveDeduction_slot_lt d) hn
        have hdec := d.decreases
        have hle' : Frame.mass (stepNarrowSync orig bs d).frame ≤ fuel := by
          simp only [stepNarrowSync_frame]
          omega
        obtain ⟨h1, h2⟩ := ih _ hle' hs'
        rw [stepNarrowSync_frame, hlen] at h1 h2
        exact ⟨h1, h2⟩

/-! ## §3 The joint invariant -/

/-- **THE RUN-WIDE SLOT INVARIANT**: the full-box length of the branch, of
every saved checkpoint and of every pending frame is the box length, and
every branch/checkpoint trail entry names a slot below it. -/
structure TrailSlotInv {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) : Prop where
  frame : (fullDomains cfg.branch.frame).length = cfg.orig.length
  branch : TrailSlotsBelow cfg.orig.length cfg.branch.trail
  checkpoints : ∀ cp ∈ cfg.checkpoints,
    (fullDomains cp.frame).length = cfg.orig.length ∧
      TrailSlotsBelow cfg.orig.length cp.trail
  pending : ∀ f ∈ cfg.pending, (fullDomains f).length = cfg.orig.length

/-- The root configuration satisfies the invariant. -/
theorem trailSlotInv_init {prio : List Nat} {actBump : Bool} {leaf : Assignment → Bool} (orig : List Domain)
    (original : List Clause) (props : List Propagator) :
    TrailSlotInv (SchedulerConfig.init (leaf := leaf) orig original props prio actBump) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (fullDomains (⟨orig, []⟩ : BranchFrame)).length = orig.length
    simp [fullDomains, Frame.domains]
  · intro e he
    simp [SchedulerConfig.init, BranchState.init] at he
  · intro cp hcp
    simp only [SchedulerConfig.init, List.mem_singleton] at hcp
    subst hcp
    refine ⟨by show (fullDomains (⟨orig, []⟩ : BranchFrame)).length = orig.length
               simp [fullDomains, Frame.domains], ?_⟩
    intro e he
    simp [rootCheckpoint] at he
  · intro f hf
    simp [SchedulerConfig.init] at hf

/-- **THE RECORDED ASSERTING LITERAL IS IN RANGE (site form)**: at a
reachable recorded-evidence site whose trail is slot-ranged below `n`, the
asserting literal names a slot below `n` — it is the negated first UIP, a
trail literal of the site. -/
theorem recordedAsserting_slot_lt {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {ev : ConflictEvidence} {an : ConflictAnalysis}
    {n : Nat} (hreach : SchedulerReachable cfg)
    (hslots : TrailSlotsBelow n cfg.branch.trail)
    (hconf : cfg.conflict = some ev) (hana : ev.analysis = some an) :
    an.asserting.atom.slot < n := by
  obtain ⟨below, uip, hrun, hcanon⟩ :=
    reachable_analysis_success leaf cfg ev an hreach hconf hana
  have hass : an.asserting = (uip.negate).norm := by
    rw [hcanon, ConflictAnalysis.normalized_asserting,
      ConflictAnalysis.ofUIP_asserting]
  obtain ⟨m, hm, hmlit, -⟩ :=
    analyzeAtAllowance_uip_on_trail hrun
  rw [hass, literal_negate_norm_atom_slot, ← hmlit]
  exact hslots m hm

/-- The canonical resume trail of a frame is slot-ranged by the frame's
full-box length. -/
theorem canonicalTrail_slots (orig : List Domain) (f : BranchFrame) :
    TrailSlotsBelow (fullDomains f).length (canonicalTrail orig f) := by
  intro e he
  have hlen : (fullDomains f).length = f.doms.length := fullDomains_length f
  rw [hlen]
  rcases List.mem_append.mp he with hp | hf
  · -- a canonical pin
    simp only [canonicalPins, List.mem_filterMap] at hp
    obtain ⟨⟨slot, idx⟩, hmem, hpin⟩ := hp
    split at hpin
    · -- the slot's domain is a singleton singleton; never `none` here
      rename_i d hd
      split at hpin
      · rename_i v hv
        have hslot : slot < f.doms.length := (List.getElem?_eq_some_iff.mp hd).1
        unfold canonicalPinEntryAt at hpin
        rcases Option.map_eq_some_iff.mp hpin with ⟨l, hl, rfl⟩
        have := valueLiteral_atom_slot hl
        simp only [norm_atom_slot]
        omega
      · cases hpin
    · cases hpin
  · -- a remaining-slot falsifier
    simp only [canonicalFalsifiers, List.mem_flatten, List.mem_filterMap] at hf
    obtain ⟨tl, ⟨⟨dom, i⟩, hmem, hsome⟩, he⟩ := hf
    have hi : i < f.doms.length := by
      have := List.mem_zipIdx hmem
      simpa using this.2.1
    split at hsome
    · cases hsome
    · rename_i hnotin
      injection hsome with htl
      subst htl
      simp only [slotFalsifiers, List.mem_filterMap] at he
      obtain ⟨⟨w, j⟩, -, hent⟩ := he
      split at hent
      · cases hent
      · rename_i l hl
        split at hent
        · cases hent
        · split at hent
          · cases hent
          · unfold canonicalRetire at hent
            rcases Option.map_eq_some_iff.mp hent with ⟨l', hl', rfl⟩
            have h1 := valueLiteral_atom_slot hl'
            simp only [literal_negate_norm_atom_slot]
            omega

/-- **THE JUMP LAW**: a successful `perform` from a slot-ranged checkpoint
with an in-range asserting literal yields a slot-ranged branch of the same
full-box length. -/
theorem perform_trailSlots {leaf : Assignment → Bool} {n : Nat}
    {original : List Clause} {props : List Propagator}
    {p : BackjumpPlan leaf} {bs restored : BranchState leaf}
    (hlen : (fullDomains p.checkpoint.frame).length = n)
    (hcp : TrailSlotsBelow n p.checkpoint.trail)
    (hass : p.asserting.atom.slot < n)
    (hperf : p.perform bs orig original props = some restored) :
    (fullDomains restored.frame).length = n ∧
      TrailSlotsBelow n restored.trail := by
  unfold BackjumpPlan.perform at hperf
  cases hr : p.restoreNarrow bs with
  | none =>
      simp only [hr, Option.map_none] at hperf
      cases hperf
  | some s =>
      simp only [hr, Option.map_some, Option.some.injEq] at hperf
      rw [← hperf]
      unfold BackjumpPlan.restoreNarrow at hr
      split at hr
      · cases hr
      · rename_i g hg
        cases hr
        have hglen : (fullDomains g).length = n :=
          (filterFrame_fullDomains_length hg).trans hlen
        have hs : TrailSlotsBelow
            (fullDomains ((p.execute (bs.learnGlobal p.learned)).narrowFrame g).frame).length
            ((p.execute (bs.learnGlobal p.learned)).narrowFrame g).trail := by
          show TrailSlotsBelow (fullDomains g).length
            (p.execute (bs.learnGlobal p.learned)).trail
          rw [BackjumpPlan.execute_trail, hglen]
          rcases p.assertExtra_cases with hx | hx
          · rw [hx, List.append_nil]; exact hcp
          · rw [hx]
            refine trailSlotsBelow_append_entry hcp ?_
            show p.asserting.norm.atom.slot < n
            rw [norm_atom_slot]
            exact hass
        have hs2 : TrailSlotsBelow
            (fullDomains (syncAll orig
              ((p.execute (bs.learnGlobal p.learned)).narrowFrame g)).frame).length
            (syncAll orig ((p.execute (bs.learnGlobal p.learned)).narrowFrame g)).trail := by
          rw [syncAll_frame]
          refine syncAll_trail_prop orig _
            (Q := fun l => l.atom.slot < (fullDomains
              ((p.execute (bs.learnGlobal p.learned)).narrowFrame g).frame).length)
            (fun i hi lit hlit => ?_) hs
          show lit.norm.atom.slot < _
          rw [norm_atom_slot, syncCands_slot lit hlit]
          have := fullDomains_length
            ((p.execute (bs.learnGlobal p.learned)).narrowFrame g).frame
          omega
        obtain ⟨h1, h2⟩ := explainedClosure_trailSlots orig original props _ hs2
        rw [syncAll_frame] at h1 h2
        have hf : ((p.execute (bs.learnGlobal p.learned)).narrowFrame g).frame = g := rfl
        rw [hf, hglen] at h1 h2
        exact ⟨h1, h2⟩

/-- The shape of a successful split: the selected slot `k` holds the
pinned head `v :: vs` and its pin literal is `l`. -/
theorem splitData_shape {f : BranchFrame} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain} {σ : List Nat} (h : splitData f σ = some (l, k, v, vs)) :
    f.doms[k]?.map Dom.enum = some (v :: vs.enum) ∧ valueLiteral k v = some l :=
  splitData_spec h

/-- **THE ONE-STEP LAW** over the real dispatcher (every arm). -/
theorem trailSlotInv_step {leaf : Assignment → Bool}
    {cfg cfg' : SchedulerConfig leaf}
    (hinv : TrailSlotInv cfg) (hreach : SchedulerReachable cfg)
    (hsucc : (schedulerNext cfg).successor = some cfg') :
    TrailSlotInv cfg' := by
  rcases C2d.schedulerNext_cases cfg with
    ⟨ev, hc, _hsj⟩ | ⟨hconf, hdead, hsj⟩ | ⟨hconf, hact, hrest⟩
  · cases ha : ev.analysis with
    | none =>
        rw [C2d.schedulerNext_eq_backjump_none_analysis hc ha] at hsucc
        rw [successor_chronologicalFallback] at hsucc
        cases hsucc
        exact ⟨hinv.frame, hinv.branch, hinv.checkpoints, hinv.pending⟩
    | some an =>
        cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
        | none =>
            rw [C2d.schedulerNext_eq_backjump_no_checkpoint hc ha hcp] at hsucc
            rw [successor_chronologicalFallback] at hsucc
            cases hsucc
            exact ⟨hinv.frame, hinv.branch, hinv.checkpoints, hinv.pending⟩
        | some cp =>
            cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                an.learned).perform cfg.branch cfg.orig cfg.original cfg.props with
            | none =>
                rw [C2d.schedulerNext_eq_backjump_perform_none hc ha hcp hp] at hsucc
                rw [successor_localExclude] at hsucc
                cases hsucc
                exact ⟨hinv.frame, hinv.branch, hinv.checkpoints, hinv.pending⟩
            | some restored =>
                rw [C2d.schedulerNext_eq_backjump_jump hc ha hcp hp] at hsucc
                rw [successor_learnBackjumpAssert] at hsucc
                cases hsucc
                have hcpI := hinv.checkpoints cp (checkpointAt_mem hcp)
                have hass := recordedAsserting_slot_lt hreach hinv.branch hc ha
                obtain ⟨h1, h2⟩ := perform_trailSlots
                  (p := BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
                  hcpI.1 hcpI.2 hass hp
                refine ⟨h1, h2, ?_, hinv.pending⟩
                intro cp' hcp'
                rw [stepLearnBackjumpAssert_checkpoints (cfg := cfg)
                  (p := BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                    an.learned) (ev := ev) (restored := restored)] at hcp'
                exact hinv.checkpoints cp' (List.mem_filter.mp hcp').1
  · rw [hsj] at hsucc
    cases hcons : stepConsume cfg with
    | none =>
        simp only [consumeStep, hcons] at hsucc
        cases hsucc
    | some next =>
        simp only [consumeStep, hcons] at hsucc
        rw [successor_chronologicalFallback] at hsucc
        cases hsucc
        cases hp : cfg.pending with
        | nil =>
            rw [(stepConsume_eq_none_iff (cfg := cfg)).mpr hp] at hcons
            cases hcons
        | cons f rest =>
            unfold LeanFzn.Solver.UIP.stepConsume at hcons
            rw [hp] at hcons
            simp only [Option.some.injEq] at hcons
            subst hcons
            have hf : (fullDomains f).length = cfg.orig.length :=
              hinv.pending f (by rw [hp]; exact List.mem_cons_self ..)
            refine ⟨by rw [resumePending_frame]; exact hf, ?_, ?_, ?_⟩
            · have hbase : TrailSlotsBelow cfg.orig.length (canonicalTrail cfg.orig f) := by
                rw [← hf]
                exact canonicalTrail_slots cfg.orig f
              refine syncAll_trail_prop cfg.orig _ (Q := fun l => l.atom.slot < cfg.orig.length)
                (fun i hi lit hlit => ?_) hbase
              show lit.norm.atom.slot < _
              rw [norm_atom_slot, syncCands_slot lit hlit]
              have := fullDomains_length f
              have hi' : i < f.doms.length := hi
              show i < cfg.orig.length
              omega
            · intro cp hcp'
              cases hcp'
            · intro g hg
              exact hinv.pending g (by rw [hp]; exact List.mem_cons_of_mem _ hg)
  · rcases hrest with
      ⟨d, hd, hsj⟩ | ⟨bs, ht, hsj⟩ | ⟨bs, cs, learned, ht, hsj⟩ |
      ⟨bs, lit, reason, learned, ht, hsj⟩
    · rw [hsj] at hsucc
      rw [successor_propagate] at hsucc
      cases hsucc
      have hlen := productiveDeduction_fullDomains_length d
      have hslot : d.literal.atom.slot < cfg.orig.length := by
        rw [← hinv.frame]; exact productiveDeduction_slot_lt d
      have hnarrow : TrailSlotsBelow cfg.orig.length
          (narrowState cfg.branch d.frame d.literal d.reason d.learned).trail := by
        show TrailSlotsBelow cfg.orig.length (cfg.branch.trail ++
          [{ literal := d.literal.norm, level := cfg.branch.level,
             reason := some { clause := d.reason } }])
        refine trailSlotsBelow_append_entry hinv.branch ?_
        show d.literal.norm.atom.slot < _
        rw [norm_atom_slot]
        exact hslot
      refine ⟨by rw [stepPropagate_branch_frame]; exact hlen.trans hinv.frame, ?_,
        hinv.checkpoints, hinv.pending⟩
      exact syncSlot_trail_prop cfg.orig _ d.literal.atom.slot
        (Q := fun l => l.atom.slot < cfg.orig.length)
        (fun lit hlit => by
          show lit.norm.atom.slot < _
          rw [norm_atom_slot, syncCands_slot lit hlit]
          exact hslot) hnarrow
    · rw [hsj] at hsucc
      unfold stableStepGuarded at hsucc
      cases hl : leafWitness leaf cfg with
      | some w =>
          simp only [hl, successor_sat] at hsucc
          cases hsucc
      | none =>
          cases hs : splitData cfg.branch.frame cfg.prio with
          | some p =>
              obtain ⟨l, k, v, vs⟩ := p
              obtain ⟨hdom, hvl⟩ := splitData_shape hs
              have hfl := hinv.frame
              have hpinLen : (fullDomains (cfg.branch.frame.pin k v)).length
                  = (fullDomains cfg.branch.frame).length := by
                rw [fullDomains, Frame.domains, BranchFrame.pin_doms, List.length_set,
                  ← fullDomains_length]
              have hklt : k < cfg.orig.length := by
                obtain ⟨dk, hdk, -⟩ := exists_dom_of_enum_cons hdom
                rw [← hfl, fullDomains_length]
                exact (List.getElem?_eq_some_iff.mp hdk).1
              simp only [hl, hs] at hsucc
              split at hsucc
              · rw [successor_decide] at hsucc
                cases hsucc
                refine ⟨?_, hinv.branch, hinv.checkpoints, hinv.pending⟩
                show (fullDomains (cfg.branch.frame.pin k v)).length = cfg.orig.length
                rw [hpinLen, hfl]
              · rw [successor_decide] at hsucc
                cases hsucc
                refine ⟨?_, ?_, ?_, ?_⟩
                · show (fullDomains (cfg.branch.frame.pin k v)).length = cfg.orig.length
                  rw [hpinLen, hfl]
                · show TrailSlotsBelow cfg.orig.length (cfg.branch.decide l).trail
                  simp only [BranchState.decide]
                  refine trailSlotsBelow_append_entry hinv.branch ?_
                  show l.norm.atom.slot < _
                  rw [norm_atom_slot, valueLiteral_atom_slot hvl]
                  exact hklt
                · intro cp hcp'
                  have hck : (stepDecide cfg k v vs l).checkpoints
                      = DecisionCheckpoint.ofBranch cfg.branch :: cfg.checkpoints := rfl
                  rw [hck] at hcp'
                  rcases List.mem_cons.mp hcp' with rfl | hcp'
                  · exact ⟨hfl, hinv.branch⟩
                  · exact hinv.checkpoints cp hcp'
                · intro g hg
                  have hpd : (stepDecide cfg k v vs l).pending
                      = cfg.branch.frame.retire k vs :: cfg.pending := rfl
                  rw [hpd] at hg
                  rcases List.mem_cons.mp hg with rfl | hg
                  · show (fullDomains (cfg.branch.frame.retire k vs)).length
                      = cfg.orig.length
                    rw [fullDomains, Frame.domains, BranchFrame.retire_doms,
                      List.length_set, ← fullDomains_length]
                    exact hfl
                  · exact hinv.pending g hg
          | none =>
              simp only [hl, hs] at hsucc
              rw [successor_localExclude] at hsucc
              cases hsucc
              exact ⟨hinv.frame, hinv.branch, hinv.checkpoints, hinv.pending⟩
    · rw [hsj] at hsucc
      cases cs with
      | nil =>
          simp only [conflictStep] at hsucc
          rw [successor_localExclude] at hsucc
          cases hsucc
          exact ⟨hinv.frame, hinv.branch, hinv.checkpoints, hinv.pending⟩
      | cons c0 rest =>
          by_cases hlevel : cfg.branch.level = 0
          · simp only [conflictStep, if_pos hlevel, successor_unsat] at hsucc
            cases hsucc
          · simp only [conflictStep, if_neg hlevel] at hsucc
            rw [successor_analyzeConflict] at hsucc
            cases hsucc
            exact ⟨hinv.frame, hinv.branch, hinv.checkpoints, hinv.pending⟩
    · rw [hsj] at hsucc
      rw [successor_localExclude] at hsucc
      cases hsucc
      exact ⟨hinv.frame, hinv.branch, hinv.checkpoints, hinv.pending⟩

/-- **THE RUN LAW (raw reachability, any propagators)**. -/
theorem trailSlotInv_of_reachable {leaf : Assignment → Bool} :
    ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg → TrailSlotInv cfg := by
  intro cfg h
  induction h with
  | init orig original props => exact trailSlotInv_init orig original props
  | step hnext hs hpre ih =>
      subst hnext
      exact trailSlotInv_step ih hpre hs

/-! ## §4 The exports -/

/-- **THE ACTUAL-RUN TRAIL SLOT RANGE**: every trail entry of every
supported configuration names a slot of the box. Premise-free. -/
theorem trailSlots_of_supportedRun {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {cfg : SchedulerConfig leaf} (hreach : SupportedReach orig original props cfg) :
    TrailSlotsBelow orig.length cfg.branch.trail := by
  have h := (trailSlotInv_of_reachable hreach.reachable).branch
  rwa [SupportedReach.orig_eq hreach] at h

/-- **THE PREMISE-FREE `hrange` FAMILY**: at every supported recorded
site the asserting literal names a slot of the box. Replaces
`supportedHrange_of_premises` (which took the refuted original-pool `hv`). -/
theorem supportedHrange_of_run {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator} :
    ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an → an.asserting.atom.slot < orig.length :=
  fun hreach hconf hana =>
    recordedAsserting_slot_lt hreach.reachable (trailSlots_of_supportedRun hreach)
      hconf hana

end LeanFzn.Solver.UIP

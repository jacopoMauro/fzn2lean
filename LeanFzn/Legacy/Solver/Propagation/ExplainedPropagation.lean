/-
File: LeanFzn/Solver/Propagation/ExplainedPropagation.lean

Purpose:
  Produce a chronological, explanation-complete trail alongside the
  active driver's finite-domain propagation. The module wraps the
  existing `propagationClosure` event stream (`Pruning.lean`) and, for
  every domain narrowing it performs, records the corresponding
  normalized literal on a `BranchState` trail with its entailed
  reason, maintaining the P1.A contracts:

  * root facts come from the original domains (level 0, no reason);
  * decisions are recorded by the driver at fresh levels;
  * every successful CP/clause deduction is recorded with its
    normalized literal, decision level and entailed reason;
  * every non-pivot reason literal has an earlier falsifier on the
    trail (the chronology premise of `recordImplied_wellFormed`);
  * finite progress: the trail only grows when the frame's domain
    mass strictly decreases, so the existing `Frame.mass` measure of
    `propagationClosure` bounds trail additions too (no separate
    fuel).

Dependencies:
  - LeanFzn.Solver.Propagation.BranchState (P1.A): the frozen state/transition
    vocabulary and its contracts.
  - LeanFzn.Solver.Propagation.Pruning: `PruningEvent`, `nextPruningEvent`,
    `filterFrame`, `frameViewedB`, `PropagationContract`.
  - LeanFzn.Solver.Propagation.FrameFilter: `filterFrame_preserves`,
    `filterFrame_cost_le` (imported through Pruning).

DAG:
  BranchState + Pruning -> ExplainedPropagation
  -> ConflictResolution (P1.C) -> BackjumpFrontier (P1.D).
-/

import LeanFzn.Legacy.Solver.Propagation.BranchState
import LeanFzn.Legacy.Solver.Propagation.Pruning
import LeanFzn.Solver.Propagation.Propagate
import LeanFzn.Legacy.Solver.Propagation.Proofs.BranchState
import LeanFzn.Solver.Propagation.Proofs.Engine
import LeanFzn.Legacy.Solver.Propagation.LcgAnalyzer
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation


open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-! ## The explained refinement record -/

/-- The output of one explained propagation step: the refined frame
(as `propagationClosure` would produce it), the extended branch
state, and the clauses freshly learned at this step. -/
structure ExplainedRefinement (leaf : Assignment → Bool) where
  /-- Refined frame (`none` = the branch is excluded). -/
  frame : Option BranchFrame
  /-- Branch state with the trail extended by this step's deductions. -/
  state : BranchState leaf
  /-- Clauses freshly learned (globally entailed). -/
  learned : List Clause := []
  deriving Repr

/-! ## Reason construction from pruning events -/

/-- The reason clause attached to a recorded deduction. For a
clause-driven unit, the reason is the clause itself (its non-pivot
literals are exactly the falsified remainder). For a propagator
deduction, the reason is the propagator's explanation clause. -/
def reasonOfEvent : PruningEvent → Option Reason
  | .implied _ c _ _ => some { clause := c }
  | _ => none

/-! ## Chronology evidence for clause reasons -/

/-- For a clause-unit deduction on frame `f` with unit literal `l`:
every other clause literal is impossible in the refined frame's
domains, i.e. its negation was justified by the narrowing that
produced the frame. The trail-side chronology premise is supplied by
`clauseUnit_falsifiers` below: each non-pivot literal of the reason
clause is falsified by an earlier trail entry, because the trail
records exactly the narrowing literals that removed those values. -/
def clauseUnitSideLiterals (c : Clause) (l : Literal) : Clause :=
  c.filter fun q => q != l

/-! ## The explained propagation step -/

/-- One propagation event applied to both the frame and the branch
state. The frame transition is exactly `filterFrame l f` (the active
driver's own narrowing); the trail transition is
`BranchState.recordImplied` with the event's reason clause. -/
def applyEvent (bs : BranchState leaf) (f : BranchFrame)
    (e : PruningEvent) : ExplainedRefinement leaf :=
  match e with
  | .stable => { frame := some f, state := bs }
  | .conflict cs =>
      { frame := none, state := bs,
        learned := cs.filter fun c => !(bs.learned.contains c) }
  | .implied l c learnReason fromLearned =>
      let refined := filterFrame l f
      let learned := if learnReason && !(bs.learned.contains c) then [c] else []
      match refined with
      | none => { frame := none, state := bs, learned }
      | some g =>
          if Frame.mass g < Frame.mass f then
            { frame := some g,
              state := bs.recordImplied l { clause := c },
              learned }
          else { frame := some f, state := bs, learned }

/-! ## Frame/trail consistency

The full-box projection and the frame/trail bridge now live in the A1
layer (`Proofs/BranchState.lean`): `fullDomains`, `fullDomains_prefix`,
`fullDomains_remaining`, `fullDomains_length`, `TrailAgreesFrame`,
`Frame.domains_subsets`, `PrefixForced`, `NarrowingComplete` and the
bridge `frame_covers_of_trail`. This module consumes them rather than
defining a second projection. -/

/-! ## Root facts from the original domains -/

/-- The root facts of a single slot: `s ≤ max` and `¬(s ≤ min−1)` when
the domain has an integer view boundary, and nothing otherwise. -/
def domainRootFacts (slot : Nat) (d : Domain) : List TrailEntry :=
  match domMinI d, domMaxI d with
  | some mn, some mx =>
      if mn ≤ mx then
        [{ literal := posLe slot mx, level := 0, reason := none },
         { literal := negLe slot (mn - 1), level := 0, reason := none }]
      else []
  | _, _ => []

/-- The root-level trail for a frame: the order-encoding bounds of the
original domains, one group per slot. Slot `s` contributes `s ≤ max`
and `¬(s ≤ min−1)` when it has an integer view; slots without an
integer view contribute nothing. These facts hold at every original
solution because every solution fits the original domains. -/
def rootFactsOfDomains (domains : List Domain) : List TrailEntry :=
  (domains.zipIdx).flatMap fun (d, s) => domainRootFacts s d

/-- Membership characterization of `rootFactsOfDomains`: an entry is a
root fact exactly when it belongs to the group of a slot in range. -/
theorem mem_rootFactsOfDomains {domains : List Domain} {e : TrailEntry} :
    e ∈ rootFactsOfDomains domains ↔
      ∃ (d : Domain) (s : Nat), (d, s) ∈ domains.zipIdx ∧
        e ∈ domainRootFacts s d := by
  simp only [rootFactsOfDomains, List.mem_flatMap]
  constructor
  · rintro ⟨p, hp, he⟩; exact ⟨p.1, p.2, hp, he⟩
  · rintro ⟨d, s, hds, he⟩; exact ⟨(d, s), hds, he⟩

/-- A domain whose values all carry an integer view. Root facts about
order bounds are only meaningful for such slots (the active LeanFzn.Solver's
`domPruningOk` gate establishes this for accepted models). -/
def IntViewedDomain (d : Domain) : Prop :=
  ∀ v ∈ d, Value.intView v ≠ none

/-- The typed-slot gate on a frame (INTERFACES §2.1, task A2): every slot
of the full box carries int-viewed values. This is a supported-fragment
gate, NOT a branch invariant: `ClosureContract.origViewed` asks for the
static hypothesis on the original box, and
`intViewedFrame_of_reachable` below transports it to every reachable
frame (A3's concrete kit consumes the pair). -/
def IntViewedFrame (f : BranchFrame) : Prop :=
  ∀ d ∈ Frame.domains f, IntViewedDomain d

/-- If the slot's value `v` is in the int-viewed domain `d`, then the
slot's integer view in `a` exists and lies in `domInts d`. -/
theorem slotInt_exists_of_mem {a : Assignment} {slot : Nat} {v : Value}
    {d : Domain} (hv : a[slot]? = some v) (hmem : v ∈ d)
    (hview : IntViewedDomain d) :
    ∃ i : Int, slotInt a slot = some i ∧ i ∈ domInts d := by
  obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp (hview v hmem)
  exact ⟨i, by simp only [slotInt, hv]; exact hi, by
    simp only [domInts]; exact List.mem_filterMap.mpr
      ⟨v, (DomainLike.mem_iff d v).mp hmem, hi⟩⟩

/-- `domMinI d = some mn` makes `mn` a lower bound of every integer
view in `d` (re-exported shape for this module's use). -/
theorem domMinI_le_mem {d : Domain} {mn : Int} {v : Value} {i : Int}
    (hv : Value.intView v = some i) (hmem : v ∈ d)
    (hmin : domMinI d = some mn) : mn ≤ i :=
  domMinI_le v i hv hmem hmin

/-- `domMaxI d = some mx` makes `mx` an upper bound of every integer
view in `d`. -/
theorem domMaxI_ge_mem {d : Domain} {mx : Int} {v : Value} {i : Int}
    (hv : Value.intView v = some i) (hmem : v ∈ d)
    (hmax : domMaxI d = some mx) : i ≤ mx :=
  domMaxI_ge v i hv hmem hmax

/-- Membership in `zipIdx` in terms of `getElem?`: `(d, s) ∈ doms.zipIdx`
exactly when `s < doms.length` and `doms[s]? = some d` is read at the
zero-based slot. -/
theorem mem_zipIdx_iff {domains : List Domain} {d : Domain} {s : Nat} :
    (d, s) ∈ domains.zipIdx ↔
      ∃ (h : s < domains.length), domains[s]'h = d := by
  constructor
  · intro hmem
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hmem
    rw [List.getElem_zipIdx] at heq
    have hlt : i < domains.length := by simpa [List.length_zipIdx] using hi
    injection heq with h1 h2
    have hs : i = s := by omega
    subst hs
    exact ⟨by simpa [List.length_zipIdx] using hi, h1⟩
  · rintro ⟨h, rfl⟩
    exact List.mem_iff_getElem.mpr
      ⟨s, by simpa [List.length_zipIdx] using h, by
        rw [List.getElem_zipIdx]
        simp⟩
/-! ## Root-fact soundness -/

/-- Root-fact soundness: every root fact derived from the original
domains holds at every assignment that fits them, provided the domains
are int-viewed. -/
theorem rootFactsOfDomains_sound (domains : List Domain)
    (a : Assignment) (hview : ∀ d ∈ domains, IntViewedDomain d)
    (hfit : a.Fits domains) :
    ∀ e ∈ rootFactsOfDomains domains, e.literal.eval a = some true := by
  intro e he
  rw [mem_rootFactsOfDomains] at he
  obtain ⟨d, s, hds, he⟩ := he
  obtain ⟨hslen, hd⟩ := mem_zipIdx_iff.mp hds
  have hlen : s < a.length := by
    rw [hfit.1]; exact hslen
  have hget : a[s]? = some (a[s]'hlen) := List.getElem?_eq_getElem _
  have hmem : a[s]'hlen ∈ d := by
    have h := hfit.2 s _ hget
    simp only [domEmpty_eq] at h
    have hgd : domains.getD s Dom.empty = d := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hslen, hd]
      rfl
    rw [hgd] at h
    exact h
  have hvd : IntViewedDomain d :=
    hview d (by rw [← hd]; exact List.getElem_mem _)
  obtain ⟨i, hi, _⟩ := slotInt_exists_of_mem hget hmem hvd
  have hvi : Value.intView (a[s]'hlen) = some i := by
    have h := hi
    simp only [slotInt, hget, Option.bind_eq_some_iff] at h
    obtain ⟨v, hv, hiv⟩ := h
    rw [Option.some.injEq] at hv
    rw [← hv] at hiv
    exact hiv
  simp only [domainRootFacts] at he
  split at he
  · rename_i mn mx hmn hmx
    split at he
    · rcases List.mem_cons.mp he with rfl | he
      · rw [eval_posLe_iff]
        refine ⟨i, hi, ?_⟩
        exact domMaxI_ge_mem hvi hmem hmx
      · rcases List.mem_cons.mp he with rfl | he
        · rw [eval_negLe_iff]
          refine ⟨i, hi, ?_⟩
          have := domMinI_le_mem hvi hmem hmn
          omega
        · simp at he
    · simp at he
  · simp at he

/-- The typed-slot gate holds at every reachable frame: the frame admits
only original values (`full_fits`) in one slot per original slot
(`length_ok`), so an int-viewed original box makes every frame slot
int-viewed. Derived, not assumed. -/
theorem intViewedFrame_of_reachable {orig : List Domain} {bs : BranchState leaf}
    (hview : ∀ d ∈ orig, IntViewedDomain d)
    (hreach : ReachableState leaf orig bs) : IntViewedFrame bs.frame := by
  intro d hd v hv
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hd
  have hlen : (fullDomains bs.frame).length = orig.length := hreach.length_ok
  have hjorig : j < orig.length := by rw [← hlen]; exact hj
  have hmemfull : v ∈ (fullDomains bs.frame).getD j Dom.empty := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    exact hv
  have hmemorig : v ∈ orig.getD j Dom.empty := hreach.full_fits _ _ hmemfull
  have horig : orig.getD j Dom.empty ∈ orig := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjorig]
    exact List.getElem_mem hjorig
  exact hview _ horig _ hmemorig

/-! ## Trail validity conditions for the closure

The closure records a deduction only when the frame's mass strictly
decreases. Two side conditions must hold for the resulting trail entry
to be a valid reason (P1.A's `recordImplied_wellFormed`):

* the reason clause is entailed by the leaf semantics (the
  `PropagationContract`'s `reason`/`conflictReason` clauses);
* the reason's non-pivot literals each have an earlier falsifier on the
  trail (chronology). For clause-unit deductions the non-pivot literal
  `q` is impossible in the *pre-narrowing* frame, i.e. every value in
  its slot's domain falsifies `q`; since the trail already records the
  narrowing literals for that slot, with the value removed by this
  step's literal being the last one, `q.negate` is a trail fact for the
  remaining values. We record this as the explicit premise
  `chronologyEvidence` below rather than re-deriving the mixed
  order-encoding combinatorics.
-/

/-- Chronology evidence for one explained step: every non-pivot literal
of the reason clause has an earlier falsifier on the trail. -/
def StepChronology (bs : BranchState leaf) (l : Literal) (c : Clause) : Prop :=
  ∀ q ∈ c, q ≠ l.norm →
    ∃ e' ∈ bs.trail, e'.literal = q.negate

/-- The obligations for one recorded deduction, bundled. -/
def StepObligations (leaf : Assignment → Bool) (bs : BranchState leaf)
    (l : Literal) (c : Clause) : Prop :=
  LearnedEntailed leaf [c] ∧ (l.norm ∈ c) = True ∧ StepChronology bs l c

/-- The per-step obligations the certified propagator layer supplies,
*conditioned on the event the driver actually selects*. This is the
same shape as `PropagationContract` (obligations for actual propagator
runs), which is what makes the contract satisfiable and dischargeable:
for a driver event that is not a deduction the implication is vacuous,
and for a genuine deduction the propagator contract supplies the
reason's entailment while the P1.B bridge supplies chronology. -/
structure ExplainedContract (leaf : Assignment → Bool)
    (original : List Clause) (props : List Propagator) : Prop where
  step : ∀ (bs : BranchState leaf) (f : BranchFrame) (db : List Clause)
      (l : Literal) (c : Clause) (learnReason fromLearned : Bool),
    nextPruningEvent original props f db = .implied l c learnReason fromLearned →
    StepObligations leaf bs l c

/-! ## The explained trail

The trail is built by following the *same* event stream as
`propagationClosure`: for every mass-decreasing deduction the closure
performs, one normalized trail entry is appended with its reason. The
frame component of `explainedClosure` is `propagationClosure`'s frame
by construction, so every existing coverage/learning/cost proof
transfers without any glue theorem. -/

/-- The trail produced by the explained closure. Recursion is on
`Frame.mass f`, the same measure the active closure uses: an entry is
appended exactly when the frame's mass strictly decreases, so trail
additions inherit the closure's finite progress. -/
def explainedTrail (original : List Clause) (props : List Propagator)
    (f : BranchFrame) (db : List Clause) (bs : BranchState leaf)
    (hc : ExplainedContract leaf original props) : BranchState leaf :=
  match nextPruningEvent original props f db with
  | .stable => bs
  | .conflict _ => bs
  | .implied l c learnReason fromLearned =>
      match filterFrame l f with
      | none => bs
      | some g =>
          if Frame.mass g < Frame.mass f then
            explainedTrail original props g
              ((if learnReason && !(db.contains c) then [c] else []) ++ db)
              (bs.recordImplied l { clause := c }) hc
          else bs
termination_by Frame.mass f

/-- The P1.B projection variant: the active driver's certified frame and
learned components, plus the explanation trail. Retained for the
refined-frame equalities; the COHERENT closure is `explainedClosure`
below (PLAN A2), which reads frame and database from the state. -/
def projectedClosure (original : List Clause) (props : List Propagator)
    (f : BranchFrame) (db : List Clause) (bs : BranchState leaf)
    (hc : ExplainedContract leaf original props) : ExplainedRefinement leaf where
  frame := (propagationClosure original props f db).frame
  learned := (propagationClosure original props f db).learned
  state := explainedTrail original props f db bs hc

/-- The frame component is `propagationClosure`'s by construction. -/
theorem projectedClosure_frame_eq (original : List Clause)
    (props : List Propagator) (f : BranchFrame) (db : List Clause)
    (bs : BranchState leaf) (hc : ExplainedContract leaf original props) :
    (projectedClosure original props f db bs hc).frame
      = (propagationClosure original props f db).frame := rfl

/-- The learned component is `propagationClosure`'s by construction. -/
theorem projectedClosure_learned_eq (original : List Clause)
    (props : List Propagator) (f : BranchFrame) (db : List Clause)
    (bs : BranchState leaf) (hc : ExplainedContract leaf original props) :
    (projectedClosure original props f db bs hc).learned
      = (propagationClosure original props f db).learned := rfl

/-! ## Trail properties

The trail never loses entries and never invents them: every step
either keeps the state or appends exactly one explained deduction. All
properties are proved by the same `termination_by`-recursive pattern
the certified closure uses. -/

/-- The trail only grows: the incoming state's trail is a prefix of the
result's trail. -/
theorem explainedTrail_trail_prefix (original : List Clause)
    (props : List Propagator) (hc : ExplainedContract leaf original props)
    (f : BranchFrame) (db : List Clause) (bs : BranchState leaf) :
    ∃ mid : List TrailEntry, (explainedTrail original props f db bs hc).trail
      = bs.trail ++ mid := by
  rw [explainedTrail]
  split
  · exact ⟨[], by simp⟩
  · exact ⟨[], by simp⟩
  · rename_i l c learnReason fromLearned hev
    split
    · exact ⟨[], by simp⟩
    · rename_i g hfilter
      split
      · rename_i hmass
        obtain ⟨mid, hmid⟩ := explainedTrail_trail_prefix original props hc
          g ((if learnReason && !(db.contains c) then [c] else []) ++ db)
          (bs.recordImplied l { clause := c })
        refine ⟨[TrailEntry.mk l.norm bs.level (some { clause := c })] ++ mid, ?_⟩
        rw [hmid]
        simp only [BranchState.recordImplied]
        rw [List.append_assoc]
      · exact ⟨[], by simp⟩
termination_by Frame.mass f

/-- Trail well-formedness: every entry the closure appends carries an
entailed reason, its normalized pivot, and earlier falsifiers for the
reason's non-pivot literals. The `ExplainedContract` supplies these
per-step obligations (from `PropagationContract` plus the root facts).
Levels are bounded because decisions set the level and deductions stay
at it. -/
theorem explainedTrail_wellFormed (original : List Clause)
    (props : List Propagator) (hc : ExplainedContract leaf original props)
    (f : BranchFrame) (db : List Clause) (bs : BranchState leaf)
    (hbs : bs.WellFormed) :
    (explainedTrail original props f db bs hc).WellFormed := by
  rw [explainedTrail]
  split
  · exact hbs
  · exact hbs
  · rename_i l c learnReason fromLearned hev
    split
    · exact hbs
    · rename_i g hfilter
      split
      · rename_i hmass
        obtain ⟨hent, hpivot, hchron⟩ := hc.step bs f db l c learnReason fromLearned hev
        exact explainedTrail_wellFormed original props hc
          g ((if learnReason && !(db.contains c) then [c] else []) ++ db)
          (bs.recordImplied l { clause := c })
          (bs.recordImplied_wellFormed hbs hent hpivot hchron)
      · exact hbs
termination_by Frame.mass f

/-! ## Finite progress for explanation recording

The plan requires that recording explanations cannot loop
independently of domain narrowing. `explainedTrail` appends exactly
one entry per strictly mass-decreasing step, so the number of recorded
entries is bounded by the frame's initial mass: no separate fuel, and
no unbounded trail growth. -/

/-- The trail grows by at most the frame's mass: each recursion step
strictly decreases the measure while appending at most one entry. -/
theorem explainedTrail_len_le (original : List Clause)
    (props : List Propagator) (hc : ExplainedContract leaf original props)
    (f : BranchFrame) (db : List Clause) (bs : BranchState leaf) :
    (explainedTrail original props f db bs hc).trail.length
      ≤ bs.trail.length + Frame.mass f := by
  rw [explainedTrail]
  split
  · simp
  · simp
  · rename_i l c learnReason fromLearned hev
    split
    · simp
    · rename_i g hfilter
      split
      · rename_i hmass
        have ih := explainedTrail_len_le original props hc
          g ((if learnReason && !(db.contains c) then [c] else []) ++ db)
          (bs.recordImplied l { clause := c })
        have hlen : (bs.recordImplied l { clause := c }).trail.length
            = bs.trail.length + 1 := by
          simp only [BranchState.recordImplied, List.length_append,
            List.length_singleton]
        rw [hlen] at ih
        omega
      · simp
termination_by Frame.mass f

/-! ## Decisions from actual chosen alternatives

A decision selects the first value of the next remaining slot. For
integers the selecting literal is the value-equality literal
`¬(s ≠ v)`; for Booleans it is the canonical positive pin. The level
is fresh and the entry carries no reason — decisions are never
mislabeled as root facts, and their level strictly exceeds the
previous one. -/

/-- The literal that asserts "slot `s` takes value `v`". -/
def valueLiteral (s : Nat) (v : Value) : Option Literal :=
  match v with
  | .bool b => some (posBool s b)
  | .int i => some (negNe s i)
  | _ => none

/-- One decision step (M2-migrated to the sparse frame): record the chosen
literal of the FIRST LIVE slot (non-singleton domain, in slot order) at a
fresh level and move to the pinned child `f.pin s v`. Returns `none` when
no live slot exists (the caller keeps such frames in its own stack). -/
private def decideFirstFrom (bs : BranchState leaf) (f : BranchFrame) :
    Nat → List Domain → Option (BranchState leaf × BranchFrame)
  | _, [] => none
  | s, d :: rest =>
      match Dom.enum d with
      | [] => decideFirstFrom bs f (s + 1) rest
      | [_] => decideFirstFrom bs f (s + 1) rest
      | v :: _ :: _ =>
          match valueLiteral s v with
          | none => none
          | some l => some (bs.decide l, f.pin s v)

/-- One decision step: the legacy first-live-slot decision, now on the
sparse frame (`f.pin` at the selected absolute slot). -/
def decideFirst (bs : BranchState leaf) (f : BranchFrame) :
    Option (BranchState leaf × BranchFrame) :=
  decideFirstFrom bs f 0 f.doms

/-- The decision literal for a value selects exactly that value:
`¬(s ≠ k)` holds iff the slot's integer view is `k`, and the Boolean
pin holds iff the slot's Boolean value is the pinned one. -/
theorem valueLiteral_holds_iff {s : Nat} {v : Value} {l : Literal}
    (h : valueLiteral s v = some l) (a : Assignment) :
    l.eval a = some true ↔
      match v with
      | .bool b => a[s]? = some (.bool b)
      | .int i => slotInt a s = some i
      | _ => False := by
  cases v with
  | bool b =>
      simp only [valueLiteral, Option.some.injEq] at h
      subst h
      simp only [posBool, Literal.eval, Atom.eval]
      cases hb : a[s]? with
      | none => simp
      | some val => cases val <;> simp [hb]
  | int i =>
      simp only [valueLiteral, Option.some.injEq] at h
      subst h
      rw [eval_negNe_iff]
      constructor
      · rintro ⟨k, hk, rfl⟩; exact hk
      · intro hi
        exact ⟨i, hi, rfl⟩
  | setOfInt _ => simp [valueLiteral] at h
  | array _ => simp [valueLiteral] at h

/-- A decision appends exactly one reason-less entry at a fresh level. -/
theorem decide_entry {bs : BranchState leaf} {f : BranchFrame}
    {bs' : BranchState leaf} {f' : BranchFrame}
    (h : decideFirst bs f = some (bs', f')) :
    ∃ l : Literal, bs' = bs.decide l := by
  have hgen : ∀ (s : Nat) (ds : List Domain),
      decideFirstFrom bs f s ds = some (bs', f') → ∃ l : Literal, bs' = bs.decide l := by
    intro s ds
    induction ds generalizing s with
    | nil => intro h; simp [decideFirstFrom] at h
    | cons d rest ih =>
        intro h
        cases hd : Dom.enum d with
        | nil =>
            simp only [decideFirstFrom, hd] at h
            exact ih (s + 1) h
        | cons v vs =>
            cases vs with
            | nil =>
                simp only [decideFirstFrom, hd] at h
                exact ih (s + 1) h
            | cons w ws =>
                cases hv : valueLiteral s v with
                | none => simp only [decideFirstFrom, hd, hv] at h; cases h
                | some l =>
                    simp only [decideFirstFrom, hd, hv, Option.some.injEq,
                      Prod.mk.injEq] at h
                    exact ⟨l, h.1.symm⟩
  exact hgen 0 f.doms h

/-- Coverage characterization of a decision: the decided state
represents exactly the predecessor's assignments that satisfy the
decided literal. This combines the P1.A forward/backward contracts and
is the exact coverage contract the plan requires for decisions — a
decision never shrinks the represented set by anything other than its
own literal. -/
theorem decide_represents_iff {bs : BranchState leaf} {l : Literal}
    (a : Assignment) :
    (bs.decide l).Represents a ↔
      bs.Represents a ∧ l.norm.eval a = some true :=
  ⟨BranchState.decide_represents_backward,
   fun ⟨hrep, hlit⟩ => BranchState.decide_represents_forward hrep hlit⟩

/-! ## Removal facts and derived bounds

Sparse domains are explained by *value removals*: a recorded
`s ≠ k` entry excludes `k` without inventing a Boolean fact for an
integer slot. The witness lemmas below are what P1.C's analysis
consumes when a reason's side literal is falsified by such a removal
rather than by an exact negation match. -/

/-- The values the trail explicitly removes from slot `s`: the
witnesses recorded in positive `s ≠ k` entries. -/
def removedValues (trail : List TrailEntry) (s : Nat) : List Int :=
  trail.filterMap fun e =>
    match e.literal.atom, e.literal.positive with
    | .intNe s' k, true => if s' = s then some k else none
    | _, _ => none

/-- A recorded removal excludes that value at every assignment
satisfying the trail: the removed value cannot be the slot's integer
view. This is the "removal fact" half of sparse-domain explanations
(`{0,2,5}` minus `0` and `2` leaves `5`). -/
theorem removedValue_excluded {trail : List TrailEntry} {a : Assignment}
    (htrail : ∀ e ∈ trail, e.literal.eval a = some true)
    {s : Nat} {k : Int} (h : k ∈ removedValues trail s) :
    slotInt a s ≠ some k := by
  obtain ⟨e, he, hmap⟩ := List.mem_filterMap.mp (by simpa [removedValues] using h)
  -- classify the entry: it is a positive removal for the same slot
  have hclass : ∃ (s' : Nat) (k' : Int), e.literal.atom = .intNe s' k' ∧
      e.literal.positive = true ∧ s' = s ∧ k' = k := by
    cases hatom : e.literal.atom with
    | boolEq sl b =>
        cases hpos : e.literal.positive <;>
          exact absurd hmap (by simp [hatom, hpos])
    | intLe sl u =>
        cases hpos : e.literal.positive <;>
          exact absurd hmap (by simp [hatom, hpos])
    | intNe s' k' =>
        cases hpos : e.literal.positive with
        | false => exact absurd hmap (by simp [hatom, hpos])
        | true =>
            simp only [hatom, hpos] at hmap
            by_cases hs : s' = s
            · rw [hs] at hmap
              simp only [if_true] at hmap
              exact ⟨s', k', rfl, rfl, hs, Option.some.inj hmap⟩
            · exact absurd hmap (by simp [hs])
  obtain ⟨s', k', hatom, hpos, hs, hk⟩ := hclass
  rw [← hs, ← hk]
  intro hik
  have hlit : (posNe s' k').eval a = some true := by
    have h := htrail e he
    have hEq : e.literal = posNe s' k' := by
      cases hl : e.literal with
      | mk atom positive =>
          simp only [hl] at hatom hpos
          rw [hatom, hpos]
          rfl
    rwa [hEq] at h
  rw [eval_posNe_iff] at hlit
  obtain ⟨i, hi, hik'⟩ := hlit
  rw [hik] at hi
  exact hik' (Option.some.inj hi).symm

/-- Bound witnesses: a lower bound for slot `s` derived from the
removal facts. If every value below `lo` admitted by the initial
domain has been removed, then `¬(s ≤ lo−1)` is witnessed. The witness
list records exactly which removals justify it, so the analysis never
fabricates an order fact for an integer slot. -/
def derivedLowerWitnesses (trail : List TrailEntry) (s : Nat)
    (domain : Domain) (lo : Int) : List Int :=
  ((Dom.enum domain).filterMap Value.intView).filter fun i =>
    i < lo && i ∉ removedValues trail s

/-- A derived lower bound is justified: when every value the initial
domain admits below `lo` has been removed, every trail-satisfying
assignment's slot value is at least `lo`. This is the lemma behind
sparse-domain singleton collapse (`{0,2,5}` minus `0` and `2` yields
the lower bound `s ≥ 5`), and it cites the removal facts rather than
inventing a Boolean fact for an integer slot. -/
theorem derivedLower_correct {trail : List TrailEntry} {a : Assignment}
    (htrail : ∀ e ∈ trail, e.literal.eval a = some true)
    {s : Nat} {domain : Domain} {lo : Int} {v : Value} {i : Int}
    (hmem : v ∈ domain) (hview : Value.intView v = some i)
    (hget : a[s]? = some v)
    (hbot : ∀ j ∈ (Dom.enum domain).filterMap Value.intView,
      j < lo → j ∈ removedValues trail s) :
    lo ≤ i := by
  refine Int.not_lt.mp fun hlt => ?_
  have hile : i < lo := hlt
  have hi : i ∈ (Dom.enum domain).filterMap Value.intView :=
    List.mem_filterMap.mpr ⟨v, (DomainLike.mem_iff domain v).mp hmem, hview⟩
  have hexcl := removedValue_excluded htrail (hbot i hi hile)
  have hslot : slotInt a s = some i := by
    simp only [slotInt, hget]
    exact hview
  exact hexcl hslot

/-! ## The duplicate-safe enqueue discipline (A2 freshness policy)

PLAN P1.1 item 2 / A1's `TrailLiteralsDistinct.decide_duplicates` show that
recording a literal the trail already carries destroys the duplicate-safe
discipline `ReachableState.distinct`. A1 proved that freshness CANNOT be
derived from `filterFrame` + mass decrease alone (a redundant enqueue can
still decrease mass when the remaining domain is empty), so the resident
closure performs the plan's own "skip repeated deductions" policy: a
selected deduction whose NORMALIZED literal already occurs on the trail is
skipped (`explainedStep` returns `.stable`, `explainedDeduction` returns
`none`), and the skip is recorded in the closure result as a stable
fixpoint. The skipped frame update only ever affects frames with no
covered assignment (`ReachableState.agrees` makes a recorded literal hold
at every frame-covered assignment, so filtering by it removes nothing
unless there is nothing to cover), so no represented leaf solution is
lost. Every recorded deduction is therefore fresh, and the `distinct`
field is discharged from the check itself. -/

/-- The trail already carries the normalized form of `l`. This is the
absence check the enqueue path performs before recording a deduction. -/
def TrailRedundant (trail : List TrailEntry) (l : Literal) : Bool :=
  trail.any fun e => decide (e.literal = l.norm)

/-- Characterization of the redundancy check. -/
theorem trailRedundant_iff {trail : List TrailEntry} {l : Literal} :
    TrailRedundant trail l = true ↔ ∃ e ∈ trail, e.literal = l.norm := by
  simp only [TrailRedundant, List.any_eq_true]
  constructor
  · rintro ⟨e, he, hd⟩
    exact ⟨e, he, of_decide_eq_true hd⟩
  · rintro ⟨e, he, heq⟩
    exact ⟨e, he, decide_eq_true heq⟩

/-- The negation of the check, in the `∀ e ∈ trail, e.literal ≠ l.norm`
shape `TrailLiteralsDistinct.enqueue` consumes. -/
theorem not_trailRedundant_iff {trail : List TrailEntry} {l : Literal} :
    TrailRedundant trail l = false ↔ ∀ e ∈ trail, e.literal ≠ l.norm := by
  constructor
  · intro h e he heq
    have htrue : TrailRedundant trail l = true := trailRedundant_iff.mpr ⟨e, he, heq⟩
    rw [htrue] at h
    exact Bool.noConfusion h
  · intro h
    cases hr : TrailRedundant trail l with
    | false => rfl
    | true =>
        obtain ⟨e, he, heq⟩ := trailRedundant_iff.mp hr
        exact absurd heq (h e he)

/-! ## A2 — the resident explained step

The step is over a SINGLE coherent state: the frame and the learned
database are read from the state itself, so no separate (and possibly
unrelated) frame/database arguments can be supplied. The step returns
the runtime effect, and the theorems below prove each row of the plan's
transition table from the concrete event data.
-/

/-- The runtime effect of one explained step. -/
inductive StepEffect (leaf : Assignment → Bool) where
  /-- no productive selected deduction remains under the scan semantics -/
  | stable
  /-- the branch is excluded by an entailed clause — or by an empty local
      explanation, in which case `learned` is empty and only this branch
      is dead (never a global UNSAT) -/
  | excluded (learned : List Clause)
  /-- a productive deduction: narrow the frame by `literal`, append the
      justified entry with reason clause `reason`, learn `learned` -/
  | narrow (literal : Literal) (reason : Clause) (learned : List Clause)
  deriving DecidableEq, Repr

/-- One explained step over a coherent state. A selected deduction whose
normalized literal is already recorded on the trail is skipped
(`.stable`): the enqueue path is absence-checked, which is the policy
that keeps `ReachableState.distinct` (A1). -/
def explainedStep (original : List Clause) (props : List Propagator)
    (bs : BranchState leaf) : StepEffect leaf :=
  match nextPruningEvent original props bs.frame bs.learned with
  | .stable => .stable
  | .conflict cs =>
      .excluded (cs.filter fun c => !(bs.learned.contains c))
  | .implied l c learnReason fromLearned =>
      let learned := if learnReason && !(bs.learned.contains c) then [c] else []
      match TrailRedundant bs.trail l with
      | true => .stable
      | false =>
          match filterFrame l bs.frame with
          | none => .excluded learned
          | some g =>
              if Frame.mass g < Frame.mass bs.frame then .narrow l c learned
              else .stable

/-- The per-event obligations the certified layer supplies for the event
the step ACTUALLY selected. Each field is required only for the event
kind it names, which is what keeps the contract satisfiable: for a
driver event that is not a deduction the implications are vacuous, and
for a genuine deduction the propagator contract supplies the reason's
entailment while the coherent state supplies chronology. -/
structure StepContract (leaf : Assignment → Bool) (original : List Clause)
    (props : List Propagator) (bs : BranchState leaf) : Prop where
  /-- a conflict event excludes every leaf solution the state represents -/
  conflictExcludes : ∀ cs, nextPruningEvent original props bs.frame bs.learned
      = .conflict cs →
    ∀ a, leaf a = true → bs.Represents a → False
  /-- a conflict event's learned clauses are globally entailed -/
  conflictEntailed : ∀ cs, nextPruningEvent original props bs.frame bs.learned
      = .conflict cs → LearnedEntailed leaf cs
  /-- a deduction's reason clause is globally entailed -/
  impliedEntailed : ∀ l c lr fl,
    nextPruningEvent original props bs.frame bs.learned = .implied l c lr fl →
      LearnedEntailed leaf [c]
  /-- the deduction's pivot is a member of its reason clause -/
  impliedPivot : ∀ l c lr fl,
    nextPruningEvent original props bs.frame bs.learned = .implied l c lr fl →
      (l.norm ∈ c) = True
  /-- chronology evidence for the deduction's non-pivot literals -/
  impliedChronology : ∀ l c lr fl,
    nextPruningEvent original props bs.frame bs.learned = .implied l c lr fl →
      StepChronology bs l c
  /-- a deduction's literal names an in-range (original) slot; this is the
      gate the historical `domPruningOkB`/well-formedness checks supply -/
  impliedInRange : ∀ l c lr fl,
    nextPruningEvent original props bs.frame bs.learned = .implied l c lr fl →
      l.atom.slot < (fullDomains bs.frame).length

/-- Normalization preserves `valueHolds`: the stored (normalized) literal
filters exactly the values the original literal filters. -/
theorem norm_valueHolds (l : Literal) (v : Value) :
    l.norm.valueHolds v = l.valueHolds v := by
  cases l with
  | mk atom positive =>
    cases atom with
    | intLe s k => cases positive <;> rfl
    | intNe s k => cases positive <;> rfl
    | boolEq s b =>
        cases positive with
        | true => rfl
        | false =>
            simp only [Literal.norm]
            cases v with
            | bool actual => cases actual <;> cases b <;> rfl
            | int i => rfl
            | setOfInt x => rfl
            | array x => rfl

/-- Normalization never changes the literal's slot. -/
theorem norm_atom_slot (l : Literal) : l.norm.atom.slot = l.atom.slot := by
  cases l with
  | mk atom positive => cases atom <;> (cases positive <;> rfl)

/-! ### Coverage monotonicity for pointwise box subsets

The narrowed-frame laws (`filterFrame_literal_holds`, `filterFrame_preserves`,
`filterFrame_removal_witness`, `filterFrame_rem_length`,
`filterFrame_singleton`) live in `FrameFilter.lean` (M3): they are sparse
filter laws shared with the run layer. Only the coverage-monotonicity
helper is closure-specific. -/

/-- Pointwise box containment implies coverage containment for boxes with
the same slot count (the shape the sparse `filterFrame` produces). -/
theorem FrameCovers_of_subsets {f g : BranchFrame} {a : Assignment}
    (hlen : g.doms.length = f.doms.length)
    (hbox : ∀ i v, v ∈ (fullDomains g).getD i Dom.empty → v ∈ (fullDomains f).getD i Dom.empty)
    (hcov : FrameCovers g a) : FrameCovers f a := by
  refine mem_allAssigns_of_getElem? _ _ ?_ ?_
  · rw [(allAssigns_fits _ _ hcov).1, hlen]
  · intro j v hv
    exact hbox j v ((allAssigns_fits _ _ hcov).2 j v hv)

/-! ### The A2 transition theorems -/

/-- A sparse filter preserves an exact singleton pin definitionally: a
targeted singleton survives only when the literal accepts its value, and
every other slot is untouched (or filtered to the same value). -/
theorem filterFrame_pin {l : Literal} {f g : BranchFrame} {k : Nat} {v : Value}
    (hg : filterFrame l f = some g)
    (hk : f.doms[k]? = some (Dom.ofList [v])) :
    g.doms[k]? = some (Dom.ofList [v]) := by
  unfold filterFrame at hg
  split at hg
  · cases hg
    exact hk
  · rename_i d hd
    split at hg
    · cases hg
    · rename_i hfil
      cases hg
      change (f.doms.set l.atom.slot (Dom.filterLitKeep l d))[k]? =
        some (Dom.ofList [v])
      by_cases hik : l.atom.slot = k
      · have hlt' : l.atom.slot < f.doms.length :=
          (List.getElem?_eq_some_iff.mp hd).1
        have hk' : f.doms[l.atom.slot]? = some (Dom.ofList [v]) := by
          rw [hik]; exact hk
        have hsame : d = Dom.ofList [v] := Option.some.inj (hd.symm.trans hk')
        have hpin : Dom.filterLitKeep l (Dom.ofList [v]) = Dom.ofList [v] := by
          apply Dom.filterLitKeep_eq_self_of_forall
          intro y hy
          rw [Dom.enum_ofList, List.mem_singleton] at hy
          subst y
          by_cases hp : l.valueHolds v = true
          · exact hp
          · exfalso
            apply hfil
            rw [hsame, Dom.enum_filterLitKeep, Dom.enum_ofList]
            simp [hp]
        rw [← hik, List.getElem?_set_self hlt', hsame, hpin]
      · rw [List.getElem?_set, if_neg hik]
        exact hk

/-- The state produced by a productive deduction. -/
def narrowState (bs : BranchState leaf) (g : BranchFrame) (l : Literal)
    (c : Clause) (learned : List Clause) : BranchState leaf :=
  { frame := g
    trail := bs.trail ++ [{ literal := l.norm, level := bs.level,
                            reason := some { clause := c } }]
    level := bs.level
    learned := learned ++ bs.learned }

/-- COVERAGE: a productive deduction preserves every leaf solution that
satisfies the deduced literal. The narrowed frame's coverage comes from
the filter, not from an assumption. -/
theorem explainedStep_narrow_coverage {bs : BranchState leaf}
    {g : BranchFrame} {l : Literal} {c : Clause} {learned : List Clause}
    (hfilter : filterFrame l bs.frame = some g)
    (hent : LearnedEntailed leaf learned) :
    ∀ a, leaf a = true → bs.Represents a → l.norm.eval a = some true →
      (narrowState bs g l c learned).Represents a := by
  intro a hleaf hrep hlit
  obtain ⟨hcov, htrail, hlearn⟩ := hrep
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨g', hg', hcov'⟩ := filterFrame_preserves hcov (by
      rwa [Literal.norm_eval] at hlit)
    rw [hfilter] at hg'
    cases hg'
    exact hcov'
  · intro e he
    simp only [narrowState] at he
    rcases trail_append_entry_mem he with he | rfl
    · exact htrail e he
    · simpa using hlit
  · intro cl hcl
    simp only [narrowState, List.mem_append] at hcl
    rcases hcl with hcl | hcl
    · exact hent cl hcl a hleaf
    · exact hlearn cl hcl

/-- COHERENCE: a productive deduction preserves the reachable invariant.
Every obligation is derived — the narrowed frame's literal from the
filter, the entry's reason from the contract, the ledger from the
completeness invariant — so no caller supplies a runtime assumption.
The `hfresh` premise is the absence check (`TrailRedundant ... = false`);
`explainedDeduction_fresh` below derives it from the selected deduction,
and `explainedDeduction_narrow_reachable` bundles that derivation with
the `ClosureContract` obligations. -/
theorem explainedStep_narrow_reachable {orig : List Domain}
    {bs : BranchState leaf} {g : BranchFrame} {l : Literal} {c : Clause}
    {learned : List Clause}
    (hreach : ReachableState leaf orig bs)
    (hfilter : filterFrame l bs.frame = some g)
    (hfresh : ∀ e ∈ bs.trail, e.literal ≠ l.norm)
    (hin : l.atom.slot < (fullDomains bs.frame).length)
    (hent : LearnedEntailed leaf learned)
    (hentReason : LearnedEntailed leaf [c])
    (hpivot : (l.norm ∈ c) = True)
    (hchron : StepChronology bs l c) :
    ReachableState leaf orig (narrowState bs g l c learned) := by
  have hlen := filterFrame_rem_length hfilter
  have horder := Frame.filterFrame_order hfilter
  have hframe : (narrowState bs g l c learned).frame = g := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- length
    rw [fullDomains_length, hframe, hlen]
    exact hreach.length_ok
  · -- no invented values
    intro i v hv
    exact hreach.full_fits i v (filterFrame_subsets hfilter i v hv)
  · -- decided slots stay singletons and forced (the trail only grew)
    intro k hk
    have hk0 : k ∈ bs.frame.order := by
      change k ∈ g.order at hk
      rwa [horder] at hk
    obtain ⟨v, hv, hforce⟩ := hreach.pins_forced k hk0
    refine ⟨v, ?_, ?_⟩
    · exact filterFrame_singleton hfilter hv
    · intro a htrail hfit
      exact hforce a (fun e he => htrail e
        (List.mem_append.mpr (Or.inl he))) hfit
  · -- every entry holds at every covered assignment
    intro e he a hcov
    simp only [narrowState] at he
    rcases trail_append_entry_mem he with he | rfl
    · exact hreach.agrees e he a
        (FrameCovers_of_subsets hlen (filterFrame_subsets hfilter) hcov)
    · exact filterFrame_literal_holds hfilter hcov (lt_of_lt_of_eq hin hlen.symm)
  · -- narrowing is complete: removed original values of undecided slots
    -- carry a falsifier (this filter's fresh entry, or an old witness)
    intro k hk w horig hnot
    have hk' : k ∉ bs.frame.order := by
      intro hmem
      exact hk (by rw [hframe, horder]; exact hmem)
    by_cases hwas : w ∈ bs.frame.doms.getD k Dom.empty
    · -- dropped by this filter: the fresh entry witnesses it
      obtain ⟨hslot, hfalse⟩ := filterFrame_removal_witness hfilter hwas hnot
      refine ⟨{ literal := l.norm, level := bs.level,
                reason := some { clause := c } }, ?_, ?_, ?_⟩
      · exact List.mem_append.mpr (Or.inr (List.mem_singleton_self _))
      · show l.norm.atom.slot = k
        rw [norm_atom_slot]
        exact hslot
      · rwa [norm_valueHolds]
    · -- already excluded: the old witness, transported
      obtain ⟨e, he, hslot, hfalse⟩ := hreach.narrowing_complete k hk' w horig hwas
      refine ⟨e, ?_, ?_, hfalse⟩
      · exact List.mem_append.mpr (Or.inl he)
      · show e.literal.atom.slot = k
        exact hslot
  · -- structural well-formedness (the learned list is freshness-filtered,
    -- so the unconditional prepend lemma does not apply directly)
    obtain ⟨hlev, hnorm, hreason, hchron0, hlearn⟩ := hreach.wf
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro e he
      simp only [narrowState] at he
      rcases trail_append_entry_mem he with he | rfl
      · exact hlev e he
      · simp [narrowState]
    · intro e he
      simp only [narrowState] at he
      rcases trail_append_entry_mem he with he | rfl
      · exact hnorm e he
      · simp [narrowState, norm_norm]
    · intro e he r hr
      simp only [narrowState] at he
      rcases trail_append_entry_mem he with he | rfl
      · exact hreason e he r hr
      · have hr1 : { clause := c } = r := by
          simpa only [Option.mem_some_iff] using hr
        rw [← hr1]
        exact ⟨hentReason, hpivot⟩
    · intro e he r hr q hq hne
      simp only [narrowState] at he
      rcases trail_append_entry_mem he with he | rfl
      · obtain ⟨e'', he'', heq, hlt⟩ := hchron0 e he r hr q hq hne
        refine ⟨e'', ?_, heq, earlierThan_extend hlt⟩
        simp only [narrowState]
        exact List.mem_append.mpr (Or.inl he'')
      · have hr1 : { clause := c } = r := by
          simpa only [Option.mem_some_iff] using hr
        have hq' : q ∈ c := by simpa only [← hr1] using hq
        have hne' : q ≠ l.norm := by simpa using hne
        obtain ⟨e'', he'', heq⟩ := hchron q hq' hne'
        refine ⟨e'', ?_, heq, earlierThan_append_last he''⟩
        simp only [narrowState]
        exact List.mem_append.mpr (Or.inl he'')
    · intro cl hcl
      simp only [narrowState, List.mem_append] at hcl
      rcases hcl with hcl | hcl
      · exact hent cl hcl
      · exact hlearn cl hcl
  · -- the trail stays LEVEL-SORTED (B2's uniqueness enabler): the fresh
    -- entry sits at the current level, which dominates every existing
    -- entry by well-formedness, and the reason clause never re-seeds the
    -- level order
    rw [narrowState]
    refine levelSorted_append hreach.sorted ?_
    intro e' he'
    have hle := hreach.wf.1 e' he'
    show e'.level ≤ bs.level
    omega
  · -- the duplicate-safe discipline: the appended entry is the
    -- absence-checked enqueue of a fresh normalized literal (A1's
    -- `TrailLiteralsDistinct.enqueue`), so `distinct` is discharged from
    -- `hfresh`, not assumed
    rw [narrowState]
    exact TrailLiteralsDistinct.enqueue hreach.distinct hreach.wf.2.1 hfresh

/-! ### Effect/event dispatch -/

/-- A `.stable` driver event yields the `.stable` effect. -/
theorem explainedStep_stable_shape {original : List Clause}
    {props : List Propagator} {bs : BranchState leaf}
    (h : nextPruningEvent original props bs.frame bs.learned = .stable) :
    explainedStep original props bs = .stable := by
  simp only [explainedStep, h]

/-- CONFLICT ROW: a conflict event excludes the branch and learns exactly
the fresh clauses of the event; an empty local explanation yields the
empty learned list, so it is a branch exclusion and never a global
UNSAT. -/
theorem explainedStep_excluded_shape {original : List Clause}
    {props : List Propagator} {bs : BranchState leaf} {cs : List Clause}
    (h : nextPruningEvent original props bs.frame bs.learned = .conflict cs) :
    explainedStep original props bs
      = .excluded (cs.filter fun c => !(bs.learned.contains c)) := by
  simp only [explainedStep, h]

/-- The entailed-clause half of the conflict row. -/
theorem explainedStep_excluded_entailed {original : List Clause}
    {props : List Propagator} {bs : BranchState leaf} {cs : List Clause}
    (h : nextPruningEvent original props bs.frame bs.learned = .conflict cs)
    (hc : StepContract leaf original props bs) :
    LearnedEntailed leaf (cs.filter fun c => !(bs.learned.contains c)) := by
  intro c hmem
  exact hc.conflictEntailed cs h c (List.mem_filter.mp hmem).1

/-- The exclusion half of the conflict row: every leaf solution the state
represents is excluded. -/
theorem explainedStep_excluded_sound {original : List Clause}
    {props : List Propagator} {bs : BranchState leaf} {cs : List Clause}
    (h : nextPruningEvent original props bs.frame bs.learned = .conflict cs)
    (hc : StepContract leaf original props bs) :
    ∀ a, leaf a = true → bs.Represents a → False :=
  hc.conflictExcludes cs h

/-- NARROW ROW: a productive, FRESH deduction yields the `.narrow` effect
with the deduced literal, its reason clause and the fresh clauses. -/
theorem explainedStep_narrow_shape {original : List Clause}
    {props : List Propagator} {bs : BranchState leaf}
    {l : Literal} {c : Clause} {lr fl : Bool} {g : BranchFrame}
    (h : nextPruningEvent original props bs.frame bs.learned = .implied l c lr fl)
    (hfilter : filterFrame l bs.frame = some g)
    (hmass : Frame.mass g < Frame.mass bs.frame)
    (hfresh : TrailRedundant bs.trail l = false) :
    explainedStep original props bs
      = .narrow l c (if lr && !(bs.learned.contains c) then [c] else []) := by
  simp only [explainedStep, h, hfresh, hfilter, if_pos hmass]

/-- A NONPRODUCTIVE deduction (the scan's advance case) yields `.stable`:
the step made no state change, so a re-dispatch cannot loop on it, and
no unjustified entry is recorded. -/
theorem explainedStep_nonproductive_shape {original : List Clause}
    {props : List Propagator} {bs : BranchState leaf}
    {l : Literal} {c : Clause} {lr fl : Bool} {g : BranchFrame}
    (h : nextPruningEvent original props bs.frame bs.learned = .implied l c lr fl)
    (hfilter : filterFrame l bs.frame = some g)
    (hmass : ¬ (Frame.mass g < Frame.mass bs.frame))
    (hfresh : TrailRedundant bs.trail l = false) :
    explainedStep original props bs = .stable := by
  simp only [explainedStep, h, hfresh, hfilter, if_neg hmass]

/-- An unsatisfiable-in-the-frame deduction (`filterFrame` returns `none`)
yields the exclusion effect: the branch is dead. -/
theorem explainedStep_nofilter_shape {original : List Clause}
    {props : List Propagator} {bs : BranchState leaf}
    {l : Literal} {c : Clause} {lr fl : Bool}
    (h : nextPruningEvent original props bs.frame bs.learned = .implied l c lr fl)
    (hfilter : filterFrame l bs.frame = none)
    (hfresh : TrailRedundant bs.trail l = false) :
    explainedStep original props bs
      = .excluded (if lr && !(bs.learned.contains c) then [c] else []) := by
  simp only [explainedStep, h, hfresh, hfilter]

/-- A REDUNDANT deduction (the literal is already recorded) is skipped:
the step is a stable fixpoint. This is the policy that keeps every
recorded deduction fresh, and hence keeps `ReachableState.distinct`. -/
theorem explainedStep_redundant_shape {original : List Clause}
    {props : List Propagator} {bs : BranchState leaf}
    {l : Literal} {c : Clause} {lr fl : Bool}
    (h : nextPruningEvent original props bs.frame bs.learned = .implied l c lr fl)
    (hred : TrailRedundant bs.trail l = true) :
    explainedStep original props bs = .stable := by
  simp only [explainedStep, h, hred]

/-! ### The productive deduction, as data

The driver recurses only on productive deductions. Carrying the narrowed
frame together with the STRICT mass decrease in the step's payload makes
the driver's termination argument immediate and fuel-free. -/

structure ProductiveDeduction (leaf : Assignment → Bool)
    (bs : BranchState leaf) where
  /-- the deduced literal -/
  literal : Literal
  /-- its reason clause -/
  reason : Clause
  /-- clauses to learn globally (already freshness-filtered) -/
  learned : List Clause
  /-- the narrowed frame -/
  frame : BranchFrame
  /-- the narrowing call that produced it -/
  filtered : filterFrame literal bs.frame = some frame
  /-- productive: the domain mass strictly decreases -/
  decreases : Frame.mass frame < Frame.mass bs.frame

/-- The next productive deduction of a state, or `none` when the step is
stable, the branch is dead, or the deduction is REDUNDANT (its normalized
literal is already recorded — the plan's "skip repeated deductions"
policy, which is what makes every returned deduction fresh and hence
keeps `ReachableState.distinct`). Mirrors `explainedStep`'s dispatch
exactly, but returns the narrowed frame and its decrease as data. -/
def explainedDeduction (original : List Clause) (props : List Propagator)
    (bs : BranchState leaf) : Option (ProductiveDeduction leaf bs) :=
  match nextPruningEvent original props bs.frame bs.learned with
  | .stable => none
  | .conflict _ => none
  | .implied l c learnReason fromLearned =>
      let learned := if learnReason && !(bs.learned.contains c) then [c] else []
      match TrailRedundant bs.trail l with
      | true => none
      | false =>
          match hf : filterFrame l bs.frame with
          | none => none
          | some g =>
              if hm : Frame.mass g < Frame.mass bs.frame then
                some { literal := l, reason := c, learned := learned, frame := g,
                       filtered := hf, decreases := hm }
              else none

/-! ## R1d frame/trail synchronisation

After a frame tightening the branch frame may be strictly tighter than the
trail records (bounds from holes, fixings). `syncOne` pushes one implied
bound/fix literal with its DOMAIN EXPLANATION clause as an ordinary
`narrowState` enqueue at the unchanged frame; `syncSlot` pushes the three
candidates of a slot, `syncAll` those of every remaining slot. -/

section FrameSyncCore

variable {leaf : Assignment → Bool}

/-- The trail entries whose literal lives on slot `s` (P2c): a literal implied
by a trail entry can only live on the same slot (`impliesP_slot_eq`), so both
the implication guard and the removers of `syncClause` may scan this filtered
trail instead of the whole one. -/
def trailOnSlot (trail : List TrailEntry) (s : Nat) : List TrailEntry :=
  trail.filter fun e => e.literal.atom.slot == s

/-- The negation of the LATEST trail literal on slot `s` that rejects `w`.
Scans from the end without materialising the reversed/negated trail (P2c):
the previous `trail.reverse.map negate` allocated one literal per entry on
every call, and `syncExplain` calls this once per rejected value. -/
def syncRemover (trail : List TrailEntry) (s : Nat) (w : Value) : Option Literal :=
  (trail.findRev? fun e =>
    e.literal.atom.slot == s && e.literal.negate.valueHolds w).map
    fun e => e.literal.negate

/-- The removers of every value of `W` (duplicate free); `none` when some
value has no remover. -/
def syncExplain (trail : List TrailEntry) (s : Nat) (W : List Value) :
    Option Clause :=
  let rs := W.map (syncRemover trail s)
  if rs.any Option.isNone then none else some (rs.filterMap id).eraseDups

/-- Filtering by slot does not change the remover search (P2c). -/
theorem syncRemover_trailOnSlot (trail : List TrailEntry) (s : Nat) (w : Value) :
    syncRemover (trailOnSlot trail s) s w = syncRemover trail s w := by
  unfold syncRemover trailOnSlot
  rw [List.findRev?_eq_find?_reverse, List.findRev?_eq_find?_reverse]
  rw [← List.filter_reverse, List.find?_filter]
  have hpred : (fun (a : TrailEntry) => decide
      ((a.literal.atom.slot == s) = true ∧
        (a.literal.atom.slot == s && a.literal.negate.valueHolds w) = true))
      = (fun (e : TrailEntry) =>
          e.literal.atom.slot == s && e.literal.negate.valueHolds w) := by
    funext a
    apply Bool.eq_iff_iff.mpr
    simp
  rw [hpred]

/-- Explanation search on a slot-filtered trail (P2c). -/
theorem syncExplain_trailOnSlot (trail : List TrailEntry) (s : Nat) (W : List Value) :
    syncExplain (trailOnSlot trail s) s W = syncExplain trail s W := by
  unfold syncExplain
  rw [show List.map (syncRemover (trailOnSlot trail s) s) W
        = List.map (syncRemover trail s) W from
      List.map_congr_left (fun w _ => syncRemover_trailOnSlot trail s w)]

/-- Scanning the slot-filtered trail for an implying entry is the same as
scanning the whole trail (P2c). -/
theorem trailOnSlot_any_impliesP {orig : List Domain} {trail : List TrailEntry}
    {s : Nat} {l : Literal} (hs : l.atom.slot = s) :
    (trailOnSlot trail s).any (fun e => impliesP orig e.literal l)
      = trail.any (fun e => impliesP orig e.literal l) := by
  unfold trailOnSlot
  rw [List.any_filter]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨e, he, hq⟩
    simp only [Bool.and_eq_true] at hq
    exact ⟨e, he, hq.2⟩
  · rintro ⟨e, he, hq⟩
    refine ⟨e, he, ?_⟩
    have hsl := impliesP_slot_eq hq
    have hse : (e.literal.atom.slot == s) = true := by rw [hsl, hs]; simp
    simp only [Bool.and_eq_true]
    exact ⟨hse, hq⟩

/-- The domain-explanation clause of pushing `lit` at `bs`, when the push is
justified: the literal holds on the whole (nonempty) remaining domain of its
slot, is not implied by the trail, rejects some original value, and every
rejected original value has a trail remover. -/
def syncClause (orig : List Domain) (bs : BranchState leaf) (lit : Literal) :
    Option Clause :=
  let s := lit.atom.slot
  match bs.frame.doms[s]? with
  | none => none
  | some d =>
    let l := lit.norm
    let tl := trailOnSlot bs.trail s
    let W := (Dom.enum (orig.getD s Dom.empty)).filter fun w => !l.valueHolds w
    if !d.isEmpty && (Dom.enum d).all l.valueHolds && !W.isEmpty
        && !(tl.any fun e => impliesP orig e.literal l) then
      (syncExplain tl s W).map (l :: ·)
    else none

/-- Tail-recursive `all` for the wide-domain guard scans: `List.all` recurses
structurally on the list and overflows the stack on the 10^7-element
enumerations of a wide `.holes` domain, while `foldl` is compiled as a loop. -/
def valueAllFast (p : Value → Bool) (vs : List Value) : Bool :=
  vs.foldl (fun b v => b && p v) true

theorem foldl_and_false (p : Value → Bool) (vs : List Value) :
    vs.foldl (fun b v => b && p v) false = false := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [List.foldl_cons, ih]

theorem valueAllFast_eq (p : Value → Bool) (vs : List Value) :
    valueAllFast p vs = vs.all p := by
  unfold valueAllFast
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      rw [List.foldl_cons]
      by_cases h : p v = true
      · simp [List.all, h, ih]
      · have h' : p v = false := by cases hp : p v <;> simp_all
        rw [h', Bool.true_and, foldl_and_false]
        simp [List.all, h']

/-- The list of `W`-removers as an `Option`: `none` if some rejected value
has no trail remover, otherwise the remover literals in `W` order. -/
def syncExplainList (trail : List TrailEntry) (s : Nat) (W : List Value) :
    Option (List Literal) :=
  let rs := W.map (syncRemover trail s)
  if rs.any Option.isNone then none else some (rs.filterMap id)

theorem syncExplain_eq_syncExplainList (trail : List TrailEntry) (s : Nat)
    (W : List Value) :
    syncExplain trail s W = (syncExplainList trail s W).map List.eraseDups := by
  unfold syncExplain syncExplainList
  dsimp only
  by_cases h : (W.map (syncRemover trail s)).any Option.isNone = true
  · simp [h]
  · simp [h]

private theorem filterMap_id_length_of_all_some {W : List Value}
    {f : Value → Option Literal}
    (h : (W.map f).any Option.isNone = false) :
    ((W.map f).filterMap id).length = W.length := by
  induction W with
  | nil => rfl
  | cons w ws ih =>
      rw [List.map_cons, List.any_cons, Bool.or_eq_false_iff] at h
      obtain ⟨h1, h2⟩ := h
      cases hw : f w with
      | none => rw [hw] at h1; simp at h1
      | some r =>
          rw [List.map_cons, List.filterMap_cons, hw]
          change (r :: List.filterMap id (List.map f ws)).length = ws.length + 1
          rw [List.length_cons, ih h2]

theorem syncExplainList_length {trail : List TrailEntry} {s : Nat}
    {W : List Value} {rs : List Literal}
    (h : syncExplainList trail s W = some rs) : rs.length = W.length := by
  unfold syncExplainList at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hc
    have hc' : (List.map (syncRemover trail s) W).any Option.isNone = false := by
      simpa using hc
    rw [Option.some.injEq] at h
    rw [← h]
    exact filterMap_id_length_of_all_some hc'

/-- Tail-recursive scan of the original enumeration, skipping values that
satisfy `l` and collecting the removers of the rejected ones (in reverse
discovery order).  It avoids materialising the rejected-value list and the
non-tail `List.any` over it. -/
def syncExplainStep (trail : List TrailEntry) (s : Nat) (l : Literal)
    (acc : Option (List Literal)) (w : Value) : Option (List Literal) :=
  match acc with
  | none => none
  | some rs =>
      if l.valueHolds w then some rs
      else
        match syncRemover trail s w with
        | none => none
        | some r => some (r :: rs)

def syncExplainFold (trail : List TrailEntry) (s : Nat) (l : Literal)
    (vs : List Value) : Option (List Literal) :=
  vs.foldl (syncExplainStep trail s l) (some [])

theorem syncExplainFold_aux (trail : List TrailEntry) (s : Nat) (l : Literal)
    (vs : List Value) (acc : Option (List Literal)) :
    vs.foldl (syncExplainStep trail s l) acc =
      (match acc with
       | none => none
       | some rs =>
           (match syncExplainList trail s
              (vs.filter fun w => !l.valueHolds w) with
            | none => none
            | some rs' => some (rs'.reverse ++ rs))) := by
  induction vs generalizing acc with
  | nil =>
      cases acc with
      | none => rfl
      | some rs => simp [syncExplainList]
  | cons w ws ih =>
      rw [List.foldl_cons, ih]
      cases acc with
      | none => rfl
      | some rs =>
          unfold syncExplainStep
          by_cases hv : l.valueHolds w = true
          · have hf : (w :: ws).filter (fun w => !l.valueHolds w) =
                ws.filter (fun w => !l.valueHolds w) := by simp [hv]
            simp [hv, hf]
          · have hv' : l.valueHolds w = false := by
              cases hp : l.valueHolds w <;> simp_all
            have hf : (w :: ws).filter (fun w => !l.valueHolds w) =
                w :: ws.filter (fun w => !l.valueHolds w) := by simp [hv']
            rw [hf]
            cases hr : syncRemover trail s w with
            | none => simp [hv', syncExplainList, hr]
            | some r =>
                simp [hv', syncExplainList, hr]
                by_cases hc : ∃ x, x ∈ ws ∧ l.valueHolds x = false ∧
                    syncRemover trail s x = none
                · simp [hc]
                · simp [hc, List.reverse_cons, List.append_assoc]

theorem syncExplainFold_eq (trail : List TrailEntry) (s : Nat) (l : Literal)
    (vs : List Value) :
    syncExplainFold trail s l vs =
      (match syncExplainList trail s
          (vs.filter fun w => !l.valueHolds w) with
       | none => none
       | some rs => some rs.reverse) := by
  unfold syncExplainFold
  rw [syncExplainFold_aux]
  simp

/-- The fast domain-shaped explanation search: `none` when the rejected set is
empty (the original guard) or some rejected value has no remover, otherwise
the same deduplicated remover clause as `syncExplain`. -/
def syncExplainDom (trail : List TrailEntry) (s : Nat) (l : Literal)
    (vs : List Value) : Option Clause :=
  match syncExplainFold trail s l vs with
  | none => none
  | some rs => if rs.isEmpty then none else some rs.reverse.eraseDups

theorem syncExplainDom_eq (trail : List TrailEntry) (s : Nat) (l : Literal)
    (vs : List Value) :
    syncExplainDom trail s l vs =
      (match vs.filter (fun w => !l.valueHolds w) with
       | [] => none
       | W => syncExplain trail s W) := by
  unfold syncExplainDom
  rw [syncExplainFold_eq]
  cases h : vs.filter (fun w => !l.valueHolds w) with
  | nil => simp [syncExplain, syncExplainList]
  | cons w ws =>
      cases hsl : syncExplainList trail s (w :: ws) with
      | none => simp [syncExplain_eq_syncExplainList, hsl]
      | some rs =>
          have hne : rs ≠ [] := by
            intro hnil
            have hlen := syncExplainList_length hsl
            rw [hnil] at hlen
            simp at hlen
          have hrev : rs.reverse ≠ [] := by simpa using hne
          simp [syncExplain_eq_syncExplainList, hsl, hrev, hne]

/-- Runtime twin of `syncClause` with structural, loop-compiled guards and a
lazy remover scan.  It is extensionally equal to `syncClause`
(`syncClauseFast_eq`), so installing it with `implemented_by` cannot change
any result. -/
def syncClauseFast (orig : List Domain) (bs : BranchState leaf) (lit : Literal) :
    Option Clause :=
  let s := lit.atom.slot
  match bs.frame.doms[s]? with
  | none => none
  | some d =>
    let l := lit.norm
    let tl := trailOnSlot bs.trail s
    if !d.isEmpty && valueAllFast l.valueHolds (Dom.enum d)
        && !(tl.any fun e => impliesP orig e.literal l) then
      (syncExplainDom tl s l (Dom.enum (orig.getD s Dom.empty))).map (l :: ·)
    else none

/-- `syncClauseFast` is the same function as `syncClause` (for every leaf
predicate): the fast guards are the same Boolean conditions (with the
loop-compiled `all`), and the explanation search is the domain-shaped twin
of `syncExplain` over the same rejected-value list. -/
theorem syncClauseFast_eq (leaf : Assignment → Bool) :
    @syncClauseFast leaf = @syncClause leaf := by
  funext orig bs lit
  unfold syncClauseFast syncClause
  dsimp only
  cases hd : bs.frame.doms[lit.atom.slot]? with
  | none => rfl
  | some d =>
    dsimp only
    rw [valueAllFast_eq]
    by_cases he : d.isEmpty = true
    · simp [he]
    · have he' : d.isEmpty = false := by simpa using he
      by_cases ha : (Dom.enum d).all lit.norm.valueHolds = true
      · by_cases ht : (trailOnSlot bs.trail lit.atom.slot).any
            (fun e => impliesP orig e.literal lit.norm) = true
        · simp [he', ha, ht]
        · have ht' : (trailOnSlot bs.trail lit.atom.slot).any
              (fun e => impliesP orig e.literal lit.norm) = false := by
            simpa using ht
          simp only [he', ha, ht', Bool.not_true, Bool.not_false, Bool.true_and,
            Bool.false_and, Bool.false_eq_true]
          rw [syncExplainDom_eq]
          by_cases hW : (Dom.enum (orig[lit.atom.slot]?.getD Dom.empty)).filter
              (fun w => !lit.norm.valueHolds w) = []
          · have hno : ¬ ∃ x, x ∈ Dom.enum (orig[lit.atom.slot]?.getD Dom.empty) ∧
                lit.norm.valueHolds x = false := by
              rw [List.filter_eq_nil_iff] at hW
              rintro ⟨x, hx, hpx⟩
              exact hW x hx (by simp [hpx])
            simp [hW, hno]
          · obtain ⟨w, ws, hW'⟩ := List.exists_cons_of_ne_nil hW
            simp [hW', List.mem_filter]
      · simp [he', ha]

attribute [implemented_by syncClauseFast] syncClause

/-! ### K1: structural domain guards (class E twin)

`syncClauseFast` tests `valueAllFast l.valueHolds (Dom.enum d)`, which
materialises the whole current domain once per candidate.  On a `.holes`
domain every value is an integer, so the three hot literal shapes reduce to
a bound, a membership test or a complement of one — all structural on the
representation.  The remaining shapes (Boolean literals, fixing literals on
a singleton) keep the enumeration: the singleton costs one value, and a
Boolean literal never targets a wide integer domain in `syncCands`. -/

/-- Structural `valueAllFast l.valueHolds` on the current domain. -/
def valueAllDom (l : Literal) (d : Dom) : Bool :=
  match d.rep with
  | .holes _ _ _ =>
      match l.atom, l.positive with
      | .intLe _ upper, true =>
          match Dom.maxInt? d with
          | some m => decide (m ≤ upper)
          | none => true
      | .intLe _ upper, false =>
          match Dom.minInt? d with
          | some m => decide (upper < m)
          | none => true
      | .intNe _ x, true => !(Dom.memBool d (.int x))
      | _, _ => valueAllFast l.valueHolds (Dom.enum d)
  | _ => valueAllFast l.valueHolds (Dom.enum d)

theorem valueAllDom_eq (l : Literal) (d : Dom) :
    valueAllDom l d = valueAllFast l.valueHolds (Dom.enum d) := by
  unfold valueAllDom
  rw [valueAllFast_eq]
  cases hrep : d.rep with
  | small isBool off bits => simp only [hrep]
  | general vs => simp only [hrep]
  | holes lo hi hs =>
    have hd : d = ⟨.holes lo hi hs⟩ := by
      cases d with
      | mk r => simp_all
    subst hd
    cases l with
    | mk atom positive =>
      cases atom with
      | boolEq s b => rfl
      | intLe s upper =>
        cases positive with
        | true =>
          dsimp only
          -- all values ≤ upper iff the maximum is
          generalize hmax : Dom.maxInt? ⟨.holes lo hi hs⟩ = mx
          cases mx with
          | none =>
              have hnone : (Dom.domInts ⟨.holes lo hi hs⟩).max? = none := by
                rw [← Dom.maxInt?_eq_domInts_max]; exact hmax
              rw [Dom.domInts_max?_eq_none_iff] at hnone
              have hempty : Dom.enum ⟨.holes lo hi hs⟩ = [] := by
                cases he : Dom.enum ⟨.holes lo hi hs⟩ with
                | nil => rfl
                | cons v vs =>
                    have hmem : v ∈ Dom.enum ⟨.holes lo hi hs⟩ := by
                      rw [he]; exact List.mem_cons_self
                    obtain ⟨i, rfl⟩ := Dom.eq_int_of_mem_holes_enum hmem
                    have hv := hnone (.int i) hmem
                    simp [Dom.valueIntView] at hv
              rw [hempty]
              rfl
          | some m =>
              dsimp only
              have hspec := Dom.domInts_max?_eq_some_iff.mp (by
                rw [← Dom.maxInt?_eq_domInts_max]; exact hmax)
              apply Bool.eq_iff_iff.mpr
              rw [List.all_eq_true]
              constructor
              · intro hle v hv
                obtain ⟨i, rfl⟩ := Dom.eq_int_of_mem_holes_enum hv
                rw [Dom.valueHolds_intLe_pos]
                exact decide_eq_true (by
                  have hle' : m ≤ upper := of_decide_eq_true hle
                  have := hspec.2 _ hv i rfl
                  omega)
              · intro hall
                obtain ⟨v, hv, hvm⟩ := hspec.1
                obtain ⟨i, rfl⟩ := Dom.eq_int_of_mem_holes_enum hv
                have hi : i = m := by simpa [Dom.valueIntView] using hvm
                have h := hall (.int i) hv
                rw [Dom.valueHolds_intLe_pos] at h
                rw [hi] at h
                exact h
        | false =>
          dsimp only
          -- all values > upper iff the minimum is
          generalize hmin : Dom.minInt? ⟨.holes lo hi hs⟩ = mn
          cases mn with
          | none =>
              have hnone : (Dom.domInts ⟨.holes lo hi hs⟩).min? = none := by
                rw [← Dom.minInt?_eq_domInts_min]; exact hmin
              rw [Dom.domInts_min?_eq_none_iff] at hnone
              have hempty : Dom.enum ⟨.holes lo hi hs⟩ = [] := by
                cases he : Dom.enum ⟨.holes lo hi hs⟩ with
                | nil => rfl
                | cons v vs =>
                    have hmem : v ∈ Dom.enum ⟨.holes lo hi hs⟩ := by
                      rw [he]; exact List.mem_cons_self
                    obtain ⟨i, rfl⟩ := Dom.eq_int_of_mem_holes_enum hmem
                    have hv := hnone (.int i) hmem
                    simp [Dom.valueIntView] at hv
              rw [hempty]
              rfl
          | some m =>
              dsimp only
              have hspec := Dom.domInts_min?_eq_some_iff.mp (by
                rw [← Dom.minInt?_eq_domInts_min]; exact hmin)
              apply Bool.eq_iff_iff.mpr
              rw [List.all_eq_true]
              constructor
              · intro hlt v hv
                obtain ⟨i, rfl⟩ := Dom.eq_int_of_mem_holes_enum hv
                rw [Dom.valueHolds_intLe_neg]
                exact decide_eq_true (by
                  have hlt' : upper < m := of_decide_eq_true hlt
                  have := hspec.2 _ hv i rfl
                  omega)
              · intro hall
                obtain ⟨v, hv, hvm⟩ := hspec.1
                obtain ⟨i, rfl⟩ := Dom.eq_int_of_mem_holes_enum hv
                have hi : i = m := by simpa [Dom.valueIntView] using hvm
                have h := hall (.int i) hv
                rw [Dom.valueHolds_intLe_neg] at h
                rw [hi] at h
                exact h
      | intNe s x =>
        cases positive with
        | true =>
          dsimp only
          -- positive disequality: no value equals `x`
          apply Bool.eq_iff_iff.mpr
          rw [List.all_eq_true]
          constructor
          · intro hb v hv
            have hfalse : Dom.memBool ⟨.holes lo hi hs⟩ (.int x) = false := by
              cases hmb : Dom.memBool ⟨.holes lo hi hs⟩ (.int x) with
              | false => rfl
              | true => simp [hmb] at hb
            obtain ⟨i, rfl⟩ := Dom.eq_int_of_mem_holes_enum hv
            rw [Dom.valueHolds_intNe_pos]
            refine decide_eq_true ?_
            intro hix
            have hmem : Dom.memBool ⟨.holes lo hi hs⟩ (.int x) = true :=
              (Dom.memBool_iff _ _).mpr (by rwa [hix] at hv)
            rw [hfalse] at hmem
            exact absurd hmem (by simp)
          · intro hall
            rw [Bool.not_eq_true']
            cases hmb : Dom.memBool ⟨.holes lo hi hs⟩ (.int x) with
            | false => rfl
            | true =>
                have hx : (.int x) ∈ Dom.enum ⟨.holes lo hi hs⟩ :=
                  (Dom.memBool_iff _ _).mp hmb
                have hbad := hall (.int x) hx
                rw [Dom.valueHolds_intNe_pos] at hbad
                simp at hbad
        | false =>
          -- negative disequality: fixing literal, enumeration is a singleton
          rfl

/-- Fast implication predicate for a non-Boolean slot: the truth-table
extension cannot fire, and the `slotBoolB` guard of `impliesBase` collapses
to `false`. -/
def impliesFast (t g : Literal) : Bool := litEqB t g || impliesLit t g

theorem impliesP_eq_impliesFast {orig : List Domain} {s : Nat} {g : Literal}
    (hbs : slotBoolB orig s = false) (hgs : g.atom.slot = s)
    (hgb : g.boolKind = false) :
    ∀ t : Literal, t.atom.slot = s →
      impliesP orig t g = impliesFast t g := by
  intro t ht
  cases g with
  | mk gatom gpos =>
    cases gatom with
    | boolEq s' b => simp [Literal.boolKind] at hgb
    | intLe s' u =>
      simp only [Atom.slot] at hgs
      cases t with
      | mk atom positive =>
        simp only [Atom.slot] at ht
        cases atom <;> cases positive <;>
          simp [impliesP, impliesBase, boolSlotImp, impliesFast, impliesLit, Literal.boolKind,
            Literal.intForm, litEqB, Atom.slot, hbs, hgb, hgs, ht,
            booleanSlotB_eq_slotBoolB]
    | intNe s' u =>
      simp only [Atom.slot] at hgs
      cases t with
      | mk atom positive =>
        simp only [Atom.slot] at ht
        cases atom <;> cases positive <;>
          simp [impliesP, impliesBase, boolSlotImp, impliesFast, impliesLit, Literal.boolKind,
            Literal.intForm, litEqB, Atom.slot, hbs, hgb, hgs, ht,
            booleanSlotB_eq_slotBoolB]

theorem any_impliesP_eq_any_impliesFast {orig : List Domain} {s : Nat}
    {g : Literal} (hbs : slotBoolB orig s = false) (hgs : g.atom.slot = s)
    (hgb : g.boolKind = false) {tl : List TrailEntry}
    (htl : ∀ e ∈ tl, e.literal.atom.slot = s) :
    tl.any (fun e => impliesP orig e.literal g)
      = tl.any (fun e => impliesFast e.literal g) := by
  induction tl with
  | nil => rfl
  | cons e es ih =>
      have he : e.literal.atom.slot = s := htl e (by simp)
      have hes : ∀ e' ∈ es, e'.literal.atom.slot = s :=
        fun e' h' => htl e' (by simp [h'])
      rw [List.any_cons, List.any_cons,
        impliesP_eq_impliesFast hbs hgs hgb e.literal he, ih hes]

/-- Every entry of a slot-filtered trail lives on that slot. -/
theorem trailOnSlot_mem_slot {trail : List TrailEntry} {s : Nat} {e : TrailEntry}
    (h : e ∈ trailOnSlot trail s) : e.literal.atom.slot = s := by
  unfold trailOnSlot at h
  rw [List.mem_filter] at h
  exact beq_iff_eq.mp h.2

/-- Filtering the appended entry: the K1 threaded trail update. -/
theorem trailOnSlot_append (trail : List TrailEntry) (e : TrailEntry) (s : Nat) :
    trailOnSlot (trail ++ [e]) s
      = trailOnSlot trail s ++ [e].filter (fun x => x.literal.atom.slot == s) := by
  unfold trailOnSlot
  rw [List.filter_append]

/-- `syncClause`'s twin with the slot trail and the slot's Boolean-ness
threaded in.  When the slot is not Boolean in the original domains and the
literal is not a Boolean atom, the truth-table `boolSlotImp` cannot fire and
`slotBoolB` is `false`, so the implication scan uses `impliesFast`; the
current-domain guard uses the structural `valueAllDom` instead of
materialising the domain.  The other cases fall back to the reference
predicates. -/
def syncClauseWithTrail (orig : List Domain) (bs : BranchState leaf)
    (tl : List TrailEntry) (bslot : Bool) (lit : Literal) : Option Clause :=
  let s := lit.atom.slot
  match bs.frame.doms[s]? with
  | none => none
  | some d =>
    let l := lit.norm
    if !bslot && !l.boolKind then
      if !d.isEmpty && valueAllDom l d &&
          !(tl.any fun e => impliesFast e.literal l) then
        (syncExplainDom tl s l (Dom.enum (orig.getD s Dom.empty))).map (l :: ·)
      else none
    else
      if !d.isEmpty && valueAllFast l.valueHolds (Dom.enum d) &&
          !(tl.any fun e => impliesP orig e.literal l) then
        (syncExplainDom tl s l (Dom.enum (orig.getD s Dom.empty))).map (l :: ·)
      else none

/-- `syncClauseWithTrail` is `syncClauseFast` when the threaded trail is the
slot-filtered one and `bslot` is the slot's original Boolean-ness. -/
theorem syncClauseWithTrail_eq_syncClauseFast {orig : List Domain}
    {bs : BranchState leaf} {s : Nat} {tl : List TrailEntry} {bslot : Bool}
    {lit : Literal} (hslot : lit.atom.slot = s)
    (htl : tl = trailOnSlot bs.trail s) (hbslot : bslot = slotBoolB orig s) :
    syncClauseWithTrail orig bs tl bslot lit = syncClauseFast orig bs lit := by
  unfold syncClauseWithTrail syncClauseFast
  dsimp only
  cases hd : bs.frame.doms[lit.atom.slot]? with
  | none => rfl
  | some d =>
    dsimp only
    rw [hslot]
    by_cases hfast : (!bslot && !lit.norm.boolKind) = true
    · rw [if_pos hfast]
      have hb1 : slotBoolB orig s = false := by
        have h := hfast
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
        rw [hbslot] at h
        exact h.1
      have hb2 : lit.norm.boolKind = false := by
        have h := hfast
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
        exact h.2
      have hmem : ∀ e ∈ tl, e.literal.atom.slot = s := by
        intro e he
        rw [htl] at he
        exact trailOnSlot_mem_slot he
      have hany : tl.any (fun e => impliesP orig e.literal lit.norm)
          = tl.any (fun e => impliesFast e.literal lit.norm) :=
        any_impliesP_eq_any_impliesFast hb1 (by rw [norm_atom_slot, hslot]) hb2 hmem
      rw [valueAllDom_eq, ← hany, htl]
    · rw [if_neg hfast, htl]

/-- Push one synchronised literal with the slot trail threaded through. -/
def syncOneWithTrail (orig : List Domain) (bs : BranchState leaf)
    (tl : List TrailEntry) (bslot : Bool) (lit : Literal) :
    BranchState leaf × List TrailEntry :=
  match syncClauseWithTrail orig bs tl bslot lit with
  | some c =>
      let e : TrailEntry :=
        { literal := lit.norm, level := bs.level, reason := some { clause := c } }
      (narrowState bs bs.frame lit c [],
       tl ++ [e].filter (fun x => x.literal.atom.slot == lit.atom.slot))
  | none => (bs, tl)

/-- Push one synchronised literal (an enqueue at the unchanged frame). -/
def syncOne (orig : List Domain) (bs : BranchState leaf) (lit : Literal) :
    BranchState leaf :=
  match syncClause orig bs lit with
  | some c => narrowState bs bs.frame lit c []
  | none => bs

/-- The state component of `syncOneWithTrail` is `syncOne`'s. -/
theorem syncOneWithTrail_fst_eq {orig : List Domain} {bs : BranchState leaf}
    {s : Nat} {lit : Literal} {tl : List TrailEntry} {bslot : Bool}
    (hslot : lit.atom.slot = s) (htl : tl = trailOnSlot bs.trail s)
    (hbslot : bslot = slotBoolB orig s) :
    (syncOneWithTrail orig bs tl bslot lit).1 = syncOne orig bs lit := by
  have hcs : syncClauseWithTrail orig bs tl bslot lit = syncClause orig bs lit := by
    rw [syncClauseWithTrail_eq_syncClauseFast hslot htl hbslot]
    exact congrFun (congrFun (congrFun (syncClauseFast_eq leaf) orig) bs) lit
  unfold syncOneWithTrail syncOne
  rw [hcs]
  cases hc : syncClause orig bs lit <;> rfl

/-- The trail component of `syncOneWithTrail` is again the slot-filtered
trail of the resulting state. -/
theorem syncOneWithTrail_snd_eq {orig : List Domain} {bs : BranchState leaf}
    {s : Nat} {lit : Literal} {tl : List TrailEntry} {bslot : Bool}
    (hslot : lit.atom.slot = s) (htl : tl = trailOnSlot bs.trail s)
    (hbslot : bslot = slotBoolB orig s) :
    (syncOneWithTrail orig bs tl bslot lit).2
      = trailOnSlot (syncOne orig bs lit).trail s := by
  have hcs : syncClauseWithTrail orig bs tl bslot lit = syncClause orig bs lit := by
    rw [syncClauseWithTrail_eq_syncClauseFast hslot htl hbslot]
    exact congrFun (congrFun (congrFun (syncClauseFast_eq leaf) orig) bs) lit
  unfold syncOneWithTrail syncOne
  rw [hcs]
  cases hc : syncClause orig bs lit with
  | none => exact htl
  | some c =>
      dsimp only
      rw [htl]
      simp only [narrowState]
      rw [trailOnSlot_append, ← hslot]


/-- The candidate literals of slot `s`: lower bound, upper bound, fixing.
Each is only offered when its threshold/value is an ORIGINAL value of the
slot (so every candidate lies in the literal pool of the box, whatever the
frame is). -/
def syncCands (orig : List Domain) (f : BranchFrame) (s : Nat) : List Literal :=
  if s < orig.length then
    match f.doms[s]? with
    | none => []
    | some d =>
      let od := orig.getD s Dom.empty
      let oints := (Dom.enum od).filterMap Value.intView
      let ints := (Dom.enum d).filterMap Value.intView
      (match ints.min? with
        | some lo => if lo ∈ oints then [negLe s (lo - 1)] else []
        | none => [])
      ++ (match ints.max? with
        | some hi => if hi ∈ oints then [posLe s hi] else []
        | none => [])
      ++ (match Dom.enum d with
          | [.int i] => if i ∈ oints then (valueLiteral s (.int i)).toList else []
          | [.bool b] => (valueLiteral s (.bool b)).toList
          | _ => [])
      ++ (match ints.min?, ints.max? with
          | some lo, some hi =>
              (oints.filter fun h => decide (lo < h) && decide (h < hi) &&
                !(ints.contains h)).eraseDups.map (posNe s)
          | _, _ => [])
  else []

/-- Inversion of candidate membership. -/
theorem syncCands_cases_k1 {orig : List Domain} {f : BranchFrame} {s : Nat}
    {lit : Literal} (h : lit ∈ syncCands orig f s) :
    s < orig.length ∧ ∃ d, f.doms[s]? = some d ∧
      ((∃ lo, ((Dom.enum d).filterMap Value.intView).min? = some lo ∧
          lo ∈ ((Dom.enum (orig.getD s Dom.empty)).filterMap Value.intView) ∧
            lit = negLe s (lo - 1)) ∨
       (∃ hi, ((Dom.enum d).filterMap Value.intView).max? = some hi ∧
          hi ∈ ((Dom.enum (orig.getD s Dom.empty)).filterMap Value.intView) ∧
            lit = posLe s hi) ∨
       (∃ i, Dom.enum d = [Value.int i] ∧
          i ∈ ((Dom.enum (orig.getD s Dom.empty)).filterMap Value.intView) ∧
            lit = negNe s i) ∨
       (∃ b, Dom.enum d = [Value.bool b] ∧ lit = posBool s b) ∨
       (∃ lo hi h, ((Dom.enum d).filterMap Value.intView).min? = some lo ∧
          ((Dom.enum d).filterMap Value.intView).max? = some hi ∧
          h ∈ ((Dom.enum (orig.getD s Dom.empty)).filterMap Value.intView) ∧
            lit = posNe s h)) := by
  unfold syncCands at h
  by_cases hc : s < orig.length
  · rw [if_pos hc] at h
    refine ⟨hc, ?_⟩
    cases hd : f.doms[s]? with
    | none => rw [hd] at h; simp at h
    | some d =>
      rw [hd] at h
      refine ⟨d, rfl, ?_⟩
      simp only [List.mem_append] at h
      rcases h with ((h | h) | h) | h
      · left
        cases hm : ((Dom.enum d).filterMap Value.intView).min? with
        | none => simp [hm] at h
        | some lo =>
          simp only [hm] at h
          by_cases hl : lo ∈ ((Dom.enum (orig.getD s Dom.empty)).filterMap Value.intView)
          · rw [if_pos hl] at h
            simp only [List.mem_singleton] at h
            exact ⟨lo, rfl, hl, h⟩
          · rw [if_neg hl] at h; simp at h
      · right; left
        cases hm : ((Dom.enum d).filterMap Value.intView).max? with
        | none => simp [hm] at h
        | some hi =>
          simp only [hm] at h
          by_cases hl : hi ∈ ((Dom.enum (orig.getD s Dom.empty)).filterMap Value.intView)
          · rw [if_pos hl] at h
            simp only [List.mem_singleton] at h
            exact ⟨hi, rfl, hl, h⟩
          · rw [if_neg hl] at h; simp at h
      · right; right
        cases hde : Dom.enum d with
        | nil => simp [hde] at h
        | cons v rest =>
          cases rest with
          | nil =>
            cases v with
            | int i =>
              simp only [hde] at h
              by_cases hv : i ∈ ((Dom.enum (orig.getD s Dom.empty)).filterMap Value.intView)
              · rw [if_pos hv] at h
                simp only [valueLiteral, Option.toList_some, List.mem_singleton] at h
                exact Or.inl ⟨i, rfl, hv, h⟩
              · rw [if_neg hv] at h; simp at h
            | bool b =>
              simp only [hde, valueLiteral, Option.toList_some,
                List.mem_singleton] at h
              exact Or.inr (Or.inl ⟨b, rfl, h⟩)
            | setOfInt _ => simp [hde] at h
            | array _ => simp [hde] at h
          | cons w rest => simp [hde] at h
      · right; right; right; right
        cases hm : ((Dom.enum d).filterMap Value.intView).min? with
        | none => simp [hm] at h
        | some lo =>
          cases hM : ((Dom.enum d).filterMap Value.intView).max? with
          | none => simp [hm, hM] at h
          | some hi =>
            simp only [hm, hM, List.mem_map] at h
            obtain ⟨h0, hh0, rfl⟩ := h
            have := List.mem_eraseDups.mp hh0
            exact ⟨lo, hi, h0, rfl, rfl, (List.mem_filter.mp this).1, rfl⟩
  · rw [if_neg hc] at h; simp at h

theorem syncCands_slot_k1 {orig : List Domain} {f : BranchFrame} {s : Nat} :
    ∀ lit ∈ syncCands orig f s, lit.atom.slot = s := by
  intro lit hlit
  obtain ⟨-, d, -, h⟩ := syncCands_cases_k1 hlit
  rcases h with ⟨lo, -, -, rfl⟩ | ⟨hi, -, -, rfl⟩ | ⟨i, -, -, rfl⟩ | ⟨b, -, rfl⟩ |
    ⟨lo, hi, h, -, -, -, rfl⟩ <;> rfl


/-- Every strictly interior integer of the materialised interval
`lo, ..., lo + n - 1` is a member. -/
theorem rangeInts_contains_of_lt_of_lt {lo hi h : Int}
    (hlo : lo < h) (hhi : h < hi) :
    (rangeInts lo ((hi - lo + 1).toNat)).contains h = true := by
  rw [List.contains_iff_mem, rangeInts_mem]
  refine ⟨(h - lo).toNat, ?_, ?_⟩
  · rw [Int.toNat_lt_toNat (by omega)]
    omega
  · rw [Int.toNat_of_nonneg (by omega)]
    omega

/-- When the current integer domain is exactly the interval with endpoints
`lo`/`hi`, the hole filter of `syncCands` is empty: every strictly interior
`h` is already present in `ints`. -/
theorem syncCands_hole_filter_eq_nil {oints ints : List Int} {lo hi : Int}
    (hints : ints = rangeInts lo ((hi - lo + 1).toNat)) :
    (oints.filter fun h => decide (lo < h) && decide (h < hi) &&
      !(ints.contains h)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro h _
  rw [hints]
  by_cases h1 : lo < h
  · by_cases h2 : h < hi
    · rw [rangeInts_contains_of_lt_of_lt h1 h2]; simp
    · simp [h2]
  · simp [h1]

/-- Integer views of an integer list mapped through `Value.int` round-trip
to the original list (used to relate the compact enumerations to
`filterMap Value.intView`). -/
theorem filterMap_intView_map_int (L : List Int) :
    (L.map Value.int).filterMap Value.intView = L := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
      change x :: (List.map Value.int xs).filterMap Value.intView = x :: xs
      rw [ih]

/-- Exactness of `memIntViewB` against the `Value.intView` image. -/
theorem memIntViewB_iff (d : Dom) (i : Int) :
    memIntViewB d i = true ↔ i ∈ (Dom.enum d).filterMap Value.intView :=
  memIntViewB_iff_intView d i

/-- Replacing the `ints.contains` test by the structural `memIntViewB` test
does not change the hole filter, provided `ints` is the int-view image of the
same domain. -/
theorem syncCands_filter_memIntViewB {oints ints : List Int} {d : Dom}
    {lo hi : Int} (hints : ints = (Dom.enum d).filterMap Value.intView) :
    (oints.filter fun h => decide (lo < h) && decide (h < hi) &&
      !(memIntViewB d h))
    = (oints.filter fun h => decide (lo < h) && decide (h < hi) &&
        !(ints.contains h)) := by
  subst hints
  apply List.filter_congr
  intro h _
  have hbeq : memIntViewB d h =
      ((Dom.enum d).filterMap Value.intView).contains h := by
    rw [List.contains_eq_mem]
    cases hb : memIntViewB d h with
    | false =>
        have hnot : h ∉ (Dom.enum d).filterMap Value.intView := by
          intro hc
          rw [(memIntViewB_iff d h).mpr hc] at hb
          exact Bool.noConfusion hb
        simp [hnot]
    | true =>
        have hmem : h ∈ (Dom.enum d).filterMap Value.intView :=
          (memIntViewB_iff d h).mp hb
        simp [hmem]
  rw [hbeq]

/-- Structural membership bridge: `memIntViewB` is the `decide` of membership
in `Dom.domInts`. -/
theorem memIntViewB_eq_decide_domInts (d : Dom) (i : Int) :
    memIntViewB d i = decide (i ∈ Dom.domInts d) := by
  rw [Dom.domInts_eq_intView]
  cases h : memIntViewB d i with
  | false =>
      have hnot : ¬ i ∈ (Dom.enum d).filterMap Value.intView := by
        intro hm
        rw [(memIntViewB_iff d i).mpr hm] at h
        exact Bool.noConfusion h
      simp [h, hnot]
  | true =>
      have hm : i ∈ (Dom.enum d).filterMap Value.intView := (memIntViewB_iff d i).mp h
      simp [h, hm]

/-- `domInts` of a hole interval is its interval enumeration. -/
theorem domInts_holes (lo hi : Int) (hs : List Int) :
    Dom.domInts ⟨.holes lo hi hs⟩ = Dom.holesInts lo hi hs := by
  rw [Dom.domInts_eq_intView]
  show ((Dom.holesInts lo hi hs).map Value.int).filterMap Value.intView = _
  rw [filterMap_intView_map_int]

/-- The hole-difference values of `syncCands`, computed without enumerating a
wide original interval.  When the original domain is a hole interval:

* a current `.holes` domain removes exactly its (sorted) hole list from the
  current interval, so the candidates are those holes that are original
  integers;
* a current `.small` integer window has at most 64 values, so enumerating the
  window between its bounds is cheap;
* every other shape falls back to the enumeration.

With a non-hole original domain the enumeration is already small (a 64-bit
window, two Booleans, or the general fallback list). -/
def syncHoleVals (od d : Dom) (lo hi : Int) : List Int :=
  match od.rep with
  | .holes _ _ _ =>
      match d.rep with
      | .holes _ _ hs =>
          if Dom.sortedIntsB hs then
            hs.filter fun h => decide (lo < h) && decide (h < hi) && memIntViewB od h
          else
            (Dom.domInts od).filter fun h =>
              decide (lo < h) && decide (h < hi) && !(memIntViewB d h)
      | .small false _ _ =>
          (rangeInts (lo + 1) (hi - lo - 1).toNat).filter fun h =>
            memIntViewB od h && !(memIntViewB d h)
      | _ =>
          (Dom.domInts od).filter fun h =>
            decide (lo < h) && decide (h < hi) && !(memIntViewB d h)
  | _ =>
      (Dom.domInts od).filter fun h =>
        decide (lo < h) && decide (h < hi) && !(memIntViewB d h)

/-- Exactness of `syncHoleVals` against the enumerating hole filter, for
current bounds given by the current domain's extrema. -/
theorem syncHoleVals_eq {od d : Dom} {lo hi : Int}
    (hmin : (Dom.domInts d).min? = some lo)
    (hmax : (Dom.domInts d).max? = some hi) :
    syncHoleVals od d lo hi =
      (Dom.domInts od).filter (fun h =>
        decide (lo < h) && decide (h < hi) && !(memIntViewB d h)) := by
  unfold syncHoleVals
  cases od with
  | mk orep =>
    cases orep with
    | holes lo0 hi0 hs0 =>
      dsimp only
      cases d with
      | mk drep =>
        cases drep with
        | holes lo1 hi1 hs =>
          dsimp only
          by_cases hsorted : Dom.sortedIntsB hs = true
          · rw [if_pos hsorted]
            have hmin' : Dom.minInt? ⟨.holes lo1 hi1 hs⟩ = some lo := by
              rw [Dom.minInt?_eq_domInts_min]
              exact hmin
            have hmax' : Dom.maxInt? ⟨.holes lo1 hi1 hs⟩ = some hi := by
              rw [Dom.maxInt?_eq_domInts_max]
              exact hmax
            obtain ⟨vlo, hvlo, hvlo'⟩ := (Dom.minInt?_eq_some_iff.mp hmin').1
            have hlo1 : lo1 ≤ lo := Dom.holes_min_le vlo hvlo lo hvlo'
            obtain ⟨vhi, hvhi, hvhi'⟩ := (Dom.maxInt?_eq_some_iff.mp hmax').1
            have hhi1 : hi ≤ hi1 := Dom.holes_max_ge vhi hvhi hi hvhi'
            apply eq_of_pairwise_lt_of_mem_iff
            · exact List.Pairwise.filter _ (Dom.sortedIntsB_iff.mp hsorted)
            · rw [domInts_holes]
              exact List.Pairwise.filter _ (Dom.pairwise_holesInts lo0 hi0 hs0)
            · intro x
              rw [List.mem_filter, List.mem_filter]
              simp only [Bool.and_eq_true, decide_eq_true_eq]
              constructor
              · rintro ⟨hxhs, ⟨hxlo, hxhi⟩, hmemod⟩
                have hnotd : memIntViewB ⟨.holes lo1 hi1 hs⟩ x = false := by
                  by_cases hmd : memIntViewB ⟨.holes lo1 hi1 hs⟩ x = true
                  · have hxdom : x ∈ Dom.domInts ⟨.holes lo1 hi1 hs⟩ :=
                      (memIntViewB_iff _ x).mp hmd
                    rw [domInts_holes] at hxdom
                    exact absurd ((Dom.mem_holesInts.mp hxdom).2.2 hxhs) (by simp)
                  · simpa using hmd
                refine ⟨?_, ⟨hxlo, hxhi⟩, ?_⟩
                · exact (memIntViewB_iff ⟨.holes lo0 hi0 hs0⟩ x).mp hmemod
                · rw [hnotd]; rfl
              · rintro ⟨hxoints, ⟨hxlo, hxhi⟩, hnotd⟩
                have hxhs : x ∈ hs := by
                  by_cases hx : x ∈ hs
                  · exact hx
                  · exfalso
                    have hxdom : x ∈ Dom.domInts ⟨.holes lo1 hi1 hs⟩ := by
                      rw [domInts_holes, Dom.mem_holesInts]
                      exact ⟨by omega, by omega, hx⟩
                    have hmemd : memIntViewB ⟨.holes lo1 hi1 hs⟩ x = true :=
                      (memIntViewB_iff _ x).mpr hxdom
                    rw [hmemd] at hnotd
                    exact absurd hnotd (by simp)
                have hmemod : memIntViewB ⟨.holes lo0 hi0 hs0⟩ x = true :=
                  (memIntViewB_iff _ x).mpr hxoints
                exact ⟨hxhs, ⟨hxlo, hxhi⟩, hmemod⟩
          · rw [if_neg hsorted]
        | small isBool off bits =>
          dsimp only
          cases isBool with
          | false =>
            apply eq_of_pairwise_lt_of_mem_iff
            · exact List.Pairwise.filter _ (rangeInts_pairwise (lo + 1) (hi - lo - 1).toNat)
            · rw [domInts_holes]
              exact List.Pairwise.filter _ (Dom.pairwise_holesInts lo0 hi0 hs0)
            · intro x
              rw [List.mem_filter, List.mem_filter, Dom.mem_rangeInts_gap]
              simp only [Bool.and_eq_true, decide_eq_true_eq]
              constructor
              · rintro ⟨⟨hxlo, hxhi⟩, hmod, hnotd⟩
                refine ⟨?_, ⟨hxlo, hxhi⟩, hnotd⟩
                exact (memIntViewB_iff ⟨.holes lo0 hi0 hs0⟩ x).mp hmod
              · rintro ⟨hxoints, ⟨hxlo, hxhi⟩, hnotd⟩
                refine ⟨⟨hxlo, hxhi⟩, ?_, hnotd⟩
                exact (memIntViewB_iff ⟨.holes lo0 hi0 hs0⟩ x).mpr hxoints
          | true => rfl
        | general vs => rfl
    | small isBool off bits => rfl
    | general vs => rfl

/-- The lower-bound branch of the fast candidate list, rewritten in
structural form. -/
theorem syncCands_min_branch_eq (od d : Dom) (s : Nat) :
    (match Dom.minInt? d with
      | some lo => if memIntViewB od lo then [negLe s (lo - 1)] else []
      | none => [])
    = (match ((Dom.enum d).filterMap Value.intView).min? with
      | some lo => if lo ∈ ((Dom.enum od).filterMap Value.intView) then
          [negLe s (lo - 1)] else []
      | none => []) := by
  rw [show Dom.minInt? d = (Dom.domInts d).min? from Dom.minInt?_eq_domInts_min d]
  change (match (Dom.domInts d).min? with
      | some lo => if memIntViewB od lo then [negLe s (lo - 1)] else []
      | none => [])
    = (match (Dom.domInts d).min? with
      | some lo => if lo ∈ Dom.domInts od then [negLe s (lo - 1)] else []
      | none => [])
  cases h : (Dom.domInts d).min? with
  | none => rfl
  | some lo =>
      simp only [h]
      rw [memIntViewB_eq_decide_domInts]
      simp

/-- The upper-bound branch of the fast candidate list, rewritten in
structural form. -/
theorem syncCands_max_branch_eq (od d : Dom) (s : Nat) :
    (match Dom.maxInt? d with
      | some hi => if memIntViewB od hi then [posLe s hi] else []
      | none => [])
    = (match ((Dom.enum d).filterMap Value.intView).max? with
      | some hi => if hi ∈ ((Dom.enum od).filterMap Value.intView) then
          [posLe s hi] else []
      | none => []) := by
  rw [show Dom.maxInt? d = (Dom.domInts d).max? from Dom.maxInt?_eq_domInts_max d]
  change (match (Dom.domInts d).max? with
      | some hi => if memIntViewB od hi then [posLe s hi] else []
      | none => [])
    = (match (Dom.domInts d).max? with
      | some hi => if hi ∈ Dom.domInts od then [posLe s hi] else []
      | none => [])
  cases h : (Dom.domInts d).max? with
  | none => rfl
  | some hi =>
      simp only [h]
      rw [memIntViewB_eq_decide_domInts]
      simp

/-- The fixing branch of the fast candidate list, rewritten in structural
form (`intSingleton?` then `boolSingleton?`). -/
theorem syncCands_singleton_branch_eq (od d : Dom) (s : Nat) :
    (match Dom.intSingleton? d with
      | some i => if memIntViewB od i then (valueLiteral s (.int i)).toList else []
      | none =>
          match Dom.boolSingleton? d with
          | some b => (valueLiteral s (.bool b)).toList
          | none => [])
    = (match Dom.enum d with
      | [.int i] => if i ∈ ((Dom.enum od).filterMap Value.intView) then
          (valueLiteral s (.int i)).toList else []
      | [.bool b] => (valueLiteral s (.bool b)).toList
      | _ => []) := by
  rw [Dom.intSingleton?_eq, Dom.boolSingleton?_eq]
  cases h : Dom.enum d with
  | nil => rfl
  | cons v rest =>
      cases rest with
      | nil =>
          cases v with
          | int i =>
              simp only [h]
              rw [memIntViewB_eq_decide_domInts, Dom.domInts_eq_intView]
              simp
          | bool b => rfl
          | setOfInt st => rfl
          | array a => rfl
      | cons w ws => cases v <;> rfl

/-- The final (hole) branch of the fast candidate list, with the enumerating
`List.contains` membership replaced by the structural `memIntViewB` test. -/
theorem syncCands_hole_branch_eq (od d : Dom) (s : Nat) :
    (match Dom.minInt? d, Dom.maxInt? d with
      | some lo, some hi => (syncHoleVals od d lo hi).eraseDups.map (posNe s)
      | _, _ => [])
    = (match ((Dom.enum d).filterMap Value.intView).min?,
             ((Dom.enum d).filterMap Value.intView).max? with
      | some lo, some hi =>
          (((Dom.enum od).filterMap Value.intView).filter fun h =>
            decide (lo < h) && decide (h < hi) &&
              !(((Dom.enum d).filterMap Value.intView).contains h)).eraseDups.map (posNe s)
      | _, _ => []) := by
  change (match Dom.minInt? d, Dom.maxInt? d with
      | some lo, some hi => (syncHoleVals od d lo hi).eraseDups.map (posNe s)
      | _, _ => [])
    = (match (Dom.domInts d).min?, (Dom.domInts d).max? with
      | some lo, some hi =>
          ((Dom.domInts od).filter fun h =>
            decide (lo < h) && decide (h < hi) &&
              !((Dom.domInts d).contains h)).eraseDups.map (posNe s)
      | _, _ => [])
  rw [Dom.minInt?_eq_domInts_min, Dom.maxInt?_eq_domInts_max]
  cases h1 : (Dom.domInts d).min? with
  | none => rfl
  | some lo =>
      cases h2 : (Dom.domInts d).max? with
      | none => rfl
      | some hi =>
          dsimp only
          rw [← syncCands_filter_memIntViewB (d := d) (oints := Dom.domInts od)
            (ints := Dom.domInts d) (lo := lo) (hi := hi) (Dom.domInts_eq_intView d)]
          rw [syncHoleVals_eq h1 h2]

/-- Runtime twin of `syncCands` with all four candidate branches structural.
It is extensionally equal to `syncCands` (`syncCandsFast_eq`), so installing
it with `implemented_by` cannot change any result. -/
def syncCandsFast (orig : List Domain) (f : BranchFrame) (s : Nat) : List Literal :=
  if s < orig.length then
    match f.doms[s]? with
    | none => []
    | some d =>
      let od := orig.getD s Dom.empty
      (match Dom.minInt? d with
        | some lo => if memIntViewB od lo then [negLe s (lo - 1)] else []
        | none => [])
      ++ (match Dom.maxInt? d with
        | some hi => if memIntViewB od hi then [posLe s hi] else []
        | none => [])
      ++ (match Dom.intSingleton? d with
          | some i => if memIntViewB od i then (valueLiteral s (.int i)).toList else []
          | none =>
              match Dom.boolSingleton? d with
              | some b => (valueLiteral s (.bool b)).toList
              | none => [])
      ++ (match Dom.minInt? d, Dom.maxInt? d with
          | some lo, some hi =>
              (syncHoleVals od d lo hi).eraseDups.map (posNe s)
          | _, _ => [])
  else []

theorem syncCandsFast_eq : syncCandsFast = syncCands := by
  funext orig f s
  unfold syncCandsFast syncCands
  by_cases hs : s < orig.length
  · simp only [if_pos hs]
    cases hd : f.doms[s]? with
    | none => rfl
    | some d =>
      dsimp only
      rw [syncCands_min_branch_eq, syncCands_max_branch_eq, syncCands_singleton_branch_eq,
        syncCands_hole_branch_eq]
  · simp only [if_neg hs]

attribute [implemented_by syncCandsFast] syncCands

/-- Synchronise slot `s`: push its candidates in order. -/
def syncSlot (orig : List Domain) (bs : BranchState leaf) (s : Nat) :
    BranchState leaf :=
  (syncCands orig bs.frame s).foldl (syncOne orig) bs

/-- K1 twin of `syncSlot`: the slot-filtered trail and the slot's original
Boolean-ness are computed once, and each pushed entry is threaded into the
trail for the remaining candidates. -/
def syncSlotFastAux (orig : List Domain) (bs : BranchState leaf) (s : Nat)
    (cands : List Literal) (tl : List TrailEntry) (bslot : Bool) :
    BranchState leaf :=
  match cands with
  | [] => bs
  | lit :: rest =>
      let p := syncOneWithTrail orig bs tl bslot lit
      syncSlotFastAux orig p.1 s rest p.2 bslot

/-- K1 twin of `syncSlot`. -/
def syncSlotFast (orig : List Domain) (bs : BranchState leaf) (s : Nat) :
    BranchState leaf :=
  syncSlotFastAux orig bs s (syncCands orig bs.frame s)
    (trailOnSlot bs.trail s) (slotBoolB orig s)

theorem syncSlotFastAux_eq (orig : List Domain) (bs : BranchState leaf) (s : Nat)
    (cands : List Literal) (tl : List TrailEntry) (bslot : Bool)
    (hcands : ∀ lit ∈ cands, lit.atom.slot = s)
    (htl : tl = trailOnSlot bs.trail s) (hbslot : bslot = slotBoolB orig s) :
    syncSlotFastAux orig bs s cands tl bslot
      = cands.foldl (syncOne orig) bs := by
  induction cands generalizing bs tl bslot with
  | nil => rfl
  | cons lit rest ih =>
      have hslot : lit.atom.slot = s := hcands lit (by simp)
      have hrest : ∀ l ∈ rest, l.atom.slot = s :=
        fun l hl => hcands l (List.mem_cons_of_mem _ hl)
      have h1 := syncOneWithTrail_fst_eq hslot htl hbslot
      have h2 := syncOneWithTrail_snd_eq hslot htl hbslot
      rw [syncSlotFastAux, List.foldl_cons]
      cases hp : syncOneWithTrail orig bs tl bslot lit with
      | mk bs' tl' =>
          rw [hp] at h1 h2
          dsimp only at h1 h2
          rw [h1, h2]
          exact ih (syncOne orig bs lit) (trailOnSlot (syncOne orig bs lit).trail s)
            bslot hrest rfl hbslot

theorem syncSlotFast_eq :
    @syncSlotFast leaf = @syncSlot leaf := by
  funext orig bs s
  unfold syncSlotFast syncSlot
  exact syncSlotFastAux_eq orig bs s (syncCands orig bs.frame s)
    (trailOnSlot bs.trail s) (slotBoolB orig s)
    (fun lit hl => syncCands_slot_k1 lit hl) rfl rfl

attribute [implemented_by syncSlotFast] syncSlot

/-- Synchronise every remaining slot. -/
def syncAll (orig : List Domain) (bs : BranchState leaf) : BranchState leaf :=
  (List.range bs.frame.doms.length).foldl
    (fun b s => syncSlot orig b s) bs


/-! ## Specification of the explanation -/

theorem syncRemover_spec {trail : List TrailEntry} {s : Nat} {w : Value}
    {q : Literal} (h : syncRemover trail s w = some q) :
    (∃ e ∈ trail, q = e.literal.negate) ∧ q.atom.slot = s ∧
      q.valueHolds w = true := by
  rw [syncRemover, List.findRev?_eq_find?_reverse] at h
  obtain ⟨e, he, hq⟩ := Option.map_eq_some_iff.mp h
  have hmem := List.mem_of_find?_eq_some he
  have hp := List.find?_some he
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  refine ⟨⟨e, List.mem_reverse.mp hmem, hq.symm⟩, ?_, ?_⟩
  · rw [← hq]; exact hp.1
  · rw [← hq]; exact hp.2

theorem syncExplain_spec {trail : List TrailEntry} {s : Nat} {W : List Value}
    {ex : Clause} (h : syncExplain trail s W = some ex) :
    (∀ q ∈ ex, ∃ e ∈ trail, q = e.literal.negate) ∧
    (∀ w ∈ W, ∃ q ∈ ex, q.atom.slot = s ∧ q.valueHolds w = true) := by
  unfold syncExplain at h
  simp only at h
  by_cases hany : (W.map (syncRemover trail s)).any Option.isNone = true
  · rw [if_pos hany] at h
    cases h
  · rw [if_neg hany] at h
    cases h
    constructor
    · intro q hq
      obtain ⟨r, hr, hrq⟩ := List.mem_filterMap.mp (List.mem_eraseDups.mp hq)
      obtain ⟨w, _, hw⟩ := List.mem_map.mp hr
      simp only [id] at hrq
      subst hrq
      exact (syncRemover_spec hw).1
    · intro w hw
      have hnn : syncRemover trail s w ≠ none := by
        intro hn
        apply hany
        exact List.any_eq_true.mpr ⟨none, List.mem_map.mpr ⟨w, hw, hn⟩, rfl⟩
      obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hnn
      obtain ⟨-, hs, hv⟩ := syncRemover_spec hq
      refine ⟨q, List.mem_eraseDups.mpr (List.mem_filterMap.mpr
        ⟨some q, List.mem_map.mpr ⟨w, hw, hq⟩, rfl⟩), hs, hv⟩

/-- Unpacking a justified push. -/
theorem syncClause_spec {orig : List Domain} {bs : BranchState leaf}
    {lit : Literal} {c : Clause} (h : syncClause orig bs lit = some c) :
    ∃ d ex, bs.frame.doms[lit.atom.slot]? = some d ∧
      d.isEmpty = false ∧ (Dom.enum d).all lit.norm.valueHolds = true ∧
      (∀ e ∈ bs.trail, impliesP orig e.literal lit.norm = false) ∧
      syncExplain bs.trail lit.atom.slot
        ((Dom.enum (orig.getD lit.atom.slot Dom.empty)).filter
          fun w => !lit.norm.valueHolds w)
          = some ex ∧
      c = lit.norm :: ex := by
  unfold syncClause at h
  simp only at h
  cases hd : bs.frame.doms[lit.atom.slot]? with
  | none => rw [hd] at h; cases h
  | some d =>
    rw [hd] at h
    simp only at h
    by_cases hg : (!d.isEmpty && (Dom.enum d).all lit.norm.valueHolds
        && !((Dom.enum (orig.getD lit.atom.slot Dom.empty)).filter
              fun w => !lit.norm.valueHolds w).isEmpty
        && !((trailOnSlot bs.trail lit.atom.slot).any
              fun e => impliesP orig e.literal lit.norm)) = true
    · rw [if_pos hg] at h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hg
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hg
      cases hx : syncExplain (trailOnSlot bs.trail lit.atom.slot) lit.atom.slot
          ((Dom.enum (orig.getD lit.atom.slot Dom.empty)).filter
            fun w => !lit.norm.valueHolds w) with
      | none => rw [hx] at h; cases h
      | some ex =>
        rw [hx] at h
        simp only [Option.map_some, Option.some.injEq] at h
        rw [syncExplain_trailOnSlot] at hx
        refine ⟨d, ex, rfl, h1, h2, ?_, hx, h.symm⟩
        intro e he
        cases hne : impliesP orig e.literal lit.norm with
        | false => rfl
        | true =>
          exfalso
          have hmem : e ∈ trailOnSlot bs.trail lit.atom.slot := by
            refine List.mem_filter.mpr ⟨he, ?_⟩
            have hsl := impliesP_slot_eq hne
            have hse : (e.literal.atom.slot == lit.atom.slot) = true := by
              rw [hsl, norm_atom_slot]; simp
            exact hse
          have : (trailOnSlot bs.trail lit.atom.slot).any
              (fun e => impliesP orig e.literal lit.norm) = true :=
            List.any_eq_true.mpr ⟨e, hmem, hne⟩
          rw [this] at h4
          cases h4
    · rw [if_neg hg] at h
      cases h


/-! ## Validity of the push -/

theorem filterFrame_id {l : Literal} {bs : BranchState leaf} {d : Domain}
    (hd : bs.frame.doms[l.atom.slot]? = some d) (hne : d.isEmpty = false)
    (hall : (Dom.enum d).all l.valueHolds = true) :
    filterFrame l bs.frame = some bs.frame := by
  unfold filterFrame
  simp only [hd]
  have hfil : Dom.filterLitKeep l d = d :=
    Dom.filterLitKeep_eq_self_of_forall (fun x hx => by
      simpa using List.all_eq_true.mp hall x hx)
  rw [hfil]
  have hnonempty : Dom.enum d ≠ [] := by
    intro hem
    have htrue : d.isEmpty = true := (Dom.isEmpty_eq_true_iff d).mpr hem
    rw [htrue] at hne
    cases hne
  match hget : d.enum with
  | [] => exact absurd hget hnonempty
  | v :: vs =>
    obtain ⟨hlt, hget'⟩ := List.getElem?_eq_some_iff.mp hd
    have hset : bs.frame.doms.set l.atom.slot d = bs.frame.doms := by
      apply List.ext_getElem?
      intro i
      by_cases his : l.atom.slot = i
      · subst his
        rw [List.getElem?_set_self hlt, List.getElem?_eq_getElem hlt, hget']
      · rw [getElem?_set_of_ne (fun hsi => his hsi.symm)]
    simp only [hset, hget]

theorem syncClause_filter {orig : List Domain} {bs : BranchState leaf}
    {lit : Literal} {c : Clause} (h : syncClause orig bs lit = some c) :
    filterFrame lit bs.frame = some bs.frame := by
  obtain ⟨d, ex, hd, hne, hall, -, -, -⟩ := syncClause_spec h
  have hall' : (Dom.enum d).all lit.valueHolds = true := by
    rw [List.all_eq_true] at hall ⊢
    intro v hv
    rw [← norm_valueHolds]
    exact hall v hv
  exact filterFrame_id hd hne hall'

theorem syncClause_hfresh {orig : List Domain} {bs : BranchState leaf}
    {lit : Literal} {c : Clause} (h : syncClause orig bs lit = some c) :
    ∀ e ∈ bs.trail, e.literal ≠ lit.norm := by
  obtain ⟨d, ex, -, -, -, himp, -, -⟩ := syncClause_spec h
  intro e he heq
  have := himp e he
  have h2 : impliesP orig e.literal lit.norm = true := by
    rw [heq]; simp [impliesP, impliesBase, litEqB]
  rw [h2] at this
  exact absurd this (by decide)

theorem syncClause_pivot {orig : List Domain} {bs : BranchState leaf}
    {lit : Literal} {c : Clause} (h : syncClause orig bs lit = some c) :
    (lit.norm ∈ c) = True := by
  obtain ⟨d, ex, -, -, -, -, -, rfl⟩ := syncClause_spec h
  simp

theorem syncClause_chron {orig : List Domain} {bs : BranchState leaf}
    {lit : Literal} {c : Clause} (h : syncClause orig bs lit = some c) :
    StepChronology bs lit c := by
  obtain ⟨d, ex, -, -, -, -, hx, rfl⟩ := syncClause_spec h
  intro q hq hne
  rcases List.mem_cons.mp hq with rfl | hq
  · exact absurd rfl hne
  · obtain ⟨e, he, rfl⟩ := (syncExplain_spec hx).1 q hq
    exact ⟨e, he, (Literal.negate_negate _).symm⟩

theorem syncClause_entailed {orig : List Domain} {bs : BranchState leaf}
    {lit : Literal} {c : Clause} (h : syncClause orig bs lit = some c)
    (hfits : ∀ a, leaf a = true → a.Fits orig)
    (hslot : lit.atom.slot < orig.length) :
    LearnedEntailed leaf [c] := by
  obtain ⟨d, ex, -, -, -, -, hx, rfl⟩ := syncClause_spec h
  intro c' hc' a ha
  rw [List.mem_singleton] at hc'
  subst hc'
  have hfit := hfits a ha
  by_cases hsl : lit.atom.slot < a.length
  · have hget : a[lit.atom.slot]? = some a[lit.atom.slot] := List.getElem?_eq_getElem hsl
    have hw : a[lit.atom.slot] ∈ orig.getD lit.atom.slot Dom.empty := hfit.2 lit.atom.slot _ hget
    by_cases hv : lit.norm.valueHolds a[lit.atom.slot] = true
    · refine ⟨lit.norm, List.mem_cons_self, ?_⟩
      exact (valueHolds_read (by rw [norm_atom_slot]; exact hget)).mp hv
    · have hw' : a[lit.atom.slot] ∈ Dom.enum (orig.getD lit.atom.slot Dom.empty) := by
        rw [← domElems_eq_enum, ← DomainLike.mem_iff]
        exact hw
      have hmem : a[lit.atom.slot] ∈
          (Dom.enum (orig.getD lit.atom.slot Dom.empty)).filter
            fun w => !lit.norm.valueHolds w :=
        List.mem_filter.mpr ⟨hw', by simpa using hv⟩
      obtain ⟨q, hq, hqs, hqv⟩ := (syncExplain_spec hx).2 _ hmem
      exact ⟨q, List.mem_cons_of_mem _ hq,
        (valueHolds_read (by rw [hqs]; exact hget)).mp hqv⟩
  · exfalso
    have := hfit.1
    omega


/-! ## Preservation -/

@[simp] theorem syncOne_frame (orig : List Domain) (bs : BranchState leaf)
    (lit : Literal) : (syncOne orig bs lit).frame = bs.frame := by
  unfold syncOne; split <;> rfl

@[simp] theorem syncOne_level (orig : List Domain) (bs : BranchState leaf)
    (lit : Literal) : (syncOne orig bs lit).level = bs.level := by
  unfold syncOne; split <;> rfl

@[simp] theorem syncOne_learned (orig : List Domain) (bs : BranchState leaf)
    (lit : Literal) : (syncOne orig bs lit).learned = bs.learned := by
  unfold syncOne; split <;> rfl

theorem syncOne_trail (orig : List Domain) (bs : BranchState leaf)
    (lit : Literal) : ∃ ex, (syncOne orig bs lit).trail = bs.trail ++ ex ∧
      ∀ e ∈ ex, e.level = bs.level := by
  unfold syncOne
  split
  · exact ⟨_, rfl, by simp [narrowState]⟩
  · exact ⟨[], by simp, by simp⟩

theorem syncClause_in {orig : List Domain} {bs : BranchState leaf}
    {lit : Literal} {c : Clause} (h : syncClause orig bs lit = some c) :
    lit.atom.slot < (fullDomains bs.frame).length := by
  obtain ⟨d, ex, hd, -, -, -, -, -⟩ := syncClause_spec h
  exact (List.getElem?_eq_some_iff.mp hd).1

theorem syncOne_reachable {orig : List Domain} {bs : BranchState leaf}
    (lit : Literal) (hreach : ReachableState leaf orig bs)
    (hfits : ∀ a, leaf a = true → a.Fits orig) :
    ReachableState leaf orig (syncOne orig bs lit) := by
  unfold syncOne
  cases h : syncClause orig bs lit with
  | none => exact hreach
  | some c =>
    simp only
    have hin := syncClause_in h
    refine explainedStep_narrow_reachable hreach (syncClause_filter h)
      (syncClause_hfresh h) hin (fun _ h => absurd h (by simp))
      (syncClause_entailed h hfits ?_) (by
        simpa using syncClause_pivot h) (syncClause_chron h)
    have := hreach.length_ok
    omega

theorem syncOne_represents {orig : List Domain} {bs : BranchState leaf}
    (lit : Literal) {a : Assignment} (hleaf : leaf a = true)
    (hreach : ReachableState leaf orig bs)
    (hfits : ∀ a, leaf a = true → a.Fits orig)
    (hrep : bs.Represents a) : (syncOne orig bs lit).Represents a := by
  unfold syncOne
  cases h : syncClause orig bs lit with
  | none => exact hrep
  | some c =>
    simp only
    refine explainedStep_narrow_coverage (syncClause_filter h)
      (fun _ h => absurd h (by simp)) a hleaf hrep ?_
    exact filterFrame_literal_holds (syncClause_filter h) hrep.1 (syncClause_in h)

theorem foldl_syncOne_inv {orig : List Domain} {P : BranchState leaf → Prop}
    (hP : ∀ b lit, P b → P (syncOne orig b lit)) :
    ∀ (cs : List Literal) (b : BranchState leaf), P b →
      P (cs.foldl (syncOne orig) b) := by
  intro cs
  induction cs with
  | nil => intro b hb; exact hb
  | cons l rest ih => intro b hb; exact ih _ (hP b l hb)

theorem syncSlot_reachable {orig : List Domain} {bs : BranchState leaf}
    (s : Nat) (hreach : ReachableState leaf orig bs)
    (hfits : ∀ a, leaf a = true → a.Fits orig) :
    ReachableState leaf orig (syncSlot orig bs s) := by
  -- the frame is invariant along the fold, so the candidates are fixed
  unfold syncSlot
  exact foldl_syncOne_inv (P := fun b => ReachableState leaf orig b)
    (fun b lit hb => syncOne_reachable lit hb hfits) _ _ hreach


theorem syncSlot_represents {orig : List Domain} {bs : BranchState leaf}
    (s : Nat) {a : Assignment} (hleaf : leaf a = true)
    (hreach : ReachableState leaf orig bs)
    (hfits : ∀ a, leaf a = true → a.Fits orig)
    (hrep : bs.Represents a) : (syncSlot orig bs s).Represents a := by
  unfold syncSlot
  exact foldl_syncOne_inv (P := fun b => ReachableState leaf orig b ∧ b.Represents a)
    (fun b lit hb => ⟨syncOne_reachable lit hb.1 hfits,
      syncOne_represents lit hleaf hb.1 hfits hb.2⟩) _ _ ⟨hreach, hrep⟩ |>.2

theorem syncSlot_shape (orig : List Domain) (bs : BranchState leaf) (s : Nat) :
    (syncSlot orig bs s).frame = bs.frame ∧
    (syncSlot orig bs s).level = bs.level ∧
    (syncSlot orig bs s).learned = bs.learned ∧
    ∃ ex, (syncSlot orig bs s).trail = bs.trail ++ ex ∧
      ∀ e ∈ ex, e.level = bs.level := by
  unfold syncSlot
  have := foldl_syncOne_inv (orig := orig)
    (P := fun b => b.frame = bs.frame ∧ b.level = bs.level ∧
      b.learned = bs.learned ∧ ∃ ex, b.trail = bs.trail ++ ex ∧
        ∀ e ∈ ex, e.level = bs.level)
    (fun b lit hb => by
      obtain ⟨h1, h2, h3, ex, h4, h4'⟩ := hb
      obtain ⟨ex', h5, h5'⟩ := syncOne_trail orig b lit
      refine ⟨by simp [h1], by simp [h2], by simp [h3],
        ex ++ ex', by rw [h5, h4, List.append_assoc], ?_⟩
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact h4' e he
      · rw [h5' e he, h2])
    (syncCands orig bs.frame s) bs ⟨rfl, rfl, rfl, [], by simp, by simp⟩
  exact this

theorem foldl_range_inv {orig : List Domain} {P : BranchState leaf → Prop}
    (f : BranchState leaf → Nat → BranchState leaf)
    (hf : ∀ b i, P b → P (f b i)) :
    ∀ (l : List Nat) (b : BranchState leaf), P b → P (l.foldl f b) := by
  intro l
  induction l with
  | nil => intro b hb; exact hb
  | cons i rest ih => intro b hb; exact ih _ (hf b i hb)

theorem syncAll_reachable {orig : List Domain} {bs : BranchState leaf}
    (hreach : ReachableState leaf orig bs)
    (hfits : ∀ a, leaf a = true → a.Fits orig) :
    ReachableState leaf orig (syncAll orig bs) := by
  unfold syncAll
  exact foldl_range_inv (orig := orig) (P := fun b => ReachableState leaf orig b) _
    (fun b i hb => syncSlot_reachable _ hb hfits) _ _ hreach

theorem syncAll_represents {orig : List Domain} {bs : BranchState leaf}
    {a : Assignment} (hleaf : leaf a = true)
    (hreach : ReachableState leaf orig bs)
    (hfits : ∀ a, leaf a = true → a.Fits orig)
    (hrep : bs.Represents a) : (syncAll orig bs).Represents a := by
  unfold syncAll
  exact (foldl_range_inv (orig := orig)
    (P := fun b => ReachableState leaf orig b ∧ b.Represents a) _
    (fun b i hb => ⟨syncSlot_reachable _ hb.1 hfits,
      syncSlot_represents _ hleaf hb.1 hfits hb.2⟩) _ _ ⟨hreach, hrep⟩).2

theorem syncAll_shape (orig : List Domain) (bs : BranchState leaf) :
    (syncAll orig bs).frame = bs.frame ∧
    (syncAll orig bs).level = bs.level ∧
    (syncAll orig bs).learned = bs.learned ∧
    ∃ ex, (syncAll orig bs).trail = bs.trail ++ ex ∧
      ∀ e ∈ ex, e.level = bs.level := by
  unfold syncAll
  exact foldl_range_inv (orig := orig)
    (P := fun b => b.frame = bs.frame ∧ b.level = bs.level ∧
      b.learned = bs.learned ∧ ∃ ex, b.trail = bs.trail ++ ex ∧
        ∀ e ∈ ex, e.level = bs.level)
    _ (fun b i hb => by
      obtain ⟨h1, h2, h3, ex, h4, h4'⟩ := hb
      obtain ⟨g1, g2, g3, ex', g4, g4'⟩ := syncSlot_shape orig b i
      refine ⟨by rw [g1, h1], by rw [g2, h2], by rw [g3, h3],
        ex ++ ex', by rw [g4, h4, List.append_assoc], ?_⟩
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact h4' e he
      · rw [g4' e he, h2])
    _ _ ⟨rfl, rfl, rfl, [], by simp, by simp⟩


@[simp] theorem syncSlot_frame (orig : List Domain) (bs : BranchState leaf)
    (s : Nat) : (syncSlot orig bs s).frame = bs.frame := (syncSlot_shape orig bs s).1
@[simp] theorem syncSlot_level (orig : List Domain) (bs : BranchState leaf)
    (s : Nat) : (syncSlot orig bs s).level = bs.level := (syncSlot_shape orig bs s).2.1
@[simp] theorem syncSlot_learned (orig : List Domain) (bs : BranchState leaf)
    (s : Nat) : (syncSlot orig bs s).learned = bs.learned := (syncSlot_shape orig bs s).2.2.1
@[simp] theorem syncAll_frame (orig : List Domain) (bs : BranchState leaf) :
    (syncAll orig bs).frame = bs.frame := (syncAll_shape orig bs).1
@[simp] theorem syncAll_level (orig : List Domain) (bs : BranchState leaf) :
    (syncAll orig bs).level = bs.level := (syncAll_shape orig bs).2.1
@[simp] theorem syncAll_learned (orig : List Domain) (bs : BranchState leaf) :
    (syncAll orig bs).learned = bs.learned := (syncAll_shape orig bs).2.2.1



theorem syncAll_trail_shape (orig : List Domain) (bs : BranchState leaf) :
    ∃ ex, (syncAll orig bs).trail = bs.trail ++ ex ∧
      ∀ e ∈ ex, e.level = bs.level := by
  obtain ⟨-, -, -, ex, hex, hlev⟩ := syncAll_shape orig bs
  exact ⟨ex, hex, hlev⟩

end FrameSyncCore

/-- One synchronised productive step: the narrowing enqueue followed by the
frame/trail synchronisation of the deduced literal's slot. -/
def stepNarrowSync (orig : List Domain) (bs : BranchState leaf)
    (d : ProductiveDeduction leaf bs) : BranchState leaf :=
  syncSlot orig (narrowState bs d.frame d.literal d.reason d.learned)
    d.literal.atom.slot

@[simp] theorem stepNarrowSync_frame (orig : List Domain) (bs : BranchState leaf)
    (d : ProductiveDeduction leaf bs) : (stepNarrowSync orig bs d).frame = d.frame := by
  simp [stepNarrowSync, narrowState]

@[simp] theorem stepNarrowSync_level (orig : List Domain) (bs : BranchState leaf)
    (d : ProductiveDeduction leaf bs) : (stepNarrowSync orig bs d).level = bs.level := by
  simp [stepNarrowSync, narrowState]

@[simp] theorem stepNarrowSync_learned (orig : List Domain) (bs : BranchState leaf)
    (d : ProductiveDeduction leaf bs) :
    (stepNarrowSync orig bs d).learned = d.learned ++ bs.learned := by
  simp [stepNarrowSync, narrowState]

theorem stepNarrowSync_trail (orig : List Domain) (bs : BranchState leaf)
    (d : ProductiveDeduction leaf bs) :
    ∃ ex, (stepNarrowSync orig bs d).trail =
        bs.trail ++ [{ literal := d.literal.norm, level := bs.level,
                       reason := some { clause := d.reason } }] ++ ex ∧
      ∀ e ∈ ex, e.level = bs.level := by
  obtain ⟨-, hl, -, ex, hex, hlev⟩ := syncSlot_shape orig
    (narrowState bs d.frame d.literal d.reason d.learned) d.literal.atom.slot
  exact ⟨ex, hex, hlev⟩

theorem stepNarrowSync_reachable {orig : List Domain} {bs : BranchState leaf}
    (d : ProductiveDeduction leaf bs)
    (h : ReachableState leaf orig
      (narrowState bs d.frame d.literal d.reason d.learned))
    (hfits : ∀ a, leaf a = true → a.Fits orig) :
    ReachableState leaf orig (stepNarrowSync orig bs d) :=
  syncSlot_reachable _ h hfits

theorem stepNarrowSync_represents {orig : List Domain} {bs : BranchState leaf}
    (d : ProductiveDeduction leaf bs) {a : Assignment} (hleaf : leaf a = true)
    (h : ReachableState leaf orig
      (narrowState bs d.frame d.literal d.reason d.learned))
    (hfits : ∀ a, leaf a = true → a.Fits orig)
    (hrep : (narrowState bs d.frame d.literal d.reason d.learned).Represents a) :
    (stepNarrowSync orig bs d).Represents a :=
  syncSlot_represents _ hleaf h hfits hrep

/-- The explained closure: iterate productive deductions until the step is
stable or the branch is dead; every step is followed by the frame/trail
synchronisation of its slot (R1d). Recursion is on `Frame.mass`, the same
measure the certified closure uses — the decrease comes from the step's
own payload, so no fuel and no restart counter is involved. -/
def explainedClosure (orig : List Domain) (original : List Clause)
    (props : List Propagator) (bs : BranchState leaf) : BranchState leaf :=
  match hd : explainedDeduction original props bs with
  | none => bs
  | some d => explainedClosure orig original props (stepNarrowSync orig bs d)
termination_by Frame.mass bs.frame
decreasing_by
  have := d.decreases
  simpa using this

/-! ### Bridging the step and its deduction -/

/-- A productive deduction of the state determines the step's effect. -/
theorem explainedStep_of_deduction {original : List Clause}
    {props : List Propagator} {bs : BranchState leaf}
    {d : ProductiveDeduction leaf bs}
    (h : explainedDeduction original props bs = some d) :
    explainedStep original props bs = .narrow d.literal d.reason d.learned := by
  cases hev : nextPruningEvent original props bs.frame bs.learned with
  | stable => simp only [explainedDeduction, hev] at h; cases h
  | conflict cs => simp only [explainedDeduction, hev] at h; cases h
  | implied l c lr fl =>
      simp only [explainedDeduction, hev] at h
      by_cases ht : TrailRedundant bs.trail l = true
      · simp only [ht] at h
        cases h
      · have hred : TrailRedundant bs.trail l = false := by
          cases hb : TrailRedundant bs.trail l
          · rfl
          · exact absurd hb ht
        simp only [hred] at h
        split at h
        · simp at h
        · rename_i g hf
          split at h
          · rename_i hm
            have hd := Option.some.inj h
            have hl : d.literal = l := by rw [← hd]
            have hc : d.reason = c := by rw [← hd]
            have hle : d.learned =
                (if lr && !(bs.learned.contains c) then [c] else []) := by rw [← hd]
            rw [hl, hc, hle]
            simp only [explainedStep, hev, hred, hf, if_pos hm]
          · simp at h

/-- The deduction's event is the driver's deduction event for its literal
and reason. -/
theorem explainedDeduction_event {original : List Clause}
    {props : List Propagator} {bs : BranchState leaf}
    {d : ProductiveDeduction leaf bs}
    (h : explainedDeduction original props bs = some d) :
    ∃ lr fl, nextPruningEvent original props bs.frame bs.learned
      = .implied d.literal d.reason lr fl := by
  cases hev : nextPruningEvent original props bs.frame bs.learned with
  | stable => simp only [explainedDeduction, hev] at h; cases h
  | conflict cs => simp only [explainedDeduction, hev] at h; cases h
  | implied l c lr fl =>
      simp only [explainedDeduction, hev] at h
      by_cases ht : TrailRedundant bs.trail l = true
      · simp only [ht] at h
        cases h
      · have hred : TrailRedundant bs.trail l = false := by
          cases hb : TrailRedundant bs.trail l
          · rfl
          · exact absurd hb ht
        simp only [hred] at h
        split at h
        · simp at h
        · rename_i g hf
          split at h
          · rename_i hm
            have hd := Option.some.inj h
            have hl : d.literal = l := by rw [← hd]
            have hc : d.reason = c := by rw [← hd]
            exact ⟨lr, fl, by simpa [hl, hc] using hev⟩
          · simp at h

/-- FRESHNESS: every deduction the closure selects is absence-checked —
its normalized literal does not occur on the trail. This is the premise
`TrailLiteralsDistinct.enqueue` needs, derived from the selected
deduction instead of asked of callers. -/
theorem explainedDeduction_fresh {original : List Clause}
    {props : List Propagator} {bs : BranchState leaf}
    {d : ProductiveDeduction leaf bs}
    (h : explainedDeduction original props bs = some d) :
    ∀ e ∈ bs.trail, e.literal ≠ d.literal.norm := by
  cases hev : nextPruningEvent original props bs.frame bs.learned with
  | stable => simp only [explainedDeduction, hev] at h; cases h
  | conflict cs => simp only [explainedDeduction, hev] at h; cases h
  | implied l c lr fl =>
      simp only [explainedDeduction, hev] at h
      by_cases ht : TrailRedundant bs.trail l = true
      · simp only [ht] at h
        cases h
      · have hred : TrailRedundant bs.trail l = false := by
          cases hb : TrailRedundant bs.trail l
          · rfl
          · exact absurd hb ht
        simp only [hred] at h
        split at h
        · simp at h
        · rename_i g hf
          split at h
          · rename_i hm
            have hd := Option.some.inj h
            have hl : d.literal = l := by rw [← hd]
            rw [hl]
            exact not_trailRedundant_iff.mp hred
          · simp at h

/-- The deduction's fresh clauses are entailed whenever its reason clause
is (they are a sublist of `[reason]`). -/
theorem explainedDeduction_learned_entailed {original : List Clause}
    {props : List Propagator} {bs : BranchState leaf}
    {d : ProductiveDeduction leaf bs}
    (h : explainedDeduction original props bs = some d) :
    LearnedEntailed leaf [d.reason] → LearnedEntailed leaf d.learned := by
  intro hent
  cases hev : nextPruningEvent original props bs.frame bs.learned with
  | stable => simp only [explainedDeduction, hev] at h; cases h
  | conflict cs => simp only [explainedDeduction, hev] at h; cases h
  | implied l c lr fl =>
      simp only [explainedDeduction, hev] at h
      by_cases ht : TrailRedundant bs.trail l = true
      · simp only [ht] at h
        cases h
      · have hred : TrailRedundant bs.trail l = false := by
          cases hb : TrailRedundant bs.trail l
          · rfl
          · exact absurd hb ht
        simp only [hred] at h
        split at h
        · simp at h
        · rename_i g hf
          split at h
          · rename_i hm
            have hd := Option.some.inj h
            have hc : d.reason = c := by rw [← hd]
            have hle : d.learned =
                (if lr && !(bs.learned.contains c) then [c] else []) := by rw [← hd]
            rw [hle]
            split
            · -- the fresh single clause is the reason clause
              simpa [hc] using hent
            · intro cl hcl
              exact absurd hcl (by simp)
          · simp at h

/-! ### The unit-database discipline (DAG-lower twins)

The closure's learned-dependent obligations are RELATIVIZED to the unit
discipline in this milestone: the ∀-`ReachableState` form is FALSE (the
kernel refutation is `Proofs/ClosureRefutation.lean`: a live, coherent
branch with a spurious multi-literal learned clause makes
`StepChronology` fail at the selected event). `UnitDB`/`UnitKit` are the
DAG-lower twins of `DomExplained.UnitLearned`/`UnitRunProfile` (the
bodies are definitionally identical, so run-level values transport by
defeq); `UnitPayload` bundles the closure's per-deduction maintenance
step, proved below from the selected-event characterization. -/

/-- The learned databases of the supported fragment: every clause is a
normalized unit clause (twin of `UnitLearned`). -/
def UnitDB (db : List Clause) : Prop :=
  ∀ c ∈ db, ∃ q : Literal, c = [q] ∧ q = q.norm

/-- The propagator kit's unit-emission profile (twin of
`UnitRunProfile`). -/
def UnitKit (props : List Propagator) : Prop :=
  (∀ p ∈ props, ∀ st l r, p.run st = .implied l r →
    ∃ q : Literal, r.clause = [q] ∧ q = q.norm) ∧
  (∀ p ∈ props, ∀ st c, p.run st = .conflict c →
    c = [] ∨ ∃ q : Literal, c = [q] ∧ q = q.norm)

/-- The closure's per-deduction maintenance step: a selected deduction's
learned payload stays in the unit discipline, given the current state's
discipline. -/
def UnitPayload (original : List Clause) (props : List Propagator) : Prop :=
  ∀ {leaf : Assignment → Bool} {bs : BranchState leaf}
    {d : ProductiveDeduction leaf bs},
    explainedDeduction original props bs = some d → UnitDB bs.learned →
      UnitDB d.learned

theorem unitDB_nil : UnitDB ([] : List Clause) := by
  intro c hc
  cases hc

theorem unitDB_append {d₁ d₂ : List Clause} (h₁ : UnitDB d₁)
    (h₂ : UnitDB d₂) : UnitDB (d₁ ++ d₂) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact h₁ c hc
  · exact h₂ c hc

theorem unitDB_if_single {c : Clause}
    (h : ∃ q : Literal, c = [q] ∧ q = q.norm) (b : Bool) :
    UnitDB (if b then [c] else []) := by
  obtain ⟨q, hcq, hqn⟩ := h
  cases b
  · intro c' hc'
    cases hc'
  · intro c' hc'
    have hc'' : c' = c := by simpa using hc'
    subst hc''
    exact ⟨q, hcq, hqn⟩

/-- CHARACTERIZATION: a selected deduction's payload is determined by the
event: its literal and reason are the event's, and its learned list is
the freshness-filtered singleton of the reason clause. (DAG-lower twin of
the `Proofs/DomExplained.lean` lemma of the same name, moved down so the
closure can maintain its discipline; the statement is unchanged.) -/
theorem explainedDeduction_learned_shape {original : List Clause}
    {props : List Propagator} {bs : BranchState leaf}
    {d : ProductiveDeduction leaf bs}
    (h : explainedDeduction original props bs = some d) :
    ∃ (c : Clause) (lr fl : Bool),
      nextPruningEvent original props bs.frame bs.learned
          = .implied d.literal c lr fl ∧
        d.reason = c ∧
        d.learned = (if lr && !(bs.learned.contains c) then [c] else []) := by
  cases hev : nextPruningEvent original props bs.frame bs.learned with
  | stable => simp only [explainedDeduction, hev] at h; cases h
  | conflict cs => simp only [explainedDeduction, hev] at h; cases h
  | implied l c lr fl =>
      simp only [explainedDeduction] at h
      rw [hev] at h
      by_cases ht : TrailRedundant bs.trail l = true
      · simp only [ht] at h; cases h
      · have hred : TrailRedundant bs.trail l = false := by
          cases hb : TrailRedundant bs.trail l
          · rfl
          · exact absurd hb ht
        simp only [hred] at h
        split at h
        · simp at h
        · rename_i g hf
          split at h
          · rename_i hm
            have hd := Option.some.inj h
            have hl : d.literal = l := by rw [← hd]
            have hr : d.reason = c := by rw [← hd]
            have hle : d.learned =
                (if lr && !(bs.learned.contains c) then [c] else []) := by
              rw [← hd]
            exact ⟨c, lr, fl, by rw [hl], hr, hle⟩
          · simp at h

/-! ### A2 closure: the whole-run obligations

`explainedClosure` keeps frame, trail and learned database in one state,
so the driver cannot pass an unrelated frame. The theorems below move the
per-step certificates of the previous section to the whole run. They are
the exports PLAN A2 asks for: `explainedClosure_preserves` (coherence) and
`explainedClosure_coverage` (no leaf solution is lost). -/

/-- The reason-shape obligation a domain propagator discharges by *naming
the trail entries it watched*: every non-pivot literal of a produced
reason clause is the negation of a literal already recorded. This is a
statement about which entries the reason builder used, not a chronology
theorem, so a domain driver can produce it directly. -/
def DomReasonRecorded (leaf : Assignment → Bool) (bs : BranchState leaf)
    (l : Literal) (c : Clause) : Prop :=
  ∀ q ∈ c, q ≠ l.norm → q.negate ∈ bs.trail.map TrailEntry.literal

/-- Chronology is *derived* from the recorded-entry obligation: the domain
driver never proves `StepChronology` itself (PLAN A2: "the concrete
constructor must not require callers to manufacture the very chronology
theorem this package is meant to establish"). -/
theorem stepChronology_of_domReasonRecorded {bs : BranchState leaf}
    {l : Literal} {c : Clause} (h : DomReasonRecorded leaf bs l c) :
    StepChronology bs l c := by
  intro q hq hne
  obtain ⟨e, he, heq⟩ := List.mem_map.mp (h q hq hne)
  exact ⟨e, he, heq⟩

/-- The whole-run obligations, indexed by the event `nextPruningEvent`
ACTUALLY selects at a coherent reachable state. This is the A2 repair of
the former deduction-indexed contract (INTERFACES §2.2):

* `literalSound` is BRANCH-RELATIVE: the deduced literal has to hold only
  at leaf solutions the CURRENT reachable state represents; its former
  global form is refuted by the `x ≠ y` acceptance example below;
* `reasonEntailed` keeps GLOBAL entailment (the two-level discipline:
  reason clauses are always globally entailed, pivot truth is not);
* `pivot`, `chronology`, `inRange` are the selected event's own
  obligations, discharged by the concrete kit (INTERFACES §4 items 3-5);
* `conflictExcludes`/`conflictEntailed` carry the `.conflict` row's
  evidence, which the result-returning closure needs for coverage;
* `originalEntailed`/`origViewed` are the supported-problem gates
  (original-clause semantics and the typed-slot fragment). The entailed
  database itself is not a field: `ReachableState.wf` already carries
  `LearnedEntailed leaf bs.learned`. -/
structure ClosureContract (leaf : Assignment → Bool) (orig : List Domain)
    (original : List Clause) (props : List Propagator) : Prop where
  /-- the problem's original clause database is globally entailed -/
  originalEntailed : ∀ c ∈ original, ∀ a, leaf a = true → c.SatisfiedBy a
  /-- every leaf solution fits the original box (the wipe-out clause's
      entailment, R1c) -/
  leafFits : ∀ a, leaf a = true → a.Fits orig
  /-- supported-fragment gate: the original box is int-viewed -/
  origViewed : ∀ d ∈ orig, IntViewedDomain d
  /-- BRANCH-RELATIVE literal soundness of the SELECTED deduction event:
      the deduced literal holds at every leaf solution the current
      reachable state represents -/
  literalSound : ∀ (bs : BranchState leaf), ReachableState leaf orig bs →
    ∀ (l : Literal) (c : Clause) (lr fl : Bool),
      nextPruningEvent original props bs.frame bs.learned = .implied l c lr fl →
      ∀ a, leaf a = true → bs.Represents a → l.norm.eval a = some true
  /-- GLOBAL entailment of the selected deduction's reason clause -/
  reasonEntailed : ∀ (bs : BranchState leaf), ReachableState leaf orig bs →
    ∀ (l : Literal) (c : Clause) (lr fl : Bool),
      nextPruningEvent original props bs.frame bs.learned = .implied l c lr fl →
      LearnedEntailed leaf [c]
  /-- the selected deduction's normalized literal is its reason's pivot,
      RELATIVIZED to unit-learned databases: the ∀-state form is FALSE
      (kernel refutation in `Proofs/ClosureRefutation.lean`), while the
      gated form is free under the unit discipline
      (`hshape_of_unitLearned`). -/
  pivot : ∀ (bs : BranchState leaf), ReachableState leaf orig bs →
    UnitDB bs.learned →
    ∀ (l : Literal) (c : Clause) (lr fl : Bool),
      nextPruningEvent original props bs.frame bs.learned = .implied l c lr fl →
      (l.norm ∈ c) = True
  /-- the reason's non-pivot literals have recorded falsifiers,
      RELATIVIZED to unit-learned databases (same refutation). -/
  chronology : ∀ (bs : BranchState leaf), ReachableState leaf orig bs →
    UnitDB bs.learned →
    ∀ (l : Literal) (c : Clause) (lr fl : Bool),
      nextPruningEvent original props bs.frame bs.learned = .implied l c lr fl →
      StepChronology bs l c
  /-- the deduced literal names an in-range (original) slot -/
  inRange : ∀ (bs : BranchState leaf), ReachableState leaf orig bs →
    ∀ (l : Literal) (c : Clause) (lr fl : Bool),
      nextPruningEvent original props bs.frame bs.learned = .implied l c lr fl →
      l.atom.slot < (fullDomains bs.frame).length
  /-- a selected conflict event excludes every leaf solution the state
      represents (branch-relative, never a global claim) -/
  conflictExcludes : ∀ (bs : BranchState leaf), ReachableState leaf orig bs →
    ∀ (cs : List Clause),
      nextPruningEvent original props bs.frame bs.learned = .conflict cs →
      ∀ a, leaf a = true → bs.Represents a → False
  /-- a selected conflict event's clauses are globally entailed -/
  conflictEntailed : ∀ (bs : BranchState leaf), ReachableState leaf orig bs →
    ∀ (cs : List Clause),
      nextPruningEvent original props bs.frame bs.learned = .conflict cs →
      LearnedEntailed leaf cs

/-- The former DEDUCTION-indexed form of `literalSound` (INTERFACES §2.2),
now DERIVED from the selected-event field: a selected deduction's event is
the driver's own deduction event for its literal and reason. -/
theorem ClosureContract.literalSound_deduction
    (hc : ClosureContract leaf orig original props)
    {bs : BranchState leaf} (hreach : ReachableState leaf orig bs)
    {d : ProductiveDeduction leaf bs}
    (hd : explainedDeduction original props bs = some d) :
    ∀ a, leaf a = true → bs.Represents a → d.literal.norm.eval a = some true := by
  intro a hleaf hrep
  obtain ⟨lr, fl, hev⟩ := explainedDeduction_event hd
  exact hc.literalSound bs hreach d.literal d.reason lr fl hev a hleaf hrep

/-- The contract-driven narrowing row: everything a productive deduction
needs to preserve the reachable invariant is DERIVED from the selected
event's contract and the absence check — never handed in as an arbitrary
`hLit`/`hEnt`/`hPiv`/`hRec`/`hRange` function. -/
theorem explainedDeduction_narrow_reachable {orig : List Domain}
    (hc : ClosureContract leaf orig original props)
    {bs : BranchState leaf} (hreach : ReachableState leaf orig bs)
    (hu : UnitDB bs.learned)
    {d : ProductiveDeduction leaf bs}
    (hd : explainedDeduction original props bs = some d) :
    ReachableState leaf orig (narrowState bs d.frame d.literal d.reason d.learned) := by
  obtain ⟨lr, fl, hev⟩ := explainedDeduction_event hd
  have hentReason := hc.reasonEntailed bs hreach d.literal d.reason lr fl hev
  exact explainedStep_narrow_reachable hreach d.filtered
    (explainedDeduction_fresh hd)
    (hc.inRange bs hreach d.literal d.reason lr fl hev)
    (explainedDeduction_learned_entailed hd hentReason)
    hentReason
    (hc.pivot bs hreach hu d.literal d.reason lr fl hev)
    (hc.chronology bs hreach hu d.literal d.reason lr fl hev)

/-- PRESERVES: the run keeps the reachable invariant. Every narrowed step's
coherence obligations are derived from the selected event's contract
(`explainedDeduction_narrow_reachable`), so the induction never assumes
what it must prove. The induction is on the frame mass with the state
generalised, because the statement mentions the state in both the closure
argument and the invariant. -/
theorem explainedClosure_reachable {orig : List Domain}
    (hc : ClosureContract leaf orig original props) (bs : BranchState leaf)
    (hpay : UnitPayload original props) (hreach : ReachableState leaf orig bs)
    (hu : UnitDB bs.learned) :
    ReachableState leaf orig (explainedClosure orig original props bs) := by
  suffices h : ∀ (fuel : Nat) (bs : BranchState leaf),
      Frame.mass bs.frame ≤ fuel →
      ReachableState leaf orig bs → UnitDB bs.learned →
      ReachableState leaf orig (explainedClosure orig original props bs) from
    h (Frame.mass bs.frame) bs (Nat.le_refl _) hreach hu
  intro fuel
  induction fuel with
  | zero =>
    intro bs hle hreach _
    rw [explainedClosure]
    split
    · exact hreach
    · rename_i d _
      exfalso
      have hdec := d.decreases
      omega
  | succ fuel ih =>
    intro bs hle hreach hu
    rw [explainedClosure]
    split
    · exact hreach
    · rename_i d hd
      refine ih (stepNarrowSync orig bs d) ?_ ?_ ?_
      · have hdec := d.decreases
        simp only [stepNarrowSync_frame]
        omega
      · exact stepNarrowSync_reachable d
          (explainedDeduction_narrow_reachable hc hreach hu hd) hc.leafFits
      · have hpay' := hpay hd hu
        rw [stepNarrowSync_learned]
        exact unitDB_append hpay' hu

/-- COVERAGE: the run cannot lose a leaf solution. Narrowing is only
applied to literals every REPRESENTED leaf solution satisfies (the
branch-relative field), and the recorded entries all hold at every
assignment the frame covers. The reachability hypothesis is what
INTERFACES §2.2 requires: branch-relative soundness can only be
instantiated at coherent states. -/
theorem explainedClosure_coverage {orig : List Domain}
    (hc : ClosureContract leaf orig original props)
    (bs : BranchState leaf) (hpay : UnitPayload original props)
    (hreach : ReachableState leaf orig bs) (hu : UnitDB bs.learned)
    (a : Assignment) (hleaf : leaf a = true) (hrep : bs.Represents a) :
    (explainedClosure orig original props bs).Represents a := by
  suffices h : ∀ (fuel : Nat) (bs : BranchState leaf),
      Frame.mass bs.frame ≤ fuel → ReachableState leaf orig bs →
      UnitDB bs.learned →
      bs.Represents a → (explainedClosure orig original props bs).Represents a from
    h (Frame.mass bs.frame) bs (Nat.le_refl _) hreach hu hrep
  intro fuel
  induction fuel with
  | zero =>
    intro bs hle hreach _ hrep
    rw [explainedClosure]
    split
    · exact hrep
    · rename_i d _
      exfalso
      have hdec := d.decreases
      omega
  | succ fuel ih =>
    intro bs hle hreach hu hrep
    rw [explainedClosure]
    split
    · exact hrep
    · rename_i d hd
      obtain ⟨lr, fl, hev⟩ := explainedDeduction_event hd
      have hnr := explainedDeduction_narrow_reachable hc hreach hu hd
      have hu' : UnitDB (stepNarrowSync orig bs d).learned := by
        rw [stepNarrowSync_learned]
        exact unitDB_append (hpay hd hu) hu
      refine ih (stepNarrowSync orig bs d) ?_
        (stepNarrowSync_reachable d hnr hc.leafFits) hu' ?_
      · have hdec := d.decreases
        simp only [stepNarrowSync_frame]
        omega
      · exact stepNarrowSync_represents d hleaf hnr hc.leafFits
          (explainedStep_narrow_coverage d.filtered
            (explainedDeduction_learned_entailed hd
              (hc.reasonEntailed bs hreach d.literal d.reason lr fl hev))
            a hleaf hrep
            (hc.literalSound bs hreach d.literal d.reason lr fl hev a hleaf hrep))

/-! ### The result-returning closure (INTERFACES §2.2)

`explainedClosure` keeps returning the coherent fixpoint state (its
reachability and coverage theorems above). The scheduler consumes the
RESULT-returning variant, which also reports the terminal event's payload:
an entailed conflict clause list, or the failed-narrowing literal — never a
global UNSAT claim. -/

/-- Terminal classification of one closure run (INTERFACES §2.2). -/
inductive ClosureResult (leaf : Assignment → Bool) where
  /-- no productive deduction remains under the scan semantics -/
  | stable (state : BranchState leaf)
  /-- the scan found a conflict; `conflicts` is the event payload
      (`PruningEvent.conflict`'s clause list, possibly `[]` for a
      database refutation), `learned` the freshness-filtered clauses to
      add to the global database -/
  | conflict (state : BranchState leaf) (conflicts : List Clause)
      (learned : List Clause)
  /-- a deduction made the branch locally dead without a conflict event:
      `filterFrame literal state.frame = none` -/
  | localExcluded (state : BranchState leaf) (literal : Option Literal)
      (reason : Option Clause) (learned : List Clause)

namespace ClosureResult

/-- The coherent state the run stopped in. -/
def state : ClosureResult leaf → BranchState leaf
  | .stable s => s
  | .conflict s _ _ => s
  | .localExcluded s _ _ _ => s

/-- The clauses the caller must add to the global database: the terminal
event's freshness-filtered clauses. Clauses learned by earlier narrowing
steps already sit in `state.learned`. -/
def newClauses : ClosureResult leaf → List Clause
  | .stable _ => []
  | .conflict _ _ learned => learned
  | .localExcluded _ _ _ learned => learned

/-- Per-case coverage relative to the input state (INTERFACES §2.2):
`stable` transports representation of the input state; the two dead cases
assert that no leaf solution is represented AT ALL — a local statement,
never a global UNSAT claim. -/
def Covers (bs : BranchState leaf) : ClosureResult leaf → Prop
  | .stable s => ∀ a, leaf a = true → bs.Represents a → s.Represents a
  | .conflict s _ _ => ∀ a, leaf a = true → s.Represents a → False
  | .localExcluded s _ _ _ => ∀ a, leaf a = true → s.Represents a → False

end ClosureResult

/-- Everything a closure result must supply, packaged (INTERFACES §2.2). -/
structure ClosureResult.Spec (leaf : Assignment → Bool) (orig : List Domain)
    (bs : BranchState leaf) (r : ClosureResult leaf) : Prop where
  /-- the carried state is coherent -/
  reachable : ReachableState leaf orig r.state
  /-- every clause the caller must learn is globally entailed -/
  entailed : ∀ c ∈ r.newClauses, LearnedEntailed leaf [c]
  /-- the run covers every leaf solution the input state represented -/
  coverage : r.Covers bs

/-- A freshness-filtered single-clause database is entailed whenever the
clause is (an empty database is trivially entailed). -/
theorem learned_entailed_filter (bs : BranchState leaf) {c : Clause}
    {lr : Bool} (h : LearnedEntailed leaf [c]) :
    ∀ c' ∈ (if lr && !(bs.learned.contains c) then [c] else []),
      LearnedEntailed leaf [c'] := by
  intro c' hc'
  split at hc'
  · rw [List.mem_singleton] at hc'
    rw [hc']
    exact h
  · simp at hc'

/-! ### The wipe-out conflict clause (R1c)

A frame with an EMPTY remaining domain holds no leaf solution. The conflict
is reported on the clause "no trail literal that removed an original value of
that slot holds": for every ORIGINAL value `w` of slot `s`, the first trail
entry whose negation holds at `w` is a remover; the clause is the (duplicate
free) list of these negated-normalized removers. It is entailed whenever every
leaf solution fits the original box (a solution with `x_s = w` makes the
remover's negation true) and falsified by the trail (each literal is the
negation of a trail literal). If some original value has no remover (the frame
and the trail disagree) no clause is built and the branch falls back to the
plain stable classification. -/

/-- The negated-normalized trail literal removing value `w` of slot `s`. -/
def wipeRemover (trail : List TrailEntry) (s : Nat) (w : Value) : Option Literal :=
  (trail.map fun e => e.literal.negate.norm).find? fun q =>
    q.atom.slot == s && q.valueHolds w

/-- The wipe-out clause of slot `s` over its original domain (nonempty). -/
def wipeoutClauseAt (orig : List Domain) (trail : List TrailEntry) (s : Nat) :
    Option Clause :=
  let rs := (Dom.enum (orig.getD s Dom.empty)).map (wipeRemover trail s)
  if rs.any Option.isNone then none
  else
    match (rs.filterMap id).eraseDups with
    | [] => none
    | c => some c

/-- Scan the remaining domains (slot indices start at `s`) for the first
empty one with a buildable wipe-out clause. -/
def wipeoutScan (orig : List Domain) (trail : List TrailEntry) :
    List Domain → Nat → Option Clause
  | [], _ => none
  | d :: rest, s =>
      match (if d.isEmpty then wipeoutClauseAt orig trail s else none) with
      | some c => some c
      | none => wipeoutScan orig trail rest (s + 1)

/-- The wipe-out conflict clause of a branch frame, if one is buildable. -/
def wipeoutClause (orig : List Domain) (trail : List TrailEntry)
    (f : BranchFrame) : Option Clause :=
  wipeoutScan orig trail f.doms 0

/-- The terminal classification when no productive deduction is selected:
stable or conflict. Three conflict sources besides the scan's own
(R1c conflict routing): an implied literal the frame filter rejects is a
conflict ON ITS REASON CLAUSE; a stable event at a frame with an emptied
domain is a conflict on the WIPE-OUT clause. (`ClosureResult.localExcluded`
is no longer produced here.) -/
def terminalResult (orig : List Domain) (original : List Clause)
    (props : List Propagator) (bs : BranchState leaf) : ClosureResult leaf :=
  match nextPruningEvent original props bs.frame bs.learned with
  | .stable =>
      match wipeoutClause orig bs.trail bs.frame with
      | some w => .conflict bs [w] []
      | none => .stable bs
  | .conflict cs =>
      .conflict bs cs (cs.filter fun c => !(bs.learned.contains c))
  | .implied l c lr fl =>
      match filterFrame l bs.frame with
      | none => .conflict bs [c]
          (if lr && !(bs.learned.contains c) then [c] else [])
      | some _ => .stable bs

/-- The result-returning closure: iterate productive deductions; the
terminal event is classified by `terminalResult`. Recursion is on
`Frame.mass` — the decrease comes from the deduction's own payload, so no
fuel is involved. -/
def explainedClosureResult (orig : List Domain) (original : List Clause)
    (props : List Propagator) (bs : BranchState leaf) : ClosureResult leaf :=
  match hd : explainedDeduction original props bs with
  | some d =>
      explainedClosureResult orig original props
        (narrowState bs d.frame d.literal d.reason d.learned)
  | none => terminalResult orig original props bs
termination_by Frame.mass bs.frame
decreasing_by
  exact d.decreases

theorem wipeRemover_spec {trail : List TrailEntry} {s : Nat} {w : Value}
    {q : Literal} (h : wipeRemover trail s w = some q) :
    (∃ e ∈ trail, q = e.literal.negate.norm) ∧ q.atom.slot = s ∧
      q.valueHolds w = true := by
  unfold wipeRemover at h
  have hmem := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  obtain ⟨e, he, hq⟩ := List.mem_map.mp hmem
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨⟨e, he, hq.symm⟩, hp.1, hp.2⟩

theorem wipeoutClauseAt_eq {orig : List Domain} {trail : List TrailEntry}
    {s : Nat} {c : Clause} (h : wipeoutClauseAt orig trail s = some c) :
    c ≠ [] ∧
      c = (((Dom.enum (orig.getD s Dom.empty)).map (wipeRemover trail s)).filterMap id).eraseDups ∧
      ((Dom.enum (orig.getD s Dom.empty)).map (wipeRemover trail s)).any Option.isNone = false := by
  unfold wipeoutClauseAt at h
  simp only at h
  generalize hrs : ((Dom.enum (orig.getD s Dom.empty)).map (wipeRemover trail s)) = rs at h ⊢
  by_cases hany : rs.any Option.isNone = true
  · rw [if_pos hany] at h
    cases h
  · rw [if_neg hany] at h
    generalize hed : (rs.filterMap id).eraseDups = ed at h
    cases ed with
    | nil => cases h
    | cons x xs =>
        cases h
        exact ⟨by simp, rfl, Bool.eq_false_iff.mpr hany⟩

/-- The wipe-out clause of a slot is falsified literal-for-literal by the
trail: every literal is the negation-normalization of a trail literal. -/
theorem wipeoutClauseAt_falsified {orig : List Domain} {trail : List TrailEntry}
    {s : Nat} {c : Clause} (h : wipeoutClauseAt orig trail s = some c) :
    ∀ q ∈ c, ∃ e ∈ trail, q = e.literal.negate.norm := by
  obtain ⟨-, hc, -⟩ := wipeoutClauseAt_eq h
  intro q hq
  rw [hc] at hq
  have hq' := (List.mem_eraseDups).mp hq
  obtain ⟨r, hr, hrq⟩ := List.mem_filterMap.mp hq'
  obtain ⟨w, _, hw⟩ := List.mem_map.mp hr
  simp only [id] at hrq
  subst hrq
  exact (wipeRemover_spec hw).1

/-- The wipe-out clause of a slot is entailed by the original box: every
assignment fitting the box satisfies it. -/
theorem wipeoutClauseAt_entailed {orig : List Domain} {trail : List TrailEntry}
    {s : Nat} {c : Clause} (h : wipeoutClauseAt orig trail s = some c)
    {a : Assignment} (hfit : a.Fits orig) :
    ∃ q ∈ c, q.eval a = some true := by
  obtain ⟨hne, hc, hany⟩ := wipeoutClauseAt_eq h
  by_cases hs : s < a.length
  · have hget : a[s]? = some a[s] := List.getElem?_eq_getElem hs
    have hw : a[s] ∈ orig.getD s Dom.empty := hfit.2 s _ hget
    have hsome : ∃ q, wipeRemover trail s a[s] = some q := by
      cases hr : wipeRemover trail s a[s] with
      | some q => exact ⟨q, rfl⟩
      | none =>
          exfalso
          have hw' : a[s] ∈ Dom.enum (orig.getD s Dom.empty) := by
            rw [← domElems_eq_enum, ← DomainLike.mem_iff]
            exact hw
          have : ((Dom.enum (orig.getD s Dom.empty)).map (wipeRemover trail s)).any
              Option.isNone = true :=
            List.any_eq_true.mpr ⟨none, List.mem_map.mpr ⟨a[s], hw', hr⟩, rfl⟩
          rw [hany] at this
          cases this
    obtain ⟨q, hq⟩ := hsome
    obtain ⟨-, hslot, hvh⟩ := wipeRemover_spec hq
    refine ⟨q, ?_, ?_⟩
    · rw [hc]
      apply (List.mem_eraseDups).mpr
      exact List.mem_filterMap.mpr ⟨some q,
        List.mem_map.mpr ⟨a[s], by
          rw [← domElems_eq_enum, ← DomainLike.mem_iff]; exact hw, hq⟩, rfl⟩
    · exact (valueHolds_read (by rw [hslot]; exact hget)).mp hvh
  · exfalso
    have hlen := hfit.1
    have hnil : orig.getD s Dom.empty = Dom.empty := by
      rw [List.getD_eq_getElem?_getD]
      have : orig[s]? = none := List.getElem?_eq_none (by omega)
      rw [this]; rfl
    rw [hnil] at hc
    simp at hc
    exact hne hc

theorem wipeoutScan_spec {orig : List Domain} {trail : List TrailEntry} :
    ∀ (ds : List Domain) (s : Nat) {c : Clause},
      wipeoutScan orig trail ds s = some c →
      ∃ s', wipeoutClauseAt orig trail s' = some c := by
  intro ds
  induction ds with
  | nil => intro s c h; simp [wipeoutScan] at h
  | cons d rest ih =>
      intro s c h
      unfold wipeoutScan at h
      generalize hx : (if d.isEmpty = true then wipeoutClauseAt orig trail s
        else none) = x at h
      cases x with
      | some c' =>
          cases h
          by_cases hd : d.isEmpty = true
          · rw [if_pos hd] at hx
            exact ⟨s, hx⟩
          · rw [if_neg hd] at hx
            cases hx
      | none => exact ih (s + 1) h

theorem wipeoutClause_falsified {orig : List Domain} {trail : List TrailEntry}
    {f : BranchFrame} {c : Clause} (h : wipeoutClause orig trail f = some c) :
    ∀ q ∈ c, ∃ e ∈ trail, q = e.literal.negate.norm := by
  obtain ⟨s', hs'⟩ := wipeoutScan_spec _ _ h
  exact wipeoutClauseAt_falsified hs'

theorem wipeoutClause_entailed {orig : List Domain} {trail : List TrailEntry}
    {f : BranchFrame} {c : Clause} (h : wipeoutClause orig trail f = some c)
    {a : Assignment} (hfit : a.Fits orig) :
    ∃ q ∈ c, q.eval a = some true := by
  obtain ⟨s', hs'⟩ := wipeoutScan_spec _ _ h
  exact wipeoutClauseAt_entailed hs' hfit

/-- A wipe-out clause is refuted by every assignment satisfying the trail
that fits the original box. -/
theorem wipeoutClause_excludes {orig : List Domain} {trail : List TrailEntry}
    {f : BranchFrame} {c : Clause} (h : wipeoutClause orig trail f = some c)
    {a : Assignment} (hfit : a.Fits orig)
    (htrail : ∀ e ∈ trail, e.literal.eval a = some true) : False := by
  obtain ⟨q, hq, hqe⟩ := wipeoutClause_entailed h hfit
  obtain ⟨e, he, rfl⟩ := wipeoutClause_falsified h q hq
  rw [Literal.norm_eval, Literal.eval_negate, htrail e he] at hqe
  simp at hqe

/-- SPEC of the terminal dispatch: coherent state, entailed new clauses,
and per-case coverage. The filter-rejection conflict case's exclusion is DERIVED
from the branch-relative literal soundness plus the failed filter — the
`x ≠ y` counterexample's shape. -/
theorem terminalResult_spec {orig : List Domain}
    (hc : ClosureContract leaf orig original props) {bs : BranchState leaf}
    (hreach : ReachableState leaf orig bs) :
    ClosureResult.Spec leaf orig bs (terminalResult orig original props bs) := by
  rw [terminalResult]
  split
  · -- stable event: stable, or the wipe-out conflict
    split
    · rename_i w hw
      refine ⟨hreach, ?_, ?_⟩
      · intro c hc'
        cases hc'
      · intro a hleaf hrep
        exact wipeoutClause_excludes hw (hc.leafFits a hleaf) hrep.2.1
    · refine ⟨hreach, ?_, ?_⟩
      · intro c hc'
        cases hc'
      · intro a _ hrep
        exact hrep
  · -- conflict
    rename_i cs hev
    refine ⟨hreach, ?_, ?_⟩
    · intro c' hc'
      obtain ⟨hmem, _⟩ := List.mem_filter.mp hc'
      intro c'' hmem'' a hleaf
      rw [List.mem_singleton] at hmem''
      rw [hmem'']
      exact hc.conflictEntailed bs hreach cs hev c' hmem a hleaf
    · intro a hleaf hrep
      exact hc.conflictExcludes bs hreach cs hev a hleaf hrep
  · -- implied
    rename_i l c lr fl hev
    split
    · -- the filter is empty: the branch is dead. The literal CANNOT hold at
      -- a represented assignment, or `filterFrame_preserves` would produce
      -- a frame.
      rename_i hf
      refine ⟨hreach, ?_, ?_⟩
      · intro c' hc'
        exact learned_entailed_filter bs
          (hc.reasonEntailed bs hreach l c lr fl hev) c' hc'
      · intro a hleaf hrep
        have hlit := hc.literalSound bs hreach l c lr fl hev a hleaf hrep
        obtain ⟨g, hg, _⟩ := filterFrame_preserves hrep.1 (by
          rwa [Literal.norm_eval] at hlit)
        rw [hf] at hg
        cases hg
    · -- non-productive (or skipped): the stable fixpoint
      refine ⟨hreach, ?_, ?_⟩
      · intro c' hc'
        cases hc'
      · intro a _ hrep
        exact hrep

/-- The terminal `.conflict` result exposes its source (R1c routing): the
scan's own `.conflict cs`; the filter-rejected `.implied` event reported as a
conflict on its reason clause; or the WIPE-OUT conflict of a stable event
at a frame with an emptied domain (payload `[]`). -/
theorem terminalResult_conflict_cases {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {bs : BranchState leaf}
    {s : BranchState leaf} {cs learned : List Clause}
    (h : terminalResult orig original props bs = .conflict s cs learned) :
    s = bs ∧
      ((nextPruningEvent original props bs.frame bs.learned = .conflict cs ∧
          learned = cs.filter fun c => !(bs.learned.contains c)) ∨
        (∃ (l : Literal) (c : Clause) (lr fl : Bool),
          nextPruningEvent original props bs.frame bs.learned = .implied l c lr fl ∧
            filterFrame l bs.frame = none ∧ cs = [c] ∧
            learned = (if lr && !(bs.learned.contains c) then [c] else [])) ∨
        (∃ w : Clause,
          nextPruningEvent original props bs.frame bs.learned = .stable ∧
            wipeoutClause orig bs.trail bs.frame = some w ∧ cs = [w] ∧
            learned = [])) := by
  unfold terminalResult at h
  split at h
  · rename_i hev
    split at h
    · rename_i w hw
      cases h
      exact ⟨rfl, Or.inr (Or.inr ⟨w, hev, hw, rfl, rfl⟩)⟩
    · cases h
  · rename_i cs' hprune
    cases h
    exact ⟨rfl, Or.inl ⟨hprune, rfl⟩⟩
  · rename_i l c lr fl hev
    split at h
    · rename_i hf
      cases h
      exact ⟨rfl, Or.inr (Or.inl ⟨l, c, lr, fl, hev, hf, rfl, rfl⟩)⟩
    · cases h

/-- The terminal `.localExcluded` result is never produced (R1c routing). -/
theorem terminalResult_ne_localExcluded {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {bs : BranchState leaf}
    {s : BranchState leaf} {lit : Option Literal} {reason : Option Clause}
    {learned : List Clause} :
    terminalResult orig original props bs ≠ .localExcluded s lit reason learned := by
  intro h
  unfold terminalResult at h
  split at h
  · split at h <;> cases h
  · cases h
  · split at h <;> cases h

/-- SPEC of the result-returning closure (INTERFACES §2.2, the frozen
`explainedClosureResult_spec`): the carried state is coherent, the
reported new clauses are globally entailed, and each case covers every
leaf solution the input state represented. -/
theorem explainedClosureResult_spec {orig : List Domain}
    (hc : ClosureContract leaf orig original props) (bs : BranchState leaf)
    (hpay : UnitPayload original props) (hreach : ReachableState leaf orig bs)
    (hu : UnitDB bs.learned) :
    ClosureResult.Spec leaf orig bs (explainedClosureResult orig original props bs) := by
  suffices h : ∀ (fuel : Nat) (bs : BranchState leaf),
      Frame.mass bs.frame ≤ fuel → ReachableState leaf orig bs →
      UnitDB bs.learned →
      ClosureResult.Spec leaf orig bs
        (explainedClosureResult orig original props bs) from
    h (Frame.mass bs.frame) bs (Nat.le_refl _) hreach hu
  intro fuel
  induction fuel with
  | zero =>
    intro bs hle hreach _
    rw [explainedClosureResult]
    split
    · rename_i d _
      exfalso
      have hdec := d.decreases
      omega
    · exact terminalResult_spec hc hreach
  | succ fuel ih =>
    intro bs hle hreach hu
    rw [explainedClosureResult]
    split
    · rename_i d hd
      have hdec := d.decreases
      have hmass : Frame.mass
          (narrowState bs d.frame d.literal d.reason d.learned).frame ≤ fuel := by
        simp only [narrowState] at hdec ⊢
        omega
      have hu' : UnitDB
          (narrowState bs d.frame d.literal d.reason d.learned).learned := by
        show UnitDB (d.learned ++ bs.learned)
        exact unitDB_append (hpay hd hu) hu
      have hspec := ih (narrowState bs d.frame d.literal d.reason d.learned)
        hmass (explainedDeduction_narrow_reachable hc hreach hu hd) hu'
      refine ⟨hspec.reachable, hspec.entailed, ?_⟩
      obtain ⟨lr, fl, hev⟩ := explainedDeduction_event hd
      have hcov : ∀ a, leaf a = true → bs.Represents a →
          d.literal.norm.eval a = some true →
          (narrowState bs d.frame d.literal d.reason d.learned).Represents a :=
        explainedStep_narrow_coverage d.filtered
          (explainedDeduction_learned_entailed hd
            (hc.reasonEntailed bs hreach d.literal d.reason lr fl hev))
      have hlit := hc.literalSound bs hreach d.literal d.reason lr fl hev
      generalize hr : explainedClosureResult orig original props
        (narrowState bs d.frame d.literal d.reason d.learned) = r at hspec ⊢
      cases r with
      | stable s =>
          intro a hleaf hrep
          exact hspec.coverage a hleaf (hcov a hleaf hrep (hlit a hleaf hrep))
      | conflict s cs cl => exact hspec.coverage
      | localExcluded s lo rc cl => exact hspec.coverage
    · exact terminalResult_spec hc hreach

/-- Coherence of the result-returning closure (corollary). -/
theorem explainedClosureResult_reachable {orig : List Domain}
    (hc : ClosureContract leaf orig original props) (bs : BranchState leaf)
    (hpay : UnitPayload original props) (hreach : ReachableState leaf orig bs)
    (hu : UnitDB bs.learned) :
    ReachableState leaf orig (explainedClosureResult orig original props bs).state :=
  (explainedClosureResult_spec hc bs hpay hreach hu).reachable

/-- Entailment of the clauses the result-returning closure reports
(corollary). -/
theorem explainedClosureResult_entailed {orig : List Domain}
    (hc : ClosureContract leaf orig original props) (bs : BranchState leaf)
    (hpay : UnitPayload original props) (hreach : ReachableState leaf orig bs)
    (hu : UnitDB bs.learned) :
    ∀ c ∈ (explainedClosureResult orig original props bs).newClauses,
      LearnedEntailed leaf [c] :=
  (explainedClosureResult_spec hc bs hpay hreach hu).entailed

/-- Per-case coverage of the result-returning closure (corollary). -/
theorem explainedClosureResult_coverage {orig : List Domain}
    (hc : ClosureContract leaf orig original props) (bs : BranchState leaf)
    (hpay : UnitPayload original props) (hreach : ReachableState leaf orig bs)
    (hu : UnitDB bs.learned) :
    (explainedClosureResult orig original props bs).Covers bs :=
  (explainedClosureResult_spec hc bs hpay hreach hu).coverage

/-! ### Selected-event characterization

The contract's obligations are stated about the event `nextPruningEvent`
ACTUALLY selects. These lemmas describe what a selected event can be, so
`domExplainedContract` below can DERIVE the semantic fields from
`PropagationContract` and the entailed database instead of asking the
caller for arbitrary conclusion functions. -/

/-- A `.implied` event from the database scan names a DATABASE clause that
is unit in the frame (and never a fresh-learned propagator reason). -/
theorem scanDatabase_implied_facts {original : List Clause} {f : BranchFrame}
    {db : List Clause} {l : Literal} {c : Clause} {lr fl : Bool}
    (h : scanDatabase original f db = .implied l c lr fl) :
    c ∈ db ∧ lr = false ∧ clauseRemaining f c = [l] := by
  induction db with
  | nil => simp [scanDatabase] at h
  | cons d rest ih =>
      rw [scanDatabase] at h
      split at h
      · simp at h
      · rename_i l₀ he
        split at h
        · injection h with h1 h2 h3 h4
          exact ⟨by rw [← h2]; exact List.mem_cons_self .., h3.symm,
            by rw [← h1, ← h2]; exact he⟩
        · obtain ⟨hmem, hlr, hunit⟩ := ih h
          exact ⟨List.mem_cons_of_mem _ hmem, hlr, hunit⟩
      · obtain ⟨hmem, hlr, hunit⟩ := ih h
        exact ⟨List.mem_cons_of_mem _ hmem, hlr, hunit⟩

/-- A `.conflict` event from the database scan names a database clause that
is empty in the frame, and the event carries exactly that clause
(`cs = [c]`, R1c conflict routing). -/
theorem scanDatabase_conflict_facts {original : List Clause} {f : BranchFrame}
    {db : List Clause} {cs : List Clause}
    (h : scanDatabase original f db = .conflict cs) :
    ∃ c ∈ db, clauseRemaining f c = [] ∧ cs = [c] := by
  induction db with
  | nil => simp [scanDatabase] at h
  | cons d rest ih =>
      rw [scanDatabase] at h
      split at h
      · rename_i he
        cases h
        exact ⟨d, List.mem_cons_self .., he, rfl⟩
      · rename_i l₀ he
        split at h
        · simp at h
        · obtain ⟨c, hmem, hunit, hcs⟩ := ih h
          exact ⟨c, List.mem_cons_of_mem _ hmem, hunit, hcs⟩
      · obtain ⟨c, hmem, hunit, hcs⟩ := ih h
        exact ⟨c, List.mem_cons_of_mem _ hmem, hunit, hcs⟩

/-- A `.implied` event from the propagator scan names a registered
propagator run and uses its explanation clause as the reason. P2b: such an
event never requests global learning (`lr = false`); the reason lives on the
trail only. -/
theorem scanPropagators_implied_facts {f : BranchFrame} {props : List Propagator}
    {l : Literal} {c : Clause} {lr fl : Bool}
    (h : scanPropagators f props = .implied l c lr fl) :
    ∃ (p : Propagator), p ∈ props ∧ ∃ (r : Reason),
      p.run (frameState f) = .implied l r ∧ c = r.clause ∧
        lr = false ∧ fl = false := by
  induction props with
  | nil => simp [scanPropagators] at h
  | cons p rest ih =>
      rw [scanPropagators] at h
      split at h
      · obtain ⟨p', hp', r, hrun', hc, hlr, hfl⟩ := ih h
        exact ⟨p', List.mem_cons_of_mem _ hp', r, hrun', hc, hlr, hfl⟩
      · simp at h
      · rename_i l₀ r₀ hrun
        split at h
        · injection h with h1 h2 h3 h4
          exact ⟨p, List.mem_cons_self .., r₀, by rw [← h1]; exact hrun,
            h2.symm, h3.symm, h4.symm⟩
        · obtain ⟨p', hp', r, hrun', hc, hlr, hfl⟩ := ih h
          exact ⟨p', List.mem_cons_of_mem _ hp', r, hrun', hc, hlr, hfl⟩

/-- A `.conflict` event from the propagator scan names a registered
propagator's conflicting run; the event's payload is the empty list when
the explanation is empty (the local case: never a global UNSAT). -/
theorem scanPropagators_conflict_facts {f : BranchFrame} {props : List Propagator}
    {cs : List Clause} (h : scanPropagators f props = .conflict cs) :
    ∃ (p : Propagator), p ∈ props ∧ ∃ (c : Clause),
      p.run (frameState f) = .conflict c ∧
        cs = (if c.isEmpty then [] else [c]) := by
  induction props with
  | nil => simp [scanPropagators] at h
  | cons p rest ih =>
      rw [scanPropagators] at h
      split at h
      · obtain ⟨p', hp', c, hrun', hcs⟩ := ih h
        exact ⟨p', List.mem_cons_of_mem _ hp', c, hrun', hcs⟩
      · rename_i c₀ hrun
        injection h with h1
        exact ⟨p, List.mem_cons_self .., c₀, hrun, h1.symm⟩
      · rename_i l₀ r₀ hrun
        split at h
        · simp at h
        · obtain ⟨p', hp', c, hrun', hcs⟩ := ih h
          exact ⟨p', List.mem_cons_of_mem _ hp', c, hrun', hcs⟩

/-- A selected `.implied` event either comes from the database scan or from
the propagator scan (which runs only on int-viewed frames). -/
theorem nextPruningEvent_implied_cases {original : List Clause}
    {props : List Propagator} {f : BranchFrame} {db : List Clause}
    {l : Literal} {c : Clause} {lr fl : Bool}
    (h : nextPruningEvent original props f db = .implied l c lr fl) :
    scanDatabase original f db = .implied l c lr fl ∨
      (scanDatabase original f db = .stable ∧ frameViewedB f = true ∧
        scanPropagators f props = .implied l c lr fl) := by
  unfold nextPruningEvent at h
  split at h
  · split at h
    · rename_i hsd hv
      exact Or.inr ⟨hsd, hv, h⟩
    · simp at h
  · -- a conflict cannot be an implied event
    rename_i cs heq
    cases h
  · -- the implied event passes the liveness gate (P1 S1′)
    rename_i l' c' lr' fl' heq
    split at h
    · cases h
      exact Or.inl heq
    · simp at h

/-! ### The unit-payload maintenance of the closure

The closure's gated contract fields need the unit discipline at every
intermediate state; these lemmas discharge that maintenance from the
selected-event characterization. `deduction_reason_unit_lower` is the
DAG-lower twin of `Proofs/DomExplained.deduction_reason_unit`. -/

/-- The reason of a selected deduction is a normalized unit clause, given
the kit's unit profile and a unit-learned database (DAG-lower twin). -/
theorem deduction_reason_unit_lower {original : List Clause}
    {props : List Propagator} {bs : BranchState leaf}
    {d : ProductiveDeduction leaf bs}
    (hkit : UnitKit props) (hdb : UnitDB bs.learned)
    (h : explainedDeduction original props bs = some d) :
    ∃ q : Literal, d.reason = [q] ∧ q = q.norm := by
  obtain ⟨c, lr, fl, hev, hr, _⟩ := explainedDeduction_learned_shape h
  rcases nextPruningEvent_implied_cases hev with hsrc | ⟨hsd, hview, hprop⟩
  · obtain ⟨hmem, hlr, hunit⟩ := scanDatabase_implied_facts hsrc
    obtain ⟨q, hcq, hqn⟩ := hdb c hmem
    exact ⟨q, by rw [hr, hcq], hqn⟩
  · obtain ⟨p, hpm, r, hrun, hcl, hlr, hfl⟩ :=
      scanPropagators_implied_facts hprop
    obtain ⟨q, hq, hqn⟩ :=
      hkit.1 p hpm (frameState bs.frame) d.literal r hrun
    exact ⟨q, by rw [hr, hcl, hq], hqn⟩

/-- The learned payload of a selected deduction is unit-learned
(DAG-lower twin of `unitLearned_deduction_learned`). -/
theorem unitDB_deduction_learned {original : List Clause}
    {props : List Propagator} {bs : BranchState leaf}
    {d : ProductiveDeduction leaf bs}
    (h : explainedDeduction original props bs = some d)
    (hunit : ∃ q : Literal, d.reason = [q] ∧ q = q.norm) :
    UnitDB d.learned := by
  obtain ⟨c, lr, fl, hev, hr, hlearned⟩ := explainedDeduction_learned_shape h
  rw [hlearned]
  exact unitDB_if_single (by rw [← hr]; exact hunit) _

/-- THE CLOSURE'S UNIT-PAYLOAD MAINTENANCE, from the kit profile alone. -/
theorem unitPayload_of_unitKit {original : List Clause}
    {props : List Propagator} (hkit : UnitKit props) :
    UnitPayload original props :=
  fun hd hu => unitDB_deduction_learned hd (deduction_reason_unit_lower hkit hu hd)

/-- A DATABASE-sourced implied event passes the liveness gate (P1 S1′):
    the event equality plus the scan equation force `frameLiveB`. This is
    the inhabitation source the contract's learned-half derivations
    consume (the propagator-sourced row carries its own recorded
    falsifiers and needs no inhabitation). -/
theorem nextPruningEvent_dbImplied_live {original : List Clause}
    {props : List Propagator} {f : BranchFrame} {db : List Clause}
    {l : Literal} {c : Clause} {lr fl : Bool}
    (hsd : scanDatabase original f db = .implied l c lr fl)
    (h : nextPruningEvent original props f db = .implied l c lr fl) :
    frameLiveB f = true := by
  unfold nextPruningEvent at h
  rw [hsd] at h
  by_cases hg : frameLiveB f = true
  · exact hg
  · exfalso
    have hgf : frameLiveB f = false := by
      cases h' : frameLiveB f <;> simp_all
    simp [hgf] at h

/-- A selected `.conflict` event either comes from the database scan or from
the propagator scan. -/
theorem nextPruningEvent_conflict_cases {original : List Clause}
    {props : List Propagator} {f : BranchFrame} {db : List Clause}
    {cs : List Clause}
    (h : nextPruningEvent original props f db = .conflict cs) :
    scanDatabase original f db = .conflict cs ∨
      (scanDatabase original f db = .stable ∧ frameViewedB f = true ∧
        scanPropagators f props = .conflict cs) := by
  unfold nextPruningEvent at h
  split at h
  · split at h
    · rename_i hsd hv
      exact Or.inr ⟨hsd, hv, h⟩
    · simp at h
  · -- the database's conflict is carried
    rename_i cs' heq
    exact Or.inl (heq.trans h)
  · -- an implied event (gated or not) cannot be a conflict
    rename_i l' c' lr' fl' heq
    split at h
    · cases h
    · cases h

/-- A literal that is not "impossible" in the frame names an in-range
slot: `literalImpossible` reads the full box at the literal's slot, and an
out-of-range slot has the empty domain, which makes every literal
impossible. -/
theorem slot_lt_of_not_impossible {f : BranchFrame} {l : Literal}
    (h : literalImpossible f l = false) :
    l.atom.slot < (fullDomains f).length := by
  by_cases hlt : l.atom.slot < (fullDomains f).length
  · exact hlt
  · exfalso
    have hlen : (Frame.domains f).length ≤ l.atom.slot := by
      simpa only [fullDomains] using Nat.le_of_not_lt hlt
    have hnil : (Frame.domains f).getD l.atom.slot Dom.empty = Dom.empty := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]
      rfl
    have htrue : literalImpossible f l = true := by
      simp only [literalImpossible, hnil, Dom.enum_empty, List.all_nil]
    rw [htrue] at h
    exact Bool.noConfusion h

/-- A unit database clause's remaining literal names an in-range slot:
`clauseRemaining` drops exactly the literals NO frame value can satisfy,
and a slot outside the full box has an empty domain (whose `all` is
vacuously true). Derived, not assumed. -/
theorem slot_lt_of_unit_clause {f : BranchFrame} {c : Clause} {l : Literal}
    (hunit : clauseRemaining f c = [l]) :
    l.atom.slot < (fullDomains f).length := by
  have hf : l ∈ c.filter (fun x => !literalImpossible f x) := by
    rw [show c.filter (fun x => !literalImpossible f x) = clauseRemaining f c
      from rfl, hunit]
    exact List.mem_singleton_self _
  have hnotimp : literalImpossible f l = false := by
    have h2 := (List.mem_filter.mp hf).2
    simpa using h2
  exact slot_lt_of_not_impossible hnotimp

/-! ### The concrete-domain constructor

`domExplainedContract` assembles the whole-run contract from the supported
problem gates, the existing `PropagationContract`, and per-kind
evidential obligations. The SEMANTIC fields (`literalSound`,
`reasonEntailed`, `conflictExcludes`, `conflictEntailed`) are DERIVED from
the selected event; the remaining fields are exactly the obligations the
ledger assigns to A3's concrete kit:

* `PropagatorEvidence` — per-propagator explanation facts beyond
  `PropagationContract`: normalized pivot membership, slot range, and the
  recorded trail entries for the explanation's non-pivot literals;
* `UnitClauseEvidence` — the database-clause hygiene discipline: a learned
  clause that is unit in the frame has its normalized pivot and recorded
  falsifiers. (Its slot range is derived by `slot_lt_of_unit_clause`.) -/

/-- A membership in the propagator conflict payload identifies the
explanation clause and shows it is nonempty (the payload is `[]` exactly
for an empty explanation, the local case). -/
theorem mem_conflict_payload {c c' : Clause}
    (h : c' ∈ (if c.isEmpty then [] else [c])) : c' = c ∧ c ≠ [] := by
  cases c with
  | nil => simp at h
  | cons x xs =>
      refine ⟨?_, by simp⟩
      have h' : c' ∈ [x :: xs] := by simpa [List.isEmpty_cons] using h
      simpa using h'

/-- Propagator-side explanation obligations beyond `PropagationContract`. -/
structure PropagatorEvidence (leaf : Assignment → Bool)
    (props : List Propagator) : Prop where
  /-- the explaining clause contains the normalized pivot -/
  pivot : ∀ f, frameViewedB f = true → ∀ p ∈ props, ∀ l r,
    p.run (frameState f) = .implied l r → (l.norm ∈ r.clause) = True
  /-- the pivot names an in-range slot -/
  inRange : ∀ f, frameViewedB f = true → ∀ p ∈ props, ∀ l r,
    p.run (frameState f) = .implied l r → l.atom.slot < (fullDomains f).length
  /-- the explanation's non-pivot literals were recorded on the trail (the
      `DomReasonRecorded` witness-list form) -/
  recorded : ∀ (bs : BranchState leaf), ∀ p ∈ props, ∀ l r,
    p.run (frameState bs.frame) = .implied l r →
      DomReasonRecorded leaf bs l r.clause

/-- Database-clause-side explanation hygiene. -/
structure UnitClauseEvidence (leaf : Assignment → Bool)
    (orig : List Domain) : Prop where
  /-- a unit learned clause contains its normalized pivot (gated by the
      unit-database discipline; see `Proofs/ClosureRefutation.lean`) -/
  pivot : ∀ (bs : BranchState leaf), ReachableState leaf orig bs →
    UnitDB bs.learned →
    ∀ c ∈ bs.learned, ∀ l, clauseRemaining bs.frame c = [l] →
      frameLiveB bs.frame = true → (l.norm ∈ c) = True
  /-- its non-pivot literals were recorded on the trail (gated) -/
  recorded : ∀ (bs : BranchState leaf), ReachableState leaf orig bs →
    UnitDB bs.learned →
    ∀ c ∈ bs.learned, ∀ l, clauseRemaining bs.frame c = [l] →
      frameLiveB bs.frame = true →
      DomReasonRecorded leaf bs l c

/-- CONCRETE (domain driver): build the whole-run contract. The
branch-relative literal soundness, reason entailment and the conflict row's
evidence are DERIVED from the selected event (propagator contract, entailed
database, `clauseRemaining` unit shape); the propagator/clause pivot,
range and recorded-entry obligations remain A3's to discharge for the
concrete propagators and clauses. -/
theorem domExplainedContract
    (hOriginal : ∀ c ∈ original, ∀ a, leaf a = true → c.SatisfiedBy a)
    (hViewed : ∀ d ∈ orig, IntViewedDomain d)
    (hSorts : DomsShapeTyped orig)
    (hLeafFits : ∀ a, leaf a = true → a.Fits orig)
    (hp : PropagationContract leaf props)
    (hProp : PropagatorEvidence leaf props)
    (hUnit : UnitClauseEvidence leaf orig) :
    ClosureContract leaf orig original props where
  originalEntailed := hOriginal
  leafFits := hLeafFits
  origViewed := hViewed
  literalSound := by
    intro bs hreach l c lr fl hev a hleaf hrep
    rcases nextPruningEvent_implied_cases hev with hdb | ⟨hsd, hview, hprop⟩
    · -- database clause: unit shape + global entailment imply the literal
      obtain ⟨hmem, hlr, hunit⟩ := scanDatabase_implied_facts hdb
      have hent : c.SatisfiedBy a := hreach.wf.2.2.2.2 c hmem a hleaf
      have hlit := clauseRemaining_singleton_implies hrep.1 hent hunit
      rwa [Literal.norm_eval]
    · -- propagator run: the existing contract's implication
      obtain ⟨p, hpm, r, hrun, hcl, hlr, hfl⟩ := scanPropagators_implied_facts hprop
      have hlit := hp.implied bs.frame hview p hpm l r hrun a hleaf hrep.1
      rwa [Literal.norm_eval]
  reasonEntailed := by
    intro bs hreach l c lr fl hev
    rcases nextPruningEvent_implied_cases hev with hdb | ⟨hsd, hview, hprop⟩
    · obtain ⟨hmem, hlr, hunit⟩ := scanDatabase_implied_facts hdb
      intro c' hc' a hleaf
      rw [List.mem_singleton] at hc'
      rw [hc']
      exact hreach.wf.2.2.2.2 c hmem a hleaf
    · obtain ⟨p, hpm, r, hrun, hcl, hlr, hfl⟩ := scanPropagators_implied_facts hprop
      rw [hcl]
      intro c' hc' a hleaf
      rw [List.mem_singleton] at hc'
      rw [hc']
      exact hp.reason bs.frame hview p hpm l r hrun a hleaf
  pivot := by
    intro bs hreach hu l c lr fl hev
    rcases nextPruningEvent_implied_cases hev with hdb | ⟨hsd, hview, hprop⟩
    · obtain ⟨hmem, hlr, hunit⟩ := scanDatabase_implied_facts hdb
      exact hUnit.pivot bs hreach hu c hmem l hunit
        (nextPruningEvent_dbImplied_live hdb hev)
    · obtain ⟨p, hpm, r, hrun, hcl, hlr, hfl⟩ := scanPropagators_implied_facts hprop
      rw [hcl]
      exact hProp.pivot bs.frame hview p hpm l r hrun
  chronology := by
    intro bs hreach hu l c lr fl hev
    rcases nextPruningEvent_implied_cases hev with hdb | ⟨hsd, hview, hprop⟩
    · obtain ⟨hmem, hlr, hunit⟩ := scanDatabase_implied_facts hdb
      exact stepChronology_of_domReasonRecorded
        (hUnit.recorded bs hreach hu c hmem l hunit
          (nextPruningEvent_dbImplied_live hdb hev))
    · obtain ⟨p, hpm, r, hrun, hcl, hlr, hfl⟩ := scanPropagators_implied_facts hprop
      rw [hcl]
      exact stepChronology_of_domReasonRecorded (hProp.recorded bs p hpm l r hrun)
  inRange := by
    intro bs hreach l c lr fl hev
    rcases nextPruningEvent_implied_cases hev with hdb | ⟨hsd, hview, hprop⟩
    · obtain ⟨hmem, hlr, hunit⟩ := scanDatabase_implied_facts hdb
      exact slot_lt_of_unit_clause hunit
    · obtain ⟨p, hpm, r, hrun, hcl, hlr, hfl⟩ := scanPropagators_implied_facts hprop
      exact hProp.inRange bs.frame hview p hpm l r hrun
  conflictExcludes := by
    intro bs hreach cs hev a hleaf hrep
    rcases nextPruningEvent_conflict_cases hev with hdb | ⟨hsd, hview, hprop⟩
    · -- database refutation: the recovered clause is entailed and empty
      obtain ⟨c, hmem, hunit, hcs⟩ := scanDatabase_conflict_facts hdb
      have hent : c.SatisfiedBy a := hreach.wf.2.2.2.2 c hmem a hleaf
      exact clauseRemaining_empty_excludes hrep.1 hunit hent
    · obtain ⟨p, hpm, c, hrun, hcs⟩ := scanPropagators_conflict_facts hprop
      exact hp.conflict bs.frame hview p hpm c hrun a hleaf hrep.1
  conflictEntailed := by
    intro bs hreach cs hev
    rcases nextPruningEvent_conflict_cases hev with hdb | ⟨hsd, hview, hprop⟩
    · obtain ⟨c, hmem, hunit, hcs⟩ := scanDatabase_conflict_facts hdb
      rw [hcs]
      intro c' hc' a hleaf
      rw [List.mem_singleton] at hc'
      rw [hc']
      exact hreach.wf.2.2.2.2 c hmem a hleaf
    · obtain ⟨p, hpm, c, hrun, hcs⟩ := scanPropagators_conflict_facts hprop
      rw [hcs]
      intro c' hc' a hleaf
      obtain ⟨hc'', hne⟩ := mem_conflict_payload hc'
      rw [hc'']
      exact hp.conflictReason bs.frame hview p hpm c hrun hne a hleaf
        (frameFaithful_of_domSub hViewed hSorts (hLeafFits a hleaf)
          ⟨hreach.length_ok, hreach.full_fits⟩)

/-! ### The `x ≠ y` acceptance example (PLAN P1.1)

Two Boolean slots `x` (slot 0) and `y` (slot 1) with the leaf semantics
`x ≠ y`. The example state has DECIDED `x = false` (a genuine branch) and
has learned the globally entailed clause `¬(x = false) ∨ y = true`
("x = true ∨ y = true", a consequence of `x ≠ y`). The selected deduction
is then the unit literal `y = true`, whose reason is that clause:

* the pivot is NOT globally true — the leaf solution `x = true, y = false`
  falsifies it (the counterexample for which I0 withdrew the global
  `literalSound`);
* it DOES hold at every leaf solution the decided state represents: the
  trail records `x = false`, and the learned clause then forces `y =
  true`. This is the branch-relative obligation;
* chronology is supplied by the decision entry: the reason's non-pivot
  literal `¬(x = false)` has the decision literal as its exact negation;
* the closure's narrowing row therefore applies: the frame narrows to
  `y = true`, the entry is recorded with its reason, and the narrowed
  state is reachable and covers every represented leaf solution. -/

/-- The signed negation of a Boolean equality: `¬(slot = b)`. Written so
that the decision literal `posBool 0 false` is its exact negation. -/
private def negBool (s : Nat) (b : Bool) : Literal := ⟨.boolEq s b, false⟩

/-- Two Boolean slots, both admitting `true` and `false`. -/
private def xyOrig : List Domain :=
  [Dom.ofList [.bool true, .bool false], Dom.ofList [.bool true, .bool false]]

/-- A Boolean slot reading with default `false` (`Value` carries no
`DecidableEq`, so the reading is defined by matching). -/
private def xyValue (a : Assignment) (s : Nat) (b : Bool) : Bool :=
  match a[s]? with
  | some (.bool actual) => actual == b
  | _ => false

/-- The `x ≠ y` leaf semantics. -/
private def xyLeaf : Assignment → Bool := fun a =>
  (xyValue a 0 true && xyValue a 1 false) ||
  (xyValue a 0 false && xyValue a 1 true)

/-- The globally entailed reason clause `¬(x = false) ∨ y = true`. -/
private def xyClause : Clause := [negBool 0 false, posBool 1 true]

/-- The decision entry: literal `x = false`, recorded at level 1. -/
private def xyDecision : TrailEntry :=
  { literal := posBool 0 false, level := 1, reason := none }

/-- The root state of the example. -/
private def xyRoot : BranchState xyLeaf :=
  BranchState.init (⟨xyOrig, []⟩ : BranchFrame)

/-- The DECIDED child: slot 0 pinned to `false`. The head remaining domain
has a second value, so the pin is a genuine branch. -/
private def xyChild : BranchState xyLeaf :=
  { xyRoot.decide (BranchState.pinLiteral 0 false) with
    frame := xyRoot.frame.pin 0 (.bool false) }

/-- The example state: the child learned the entailed reason clause. -/
private def xyState : BranchState xyLeaf := xyChild.learnGlobal xyClause

/-- The decided child's trail is exactly the decision entry. -/
private theorem xyChild_trail : xyChild.trail = [xyDecision] := rfl

/-- A Boolean slot reading is `true` exactly at the named Boolean value. -/
private theorem xyValue_eq_true {a : Assignment} {s : Nat} {b : Bool} :
    xyValue a s b = true ↔ a[s]? = some (.bool b) := by
  cases b with
  | true =>
      cases h : a[s]? with
      | none => simp [xyValue, h]
      | some val => cases val <;> simp [xyValue, h]
  | false =>
      cases h : a[s]? with
      | none => simp [xyValue, h]
      | some val => cases val <;> simp [xyValue, h]

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

/-- The pin's normalized form (the decision entry's literal). -/
private theorem pinLiteral_norm :
    (BranchState.pinLiteral 0 false).norm = posBool 0 false := rfl

/-- The decision is a genuine branching pin, so the child is reachable
(`reachable_decide_of_second_value` discharges the freshness premise from
the second value of the head remaining domain). -/
private theorem xyChild_reachable : ReachableState xyLeaf xyOrig xyChild := by
  have h := reachable_decide_of_second_value (leaf := xyLeaf)
    (reachable_init xyLeaf xyOrig)
    (k := 0) (v := .bool false) (w' := .bool true)
    (d := Dom.ofList [.bool true, .bool false])
    (l := BranchState.pinLiteral 0 false)
    rfl (by simp [mem_ofList_iff]) (by simp [mem_ofList_iff]) (by intro h; cases h)
    (fun a => by
      show (BranchState.pinLiteral 0 false).norm.eval a = some true ↔
        a[0]? = some (.bool false)
      rw [pinLiteral_norm]
      exact eval_posBool_iff a 0 false)
    ⟨[Value.bool true, Value.bool true], by
      show [Value.bool true, Value.bool true] ∈
        allAssigns [Dom.ofList [Value.bool true, Value.bool false],
          Dom.ofList [Value.bool true, Value.bool false]]
      rw [mem_allAssigns_cons_iff]
      refine ⟨Value.bool true, by simp [mem_ofList_iff], [Value.bool true], ?_, rfl⟩
      rw [mem_allAssigns_cons_iff]
      exact ⟨Value.bool true, by simp [mem_ofList_iff], [],
        by simp [allAssigns], rfl⟩⟩
  exact h

/-- The reason clause is globally entailed by `x ≠ y`. -/
private theorem xyClause_entailed : LearnedEntailed xyLeaf [xyClause] := by
  intro c hc a ha
  rw [List.mem_singleton] at hc
  rw [hc]
  have ha' : (xyValue a 0 true = true ∧ xyValue a 1 false = true) ∨
      (xyValue a 0 false = true ∧ xyValue a 1 true = true) := by
    simpa only [xyLeaf, Bool.or_eq_true, Bool.and_eq_true] using ha
  rcases ha' with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have hx : a[0]? = some (.bool true) := xyValue_eq_true.mp h0
    refine ⟨negBool 0 false, by simp [xyClause], ?_⟩
    exact negBool_eval_true_iff.mpr hx
  · have hy : a[1]? = some (.bool true) := xyValue_eq_true.mp h1
    refine ⟨posBool 1 true, by simp [xyClause], ?_⟩
    exact (eval_posBool_iff a 1 true).mpr hy

/-- The example state is reachable (learning an entailed clause only grows
the database). -/
private theorem xyState_reachable : ReachableState xyLeaf xyOrig xyState :=
  reachable_learnGlobal xyChild_reachable xyClause_entailed

/-- GLOBAL FALSITY: the pivot `y = true` is not true at every leaf solution
— `x = true, y = false` is an `x ≠ y` solution that falsifies it. This is
exactly what the withdrawn global `literalSound` demanded. -/
private theorem xy_pivot_not_global :
    ¬ (∀ a, xyLeaf a = true → (posBool 1 true).norm.eval a = some true) := by
  intro h
  have hw := h [.bool true, .bool false] (by decide)
  have hf : (posBool 1 true).eval [.bool true, .bool false] = some false := by
    decide
  rw [Literal.norm_eval, hf] at hw
  exact absurd hw (fun h => by cases h)

/-- BRANCH-RELATIVE TRUTH: the pivot holds at every leaf solution the
DECIDED state represents. The trail pins `x = false`; the learned clause
then rules out its first literal (`¬(x = false)` would force `x = true`),
leaving `y = true`. -/
private theorem xy_pivot_branch_relative :
    ∀ a, xyLeaf a = true → xyState.Represents a →
      (posBool 1 true).norm.eval a = some true := by
  intro a hleaf hrep
  obtain ⟨-, htrail, hlearned⟩ := hrep
  have hdec : (posBool 0 false).eval a = some true := by
    have h := htrail xyDecision (by
      show xyDecision ∈ xyChild.trail
      rw [xyChild_trail]
      exact List.mem_singleton_self _)
    simpa [xyDecision] using h
  have hx : a[0]? = some (.bool false) := (eval_posBool_iff a 0 false).mp hdec
  have hsat := hlearned xyClause (by
    show xyClause ∈ xyClause :: xyChild.learned
    exact List.mem_cons_self ..)
  obtain ⟨l, hl, hleval⟩ := hsat
  rw [xyClause] at hl
  rcases List.mem_cons.mp hl with rfl | hl
  · exfalso
    have hx' : a[0]? = some (.bool true) := negBool_eval_true_iff.mp hleval
    rw [hx] at hx'
    cases hx'
  · have hl' : l = posBool 1 true := by simpa using hl
    rw [hl'] at hleval
    rwa [Literal.norm_eval]

/-- The selected event at the example state: the database clause is unit on
`y = true`. Proven by evaluation. -/
private theorem xy_event : nextPruningEvent [] [] xyState.frame xyState.learned
    = .implied (posBool 1 true) xyClause false true := by
  rfl

/-- The deduction is selected. -/
private theorem xy_deduction :
    ∃ d : ProductiveDeduction xyLeaf xyState,
      explainedDeduction [] [] xyState = some d :=
  ⟨_, rfl⟩

/-- The selected deduction's literal and reason are the expected ones. -/
private theorem xy_deduction_fields
    (e : ProductiveDeduction xyLeaf xyState)
    (he : explainedDeduction [] [] xyState = some e) :
    e.literal = posBool 1 true ∧ e.reason = xyClause := by
  obtain ⟨lr, fl, h2⟩ := explainedDeduction_event he
  rw [xy_event] at h2
  constructor
  · injection h2 with h1 _ _ _
    exact h1.symm
  · injection h2 with _ h2' _ _
    exact h2'.symm

/-- THE ACCEPTANCE EXAMPLE (PLAN P1.1): a decision was made on slot 0, the
selected deduction's pivot is NOT globally true, and the closure still
handles it under the branch-relative contract — the narrowing row applies,
the recorded entry is chronologically justified by the decision entry, and
the narrowed state is reachable and covers every represented leaf
solution. -/
example :
    (∃ a, xyLeaf a = true ∧ (posBool 1 true).norm.eval a = some false) ∧
    (∀ a, xyLeaf a = true → xyState.Represents a →
      (posBool 1 true).norm.eval a = some true) ∧
    (∃ d : ProductiveDeduction xyLeaf xyState,
      explainedDeduction [] [] xyState = some d ∧
      d.literal = posBool 1 true ∧ d.reason = xyClause) ∧
    (∀ d : ProductiveDeduction xyLeaf xyState,
      explainedDeduction [] [] xyState = some d →
      ReachableState xyLeaf xyOrig
        (narrowState xyState d.frame d.literal d.reason d.learned) ∧
      (∀ a, xyLeaf a = true → xyState.Represents a →
        (narrowState xyState d.frame d.literal d.reason d.learned).Represents a)) := by
  obtain ⟨d, hd⟩ := xy_deduction
  obtain ⟨hl, hc⟩ := xy_deduction_fields d hd
  refine ⟨⟨[.bool true, .bool false], by decide, by decide⟩, ?_,
    ⟨d, hd, hl, hc⟩, ?_⟩
  · intro a hleaf hrep
    have hlit := xy_pivot_branch_relative a hleaf hrep
    rwa [Literal.norm_eval] at hlit
  · intro d' hd'
    obtain ⟨hl', hc'⟩ := xy_deduction_fields d' hd'
    have hentReason : LearnedEntailed xyLeaf [d'.reason] := by
      rw [hc']
      exact xyClause_entailed
    have hentLearned := explainedDeduction_learned_entailed hd' hentReason
    have hpivot : (d'.literal.norm ∈ d'.reason) = True := by
      rw [hl', hc']
      decide
    have hin : d'.literal.atom.slot < (fullDomains xyState.frame).length := by
      rw [hl']
      decide
    have hchron : StepChronology xyState d'.literal d'.reason := by
      intro q hq hne
      rw [hc'] at hq
      rw [hl'] at hne
      rw [xyClause] at hq
      rcases List.mem_cons.mp hq with rfl | hq
      · refine ⟨xyDecision, ?_, ?_⟩
        · show xyDecision ∈ xyChild.trail
          rw [xyChild_trail]
          exact List.mem_singleton_self _
        · simp [xyDecision, negBool, Literal.negate, posBool]
      · have hq' : q = posBool 1 true := by simpa using hq
        rw [hq'] at hne
        exact absurd rfl hne
    exact ⟨explainedStep_narrow_reachable xyState_reachable d'.filtered
        (explainedDeduction_fresh hd') hin hentLearned hentReason hpivot hchron,
      fun a hleaf hrep =>
        explainedStep_narrow_coverage d'.filtered hentLearned
          a hleaf hrep (by
            rw [hl']
            exact xy_pivot_branch_relative a hleaf hrep)⟩

end LeanFzn.Solver.Propagation

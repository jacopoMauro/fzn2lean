/-
File: LeanFzn/Solver/Propagation/Proofs/BranchState.lean

Purpose:
  Transition contracts for `BranchState`: initialization, decision,
  explained propagation, learning, and the initialization/projection
  bridges between `BranchState.Represents` and `FrameCovers`. These
  are the frozen interfaces P1.B-P1.D build against; the exact
  missing hypotheses are explicit premises here (see each theorem's
  docstring).

  M2 (sparse switch): the frame is the sparse `BranchFrame` (`doms` +
  `order`), so the former positional "chosen prefix" vocabulary is
  restated slot-wise:
  * `fullDomains f := f.doms` (the box already is the full projection);
  * `PinsForced` replaces `PrefixForced`: every DECIDED slot (member of
    `f.order`) is a singleton and its value is forced by the trail over
    the fitting assignments of the original box;
  * `NarrowingComplete` ranges over the UNDECIDED slots (the positional
    remaining domains) at absolute slot indices.

Dependencies:
  - LeanFzn.Solver.Propagation.BranchState: the state record and relations.
  - LeanFzn.Solver.Propagation.Proofs.Analyze: `norm_norm` (literal normalization
    idempotence, used by the decision/propagation contracts).

DAG:
  BranchState -> Proofs.BranchState
  -> Proofs.ExplainedPropagation (P1.B)
  -> Proofs.ConflictResolution (P1.C, analysis-soundness consumers)
  -> Proofs.BackjumpFrontier  (P1.D).
-/

import LeanFzn.Legacy.Solver.Propagation.BranchState
import LeanFzn.Solver.Propagation.FrameFilter
import LeanFzn.Solver.Propagation.Proofs.Analyze
open LeanFzn.Semantics LeanFzn.Solver.Propagation



namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-! ## The full-box projection (PLAN A1)

All branch reasoning indexes slots in ORIGINAL coordinates. The single
projection is `Frame.domains` / `fullDomains`: the sparse frame's full
per-slot box (decided slots hold their singleton), in original slot order.
The laws below are the ones the closure, the analyzer and the branch
nogood use; no second projection is introduced. -/

/-- The full box of a frame in original slot order (PLAN A1). -/
abbrev fullDomains (f : BranchFrame) : List Domain := Frame.domains f

/-- The full box has one slot per total slot. -/
theorem fullDomains_length (f : BranchFrame) :
    (fullDomains f).length = f.doms.length := rfl

/-- A decided slot reads its pinned singleton. -/
theorem fullDomains_decided {f : BranchFrame} {k : Nat} {v : Value}
    (h : f.doms[k]? = some (Dom.ofList [v])) : (fullDomains f)[k]? = some (Dom.ofList [v]) := h

/-- A map-`enum` singleton read exposes the structural domain at the slot. -/
theorem exists_dom_of_enum_singleton {l : List Domain} {k : Nat} {v : Value}
    (h : l[k]?.map Dom.enum = some [v]) :
    ∃ d, l[k]? = some d ∧ Dom.enum d = [v] := by
  cases hd : l[k]? with
  | none => rw [hd] at h; cases h
  | some d => rw [hd] at h; exact ⟨d, rfl, by simpa using h⟩

/-- A map-`enum` singleton read puts the value in the slot's `getD` read. -/
theorem mem_getD_of_enum_singleton {l : List Domain} {k : Nat} {v : Value}
    (h : l[k]?.map Dom.enum = some [v]) : v ∈ l.getD k Dom.empty := by
  obtain ⟨d, hd, hde⟩ := exists_dom_of_enum_singleton h
  rw [List.getD_eq_getElem?_getD, hd, Option.getD_some]
  exact (DomainLike.mem_iff _ _).mpr (by
    rw [domElems_eq_enum, hde]; exact List.mem_singleton_self v)

/-- A map-`enum` head-cons read exposes the structural domain at the slot. -/
theorem exists_dom_of_enum_cons {l : List Domain} {k : Nat} {v : Value}
    {vs : Domain} (h : l[k]?.map Dom.enum = some (v :: vs.enum)) :
    ∃ d, l[k]? = some d ∧ Dom.enum d = v :: vs.enum := by
  cases hd : l[k]? with
  | none => rw [hd] at h; cases h
  | some d => rw [hd] at h; exact ⟨d, rfl, by simpa using h⟩

/-- Pointwise-subset transfer across a shared prefix: if `bs ⊆ bs'`
slotwise, then `as ++ bs ⊆ as ++ bs'` slotwise. -/
theorem getD_append_subset {as bs bs' : List Domain}
    (h : ∀ i v, v ∈ bs.getD i Dom.empty → v ∈ bs'.getD i Dom.empty) :
    ∀ i v, v ∈ (as ++ bs).getD i Dom.empty → v ∈ (as ++ bs').getD i Dom.empty := by
  intro i v hv
  rw [List.getD_eq_getElem?_getD] at hv ⊢
  rw [List.getElem?_append] at hv ⊢
  by_cases hlt : i < as.length
  · simp only [hlt, if_true] at hv ⊢
    exact hv
  · simp only [hlt, if_false] at hv ⊢
    exact h _ v hv

/-- Filtering narrows the full box pointwise. -/
theorem Frame.domains_subsets {l : Literal} {f g : BranchFrame}
    (hg : filterFrame l f = some g) :
    ∀ i v, v ∈ (Frame.domains g).getD i Dom.empty → v ∈ (Frame.domains f).getD i Dom.empty :=
  filterFrame_subsets hg

/-- A literal recorded on the trail constrains its slot's domain: every
value still present evaluates the literal to `true`. -/
def TrailAgreesFrame (trail : List TrailEntry) (f : BranchFrame) : Prop :=
  ∀ e ∈ trail, ∀ v ∈ (fullDomains f).getD e.literal.atom.slot Dom.empty,
    e.literal.valueHolds v = true

/-- `filterFrame` preserves trail/frame agreement. -/
theorem TrailAgreesFrame_filterFrame {trail : List TrailEntry}
    {l : Literal} {f g : BranchFrame}
    (hag : TrailAgreesFrame trail f) (hg : filterFrame l f = some g) :
    TrailAgreesFrame trail g := by
  intro e he v hv
  exact hag e he v (Frame.domains_subsets hg _ _ hv)

/-- Every decided slot is a singleton and its value is forced by the trail:
any assignment satisfying all trail literals **and fitting the original
box** reads the recorded value at the slot. The `Fits` restriction is
load-bearing (PLAN B2a): the literal language is shape-blind at equal
integer view (`negNe s 0` holds at `.bool false`), so the unrestricted
form is refuted for integer pins with constant `0`/`1`. This replaces the
positional `PrefixForced` (M2): decided slots are exactly `f.order`. -/
def PinsForced (trail : List TrailEntry) (orig : List Domain)
    (f : BranchFrame) : Prop :=
  ∀ k ∈ f.order, ∃ v, f.doms[k]?.map Dom.enum = some [v] ∧
    ∀ a, (∀ e ∈ trail, e.literal.eval a = some true) → a.Fits orig →
      a[k]? = some v

/-- Narrowing is complete: every original value an UNDECIDED slot no longer
admits has a recorded falsifier FOR THAT SLOT on the trail. Decided slots
are covered by `PinsForced`; this is the sparse (per absolute slot) form of
the positional remaining-domain reading. -/
def NarrowingComplete (trail : List TrailEntry) (orig : List Domain)
    (f : BranchFrame) : Prop :=
  ∀ k ∉ f.order, ∀ w, w ∈ orig.getD k Dom.empty → w ∉ f.doms.getD k Dom.empty →
    ∃ e ∈ trail, e.literal.atom.slot = k ∧
      e.literal.valueHolds w = false

/-- THE FRAME/TRAIL BRIDGE (PLAN A1): under coherent reachability, any
original-fitting assignment that satisfies the whole trail is covered
by the frame. Derived once here; the branch nogood and the restoration
paths consume it instead of assuming it. -/
theorem frame_covers_of_trail {bs : BranchState leaf} {orig : List Domain}
    {a : Assignment}
    (hlen : (fullDomains bs.frame).length = orig.length)
    (hfit : a.Fits orig)
    (hpins : PinsForced bs.trail orig bs.frame)
    (hcomplete : NarrowingComplete bs.trail orig bs.frame)
    (htrail : ∀ e ∈ bs.trail, e.literal.eval a = some true) :
    FrameCovers bs.frame a := by
  refine mem_allAssigns_of_getElem? _ _ ?_ ?_
  · rw [hfit.1]
    exact hlen.symm
  · intro j v hv
    by_cases hmem : v ∈ bs.frame.doms.getD j Dom.empty
    · exact hmem
    · exfalso
      have horig : v ∈ orig.getD j Dom.empty := hfit.2 j v hv
      by_cases hdec : j ∈ bs.frame.order
      · obtain ⟨v', hv', hforce⟩ := hpins j hdec
        have haj : a[j]? = some v' := hforce a htrail hfit
        rw [haj] at hv
        have hvv : v' = v := Option.some.inj hv
        subst hvv
        exact hmem (mem_getD_of_enum_singleton hv')
      · obtain ⟨e, he, hslot, hfalse⟩ := hcomplete j hdec v horig hmem
        have hev := htrail e he
        have hread : e.literal.valueHolds v = true :=
          (valueHolds_read (by rw [hslot]; exact hv)).mpr hev
        rw [hread] at hfalse
        simp at hfalse

/-! ## Basic trail lemmas -/

/-- Any entry of `bs.trail ++ [e]` is either an entry of `bs.trail` or
`e` itself. -/
theorem trail_append_entry_mem {bs : BranchState leaf}
    {e e' : TrailEntry} (h : e' ∈ bs.trail ++ [e]) :
    e' ∈ bs.trail ∨ e' = e := by
  rcases List.mem_append.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (List.mem_singleton.mp h)

/-- Membership transfers from the trail prefix into the extended
    trail. -/
theorem trail_mem_append {bs : BranchState leaf} {e : TrailEntry}
    (h : e ∈ bs.trail) : ∀ (t : TrailEntry), e ∈ bs.trail ++ [t] :=
  fun _ => List.mem_append.mpr (Or.inl h)

/-! ## Chronology transfer -/

/-- Chronology is preserved when the trail is extended on the right:
indices into the prefix are unchanged. -/
theorem earlierThan_extend {trail : List TrailEntry} {e' e t : TrailEntry}
    (h : TrailEntry.earlierThan trail e' e) :
    TrailEntry.earlierThan (trail ++ [t]) e' e := by
  obtain ⟨i, j, hi, hj, hval, hvalj, hij⟩ := h
  refine ⟨i, j, ?_, ?_, ?_, ?_, hij⟩ <;>
    all_goals simp [List.getElem_append] <;> first | omega | simp_all

/-- An entry of the prefix is chronologically before the appended
entry: index `i` in the prefix against the last index. -/
theorem earlierThan_append_last {trail : List TrailEntry}
    {t : TrailEntry} {e : TrailEntry}
    (he : e ∈ trail) :
    TrailEntry.earlierThan (trail ++ [t]) e t := by
  obtain ⟨i, hi, hval⟩ := List.getElem_of_mem he
  have hlen : (trail ++ [t]).length = trail.length + 1 := by simp
  refine ⟨i, trail.length, ?_, ?_, ?_, ?_, hi⟩ <;>
    simp [List.getElem_append, List.length_append] <;>
    first | omega | simp_all

/-! ## Initialization and projection bridges -/

/-- Initialization bridge: the fresh branch state represents exactly
the assignments its frame covers, with no trail and no learned
clauses to constrain them. This is the projection lemma connecting
`BranchState.Represents` to `FrameCovers` (PLAN P1.A item 3). -/
theorem BranchState.init_represents_iff (f : BranchFrame)
    (a : Assignment) :
    (BranchState.init (leaf := leaf) f).Represents a ↔ FrameCovers f a := by
  constructor
  · intro ⟨hcov, _, _⟩; exact hcov
  · intro hcov
    refine ⟨hcov, ?_, ?_⟩
    · intro e he
      simp only [BranchState.init] at he
      cases he
    · intro c hc
      simp only [BranchState.init] at hc
      cases hc

/-- Initialization is well-formed: the trail is empty and the learned
database is empty, so every conjunct of `WellFormed` holds vacuously. -/
theorem BranchState.init_wellFormed (f : BranchFrame) :
    (BranchState.init (leaf := leaf) f).WellFormed := by
  refine ⟨fun e he => absurd he (by simp [BranchState.init]),
    fun e he => absurd he (by simp [BranchState.init]),
    fun e he => absurd he (by simp [BranchState.init]),
    fun e he => absurd he (by simp [BranchState.init]),
    fun c hc => absurd hc (by simp [BranchState.init])⟩

/-! ## Transition contracts -/

/-- DECISION CONTRACT. A decision at a fresh level preserves the
structural invariant: trail levels, normalization, reason validity,
chronology, and learned-clause entailment all transfer, and the fresh
entry is a level-`(level+1)` decision with no reason. -/
theorem BranchState.decide_wellFormed {bs : BranchState leaf} {l : Literal}
    (h : bs.WellFormed) :
    (bs.decide l).WellFormed := by
  obtain ⟨hlev, hnorm, hreason, hchron, hlearn⟩ := h
  refine ⟨?_, ?_, ?_, ?_, hlearn⟩
  · intro e he
    rcases trail_append_entry_mem he with he | rfl
    · exact Nat.le_trans (hlev e he) (Nat.le_succ _)
    · simp only [BranchState.decide]
      simp
  · intro e he
    rcases trail_append_entry_mem he with he | rfl
    · exact hnorm e he
    · simp only [BranchState.decide]
      rw [norm_norm]
  · intro e he r hr
    rcases trail_append_entry_mem he with he | rfl
    · exact hreason e he r hr
    · simp only [BranchState.decide] at hr
      cases hr
  · intro e he r hr q hq hne
    rcases trail_append_entry_mem he with he | rfl
    · obtain ⟨e'', he'', heq, hlt⟩ := hchron e he r hr q hq hne
      exact ⟨e'', trail_mem_append he'' _, heq, earlierThan_extend hlt⟩
    · simp only [BranchState.decide] at hr
      cases hr

/-- DECISION COVERAGE (forward direction). If `a` is represented by
the old state and satisfies the normalized decision literal, then `a`
is represented by the new state. -/
theorem BranchState.decide_represents_forward {bs : BranchState leaf}
    {l : Literal} {a : Assignment}
    (hrep : bs.Represents a) (hlit : l.norm.eval a = some true) :
    (bs.decide l).Represents a := by
  obtain ⟨hcov, htrail, hlearn⟩ := hrep
  refine ⟨hcov, ?_, hlearn⟩
  intro e he
  rcases trail_append_entry_mem he with he | rfl
  · exact htrail e he
  · exact hlit

/-- DECISION COVERAGE (backward direction). Every assignment
represented by the decided state is represented by the predecessor
and satisfies the decided literal. -/
theorem BranchState.decide_represents_backward {bs : BranchState leaf}
    {l : Literal} {a : Assignment}
    (hrep : (bs.decide l).Represents a) :
    bs.Represents a ∧ l.norm.eval a = some true := by
  obtain ⟨hcov, htrail, hlearn⟩ := hrep
  refine ⟨⟨hcov, fun e he => htrail e (trail_mem_append he _), hlearn⟩, ?_⟩
  have hlast := htrail (TrailEntry.mk l.norm (bs.level + 1) none)
    (List.mem_append.mpr (Or.inr (List.mem_singleton_self _)))
  simp only [BranchState.decide, norm_norm] at hlast
  exact hlast

/-- PROPAGATION CONTRACT. Recording an explained deduction with an
entailed reason whose pivot is the recorded literal preserves
well-formedness, provided the reason's non-pivot literals have
strictly earlier falsifiers on the trail (the chronology hypothesis
is a premise: the propagation layer of P1.B must establish it from
its own evidence). -/
theorem BranchState.recordImplied_wellFormed {bs : BranchState leaf}
    {l : Literal} {r : Reason}
    (h : bs.WellFormed)
    (hent : LearnedEntailed leaf [r.clause])
    (hpivot : (l.norm ∈ r.clause) = True)
    (hchron : ∀ q ∈ r.clause, q ≠ l.norm →
      ∃ e' ∈ bs.trail, e'.literal = q.negate) :
    (bs.recordImplied l r).WellFormed := by
  obtain ⟨hlev, hnorm, hreason, hchron0, hlearn⟩ := h
  refine ⟨?_, ?_, ?_, ?_, hlearn⟩
  · intro e he
    rcases trail_append_entry_mem he with he | rfl
    · exact hlev e he
    · simp only [BranchState.recordImplied]
      simp
  · intro e he
    rcases trail_append_entry_mem he with he | rfl
    · exact hnorm e he
    · simp only [BranchState.recordImplied]
      rw [norm_norm]
  · intro e he r' hr'
    rcases trail_append_entry_mem he with he | rfl
    · exact hreason e he r' hr'
    · simp only [BranchState.recordImplied] at hr'
      injection hr' with hr'
      subst hr'
      exact ⟨hent, hpivot⟩
  · intro e he r' hr' q hq hne
    rcases trail_append_entry_mem he with he | rfl
    · obtain ⟨e'', he'', heq, hlt⟩ := hchron0 e he r' hr' q hq hne
      exact ⟨e'', trail_mem_append he'' _, heq, earlierThan_extend hlt⟩
    · injection hr' with hr'
      subst hr'
      -- the fresh entry is LAST on the extended trail: its falsifiers lie in
      -- the prefix, so plain position transfer through the append works
      obtain ⟨e'', he'', heq⟩ := hchron q hq hne
      refine ⟨e'', trail_mem_append he'' _, heq, ?_⟩
      obtain ⟨i, hi, hval⟩ := List.getElem_of_mem he''
      refine earlierThan_append_last he''

/-- PROPAGATION COVERAGE. An explained deduction preserves the
represented assignments that satisfy the implied literal: the reason
clause is entailed at every leaf solution, so every leaf-solution
satisfying the current trail and the reason's falsified side literals
also satisfies the pivot. The hypothesis `hlit` is the semantic
bridge the propagation layer supplies (for clause reasons it follows
from unit justification; for domain-based deductions P1.B derives it
from bound-witness evidence). -/
theorem BranchState.recordImplied_preserves {bs : BranchState leaf}
    {l : Literal} {r : Reason} {a : Assignment}
    (hrep : bs.Represents a)
    (hlit : l.norm.eval a = some true) :
    (bs.recordImplied l r).Represents a := by
  obtain ⟨hcov, htrail, hlearn⟩ := hrep
  refine ⟨hcov, ?_, hlearn⟩
  intro e he
  rcases trail_append_entry_mem he with he | rfl
  · exact htrail e he
  · exact hlit

/-- LEARNING CONTRACT. Adding a globally entailed clause preserves
well-formedness. -/
theorem BranchState.learnGlobal_wellFormed {bs : BranchState leaf} {c : Clause}
    (h : bs.WellFormed) (hent : LearnedEntailed leaf [c]) :
    (bs.learnGlobal c).WellFormed := by
  obtain ⟨hlev, hnorm, hreason, hchron, hlearn⟩ := h
  refine ⟨hlev, hnorm, hreason, hchron, ?_⟩
  intro c' hc'
  rcases List.mem_cons.mp hc' with rfl | hc'
  · exact fun a ha => hent c' (List.mem_singleton_self _) a ha
  · exact hlearn c' hc'

/-- RESTORATION COVERAGE (backward direction). Every assignment
represented by the restored state is represented by the original,
provided every original trail entry's level is at most the target
(the restoration premise: the trail is level-monotone, so the filter
keeps a prefix sub-trail). -/
theorem BranchState.restoreLevel_represents {bs : BranchState leaf}
    {target : Nat} {a : Assignment}
    (hlev : ∀ e ∈ bs.trail, e.level ≤ target)
    (hrep : (bs.restoreLevel target).Represents a) :
    bs.Represents a := by
  obtain ⟨hcov, htrail, hlearn⟩ := hrep
  refine ⟨hcov, ?_, hlearn⟩
  intro e he
  exact htrail e (List.mem_filter.mpr ⟨he, by simpa using hlev e he⟩)

/-! ## The reachable-state invariant (PLAN A1) -/

/-- Consing a value of the head domain onto a complete tail keeps it a
complete assignment of the head domain's frame. -/
theorem allAssigns_cons_of_mem {d : Domain} {rest : List Domain}
    {w : Value} {tail : Assignment}
    (hw : w ∈ d) (htail : tail ∈ allAssigns rest) :
    (w :: tail) ∈ allAssigns (d :: rest) := by
  refine mem_allAssigns_of_getElem? _ _ ?_ ?_
  · have hfits := allAssigns_fits rest tail htail
    simp [hfits.1]
  · intro j v hv
    have hfits := allAssigns_fits rest tail htail
    cases j with
    | zero =>
        have hwv : w = v := by simpa using hv
        subst hwv
        exact hw
    | succ j =>
        have htailget : tail[j]? = some v := by simpa using hv
        exact hfits.2 j v htailget

/-- The sparse pin refines coverage: any assignment of the pinned child is
an assignment of the parent (the pinned slot already admitted the value). -/
theorem FrameCovers_pin_subset {f : BranchFrame} {k : Nat} {v : Value}
    {d : Domain} (hd : f.doms[k]? = some d) (hv : v ∈ d) {a : Assignment}
    (h : FrameCovers (f.pin k v) a) : FrameCovers f a := by
  refine mem_allAssigns_of_mem_set (x := Dom.ofList [v]) ?_ h
  intro w hw
  rw [List.getD_eq_getElem?_getD, hd, Option.getD_some]
  rw [mem_ofList_iff] at hw
  rcases List.mem_singleton.mp hw with rfl
  exact hv

/-- The trail is LEVEL-SORTED: levels never decrease along it. This is
the standard CDCL invariant that makes "the falsifier at the current
level" unique, and it is exactly what B2's uniqueness conjunct (precisely
one learned literal is falsified at the current level) consumes: a
falsifier recorded BELOW the current level forces every other falsifier of
the same literal to be below it too. -/
def TrailLevelSorted (trail : List TrailEntry) : Prop :=
  List.Pairwise (fun a b : TrailEntry => a.level ≤ b.level) trail

/-- Appending an entry whose level dominates the trail keeps the trail
level-sorted. This is the shape every trail-extending transition has. -/
theorem levelSorted_append {trail : List TrailEntry} {e : TrailEntry}
    (hs : TrailLevelSorted trail) (hmax : ∀ e' ∈ trail, e'.level ≤ e.level) :
    TrailLevelSorted (trail ++ [e]) := by
  rw [TrailLevelSorted, List.pairwise_append]
  refine ⟨hs, by simp, ?_⟩
  intro a ha b hb
  simp only [List.mem_singleton] at hb
  subst hb
  exact hmax a ha

/-- Prefixes of a level-sorted trail are level-sorted (restoration). -/
theorem levelSorted_of_sublist {trail trail' : List TrailEntry}
    (hs : TrailLevelSorted trail') (h : List.Sublist trail trail') :
    TrailLevelSorted trail :=
  List.Pairwise.sublist h hs

/-- Filtering a level-sorted trail keeps it level-sorted (restoration by
level, `BranchState.restoreLevel`). -/
theorem levelSorted_filter {trail : List TrailEntry} (p : TrailEntry → Bool)
    (hs : TrailLevelSorted trail) : TrailLevelSorted (trail.filter p) :=
  List.Pairwise.sublist (List.filter_sublist) hs

/-- The empty trail is level-sorted. -/
theorem levelSorted_nil : TrailLevelSorted ([] : List TrailEntry) :=
  List.Pairwise.nil

/-! ## The duplicate-safe trail discipline (PLAN A1 item 1)

These are the preservation lemmas the concrete transitions instantiate
(`init`, `decide`, `recordImplied`/`narrowState`, `learnGlobal`,
`restoreLevel`). The discipline is stated once (`TrailLiteralsDistinct`,
in `BranchState.lean`) and `ReachableState` carries it as its eighth
field, so no consumer needs a caller-supplied distinctness hypothesis.

The single non-structural obligation is FRESHNESS of the literal being
recorded (the "branching pin" / absence-checked enqueue). Two discharge
routes are exported:

* `pin_not_forced_of_second_value` — a genuine branch (the live slot has a
  second value and the frame is live) is not forced by the frame, hence
  `ReachableState.fresh_of_not_forced` gives freshness;
* a caller may also skip the redundant decision/enqueue outright; the
  policy theorem `TrailLiteralsDistinct.not_append_of_mem` (with the
  concrete `decide_duplicates`) shows the premise cannot be dropped. -/

namespace TrailLiteralsDistinct

/-- The empty trail carries no duplicates. -/
theorem nil : TrailLiteralsDistinct ([] : List TrailEntry) :=
  ⟨fun e he => absurd he (by simp),
    List.Sublist.nodup (List.nil_sublist _) List.nodup_nil⟩

/-- APPEND PRESERVATION (the reusable lemma A2 instantiates at its
narrowing step): appending a NORMALIZED entry whose literal is fresh
preserves the duplicate-safe discipline. `hnorm` is `ReachableState.wf`'s
normalization conjunct for the existing trail; `henorm` holds for every
entry the transitions append (`norm_norm`); `hfresh` is the
branching-pin/absence-check obligation. -/
theorem append_singleton {trail : List TrailEntry} {e : TrailEntry}
    (hd : TrailLiteralsDistinct trail)
    (hnorm : ∀ e' ∈ trail, e'.literal = e'.literal.norm)
    (henorm : e.literal = e.literal.norm)
    (hfresh : ∀ e' ∈ trail, e'.literal ≠ e.literal) :
    TrailLiteralsDistinct (trail ++ [e]) := by
  constructor
  · intro e₁ h₁ e₂ h₂ hlit
    rcases List.mem_append.mp h₁ with h₁ | h₁
    · rcases List.mem_append.mp h₂ with h₂ | h₂
      · exact hd.1 e₁ h₁ e₂ h₂ hlit
      · rw [List.mem_singleton] at h₂
        exfalso
        exact absurd ((hnorm e₁ h₁).trans (hlit.symm.trans (by rw [h₂])))
          (hfresh e₁ h₁)
    · rw [List.mem_singleton] at h₁
      rw [h₁] at hlit
      rcases List.mem_append.mp h₂ with h₂ | h₂
      · exfalso
        exact absurd (hlit.trans henorm.symm) (hfresh e₂ h₂)
      · rw [List.mem_singleton] at h₂
        rw [h₂, h₁]
  · rw [List.nodup_append]
    refine ⟨hd.2, by simp, ?_⟩
    intro a ha b hb heq
    rw [List.mem_singleton] at hb
    exact hfresh a ha (by rw [heq, hb])

/-- The ENQUEUE shape (`narrowState`, `BranchState.recordImplied`): the
appended entry is the normalized literal at the current level with its
reason. This is the exact instantiation A2's `explainedStep_narrow_reachable`
needs for the `distinct` field. -/
theorem enqueue {trail : List TrailEntry} {l : Literal} {lvl : Nat} {r : Reason}
    (hd : TrailLiteralsDistinct trail)
    (hnorm : ∀ e' ∈ trail, e'.literal = e'.literal.norm)
    (hfresh : ∀ e' ∈ trail, e'.literal ≠ l.norm) :
    TrailLiteralsDistinct
      (trail ++ [{ literal := l.norm, level := lvl, reason := some r }]) :=
  append_singleton hd hnorm (norm_norm l).symm hfresh

/-- The DECISION shape (`BranchState.decide`): the appended entry is a
reason-less normalized literal at the fresh level. -/
theorem decisionEntry {trail : List TrailEntry} {l : Literal} {lvl : Nat}
    (hd : TrailLiteralsDistinct trail)
    (hnorm : ∀ e' ∈ trail, e'.literal = e'.literal.norm)
    (hfresh : ∀ e' ∈ trail, e'.literal ≠ l.norm) :
    TrailLiteralsDistinct
      (trail ++ [{ literal := l.norm, level := lvl, reason := none }]) :=
  append_singleton hd hnorm (norm_norm l).symm hfresh

/-- Restoration (`BranchState.restoreLevel`): filtering a level-sorted
trail by level keeps the duplicate-safe discipline. -/
theorem filter {trail : List TrailEntry} (p : TrailEntry → Bool)
    (hd : TrailLiteralsDistinct trail) :
    TrailLiteralsDistinct (trail.filter p) :=
  ⟨fun e₁ h₁ e₂ h₂ hlit =>
      hd.1 e₁ (List.mem_filter.mp h₁).1 e₂ (List.mem_filter.mp h₂).1 hlit,
    List.Sublist.nodup (List.filter_sublist) hd.2⟩

/-- DUPLICATE POLICY (the theorem that expresses it): appending a
normalized literal that an earlier entry already records at a different
level DESTROYS `TrailLiteralsDistinct`. Hence the branching-pin
freshness premise of `reachable_decide` (and the absence check of the
enqueue path) is necessary, not decorative: a forced decision that pins
an already-recorded value is exactly this shape. -/
theorem not_append_of_mem {trail : List TrailEntry} {l : Literal} {k : Nat}
    {r : Option Reason}
    (hn : l.norm.norm = l.norm)
    (hmem : ∃ e ∈ trail, e.literal = l.norm ∧ e.level ≠ k) :
    ¬ TrailLiteralsDistinct
      (trail ++ [{ literal := l.norm, level := k, reason := r }]) := by
  rintro ⟨hdf, _⟩
  obtain ⟨e, he, hlit, hlevel⟩ := hmem
  have hlitnew : ({ literal := l.norm, level := k, reason := r } : TrailEntry).literal
      = e.literal.norm := by
    show l.norm = e.literal.norm
    rw [hlit, hn]
  have hnew : ({ literal := l.norm, level := k, reason := r } : TrailEntry) = e :=
    hdf e (List.mem_append.mpr (Or.inl he)) _
      (List.mem_append.mpr (Or.inr (List.mem_singleton_self _))) hlitnew
  have hlevel' : k = e.level := by
    have := congrArg TrailEntry.level hnew
    simpa using this
  exact hlevel hlevel'.symm

/-- The FORCED-DECISION instance of the policy: deciding a literal an
earlier entry already records makes the decided state non-distinct. -/
theorem decide_duplicates {bs : BranchState leaf} {l : Literal}
    (hmem : ∃ e ∈ bs.trail, e.literal = l.norm ∧ e.level ≠ bs.level + 1) :
    ¬ TrailLiteralsDistinct (bs.decide l).trail := by
  show ¬ TrailLiteralsDistinct
    (bs.trail ++ [{ literal := l.norm, level := bs.level + 1, reason := none }])
  exact not_append_of_mem (norm_norm l) hmem

end TrailLiteralsDistinct

/-- THE REACHABLE-STATE INVARIANT (PLAN A1): the original domains, the
sparse frame (full box plus decision order), the trail, the level and the
global database cohere. Instantiated at the initial frame
(`reachable_init`) and preserved by decisions (`reachable_decide`),
propagation and learning; no field is an uninstantiated runtime
assumption. -/
structure ReachableState (leaf : Assignment → Bool) (orig : List Domain)
    (bs : BranchState leaf) : Prop where
  /-- the full box has one slot per original slot -/
  length_ok : (fullDomains bs.frame).length = orig.length
  /-- no invented values: every admitted value is an original value
      (also the typed discipline: an original domain admits one value
      shape, so `.bool true` is never exchanged for `.int 1`) -/
  full_fits : ∀ i v, v ∈ (fullDomains bs.frame).getD i Dom.empty → v ∈ orig.getD i Dom.empty
  /-- every decided slot is a singleton and its value is forced by a
      recorded decision, over the typed/represented assignments of the
      original box (the sparse replacement of `PrefixForced`) -/
  pins_forced : PinsForced bs.trail orig bs.frame
  /-- every narrowing literal is sound over the frame: it holds at every
      assignment the frame covers (the semantic form the closure's
      coverage arguments consume) -/
  agrees : ∀ e ∈ bs.trail, ∀ a, FrameCovers bs.frame a →
    e.literal.eval a = some true
  /-- narrowing is complete: removed original values of UNDECIDED slots
      carry falsifiers -/
  narrowing_complete : NarrowingComplete bs.trail orig bs.frame
  /-- the structural trail/database invariant -/
  wf : bs.WellFormed
  /-- the trail is level-sorted: this is what makes the current-level
      falsifier of a literally-unique lookup unique (B2) -/
  sorted : TrailLevelSorted bs.trail
  /-- THE DUPLICATE-SAFE DISCIPLINE (PLAN A1 item 1, INTERFACES §2.1
      FORM 1): trail literals occur at most once up to normalization. The
      transitions must be branching pins / absence-checked enqueues
      (`TrailLiteralsDistinct.decide_duplicates` shows an unrestricted
      forced decision would break this field); consumers cite
      `hreach.distinct` (or the FORM 2 theorem `reachable_distinct`)
      without any caller-supplied hypothesis. -/
  distinct : TrailLiteralsDistinct bs.trail

/-- A covered assignment of a reachable state fits the original box. -/
theorem ReachableState.fits {leaf : Assignment → Bool} {orig : List Domain}
    {bs : BranchState leaf} (h : ReachableState leaf orig bs) {a : Assignment}
    (hcov : FrameCovers bs.frame a) : a.Fits orig := by
  have hf := FrameCovers.fits hcov
  refine ⟨?_, ?_⟩
  · rw [hf.1, h.length_ok]
  · intro i v hv
    exact h.full_fits i v (hf.2 i v hv)

/-- Initialization is reachable: the root frame has the whole original
box, an empty order, an empty trail and the original database. -/
theorem reachable_init (leaf : Assignment → Bool) (orig : List Domain) :
    ReachableState leaf orig
      (BranchState.init (⟨orig, []⟩ : BranchFrame)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · intro i v hv; exact hv
  · intro k hk
    simp [BranchState.init] at hk
  · intro e he
    simp [BranchState.init] at he
  · intro k _ w hw hnot
    exact absurd hw hnot
  · exact BranchState.init_wellFormed _
  · exact levelSorted_nil
  · exact TrailLiteralsDistinct.nil

/-- The SEEDED root (R1c): the same root state with the problem's original
clauses preloaded as the scanned database. Reachable as soon as they are
globally entailed. -/
theorem reachable_seed (leaf : Assignment → Bool) (orig : List Domain)
    (db : List Clause) (h : LearnedEntailed leaf db) :
    ReachableState leaf orig
      ({ BranchState.init (leaf := leaf) (⟨orig, []⟩ : BranchFrame)
         with learned := db }) := by
  have h0 := reachable_init leaf orig
  exact { h0 with wf := ⟨h0.wf.1, h0.wf.2.1, h0.wf.2.2.1, h0.wf.2.2.2.1, h⟩ }

/-- FORM 2 of the distinctness obligation (INTERFACES §2.1): the reachable
invariant IMPLIES the duplicate-safe discipline, so B1/B2/C2 consumers
never take a caller-supplied `TrailLiteralsDistinct` hypothesis. -/
theorem reachable_distinct {leaf : Assignment → Bool} {orig : List Domain}
    {bs : BranchState leaf} (h : ReachableState leaf orig bs) :
    TrailLiteralsDistinct bs.trail :=
  h.distinct

/-- FRESHNESS FROM A FRAME WITNESS (the semantic discharge of the
branching-pin premise): if some frame-covered assignment does not satisfy
the pin, then no trail entry can carry it — `ReachableState.agrees` would
make it hold at every covered assignment. The concrete decision obtains
the witness from a second value of the live slot
(`pin_not_forced_of_second_value`). -/
theorem ReachableState.fresh_of_not_forced {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf} {l : Literal}
    (h : ReachableState leaf orig bs)
    (hnotforced : ∃ a, FrameCovers bs.frame a ∧ l.norm.eval a ≠ some true) :
    ∀ e ∈ bs.trail, e.literal ≠ l.norm := by
  obtain ⟨a, hcov, hne⟩ := hnotforced
  intro e he hlit
  exact hne (by rw [← hlit]; exact h.agrees e he a hcov)

/-- BRANCHING-PIN WITNESS: if the live slot's domain has a second value
`w' ≠ v` and the frame is live, the pin is not forced by the frame. This is
the discharge the concrete decision transition applies (a genuine branch is
not a forced decision). -/
theorem pin_not_forced_of_second_value {bs : BranchState leaf}
    {k : Nat} {v w' : Value} {d : Domain} {l : Literal}
    (hd : bs.frame.doms[k]? = some d) (hv : v ∈ d) (hw' : w' ∈ d)
    (hne : w' ≠ v)
    (hpin : ∀ a, l.norm.eval a = some true ↔ a[k]? = some v)
    (hlive : ∃ a, FrameCovers bs.frame a) :
    ∃ a, FrameCovers bs.frame a ∧ l.norm.eval a ≠ some true := by
  obtain ⟨a, ha⟩ := hlive
  have hk : k < bs.frame.doms.length := (List.getElem?_eq_some_iff.mp hd).1
  have hw'mem : w' ∈ bs.frame.doms.getD k Dom.empty := by
    rw [List.getD_eq_getElem?_getD, hd, Option.getD_some]
    exact hw'
  refine ⟨a.set k w', mem_allAssigns_set_coord ha hk hw'mem, ?_⟩
  intro hev
  have hak : k < a.length := by
    rw [(allAssigns_fits _ _ ha).1]
    exact hk
  have hread : (a.set k w')[k]? = some v := (hpin _).mp hev
  rw [List.getElem?_set_self hak] at hread
  exact hne (Option.some.inj hread)

/-- Decision preservation (PLAN A1): recording a BRANCHING decision for a
value `v` of the live slot `k` — with a pinning literal whose semantics is
`l.norm.eval a = some true ↔ a[k]? = some v` and whose literal is FRESH on
the trail — preserves the reachable invariant while advancing the frame to
the pinned child `f.pin k v`.

The freshness premise is exactly the branching-pin policy: a decision on
a domain that is already a singleton would pin an already-recorded value
and duplicate its entry (`TrailLiteralsDistinct.decide_duplicates`), so
the runtime must either not decide forced values or skip the redundant
entry. `pin_not_forced_of_second_value` + `ReachableState.fresh_of_not_forced`
discharge the premise from a genuine branch; `reachable_decide_of_second_value`
bundles that discharge. -/
theorem reachable_decide {leaf : Assignment → Bool} {orig : List Domain}
    {bs : BranchState leaf} {k : Nat} {v : Value} {d : Domain}
    {l : Literal}
    (h : ReachableState leaf orig bs)
    (hd : bs.frame.doms[k]? = some d) (hv : v ∈ d)
    (hpin : ∀ a : Assignment, a.Fits orig →
      (l.norm.eval a = some true ↔ a[k]? = some v))
    (hfresh : ∀ e ∈ bs.trail, e.literal ≠ l.norm) :
    ReachableState leaf orig
      { (bs.decide l) with frame := bs.frame.pin k v } := by
  have hk : k < bs.frame.doms.length := (List.getElem?_eq_some_iff.mp hd).1
  have hgetv : v ∈ bs.frame.doms.getD k Dom.empty := by
    rw [List.getD_eq_getElem?_getD, hd, Option.getD_some]
    exact hv
  -- the trail of the decided state, for the prefix-transfer arguments
  have htrail_prefix : ∀ e ∈ bs.trail,
      e ∈ (bs.decide l).trail :=
    fun e he => List.mem_append.mpr (Or.inl he)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- length: the pin preserves the box length
    simp only [fullDomains, Frame.domains, BranchFrame.pin_doms, List.length_set]
    exact h.length_ok
  · -- no invented values: the child box is a pointwise subset of the parent's
    intro i w hw
    simp only [fullDomains, Frame.domains, BranchFrame.pin_doms] at hw
    exact h.full_fits i w (getD_set_subset
      (fun w' hw' => by
        rw [mem_ofList_iff] at hw'
        rcases List.mem_singleton.mp hw' with rfl
        simp only [fullDomains, Frame.domains, List.getD_eq_getElem?_getD, hd,
          Option.getD_some]
        exact hv) i w hw)
  · -- pins forced: the new pin is forced by the decision entry; old
    -- decided slots transfer (the pin only writes the decision slot)
    intro k' hk'
    by_cases hkk : k' = k
    · subst hkk
      refine ⟨v, ?_, ?_⟩
      · rw [BranchFrame.pin_doms, List.getElem?_set_self hk]
        simp
      · intro a htrail hfit
        exact (hpin a hfit).mp
          (htrail (TrailEntry.mk l.norm (bs.level + 1) none)
            (by rw [BranchState.decide]
                exact List.mem_append.mpr (Or.inr (List.mem_singleton_self _))))
    · have hcases : k' ∈ bs.frame.order ∨ k' = k := by
        rw [BranchFrame.pin_order] at hk'
        rwa [List.mem_append, List.mem_singleton] at hk'
      rcases hcases with hk'ord | hkk'
      · obtain ⟨v', hv', hforce⟩ := h.pins_forced k' hk'ord
        refine ⟨v', ?_, ?_⟩
        · rw [BranchFrame.pin_doms]
          have hset : (bs.frame.doms.set k (Dom.ofList [v]))[k']? = bs.frame.doms[k']? := by
            rw [List.getElem?_set, if_neg (fun hk_eq => hkk hk_eq.symm)]
          rw [hset, hv']
        · intro a htrail hfit
          exact hforce a (fun e he => htrail e (htrail_prefix e he)) hfit
      · exact absurd hkk' hkk
  · -- every entry holds at every child-covered assignment
    intro e he a hcov
    rw [BranchState.decide] at he
    rcases trail_append_entry_mem he with he | rfl
    · exact h.agrees e he a (FrameCovers_pin_subset hd hv hcov)
    · -- the fresh entry: the pinned value is the child's box value
      have hread : a[k]? = some v :=
        covers_read hcov (by rw [BranchFrame.pin_doms, List.getElem?_set_self hk])
      exact (hpin a (h.fits (FrameCovers_pin_subset hd hv hcov))).mpr hread
  · -- narrowing is complete: the child's undecided slots are the
    -- parent's, and the pin only writes the decision slot
    intro j hj w hw hnot
    rw [BranchFrame.pin_order, List.mem_append, List.mem_singleton, not_or] at hj
    obtain ⟨hj, hjk⟩ := hj
    have hnot' : w ∉ bs.frame.doms.getD j Dom.empty := by
      intro hmem
      apply hnot
      rw [BranchFrame.pin_doms, List.getD_eq_getElem?_getD]
      rw [List.getElem?_set, if_neg (fun hk_eq : k = j => hjk hk_eq.symm)]
      rwa [List.getD_eq_getElem?_getD] at hmem
    obtain ⟨e, he, hslot, hfalse⟩ := h.narrowing_complete j hj w hw hnot'
    exact ⟨e, htrail_prefix e he, hslot, hfalse⟩
  · -- structural well-formedness transfers
    exact BranchState.decide_wellFormed h.wf
  · -- the trail stays level-sorted: the fresh decision sits at the NEW
    -- level, which dominates every existing entry (well-formedness)
    rw [BranchState.decide]
    refine levelSorted_append h.sorted ?_
    intro e' he'
    have hle := h.wf.1 e' he'
    show e'.level ≤ bs.level + 1
    omega
  · -- the duplicate-safe discipline: the decision is a BRANCHING PIN
    rw [BranchState.decide]
    exact TrailLiteralsDistinct.decisionEntry h.distinct h.wf.2.1 hfresh

/-- Convenience: a GENUINE branch — the live slot has a second value and
the frame is live — satisfies the branching-pin freshness premise, so the
concrete decision transition preserves the reachable invariant. (A forced
value must instead be propagated/skipped, never decided:
`TrailLiteralsDistinct.decide_duplicates`.) -/
theorem reachable_decide_of_second_value {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf} {k : Nat} {v w' : Value}
    {d : Domain} {l : Literal}
    (h : ReachableState leaf orig bs)
    (hd : bs.frame.doms[k]? = some d) (hv : v ∈ d)
    (hw' : w' ∈ d) (hne : w' ≠ v)
    (hpin : ∀ a, l.norm.eval a = some true ↔ a[k]? = some v)
    (hlive : ∃ a, FrameCovers bs.frame a) :
    ReachableState leaf orig
      { (bs.decide l) with frame := bs.frame.pin k v } :=
  reachable_decide h hd hv (fun a _ => hpin a)
    (h.fresh_of_not_forced
      (pin_not_forced_of_second_value hd hv hw' hne hpin hlive))

/-- IMPLIED-ENTRY OBLIGATION (PLAN A1): recording a FRAME-IMPLIED, fresh
deduction preserves the reachable invariant. The recorded literal must
hold at every frame-covered assignment (`hagrees` — e.g. a derived bound
supplied by `frameBoundAbove_eval`, or a removal implied by a sparse
domain), be fresh (the absence-checked enqueue), and carry the
`recordImplied_wellFormed` evidence; the frame is untouched, so the
frame-level fields transfer unchanged. -/
theorem reachable_recordImplied {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf} {l : Literal} {r : Reason}
    (h : ReachableState leaf orig bs)
    (hagrees : ∀ a, FrameCovers bs.frame a → l.norm.eval a = some true)
    (hent : LearnedEntailed leaf [r.clause])
    (hpivot : (l.norm ∈ r.clause) = True)
    (hchron : ∀ q ∈ r.clause, q ≠ l.norm →
      ∃ e' ∈ bs.trail, e'.literal = q.negate)
    (hfresh : ∀ e' ∈ bs.trail, e'.literal ≠ l.norm) :
    ReachableState leaf orig (bs.recordImplied l r) := by
  have htrail_prefix : ∀ e ∈ bs.trail,
      e ∈ (bs.recordImplied l r).trail :=
    fun e he => List.mem_append.mpr (Or.inl he)
  refine ⟨h.length_ok, h.full_fits, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨v, hv, hforce⟩ := h.pins_forced k hk
    exact ⟨v, hv, fun a htrail hfit =>
      hforce a (fun e he => htrail e (htrail_prefix e he)) hfit⟩
  · intro e he a hcov
    rcases trail_append_entry_mem he with he | rfl
    · exact h.agrees e he a hcov
    · simpa [BranchState.recordImplied] using hagrees a hcov
  · intro j hj w hw hnot
    obtain ⟨e, he, hslot, hfalse⟩ := h.narrowing_complete j hj w hw hnot
    exact ⟨e, htrail_prefix e he, hslot, hfalse⟩
  · exact BranchState.recordImplied_wellFormed h.wf hent hpivot hchron
  · rw [BranchState.recordImplied]
    refine levelSorted_append h.sorted ?_
    intro e' he'
    have hle := h.wf.1 e' he'
    show e'.level ≤ bs.level
    omega
  · rw [BranchState.recordImplied]
    exact TrailLiteralsDistinct.enqueue h.distinct h.wf.2.1 hfresh

/-- LEARNING OBLIGATION (PLAN A1): adding a globally entailed clause
preserves the reachable invariant — it changes only the shared database. -/
theorem reachable_learnGlobal {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf} {c : Clause}
    (h : ReachableState leaf orig bs) (hent : LearnedEntailed leaf [c]) :
    ReachableState leaf orig (bs.learnGlobal c) :=
  ⟨h.length_ok, h.full_fits, h.pins_forced, h.agrees,
    h.narrowing_complete, BranchState.learnGlobal_wellFormed h.wf hent,
    h.sorted, h.distinct⟩

/-- RESTORATION OBLIGATION (PLAN A1): when the whole trail already sits at
or below the target (the filter `BranchState.restoreLevel` applies is the
identity), the projection preserves the reachable invariant: only the
level is lowered. -/
theorem reachable_restoreLevel {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf} {target : Nat}
    (h : ReachableState leaf orig bs)
    (hlev : ∀ e ∈ bs.trail, e.level ≤ target) :
    ReachableState leaf orig (bs.restoreLevel target) := by
  have htrail : (bs.restoreLevel target).trail = bs.trail := by
    show bs.trail.filter (fun e => e.level ≤ target) = bs.trail
    exact List.filter_eq_self.mpr (fun a ha => by simpa using hlev a ha)
  have hlevel : (bs.restoreLevel target).level = target := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h.length_ok
  · exact h.full_fits
  · intro k hk
    obtain ⟨v, hv, hforce⟩ := h.pins_forced k hk
    exact ⟨v, hv, fun a htrail' hfit =>
      hforce a (fun e he => htrail' e (by rw [htrail]; exact he)) hfit⟩
  · intro e he a hcov
    exact h.agrees e (by rw [← htrail]; exact he) a hcov
  · intro j hj w hw hnot
    obtain ⟨e, he, hslot, hfalse⟩ := h.narrowing_complete j hj w hw hnot
    exact ⟨e, by rw [htrail]; exact he, hslot, hfalse⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := h.wf
    refine ⟨?_, ?_, ?_, ?_, h5⟩
    · intro e he
      have he' : e ∈ bs.trail := by rw [htrail] at he; exact he
      rw [hlevel]
      exact hlev e he'
    · intro e he
      exact h2 e (by rw [htrail] at he; exact he)
    · intro e he r hr
      exact h3 e (by rw [htrail] at he; exact he) r hr
    · intro e he r hr q hq hne
      obtain ⟨e'', he'', heq, hlt⟩ :=
        h4 e (by rw [htrail] at he; exact he) r hr q hq hne
      exact ⟨e'', by rw [htrail]; exact he'', heq, by rw [htrail]; exact hlt⟩
  · rw [htrail]
    exact h.sorted
  · rw [htrail]
    exact h.distinct

/-! ## Frame-derived bounds and their exact trail witnesses (PLAN A1 item 2)

The sparse-domain "deletion-to-bound" transition records a pair whose
falsifier is a DERIVED bound (`s ≥ lo`) rather than an exact trail entry.
The analyzer then needs an exact `findEntryOf` falsifier for the negated
UPGRADED literal (its `orderUpgrade` output), which means the bound entry
must be MATERIALIZED on the trail. The reusable shapes A2/A3 instantiate:

* `FrameBoundAbove` + `frameBoundAbove_eval`: the bound holds at every
  frame-covered assignment, so recording it preserves `agrees` — combine
  with `reachable_recordImplied` to materialize it;
* `recordBound_lookup`: after materialization the bound's negation has an
  exact `findEntryOf` witness at the bound's own slot, at the current
  level;
* `trailLoOf_append_bound` + `orderUpgrade_bound` + `derivedBound_exact_falsifier`:
  the materialized bound is visible to the analyzer's `trailLoOf`/
  `orderUpgrade` machinery, and every scanned `posLe s k` strictly below
  the derived bound has an exact falsifier (a trail entry at the bound's
  slot, at a level at or below the level bound supplied). -/

/-- The frame's full box at slot `s` admits only integer views at or above
`lo` (the frame-level, order-encoded form of "the deletions left the
domain above `lo`"). Bundling the integer view is deliberate: it is the
typed-slot gate (`IntViewedDomain` at one slot) that makes the soundness
lemma unconditional. -/
def FrameBoundAbove (f : BranchFrame) (s : Nat) (lo : Int) : Prop :=
  ∀ v ∈ (fullDomains f).getD s Dom.empty, ∃ i : Int, Value.intView v = some i ∧ lo ≤ i

/-- SOUNDNESS: a frame-derived lower bound holds at every assignment the
frame covers. This is the `agrees` half of materializing the bound entry
via `reachable_recordImplied`. -/
theorem frameBoundAbove_eval {f : BranchFrame} {s : Nat} {lo : Int}
    {a : Assignment} (hs : s < (fullDomains f).length)
    (hb : FrameBoundAbove f s lo) (hcov : FrameCovers f a) :
    (negLe s (lo - 1)).eval a = some true := by
  have hfits := FrameCovers.fits hcov
  have hlen : s < a.length := by
    rw [hfits.1]
    exact hs
  have hv : a[s]? = some a[s] := List.getElem?_eq_getElem hlen
  obtain ⟨v, hv'⟩ : ∃ v, a[s]? = some v := ⟨a[s], hv⟩
  obtain ⟨i, hiv, hlo⟩ := hb v (hfits.2 s v hv')
  rw [eval_negLe_iff]
  refine ⟨i, ?_, by omega⟩
  show slotInt a s = some i
  simpa [slotInt, hv'] using hiv

/-- The lower-bound fold step of `trailLoOf`, named so the attainment and
visibility lemmas can be stated once. -/
private def lowerStep (s : Nat) : Option Int → TrailEntry → Option Int
  | acc, e =>
    match e.literal.atom with
    | .intLe s' k =>
        if s' == s && !e.literal.positive then
          match acc with
          | none => some (k + 1)
          | some c => some (maxI c (k + 1))
        else acc
    | _ => acc

private theorem lowerStep_eq_trailLoOf (trail : List TrailEntry) (s : Nat) :
    trail.foldl (lowerStep s) none = trailLoOf trail s := rfl

/-- An entry of the lower-bound fold whose literal is `¬(s ≤ lo−1)`: the
condition supplies the slot/positivity/level equations. -/
private theorem lowerStep_entry_eq {s s' : Nat} {k lo : Int} {e : TrailEntry}
    (hcond : e.literal.atom = Atom.intLe s' k)
    (hc : (s' == s && !e.literal.positive) = true)
    (hk : k + 1 = lo) :
    e.literal = negLe s (lo - 1) := by
  have hs' : s' = s := by
    have hh := hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hh
    exact hh.1
  have hpos : e.literal.positive = false := by
    have hh := hc
    simp only [Bool.and_eq_true] at hh
    simpa using hh.2
  cases hl : e.literal with
  | mk atom positive =>
      have hcond' : atom = Atom.intLe s' k := by simpa [hl] using hcond
      have hpos' : positive = false := by simpa [hl] using hpos
      rw [hcond', hpos', hs']
      rw [show k = lo - 1 by omega]
      rfl

/-- ATTAINMENT: the lower-bound fold's value is the value of one of its
entries (or of the accumulator). -/
private theorem lowerStep_go_attained {s : Nat} {lo : Int} :
    ∀ (trail : List TrailEntry) (acc : Option Int),
      trail.foldl (lowerStep s) acc = some lo →
      (∃ e ∈ trail, e.literal = negLe s (lo - 1)) ∨ acc = some lo := by
  intro trail
  induction trail with
  | nil => intro acc h; exact Or.inr (by simpa using h)
  | cons e rest ih =>
      intro acc h
      rw [List.foldl_cons] at h
      rcases ih (lowerStep s acc e) h with ⟨w, hw, hlit⟩ | hacc
      · exact Or.inl ⟨w, List.mem_cons_of_mem _ hw, hlit⟩
      · cases acc with
        | none =>
            simp only [lowerStep] at hacc
            split at hacc
            · rename_i s' k hcond
              split at hacc
              · rename_i hc
                exact Or.inl ⟨e, List.mem_cons_self ..,
                  lowerStep_entry_eq hcond hc (Option.some.inj hacc)⟩
              · exact absurd hacc (by simp)
            · exact absurd hacc (by simp)
        | some c =>
            simp only [lowerStep] at hacc
            split at hacc
            · rename_i s' k hcond
              split at hacc
              · rename_i hc
                have hmax : maxI c (k + 1) = lo := Option.some.inj hacc
                by_cases hle : c ≤ k + 1
                · have hk : k + 1 = lo := by
                    have hh := hmax
                    simp only [maxI, if_pos hle] at hh
                    exact hh
                  exact Or.inl ⟨e, List.mem_cons_self ..,
                    lowerStep_entry_eq hcond hc hk⟩
                · have hc' : c = lo := by
                    have hh := hmax
                    simp only [maxI, if_neg hle] at hh
                    exact hh
                  exact Or.inr (by rw [hc'])
              · exact Or.inr hacc
            · exact Or.inr hacc

/-- WITNESS: a trail whose lower bound is `lo` contains an entry whose
literal is exactly `¬(s ≤ lo−1)`. This is what makes the analyzer's
order-upgrade path land on an EXACT `findEntryOf` falsifier instead of a
merely implied bound. -/
theorem trailLoOf_witness {trail : List TrailEntry} {s : Nat} {lo : Int}
    (h : trailLoOf trail s = some lo) :
    ∃ e ∈ trail, e.literal = negLe s (lo - 1) := by
  rw [← lowerStep_eq_trailLoOf trail s] at h
  rcases lowerStep_go_attained trail none h with hw | hacc
  · exact hw
  · simp at hacc

/-- The materialized bound entry's contribution to the lower-bound fold. -/
private theorem lowerStep_bound (s : Nat) (lo : Int) (lvl : Nat) (r : Reason)
    (acc : Option Int) :
    lowerStep s acc { literal := negLe s (lo - 1), level := lvl, reason := some r }
      = (match acc with | none => some lo | some c => some (maxI c lo)) := by
  unfold lowerStep
  simp [negLe, Int.sub_add_cancel]

/-- MATERIALIZATION VISIBILITY: appending a materialized bound entry
`¬(s ≤ lo−1)` makes the analyzer's lower-bound fold return at least `lo`,
so `orderUpgrade` can weaken every `posLe s k` with `k < lo` to the exact
entry. -/
theorem trailLoOf_append_bound {trail : List TrailEntry} {s : Nat} {lo : Int}
    {lvl : Nat} {r : Reason} :
    ∃ lo', trailLoOf (trail ++ [{ literal := negLe s (lo - 1), level := lvl,
                                   reason := some r }]) s = some lo' ∧
      lo ≤ lo' := by
  have hb : trailLoOf (trail ++ [{ literal := negLe s (lo - 1), level := lvl,
                                   reason := some r }]) s
      = List.foldl (lowerStep s) none
          (trail ++ [{ literal := negLe s (lo - 1), level := lvl,
                       reason := some r }]) := rfl
  rw [hb, List.foldl_append, List.foldl_cons, List.foldl_nil, lowerStep_bound]
  generalize hacc : List.foldl (lowerStep s) none trail = acc
  cases acc with
  | none => exact ⟨lo, by simp, Int.le_refl lo⟩
  | some c =>
      refine ⟨maxI c lo, by simp, ?_⟩
      simp only [maxI]; split <;> omega

/-- An entry appended to the trail is found by the exact lookup, provided
its literal is the normalized search literal. -/
theorem findEntryOf_append_self {trail : List TrailEntry} {l : Literal}
    {e : TrailEntry} (h : e.literal = l.norm) :
    findEntryOf (trail ++ [e]) l = some e := by
  unfold findEntryOf
  rw [List.reverse_append, List.reverse_singleton]
  exact List.find?_cons_of_pos (by simp only [litEqB, decide_eq_true_eq]; exact h)

/-- A literal present on the trail (in normalized form) makes the exact
lookup succeed. -/
theorem findEntryOf_isSome_of_mem {trail : List TrailEntry} {l : Literal}
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

/-- `orderUpgrade` on a `posLe` falsified by the trail's lower bound
weakens it to exactly the bound's own entry. -/
theorem orderUpgrade_bound {trail : List TrailEntry} {s : Nat} {k lo : Int}
    (hlo : trailLoOf trail s = some lo) (hk : k < lo) :
    orderUpgrade trail (posLe s k) = posLe s (lo - 1) := by
  simp only [orderUpgrade, posLe, hlo]
  rw [if_pos hk]
  exact ite_true _ _

/-- MATERIALIZED BOUND, EXACT LOOKUP: after recording the bound entry
`¬(s ≤ lo−1)` via `BranchState.recordImplied`, the bound's negation has an
exact `findEntryOf` witness at the bound's own slot, at the current level.
This is the "justifying trail entry at the right slot, at or below the
current level" the plan asks for; A3 combines it with
`reachable_recordImplied` (whose `agrees` premise is
`frameBoundAbove_eval`). -/
theorem recordBound_lookup {bs : BranchState leaf} {s : Nat} {lo : Int}
    {r : Reason} :
    ∃ e, findEntryOf (bs.recordImplied (negLe s (lo - 1)) r).trail
          (negLe s (lo - 1)) = some e ∧
      e.literal = negLe s (lo - 1) ∧ e.literal.atom.slot = s ∧
      e.level = bs.level := by
  have htr : (bs.recordImplied (negLe s (lo - 1)) r).trail
      = bs.trail ++ [{ literal := (negLe s (lo - 1)).norm, level := bs.level,
                       reason := some r }] := rfl
  have hfind : findEntryOf
      (bs.trail ++ [{ literal := (negLe s (lo - 1)).norm, level := bs.level,
                      reason := some r }])
      (negLe s (lo - 1)) =
      some ({ literal := (negLe s (lo - 1)).norm, level := bs.level,
              reason := some r } : TrailEntry) := by
    unfold findEntryOf
    rw [List.reverse_append, List.reverse_singleton]
    exact List.find?_cons_of_pos (by simp only [litEqB, decide_eq_true_eq])
  refine ⟨({ literal := (negLe s (lo - 1)).norm, level := bs.level,
              reason := some r } : TrailEntry), ?_, ?_, ?_, ?_⟩
  · rw [htr]
    exact hfind
  · rfl
  · rfl
  · rfl

/-- DERIVED-BOUND ANALYZER SHAPE (the lemma A2/A3 instantiate): if the
trail's lower bound is `lo` and every trail entry sits at level at most
the supplied level, then the analyzer's `orderUpgrade` weakening of any
`posLe s k` strictly below the bound has an EXACT `findEntryOf` falsifier
at the bound's slot, at a level at or below the level bound. No
`orderUpgrade`/lookup can fail on a scanned literal below a derived
bound. -/
theorem derivedBound_exact_falsifier {trail : List TrailEntry} {s : Nat}
    {k lo : Int} {lvl : Nat} (hlo : trailLoOf trail s = some lo) (hk : k < lo)
    (hlev : ∀ e ∈ trail, e.level ≤ lvl) :
    ∃ e, findEntryOf trail (orderUpgrade trail (posLe s k)).negate = some e ∧
      e.literal.atom.slot = s ∧ e.level ≤ lvl := by
  rw [orderUpgrade_bound hlo hk]
  obtain ⟨e₀, he₀, hlit₀⟩ := trailLoOf_witness hlo
  obtain ⟨e, he⟩ : ∃ e, findEntryOf trail (posLe s (lo - 1)).negate = some e :=
    findEntryOf_isSome_of_mem he₀ (by rw [hlit₀]; rfl)
  have hlit : e.literal = negLe s (lo - 1) := by
    simpa only [negLe, posLe, Literal.negate, Literal.norm, Bool.not_true] using
      findEntryOf_literal trail _ e he
  exact ⟨e, he, by rw [hlit]; rfl, hlev e (findEntry_mem trail _ e he)⟩

/-! ## Concrete examples (PLAN A1 done criteria)

Each example runs the CONCRETE transitions (`BranchState.init`,
`BranchState.decide`, `BranchState.recordImplied`) and proves the
eight-field `ReachableState` (hence distinctness, level-sortedness and the
frame/trail bridge) for the result, or exhibits the duplicate policy and
the deletion-to-bound witness on concrete data. -/

/-- The root Boolean state of the concrete examples. -/
private def boolRoot : BranchState (fun _ : Assignment => true) :=
  BranchState.init (leaf := fun _ : Assignment => true)
    (⟨[Dom.ofList [.bool true, .bool false]], []⟩ : BranchFrame)

/-- A genuine Boolean branch: the root decided to `true` by the canonical
pin. -/
private def boolChild : BranchState (fun _ : Assignment => true) :=
  { boolRoot.decide (BranchState.pinLiteral 0 true) with
    frame := ⟨[Dom.ofList [.bool true]], [0]⟩ }

/-- CONCRETE BOOLEAN BRANCH (decision example). The live slot has a second
value, so the branching-pin freshness premise is discharged by
`pin_not_forced_of_second_value` from the concrete frame — the decision is
a genuine branch, not a forced one. -/
example :
    ReachableState (leaf := fun _ : Assignment => true)
      [Dom.ofList [.bool true, .bool false]] boolChild := by
  refine reachable_decide_of_second_value (reachable_init _ _)
    (k := 0) (v := .bool true) (w' := .bool false) (d := Dom.ofList [.bool true, .bool false])
    rfl (by simp) (by simp) (by intro h; cases h) ?_
    ⟨[.bool true], by
      show [Value.bool true] ∈ allAssigns [Dom.ofList [Value.bool true, Value.bool false]]
      rw [mem_allAssigns_cons_iff]
      exact ⟨.bool true, by simp, [], by simp [allAssigns], rfl⟩⟩
  · intro a
    show (BranchState.pinLiteral 0 true).norm.eval a = some true ↔
      a[0]? = some (.bool true)
    cases h : a[0]? with
    | none =>
        simp [BranchState.pinLiteral, Literal.boolOfSlot, Literal.norm,
          Literal.eval, Atom.eval, h]
    | some v =>
        cases v <;>
          simp [BranchState.pinLiteral, Literal.boolOfSlot, Literal.norm,
            Literal.eval, Atom.eval, h]

/-- CONCRETE FORCED-DECISION DUPLICATE (policy example). Deciding the same
pin a second time pins a value the first entry already records: the
result is NOT `TrailLiteralsDistinct`. A runtime must therefore skip the
redundant decision (or propagate the forced value), which is exactly the
freshness premise `reachable_decide` carries. -/
example : ¬ TrailLiteralsDistinct
    (boolChild.decide (BranchState.pinLiteral 0 true)).trail := by
  refine TrailLiteralsDistinct.decide_duplicates
    ⟨{ literal := (BranchState.pinLiteral 0 true).norm, level := 1,
        reason := none }, ?_, ?_, ?_⟩
  · simp [boolChild, boolRoot, BranchState.decide, BranchState.init]
  · rfl
  · intro h
    have hl : boolChild.level = 1 := rfl
    exact absurd (hl.symm.trans h) (by decide)

/-! ### Sparse/negative (deletion-to-bound) example

Root frame `[[.int 5]]` under the leaf "slot 0 is 5". Two deductions are
recorded through the concrete `BranchState.recordImplied` — the deletion
`s ≠ 0` and the materialized derived lower bound `s ≥ 5` (`¬(s ≤ 4)`) —
each with its frame-implied `agrees` evidence (`frameBoundAbove_eval` for
the bound). The result is a full `ReachableState`, and the analyzer's
exact lookup for a scanned literal below the bound is exhibited. -/

/-- The sparse example leaf: slot 0's integer view is 5. -/
private def sparseLeaf : Assignment → Bool := fun a => slotInt a 0 == some 5

/-- The removal step: `BranchState.init` + one explained deletion. -/
private def sparseRemoval : BranchState sparseLeaf :=
  (BranchState.init (leaf := sparseLeaf)
    (⟨[Dom.ofList [.int 5]], []⟩ : BranchFrame)).recordImplied
    (posNe 0 0) { clause := [posNe 0 0] }

/-- The deletion-to-bound step: the materialized lower bound `s ≥ 5`,
written in the canonical `¬(s ≤ lo−1)` form the materialization lemmas
produce. -/
private def sparseState : BranchState sparseLeaf :=
  sparseRemoval.recordImplied (negLe 0 (5 - 1)) { clause := [negLe 0 (5 - 1)] }

/-- Every assignment the root `[[.int 5]]` frame covers has slot 0 equal
to `.int 5` (typed-slot reading). -/
private theorem sparseFrame_slotInt {a : Assignment}
    (hcov : FrameCovers (⟨[Dom.ofList [.int 5]], []⟩ : BranchFrame) a) :
    slotInt a 0 = some 5 := by
  have hfits := FrameCovers.fits hcov
  have hlen : 0 < a.length := by
    rw [hfits.1]
    simp [fullDomains, Frame.domains]
  have hv : a[0]? = some a[0] := List.getElem?_eq_getElem hlen
  obtain ⟨v, hv'⟩ : ∃ v, a[0]? = some v := ⟨a[0], hv⟩
  have hmem : v ∈ (Dom.ofList [.int 5] : Domain) := by
    have h := hfits.2 0 v hv'
    simpa [fullDomains, Frame.domains] using h
  rw [mem_ofList_iff, List.mem_singleton] at hmem
  rw [hmem] at hv'
  simp only [slotInt, hv', Option.bind_some]
  rfl

/-- The root `[[.int 5]]` frame implies the derived lower bound `s ≥ 5`. -/
private theorem sparseFrame_bound :
    FrameBoundAbove (⟨[Dom.ofList [.int 5]], []⟩ : BranchFrame) 0 5 := by
  intro v hv
  have hmem : v ∈ (Dom.ofList [.int 5] : Domain) := by
    simpa [FrameBoundAbove, Frame.domains] using hv
  rw [mem_ofList_iff, List.mem_singleton] at hmem
  rw [hmem]
  exact ⟨5, rfl, Int.le_refl 5⟩

/-- `frameBoundAbove_eval` instantiated at the example frame. -/
private theorem sparseFrame_eval_bound {a : Assignment}
    (hcov : FrameCovers (⟨[Dom.ofList [.int 5]], []⟩ : BranchFrame) a) :
    (negLe 0 4).eval a = some true :=
  frameBoundAbove_eval (f := (⟨[Dom.ofList [.int 5]], []⟩ : BranchFrame)) (s := 0) (lo := 5)
    (a := a) (by simp [fullDomains, Frame.domains]) sparseFrame_bound hcov

/-- SPARSE EXAMPLE, STEP 1: the deletion `s ≠ 0` is recorded through the
concrete `recordImplied` and the state stays reachable. -/
private theorem sparseRemoval_reachable :
    ReachableState sparseLeaf [Dom.ofList [.int 5]] sparseRemoval := by
  refine reachable_recordImplied (reachable_init _ _) ?_ ?_ ?_ ?_ ?_
  · -- `s ≠ 0` holds at every root-covered assignment
    intro a hcov
    show (posNe 0 0).eval a = some true
    rw [eval_posNe_iff]
    exact ⟨5, sparseFrame_slotInt hcov, by omega⟩
  · -- entailment: the leaf forces slot 0 to 5, hence `s ≠ 0`
    intro c hc a ha
    have hc' : c = [posNe 0 0] := by simpa using hc
    have h5 : slotInt a 0 = some 5 := by simpa [sparseLeaf, beq_iff_eq] using ha
    rw [hc']
    refine ⟨posNe 0 0, List.mem_singleton_self _, ?_⟩
    show (posNe 0 0).eval a = some true
    rw [eval_posNe_iff]
    exact ⟨5, h5, by omega⟩
  · -- the recorded literal is the reason's pivot
    change (posNe 0 0 ∈ [posNe 0 0]) = True
    simp
  · -- chronology (the reason clause is the unit `[s ≠ 0]`)
    intro q hq hne
    exact absurd (List.mem_singleton.mp hq) hne
  · -- freshness: the trail is empty
    intro e he
    simp [BranchState.init] at he

/-- SPARSE EXAMPLE, STEP 2 (deletion-to-bound): the derived lower bound
`s ≥ 5` is materialized on the trail through the concrete
`recordImplied`, with `agrees` supplied by `frameBoundAbove_eval`; the
state is still reachable. -/
private theorem sparseState_reachable :
    ReachableState sparseLeaf [Dom.ofList [.int 5]] sparseState := by
  refine reachable_recordImplied sparseRemoval_reachable ?_ ?_ ?_ ?_ ?_
  · -- the derived bound holds at every root-covered assignment
    intro a hcov
    exact sparseFrame_eval_bound hcov
  · -- entailment: the leaf forces slot 0 to 5, hence `s ≥ 5`
    intro c hc a ha
    have hc' : c = [negLe 0 (5 - 1)] := by simpa using hc
    have h5 : slotInt a 0 = some 5 := by simpa [sparseLeaf, beq_iff_eq] using ha
    rw [hc']
    refine ⟨negLe 0 (5 - 1), List.mem_singleton_self _, ?_⟩
    show (negLe 0 (5 - 1)).eval a = some true
    rw [eval_negLe_iff]
    exact ⟨5, h5, by omega⟩
  · -- the recorded literal is the reason's pivot
    change (negLe 0 (5 - 1) ∈ [negLe 0 (5 - 1)]) = True
    simp
  · -- chronology (the reason clause is the unit `[s ≥ 5]`)
    intro q hq hne
    exact absurd (List.mem_singleton.mp hq) hne
  · -- freshness: the removal entry has a different atom
    intro e he
    have heq : e = { literal := (posNe 0 0).norm, level := 0,
                     reason := some { clause := [posNe 0 0] } } := by
      simpa [sparseRemoval, BranchState.recordImplied, BranchState.init] using he
    intro h
    rw [heq] at h
    simp only [posNe, negLe, Literal.norm] at h
    exact absurd h (by decide)

/-- SPARSE EXAMPLE, WITNESS: the materialized bound has an exact
`findEntryOf` witness at the bound's own slot, at the current level. -/
example : ∃ e, findEntryOf sparseState.trail (negLe 0 (5 - 1)) = some e ∧
    e.literal = negLe 0 (5 - 1) ∧ e.literal.atom.slot = 0 ∧ e.level = 0 :=
  recordBound_lookup (bs := sparseRemoval) (s := 0) (lo := 5)
    (r := { clause := [negLe 0 (5 - 1)] })

/-- SPARSE EXAMPLE, ANALYZER SHAPE: scanning `s ≤ 0` (a literal strictly
below the materialized bound) upgrades to the bound's exact negation, and
the upgrade's lookup succeeds — the trail's lower-bound fold sees the
materialized entry. -/
example : ∃ e, findEntryOf sparseState.trail
      (orderUpgrade sparseState.trail (posLe 0 0)).negate = some e ∧
    e.literal.atom.slot = 0 ∧ e.level ≤ 0 := by
  have hvis : ∃ lo', trailLoOf sparseState.trail 0 = some lo' ∧ 5 ≤ lo' :=
    trailLoOf_append_bound (trail := sparseRemoval.trail) (s := 0) (lo := 5)
      (lvl := 0) (r := { clause := [negLe 0 (5 - 1)] })
  obtain ⟨lo', hlo', hle⟩ := hvis
  exact derivedBound_exact_falsifier (k := 0) hlo' (by omega)
    (fun e he => sparseState_reachable.wf.1 e he)

end LeanFzn.Solver.Propagation

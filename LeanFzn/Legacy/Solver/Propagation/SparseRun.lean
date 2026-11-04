/-
File: LeanFzn/Solver/Propagation/SparseRun.lean

Purpose (M2 stage 2 = S0 migration stage M3: the sparse closure/run layer, UNWIRED).

  This module is the ACTIVE-BRANCH STEP / CLOSURE / RUN layer over the sparse
  frame of `SparseFrame.lean` (S0-decision-design.md §3), written against the
  frozen API and proving the M3 obligations at the frame level:

  * the DEDUCTION STEP `Frame.deduce` (apply a justified literal at its own
    absolute slot; `Frame.filterFrame`-based, `none` = local exclusion) with
    coverage (`Frame.deduce_covers_iff`, the `covers_filterFrame_iff` twin),
    refinement, order preservation and progress laws;
  * the DECISION STEP `Frame.splitData` (`selectSlot`-style, returning the
    decision literal `valueLiteral k v`, the ORIGINAL slot and the tail) with
    `covers_split_at` (the S0 §3.5 arbitrary-slot exhaustiveness law, reused
    from `SparseFrame.covers_pin_or_retire`), child disjointness, strict
    progress (mass/cost/frontierWeight) and the level/`slotAtLevel`/
    `decisionEntry` ledger;
  * the RUN STEP classification `Step`/`step` (one active-branch step: apply a
    pending deduction literal, otherwise decide, otherwise stop) and the
    frontier-level coverage law `frontierCovers_split_at` over a pending stack;
  * the RESTORATION STUBS on sparse checkpoints (`Checkpoint.restore`,
    `Checkpoint.restore_level`/`_descends`/`_children`/`resume_descends`) and
    the transported checkpoint statements for the CURRENT runtime
    `DecisionCheckpoint.Identifies` (`checkpoint_identifies_pin_transport`,
    `checkpoint_identifies_retire_transport`, reusing
    `SparseFrame.Checkpoint.identifies_toDecisionCheckpoint`).

  Everything is a pure function of sparse frames and literals: METADATA-FREE
  (no activity/phase state; S2's `splitAct`/`Meta` can replace `Frame.splitData`
  behind these laws without changing them). Nothing is wired: the shared
  scheduled cone still uses the positional `BranchFrame`.

  TRANSPORT BRIDGES (exact names; the later stages switch with these alone):
  * coverage: `SparseFrame.Frame.covers_iff_FrameCovers` (frame-level, imported)
    and `frontierCovers_toPrefixFrame` (frontier-level, this module), against the
    current `FrameCovers`/`FrontierCovers`;
  * mass/cost: `mass_toPrefixFrame` (`Frame.mass`),
    `branchCost_toPrefixFrame`/`frontierCost_toPrefixFrame` and
    `frameWeight`/`frontierWeight_eq_sum_frameWeight` against the current
    `branchCost`/`frontierCost`;
  * checkpoints: `SparseFrame.Checkpoint.identifies_toDecisionCheckpoint`
    (imported) and the two `checkpoint_identifies_*_transport` wrappers against
    `DecisionCheckpoint.Identifies`;
  * the step layer's sparse filter is definitionally the slot-direct M2
    `Frame.filterFrame` (`SparseFrame.Frame.covers_filterFrame_iff`); its success
    transports to the current positional `filterFrame` by `narrow_toPrefixFrame`
    (this module; the converse differs exactly on the empty filtered domain),
    and the semantic bridge is `SparseFrame.filterSlots_covers_iff_filterFrame`.

Obligation ledger (S0 `S0-decision-design.md` §5 migration map).

  Covered by this stage (M3, closure/run semantics at absolute slots):
  * deduction application at the literal's slot with coverage/refinement/
    exclusion laws and productive-step progress;
  * exhaustive arbitrary-slot split at the selected slot, with disjointness,
    progress and the decision-literal/level vocabulary;
  * run-step classification and frontier coverage replacement laws;
  * frame-level restoration consistency and the checkpoint transport wrappers;
  * the M3 transport bridges listed above.

  Remaining (later stages; this module is the interface):
  * M2 (D1-gated shared edit): switch the scheduled cone's `BranchFrame` to the
    sparse type (Frontier/FrameFilter/chronological rename; statement shapes of
    `FrameCovers`/`FrameDescendsFrom`/`Identifies` unchanged);
  * M4 (restoration): the sparse `canonicalPins`/`slotFalsifiers`/`canonicalTrail`/
    `resumePending` trail construction and `resumePending_level = f.level`; the
    trail-prefix law transported (`Checkpoint.identifies_toDecisionCheckpoint`)
    for the RESUME state, plus `ResumeCoherent` at `f.level`. Restated as
    obligations at §4 below: only the frame-level half is proved here;
  * M5 (proof layer): `SchedulerRank` adoption `(frontierWeight, Frame.mass,
    Frame.level)` over the current `frontierCost`-based rank;
  * M6 (S1 wiring + measurement): dispatcher wiring of `selectSlot`/the step
    layer and the runtime A/B;
  * M7 (public/optimization): re-diff of the byte-identical public statements;
    none expected (`toStore` untouched; the witness is read at the ORIGINAL
    slot indices).

  Exact next-stage interface: use `Frame.deduce`/`Frame.splitData`/`step` for
  the run semantics, `frontierCovers_split_at` for split coverage,
  `frontierWeight_replace_lt`/`Frame.deduce_frontierWeight_lt` for progress,
  `Checkpoint.restore` + `checkpoint_identifies_*_transport` for restoration,
  and the §5 bridges for the positional vocabulary.

DAG: SparseFrame (+ ExplainedPropagation for `valueLiteral`, transitively
available) -> SparseRun
     (leaf module; nothing scheduled imports it yet).  No cycle: no module in
     the cone imports SparseRun; `SparseFrame` imports `DecisionProto`,
     `FrameFilter`, `BackjumpFrontier`, and `ExplainedPropagation` imports
     neither.

No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`, no proof escapes. Not wired.
-/
import LeanFzn.Legacy.Solver.Propagation.SparseFrame
import LeanFzn.Legacy.Solver.Propagation.SelectPolicy
import LeanFzn.Legacy.Solver.Propagation.ExplainedPropagation

open LeanFzn.Semantics LeanFzn.Solver.Core

namespace LeanFzn.Solver.Propagation.SparseRun
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.SparseFrame

/-! ## §1 The deduction step (closure layer): apply a literal at its own slot -/

/-- The outcome of applying one deduction literal to an active sparse frame at
the literal's own slot: `narrowed` = the filter kept a nonempty domain (it is a
no-op for an out-of-range slot), `excluded` = the target domain emptied, so the
branch is locally dead (`Frame.filterFrame` returned `none`). -/
inductive DeductionResult where
  /-- the literal's slot was filtered to a nonempty domain -/
  | narrowed (g : Frame)
  /-- the literal's slot emptied: local exclusion of the branch -/
  | excluded

/-- THE DEDUCTION STEP: apply a justified literal at its own absolute slot.
Pure on the frame — no trail, level or heuristic metadata is read. `none` from
`Frame.filterFrame` is exactly the local-exclusion outcome. -/
def Frame.deduce (l : Literal) (f : Frame) : DeductionResult :=
  match Frame.filterFrame l f with
  | some g => .narrowed g
  | none => .excluded

/-- Characterization of the narrowed outcome. -/
theorem Frame.deduce_narrowed_iff {l : Literal} {f g : Frame} :
    Frame.deduce l f = .narrowed g ↔ Frame.filterFrame l f = some g := by
  unfold Frame.deduce
  cases h : Frame.filterFrame l f <;> simp_all

/-- Characterization of the excluded outcome. -/
theorem Frame.deduce_excluded_iff {l : Literal} {f : Frame} :
    Frame.deduce l f = .excluded ↔ Frame.filterFrame l f = none := by
  unfold Frame.deduce
  cases h : Frame.filterFrame l f <;> simp_all

/-- DEDUCTION COVERAGE (the `covers_filterFrame_iff` twin): a narrowed frame
covers exactly the parent's assignments that satisfy the applied literal at the
literal's absolute slot. -/
theorem Frame.deduce_covers_iff {l : Literal} {f g : Frame}
    (h : Frame.deduce l f = .narrowed g) (hsl : l.atom.slot < f.doms.length)
    (a : Assignment) :
    g.covers a ↔ f.covers a ∧ l.eval a = some true :=
  Frame.covers_filterFrame_iff ((Frame.deduce_narrowed_iff).mp h) hsl a

/-- A narrowed frame never covers anything the parent did not: no leaf is
invented by a deduction (holds without the in-range hypothesis). -/
theorem Frame.deduce_refines {l : Literal} {f g : Frame}
    (h : Frame.deduce l f = .narrowed g) {a : Assignment} (hc : g.covers a) :
    f.covers a := by
  have hf : Frame.filterFrame l f = some g := (Frame.deduce_narrowed_iff).mp h
  unfold Frame.filterFrame at hf
  split at hf
  · rename_i hd
    injection hf with hge
    subst hge
    exact hc
  · rename_i d hd
    split at hf
    · cases hf
    · rename_i d' hfil
      injection hf with hge
      subst hge
      exact SparseFrame.mem_allAssigns_of_mem_set
        (fun v hv => by
          have hvd : v ∈ d := (Dom.mem_filterLitKeep_iff.mp hv).1
          rw [List.getD_eq_getElem?_getD, hd]
          exact hvd) hc

/-- LOCAL EXCLUSION: a rejected deduction literal forbids every covered
assignment of the branch. -/
theorem Frame.deduce_excluded_no_satisfier {l : Literal} {f : Frame}
    (h : Frame.deduce l f = .excluded) :
    ∀ a, f.covers a → l.eval a ≠ some true :=
  Frame.covers_filterFrame_none ((Frame.deduce_excluded_iff).mp h)

/-- Exact rejection criterion of the deduction step. -/
theorem Frame.deduce_excluded_iff_exists (l : Literal) (f : Frame) :
    Frame.deduce l f = .excluded ↔
      ∃ d : Domain, f.doms[l.atom.slot]? = some d ∧
        Dom.enum (d.filter l.valueHolds) = [] :=
  (Frame.deduce_excluded_iff).trans (SparseFrame.Frame.filterFrame_eq_none_iff l f)

/-- A deduction never decides: the decision order is untouched. -/
theorem Frame.deduce_narrowed_order {l : Literal} {f g : Frame}
    (h : Frame.deduce l f = .narrowed g) : g.order = f.order :=
  Frame.filterFrame_order ((Frame.deduce_narrowed_iff).mp h)

/-! ### Progress of the deduction step -/

/-- Monotone variant of `DecisionProto.sumMass_set_lt`: a slot-wise
length-nonincreasing replacement never increases the sum measure. -/
theorem sumMass_set_le {ds : List Domain} {k : Nat} {d x : Domain}
    (h : ds[k]? = some d) (hle : x.length ≤ d.length) :
    DecisionProto.sumMass (ds.set k x) ≤ DecisionProto.sumMass ds := by
  induction ds generalizing k with
  | nil => simp at h
  | cons d₀ rest ih =>
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h
          subst h
          simp only [List.set_cons_zero, DecisionProto.sumMass, List.map_cons,
            List.sum_cons]
          omega
      | succ k =>
          simp only [List.getElem?_cons_succ] at h
          have hih : (List.map (fun d => d.length) (rest.set k x)).sum ≤
              (List.map (fun d => d.length) rest).sum := ih h
          simp only [List.set_cons_succ, DecisionProto.sumMass, List.map_cons,
            List.sum_cons]
          omega

/-- A strict sum-measure decrease at a slot forces the replacement domain to be
strictly shorter: the strictness is a slot-local fact. -/
theorem sumMass_set_len_lt {ds : List Domain} {k : Nat} {d x : Domain}
    (h : ds[k]? = some d)
    (hsum : DecisionProto.sumMass (ds.set k x) < DecisionProto.sumMass ds) :
    x.length < d.length := by
  induction ds generalizing k with
  | nil => simp at h
  | cons d₀ rest ih =>
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h
          subst h
          simp only [List.set_cons_zero, DecisionProto.sumMass, List.map_cons,
            List.sum_cons] at hsum
          omega
      | succ k =>
          simp only [List.getElem?_cons_succ] at h
          have hsum' : DecisionProto.sumMass (rest.set k x) <
              DecisionProto.sumMass rest := by
            simp only [DecisionProto.sumMass, List.set_cons_succ, List.map_cons,
              List.sum_cons] at hsum
            simp only [DecisionProto.sumMass]
            omega
          exact ih h hsum'

/-- PROGRESS (deduction arm, sum measure): narrowing never increases the mass
(it is a no-op exactly when the filter removed nothing). -/
theorem Frame.deduce_narrowed_mass_le {l : Literal} {f g : Frame}
    (h : Frame.deduce l f = .narrowed g) : g.mass ≤ f.mass := by
  have hf : Frame.filterFrame l f = some g := (Frame.deduce_narrowed_iff).mp h
  unfold Frame.filterFrame at hf
  split at hf
  · injection hf with hge
    subst hge
    exact Nat.le_refl _
  · rename_i d hd
    split at hf
    · cases hf
    · rename_i d' hfil
      injection hf with hge
      subst hge
      exact sumMass_set_le hd (Dom.card_filterLitKeep_le l d)

/-- PROGRESS (deduction arm, decide-arm cost): a PRODUCTIVE narrowing (strict
mass decrease) strictly decreases `branchCost`, under the route shape (every
domain nonempty; an empty domain is dead and never stepped). -/
theorem Frame.deduce_narrowed_cost_lt {l : Literal} {f g : Frame}
    (h : Frame.deduce l f = .narrowed g) (hprod : g.mass < f.mass)
    (hall : ∀ e ∈ f.doms, e.enum ≠ []) : g.cost < f.cost := by
  have hf : Frame.filterFrame l f = some g := (Frame.deduce_narrowed_iff).mp h
  unfold Frame.filterFrame at hf
  split at hf
  · injection hf with hge
    subst hge
    exact absurd hprod (Nat.lt_irrefl _)
  · rename_i d hd
    split at hf
    · cases hf
    · rename_i d' hfil
      injection hf with hge
      subst hge
      exact DecisionProto.branchCost_set_lt hd (sumMass_set_len_lt hd hprod) hall

/-- PROGRESS (consume/replace arm of the frontier): replacing a pending frame by
a strictly cost-lower frame strictly decreases the frontier weight. -/
theorem frontierWeight_replace_lt {pending : List Frame} {f g : Frame}
    (h : g.cost < f.cost) :
    frontierWeight (g :: pending) < frontierWeight (f :: pending) := by
  have hpow : 3 ^ g.cost < 3 ^ f.cost :=
    Nat.pow_lt_pow_right (by decide : 1 < 3) h
  simp only [LeanFzn.Solver.Propagation.frontierWeight,
    LeanFzn.Solver.Propagation.frameWeight, List.map_cons, List.sum_cons]
  exact Nat.add_lt_add_right hpow _

/-- PROGRESS (deduction arm, frontier weight): a productive narrowing strictly
decreases the frontier weight when it replaces the active frame. -/
theorem Frame.deduce_frontierWeight_lt {pending : List Frame} {l : Literal}
    {f g : Frame} (h : Frame.deduce l f = .narrowed g) (hprod : g.mass < f.mass)
    (hall : ∀ e ∈ f.doms, e.enum ≠ []) :
    frontierWeight (g :: pending) < frontierWeight (f :: pending) :=
  frontierWeight_replace_lt (Frame.deduce_narrowed_cost_lt h hprod hall)

/-! ## §2 The decision step (S0 §3.3 `splitData`): select the S1 slot, split -/

/-- THE POLICY SPLIT: select a live slot by the policy `SelectPolicy.selectSlotP σ`
(the S1 rule for the empty vector, the S2 activity rule for a covering one) and
decompose its domain into head value and tail. The `DecisionProto.Frame.split`
shape with the selector made a parameter. -/
def Frame.splitP (σ : List Nat) (f : Frame) : Option (Nat × Value × Domain) :=
  match SelectPolicy.selectSlotP σ f.doms with
  | none => none
  | some k =>
      match f.doms[k]? with
      | some d =>
          match Dom.enum d with
          | [] => none
          | v :: vs => some (k, v, Dom.ofList vs)
      | none => none

/-- The empty policy vector is the S1 split. -/
theorem Frame.splitP_nil (f : Frame) : Frame.splitP [] f = DecisionProto.Frame.split f := by
  unfold Frame.splitP DecisionProto.Frame.split
  rw [SelectPolicy.selectSlotP_nil]
  rfl

/-- The policy split decomposes the selected slot's domain and names the
selected slot. -/
theorem Frame.splitP_spec {σ : List Nat} {f : Frame} {k : Nat} {v : Value} {vs : Domain}
    (h : Frame.splitP σ f = some (k, v, vs)) :
    SelectPolicy.selectSlotP σ f.doms = some k ∧
      f.doms[k]?.map Dom.enum = some (v :: vs.enum) := by
  unfold Frame.splitP at h
  cases hs : SelectPolicy.selectSlotP σ f.doms with
  | none => simp [hs] at h
  | some j =>
      simp only [hs] at h
      cases hd : f.doms[j]? with
      | none => simp [hd] at h
      | some d =>
          cases hd' : Dom.enum d with
          | nil => simp [hd, hd'] at h
          | cons w ws =>
              simp only [hd, hd', Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              refine ⟨rfl, ?_⟩
              simp [hd, hd']

/-- The policy split's sibling is nonempty (only live slots split). -/
theorem Frame.splitP_live {σ : List Nat} {f : Frame} {k : Nat} {v : Value} {vs : Domain}
    (h : Frame.splitP σ f = some (k, v, vs)) : vs.enum ≠ [] := by
  obtain ⟨hs, hspec⟩ := Frame.splitP_spec h
  obtain ⟨v', vs', hv', hne'⟩ := SelectPolicy.selectSlotP_live hs
  rw [hspec] at hv'
  have hvs : vs.enum = vs'.enum := (List.cons.inj (Option.some.inj hv')).2
  exact fun hnil => hne' (hvs ▸ hnil)

/-- THE DECISION STEP: select the live slot by the policy `σ`
(`SelectPolicy.selectSlotP`, via `Frame.splitP`; `σ = []` is the S1 rule
`selectSlot`) and decompose its domain into its head value `v` and tail `vs`;
the decision literal is `valueLiteral k v` at the ORIGINAL slot index `k`.
`none` when no live slot exists or the selected value has no decision literal
(sets/arrays, which the scheduler never splits). -/
def Frame.splitData (f : Frame) (σ : List Nat := []) :
    Option (Literal × Nat × Value × Domain) :=
  match Frame.splitP σ f with
  | none => none
  | some (k, v, vs) => (valueLiteral k v).map fun l => (l, k, v, vs)

/-- The split data comes from the underlying `Frame.splitP`: the selected slot,
value and sibling tail are exactly the split's. -/
theorem Frame.splitData_split {f : Frame} {σ : List Nat} {l : Literal} {k : Nat}
    {v : Value} {vs : Domain} (h : Frame.splitData f σ = some (l, k, v, vs)) :
    Frame.splitP σ f = some (k, v, vs) := by
  cases hs : Frame.splitP σ f with
  | none =>
      have h' : Frame.splitData f σ = none := by simp [Frame.splitData, hs]
      rw [h'] at h
      cases h
  | some p =>
      obtain ⟨k', v', vs'⟩ := p
      have h' : Frame.splitData f σ =
          Option.map (fun l => (l, k', v', vs')) (valueLiteral k' v') := by
        simp [Frame.splitData, hs]
      rw [h'] at h
      obtain ⟨l', hl', heq⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl, rfl, rfl⟩ := heq
      rfl

/-- THE DECISION STEP'S SPECIFICATION (S0 §3.3 `splitData_spec`): the selected
slot is decomposed into `v :: vs` and the decision literal is `valueLiteral k v`. -/
theorem Frame.splitData_spec {f : Frame} {σ : List Nat} {l : Literal} {k : Nat}
    {v : Value} {vs : Domain} (h : Frame.splitData f σ = some (l, k, v, vs)) :
    f.doms[k]?.map Dom.enum = some (v :: vs.enum) ∧ valueLiteral k v = some l := by
  cases hs : Frame.splitP σ f with
  | none =>
      have h' : Frame.splitData f σ = none := by simp [Frame.splitData, hs]
      rw [h'] at h
      cases h
  | some p =>
      obtain ⟨k', v', vs'⟩ := p
      have h' : Frame.splitData f σ =
          Option.map (fun l => (l, k', v', vs')) (valueLiteral k' v') := by
        simp [Frame.splitData, hs]
      rw [h'] at h
      obtain ⟨l', hl', heq⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
      exact ⟨(Frame.splitP_spec hs).2, hl'⟩

/-- DECISION LEGALITY (slot): the decision's slot is the policy-selected slot. -/
theorem Frame.splitData_slot {f : Frame} {σ : List Nat} {l : Literal} {k : Nat}
    {v : Value} {vs : Domain} (h : Frame.splitData f σ = some (l, k, v, vs)) :
    SelectPolicy.selectSlotP σ f.doms = some k :=
  (Frame.splitP_spec (Frame.splitData_split h)).1

/-- DECISION LEGALITY (liveness): the selected slot is live (non-singleton). -/
theorem Frame.splitData_live {f : Frame} {σ : List Nat} {l : Literal} {k : Nat}
    {v : Value} {vs : Domain} (h : Frame.splitData f σ = some (l, k, v, vs)) : f.Live k :=
  SelectPolicy.selectSlotP_live (Frame.splitData_slot h)

/-- The retired sibling is nonempty: only live slots split. -/
theorem Frame.splitData_sibling_ne_nil {f : Frame} {σ : List Nat} {l : Literal} {k : Nat}
    {v : Value} {vs : Domain} (h : Frame.splitData f σ = some (l, k, v, vs)) :
    vs.enum ≠ [] :=
  Frame.splitP_live (Frame.splitData_split h)

/-- THE ARBITRARY-SLOT SPLIT (`covers_split_at`, S0 §3.5): the parent's coverage
is exactly the union of the pinned child's and the retired sibling's coverage.
Reused from `SparseFrame.covers_pin_or_retire` (the S0 union law). -/
theorem covers_split_at {f : Frame} {k : Nat} {v : Value} {vs : Domain}
    (h : f.doms[k]?.map Dom.enum = some (v :: vs.enum)) (a : Assignment) :
    f.covers a ↔ (f.pin k v).covers a ∨ (f.retire k vs).covers a :=
  SparseFrame.covers_pin_or_retire h a

/-- EXCLUSIVITY OF THE SPLIT: when the retired tail does not contain the pinned
value, no covered assignment lands in BOTH children — with `covers_split_at`
this is "exactly one child" per covered leaf. (Domains may contain duplicate
values, in which case the union law still holds and the overlap is exactly the
duplicated value; the runtime never relies on exclusivity.) -/
theorem covers_split_at_exclusive {f : Frame} {k : Nat} {v : Value} {vs : Domain}
    (h : f.doms[k]?.map Dom.enum = some (v :: vs.enum)) (hno : v ∉ vs)
    {a : Assignment} :
    ¬ ((f.pin k v).covers a ∧ (f.retire k vs).covers a) := by
  rintro ⟨hc, hs⟩
  obtain ⟨d, hd, -⟩ := Option.map_eq_some_iff.mp h
  have hklt : k < f.doms.length := (List.getElem?_eq_some_iff.mp hd).1
  have hread : a[k]? = some v :=
    DecisionProto.covers_read hc (List.getElem?_set_self hklt)
  have hklt' : k < (f.retire k vs).doms.length := by
    rw [DecisionProto.Frame.retire_doms, List.length_set]
    exact hklt
  obtain ⟨w, hw, hreadw⟩ := SparseFrame.exists_read_of_covers hs hklt'
  have hwvs : w ∈ vs := by
    have hw' : w ∈ (f.doms.set k vs).getD k Dom.empty := hw
    rw [SparseFrame.getD_set_self hklt] at hw'
    exact hw'
  have hwv : w = v := by
    rw [hread] at hreadw
    exact (Option.some.inj hreadw).symm
  exact hno (hwv ▸ hwvs)

/-- COVERAGE AT THE SELECTED SPLIT: the S1 decision is exhaustive. -/
theorem Frame.splitData_covers {f : Frame} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain} {σ : List Nat} (h : Frame.splitData f σ = some (l, k, v, vs)) (a : Assignment) :
    f.covers a ↔ (f.pin k v).covers a ∨ (f.retire k vs).covers a :=
  covers_split_at (Frame.splitData_spec h).1 a

/-- The decision literal `valueLiteral s v` refers to the value's own slot. -/
theorem valueLiteral_slot {s : Nat} {v : Value} {l : Literal}
    (h : valueLiteral s v = some l) : l.atom.slot = s := by
  cases v with
  | bool b =>
      simp only [valueLiteral, Option.some.injEq] at h
      subst h
      rfl
  | int i =>
      simp only [valueLiteral, Option.some.injEq] at h
      subst h
      rfl
  | setOfInt xs => simp [valueLiteral] at h
  | array a => simp [valueLiteral] at h

/-- THE DECISION LITERAL HOLDS ON ITS CHILD: every assignment covered by the
pinned child satisfies the recorded decision literal at the ORIGINAL slot. -/
theorem Frame.splitData_child_literal {f : Frame} {l : Literal} {k : Nat}
    {v : Value} {vs : Domain} {σ : List Nat} (h : Frame.splitData f σ = some (l, k, v, vs))
    {a : Assignment} (ha : (f.pin k v).covers a) : l.eval a = some true := by
  obtain ⟨hget, hval⟩ := Frame.splitData_spec h
  obtain ⟨d, hd, -⟩ := Option.map_eq_some_iff.mp hget
  have hklt : k < f.doms.length := (List.getElem?_eq_some_iff.mp hd).1
  have hread : a[k]? = some v :=
    DecisionProto.covers_read ha (List.getElem?_set_self hklt)
  have hslot : l.atom.slot = k := valueLiteral_slot hval
  have hread' : a[l.atom.slot]? = some v := by rwa [hslot]
  exact (valueHolds_read hread').mp (valueLiteral_valueHolds_self hval)

/-! ### Progress of the decision step (both children strictly decrease) -/

/-- PROGRESS (decide arm, sum measure): both children strictly decrease the
mass (reuses `DecisionProto.mass_pin_lt`/`mass_retire_lt`). -/
theorem Frame.splitData_mass_lt {f : Frame} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain} {σ : List Nat} (h : Frame.splitData f σ = some (l, k, v, vs)) :
    (f.pin k v).mass < f.mass ∧ (f.retire k vs).mass < f.mass :=
  ⟨mass_pin_lt (Frame.splitData_spec h).1 (Frame.splitData_sibling_ne_nil h),
   mass_retire_lt (Frame.splitData_spec h).1⟩

/-- PROGRESS (decide arm, decide-arm cost): both children strictly decrease
`branchCost`, under the route shape (every domain nonempty). -/
theorem Frame.splitData_cost_lt {f : Frame} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain} {σ : List Nat} (h : Frame.splitData f σ = some (l, k, v, vs))
    (hall : ∀ e ∈ f.doms, e.enum ≠ []) :
    (f.pin k v).cost < f.cost ∧ (f.retire k vs).cost < f.cost :=
  ⟨cost_pin_lt (Frame.splitData_spec h).1 (Frame.splitData_sibling_ne_nil h) hall,
   cost_retire_lt (Frame.splitData_spec h).1 hall⟩

/-- PROGRESS (decide arm, frontier weight): the S1 decision strictly decreases
the frontier weight (reuses `DecisionProto.frontierWeight_split_lt`). -/
theorem Frame.splitData_frontierWeight_lt {pending : List Frame} {f : Frame}
    {l : Literal} {k : Nat} {v : Value} {vs : Domain}
    {σ : List Nat} (h : Frame.splitData f σ = some (l, k, v, vs)) (hall : ∀ e ∈ f.doms, e.enum ≠ []) :
    frontierWeight ((f.pin k v) :: (f.retire k vs) :: pending) <
      frontierWeight (f :: pending) :=
  frontierWeight_split_lt (Frame.splitData_cost_lt h hall).1
    (Frame.splitData_cost_lt h hall).2

/-! ### Decision level / checkpoint vocabulary -/

/-- LEVEL LEDGER at the selected split: the decision opens exactly level
`f.level + 1` at the decided slot `k` (`slotAtLevel` records it), the sibling
keeps the level, and `decisionEntry` records the decision literal's normalized
form at the new level with no reason (the trail entry `BranchState.decide`
appends). -/
theorem Frame.splitData_level_ledger {f : Frame} {l : Literal} {k : Nat}
    {v : Value} {vs : Domain} {σ : List Nat} (h : Frame.splitData f σ = some (l, k, v, vs)) :
    (f.pin k v).level = f.level + 1 ∧
      (f.pin k v).slotAtLevel (f.level + 1) = some k ∧
      (f.retire k vs).level = f.level ∧
      f.decisionEntry k v =
        some { literal := l.norm, level := f.level + 1, reason := none } :=
  ⟨Frame.level_pin f k v, Frame.slotAtLevel_pin f k v, Frame.level_retire f k vs,
    Frame.decisionEntry_matches_literal (Frame.splitData_spec h).2⟩

/-- DECISION FRESHNESS: in a well-formed frame the selected slot is not already
decided (a live slot is never in the decision order). -/
theorem Frame.splitData_fresh {f : Frame} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain} {σ : List Nat} (h : Frame.splitData f σ = some (l, k, v, vs)) (hwf : f.WF) :
    k ∉ f.order :=
  hwf.not_mem_order_of_live (Frame.splitData_live h)

/-- The pinned child preserves the frame invariant. -/
theorem Frame.splitData_child_WF {f : Frame} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain} {σ : List Nat} (h : Frame.splitData f σ = some (l, k, v, vs)) (hwf : f.WF) :
    (f.pin k v).WF :=
  hwf.pin_of_live (Frame.splitData_spec h).1 (Frame.splitData_live h)

/-- The retired sibling preserves the frame invariant. -/
theorem Frame.splitData_sibling_WF {f : Frame} {l : Literal} {k : Nat}
    {v : Value} {vs : Domain} {σ : List Nat} (h : Frame.splitData f σ = some (l, k, v, vs))
    (hwf : f.WF) : (f.retire k vs).WF :=
  hwf.retire (Frame.splitData_fresh h hwf)

/-! ## §3 The run step: deduction first, otherwise decide -/

/-- The active-branch step's outcome (metadata-free): `narrowed`/`excluded` from
a supplied deduction literal, `decided` from the S1 split, `exhausted` when no
live slot remains. -/
inductive Step where
  /-- a pending deduction literal narrowed the frame -/
  | narrowed (g : Frame)
  /-- a pending deduction literal emptied its slot: local exclusion -/
  | excluded
  /-- the decision step selected a live slot with a decision literal -/
  | decided (l : Literal) (k : Nat) (v : Value) (vs : Domain)
  /-- no live slot: the frame is exhausted -/
  | exhausted

/-- ONE ACTIVE-BRANCH STEP: apply the pending deduction literal when one is
supplied (otherwise the decide arm is not attempted), else decide by the S1
selector. Pure function of the frame and the literal; no metadata. -/
def step (ded : Option Literal) (f : Frame) : Step :=
  match ded with
  | some l =>
      match Frame.deduce l f with
      | .narrowed g => .narrowed g
      | .excluded => .excluded
  | none =>
      match Frame.splitData f with
      | some (l, k, v, vs) => .decided l k v vs
      | none => .exhausted

/-- Characterization: the deduction arm narrows exactly as `Frame.deduce`. -/
theorem step_some_narrowed {l : Literal} {f g : Frame} :
    step (some l) f = .narrowed g ↔ Frame.deduce l f = .narrowed g := by
  unfold step
  cases h : Frame.deduce l f <;> simp_all

/-- Characterization: the deduction arm excludes exactly as `Frame.deduce`. -/
theorem step_some_excluded {l : Literal} {f : Frame} :
    step (some l) f = .excluded ↔ Frame.deduce l f = .excluded := by
  unfold step
  cases h : Frame.deduce l f <;> simp_all

/-- Characterization: the decide arm returns exactly `Frame.splitData`. -/
theorem step_none_decided {f : Frame} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain} :
    step none f = .decided l k v vs ↔ Frame.splitData f = some (l, k, v, vs) := by
  unfold step
  simp only []
  cases h : Frame.splitData f with
  | none => simp
  | some d =>
      obtain ⟨l', k', v', vs'⟩ := d
      simp only []
      constructor <;> intro hh <;> cases hh <;> rfl

/-- Characterization: the decide arm is exhausted exactly when no split data
exists (no live slot, or an unsupported value shape). -/
theorem step_none_exhausted {f : Frame} :
    step none f = .exhausted ↔ Frame.splitData f = none := by
  unfold step
  cases h : Frame.splitData f <;> simp_all

/-! ### Run-step coverage -/

/-- RUN COVERAGE (deduction arm): the narrowed frame keeps exactly the parent's
assignments satisfying the applied literal. -/
theorem step_some_narrowed_covers {l : Literal} {f g : Frame}
    (h : step (some l) f = .narrowed g) (hsl : l.atom.slot < f.doms.length)
    (a : Assignment) :
    g.covers a ↔ f.covers a ∧ l.eval a = some true :=
  Frame.deduce_covers_iff ((step_some_narrowed (l := l) (f := f)).mp h) hsl a

/-- RUN LOCAL EXCLUSION: the excluded step forbids every covered assignment. -/
theorem step_some_excluded_no_satisfier {l : Literal} {f : Frame}
    (h : step (some l) f = .excluded) :
    ∀ a, f.covers a → l.eval a ≠ some true :=
  Frame.deduce_excluded_no_satisfier ((step_some_excluded (l := l) (f := f)).mp h)

/-- RUN COVERAGE (decision arm): the decision replaces the parent's coverage by
exactly the two children's (exhaustiveness at the selected slot). -/
theorem step_none_decided_covers {f : Frame} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain} (h : step none f = .decided l k v vs) (a : Assignment) :
    f.covers a ↔ (f.pin k v).covers a ∨ (f.retire k vs).covers a :=
  Frame.splitData_covers ((step_none_decided (f := f)).mp h) a

/-! ### Frontier coverage over a sparse pending stack -/

/-- Frontier coverage: some frame of the pending stack covers the assignment
(the frontier-level form of `Frame.covers`; same shape as the current positional
`FrontierCovers` and as `RestartProto.FrontierCovers`, bridged in §5). -/
def frontierCovers (pending : List Frame) (a : Assignment) : Prop :=
  ∃ f ∈ pending, f.covers a

/-- Unfolding of frontier coverage at the active frame. -/
theorem frontierCovers_cons_iff {f : Frame} {pending : List Frame} (a : Assignment) :
    frontierCovers (f :: pending) a ↔ f.covers a ∨ frontierCovers pending a := by
  constructor
  · rintro ⟨g, hg, hc⟩
    rcases List.mem_cons.mp hg with rfl | hg
    · exact Or.inl hc
    · exact Or.inr ⟨g, hg, hc⟩
  · rintro (hc | ⟨g, hg, hc⟩)
    · exact ⟨f, List.mem_cons_self .., hc⟩
    · exact ⟨g, List.mem_cons_of_mem _ hg, hc⟩

/-- FRONTIER SPLIT COVERAGE (run level): replacing the active frame by its two
split children preserves the frontier's covered set exactly — every covered leaf
of the parent is covered by a child and no leaf is lost or invented. -/
theorem frontierCovers_split_at {pending : List Frame} {f : Frame} {k : Nat}
    {v : Value} {vs : Domain}
    (h : f.doms[k]?.map Dom.enum = some (v :: vs.enum)) (a : Assignment) :
    frontierCovers ((f.pin k v) :: (f.retire k vs) :: pending) a ↔
      frontierCovers (f :: pending) a := by
  constructor
  · rintro ⟨g, hg, hc⟩
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨f, List.mem_cons_self .., (covers_split_at h a).mpr (Or.inl hc)⟩
    · rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨f, List.mem_cons_self .., (covers_split_at h a).mpr (Or.inr hc)⟩
      · exact ⟨g, List.mem_cons_of_mem _ hg, hc⟩
  · rintro ⟨g, hg, hc⟩
    rcases List.mem_cons.mp hg with hgf | hg
    · rw [hgf] at hc
      rcases (covers_split_at h a).mp hc with h' | h'
      · exact ⟨f.pin k v, List.mem_cons_self .., h'⟩
      · exact ⟨f.retire k vs, List.mem_cons_of_mem _ (List.mem_cons_self ..), h'⟩
    · exact ⟨g, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg), hc⟩

/-- RUN COVERAGE AT THE STEP (decision arm): the step's split preserves the
frontier coverage exactly. -/
theorem step_decided_frontierCovers {f : Frame} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain} {pending : List Frame} (h : step none f = .decided l k v vs)
    (a : Assignment) :
    frontierCovers ((f.pin k v) :: (f.retire k vs) :: pending) a ↔
      frontierCovers (f :: pending) a :=
  frontierCovers_split_at (Frame.splitData_spec
    ((step_none_decided (f := f)).mp h)).1 a

/-! ### Run-step progress -/

/-- RUN PROGRESS (decision arm): the step's split strictly decreases the
frontier weight. -/
theorem step_decided_frontierWeight_lt {f : Frame} {l : Literal} {k : Nat}
    {v : Value} {vs : Domain} {pending : List Frame}
    (h : step none f = .decided l k v vs) (hall : ∀ e ∈ f.doms, e.enum ≠ []) :
    frontierWeight ((f.pin k v) :: (f.retire k vs) :: pending) <
      frontierWeight (f :: pending) :=
  Frame.splitData_frontierWeight_lt ((step_none_decided (f := f)).mp h) hall

/-- RUN PROGRESS (deduction arm): a productive narrowed step strictly decreases
the frontier weight. -/
theorem step_narrowed_frontierWeight_lt {l : Literal} {f g : Frame}
    {pending : List Frame} (h : step (some l) f = .narrowed g)
    (hprod : g.mass < f.mass) (hall : ∀ e ∈ f.doms, e.enum ≠ []) :
    frontierWeight (g :: pending) < frontierWeight (f :: pending) :=
  Frame.deduce_frontierWeight_lt ((step_some_narrowed (l := l) (f := f)).mp h)
    hprod hall

/-! ## §4 Restoration stubs and checkpoint transport

The sparse checkpoint layer is `DecisionProto.Checkpoint` (level, box, order)
with `Checkpoint.Identifies` and `Checkpoint.identifies_self/pin/retire`; the
transport to the CURRENT runtime `DecisionCheckpoint.Identifies` is
`SparseFrame.Checkpoint.identifies_toDecisionCheckpoint`. This section proves
what holds at the FRAME level (enough to resume a sibling without losing
coverage) and marks the trail-level residue as the M4 obligation.

M4 obligations (NOT proved here; the exact residue):
* sparse `canonicalPins`/`slotFalsifiers`/`canonicalTrail`/`resumePending`
  (`BackjumpFrontier.lean` currently defines them positionally, with
  `j := f.2.length + i` and `level := slot + 1`);
* `resumePending_level = f.level` (was `= f.2.length`) and the trail-shape
  laws `resumePending_frame`/`_learned`/`_trail` at the sparse frame;
* the transported `Checkpoint.identifies_toDecisionCheckpoint` for the RESUME
  state itself: the reconstructed trail must satisfy the trail-prefix law
  (supplied as an explicit hypothesis in the transports below);
* `ResumeCoherent` at `f.level` and the level-to-slot ledger in
  `checkpointAt`/the backjump target arithmetic. -/

/-- RESTORATION STUB: the sparse frame a checkpoint restores — its recorded box
and decision order. The M4 restoration layer reconstructs the trail on top of
this frame; the frame-level consistency laws below are what is available before
M4. -/
def Checkpoint.restore (cp : DecisionProto.Checkpoint) : Frame :=
  { doms := cp.doms, order := cp.order }

/-- The restored frame's level is the checkpoint's own level whenever the
checkpoint identifies a frame: the recorded order is the frame's order
truncated at that level (`Identifies`' third conjunct). -/
theorem Checkpoint.restore_level {cp : DecisionProto.Checkpoint} {f : Frame}
    (h : cp.Identifies f) : (Checkpoint.restore cp).level = cp.level := by
  obtain ⟨hlev, -, hord⟩ := h
  change cp.order.length = cp.level
  rw [hord, List.length_take, Nat.min_eq_left (show cp.level ≤ f.order.length from hlev)]

/-- RESTORATION COVERAGE (frame level): everything the identified frame covers
is covered by the restored checkpoint region. -/
theorem Checkpoint.restore_descends {cp : DecisionProto.Checkpoint} {f : Frame}
    (h : cp.Identifies f) : Frame.DescendsFrom f (Checkpoint.restore cp) :=
  fun a ha => h.2.1 a ha

/-- RESTORATION CONSISTENCY (children): after a decision from an identified
frame, BOTH children still descend to the restored checkpoint region — resuming
either branch never leaves the checkpoint's covered area (the trail half of the
resume is M4). -/
theorem Checkpoint.restore_children {cp : DecisionProto.Checkpoint} {f : Frame}
    (h : cp.Identifies f) {k : Nat} {v : Value} {vs : Domain}
    (hk : f.doms[k]?.map Dom.enum = some (v :: vs.enum)) :
    Frame.DescendsFrom (f.pin k v) (Checkpoint.restore cp) ∧
      Frame.DescendsFrom (f.retire k vs) (Checkpoint.restore cp) :=
  ⟨fun a ha => h.2.1 a ((covers_split_at hk a).mpr (Or.inl ha)),
   fun a ha => h.2.1 a ((covers_split_at hk a).mpr (Or.inr ha))⟩

/-- RESUME WITHOUT LOSS (frame level): resuming any sibling that descends from
an identified frame never leaves the checkpoint region — composition of
descent. This is the exact statement available before M4's trail
reconstruction. -/
theorem Checkpoint.resume_descends {cp : DecisionProto.Checkpoint} {f sib : Frame}
    (h : cp.Identifies f) (hdesc : Frame.DescendsFrom sib f) :
    Frame.DescendsFrom sib (Checkpoint.restore cp) :=
  fun a ha => h.2.1 a (hdesc a ha)

/-- CHECKPOINT TRANSPORT (decision step, pinned child): the checkpoint that
identifies the parent also identifies the transported pinned-child branch state
(empty-prefix positional frame), under the trailing-trail law that M4 must
supply — this is `SparseFrame.Checkpoint.identifies_toDecisionCheckpoint`
applied through `Checkpoint.identifies_pin`. -/
theorem checkpoint_identifies_pin_transport {cp : DecisionProto.Checkpoint}
    {f : Frame} (h : cp.Identifies f) {k : Nat} {v : Value} {vs : Domain}
    (hk : f.doms[k]?.map Dom.enum = some (v :: vs.enum)) {leaf : Assignment → Bool}
    {bs : BranchState leaf}
    (hframe : bs.frame = ⟨(f.pin k v).doms, (f.pin k v).order⟩)
    {trail : List TrailEntry}
    (htrail : ∃ mid : List TrailEntry,
      bs.trail = trail ++ mid ∧ ∀ e ∈ mid, cp.level ≤ e.level) :
    (SparseFrame.toDecisionCheckpoint (leaf := leaf) cp trail).Identifies bs cp.level :=
  SparseFrame.Checkpoint.identifies_toDecisionCheckpoint
    (DecisionProto.Checkpoint.identifies_pin h hk) hframe htrail

/-- CHECKPOINT TRANSPORT (decision step, retired sibling): the checkpoint that
identifies the parent also identifies the transported sibling branch state —
the "resume the sibling" direction of restoration, frame-level. -/
theorem checkpoint_identifies_retire_transport {cp : DecisionProto.Checkpoint}
    {f : Frame} (h : cp.Identifies f) {k : Nat} {v : Value} {vs : Domain}
    (hk : f.doms[k]?.map Dom.enum = some (v :: vs.enum)) {leaf : Assignment → Bool}
    {bs : BranchState leaf}
    (hframe : bs.frame = ⟨(f.retire k vs).doms, (f.retire k vs).order⟩)
    {trail : List TrailEntry}
    (htrail : ∃ mid : List TrailEntry,
      bs.trail = trail ++ mid ∧ ∀ e ∈ mid, cp.level ≤ e.level) :
    (SparseFrame.toDecisionCheckpoint (leaf := leaf) cp trail).Identifies bs cp.level :=
  SparseFrame.Checkpoint.identifies_toDecisionCheckpoint
    (DecisionProto.Checkpoint.identifies_retire h hk) hframe htrail

/-! ## §5 Transport bridges to the current runtime vocabulary

Bridges proved in this module:
* `mass_toPrefixFrame` — sparse `Frame.mass` is the current `Frame.mass` of the
  empty-prefix transport;
* `branchCost_toPrefixFrame` / `frontierCost_toPrefixFrame` — the current
  positional cost vocabulary on the transported frontier;
* `frameWeight_eq_sum_frameWeight` — the S0 §3.5 per-frame weight
  (`3 ^ cost`) and the frontier sum;
* `frontierCovers_toPrefixFrame` — sparse frontier coverage is the current
  positional `FrontierCovers` of the transported frontier;
* `narrow_toPrefixFrame` — a successful sparse deduction step is a successful
  current positional `filterFrame` on the empty prefix.

Bridges imported (already proved in the stage-1 module, stated here for the
later switch):
* `SparseFrame.Frame.covers_iff_FrameCovers` (frame coverage);
* `SparseFrame.covers_split_iff_sparse_pin_or_retire` (the current positional
  `covers_split` is the sparse split at slot 0 of the empty-order frame);
* `SparseFrame.filterSlots_covers_iff_filterFrame` (deduction coverage);
* `SparseFrame.Checkpoint.identifies_toDecisionCheckpoint` (checkpoint; wrapped
  by `checkpoint_identifies_pin_transport`/`_retire_transport` in §4). -/

/-- Bridge (`Frame.mass`): the sparse mass is the current positional
`Frame.mass` of the empty-prefix transport. -/
theorem mass_toPrefixFrame (f : Frame) :
    PrefixFrame.mass (toPrefixFrame f) = f.mass := rfl

/-- Bridge (`branchCost`): the current positional cost of the transported frame
is the sparse decide-arm cost. -/
theorem branchCost_toPrefixFrame (f : Frame) :
    branchCost (toPrefixFrame f).1 = f.cost := rfl

/-- Bridge (`frontierCost`): the current positional frontier cost of the
transported frontier is the unweighted sum of `Frame.cost` over the sparse
frontier (the measure `frontierWeight` pole-vaults with `3 ^ cost`). -/
theorem frontierCost_toPrefixFrame (pending : List Frame) :
    frontierCost (pending.map toPrefixFrame) = (pending.map fun f => f.cost).sum := by
  induction pending with
  | nil => rfl
  | cons f rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [show frontierCost (toPrefixFrame f :: rest.map toPrefixFrame) =
          branchCost f.doms + frontierCost (rest.map toPrefixFrame) from rfl, ih]
      rfl

/-- The per-frame frontier weight (S0 §3.5's `frameWeight`): `3 ^ cost`. -/
def frameWeight (f : Frame) : Nat := 3 ^ f.cost

/-- Bridge: `frontierWeight` is the sum of the per-frame weights. -/
theorem frontierWeight_eq_sum_frameWeight (pending : List Frame) :
    frontierWeight pending = (pending.map frameWeight).sum := rfl

/-- Bridge (frontier coverage): the sparse frontier covers exactly the current
positional `FrontierCovers` of the transported frontier. -/
theorem frontierCovers_toPrefixFrame (pending : List Frame) (a : Assignment) :
    frontierCovers pending a ↔
      PrefixFrontierCovers (pending.map toPrefixFrame) a := by
  constructor
  · rintro ⟨f, hf, hc⟩
    exact ⟨toPrefixFrame f, List.mem_map_of_mem hf,
      (SparseFrame.covers_toPrefixFrame_iff f a).mp hc⟩
  · rintro ⟨g, hg, hc⟩
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
    exact ⟨f, hf, (SparseFrame.covers_toPrefixFrame_iff f a).mpr hc⟩

/-- Bridge (deduction step): a successful sparse `Frame.filterFrame` is a
successful current positional `filterFrame` on the empty-prefix transport. The
converse differs exactly on the empty filtered domain: the sparse step reports
local exclusion (`none`), the positional filter keeps the empty domain. -/
theorem narrow_toPrefixFrame {l : Literal} {f g : Frame}
    (h : Frame.filterFrame l f = some g) :
    prefixFilterFrame l (toPrefixFrame f) = some (toPrefixFrame g) := by
  unfold Frame.filterFrame at h
  split at h
  · rename_i hd
    rw [List.getElem?_eq_none_iff] at hd
    injection h with hge
    subst hge
    show some (filterSlots l 0 f.doms, []) = some ((f.doms, []) : PrefixFrame)
    have hfix : SparseFrame.filterSlot l f.doms = f.doms := by
      unfold SparseFrame.filterSlot
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr hd]
      exact List.set_eq_of_length_le hd
    rw [filterSlots_zero_eq_filterSlot, hfix]
  · rename_i d hd
    split at h
    · cases h
    · injection h with hge
      subst hge
      show some (filterSlots l 0 f.doms, []) =
        some ((f.doms.set l.atom.slot (Dom.filterLitKeep l d), []) : PrefixFrame)
      rw [filterSlots_zero_eq_filterSlot]
      unfold SparseFrame.filterSlot
      rw [List.getD_eq_getElem?_getD, hd]
      rfl

/-! ## §6 Tiny computed instance (the layer computes) -/

/-- The tiny two-slot box of the S0/S1 prototype (cards 3 and 2): the S1 split
takes the LATER, smaller slot `1`. -/
def tinyRun : Frame := { doms := DecisionProto.tinySmallLast, order := [] }

/-- The computed split data: slot `1`, value `true`, sibling `[false]`, decision
literal `posBool 1 true`. -/
theorem tinyRun_splitData :
    Frame.splitData tinyRun =
      some (posBool 1 true, 1, Value.bool true, Dom.ofList [Value.bool false]) := rfl

/-- The computed run step (decide arm). -/
theorem tinyRun_step :
    step none tinyRun =
      .decided (posBool 1 true) 1 (Value.bool true) (Dom.ofList [Value.bool false]) := rfl

/-- The computed decision literal holds on the concrete child. -/
theorem tinyRun_child_literal {a : Assignment}
    (ha : (tinyRun.pin 1 (Value.bool true)).covers a) :
    (posBool 1 true).eval a = some true :=
  Frame.splitData_child_literal tinyRun_splitData ha

/-- Concrete read-back: a covered assignment of the tiny child reads `true` at
the ORIGINAL slot `1`. -/
theorem tinyRun_split_pin_read {a : Assignment}
    (ha : (tinyRun.pin 1 (Value.bool true)).covers a) :
    a[1]? = some (Value.bool true) :=
  DecisionProto.Frame.split_pin_read
    ((Frame.splitP_nil tinyRun) ▸ Frame.splitData_split tinyRun_splitData) ha

end LeanFzn.Solver.Propagation.SparseRun

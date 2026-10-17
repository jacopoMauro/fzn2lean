/-
File: LeanFzn/Solver/UIP/Proofs/SupportedRun.lean

Purpose: the S1 interface. Raw `SchedulerReachable` is initialized by
`SchedulerConfig.init orig original props` for ARBITRARY boxes, clause
bases and propagator lists, so a consumer that quantifies over it claims
facts about unsupported executions (a mixed int/bool slot admits the
`pin_int_global_false` collision; arbitrary propagators lack the intended
entailment/evidence contracts). S1 fixes the execution basis:

  §1 `SupportedInput` — the honest problem-level hypotheses of ONE actual
     initializer: leaf/box fit, slot-wise typing, int-viewed domains,
     original-clause entailment by the leaf, and the concrete
     propagation/evidence obligations of the registered propagators.
     Every field has a compiled producer assigned to D1 (noted per field).
  §2 `SupportedReach orig original props` — root-indexed execution from
     EXACTLY `SchedulerConfig.init orig original props` along real
     `schedulerNext` successors. No invariant, preservation or progress
     field: the relation records only actual transitions.
  §3 The forgetting map `SupportedReach.reachable` (structural lemmas over
     raw reachability stay reusable) and the preserved-static-input
     adapters (`orig_eq`, `inputs_eq`, `triple_eq`).
  §4 A concrete supported-input witness: the hypotheses are inhabitable.
  §5 A kernel-checked counterexample isolating why the OLD universal gate
     shapes are false: at a mixed int/bool box the decision-pin claim
     fails at a `Fits`-assignment (the collision is
     `pin_int_global_false`, reused here at the split site).

NO `sorry`, NO custom axiom. Registration owes the umbrella import line
`LeanFzn.Solver.UIP.Proofs.SupportedRun` in `LeanFzn.Solver/LeanFzn.Solver.UIP.lean` (coordinator).
-/

import LeanFzn.Solver.UIP.Proofs.SchedulerDecision
import LeanFzn.Solver.UIP.Proofs.SchedulerRun
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 The supported-input hypotheses of one actual initializer -/

/-- The honest problem-level hypotheses of ONE supported initialization:
facts about the triple `(orig, original, props)` and the leaf ONLY — no
configuration, no run, no invariant. Each field names its compiled
producer (D1's job); none of them is a per-state semantic assumption. -/
structure SupportedInput (leaf : Assignment → Bool) (orig : List Domain)
    (original : List Clause) (props : List Propagator) : Prop where
  /-- every leaf solution fits the box (D1 producer:
      `CompiledInput.leaf_fits`) -/
  leaf_fits : ∀ a, leaf a = true → Assignment.Fits orig a
  /-- slot-wise typing of the box: every domain is int- or bool-shaped
      (D1 producer: the compiled declaration forms; the fragment gate the
      typed-pin producers consume) -/
  shape : ShapeTypedDomains orig
  /-- int-viewed domains (D1 producer: `CompiledInput.intViewedDomains`) -/
  viewed : ∀ d ∈ orig, IntViewedDomain d
  /-- the original clause base is entailed by the leaf (D1 producer:
      `CompiledInput.leaf_clauses`) -/
  original_entailed : ∀ c ∈ original, ∀ a, leaf a = true → c.SatisfiedBy a
  /-- the concrete propagation contract of the registered propagators
      (D1 producer: `CompiledInput.propagationContract`) -/
  contract : PropagationContract leaf props
  /-- the explanation-evidence discipline of the registered families
      (D1 producer: `propagatorEvidence_unit` and the E2 matrix rows) -/
  evidence : PropagatorEvidence leaf props

/-! ## §2 Root-indexed execution -/

/-- Execution from ONE fixed actual initializer: the exact
`SchedulerConfig.init orig original props` and its real `schedulerNext`
successors. No companion invariant or progress field — the constructors
record only the transition equations. -/
inductive SupportedReach {leaf : Assignment → Bool} (orig : List Domain)
    (original : List Clause) (props : List Propagator) :
    SchedulerConfig leaf → Prop where
  /-- the actual initializer of the supported triple -/
  | init (hent : LearnedEntailed leaf original) : SupportedReach orig original props
      (SchedulerConfig.init (leaf := leaf) orig original props)
  /-- one real dispatcher successor -/
  | step {cfg cfg' : SchedulerConfig leaf} :
      SupportedReach orig original props cfg →
      (schedulerNext cfg).successor = some cfg' →
      SupportedReach orig original props cfg'

namespace SupportedReach

variable {leaf : Assignment → Bool} {orig : List Domain}
  {original : List Clause} {props : List Propagator}

/-- FORGETTING MAP: supported execution is raw reachability, so every
structural lemma stated over `SchedulerReachable` remains reusable (with
the root triple carried explicitly by the S1 consumers). -/
theorem reachable : ∀ {cfg : SchedulerConfig leaf},
    SupportedReach orig original props cfg → SchedulerReachable cfg
  | _, .init hent => SchedulerReachable.init orig original props hent
  | _, .step h hs => SchedulerReachable.step rfl hs (reachable h)

/-- Every supported configuration carries the initializer's own box. -/
theorem orig_eq : ∀ {cfg : SchedulerConfig leaf},
    SupportedReach orig original props cfg → cfg.orig = orig
  | _, .init _ => rfl
  | _, .step h hs => (W1.schedulerNext_succ_orig hs).trans (orig_eq h)

/-- Every supported configuration carries the initializer's static
inputs (`orig`, `original`, `props`) — the frame facts the root-level
closure/contract transfer consumes. -/
theorem triple_eq : ∀ {cfg : SchedulerConfig leaf},
    SupportedReach orig original props cfg →
      cfg.orig = orig ∧ cfg.original = original ∧ cfg.props = props
  | _, .init _ => ⟨rfl, rfl, rfl⟩
  | _, .step h hs =>
      ⟨(W1.schedulerNext_succ_inputs hs).1.trans (triple_eq h).1,
       (W1.schedulerNext_succ_inputs hs).2.1.trans (triple_eq h).2.1,
       (W1.schedulerNext_succ_inputs hs).2.2.trans (triple_eq h).2.2⟩

theorem original_eq {cfg : SchedulerConfig leaf}
    (h : SupportedReach orig original props cfg) :
    cfg.original = original :=
  (triple_eq h).2.1

theorem props_eq {cfg : SchedulerConfig leaf}
    (h : SupportedReach orig original props cfg) :
    cfg.props = props :=
  (triple_eq h).2.2

end SupportedReach

/-! ## §3 Consumer shapes (frozen)

The S2 ports quantify over `SupportedReach orig original props` instead of
raw `SchedulerReachable`; the triple stays explicit so a producer for one
supported initializer discharges the premises of exactly that run. -/

/-- The scoped consumer shape: a property of every configuration of the
supported run. -/
def SupportedInvariantOn {leaf : Assignment → Bool} (orig : List Domain)
    (original : List Clause) (props : List Propagator)
    (P : SchedulerConfig leaf → Prop) : Prop :=
  ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg → P cfg

/-! ## §4 A concrete supported-input witness -/

/-- The witness box: one int slot with domain `{0, 1}`. -/
def witnessOrig : List Domain := [[Value.int 0, Value.int 1]]

/-- The witness leaf: exactly the assignment `[1]` is a solution. -/
def witnessLeaf : Assignment → Bool
  | [Value.int i] => decide (i = 1)
  | _ => false

theorem witness_fits : Assignment.Fits witnessOrig [Value.int 1] := by
  refine ⟨rfl, ?_⟩
  intro slot value hv
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hv
  have hslot : slot = 0 := by
    simp only [List.length_cons, List.length_nil] at hlt
    omega
  subst hslot
  have hval : value = Value.int 1 := by simpa using hget.symm
  subst hval
  show Value.int 1 ∈ [Value.int 0, Value.int 1]
  exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

theorem witness_shape : ShapeTypedDomains witnessOrig := by
  intro d hd
  simp only [witnessOrig, List.mem_singleton] at hd
  subst hd
  left
  intro v hv
  rcases (by simpa using hv : v = Value.int 0 ∨ v = Value.int 1) with
    rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

theorem witness_viewed : ∀ d ∈ witnessOrig, IntViewedDomain d := by
  intro d hd
  simp only [witnessOrig, List.mem_singleton] at hd
  subst hd
  intro v hv
  rcases (by simpa using hv : v = Value.int 0 ∨ v = Value.int 1) with
    rfl | rfl <;>
    simp [Value.intView]

/-- THE CONCRETE SUPPORTED-INPUT WITNESS: the interface is inhabitable
(not a vacuous record). The box is typed and viewed, the clause base and
propagator list are empty (their obligations vacuous), and the leaf fits
the box. -/
theorem witnessInput :
    SupportedInput witnessLeaf witnessOrig [] [] where
  leaf_fits := by
    intro a ha
    match a with
    | [] => simp [witnessLeaf] at ha
    | [v] =>
        match v with
        | Value.int i =>
            have hi : i = 1 :=
              of_decide_eq_true (by simpa [witnessLeaf] using ha)
            subst hi
            exact witness_fits
        | Value.bool b => simp [witnessLeaf] at ha
        | Value.setOfInt s => simp [witnessLeaf] at ha
        | Value.array s => simp [witnessLeaf] at ha
    | _ :: _ :: _ => simp [witnessLeaf] at ha
  shape := witness_shape
  viewed := witness_viewed
  original_entailed := by
    intro c hc
    exact absurd hc (by simp)
  contract :=
    ⟨fun _ _ p hp => (List.not_mem_nil hp).elim,
     fun _ _ p hp => (List.not_mem_nil hp).elim,
     fun _ _ p hp => (List.not_mem_nil hp).elim,
     fun _ _ p hp => (List.not_mem_nil hp).elim⟩
  evidence :=
    ⟨fun _ _ p hp => (List.not_mem_nil hp).elim,
     fun _ _ p hp => (List.not_mem_nil hp).elim,
     fun _ p hp => (List.not_mem_nil hp).elim⟩

/-- The witness initializer is a supported configuration (non-vacuity of
the root-indexed execution). -/
theorem witnessReach_init (leaf : Assignment → Bool) :
    SupportedReach (leaf := leaf) witnessOrig [] []
      (SchedulerConfig.init (leaf := leaf) witnessOrig [] []) :=
  SupportedReach.init (fun _ hc => absurd hc (List.not_mem_nil))

/-! ## §5 The universal-shape counterexample (mixed int/bool box)

The OLD gate shapes quantify a pin claim over EVERY reachable
configuration of an arbitrary box. This is FALSE: at the box
`[[.int 0, .bool false]]`, the split head `.int 0` carries the pin
`negNe 0 0`, whose normalized evaluation holds at the fitting assignment
`[.bool false]` (its integer view is `0`) while the slot does NOT hold
`.int 0`. The gate therefore cannot be produced over all roots — the S1
restriction to supported (typed) initialization is what makes the typed
pin producers applicable. -/

/-- The mixed witness box: slot 0 has domain `{.int 0, .bool false}`. -/
def mixedOrig : List Domain := [[Value.int 0, Value.bool false]]

/-- The colliding fitting assignment. -/
def mixedAssign : Assignment := [Value.bool false]

theorem mixed_fits : Assignment.Fits mixedOrig mixedAssign := by
  refine ⟨rfl, ?_⟩
  intro slot value hv
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hv
  have hslot : slot = 0 := by
    simp only [mixedAssign, List.length_cons, List.length_nil] at hlt
    omega
  subst hslot
  have hval : value = Value.bool false := by simpa [mixedAssign] using hget.symm
  subst hval
  show Value.bool false ∈ [Value.int 0, Value.bool false]
  exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

theorem mixed_splitData :
    splitData (SchedulerConfig.init (leaf := fun _ => false) mixedOrig [] []).branch.frame =
      some (negNe 0 0, Value.int 0, [Value.bool false], []) := by
  change splitData (mixedOrig, ([] : Assignment)) = _
  rw [splitData_eq_some_iff]
  exact ⟨rfl, valueLiteral_int⟩

/-- **THE COUNTEREXAMPLE**: the universal (all-roots) decision-pin gate
shape is FALSE. The statement below is exactly the `hpin` field shape of
`ArmGates`/`ArmInvGates` (a `SchedulerReachable` configuration, a
`splitData` equation, a non-redundant trail, and the pin iff for every
`Fits` assignment) — instantiated at the mixed box's root. No supported
initializer can inhabit the record while this field quantifies over every
root, which is precisely the S1 obstruction. -/
theorem universal_pin_gate_false :
    ¬ (∀ {leaf : Assignment → Bool} {cfg : SchedulerConfig leaf}
        {l : Literal} {v : Value} {vs : Domain} {doms : List Domain},
        SchedulerReachable cfg →
        splitData cfg.branch.frame = some (l, v, vs, doms) →
        TrailRedundant cfg.branch.trail l = false →
          ∀ a : Assignment, Assignment.Fits cfg.orig a →
            (l.norm.eval a = some true ↔
              a[cfg.branch.frame.2.length]? = some v)) := by
  intro h
  have hred : TrailRedundant (SchedulerConfig.init (leaf := fun _ => false)
      mixedOrig [] []).branch.trail (negNe 0 0) = false := rfl
  have hfit : Assignment.Fits (SchedulerConfig.init (leaf := fun _ => false)
      mixedOrig [] []).orig mixedAssign := by
    change Assignment.Fits mixedOrig mixedAssign
    exact mixed_fits
  have hp := h (leaf := fun _ => false)
    (cfg := SchedulerConfig.init (leaf := fun _ => false) mixedOrig [] [])
    (SchedulerReachable.init mixedOrig [] [] (fun _ hc => absurd hc (List.not_mem_nil))) mixed_splitData hred
    mixedAssign hfit
  change (negNe 0 0).norm.eval mixedAssign = some true ↔
    mixedAssign[0]? = some (Value.int 0) at hp
  change (negNe 0 0).norm.eval [Value.bool false] = some true ↔
    ([Value.bool false] : Assignment)[0]? = some (Value.int 0) at hp
  exact pin_int_global_false hp

end LeanFzn.Solver.UIP

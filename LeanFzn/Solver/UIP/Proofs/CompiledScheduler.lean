/-
File: LeanFzn/Solver/UIP/Proofs/CompiledScheduler.lean

Purpose:
  THE COMPILED-DOMAIN INSTANTIATION of the certified first-UIP/backjump
  scheduler. The accepted proof layers (S0 invariant, E3 root arm, C2a
  closure contract, A3/E1/E2 domain evidence) are stated for an
  ABSTRACT `leaf`/`orig`/`original`/`props`; this module fixes them to a
  compiled, gate-passing FlatZinc model and discharges the four named
  open premises:

  * `RootFactsBridge` (E3) — DISCHARGED here for (a) the real root
    configuration (`trail = []`, vacuous) and (b) any level-0 branch
    whose trail is the domain root-fact list (`rootFactsBridge_of_rootFacts`,
    from `rootFactsOfDomains_sound` + the problem→leaf fits bridge).
    The level-0 `.unsat` arm's coverage conclusion is exported as
    `root_arm_coverage`.
  * `ClosureContract` (C2a) — DISCHARGED by
    `CompiledInput.closureContract_of_provenance` (E1 route) and
    `CompiledInput.closureContract_of_discipline` (A3 route). The only
    non-derived argument is E1's per-state unit-shape scope condition
    `hShape`, tagged in the ledger.
  * `hpin`, the Int case (C2a) — `pin_int_of_frameHead`: the pin iff for
    frame-covered assignments of an int-typed head domain. FINDING: the
    GLOBAL iff shape requested by C2a is FALSE in general even for
    int-viewed slots — `.bool false`/`.bool true` share the integer view
    `0`/`1`, so `slotInt a s = some 0` holds at `a[s] = .bool false`
    while `a[s]? = some (.int 0)` fails (counterexample `pin_int_global_false`).
    Compiled models are slot-wise typed (`varDomain`: `.intDom` / `.boolDom`),
    so int slots use the frame-restricted pin and bool slots go through
    C2a's `stepDecide_bool_reachable`.
  * `hlent` / chronology — NOT public hypotheses of this file: the
    closure contract's `reasonEntailed`/`chronology` fields are what C2a
    consumes, and they are instantiated from A3/E1 evidence here; the
    learned-database discipline enters only through `hShape`.

Scalars and auxiliary slots (explicit accounting, PLAN D1a):
  A compiled model's variables become the problem's `domains` slots;
  the LCG layer has NO separate scalar/array storage — scalar
  parameters are either (a) folded into the constraint arguments
  (`DomConstraint.leConstHi slot k` carries `k` as data, not as a slot),
  or (b) materialised as ordinary single-valued slots by the front-end.
  Both cases are handled uniformly here: a materialised parameter slot
  is an ordinary domain slot, covered by the gate (`gateOk` requires it
  nonempty and int-viewed) and by every theorem below; a folded
  parameter never appears in `domains`, so no slot-indexed statement in
  this file quantifies over it. Auxiliary (definitional) slots are
  likewise ordinary slots of `problem.domains`: root facts
  (`rootFactsOfDomains`), the invariant and the contract are indexed by
  the full slot list, so nothing is silently dropped.

DAG:
  Proofs.SchedulerInvariant + Proofs.SchedulerConflict
    + Proofs.DomExplained + Proofs.LearnedExplanation
    + DomPruning + Certified
      -> Proofs.CompiledScheduler (this module; consumed by C3b / D1b)

Import line for the coordinator:

    import LeanFzn.Solver.UIP.Proofs.CompiledScheduler
-/

import LeanFzn.Solver.UIP.Proofs.SchedulerInvariant
import LeanFzn.Solver.UIP.Proofs.SchedulerConflict
import LeanFzn.Solver.UIP.Proofs.DomExplained
import LeanFzn.Solver.UIP.Proofs.LearnedExplanation
import LeanFzn.Solver.Propagation.DomPruningKit
import LeanFzn.Solver.Propagation.Gates
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 The compiled gate-passing input bundle -/

/-- A compiled, gate-passing model at the LCG level: the front-end's
`LeanFzn.Solver.Propagation.Problem DomConstraint Unit` together with the two executable gates the
certified path checks (`gateOk`, `domPruningOkB`) and the leaf
identification. `leaf_eq` is the problem→leaf entailment bridge: the
scheduler's leaf is the compiled chronological leaf, which is what makes
`fits` and the original clause database extractable. -/
structure CompiledInput (leaf : Assignment → Bool)
    (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit) : Prop where
  /-- the scheduler leaf IS the compiled chronological leaf -/
  leaf_eq : leaf = chronologicalLeaf problem DomConstraint.satisfiedB
  /-- the executable source gate: nonempty, int-viewed domains -/
  gate : gateOk problem = true
  /-- the executable kit gate: int-viewed domains and linear arity -/
  pruning : domPruningOkB problem = true

namespace CompiledInput

variable {leaf : Assignment → Bool} {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}

/-- The gate's int-view invariant, in the closure contract's vocabulary.
This is the typed-slot fragment gate the whole explained kit rests on;
DERIVED from `gateOk`, never assumed. -/
theorem intViewedDomains (hin : CompiledInput leaf problem) :
    ∀ d ∈ problem.domains, IntViewedDomain d := by
  intro d hd v hv
  exact intViewed_of_gate hin.gate d hd v hv

/-- The problem→leaf entailment bridge, part 1: a leaf assignment fits
the compiled box. -/
theorem leaf_fits (hin : CompiledInput leaf problem) {a : Assignment}
    (ha : leaf a = true) : a.Fits problem.domains := by
  rw [hin.leaf_eq] at ha
  simp only [chronologicalLeaf, Bool.and_eq_true] at ha
  exact fitsB_iff.mp ha.1

/-- The problem→leaf entailment bridge, part 2 (`hOriginal` of A3/E1): the
compiled leaf predicate already CONTAINS the original clause database,
so every original clause is entailed by the leaf semantics. This is a
derivation, not a premise. -/
theorem leaf_clauses (hin : CompiledInput leaf problem) (c : Clause)
    (hc : c ∈ problem.clauses) :
    ∀ a, leaf a = true → c.SatisfiedBy a := by
  intro a ha
  rw [hin.leaf_eq] at ha
  simp only [chronologicalLeaf, Bool.and_eq_true] at ha
  obtain ⟨l, hl, hev⟩ :=
    List.any_eq_true.mp (List.all_eq_true.mp ha.2.2 c hc)
  exact ⟨l, hl, of_decide_eq_true hev⟩

/-- The gate's shape-typing invariant (every domain holds only integers or
only Booleans), DERIVED from `domPruningOkB`: the premise under which the
explained `neSlot`/`allDiff` conflict clauses are entailed. -/
theorem shapeTypedDomains (hin : CompiledInput leaf problem) :
    DomsShapeTyped problem.domains :=
  domPruningOk_shape hin.pruning

/-- The certified propagation contract, transported from the executable
kit gate (`domPropagationContract`): the registered proved propagators of
the compiled problem discharge A2's `PropagationContract`. No
propagator-safety premise is asked of the caller. -/
theorem propagationContract (hin : CompiledInput leaf problem) :
    PropagationContract leaf
      (problem.constraints.filterMap propagatorOfProved) := by
  rw [hin.leaf_eq]
  exact domPropagationContract problem hin.pruning

/-! ## §2 The closure contract (C2a's `ClosureContract`) -/

/-- THE E1-ROUTE CONTRACT EXPORT: A2's complete `ClosureContract` for a
compiled gate-passing model, with the learned half supplied by E1's
insertion-provenance scope condition. Every other premise is derived
from the gates (`hOriginal` from the leaf, `hViewed` from `gateOk`, `hp`
from `domPruningOkB`, `hEvidence` from A3's unit kit). `hShape` is E1's
per-state unit-shape condition — the ONE named, explicitly-scoped
premise (owner: E1/integration); it is not learned-clause entailment and
not chronology. -/
theorem closureContract_of_provenance (hin : CompiledInput leaf problem)
    (hSupp : ∀ dc ∈ problem.constraints, unitFamilyB dc = true) :
    ClosureContract leaf problem.domains problem.clauses
      (problem.constraints.filterMap propagatorOfProved) :=
  domExplainedContract_of_provenance hin.leaf_clauses hin.intViewedDomains
    hin.shapeTypedDomains (fun _ ha => hin.leaf_fits ha)
    hin.propagationContract
    (propagatorEvidence_unit problem.constraints hSupp)
    (fun _ _ hu => hshape_of_unitLearned hu)

/-- THE A3-ROUTE CONTRACT EXPORT: the same contract with the learned half
supplied by A3's per-state `LearnedExplained` discipline instead of E1's
provenance. Kept for consumers written against A3; E1's route above is
the preferred one (the discipline is not stable under narrowing). -/
theorem closureContract_of_discipline (hin : CompiledInput leaf problem)
    (hSupp : ∀ dc ∈ problem.constraints, unitFamilyB dc = true)
    (hDisc : ∀ bs : BranchState leaf,
      ReachableState leaf problem.domains bs →
        UnitDB bs.learned → LearnedExplained leaf bs) :
    ClosureContract leaf problem.domains problem.clauses
      (problem.constraints.filterMap propagatorOfProved) :=
  domExplainedContract_of_problem problem hin.propagationContract hSupp
    hin.leaf_clauses hin.intViewedDomains hin.shapeTypedDomains
    (fun _ ha => hin.leaf_fits ha) hDisc

/-- THE SHAPE-FREE E1 CONTRACT EXPORT (D0): `hShape` is GONE — it is
discharged by L1's `unitShape_of_provenance` (`unit_shape_pivot`), at the
cost of the two reachable-state premises L1 names. Both are stated at
`ReachableState leaf problem.domains`:
* `hprov` — `ReachableLearnedProvenance`, the learned-database provenance
along reachable execution: preserved by every real step (L1's one-step
components); the composite is the standing S1/S5 driver-invariant
obligation (RESIDUAL, owner S1/S5 — NOT a hypothesis of explanation
validity: it is the database's insertion provenance, whose empty-state
case is `compiledScheduler_learned_entailed`);
* `hinhab` — `ReachableFrameInhabited`, per-state frame inhabitedness;
states whose frame has an empty remaining domain are excluded by PROVED
frame exclusion (`emptyFrame_byFrame_sound`, the same route
`arm_localExclude_log_sound` consumes), never by this predicate.
No explanation-validity or learned-entailment hypothesis is added: the
contract's `reasonEntailed`/`chronology` fields are still instantiated
from A3/E1 evidence inside. -/
theorem closureContract_of_reachable (hin : CompiledInput leaf problem)
    (hSupp : ∀ dc ∈ problem.constraints, unitFamilyB dc = true)
    (hprov : ReachableLearnedProvenance leaf
      (ReachableState leaf problem.domains)) :
    ClosureContract leaf problem.domains problem.clauses
      (problem.constraints.filterMap propagatorOfProved) :=
  domExplainedContract_of_provenance' hin.leaf_clauses hin.intViewedDomains
    hin.shapeTypedDomains (fun _ ha => hin.leaf_fits ha)
    hin.propagationContract
    (propagatorEvidence_unit problem.constraints hSupp)
    (fun bs hreach => hprov bs hreach)

end CompiledInput

/-! ## §3 Root facts (E3's `RootFactsBridge`) -/

/-- The bridge at the real root configuration: the trail is empty, so
every trail fact holds at every leaf solution — vacuously. This is the
a-priori level-0 justification at the initialiser. -/
theorem rootFactsBridge_init (leaf : Assignment → Bool) (orig : List Domain) :
    RootFactsBridge leaf (BranchState.init (orig, [])) := by
  intro a _ e he
  simp only [BranchState.init, List.not_mem_nil] at he

/-- The bridge for a level-0 branch whose trail IS the compiled box's
root-fact list: every root fact holds at every leaf solution, because
the leaf fits the box (`CompiledInput.leaf_fits`) and the box is
int-viewed (`rootFactsOfDomains_sound`). This is the a-priori argument
the level-0 `.unsat` arm rests on (E3's finding: the analyzer is NOT
consulted there). -/
theorem rootFactsBridge_of_rootFacts {leaf : Assignment → Bool}
    {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit} (hin : CompiledInput leaf problem)
    {bs : BranchState leaf}
    (htrail : bs.trail = rootFactsOfDomains problem.domains) :
    RootFactsBridge leaf bs := by
  intro a ha e he
  rw [htrail] at he
  exact rootFactsOfDomains_sound problem.domains a hin.intViewedDomains
    (hin.leaf_fits ha) e he

/-- EXACT REDUCTION OF THE PROPAGATED-TRAIL CASE (D0): the bridge from a
state that REPRESENTS every leaf solution. The trail-fact component of
`BranchState.Represents` IS the bridge's conclusion, so the level-0
propagated-trail case reduces to coverage correctness of the propagated
state — no trail-shape equality is needed. -/
theorem rootFactsBridge_of_represents {leaf : Assignment → Bool}
    {bs : BranchState leaf}
    (h : ∀ a, leaf a = true → bs.Represents a) :
    RootFactsBridge leaf bs :=
  fun a ha e he => (h a ha).2.1 e he

/-- THE LEVEL-0 PROPAGATED-TRAIL BRIDGE, DISCHARGED for the
explained-propagation driver: the trail of `explainedClosure` of the
compiled initial state is `rootFactsOfDomains`/narrowing literals in
arbitrary order (level-0 runtime propagation), and the bridge holds. The
proof is contract-driven (no trail-shape premise): the shape-free E1
contract's `explainedClosure_coverage` keeps every leaf solution
represented through the whole closure, and `Represents` carries the
trail facts. The two reachable-state premises are the S1/S5 residual
(`hprov`/`hinhab` of `closureContract_of_reachable`), and `hpay` is the
closure's payload-maintenance field (P1 round-2 repair; supplied at the
supported index by `unitPayload_of_unitKit (unitRunProfile_proved …)`);
the initial state is the PROVED root representation (`root_init_represents`
+ `hin.leaf_fits`). -/
theorem rootFactsBridge_of_explainedClosure {leaf : Assignment → Bool}
    {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit} (hin : CompiledInput leaf problem)
    (hSupp : ∀ dc ∈ problem.constraints, unitFamilyB dc = true)
    (hprov : ReachableLearnedProvenance leaf
      (ReachableState leaf problem.domains))
    (hpay : UnitPayload problem.clauses
      (problem.constraints.filterMap propagatorOfProved))
    (hinhab : ReachableFrameInhabited leaf
      (ReachableState leaf problem.domains)) :
    RootFactsBridge leaf
      (explainedClosure problem.domains problem.clauses
        (problem.constraints.filterMap propagatorOfProved)
        (BranchState.init (problem.domains, []))) :=
  rootFactsBridge_of_represents fun a ha =>
    explainedClosure_coverage
      (hin.closureContract_of_reachable hSupp hprov)
      (BranchState.init (problem.domains, [])) hpay
      (reachable_init leaf problem.domains) unitDB_nil a ha
      (root_init_represents (hin.leaf_fits ha))

/-- The `hdead` shape S0's `SchedulerInvariant.unsat_coverage` consumes,
discharged from an `AnalyzerInput` plus the root-facts bridge. -/
theorem root_unsat_dead {leaf : Assignment → Bool} {bs : BranchState leaf}
    (hin : AnalyzerInput leaf bs) (hbridge : RootFactsBridge leaf bs)
    (f : BranchFrame) :
    ∀ a, leaf a = true → FrameCovers f a → False :=
  dead_of_root_contradiction (rootContradiction_sound hin hbridge) f

/-- THE LEVEL-0 `.unsat` ARM, ASSEMBLED: with the level-0 conflict's
`AnalyzerInput` + `RootFactsBridge` and an exhausted frontier, every
original leaf solution is excluded by the learned database — exactly the
conclusion the `unsat` verdict needs. Composes E3's
`rootContradiction_sound` with S0's `unsat_coverage`. -/
theorem root_arm_coverage {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} (hinv : SchedulerInvariant cfg)
    (hpend : cfg.pending = [])
    (hin : AnalyzerInput leaf cfg.branch)
    (hbridge : RootFactsBridge leaf cfg.branch) :
    ∀ a, OriginalLeaves leaf cfg.orig a →
      ∃ c ∈ cfg.branch.learned, ¬ c.SatisfiedBy a :=
  hinv.unsat_coverage hpend (root_unsat_dead hin hbridge cfg.branch.frame)

/-! ## §4 The concrete initialisation package (consumed by C3b / D1b) -/

/-- The concrete `SchedulerConfig` of a compiled problem: the real root
configuration over the compiled box, clause database and registered
proved propagators. -/
def CompiledScheduler (leaf : Assignment → Bool)
    (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit) : SchedulerConfig leaf :=
  SchedulerConfig.init (leaf := leaf) problem.domains problem.clauses
    (problem.constraints.filterMap propagatorOfProved)

/-- THE INITIALISER WITNESS (S0 instantiated at a real compiled problem):
the concrete configuration satisfies the full scheduler invariant. NO
premises beyond the entailment of the problem's original clauses (R1c: they
seed the scanned database; vacuous for the compiled `clauses = []`): the
frontier is the real `[(orig, [])]`, the pending list is empty. -/
theorem compiledScheduler_invariant (leaf : Assignment → Bool)
    (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit)
    (hent : LearnedEntailed leaf problem.clauses) :
    SchedulerInvariant (CompiledScheduler leaf problem) :=
  schedulerInvariant_init leaf problem.domains problem.clauses
    (problem.constraints.filterMap propagatorOfProved) hent

/-- The initialiser's root-facts bridge (vacuous trail). -/
theorem compiledScheduler_rootFacts (leaf : Assignment → Bool)
    (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit) :
    RootFactsBridge leaf (CompiledScheduler leaf problem).branch :=
  rootFactsBridge_init leaf problem.domains

/-- The initialiser's coverage obligation, extracted from the invariant —
the non-vacuity half C3b's `unsat_outcome_coverage` consumes. -/
theorem compiledScheduler_coverage (leaf : Assignment → Bool)
    (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit)
    (hent : LearnedEntailed leaf problem.clauses) :
    (CompiledScheduler leaf problem).coverage :=
  (compiledScheduler_invariant leaf problem hent).coverage

/-- The initialiser's learned-database entailment: the database is empty,
so `LearnedEntailed` holds without any chronology or entailment premise.
(`hlent` is never a public hypothesis of this package.) -/
theorem compiledScheduler_learned_entailed (leaf : Assignment → Bool)
    (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit)
    (hent : LearnedEntailed leaf problem.clauses) :
    ∀ c ∈ (CompiledScheduler leaf problem).branch.learned,
      LearnedEntailed leaf [c] :=
  (compiledScheduler_invariant leaf problem hent).learned_entailed

/-- THE BUNDLE FROM THE EXECUTABLE GATES (D0): the two executable checks
(`gateOk`, `domPruningOkB`) plus the problem→leaf identification ARE the
`CompiledInput` bundle — no further source premise exists. Materialised
parameter and auxiliary slots are ordinary slots of `problem.domains`
here; folded scalar parameters are constraint arguments and appear
nowhere in this statement. -/
theorem compiledInput_of_gates {leaf : Assignment → Bool}
    {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (hleaf : leaf = chronologicalLeaf problem DomConstraint.satisfiedB)
    (hgate : gateOk problem = true) (hprune : domPruningOkB problem = true) :
    CompiledInput leaf problem :=
  ⟨hleaf, hgate, hprune⟩

/-- THE EXISTING SOURCE GATE IMPLIES THE REQUIRED INITIAL PACKAGE (D0):
from the two executable checks alone, the compiled configuration carries
the full scheduler invariant (no premises), the root-facts bridge, the
coverage obligation, the empty-database entailment, and the typed-slot
fragment (`IntViewedDomain` for EVERY slot — including materialised
parameter and auxiliary slots; folded parameters are constraint
arguments and are not quantified over). -/
theorem initialPackage_of_gates {leaf : Assignment → Bool}
    {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (hleaf : leaf = chronologicalLeaf problem DomConstraint.satisfiedB)
    (hgate : gateOk problem = true) (hprune : domPruningOkB problem = true) :
    SchedulerInvariant (CompiledScheduler leaf problem) ∧
      RootFactsBridge leaf (CompiledScheduler leaf problem).branch ∧
      (CompiledScheduler leaf problem).coverage ∧
      (∀ c ∈ (CompiledScheduler leaf problem).branch.learned,
        LearnedEntailed leaf [c]) ∧
      (∀ d ∈ problem.domains, IntViewedDomain d) :=
  have hin := compiledInput_of_gates hleaf hgate hprune
  have hent : LearnedEntailed leaf problem.clauses := hin.leaf_clauses
  ⟨compiledScheduler_invariant leaf problem hent,
   compiledScheduler_rootFacts leaf problem,
   compiledScheduler_coverage leaf problem hent,
   compiledScheduler_learned_entailed leaf problem hent,
   hin.intViewedDomains⟩

/-! ## §5 The Int pin bridge (`hpin` of C2a's decide theorem) -/

/-- An int-typed domain: every value is literally `.int`. Compiled models
are slot-wise typed (`varDomain` produces `.intDom` or `.boolDom`). -/
def IntTypedDomain (d : Domain) : Prop :=
  ∀ v ∈ d, ∃ i : Int, v = .int i

/-- The pin literal of an int-typed head value: `valueLiteral` sends
`.int i` to `negNe slot i`. -/
theorem valueLiteral_int {s : Nat} {i : Int} :
    valueLiteral s (.int i) = some (negNe s i) := rfl

/-- The lift from a slot-typed assignment to the int literal: for an
assignment whose slot value is literally an `.int`, `slotInt` equality
and value equality coincide. This is the exact content the C2a hand-off
names (`IntViewedDomain` alone is INSUFFICIENT — see
`pin_int_global_false`). -/
theorem pin_int_iff_of_intSlot {s : Nat} {i : Int} {a : Assignment}
    (htyp : ∀ v, a[s]? = some v → ∃ k : Int, v = .int k) :
    (negNe s i).norm.eval a = some true ↔ a[s]? = some (.int i) := by
  constructor
  · intro h
    rw [Literal.norm_eval, eval_negNe_iff] at h
    obtain ⟨j, hj, hji⟩ := h
    subst j
    obtain ⟨v, hv, hiv⟩ := Option.bind_eq_some_iff.mp hj
    obtain ⟨k, rfl⟩ := htyp v hv
    rw [Value.intView] at hiv
    have hk : k = i := Option.some.inj hiv
    rw [hk] at hv
    exact hv
  · intro h
    rw [Literal.norm_eval, eval_negNe_iff]
    exact ⟨i, by simp only [slotInt, h, Option.bind_some, Value.intView], rfl⟩

/-- The coverage of a frame with a nonempty head domain: every covered
assignment reads a member of the head domain at the split slot. -/
theorem frameCovers_head_mem {d : Domain} {rest : List Domain}
    {pre : Assignment} {a : Assignment}
    (hcov : FrameCovers ((d :: rest), pre) a) :
    ∃ v ∈ d, a[pre.length]? = some v := by
  obtain ⟨tail, htail, rfl⟩ := hcov
  cases d with
  | nil => simp only [allAssigns, List.not_mem_nil] at htail
  | cons v0 vs =>
      obtain ⟨w, hw, suffix, _, rfl⟩ :=
        (mem_allAssigns_singleton v0 vs rest tail).mp htail
      exact ⟨w, hw, by
        rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl⟩

/-- THE INT PIN THEOREM (the discharge of C2a's `hpin` for int-typed head
domains, in the frame-restricted form the decide transition actually
uses): for every assignment covered by the frame with head domain `d`,
the integer pin `negNe pre.length i` holds exactly when the slot takes
the value `.int i`. -/
theorem pin_int_of_frameHead {d : Domain} {rest : List Domain}
    {pre : Assignment} {i : Int} (htyp : IntTypedDomain d)
    (a : Assignment) (hcov : FrameCovers ((d :: rest), pre) a) :
    (negNe pre.length i).norm.eval a = some true ↔
      a[pre.length]? = some (.int i) := by
  obtain ⟨v0, hv0, hget⟩ := frameCovers_head_mem hcov
  obtain ⟨k, rfl⟩ := htyp v0 hv0
  exact pin_int_iff_of_intSlot (s := pre.length) (i := i) (a := a)
    (fun v hv => by
      rw [hget] at hv
      exact ⟨k, (Option.some.inj hv).symm⟩)

/-- The `∀ a` form C2a's `hpin` consumes, frame-restricted. -/
theorem pin_int_of_frameHead_forall {d : Domain} {rest : List Domain}
    {pre : Assignment} {i : Int} (htyp : IntTypedDomain d) :
    ∀ a, FrameCovers ((d :: rest), pre) a →
      ((negNe pre.length i).norm.eval a = some true ↔
        a[pre.length]? = some (.int i)) :=
  fun a hcov => pin_int_of_frameHead (d := d) (rest := rest) (pre := pre)
    (i := i) htyp a hcov

/-- FINDING / COUNTEREXAMPLE: the GLOBAL pin iff requested by C2a's
`stepDecide_reachable` is FALSE for Int decisions whose value collides
with a Boolean integer view (`intView (.bool false) = some 0`,
`intView (.bool true) = some 1`). At `a = [.bool false]` the literal
`negNe 0 0` EVALUATES true (`slotInt = some 0`) while the slot does not
hold `.int 0`, so the `.mp` direction (the one `reachable_decide` uses
for `prefix_forced`) fails. The frame-restricted `pin_int_of_frameHead`
above is the true statement; compiled models avoid the collision because
`varDomain` is slot-wise typed (bool slots take the Bool route). -/
theorem pin_int_global_false :
    ¬ ((negNe 0 0).norm.eval ([.bool false] : List Value) = some true ↔
        (([.bool false] : List Value)[0]? = some (.int 0))) := by
  intro h
  have hl : (negNe 0 0).norm.eval ([.bool false] : List Value) = some true := by
    rw [Literal.norm_eval, eval_negNe_iff]
    exact ⟨0, by simp [slotInt, Value.intView], rfl⟩
  have hc := h.mp hl
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
  cases hc

/-! ## §6 Representative compiled inputs, every retained source family -/

/-- Supported unit family (E2 matrix row 1: `leConstHi`): slot 0 has the
finite int domain `{0,1,2}` and the box bound `x ≤ 2` relative to the
original domain. (The constraint's constant `2` is a SCALAR PARAMETER
folded into the constraint argument — it is data, not a slot; no slot of
`domains` is consumed by it.) -/
private def famUnit : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
  { names := ["x"], domains := [[.int 0, .int 1, .int 2]],
    constraints := [.leConstHi 0 2], objective := (), clauses := [] }

/-- Boolean family (E2 matrix row 2: `boolNotSlot`, explained non-unit):
a materialised auxiliary Boolean slot `b` (the compiled front-end gives
it an ordinary two-value domain); the constraint is NOT in the unit
fragment, so this family keeps the proved local fallback for the
explained route while every scalar/aux-slot-independent export below
still applies. -/
private def famBool : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
  { names := ["x", "b"], domains := [[.int 0, .int 1], [.bool false, .bool true]],
    constraints := [.boolNotSlot 1 0], objective := (), clauses := [] }

/-- Deferred family (E2 matrix row 3: `allDiff`, proved local fallback):
an integer-typed box with an `allDiff` over the two materialised scalar
slots. -/
private def famAllDiff : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
  { names := ["x", "y"], domains := [[.int 0, .int 1], [.int 0, .int 1]],
    constraints := [.allDiff [0, 1]], objective := (), clauses := [] }

private def famUnitLeaf : Assignment → Bool :=
  chronologicalLeaf famUnit DomConstraint.satisfiedB

private def famBoolLeaf : Assignment → Bool :=
  chronologicalLeaf famBool DomConstraint.satisfiedB

private def famAllDiffLeaf : Assignment → Bool :=
  chronologicalLeaf famAllDiff DomConstraint.satisfiedB

/-- The executable source gate on the supported-family representative:
kernel reduction on a concrete problem (no `decide` tactic, no
`native_decide`; every `Decidable`/`BEq` instance here is kernel-reducible). -/
private theorem gateOk_famUnit : gateOk famUnit = true := rfl

/-- The executable source gate on the Boolean-family representative. -/
private theorem gateOk_famBool : gateOk famBool = true := rfl

/-- The executable source gate on the `allDiff`-family representative. -/
private theorem gateOk_famAllDiff : gateOk famAllDiff = true := rfl

/-- The kit gate on the supported-family representative. -/
private theorem pruningOk_famUnit : domPruningOkB famUnit = true := rfl

/-- The kit gate on the Boolean-family representative. -/
private theorem pruningOk_famBool : domPruningOkB famBool = true := rfl

/-- The kit gate on the `allDiff`-family representative. -/
private theorem pruningOk_famAllDiff : domPruningOkB famAllDiff = true := rfl

/-- The supported family passes the supported-fragment gate. -/
example : domSupportedB famUnit = true := rfl

/-- The Boolean and `allDiff` families do NOT (they keep the fallback). -/
example : domSupportedB famBool = false := rfl

example : domSupportedB famAllDiff = false := rfl

/-- Every retained family's representative passes the executable source
gate. -/
example : gateOk famUnit = true := gateOk_famUnit

example : gateOk famBool = true := gateOk_famBool

example : gateOk famAllDiff = true := gateOk_famAllDiff

/-- Every retained family's representative passes the kit gate. -/
example : domPruningOkB famUnit = true := pruningOk_famUnit

example : domPruningOkB famBool = true := pruningOk_famBool

example : domPruningOkB famAllDiff = true := pruningOk_famAllDiff

/-- The `CompiledInput` bundle for each retained family. -/
example : CompiledInput famUnitLeaf famUnit :=
  ⟨rfl, gateOk_famUnit, pruningOk_famUnit⟩

example : CompiledInput famBoolLeaf famBool :=
  ⟨rfl, gateOk_famBool, pruningOk_famBool⟩

example : CompiledInput famAllDiffLeaf famAllDiff :=
  ⟨rfl, gateOk_famAllDiff, pruningOk_famAllDiff⟩

/-- The initialisation package applies to every retained family,
unconditionally (no premises at all). -/
example : SchedulerInvariant (CompiledScheduler famUnitLeaf famUnit) :=
  compiledScheduler_invariant famUnitLeaf famUnit
    (⟨rfl, gateOk_famUnit, pruningOk_famUnit⟩ : CompiledInput famUnitLeaf famUnit).leaf_clauses

example : SchedulerInvariant (CompiledScheduler famBoolLeaf famBool) :=
  compiledScheduler_invariant famBoolLeaf famBool
    (⟨rfl, gateOk_famBool, pruningOk_famBool⟩ : CompiledInput famBoolLeaf famBool).leaf_clauses

example : SchedulerInvariant (CompiledScheduler famAllDiffLeaf famAllDiff) :=
  compiledScheduler_invariant famAllDiffLeaf famAllDiff
    (⟨rfl, gateOk_famAllDiff, pruningOk_famAllDiff⟩ : CompiledInput famAllDiffLeaf famAllDiff).leaf_clauses

/-- The compiled leaf→fits bridge on a representative input, from the
bundle alone. -/
example {a : Assignment} (ha : famUnitLeaf a = true) :
    a.Fits famUnit.domains :=
  CompiledInput.leaf_fits
    (hin := ⟨rfl, gateOk_famUnit, pruningOk_famUnit⟩) ha

/-! ## §7 Family exercise note (D0): explained route vs proved fallback

Retained-family accounting against L2's matrix, decided executably here:

* famUnit (`leConstHi`, matrix row 1, `unitFamilyB = true`): propagates
EXPLAINED. Its constraint's evidence is `propagatorEvidence_unit`'s unit
row, so the shape-free contract instance is available
(`closureContract_of_reachable`, §2) with only the two S1/S5
reachable-state premises; the level-0 propagated-trail bridge of §3
applies to it unchanged.
* famBool (`boolNotSlot`, matrix row 2, `unitFamilyB = false`): outside
the unit evidence fragment, so the explained-route contract export does
NOT apply and this family keeps the proved local fallback
(`propagatorOfProved` drops it; `CompiledInput.propagationContract`
holds for the registered proved subset via `domPruningOkB`). Its
materialised AUXILIARY Boolean slot is still a gate-typed slot
(`IntViewedDomain`, proved below); its pins go through S1's bool route
(`stepDecide_bool_reachable`), never the int frame fallback.
* famAllDiff (`allDiff`, matrix row 3, `unitFamilyB = false`): deferred
row — proved local fallback, same accounting as famBool; the family
checks `gateOk`/`domPruningOkB`/`CompiledInput`/invariant already hold
unconditionally above.

No family exercises a source-level explanation-validity or
learned-entailment hypothesis: the fallback families never enter the
contract export at all, and the unit family's export takes only the
two reachable-state premises. -/

/-- The unit-family evidence premise, decided by kernel reduction. -/
private theorem unitFamily_famUnit :
    ∀ dc ∈ famUnit.constraints, unitFamilyB dc = true := by
  intro dc hd
  simp only [famUnit, List.mem_singleton] at hd
  rw [hd]
  rfl

/-- The bool row is OUTSIDE the unit evidence fragment (executable). -/
example : unitFamilyB (.boolNotSlot 1 0) = false := rfl

/-- The allDiff row is OUTSIDE the unit evidence fragment (executable). -/
example : unitFamilyB (.allDiff [0, 1]) = false := rfl

/-- The unit family's shape-free contract instance: only the two
reachable-state premises remain (owner S1/S5 for the composite). -/
example (hprov : ReachableLearnedProvenance famUnitLeaf
      (ReachableState famUnitLeaf famUnit.domains))
    (hinhab : ReachableFrameInhabited famUnitLeaf
      (ReachableState famUnitLeaf famUnit.domains)) :
    ClosureContract famUnitLeaf famUnit.domains famUnit.clauses
      (famUnit.constraints.filterMap propagatorOfProved) :=
  CompiledInput.closureContract_of_reachable
    (hin := ⟨rfl, gateOk_famUnit, pruningOk_famUnit⟩)
    (hSupp := unitFamily_famUnit) hprov

/-- The unit family's level-0 propagated-trail bridge (same premises; the
payload-maintenance field is supplied by `unitPayload_of_unitKit` from the
proved kit profile, `unitRunProfile_proved`). -/
example (hprov : ReachableLearnedProvenance famUnitLeaf
      (ReachableState famUnitLeaf famUnit.domains))
    (hinhab : ReachableFrameInhabited famUnitLeaf
      (ReachableState famUnitLeaf famUnit.domains)) :
    RootFactsBridge famUnitLeaf
      (explainedClosure famUnit.domains famUnit.clauses
        (famUnit.constraints.filterMap propagatorOfProved)
        (BranchState.init (famUnit.domains, []))) :=
  rootFactsBridge_of_explainedClosure
    (hin := ⟨rfl, gateOk_famUnit, pruningOk_famUnit⟩)
    (hSupp := unitFamily_famUnit) hprov
    (unitPayload_of_unitKit
      (unitRunProfile_proved famUnit.constraints unitFamily_famUnit))
    hinhab

/-- The aux Bool slot of famBool is a gate-typed slot (`IntViewedDomain`
includes `.bool` values through their integer view) — aux slots need no
special handling. -/
example : ∀ d ∈ famBool.domains, IntViewedDomain d :=
  (⟨rfl, gateOk_famBool, pruningOk_famBool⟩ :
    CompiledInput famBoolLeaf famBool).intViewedDomains

/-- TYPED PINS from the gate shape: the supported family's int head
domain is literally `.int`-typed, so C2a's frame-restricted int pin is
available for it via `pin_int_of_frameHead` (the gate's int-VIEW alone
would not suffice — see `pin_int_global_false`; `.intDom`-compiled
domains are literally int-typed, bool slots take S1's bool route). -/
example (i : Int) (a : Assignment)
    (hcov : FrameCovers ([[.int 0, .int 1, .int 2]], []) a) :
    (negNe 0 i).norm.eval a = some true ↔ a[0]? = some (.int i) :=
  pin_int_of_frameHead (d := [.int 0, .int 1, .int 2]) (rest := [])
    (pre := []) (i := i)
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩)
    a hcov

/-- The initial package of the supported family, from its two
executable gates alone (all five conjuncts of
`initialPackage_of_gates`). -/
example : SchedulerInvariant (CompiledScheduler famUnitLeaf famUnit) ∧
    RootFactsBridge famUnitLeaf
      (CompiledScheduler famUnitLeaf famUnit).branch ∧
    (∀ d ∈ famUnit.domains, IntViewedDomain d) :=
  ⟨(initialPackage_of_gates (leaf := famUnitLeaf) (problem := famUnit)
      rfl gateOk_famUnit pruningOk_famUnit).1,
   (initialPackage_of_gates (leaf := famUnitLeaf) (problem := famUnit)
      rfl gateOk_famUnit pruningOk_famUnit).2.1,
   (initialPackage_of_gates (leaf := famUnitLeaf) (problem := famUnit)
      rfl gateOk_famUnit pruningOk_famUnit).2.2.2.2⟩

end LeanFzn.Solver.UIP

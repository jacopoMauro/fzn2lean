/-
File: solver/LCG/Proofs/Obstructions.lean

Purpose:
  Machine-checked obstructions and counterexamples that justify the
  invariant gates and premise shapes of the LCG proof chain. These are
  negative results: each theorem here demonstrates that a proposed
  WEAKER premise or invariant is refuted by an explicit witness state,
  so the corresponding stronger premise carried by the live theorems
  is necessary, not accidental. Extracted from the former tmp/ scratch
  deliverables (a3_candidate.lean, a3_vacuity_test.lean,
  leafng_deliverable.lean) whose prose citations in Run.lean,
  Reason.lean and Fallback.lean pointed here; they are now maintained
  regressions.

Contents:
  1. `counterexample_opposing_fires` + `premises_inconsistent` — the
     two obstructions that forced the DECISION-DESCENT master
     theorem's `TrailDistinct` invariant and the run-relativized
     `hconfent` premise (formerly vacuous over freely-constructed
     states).
  2. `boolPins_premise_necessary` — the `TrailBoolPins` premise of
     `leafNogood_entailed` (Reason.lean) is necessary: without it the
     leaf-nogood entitlement is FALSE on a mixed-domain witness.
  3. `hconfent_vacuous` — the OLD `hconfent` premise shape (no
     invariant restriction on its state) is inconsistent with
     solvability; vacuity regression guarding the repaired premise.

Dependencies:
  - solver.LCG.Proofs.Run (State, RunInv, Level0Solved, the engine's
    propagateLoop / repairAfterBackjump / enqueueNorm / analyzeConflict
    definitions and the master theorem's context).
  - solver.LCG.Proofs.Search (ProblemSolution, fitsB, RootFacts,
    TrailBoolPins, allSingleton, singletonAssignment, domOfLit — the
    leaf-entitlement vocabulary).

Why:
  Each witness needs the full run-level state shapes to be a genuine
  counterexample, so the proofs live beside the definitions they
  constrain.

DAG:
  LCG.Proofs.Run + LCG.Proofs.Search -> Obstructions (leaf module;
  nothing imports it; audited by CI's user-axiom and proof-hole scans
  together with the rest of the tree).
-/

import solver.LCG.Proofs.Run
import solver.LCG.Proofs.Search

namespace LeanFzn.Solver.LCG

open LeanFzn LeanFzn.Solver.Core

/-! ## Obstruction 1 (TrailDistinct is not derivable from
RunInv + Level0Solved): the opposing-fire witness -/

/-- The witness problem: one int slot with domain {1,2,4,5} and the
    entitled clause [¬(s ≤ 3), s ≤ 2]. -/
def probX : Problem DomConstraint Unit where
  names := ["s"]
  domains := [[Value.int 1, Value.int 2, Value.int 4, Value.int 5]]
  constraints := []
  objective := ()
  clauses := [[negLe 0 3, posLe 0 2]]

/-- The witness state: the UIP literal posLe 0 3 appears at BOTH level 1
    and level 2; negLe 0 2 at level 1. The state satisfies RunInv +
    Level0Solved + conflict-none (verified in the former
    tmp/a3_probe3.lean, re-provable from the RunInv field lemmas), so
    it is a legitimate induction subject for the master theorem's IH —
    but its trail is NOT literal-distinct, which is why RunInv carries
    the separate `TrailDistinct` field. -/
def stX : State where
  domains := [[]]
  trail := [⟨posLe 0 3, 1, none⟩, ⟨negLe 0 2, 1, none⟩, ⟨posLe 0 3, 2, none⟩]
  decisionLevel := 2
  clauses := probX.clauses
  learned := []
  queue := []
  conflict := none

/-- OBSTRUCTION 1, machine-checked: on stX, the analysis arm's
    asserting enqueue hits the OPPOSING branch (the enqueued literal
    is already on the trail at the retained level): the enqueued state
    carries the two-literal conflict, so an IH transfer that assumes
    conflict-clear from RunInv + Level0Solved alone cannot close the
    arm. This is the machine-checked justification for the
    `TrailDistinct` invariant field (RunInv): with trail distinctness,
    the enqueue's skip branch fires instead and the conflict slot stays
    clear. -/
theorem counterexample_opposing_fires :
    (propagateLoop (engineFuel stX) [] stX).conflict.isSome = true ∧
    ∃ an : ConflictAnalysis,
      analyzeConflict (propagateLoop (engineFuel stX) [] stX) = some an ∧
      an.backjumpLevel = 1 ∧
      ((enqueueNorm
          ({ repairAfterBackjump probX 1
              (propagateLoop (engineFuel stX) [] stX) with
            learned := [negLe 0 3, posLe 0 2] ::
              (repairAfterBackjump probX 1
                (propagateLoop (engineFuel stX) [] stX)).learned })
        (negLe 0 3)
        (some { clause := [negLe 0 3, posLe 0 2] })).conflict
        = some [negLe 0 3, posLe 0 3]) := by
  have h1 : (propagateLoop (engineFuel stX) [] stX).conflict.isSome
      = true := by native_decide
  refine ⟨h1, ?_⟩
  have h1' : (propagateLoop (engineFuel stX) [] stX).conflict
      = some [negLe 0 3, posLe 0 2] := by native_decide
  have h1'' : (propagateLoop (engineFuel stX) [] stX).decisionLevel = 2 := by
    native_decide
  have h2 : analyzeTrail (propagateLoop (engineFuel stX) [] stX).trail
      2 [negLe 0 3, posLe 0 2]
      = some ([(posLe 0 2, 1)], posLe 0 3) := by native_decide
  have hdec : analyzeConflict (propagateLoop (engineFuel stX) [] stX)
      = some (⟨[negLe 0 3, posLe 0 2], 1, negLe 0 3⟩ : ConflictAnalysis) := by
    unfold analyzeConflict
    rw [h1']
    simp only []
    rw [h1'', h2]
    rfl
  rw [hdec]
  have h3 : (enqueueNorm
      { repairAfterBackjump probX 1
          (propagateLoop (engineFuel stX) [] stX) with
        learned := [negLe 0 3, posLe 0 2] ::
          (repairAfterBackjump probX 1
            (propagateLoop (engineFuel stX) [] stX)).learned }
      (negLe 0 3)
      (some { clause := [negLe 0 3, posLe 0 2] })).conflict
      = some [negLe 0 3, (negLe 0 3).negate] := by
    native_decide
  refine ⟨_, rfl, rfl, ?_⟩
  rw [h3]
  show some [negLe 0 3, (negLe 0 3).negate] = some [negLe 0 3, posLe 0 3]
  rfl

/-! ## Obstruction 2 (the run-unrelativized `hconfent` premise is
inconsistent with solvability) -/

/-- OBSTRUCTION 2, machine-checked: `hconfent` in its run-unrelativized
    shape (quantified over ALL states with no invariant premise)
    contradicts `hsolvable`: instantiating it at a freely-constructed
    state whose conflict slot carries the EMPTY clause demands a member
    of `[]`. The master theorem's premise set was therefore
    UNSATISFIABLE in that shape and the theorem held only vacuously;
    the live premise restricts entitlement to the run's own states.
    Regression: if the premise is ever widened back, this theorem (and
    `hconfent_vacuous` below) re-fires. -/
theorem premises_inconsistent
    {Constraint Objective : Type}
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    (hsolvable : ∃ b, ProblemSolution problem constraintHolds b)
    (hconfent : ∀ (st1 : State) (cc : Clause),
      st1.conflict = some cc →
      ∀ a, ProblemSolution problem constraintHolds a →
        ∃ l ∈ cc, l.eval a = some true) :
    False := by
  obtain ⟨b, hb⟩ := hsolvable
  have hbad : ∃ l, l ∈ ([] : Clause) ∧ l.eval b = some true :=
    hconfent (⟨[], [], 0, [], [], [], some []⟩ : State) [] rfl b hb
  rcases hbad with ⟨l, hl, _⟩
  exact absurd hl (by simp)

/-- The compact twin of `premises_inconsistent` kept from the original
    vacuity probe: the run-unrelativized `hconfent` demands a true
    member of the EMPTY clause at a solution. -/
theorem hconfent_vacuous
    {Constraint Objective : Type}
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    (hsolvable : ∃ b, ProblemSolution problem constraintHolds b)
    (hconfent : ∀ (st1 : State) (cc : Clause),
      st1.conflict = some cc →
      ∀ a, ProblemSolution problem constraintHolds a →
        ∃ l ∈ cc, l.eval a = some true) :
    False := premises_inconsistent hsolvable hconfent

/-! ## Obstruction 3 (the `TrailBoolPins` premise of the leaf-nogood
entitlement is necessary) -/

/-- The witness problem: one slot whose domain mixes an integer and a
    Boolean; no constraints, no SAT clauses. -/
def probB : Problem DomConstraint Unit where
  names := ["x"]
  domains := [[Value.int 5, Value.bool false]]
  constraints := []
  objective := ()
  clauses := []

/-- The witness state: the trail is the single level-1 Boolean pin
    `boolEq 0 true`; the domains are its `domOfLit` fold (the pinned
    slot becomes `[.bool true]`). -/
def stB : State where
  domains := [[Value.bool true]]
  trail := [TrailEntry.mk (Literal.mk (Atom.boolEq 0 true) true) 1 none]
  decisionLevel := 1
  clauses := []
  learned := []
  queue := []
  conflict := none

/-- `[.int 5]` is a ProblemSolution of `probB` (it fits the mixed
    domain; there are no constraints to satisfy). -/
private theorem solB : ProblemSolution probB DomConstraint.SatisfiedBy
    [Value.int 5] := by
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · intro slot value hv
    have hlt : slot < 1 := (List.getElem?_eq_some_iff.mp hv).1
    have h0 : slot = 0 := by omega
    subst h0
    have hv2 : ([Value.int 5] : List Value)[0]? = some value := hv
    rw [show ([Value.int 5] : List Value)[0]? = some (Value.int 5)
      from rfl] at hv2
    injection hv2 with hv3
    rw [← hv3]
    exact List.mem_cons_self
  · intro dc hdc
    exact absurd hdc (by simp [probB])

/-- The witness state is coherent (the domains are the pin's
    `domOfLit` fold). -/
private theorem stB_coherent : DomainCoherent probB stB := by
  show stB.domains = stB.trail.foldl
      (fun acc e => domOfLit acc e.literal) probB.domains
  rfl

/-- The witness state is all-singleton. -/
private theorem stB_allSingleton : allSingleton stB = true := by
  rw [allSingleton, List.all_eq_true]
  intro d hd
  cases hd with
  | head => rfl
  | tail _ hd => cases hd

/-- The complete assignment is `[.bool true]`. -/
private theorem stB_singleton : singletonAssignment stB = some [Value.bool true] := rfl

/-- The leaf test FAILS at `a0 = [.bool true]` (it does not fit the
    mixed problem domain). -/
private theorem stB_leafFails :
    ¬ (fitsB probB [Value.bool true] &&
        probB.constraints.all (fun c => DomConstraint.satisfiedB c
          [Value.bool true])) := by
  rw [Bool.and_eq_true]
  intro ⟨hfit, _⟩
  rw [fitsB_iff] at hfit
  obtain ⟨_, hmem⟩ := hfit
  have h5 : Value.bool true ∈ probB.domains.getD 0 [] := hmem 0
    (Value.bool true) (by rfl)
  simp only [probB, List.getD_cons_zero, List.mem_cons, List.not_mem_nil,
    or_false] at h5
  rcases h5 with h5 | h5
  · exact Value.noConfusion h5
  · -- .bool true = .bool false is impossible
    cases h5

/-- OBSTRUCTION 3, machine-checked: WITHOUT the `TrailBoolPins`
    premise, the leaf-nogood entitlement (Reason.lean's
    `leafNogood_entailed`) is FALSE. The witness stB satisfies every
    other premise (coherence, all-singleton, the complete assignment,
    the failed leaf test, rootFacts vacuously — the trail's only
    entry is at level 1), `[.int 5]` is a ProblemSolution, yet the
    learned clause has no literal true there (the negated Boolean pin
    evaluates to `none` at an integer slot value). The `hboolpins`
    premise of `leafNogood_entailed` (and the `trailBoolPinsOk`
    invariant field feeding it) is therefore necessary, not
    decorative. -/
theorem boolPins_premise_necessary :
    ¬ ∀ (problem : Problem DomConstraint Unit)
        (st : State),
          DomainCoherent problem st →
          allSingleton st = true →
          singletonAssignment st = some [Value.bool true] →
          ¬ (fitsB problem [Value.bool true] &&
              problem.constraints.all (fun c =>
                DomConstraint.satisfiedB c [Value.bool true])) →
          RootFacts problem DomConstraint.SatisfiedBy st.trail →
          ∀ (a : Assignment),
            ProblemSolution problem DomConstraint.SatisfiedBy a →
            ∃ l ∈ (st.trail.filter fun e => e.level > 0).map
              (fun e => e.literal.negate.norm),
              l.eval a = some true := by
  intro hall
  have hroot : RootFacts probB DomConstraint.SatisfiedBy stB.trail := by
    intro e he hlev0
    exfalso
    have he1 : e = TrailEntry.mk
        (Literal.mk (Atom.boolEq 0 true) true) 1 none :=
      List.mem_singleton.mp he
    rw [he1] at hlev0
    exact absurd hlev0 (by simp)
  have := hall probB stB stB_coherent stB_allSingleton stB_singleton
    stB_leafFails hroot [Value.int 5] solB
  -- at the solution `[.int 5]`, the only leafNg literal (the negated
  -- normalized pin) evaluates to `none`, not `some true`
  rcases this with ⟨l, hl, hev⟩
  have hshape : (stB.trail.filter fun e => e.level > 0).map
      (fun e => e.literal.negate.norm)
      = [(Literal.mk (Atom.boolEq 0 true) false).norm] := rfl
  rw [hshape] at hl
  have hll : l = (Literal.mk (Atom.boolEq 0 true) false).norm :=
    List.mem_singleton.mp hl
  subst hll
  have hbool : (Literal.mk (Atom.boolEq 0 true) false).eval
      [Value.int 5] = none := by
    show (Atom.eval (Atom.boolEq 0 true) [Value.int 5]).map
      (fun value => if (Literal.mk (Atom.boolEq 0 true) false).positive
        then value else !value) = none
    unfold Atom.eval
    rfl
  rw [Literal.norm_eval (Literal.mk (Atom.boolEq 0 true) false)
      [Value.int 5], hbool] at hev
  exact absurd hev (by simp)

end LeanFzn.Solver.LCG

#print axioms LeanFzn.Solver.LCG.counterexample_opposing_fires
#print axioms LeanFzn.Solver.LCG.premises_inconsistent
#print axioms LeanFzn.Solver.LCG.hconfent_vacuous
#print axioms LeanFzn.Solver.LCG.boolPins_premise_necessary

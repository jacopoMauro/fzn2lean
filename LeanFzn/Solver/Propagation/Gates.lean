/- Shared finite-domain gates; no solver strategy dependency. -/
import LeanFzn.Solver.Propagation.CompactDomain
import LeanFzn.Solver.Propagation.Proofs.Theory
import LeanFzn.Solver.Propagation.Proofs.Reachability
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Reference
def fragmentOk (problem : Problem Constraint Objective) : Bool :=
  problem.domains.all (fun d => d.length == 1)

/-- Certified source gate: nonempty finite int/bool-viewed domains. Both SAT
and UNSAT are proved for multi-value models; singleton fragments are retained
for historical theorem compatibility. The concrete pruning kit enables the
proved propagators and learned clauses after this gate and compilation. -/
def gateOk (problem : Problem Constraint Objective) : Bool :=
  problem.domains.all (fun d =>
    d.length ≥ 1 && (Dom.enum d).all (fun v => Value.intView v ≠ none))

namespace Dom

/-- The structural int-view test `Dom.intViewableB` agrees with the
enumerating test on every representation (empty domains included: the
enumeration test is then vacuously true, and `intViewableB` is too on every
constructor whose values are integers or Booleans, while an empty `.general`
has a vacuous `all`).  This is the bridge `gateOkFast` and
`domPruningOkFastB` consume. -/
theorem enum_all_intView_eq (d : Dom) :
    (enum d).all (fun v => Value.intView v ≠ none) = intViewableB d := by
  cases d with
  | mk rep =>
    cases rep with
    | small isBool off bits =>
        cases isBool with
        | true =>
            show (smallBools bits).all (fun v => Value.intView v ≠ none) = true
            rw [List.all_eq_true]
            intro v hv
            obtain ⟨b, rfl⟩ := eq_bool_of_mem_smallBools hv
            simp [Value.intView]
        | false =>
            show (((smallInts off bits).map Value.int).all
              (fun v => Value.intView v ≠ none)) = true
            rw [List.all_eq_true]
            intro v hv
            obtain ⟨i, -, rfl⟩ := List.mem_map.mp hv
            simp [Value.intView]
    | holes lo hi hs =>
        show (((holesInts lo hi hs).map Value.int).all
          (fun v => Value.intView v ≠ none)) = true
        rw [List.all_eq_true]
        intro v hv
        obtain ⟨i, rfl⟩ := eq_int_of_mem_holes_enum hv
        simp [Value.intView]
    | general vs =>
        exact List.all_congr rfl (fun v => by
          rw [valueIntView_eq_value_intView]
          cases Value.intView v <;> rfl)

/-- The `!=`-shaped (BEq) form of `enum_all_intView_eq`, matching the
conjunct written in `domPruningOkB`. -/
theorem enum_all_intViewBeq_eq (d : Dom) :
    (enum d).all (fun v => v.intView != none) = intViewableB d := by
  rw [← enum_all_intView_eq]
  rw [List.all_congr rfl (fun v => ?_)]
  cases Value.intView v <;> rfl

end Dom

/-- Compiled twin of `gateOk`: identical statement, with the enumeration
scan replaced by the structural `Dom.intViewableB` view test. -/
def gateOkFast (problem : Problem Constraint Objective) : Bool :=
  problem.domains.all (fun d =>
    d.length ≥ 1 && Dom.intViewableB d)

theorem gateOkFast_eq (problem : Problem Constraint Objective) :
    gateOkFast problem = gateOk problem := by
  simp only [gateOkFast, gateOk, Dom.enum_all_intView_eq]

attribute [implemented_by gateOkFast] gateOk

/-- The executable check implies the fragment predicate. -/
theorem fragmentOk_iff {problem : Problem Constraint Objective} :
    fragmentOk problem = true ↔ PropFragment problem := by
  constructor
  · intro h
    intro d hd
    have hall : problem.domains.all (fun d => d.length == 1) = true := h
    rw [List.all_eq_true] at hall
    have := hall d hd
    simpa using this
  · intro h
    rw [fragmentOk, List.all_eq_true]
    intro d hd
    simpa using h d hd

/-- A problem whose domain values all have integer views is
    int-viewed. (The premise holds for every compiled problem by
    `domains_intViewed`; singleton-ness is not what carries it.) -/
theorem intViewed_of_fragment {problem : Problem Constraint Objective}
    (hint : ∀ d ∈ problem.domains, ∀ v ∈ d, Value.intView v ≠ none) :
    IntViewed problem := hint

/-- The widened gate implies the int-view invariant (the gate checks
    exactly the int/bool-viewed half, nonemptily). -/
theorem intViewed_of_gate {problem : Problem Constraint Objective}
    (hgate : gateOk problem = true) :
    IntViewed problem := by
  rw [gateOk, List.all_eq_true] at hgate
  intro d hd v hv
  have hpair := hgate d hd
  rw [Bool.and_eq_true, List.all_eq_true] at hpair
  exact of_decide_eq_true (hpair.2 v ((DomainLike.mem_iff d v).mp hv))

/-- Every gate-passing domain is nonempty (the SAT search space is
    nontrivial and the leaf test always has a complete assignment to
    reach). -/
theorem gate_nonempty {problem : Problem Constraint Objective}
    (hgate : gateOk problem = true) :
    ∀ d ∈ problem.domains, d.length ≥ 1 := by
  rw [gateOk, List.all_eq_true] at hgate
  intro d hd
  have hpair := hgate d hd
  rw [Bool.and_eq_true] at hpair
  exact of_decide_eq_true hpair.1

/-- The singleton-fragment check implies the widened gate (a
    singleton list is nonempty, and its single value's view was
    already derived for compiled problems by `domains_intViewed`;
    the gate re-checks it executably). -/
theorem gateOk_of_fragmentOk {problem : Problem Constraint Objective}
    (hint : ∀ d ∈ problem.domains, ∀ v ∈ d, Value.intView v ≠ none)
    (hfrag : fragmentOk problem = true) :
    gateOk problem = true := by
  rw [gateOk, List.all_eq_true]
  intro d hd
  have hlen : d.length = 1 := (fragmentOk_iff.mp hfrag) d hd
  -- the single value of a length-1 list: its head
  have hlen' : (Dom.enum d).length = 1 := by
    rwa [← Dom.length_eq_enum]
  obtain ⟨v2, hvenum⟩ : ∃ v2, Dom.enum d = [v2] := by
    match he : Dom.enum d with
    | [] => rw [he, List.length_nil] at hlen'; omega
    | [v2] => exact ⟨v2, rfl⟩
    | v2 :: v3 :: rest =>
        rw [he, List.length_cons, List.length_cons] at hlen'
        omega
  have hvint : Value.intView v2 ≠ none :=
    hint d hd v2 ((DomainLike.mem_iff d v2).mpr (by
      show v2 ∈ Dom.enum d
      rw [hvenum]; exact List.mem_cons_self))
  simp [hvenum, hvint, hlen]

/-- The empty clause database is trivially entitled. -/
theorem db0_nil {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    (hclauses : problem.clauses = []) :
    ∀ c ∈ problem.clauses,
      ∀ a, ProblemSolution problem constraintHolds a →
        ∃ l ∈ c, l.eval a = some true := by
  intro c hc
  rw [hclauses] at hc
  cases hc

end LeanFzn.Solver.Propagation

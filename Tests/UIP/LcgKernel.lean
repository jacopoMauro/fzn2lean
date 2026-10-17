/-
Purpose: execute the actual fuel-free LCG phase kernel on nonunit integer
SAT/UNSAT inputs and compare each result with independent exhaustive search.
Dependencies: LcgPhaseKernel supplies solve; LcgCompiledKit constructs the
semantic kit from executable problem gates; Enumerate supplies only Cartesian
assignment enumeration. This test leaf feeds LcgKernelRunner.
-/
import LeanFzn.Solver.UIP.Proofs.LcgPhaseKernel
import LeanFzn.Solver.UIP.Proofs.LcgCompiledKit
import LeanFzn.Solver.Core.Enumerate

namespace LcgKernelFixtures
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Solver.Chronological
open LeanFzn.Solver.UIP LeanFzn.Solver.UIP.C3b LeanFzn.Solver.UIP.LcgRunGood

def satProblem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
  { names := ["x", "y"], domains := [[.int 0, .int 1], [.int 0, .int 1]],
    constraints := [.neSlot 0 1], clauses := [], objective := () }

def unsatProblem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
  { names := ["x", "y", "z"],
    domains := [[.int 0, .int 1], [.int 0, .int 1], [.int 0, .int 1]],
    constraints := [.neSlot 0 1, .neSlot 0 2, .neSlot 1 2],
    clauses := [], objective := () }

def leaf (p : LeanFzn.Solver.Propagation.Problem DomConstraint Unit) : Assignment → Bool :=
  chronologicalLeaf p DomConstraint.satisfiedB

def rawProps (p : LeanFzn.Solver.Propagation.Problem DomConstraint Unit) : List Propagator :=
  p.constraints.filterMap propagatorOfProved

def props (p : LeanFzn.Solver.Propagation.Problem DomConstraint Unit) : List Propagator :=
  clampProps p.domains (rawProps p)

theorem satInput : CompiledInput (leaf satProblem) satProblem := ⟨rfl, rfl, rfl⟩
theorem unsatInput : CompiledInput (leaf unsatProblem) unsatProblem := ⟨rfl, rfl, rfl⟩

theorem satKit : LcgKit (leaf satProblem) satProblem.domains satProblem.clauses
    satProblem.constraints (rawProps satProblem) (props satProblem) :=
  LcgCompiledKit.kit_of_compiled_nil satInput rfl rfl

theorem unsatKit : LcgKit (leaf unsatProblem) unsatProblem.domains unsatProblem.clauses
    unsatProblem.constraints (rawProps unsatProblem) (props unsatProblem) :=
  LcgCompiledKit.kit_of_compiled_nil unsatInput rfl rfl

/-- Enumeration shares constraint semantics, but no scheduler search machinery. -/
def oracle (p : LeanFzn.Solver.Propagation.Problem DomConstraint Unit) : List Assignment :=
  (allAssigns p.domains).filter fun a => p.constraints.all (fun c => c.satisfiedB a)

theorem satOracleCount : (oracle satProblem).length = 2 := rfl
theorem unsatOracleCount : (oracle unsatProblem).length = 0 := rfl

def satResult : DriverResult (leaf satProblem) :=
  LcgPhaseKernel.solve satProblem.domains satProblem.clauses (props satProblem)
    (fun _ hc => by cases hc)

def unsatResult : DriverResult (leaf unsatProblem) :=
  LcgPhaseKernel.solve unsatProblem.domains unsatProblem.clauses (props unsatProblem)
    (fun _ hc => by cases hc)

/-- SAT must return a leaf-accepted member of the enumerated solution set;
UNSAT must agree with the empty enumerated set. No step bound is used. -/
def agrees (p : LeanFzn.Solver.Propagation.Problem DomConstraint Unit) (r : DriverResult (leaf p)) : Bool :=
  match r with
  | .sat a => leaf p a && (oracle p).contains a
  | .unsat => (oracle p).isEmpty


/-- PLAN L3: all-slot `minPair` (rides `propMin`/`propMax`), SAT. -/
def minPair_satProblem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
  { names := ["x", "y", "z"],
    domains := [[.int 0, .int 1, .int 2], [.int 0, .int 1, .int 2], [.int 2]],
    constraints := [.minPair (.slot 0) (.slot 1) (.slot 2)], clauses := [], objective := () }

theorem minPair_satInput : CompiledInput (leaf minPair_satProblem) minPair_satProblem := ⟨rfl, rfl, rfl⟩

theorem minPair_satKit : LcgKit (leaf minPair_satProblem) minPair_satProblem.domains minPair_satProblem.clauses
    minPair_satProblem.constraints (rawProps minPair_satProblem) (props minPair_satProblem) :=
  LcgCompiledKit.kit_of_compiled_nil minPair_satInput rfl rfl

def minPair_satResult : DriverResult (leaf minPair_satProblem) :=
  LcgPhaseKernel.solve minPair_satProblem.domains minPair_satProblem.clauses (props minPair_satProblem)
    (fun _ hc => by cases hc)

/-- PLAN L3: all-slot `minPair` (rides `propMin`/`propMax`), UNSAT. -/
def minPair_unsatProblem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
  { names := ["x", "y", "z"],
    domains := [[.int 0, .int 1, .int 2], [.int 0, .int 1, .int 2], [.int 3]],
    constraints := [.minPair (.slot 0) (.slot 1) (.slot 2)], clauses := [], objective := () }

theorem minPair_unsatInput : CompiledInput (leaf minPair_unsatProblem) minPair_unsatProblem := ⟨rfl, rfl, rfl⟩

theorem minPair_unsatKit : LcgKit (leaf minPair_unsatProblem) minPair_unsatProblem.domains minPair_unsatProblem.clauses
    minPair_unsatProblem.constraints (rawProps minPair_unsatProblem) (props minPair_unsatProblem) :=
  LcgCompiledKit.kit_of_compiled_nil minPair_unsatInput rfl rfl

def minPair_unsatResult : DriverResult (leaf minPair_unsatProblem) :=
  LcgPhaseKernel.solve minPair_unsatProblem.domains minPair_unsatProblem.clauses (props minPair_unsatProblem)
    (fun _ hc => by cases hc)

/-- PLAN L3: all-slot `maxPair` (rides `propMin`/`propMax`), SAT. -/
def maxPair_satProblem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
  { names := ["x", "y", "z"],
    domains := [[.int 0, .int 1, .int 2], [.int 0, .int 1, .int 2], [.int 0]],
    constraints := [.maxPair (.slot 0) (.slot 1) (.slot 2)], clauses := [], objective := () }

theorem maxPair_satInput : CompiledInput (leaf maxPair_satProblem) maxPair_satProblem := ⟨rfl, rfl, rfl⟩

theorem maxPair_satKit : LcgKit (leaf maxPair_satProblem) maxPair_satProblem.domains maxPair_satProblem.clauses
    maxPair_satProblem.constraints (rawProps maxPair_satProblem) (props maxPair_satProblem) :=
  LcgCompiledKit.kit_of_compiled_nil maxPair_satInput rfl rfl

def maxPair_satResult : DriverResult (leaf maxPair_satProblem) :=
  LcgPhaseKernel.solve maxPair_satProblem.domains maxPair_satProblem.clauses (props maxPair_satProblem)
    (fun _ hc => by cases hc)

/-- PLAN L3: all-slot `maxPair` (rides `propMin`/`propMax`), UNSAT. -/
def maxPair_unsatProblem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
  { names := ["x", "y", "z"],
    domains := [[.int 0, .int 1, .int 2], [.int 0, .int 1, .int 2], [.int 3]],
    constraints := [.maxPair (.slot 0) (.slot 1) (.slot 2)], clauses := [], objective := () }

theorem maxPair_unsatInput : CompiledInput (leaf maxPair_unsatProblem) maxPair_unsatProblem := ⟨rfl, rfl, rfl⟩

theorem maxPair_unsatKit : LcgKit (leaf maxPair_unsatProblem) maxPair_unsatProblem.domains maxPair_unsatProblem.clauses
    maxPair_unsatProblem.constraints (rawProps maxPair_unsatProblem) (props maxPair_unsatProblem) :=
  LcgCompiledKit.kit_of_compiled_nil maxPair_unsatInput rfl rfl

def maxPair_unsatResult : DriverResult (leaf maxPair_unsatProblem) :=
  LcgPhaseKernel.solve maxPair_unsatProblem.domains maxPair_unsatProblem.clauses (props maxPair_unsatProblem)
    (fun _ hc => by cases hc)

def main : IO UInt32 := do
  let satRun ← IO.lazyPure fun _ => satResult
  let unsatRun ← IO.lazyPure fun _ => unsatResult
  let satOK := match satRun with | .sat _ => agrees satProblem satRun | .unsat => false
  let unsatOK := match unsatRun with | .unsat => agrees unsatProblem unsatRun | .sat _ => false
  IO.println s!"fuel-free 2-color 2-clique SAT: {satOK}; oracle solutions=2"
  IO.println s!"fuel-free 2-color 3-clique UNSAT: {unsatOK}; oracle solutions=0"
  let minPair_satRun ← IO.lazyPure fun _ => minPair_satResult
  let minPair_satOK := match minPair_satRun with | .sat _ => agrees minPair_satProblem minPair_satRun | .unsat => false
  IO.println s!"fuel-free all-slot minPair SAT: {minPair_satOK}"
  let minPair_unsatRun ← IO.lazyPure fun _ => minPair_unsatResult
  let minPair_unsatOK := match minPair_unsatRun with | .unsat => agrees minPair_unsatProblem minPair_unsatRun | .sat _ => false
  IO.println s!"fuel-free all-slot minPair UNSAT: {minPair_unsatOK}"
  let maxPair_satRun ← IO.lazyPure fun _ => maxPair_satResult
  let maxPair_satOK := match maxPair_satRun with | .sat _ => agrees maxPair_satProblem maxPair_satRun | .unsat => false
  IO.println s!"fuel-free all-slot maxPair SAT: {maxPair_satOK}"
  let maxPair_unsatRun ← IO.lazyPure fun _ => maxPair_unsatResult
  let maxPair_unsatOK := match maxPair_unsatRun with | .unsat => agrees maxPair_unsatProblem maxPair_unsatRun | .sat _ => false
  IO.println s!"fuel-free all-slot maxPair UNSAT: {maxPair_unsatOK}"
  return if satOK && unsatOK && minPair_satOK && minPair_unsatOK && maxPair_satOK && maxPair_unsatOK then 0 else 1

end LcgKernelFixtures

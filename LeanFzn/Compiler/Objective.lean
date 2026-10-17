/-
File: LeanFzn/Compiler/Objective.lean

Purpose:
  The optimization front end of the certified compiler (PLAN.md task O1).
  `compileModelOpt` accepts `solve minimize x` / `solve maximize x` where
  `x` is a declared, initializer-free `var int` scalar.  It compiles the
  SATISFY part of the model exactly as `compileModelFull` does (the solve
  item is replaced by `satisfy`) and records the objective as an
  `ObjectiveSpec`: the objective variable's slot index in the compiled
  problem and the direction.  The returned problem's `source` is the
  ORIGINAL optimization model, so its stores are stores of the original.

  `ObjectiveSpec.improveBound` is the bound constraint a branch-and-bound
  driver adds to the compiled problem to ask for a strictly better
  objective: `leConstHi slot (v-1)` (minimize) / `leConstLo slot (v+1)`
  (maximize), an existing `DomConstraint`.

  Correctness theorems are in `Proofs/Objective`.

Dependencies:
  - LeanFzn.Compiler.Normalize: `compileModelFull`.
-/

import LeanFzn.Compiler.Normalize

namespace LeanFzn.Compiler
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Semantics LeanFzn.Semantics.Evaluation

/-- Optimization direction. -/
inductive OptDir where
  | minimize
  | maximize
  deriving Repr, DecidableEq

/-- The objective of a compiled optimization model: the slot of the
    objective variable, the direction, and the source variable. -/
structure ObjectiveSpec where
  slot : Nat
  dir : OptDir
  var : Ident

/-- The direction and variable of an optimize item whose objective is a
    variable name. -/
def objectiveOf : SolveItem → Option (OptDir × Ident)
  | .minimize _ (.ident x) => some (.minimize, x)
  | .maximize _ (.ident x) => some (.maximize, x)
  | _ => none

/-- The satisfy part of a model: the solve item replaced by `satisfy`. -/
def satisfyPart (m : Model) : Model := { m with solve := .satisfy [] }

/-- `x` is declared as an initializer-free scalar `var int`. -/
def objVarOkB (m : Model) (x : Ident) : Bool :=
  m.variables.any (fun d => match d with
    | .basic ty n _ none => n.name == x.name && decide (ty.base = .int)
    | _ => false)

/-- The improving bound for objective value `v`: strictly below `v`
    (minimize) or strictly above `v` (maximize). -/
def ObjectiveSpec.improveBound (spec : ObjectiveSpec) (v : Int) : DomConstraint :=
  match spec.dir with
  | .minimize => .leConstHi spec.slot (v - 1)
  | .maximize => .leConstLo spec.slot (v + 1)

/-- The compiled problem with one more constraint. -/
def CompiledProblem.addConstraint (p : CompiledProblem DomConstraint)
    (c : DomConstraint) : CompiledProblem DomConstraint :=
  { p with constraints := p.constraints ++ [c] }

/-- Compile an optimization model: the satisfy part via
    `compileModelFull`, the objective as a slot + direction. -/
def compileModelOpt (m : Model) :
    Except String (CompiledProblem DomConstraint × ObjectiveSpec) :=
  match objectiveOf m.solve with
  | none => .error "not an optimization model with a variable objective"
  | some (dir, x) =>
    if objVarOkB m x then
      match compileModelFull (satisfyPart m) with
      | .error e => .error e
      | .ok p =>
        match nameIndex p.names x.name with
        | none => .error "objective variable has no search slot"
        | some i => .ok ({ p with source := m }, ⟨i, dir, x⟩)
    else .error "objective is not a declared var int"

end LeanFzn.Compiler

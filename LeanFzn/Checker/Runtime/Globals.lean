/-
Purpose: Executable globals checker definitions and required local lemmas.
Dependencies: Parser, semantics and earlier Checker.Runtime modules.
DAG: Checker.Runtime.Globals -> Checker.Proofs.Globals -> compatibility import Checker.Globals.
-/
import LeanFzn.Semantics.Globals
import LeanFzn.Checker.Runtime.Solution
open LeanFzn.Semantics LeanFzn.Parser


namespace LeanFzn.Checker.Globals


open LeanFzn LeanFzn.Semantics LeanFzn.Semantics.Globals

/-! ## The full solution checker -/

namespace Internal

/-- Evaluate a constraint's arguments and check the predicate under
    the combined twin (executable counterpart of
    `ConstraintItem.Holds fullInterp`). -/
def constraintHoldsFullB (store : Store) (c : ConstraintItem) : Bool :=
  match c.args.mapM (Expr.eval store) with
  | some args => fullInterpB c.name args
  | none => false

end Internal

open Internal

/-- The top-level solution checker for the full fragment: parse the
    solution string, build the candidate store, and check every
    dynamic condition of `Satisfies fullSig fullInterp` — variable
    domains, initializers, and constraints (both standard and global)
    — with executable Boolean twins. -/
def checkSolutionFull (m : Model) (sol : String) : Bool :=
  match LeanFzn.Checker.Solution.parseSolution
      (LeanFzn.Checker.Solution.stripSeparators sol) with
  | .error _ => false
  | .ok es =>
      let box := LeanFzn.Checker.Solution.completedBox m es
      LeanFzn.Checker.Solution.allAssignedB box.f m.variables &&
      LeanFzn.Checker.Solution.varDeclsOkB box.f m.variables &&
      m.constraints.all (fun c => constraintHoldsFullB box.f c)

/-! ### The correctness theorem

The checker decides the *dynamic* conditions of
`Satisfies fullSig fullInterp`: `checkSolutionFull m sol = true`
exactly when the solution string parses and the candidate store it
describes satisfies every variable-domain, initializer, and constraint
condition.  Static well-formedness (`WellFormed fullSig m`) is a
*precondition* of the theorem (`hwf`), not re-decided by the checker;
combining `hwf` with the right-hand side yields `Satisfies`
(`Satisfies` is `WellFormed ∧ SatisfiesDyn`, see `FznSemantics.lean`). -/

namespace Internal

/-- Evaluate a constraint's arguments and check the predicate with
    the hash-dispatched twin (fast counterpart of
    `constraintHoldsFullB`). -/
def constraintHoldsFullFastB (store : Store) (c : ConstraintItem) : Bool :=
  match c.args.mapM (Expr.eval store) with
  | some args => preparedInterpB c.name args
  | none => false

end Internal

/-- **The fast dynamic checker.**  Same structure as
    `checkSolutionFull`, with the hash-dispatched predicate twin: each
    constraint call costs one map lookup instead of a walk over the
    218-name membership chain. -/
def checkSolutionFullFast (m : Model) (sol : String) : Bool :=
  match LeanFzn.Checker.Solution.parseSolution
      (LeanFzn.Checker.Solution.stripSeparators sol) with
  | .error _ => false
  | .ok es =>
      let box := LeanFzn.Checker.Solution.completedBox m es
      LeanFzn.Checker.Solution.allAssignedB box.f m.variables &&
      LeanFzn.Checker.Solution.varDeclsOkB box.f m.variables &&
      m.constraints.all (fun c => constraintHoldsFullFastB box.f c)

end LeanFzn.Checker.Globals

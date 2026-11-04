/-
File: LeanFzn/Integration/Proofs/CompiledEntry.lean

Purpose: the `LeanFzn.Integration.toLCG` instance of the F1 supported-input assembly.
`LeanFzn.Integration.toLCG` lives in the CLI module (`LeanFzn/Compiler/Cli.lean`), which is
not in `Proofs/CompiledShape.lean`'s import cone — so the wrapper lives
here, where both cones are available:

  `supportedInput_of_compiled_toLCG` — every `SupportedInput` field of the
  compiled CLI problem (`hdoms := rfl`: `toLCG` copies the domains
  verbatim; clause base empty), from successful compilation + the
  executable gates + the unit fragment gate.

NO `sorry`, NO custom axiom. Registration owes the umbrella import line
`LeanFzn.Integration.Proofs.CompiledEntry` in `LeanFzn.Solver/LeanFzn.Solver.UIP.lean`.
-/

import LeanFzn.Legacy.Integration.Solve.Certified
import LeanFzn.Legacy.Integration.Proofs.CompiledShape
open LeanFzn.Compiler.Domains
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler LeanFzn.Integration


namespace LeanFzn.Integration
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-- The compiled-CLI instance (`LeanFzn.Integration.toLCG`): the LCG problem's domains
are the compiled problem's definitionally, and its clause base is empty. -/
theorem supportedInput_of_compiled_toLCG {leaf : Assignment → Bool}
    {m : Model} {compiled : LeanFzn.Compiler.CompiledProblem DomConstraint}
    (hc : LeanFzn.Compiler.compileModel m = .ok compiled)
    (hin : CompiledInput leaf (LeanFzn.Integration.toLCG compiled))
    (hSupp : ∀ dc ∈ (LeanFzn.Integration.toLCG compiled).constraints,
      unitFamilyB dc = true) :
    SupportedInput leaf (LeanFzn.Integration.toLCG compiled).domains
      (LeanFzn.Integration.toLCG compiled).clauses
      ((LeanFzn.Integration.toLCG compiled).constraints.filterMap propagatorOfProved) :=
  supportedInput_of_compiled (problem := LeanFzn.Integration.toLCG compiled) hc rfl hin hSupp

end LeanFzn.Integration

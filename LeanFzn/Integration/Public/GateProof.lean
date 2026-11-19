/-
Purpose: The emission lemma for gated models: a `GatedModel`'s printable-name
  fact is exactly the premise of the certified emitter round trip, so every
  reported solution text of a gated satisfying store parses into entries that
  name the declared variables with their values.
Dependencies: the gate (`Public.Gate`) and the report proofs.
DAG: Public.Gate + Report.Proofs -> GateProof -> Report callers.
-/
import LeanFzn.Integration.Public.Gate
import LeanFzn.Integration.Report.Proofs

namespace LeanFzn.Core
open LeanFzn LeanFzn.Semantics LeanFzn.Integration
open LeanFzn.Checker.Solution LeanFzn.Parser.Lexer
open LeanFzn.Semantics.Globals (fullSig fullInterp)
open LeanFzn.Integration.Report

/-- A gated model's printable-name check feeds the emitter: every satisfying
store of a gated model has a solution text whose parsed entries name the
declared variables with their values. -/
theorem GatedModel.printable_entries {g : GatedModel} {store : Store}
    (hs : Satisfies fullSig fullInterp g.model store) :
    ∃ es,
      LeanFzn.Checker.Solution.parseSolution
          (LeanFzn.Checker.Solution.stripSeparators
            (LeanFzn.Integration.emitCertifiedSolution g.model store)) = .ok es ∧
      es.map LeanFzn.Checker.Solution.Entry.name =
        (LeanFzn.Integration.Report.certifiedEntryPairs g.model store).map Prod.fst ∧
      (∀ e ∈ es, ∃ d ∈ g.model.variables, ∃ v,
        e.name = d.name.name ∧ store d.name = some v ∧
        LeanFzn.Integration.SolValueMatches e.value v) :=
  have hp : LeanFzn.Integration.Report.outputNamesPrintableB g.model = true :=
    g.printables
  solution_entries_bind_of_gate hs hp

end LeanFzn.Core

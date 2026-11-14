/-
Purpose: Close the solver-to-checker text boundary: actual certified emission
has independent solution syntax, parses completely, and preserves every value.
Dependencies: TokenRoundTrip supplies syntax/value derivations, LexerLayout
verifies rendered text, and SolutionParser/SolutionSeparators connect the real
parser and status-marker handling to those independent derivations.
DAG: emitter + lexical/syntactic proofs -> Emit.RoundTrip; runtime emission does
not import this proof module.
-/
import LeanFzn.Integration.Emit.TokenRoundTrip
import LeanFzn.Checker.Proofs.SolutionParser
import LeanFzn.Checker.Proofs.SolutionSeparators
import LeanFzn.Parser.Proofs.LexerRender
import LeanFzn.Parser.Proofs.LexerLayout

namespace LeanFzn.Integration
open LeanFzn LeanFzn.Semantics LeanFzn.Checker.Solution LeanFzn.Parser.Lexer

/-- Stripping the actual emitter's status marker preserves every assignment,
and gives exactly the canonically rendered declaration token chunks. -/
theorem strip_emitCertifiedSolution (m : Model) (store : Store)
    (hn : ∀ d ∈ m.variables, PrintableSolutionName d.name.name)
    (h : ∀ d ∈ m.variables, ∃ v, store d.name = some v ∧ DeclValueFits d v) :
    stripSeparators (emitCertifiedSolution m store) =
      String.intercalate "\n"
        ((emittedStoreTokenLines m.variables store).map renderSolutionTokens) := by
  rw [emitCertifiedSolution, certifiedEntries_eq_render]
  apply stripSeparators_terminated
  · intro line hl
    obtain ⟨ts, hts, rfl⟩ := List.mem_map.mp hl
    exact renderSolutionTokens_noNewline ts
      (printable_emittedStoreTokenLines m.variables store hn h ts hts)
  · intro line hl
    obtain ⟨ts, hts, rfl⟩ := List.mem_map.mp hl
    obtain ⟨d, hd, hlookup⟩ := List.mem_filterMap.mp hts
    obtain ⟨v, hv, _⟩ := h d hd
    simp only [hv, Option.map_some, Option.some.injEq] at hlookup
    subst ts
    exact renderSolutionTokens_ident_notStatus (hn d hd)

/-- The actual declaration-aware solver output has independently specified
solution syntax and exactly the normalized values emitted for its typed store. -/
theorem emitCertifiedSolution_grammar (m : Model) (store : Store)
    (hn : ∀ d ∈ m.variables, PrintableSolutionName d.name.name)
    (h : ∀ d ∈ m.variables, ∃ v, store d.name = some v ∧ DeclValueFits d v) :
    SolutionGrammar (stripSeparators (emitCertifiedSolution m store))
      (emittedStoreEntries m.variables store) := by
  refine ⟨(emittedStoreTokenLines m.variables store).flatten.toArray, ?_, ?_⟩
  · rw [strip_emitCertifiedSolution m store hn h]
    exact tokenize_renderSolutionTokenLines _
      (printable_emittedStoreTokenLines m.variables store hn h)
  · simpa only [List.toList_toArray] using
      emittedStoreTokens_grammar m.variables store h

/-- Full string-level solver/checker round trip. This is about the real
`emitCertifiedSolution`, not a token-only surrogate or a parser-success
precondition. Legal names and the ordinary store typing contract suffice. -/
theorem parse_emitCertifiedSolution (m : Model) (store : Store)
    (hn : ∀ d ∈ m.variables, PrintableSolutionName d.name.name)
    (h : ∀ d ∈ m.variables, ∃ v, store d.name = some v ∧ DeclValueFits d v) :
    parseSolution (stripSeparators (emitCertifiedSolution m store)) =
      .ok (emittedStoreEntries m.variables store) := by
  exact parseSolution_eq_ok_iff_grammar.mpr (emitCertifiedSolution_grammar m store hn h)

/-- A satisfying store supplies the output typing contract automatically.
Identifier legality is separate because static model semantics admits raw
`String` names; it is not a hypothesis about the parser's behavior. -/
theorem parse_emitCertifiedSolution_of_satisfies
    {sig : SigEnv} {pred : PredicateInterpretation} {m : Model} {store : Store}
    (hs : Satisfies sig pred m store)
    (hn : ∀ d ∈ m.variables, PrintableSolutionName d.name.name) :
    parseSolution (stripSeparators (emitCertifiedSolution m store)) =
      .ok (emittedStoreEntries m.variables store) := by
  exact parse_emitCertifiedSolution m store hn
    (fun _ hd => declValueFits_of_satisfiesDyn hs.2 hd)

/-- The complete semantic round trip: all and only the declared names are
read, in order, every decoded assignment denotes its original store value,
and every declared variable is represented. Set equality is extensional and
array equality compares corresponding scalar values in their original order. -/
theorem emitCertifiedSolution_roundTrip
    {sig : SigEnv} {pred : PredicateInterpretation} {m : Model} {store : Store}
    (hs : Satisfies sig pred m store)
    (hn : ∀ d ∈ m.variables, PrintableSolutionName d.name.name) :
    ∃ es,
      parseSolution (stripSeparators (emitCertifiedSolution m store)) = .ok es ∧
      es.map Entry.name = m.variables.map (fun d => d.name.name) ∧
      (∀ e ∈ es, ∃ d ∈ m.variables, ∃ v,
        e.name = d.name.name ∧ store d.name = some v ∧ SolValueMatches e.value v) ∧
      (∀ d ∈ m.variables, ∃ v, store d.name = some v ∧
        emittedDeclEntry d v ∈ es ∧ SolValueMatches (emittedDeclEntry d v).value v) := by
  have hfit : ∀ d ∈ m.variables, ∃ v, store d.name = some v ∧ DeclValueFits d v :=
    fun _ hd => declValueFits_of_satisfiesDyn hs.2 hd
  refine ⟨emittedStoreEntries m.variables store,
    parse_emitCertifiedSolution_of_satisfies hs hn,
    emittedStoreEntries_names m.variables store hfit,
    emittedStoreEntries_denote m.variables store hfit, ?_⟩
  intro d hd
  obtain ⟨v, hv, htyped⟩ := hfit d hd
  exact ⟨v, hv, emittedStoreEntries_covers hd hv, emittedDeclEntry_denotes htyped⟩

end LeanFzn.Integration

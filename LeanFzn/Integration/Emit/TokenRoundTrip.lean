/-
Purpose: Prove that declaration-aware solver emission derives the independent
solution grammar and preserves every emitted value, including arrays of sets.
Dependencies: Emit.Values relates typed stores to decoded literals;
Checker.SolutionGrammar specifies syntax without referring to the parser.
DAG: Emit.Values + SolutionGrammar -> Emit.TokenRoundTrip -> Emit.RoundTrip.
-/
import LeanFzn.Integration.Emit.Values
import LeanFzn.Parser.SolutionRender

namespace LeanFzn.Integration
open LeanFzn LeanFzn.Semantics LeanFzn.Checker.Solution LeanFzn.Parser.Lexer

@[simp] theorem commaSeparatedTokens_nil : commaSeparatedTokens [] = [] := rfl
@[simp] theorem commaSeparatedTokens_single (ts : List Token) :
    commaSeparatedTokens [ts] = ts := by simp [commaSeparatedTokens]

@[simp] theorem commaSeparatedTokens_cons_cons (ts us : List Token) (tss : List (List Token)) :
    commaSeparatedTokens (ts :: us :: tss) = ts ++ .comma :: commaSeparatedTokens (us :: tss) := by
  simp [commaSeparatedTokens]

/-- Canonical integer enumeration tokens derive every set, not just a final
array element. The suffix may itself start with the array comma. -/
theorem emittedSetTokens_grammar (xs : List Int) (rest : List Token) :
    GrSolSetTail
      (commaSeparatedTokens (xs.map (fun i => [.intLit i])) ++ .rBrace :: rest) xs rest := by
  induction xs with
  | nil => exact .empty
  | cons i xs ih =>
      cases xs with
      | nil => exact .singleton
      | cons j xs =>
          simpa [commaSeparatedTokens, List.append_assoc] using
            (GrSolSetTail.cons (i := i) ih)

/-- Canonical scalar tokens satisfy the literal grammar with any legal FOLLOW
punctuation, including the separator of a following array element. -/
theorem emittedScalarTokens_grammar {v : Value} (hv : ScalarSolutionValue v)
    (term : SolTerminator) (rest : List Token) :
    GrSolLiteral (scalarSolutionTokens v ++ term.token :: rest)
      (emittedScalarLiteral v) term rest := by
  cases v with
  | bool b => exact .bool
  | int i => exact .int
  | setOfInt s =>
      simpa [scalarSolutionTokens, emittedScalarLiteral, List.append_assoc] using
        (GrSolLiteral.set (emittedSetTokens_grammar s.sortElems (term.token :: rest)))
  | array _ => cases hv

private theorem emittedArrayItems_grammar (v : Value) (vs : List Value)
    (hv : ScalarSolutionValue v) (hvs : ∀ w ∈ vs, ScalarSolutionValue w)
    (rest : List Token) :
    GrSolArrayItems
      (commaSeparatedTokens ((v :: vs).map scalarSolutionTokens) ++ .rBrack :: rest)
      ((v :: vs).map emittedScalarLiteral) rest := by
  induction vs generalizing v with
  | nil =>
      simpa only [List.map_cons, List.map_nil, commaSeparatedTokens_single, SolTerminator.token] using
        GrSolArrayItems.last (emittedScalarTokens_grammar hv .rBrack rest)
  | cons w ws ih =>
      have hw := hvs w (by simp)
      have hws : ∀ x ∈ ws, ScalarSolutionValue x := fun x hx => hvs x (by simp [hx])
      have hs := emittedScalarTokens_grammar hv .comma
        (commaSeparatedTokens ((w :: ws).map scalarSolutionTokens) ++ .rBrack :: rest)
      have ht := ih w hw hws
      simpa only [List.map_cons, commaSeparatedTokens_cons_cons, List.append_assoc,
        List.cons_append, SolTerminator.token] using GrSolArrayItems.cons hs ht

/-- Every flat array of scalar values derives the array grammar. -/
theorem emittedArrayTokens_grammar (vs : List Value)
    (hvs : ∀ v ∈ vs, ScalarSolutionValue v) (rest : List Token) :
    GrSolArray
      (commaSeparatedTokens (vs.map scalarSolutionTokens) ++ .rBrack :: rest)
      (vs.map emittedScalarLiteral) rest := by
  cases vs with
  | nil => exact .empty
  | cons v vs =>
      exact .items (emittedArrayItems_grammar v vs (hvs v (by simp))
        (fun w hw => hvs w (by simp [hw])) rest)

/-- A typed declaration's emitted tokens derive precisely its decoded entry. -/
theorem emittedDeclEntryTokens_grammar {d : VarDeclItem} {v : Value}
    (h : DeclValueFits d v) (rest : List Token) :
    GrSolEntry (declEntryTokens d v ++ rest) (emittedDeclEntry d v) rest := by
  cases d with
  | basic ty n anns init =>
      simpa [declEntryTokens, declSolutionTokens, emittedDeclEntry, VarDeclItem.name,
        List.append_assoc, SolTerminator.token] using
        (GrSolEntry.scalar (x := n.name) (emittedScalarTokens_grammar
          (scalarSolutionValue_of_contains h) .semi rest))
  | array ty n anns es =>
      cases v with
      | bool _ | int _ | setOfInt _ => cases h
      | array vs =>
          have hs := emittedArrayTokens_grammar vs
            (fun w hw => scalarSolutionValue_of_contains (h.2 w hw))
            (.rParen :: .semi :: rest)
          simpa only [declEntryTokens, declSolutionTokens, emittedDeclEntry,
            VarDeclItem.name, List.append_assoc, List.cons_append, List.nil_append] using
            (GrSolEntry.array1d (x := n.name) (hi := (vs.length : Int)) hs (by simp))

private theorem printable_commaSeparatedTokens {tss : List (List Token)}
    (h : ∀ ts ∈ tss, ∀ t ∈ ts, PrintableSolutionToken t) :
    ∀ t ∈ commaSeparatedTokens tss, PrintableSolutionToken t := by
  induction tss with
  | nil => simp
  | cons ts tss ih =>
      cases tss with
      | nil => simpa using h ts (by simp)
      | cons us tss =>
          intro t ht
          simp only [commaSeparatedTokens_cons_cons, List.mem_append, List.mem_cons] at ht
          rcases ht with ht | rfl | ht
          · exact h ts (by simp) t ht
          · trivial
          · exact ih (fun xs hx => h xs (by simp [hx])) t ht

/-- Canonical scalar emission contains only printable tokens. -/
theorem printable_scalarSolutionTokens {v : Value} (hv : ScalarSolutionValue v) :
    ∀ t ∈ scalarSolutionTokens v, PrintableSolutionToken t := by
  cases v with
  | bool b => simp [scalarSolutionTokens, PrintableSolutionToken]
  | int i => simp [scalarSolutionTokens, PrintableSolutionToken]
  | setOfInt s =>
      intro t ht
      simp only [scalarSolutionTokens, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ht
      rcases ht with (rfl | ht) | rfl
      · trivial
      · apply printable_commaSeparatedTokens ?_ t ht
        intro ts hts t ht
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hts
        simp only [List.mem_singleton] at ht
        subst t
        trivial
      · trivial
  | array _ => cases hv

/-- The fixed constructor name `array1d` is an ordinary identifier. -/
theorem printable_array1d : PrintableSolutionName "array1d" := by
  refine ⟨⟨'a', ['r', 'r', 'a', 'y', '1', 'd'], rfl, by decide, ?_⟩, rfl, rfl⟩
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- A legal declaration name and a typed value make every emitted token
lexically printable. Neither premise refers to parsing or lexing the output. -/
theorem printable_declEntryTokens {d : VarDeclItem} {v : Value}
    (hn : PrintableSolutionName d.name.name) (hv : DeclValueFits d v) :
    ∀ t ∈ declEntryTokens d v, PrintableSolutionToken t := by
  have hval : ∀ t ∈ declSolutionTokens d v, PrintableSolutionToken t := by
    cases d with
    | basic ty n anns init =>
        exact printable_scalarSolutionTokens (scalarSolutionValue_of_contains hv)
    | array ty n anns es =>
        cases v with
        | bool _ | int _ | setOfInt _ => cases hv
        | array vs =>
            intro t ht
            simp only [declSolutionTokens, List.mem_append, List.mem_cons,
              List.not_mem_nil, or_false] at ht
            rcases ht with (ht | ht) | ht
            · rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
              · exact printable_array1d
              all_goals trivial
            · apply printable_commaSeparatedTokens ?_ t ht
              intro ts hts t ht
              obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hts
              exact printable_scalarSolutionTokens (scalarSolutionValue_of_contains (hv.2 w hw)) t ht
            · rcases ht with rfl | rfl
              all_goals trivial
  intro t ht
  simp only [declEntryTokens, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at ht
  rcases ht with ((rfl | rfl) | ht) | rfl
  · exact hn
  · trivial
  · exact hval t ht
  · trivial

/-- Decoded source-model entries, in the exact declaration order used by the
actual certified emitter. Missing lookups are ruled out by store typing. -/
def emittedStoreEntries (ds : List VarDeclItem) (store : Store) : List Entry :=
  ds.filterMap fun d => (store d.name).map (emittedDeclEntry d)

/-- The exact token chunks rendered by the certified emitter. -/
def emittedStoreTokenLines (ds : List VarDeclItem) (store : Store) : List (List Token) :=
  ds.filterMap fun d => (store d.name).map (declEntryTokens d)

/-- Typed source-model output derives the solution grammar with its actual
normalized values. No parser appears in the statement or proof. -/
theorem emittedStoreTokens_grammar (ds : List VarDeclItem) (store : Store)
    (h : ∀ d ∈ ds, ∃ v, store d.name = some v ∧ DeclValueFits d v) :
    GrSolution (emittedStoreTokenLines ds store).flatten (emittedStoreEntries ds store) := by
  induction ds with
  | nil => exact .nil
  | cons d ds ih =>
      obtain ⟨v, hv, hfit⟩ := h d (by simp)
      have ht := ih (fun e he => h e (by simp [he]))
      simpa only [emittedStoreTokenLines, emittedStoreEntries, List.filterMap_cons,
        hv, Option.map_some, List.flatten_cons] using
        GrSolution.cons (emittedDeclEntryTokens_grammar hfit _) ht

/-- Legal names and store typing imply that every token of actual emitted
output meets the lexical renderer's character-level preconditions. -/
theorem printable_emittedStoreTokenLines (ds : List VarDeclItem) (store : Store)
    (hn : ∀ d ∈ ds, PrintableSolutionName d.name.name)
    (h : ∀ d ∈ ds, ∃ v, store d.name = some v ∧ DeclValueFits d v) :
    ∀ ts ∈ emittedStoreTokenLines ds store, ∀ t ∈ ts, PrintableSolutionToken t := by
  intro ts hts
  obtain ⟨d, hd, hlookup⟩ := List.mem_filterMap.mp hts
  obtain ⟨v, hv, hfit⟩ := h d hd
  simp only [hv, Option.map_some, Option.some.injEq] at hlookup
  subst ts
  exact printable_declEntryTokens (hn d hd) hfit

/-- Every decoded emitted entry corresponds to a declaration lookup and has
exactly that declaration's semantic value, with array elements compared in order. -/
theorem emittedStoreEntries_denote (ds : List VarDeclItem) (store : Store)
    (h : ∀ d ∈ ds, ∃ v, store d.name = some v ∧ DeclValueFits d v) :
    ∀ e ∈ emittedStoreEntries ds store,
      ∃ d ∈ ds, ∃ v, e.name = d.name.name ∧ store d.name = some v ∧
        SolValueMatches e.value v := by
  intro e he
  obtain ⟨d, hd, he⟩ := List.mem_filterMap.mp he
  obtain ⟨v, hv, hfit⟩ := h d hd
  simp only [hv, Option.map_some, Option.some.injEq] at he
  subst e
  exact ⟨d, hd, v, rfl, hv, emittedDeclEntry_denotes hfit⟩

/-- The actual executable emitter renders exactly the token chunks specified
above; the implementation's missing-store failure contributes no logical entry. -/
theorem certifiedEntries_eq_render (m : Model) (store : Store) :
    certifiedEntries m store =
      (emittedStoreTokenLines m.variables store).map renderSolutionTokens := by
  simp only [certifiedEntries, emittedStoreTokenLines, emitDeclEntry, List.map_filterMap]
  congr 1
  funext d
  cases store d.name <;> rfl

/-- Every assigned declaration is present in the decoded emitted list; this
is the other direction of the value correspondence (no output is omitted). -/
theorem emittedStoreEntries_covers {ds : List VarDeclItem} {store : Store}
    {d : VarDeclItem} (hd : d ∈ ds) {v : Value} (hv : store d.name = some v) :
    emittedDeclEntry d v ∈ emittedStoreEntries ds store := by
  apply List.mem_filterMap.mpr
  exact ⟨d, hd, by simp [hv]⟩

/-- The emitted assignment names are exactly the declaration names, in order. -/
theorem emittedStoreEntries_names (ds : List VarDeclItem) (store : Store)
    (h : ∀ d ∈ ds, ∃ v, store d.name = some v ∧ DeclValueFits d v) :
    (emittedStoreEntries ds store).map Entry.name = ds.map (fun d => d.name.name) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
      obtain ⟨v, hv, _⟩ := h d (by simp)
      simp only [emittedStoreEntries, List.filterMap_cons, hv, Option.map_some,
        List.map_cons, emittedDeclEntry]
      exact congrArg (d.name.name :: ·) (ih (fun e he => h e (by simp [he])))

end LeanFzn.Integration

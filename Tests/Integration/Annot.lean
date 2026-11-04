/-
Purpose: executable regression for F2 annotation extraction: `seq_search`
group order, `input_order` offsets, unannotated fallback, per-slot value
orders, and the configuration dispatch.  Parsed fixtures only; no search.
Dependencies/DAG: Integration.Annot + Parser -> this test leaf.
-/
import LeanFzn.Legacy.Integration.Annot
import LeanFzn.Parser.Parser

namespace Tests.Integration.Annot
open LeanFzn LeanFzn.Semantics LeanFzn.Compiler LeanFzn.Integration LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation

private def parse (label src : String) : IO (Option Model) := do
  match Parser.parseModel src with
  | .ok m => pure (some m)
  | .error e =>
      IO.eprintln s!"FAIL {label}: parse {e}"
      pure none

private def expect (label : String) (b : Bool) : IO Bool := do
  if b then pure true
  else
    IO.eprintln s!"FAIL {label}"
    pure false

private def enumOf (d : Domain) : List LeanFzn.Semantics.Value :=
  Dom.enum d

def run : IO UInt32 := do
  let ok ← IO.mkRef true
  let check (b : Bool) : IO Unit := do
    if !b then ok.set false
  -- Two `seq_search` groups: the first is `input_order` on x, the second
  -- names y with `first_fail`/`indomain_median`.
  let src :=
    "var 1..3: x;\nvar 1..3: y;\nconstraint int_ne(x, y);\n" ++
    "solve :: seq_search([int_search([x], input_order, indomain_max, complete), " ++
    "int_search([y], first_fail, indomain_median, complete)]) satisfy;\n"
  match ← parse "seq" src with
  | none => pure ()
  | some m =>
      let names := ["x", "y"]
      let searches := annSearches m
      check (← expect "group-count" (decide (searches.length = 2)))
      check (← expect "group-vars" (decide (searches.map (·.vars) = [["x"], ["y"]])))
      check (← expect "group-input" (decide (searches.map (·.inputOrder) = [true, false])))
      check (← expect "group-order"
        (decide (searches.map (·.order) = [.max, .median])))
      let K := annBase names.length
      check (← expect "priority"
        (decide (annotPrio m names = [2 * K + 1, K])))
      check (← expect "orders"
        (decide (annotOrders m names = [.max, .median])))
      let dx : Domain := Dom.ofList [.int 1, .int 2, .int 3]
      check (← expect "max-order"
        (enumOf (sortDomAnnot .max dx) == [.int 3, .int 2, .int 1]))
      check (← expect "median-order"
        (enumOf (sortDomAnnot .median dx) == [.int 2, .int 1, .int 3]))
      check (← expect "min-order"
        (enumOf (sortDomAnnot .min dx) == [.int 1, .int 2, .int 3]))
      check (← expect "split-approx"
        (enumOf (sortDomAnnot .split dx) == enumOf (sortDomAnnot .min dx)))
      check (← expect "reverse-split-approx"
        (enumOf (sortDomAnnot .reverseSplit dx) ==
          enumOf (sortDomAnnot .max dx)))
  -- Unannotated slots keep score 0 (S1 fallback), and a bracketed list with
  -- one unannotated slot inserts only the named one.
  let src2 :=
    "var 0..2: a;\nvar 0..2: b;\nvar 0..2: c;\n" ++
    "solve :: int_search([a, c], input_order, indomain_min, complete) satisfy;\n"
  match ← parse "partial" src2 with
  | none => pure ()
  | some m =>
      let names := ["a", "b", "c"]
      let K := annBase names.length
      check (← expect "partial-priority"
        (decide (annotPrio m names = [K + 2, 0, K + 1])))
      check (← expect "partial-orders"
        (decide (annotOrders m names = [.min, .none, .min])))
  -- Well-formed configuration dispatch: the annotation config selects the
  -- annotation route, the default is definitionally the old optioned route.
  let src3 :=
    "var 1..2: x;\nsolve :: int_search([x], input_order, indomain_max, complete) satisfy;\n"
  match ← parse "dispatch" src3 with
  | none => pure ()
  | some m =>
      match compileModelFull m with
      | .error e => IO.eprintln s!"FAIL dispatch: compile {e}"; ok.set false
      | .ok p =>
          let c : SearchConfig := { var := .annot, val := .annot }
          -- Definitional equalities: the annotation configuration selects the
          -- annotated entry, and the default configuration is still exactly
          -- the pre-F2 optioned entry.
          let _dispatchAnnot : solveSearchConfig p c =
              solveCompiledAnnot p (annotPrio p.source p.names)
                (annotOrders p.source p.names) false := rfl
          let _dispatchDefault : solveSearchConfig p (default : SearchConfig) =
              LcgHeur.solveCompiledLcgHeurOpts (default : LcgHeur.HeurOpts) p := rfl
          check true
  -- F3: `atRank` rotation, phase orders from the previous incumbent, static
  -- per-slot orders, and the phase-aware dispatch.
  let src4 := "var 1..3: x;\nvar 1..3: y;\nsolve satisfy;\n"
  match ← parse "f3" src4 with
  | none => pure ()
  | some m =>
      match compileModelFull m with
      | .error e => IO.eprintln s!"FAIL f3: compile {e}"; ok.set false
      | .ok p =>
          let dx : Domain := Dom.ofList [.int 1, .int 2, .int 3]
          check (← expect "atRank-1"
            (enumOf (sortDomAnnot (.atRank 1) dx) ==
              [.int 2, .int 1, .int 3]))
          check (← expect "atRank-2"
            (enumOf (sortDomAnnot (.atRank 2) dx) ==
              [.int 3, .int 1, .int 2]))
          check (← expect "atRank-out"
            (enumOf (sortDomAnnot (.atRank 9) dx) == enumOf dx))
          check (← expect "phase-none" (decide (phaseOrders p none = [])))
          let sx := (annSlot? p.names "x").getD 0
          let sy := (annSlot? p.names "y").getD 0
          let po := phaseOrders p (some [.int 3, .int 1])
          check (← expect "phase-x"
            (decide (po.getD sx .none = .atRank 2)))
          check (← expect "phase-y"
            (decide (po.getD sy .none = .atRank 0)))
          check (← expect "config-min"
            (configOrders p { val := .min } none =
              List.replicate p.domains.length .min))
          check (← expect "config-max"
            (configOrders p { val := .max } none =
              List.replicate p.domains.length .max))
          check (← expect "config-median"
            (configOrders p { val := .median } none =
              List.replicate p.domains.length .median))
          check (← expect "config-incumbent"
            (configOrders p { val := .incumbent } (some [.int 2, .int 3]) =
              phaseOrders p (some [.int 2, .int 3])))
          check (← expect "config-annot"
            (configOrders p { val := .annot } none =
              annotOrders p.source p.names))
          -- Definitional dispatch: `--val=min` on the root problem is the
          -- annotation presentation route with the static min table.
          let _dispatchMin : solveSearchConfigWith p { val := .min } none =
              solveCompiledAnnot p [] (List.replicate p.domains.length .min)
                false := rfl
          check true
  if ← ok.get then
    IO.println "annotation extraction: OK"
    pure 0
  else
    IO.eprintln "annotation extraction: FAIL"
    pure 1

end Tests.Integration.Annot

def main : IO UInt32 := Tests.Integration.Annot.run

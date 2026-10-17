/-
File: Tests/E1/PhaseTiming.lean

Purpose (PLAN task E1, TEST-ONLY, UNCERTIFIED): a phase-level wall-time
breakdown of the PUBLIC solve route (`leanfzn solve`), which the E1 manifest
runner measures only end-to-end. Per input file it times, with `IO.monoMsNow`:

  parse    -- `Parser.parseModel` + `wellFormedFastB` (what the CLI does first)
  compile  -- `Compiler.compileModelFull` (the full array-aware front end)
  solve    -- `Integration.solveCompiledLcg` (same entry `solveCertified` calls)
  check    -- `emitCertifiedSolution` + the verified `checkModelSolutionFast`
              (only for SAT results; the CLI `check` subcommand does this)

and reports the route the public solver takes on the compiled problem:

  lcg      -- `lcgRouteGateMixed p = true`, so `solveCompiledLcgMixed` runs the
              fuel-free first-UIP kernel (`lcgRun`)
  chrono   -- the gate failed, so the proved chronological fallback runs

plus the gate components (`gateOk`, `domPruningOkB`,
`mixedKitGateFastB` — the P3b sort-based twin of `mixedKitGateB`, equal by
`mixedKitGateFastB_eq`, and the gate the route now evaluates), the
constraint-family histogram of the compiled problem with each family's
`lcgFamB` membership (families outside the gate keep the proved fallback arm)
and the sizes of the propagated/seed data (`props`, `seedClauses`).

This is measurement only: it calls the same functions the CLI calls and does
not modify `LeanFzn/**` runtime code. Run:

  lake env lean --run Tests/E1/PhaseTiming.lean FILE...
-/
import LeanFzn.Integration.CertifiedSolve
import LeanFzn.Integration.LcgOptimize
import LeanFzn.Checker.Check
open LeanFzn

namespace Tests.E1

/-- Human-readable constructor name of a compiled constraint family. -/
def dcName : LeanFzn.Solver.Propagation.DomainFiltering.DomConstraint → String
  | .eqSlot .. => "eqSlot"
  | .neSlot .. => "neSlot"
  | .leSlot .. => "leSlot"
  | .constEq .. => "constEq"
  | .plusSlot .. => "plusSlot"
  | .leConstHi .. => "leConstHi"
  | .leConstLo .. => "leConstLo"
  | .allDiff .. => "allDiff"
  | .timesSlot .. => "timesSlot"
  | .minSlot .. => "minSlot"
  | .maxSlot .. => "maxSlot"
  | .absSlot .. => "absSlot"
  | .linEq .. => "linEq"
  | .linLe .. => "linLe"
  | .linNe .. => "linNe"
  | .ltSlot .. => "ltSlot"
  | .ltConstHi .. => "ltConstHi"
  | .ltConstLo .. => "ltConstLo"
  | .boolNotSlot .. => "boolNotSlot"
  | .boolAndSlot .. => "boolAndSlot"
  | .boolOrSlot .. => "boolOrSlot"
  | .boolClauseSlot .. => "boolClauseSlot"
  | .arrayBoolAndSlot .. => "arrayBoolAndSlot"
  | .bool2intSlot .. => "bool2intSlot"
  | .boolEqSlot .. => "boolEqSlot"
  | .arrayIntElementSlot .. => "arrayIntElementSlot"
  | .arrayVarIntElementSlot .. => "arrayVarIntElementSlot"
  | .arrayVarBoolElementSlot .. => "arrayVarBoolElementSlot"
  -- Added by C5 (reified slot families); display names only.
  | .eqReifSlot .. => "eqReifSlot"
  | .leReifSlot .. => "leReifSlot"
  | .neReifSlot .. => "neReifSlot"
  | .linEqReif .. => "linEqReif"
  | .linLeReif .. => "linLeReif"
  | .linNeReif .. => "linNeReif"
  -- Added by C6 (general min/max/div/mod families); display names only.
  | .maxGen .. => "maxGen"
  | .minGen .. => "minGen"
  | .divGen .. => "divGen"
  | .modGen .. => "modGen"
  | .minPair .. => "minPair"
  | .maxPair .. => "maxPair"

/-- Insert or bump a (name, count) pair in a histogram (kept name-sorted). -/
def bump (h : List (String × Nat)) (name : String) : List (String × Nat) :=
  if h.any (·.1 == name) then
    h.map fun p => if p.1 == name then (p.1, p.2 + 1) else p
  else
    (h ++ [(name, 1)]).mergeSort (fun a b => a.1 ≤ b.1)

def renderHist (h : List (String × Nat)) : String :=
  "[" ++ ",".intercalate (h.map fun p => s!"{p.1}x{p.2}") ++ "]"

def run (args : List String) : IO UInt32 := do
  for path in args do
    let src ← IO.FS.readFile path
    let t0 ← IO.monoMsNow
    match LeanFzn.Parser.parseModel src with
    | .error e =>
        IO.println s!"PHASES file={path} parse=ERROR {e}"
    | .ok m =>
        let wf := LeanFzn.Checker.wellFormedFastB m
        let t1 ← IO.monoMsNow
        match m.solve with
        | .minimize _ _ | .maximize _ _ =>
            -- Optimization models: the CLI runs certified branch-and-bound
            -- (`runOptimize` -> `optimizeStream lcgSolver`), never
            -- `compileModelFull`, so time that route instead.
            match LeanFzn.Compiler.compileModelOpt m with
            | .error e =>
                IO.println s!"PHASES file={path} parseMs={t1 - t0} wf={wf} route=optimize compileOpt=ERROR {e}"
            | .ok (po, _) =>
                let t2 ← IO.monoMsNow
                let gOk := LeanFzn.Solver.Propagation.gateOk (LeanFzn.Integration.toLCG po)
                let dpOk := LeanFzn.Solver.Propagation.domPruningOkB (LeanFzn.Integration.toLCG po)
                let mkOk := LeanFzn.Solver.UIP.LcgMixedCompiledKit.mixedKitGateFastB (LeanFzn.Integration.toLCG po)
                let seen ← IO.mkRef ([] : List String)
                let t3 ← IO.monoMsNow
                let out ← LeanFzn.Integration.optimizeStream LeanFzn.Integration.lcgSolver m
                  (fun store => do
                    seen.modify (fun l => LeanFzn.Integration.emitCertifiedSolution m store :: l))
                let t4 ← IO.monoMsNow
                -- `seen` is in REVERSE emission order, so its head is the LAST
                -- (best) improving solution.
                let lastText ← seen.get
                let (verdict, nSols, complete, detail) :=
                  match out with
                  | .error e => ("opt_error", 0, false, e)
                  | .ok s =>
                      (if s.run.complete then (if s.run.sols.isEmpty then "unsat" else "optimal")
                         else "incomplete",
                       s.run.sols.length, s.run.complete,
                       s!"lastBound={s.run.lastBound} emitted={s.emitted.length}")
                let mut checkMs := 0
                let mut checkOut := "-"
                match lastText with
                | text :: _ =>
                    let t5 ← IO.monoMsNow
                    let outcome := LeanFzn.Checker.checkModelSolutionFast m text
                    let t6 ← IO.monoMsNow
                    checkMs := t6 - t5
                    checkOut :=
                      match outcome with
                      | .accepted => "accepted"
                      | .unsatisfied => "REJECTED"
                      | .malformedModel _ => "MALFORMED_MODEL"
                      | .unsupportedPredicate _ => "UNSUPPORTED_PREDICATE"
                      | .malformedSolution _ => "MALFORMED_SOLUTION"
                | [] => pure ()
                IO.println s!"PHASES file={path} \
verdict={verdict} route=optimize parseMs={t1 - t0} compileOptMs={t2 - t1} gateMs=0 solveMs={t4 - t3} checkMs={checkMs} check={checkOut} nSols={nSols} complete={complete}"
                IO.println s!"ROUTE file={path} wf={wf} gateOk={gOk} domPruningOkB={dpOk} \
mixedKitGateFastB={mkOk} route=optimize constraints={po.constraints.length} \
domains={po.domains.length} detail=\"{detail}\""
        | .satisfy _ =>
          match LeanFzn.Compiler.compileModelFull m with
          | .error e =>
              IO.println s!"PHASES file={path} parseMs={t1 - t0} wf={wf} compile=ERROR {e}"
          | .ok p =>
            let t2 ← IO.monoMsNow
            let lcgp := LeanFzn.Integration.toLCG p
            let gOk := LeanFzn.Solver.Propagation.gateOk lcgp
            let dpOk := LeanFzn.Solver.Propagation.domPruningOkB lcgp
            let mkOk := LeanFzn.Solver.UIP.LcgMixedCompiledKit.mixedKitGateFastB lcgp
            let routed := LeanFzn.Integration.lcgRouteGateMixed p
            let props := LeanFzn.Integration.lcgProps p
            let seeds := LeanFzn.Compiler.seedClauses p.constraints
            let hist := p.constraints.foldl (fun h dc => bump h (dcName dc)) []
            let famOff := p.constraints.filter fun dc =>
              LeanFzn.Solver.UIP.LcgFamilies.lcgFamB dc == false
            let t3 ← IO.monoMsNow
            let r := LeanFzn.Integration.solveCompiledLcg p
            let t4 ← IO.monoMsNow
            let verdict :=
              match r with
              | .sat _ => "sat"
              | .unsat => "unsat"
              | .unknown => "unknown"
            let mut checkMs := 0
            let mut checkOut := "-"
            match r with
            | .sat a =>
                let t5 ← IO.monoMsNow
                let text := LeanFzn.Integration.emitCertifiedSolution m (p.toStore a)
                let outcome := LeanFzn.Checker.checkModelSolutionFast m text
                let t6 ← IO.monoMsNow
                checkMs := t6 - t5
                checkOut :=
                  match outcome with
                  | .accepted => "accepted"
                  | .unsatisfied => "REJECTED"
                  | .malformedModel _ => "MALFORMED_MODEL"
                  | .unsupportedPredicate _ => "UNSUPPORTED_PREDICATE"
                  | .malformedSolution _ => "MALFORMED_SOLUTION"
            | _ => pure ()
            IO.println s!"PHASES file={path} \
verdict={verdict} route={if routed then "lcg" else "chrono"} \
parseMs={t1 - t0} compileMs={t2 - t1} gateMs={t3 - t2} solveMs={t4 - t3} checkMs={checkMs} check={checkOut}"
            IO.println s!"ROUTE file={path} wf={wf} gateOk={gOk} domPruningOkB={dpOk} \
mixedKitGateFastB={mkOk} route={if routed then "lcg" else "chrono"} \
constraints={p.constraints.length} props={props.length} seeds={seeds.length} \
domains={p.domains.length} famOffGate={renderHist (famOff.foldl (fun h dc => bump h (dcName dc)) [])}"
            IO.println s!"FAMILIES file={path} {renderHist hist}"
  return 0

end Tests.E1

/-- Entry point for `lake env lean --run`. -/
def main (args : List String) : IO UInt32 := Tests.E1.run args

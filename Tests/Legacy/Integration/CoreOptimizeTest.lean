/-
File: Tests/Legacy/Integration/CoreOptimizeTest.lean

N11a runtime tests for the Core certified optimizer.

Coverage:
1. `minimize` / `maximize` / parameter-array objective models with small
   finite objective domains: the incumbent sequence strictly improves and
   the final objective equals the exhaustive oracle, the LCG run and the
   chronological run.
2. An unsatisfiable optimization model: `optimizeCore` returns the empty
   complete run and no box assignment is accepted.
3. A source model whose root bound round makes Core give up
   (`int_max` + `int_lin_ne`): the raw `coreSolve` is `.gaveUp`, the kernel
   fallback `solveSearchConfigWith` is SAT, and the emitted first incumbent
   is exactly that fallback witness.
4. Every emitted incumbent is re-checked with `accepts p` and membership in
   `allAssigns p.domains`.
5. `coreSolver` field smoke checks: the gate is `true`, `solve` agrees with
   `solveSearchConfigCore`, `solveWith` agrees with `solveSearchConfigWith`
   on a Core give-up and with `solve` when Core decides.

Run with:
  lake env lean --run Tests/Legacy/Integration/CoreOptimizeTest.lean
-/
import LeanFzn.Legacy.Integration.CoreOptimize
import LeanFzn.Legacy.Integration.LcgOptimize
import LeanFzn.Parser.Parser

namespace Tests.Integration.CoreOptimize

open LeanFzn LeanFzn.Semantics LeanFzn.Compiler LeanFzn.Integration
open LeanFzn.Solver.Core LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Engine

/-- Passed/failed accounting. -/
structure St where
  passed : Nat := 0
  failed : Nat := 0

/-- Record one check. -/
def St.check (st : St) (label : String) (ok : Bool) : IO St := do
  if ok then
    pure { st with passed := st.passed + 1 }
  else
    IO.eprintln s!"FAIL {label}"
    pure { st with failed := st.failed + 1 }

/-- Brute-force optimum of the compiled problem (none if infeasible). -/
private def oracle (p : CompiledProblem DomConstraint) (spec : ObjectiveSpec) : Option Int :=
  let vals := ((allAssigns p.domains).filter (accepts p)).filterMap fun (a : List Value) =>
    match a[spec.slot]? with
    | some (Value.int i) => some i
    | _ => none
  match vals with
  | [] => none
  | v :: vs => some (match spec.dir with
    | .minimize => vs.foldl min v
    | .maximize => vs.foldl max v)

/-- Strict improvement along the emitted sequence. -/
private def improving (spec : ObjectiveSpec) : List (List Value × Int) → Bool
  | [] => true
  | [_] => true
  | s :: t :: rest => betterB spec.dir t.2 s.2 && improving spec (t :: rest)

/-- Every incumbent is accepted, is a box member, and reads the reported
    objective value. -/
private def solsOk (p : CompiledProblem DomConstraint) (spec : ObjectiveSpec)
    (run : OptRun) : Bool :=
  run.sols.all fun s => accepts p s.1 &&
    decide (s.1 ∈ allAssigns p.domains) &&
    s.1[spec.slot]? == some (.int s.2)

/-- The last reported objective value. -/
private def lastVal (run : OptRun) : Option Int :=
  run.sols.getLast?.map (fun s => s.2)

/-- A certified verdict is not a `fail`. -/
private def certNotFail : CertVerdict → Bool
  | .fail => false
  | _ => true

/-- Agree with the seam verdict (`fail` corresponds to `unknown`). -/
private def sameVerdict : CertVerdict → SearchResult → Bool
  | .sat a, .sat b => a == b
  | .unsat, .unsat => true
  | .fail, .unknown => true
  | _, _ => false

/-- Agreement of two certified verdicts. -/
private def sameCert : CertVerdict → CertVerdict → Bool
  | .sat a, .sat b => a == b
  | .unsat, .unsat => true
  | .fail, .fail => true
  | _, _ => false

/-- The root bound round is a raw Core give-up. -/
private def isGaveUp : CoreResult → Bool
  | .gaveUp => true
  | _ => false

/-- The source model has no accepted box assignment. -/
private def noAccepted (p : CompiledProblem DomConstraint) : Bool :=
  (allAssigns p.domains).all fun a => !accepts p a

/-- Common field checks on one compiled problem. -/
private def fieldChecks (st : St) (label : String)
    (p : CompiledProblem DomConstraint) : IO St := do
  let S : CertSolver := coreSolver ({} : SearchConfig)
  let st ← st.check s!"{label}: gate is true" (S.gate p)
  let st ← st.check s!"{label}: solve agrees with the seam"
    (sameVerdict (S.solve p) (solveSearchConfigCore p ({} : SearchConfig)))
  let st ← st.check s!"{label}: solve is total"
    (certNotFail (S.solve p))
  st.check s!"{label}: solveWith none agrees with the phase-aware seam"
    (sameVerdict (S.solveWith none p) (solveSearchConfigWith p ({} : SearchConfig) none))

/-- Run one optimum case end to end. -/
private def optCase (st : St) (label src : String) : IO St := do
  match Parser.parseModel src with
  | .error e =>
      IO.eprintln s!"FAIL {label}: parse {e}"
      return { st with failed := st.failed + 1 }
  | .ok m =>
      match compileModelOpt m with
      | .error e =>
          IO.eprintln s!"FAIL {label}: compile {e}"
          return { st with failed := st.failed + 1 }
      | .ok (p, spec) =>
          match optimizeCore m with
          | .error e =>
              IO.eprintln s!"FAIL {label}: optimizeCore {e}"
              return { st with failed := st.failed + 1 }
          | .ok (_, run) =>
              let lcg := optLoop (lcgSolver ({} : SearchConfig)) p spec none
              let chron := optLoop chronSolver p spec none
              let coreAgain := optLoop (coreSolver ({} : SearchConfig)) p spec none
              let opt := oracle p spec
              let last := lastVal run
              let prev := run.sols.head?.map (fun s => s.1)
              let S : CertSolver := coreSolver ({} : SearchConfig)
              let okRun := run.complete && !run.sols.isEmpty &&
                run.lastBound == last
              let okImp := improving spec run.sols
              let okLast := last == opt && last == lastVal lcg && last == lastVal chron
              let okAcc := solsOk p spec run
              let okSame := run.sols == coreAgain.sols &&
                run.complete == coreAgain.complete &&
                run.lastBound == coreAgain.lastBound
              let okPrev := match prev with
                | some a => sameCert (S.solveWith (some a) p) (S.solve p)
                | none => false
              let ok := okRun && okImp && okLast && okAcc && okSame && okPrev
              if !ok then
                IO.eprintln s!"FAIL {label}: complete={run.complete} sols={last} oracle={opt} lcg={lastVal lcg} chron={lastVal chron} improving={okImp} accepted={okAcc} sameLoop={okSame} solveWith={okPrev}"
              let st ← st.check s!"{label}: complete nonempty run" okRun
              let st ← st.check s!"{label}: strict improvement" okImp
              let st ← st.check s!"{label}: optimum agrees with oracle/LCG/chronological" okLast
              let st ← st.check s!"{label}: incumbents accepted and in allAssigns" okAcc
              let st ← st.check s!"{label}: optimizeCore equals optLoop coreSolver" okSame
              let st ← st.check s!"{label}: solveWith equals solve while Core decides" okPrev
              fieldChecks st label p

/-- The unsatisfiable optimization model. -/
private def unsatCase (st : St) : IO St := do
  let label := "unsat"
  let src := "var 0..3: x; var 0..3: y; constraint int_lin_le([1,1],[x,y],1); constraint int_lin_le([-1,-1],[x,y],-4); solve minimize x;"
  match Parser.parseModel src with
  | .error e =>
      IO.eprintln s!"FAIL {label}: parse {e}"
      return { st with failed := st.failed + 1 }
  | .ok m =>
      match compileModelOpt m with
      | .error e =>
          IO.eprintln s!"FAIL {label}: compile {e}"
          return { st with failed := st.failed + 1 }
      | .ok (p, spec) =>
          match optimizeCore m with
          | .error e =>
              IO.eprintln s!"FAIL {label}: optimizeCore {e}"
              return { st with failed := st.failed + 1 }
          | .ok (_, run) =>
              let lcg := optLoop (lcgSolver ({} : SearchConfig)) p spec none
              let chron := optLoop chronSolver p spec none
              let okRun := run.complete && run.sols.isEmpty && run.lastBound == none
              let okNo := noAccepted p && oracle p spec == none
              let okRef := lcg.complete && lcg.sols.isEmpty && chron.complete && chron.sols.isEmpty
              let okCert := match coreVerdict p ({} : SearchConfig) with
                | .unsat => true
                | _ => false
              let okSeam := match solveSearchConfigCore p ({} : SearchConfig) with
                | .unsat => true
                | _ => false
              let st ← st.check s!"{label}: complete empty run" okRun
              let st ← st.check s!"{label}: no accepted assignment" okNo
              let st ← st.check s!"{label}: LCG/chronological agree on infeasibility" okRef
              let st ← st.check s!"{label}: coreVerdict is UNSAT" okCert
              let st ← st.check s!"{label}: seam is UNSAT" okSeam
              fieldChecks st label p

/-- A source model where the root bound round makes Core give up: `int_max`
    plus `int_lin_ne` reaches a leaf whose fixed assignment violates the
    linear disequality, and the raw Core run makes no claim.  The kernel
    fallback decides the round and the emitted first incumbent is exactly
    its SAT witness. -/
private def fallbackCase (st : St) : IO St := do
  let label := "core-giveup-fallback"
  let src := "var 0..2: x; var 0..2: y; var 0..2: z; constraint int_max(x,y,z); constraint int_lin_ne([1,1],[y,z],0); solve maximize z;"
  match Parser.parseModel src with
  | .error e =>
      IO.eprintln s!"FAIL {label}: parse {e}"
      return { st with failed := st.failed + 1 }
  | .ok m =>
      match compileModelOpt m with
      | .error e =>
          IO.eprintln s!"FAIL {label}: compile {e}"
          return { st with failed := st.failed + 1 }
      | .ok (p, spec) =>
          match optimizeCore m with
          | .error e =>
              IO.eprintln s!"FAIL {label}: optimizeCore {e}"
              return { st with failed := st.failed + 1 }
          | .ok (_, run) =>
              let raw := coreSolve p ({} : SearchConfig) coreFuel
              let kernelRoot := solveSearchConfigWith p ({} : SearchConfig) none
              let lcg := optLoop (lcgSolver ({} : SearchConfig)) p spec none
              let chron := optLoop chronSolver p spec none
              let opt := oracle p spec
              let okGaveUp := isGaveUp raw
              let okFallback := match kernelRoot with
                | .sat _ => true
                | .unsat => true
                | .unknown => false
              let okRun := run.complete && !run.sols.isEmpty && improving spec run.sols &&
                solsOk p spec run && lastVal run == opt &&
                lastVal run == lastVal lcg && lastVal run == lastVal chron
              let okHead := match kernelRoot, run.sols.head? with
                | .sat a, some s => s.1 == a
                | _, _ => false
              let S : CertSolver := coreSolver ({} : SearchConfig)
              let okWith := match kernelRoot with
                | .sat a => sameVerdict (S.solveWith none p) (.sat a)
                | .unsat => sameVerdict (S.solveWith none p) .unsat
                | .unknown => false
              let st ← st.check s!"{label}: raw Core gave up on the root round" okGaveUp
              let st ← st.check s!"{label}: kernel fallback decides" okFallback
              let st ← st.check s!"{label}: complete, improving, accepted run with the shared optimum" okRun
              let st ← st.check s!"{label}: first incumbent is the fallback witness" okHead
              let st ← st.check s!"{label}: solveWith is the fallback verdict" okWith
              fieldChecks st label p

end Tests.Integration.CoreOptimize

open Tests.Integration.CoreOptimize in
def main : IO UInt32 := do
  let mut st : St := {}
  st ← optCase st "minimize"
    "var 0..4: x; var 0..4: y; constraint int_lin_le([-1,-1],[x,y],-4); solve minimize y;"
  st ← optCase st "maximize"
    "var 0..4: x; var 0..4: y; constraint int_lin_le([1,1],[x,y],4); solve maximize y;"
  st ← optCase st "parameter-array objective"
    "array [1..3] of int: co=[2,3,-1]; var 0..3: x; var 0..3: y; var 0..15: z; constraint int_lin_eq(co,[x,y,z],0); solve maximize z;"
  st ← unsatCase st
  st ← fallbackCase st
  if st.failed == 0 then
    IO.println s!"CoreOptimizeTest: {st.passed} checks passed"
    IO.println "CoreOptimizeTest: OK"
    return 0
  else
    IO.eprintln s!"CoreOptimizeTest: {st.failed} failed, {st.passed} passed"
    return 1

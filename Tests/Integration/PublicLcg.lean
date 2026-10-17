/-
Purpose: parsed-source regression for the public certified LCG route (mixed
int/bool kits) and fuel-free observations of its exact phase kernel. Source
SAT witnesses are checked by the verified checker; tiny UNSAT cases use
exhaustive enumeration. Boolean fixtures must reach the LCG route and (for
the UNSAT one) exhibit real conflict-driven work: analysis resolutions and a
completed learn/backjump/assert transition.
Dependencies: CertifiedSolve supplies the public entry; LcgPhaseObserved has
a proved verdict projection to the production kernel. No bounded driver.
DAG: public integration and observer -> this test leaf -> PublicLcgRunner.
-/
import LeanFzn.Integration.CertifiedSolve
import LeanFzn.Solver.UIP.Proofs.LcgPhaseObserved

namespace PublicLcgFixtures
open LeanFzn LeanFzn.Semantics LeanFzn.Compiler LeanFzn.Integration
open LeanFzn.Solver.Core LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP LeanFzn.Solver.UIP.C3b

def pigeon (n colors : Nat) (dummy : Bool := false) : String :=
  String.join ((List.range n).map fun i =>
    s!"var 1..{colors}: x{i};\n" ++
      (if dummy && i == 0 then "var 0..1: irrelevant;\n" else "")) ++
  String.join ((List.range n).flatMap fun i =>
    ((List.range n).filter (· > i)).map fun j =>
      s!"constraint int_ne(x{i}, x{j});\n") ++ "solve satisfy;\n"

/-- Pairwise `bool_not` over three Booleans: three pairwise-distinct values
out of two, i.e. UNSAT, with a genuine conflict-driven refutation on the LCG
route (analysis resolutions, one learned clause, one completed
learn/backjump/assert transition). -/
def boolPigeon3 : String :=
  "var bool: a;\nvar bool: b;\nvar bool: c;\n\
   constraint bool_not(a, b);\nconstraint bool_not(a, c);\n\
   constraint bool_not(b, c);\nsolve satisfy;\n"

def observe (p : CompiledProblem DomConstraint) :
    DriverResult (lcgLeaf p) × LcgPhaseObserved.Observations :=
  LcgPhaseObserved.solve (leaf := lcgLeaf p) p.domains
    (LeanFzn.Compiler.seedClauses p.constraints) (lcgProps p) (lcgSeedEntailed p)

theorem observe_eq (p : CompiledProblem DomConstraint) :
    (observe p).1 = lcgRun p :=
  (LcgPhaseObserved.solve_fst _ _ _ _).trans (lcgRun_eq_solve p).symm

/-- One fixture with its route and observation expectations: the public
route must take the LCG branch (`routed`), and when routed the observed
run must show at least `minRes` analysis resolutions and `minBack`
completed learn/backjump/assert transitions (0 = no expectation). -/
structure Fixture where
  name : String
  src : String
  sat : Bool
  routed : Bool
  minRes : Nat := 0
  minBack : Nat := 0

def runOne (f : Fixture) : IO (Bool × LcgPhaseObserved.Observations) := do
  match Parser.parseModel f.src with
  | .error e => IO.eprintln s!"{f.name}: parse {e}"; return (false, {})
  | .ok m =>
    match compileModelFull m with
    | .error e => IO.eprintln s!"{f.name}: compile {e}"; return (false, {})
    | .ok p =>
      let publicResult ← IO.lazyPure fun _ => solveCertified m
      let compiledResult ← IO.lazyPure fun _ => solveCompiledLcg p
      let sols := (allAssigns p.domains).filter (accepts p)
      let publicOK := match publicResult with
        | .sat store => f.sat &&
            (match Checker.checkModelSolutionFast m (emitCertifiedSolution m store) with
             | .accepted => true | _ => false)
        | .unsat => !f.sat && sols.isEmpty
        | _ => false
      let compiledOK := match compiledResult with
        | .sat a => f.sat && sols.contains a
        | .unsat => !f.sat && sols.isEmpty
        | .unknown => false
      let mut obs : LcgPhaseObserved.Observations := {}
      let mut same := true
      if lcgRouteGateMixed p then
        let observed ← IO.lazyPure fun _ => observe p
        obs := observed.2
        same := match observed.1, compiledResult with
          | .sat a, .sat b => a == b
          | .unsat, .unsat => true
          | _, _ => false
      let obsOK := obs.maxResolutions ≥ f.minRes && obs.events.backjumps ≥ f.minBack
      let ok := publicOK && compiledOK && same &&
        (lcgRouteGateMixed p == f.routed) && obsOK
      IO.println s!"{f.name}: ok={ok} LCG={lcgRouteGateMixed p} \
        need(res>={f.minRes},backjumps>={f.minBack}) observations={repr obs}"
      return (ok, obs)

def fixtures : List Fixture :=
  [ { name := "nonunit-sat", src := pigeon 2 2, sat := true, routed := true },
    { name := "nonunit-unsat", src := pigeon 3 2, sat := false, routed := true },
    { name := "learning-4-3", src := pigeon 4 3, sat := false, routed := true },
    { name := "skipped-4-3", src := pigeon 4 3 true, sat := false, routed := true },
    { name := "boolean-lcg",
      src := "var bool: x;\nvar bool: y;\nconstraint bool_not(x,y);\nsolve satisfy;\n",
      sat := true, routed := true },
    { name := "boolean-unsat-lcg", src := boolPigeon3, sat := false, routed := true,
      minRes := 2, minBack := 1 },
    -- PLAN L0c: the new `propCheck` families on the public LCG route.
    { name := "linne-sat",
      src := "var 1..3: x;\nconstraint int_lin_ne([1],[x],2);\n\
              constraint int_ne(x,3);\nsolve satisfy;\n",
      sat := true, routed := true },
    { name := "lereif-unsat",
      src := "var 0..3: x;\nvar 0..3: y;\nvar bool: b;\n\
              constraint int_le_reif(x, y, b);\n\
              constraint bool_clause([b], []);\n\
              constraint int_lt(y, x);\nsolve satisfy;\n",
      sat := false, routed := true },
    { name := "max-unsat",
      src := "var 0..3: x;\nvar 0..3: y;\nvar 0..3: z;\n\
              constraint int_max(x, y, z);\n\
              constraint int_ne(z, x);\nconstraint int_ne(z, y);\n\
              solve satisfy;\n",
      sat := false, routed := true } ]

def main : IO UInt32 := do
  let mut ok := true
  let mut maxRes := 0
  let mut nonunit := 0
  let mut skipped := 0
  let mut assertProp := 0
  let mut boolRes := 0
  let mut boolBack := 0
  for f in fixtures do
    let (pass, o) ← runOne f
    ok := ok && pass
    maxRes := max maxRes o.maxResolutions
    nonunit := nonunit + o.nonunitLearned
    skipped := skipped + o.skippedJumps
    assertProp := assertProp + o.assertionPropagation
    if f.name.startsWith "boolean" then
      boolRes := boolRes + o.maxResolutions
      boolBack := boolBack + o.events.backjumps
  IO.println s!"activation: maxResolutions={maxRes} nonunitLearned={nonunit} \
    skippedJumps={skipped} assertionPropagation={assertProp}"
  IO.println s!"boolean activation: resolutions={boolRes} backjumps={boolBack}"
  let activation := maxRes >= 2 && nonunit > 0 && skipped > 0 && assertProp > 0
  let boolActivation := boolRes >= 2 && boolBack >= 1
  return if ok && activation && boolActivation then 0 else 1

end PublicLcgFixtures

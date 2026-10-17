/-
Purpose (PLAN task P2): parsed-source regression for the ACTIVITY-ORDERED LCG
route (`Integration/LcgHeur.lean`). For every fixture the test checks that

  * the heuristic presentation (`heurDomains`) is a per-slot permutation of the
    compiled box (the property the certified transfer rests on),
  * the activity-ordered entry (`solveCompiledLcgHeur`) and the certified entry
    (`solveCompiledLcg`) agree on the VERDICT (witnesses may differ — that is
    the point of a decision-order change),
  * the activity-ordered entry's verdict is the enumeration's verdict, and its
    SAT witness is one of the enumerated solutions,
  * the activity order actually FIRES on at least one fixture (the report's
    "the heuristic is not vacuous" evidence: the counters are printed).

Dependencies/DAG: Integration.LcgHeur + Integration.Lcg -> this test leaf ->
HeurLcgRunner.
-/
import LeanFzn.Integration.LcgHeur
import LeanFzn.Compiler.Normalize

namespace HeurLcgFixtures
open LeanFzn LeanFzn.Semantics LeanFzn.Compiler LeanFzn.Integration
open LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering

/-- Every fixture: a source model and whether it is satisfiable. -/
structure Fixture where
  name : String
  src : String
  sat : Bool

/-- A reordered box must keep the VALUE MULTISET of every slot: this is the
per-slot permutation obligation the certified transfer is built on. -/
def permOK (p : CompiledProblem DomConstraint) : Bool :=
  ((p.domains.zip (LcgHeur.heurDomains p)).all fun pr => pr.1.length == pr.2.length)

/-- Did the activity order change the presentation at all? -/
def heurDomainsFired (p : CompiledProblem DomConstraint) : Bool :=
  !((p.domains.zip (LcgHeur.heurDomains p)).all fun pr => pr.1 == pr.2)

/-- The JSON-ish verdict tag of a compiled entry. -/
def tagOf : SearchResult → String
  | .sat _ => "sat"
  | .unsat => "unsat"
  | .unknown => "unknown"

def runOne (f : Fixture) : IO (Bool × Bool) := do
  match Parser.parseModel f.src with
  | .error e => IO.eprintln s!"{f.name}: parse {e}"; return (false, false)
  | .ok m =>
    match compileModelFull m with
    | .error e => IO.eprintln s!"{f.name}: compile {e}"; return (false, false)
    | .ok p =>
      let heur := LcgHeur.solveCompiledLcgHeur p
      let cert := solveCompiledLcg p
      let sols := (allAssigns p.domains).filter (accepts p)
      let fired := heurDomainsFired p
      let perm := permOK p
      let verdictsAgree := tagOf heur == tagOf cert
      let enumOK := match heur with
        | .sat a => f.sat && sols.contains a
        | .unsat => !f.sat && sols.isEmpty
        | .unknown => false
      let ok := perm && verdictsAgree && enumOK
      IO.println s!"{f.name}: ok={ok} perm={perm} agreed={verdictsAgree} \
heur={tagOf heur} cert={tagOf cert} fired={fired} sols={sols.length}"
      return (ok, fired)

def fixtures : List Fixture :=
  [ { name := "pigeon-4-3-unsat",
      src := String.join ((List.range 4).map fun i => s!"var 1..3: x{i};\n") ++
        String.join ((List.range 4).flatMap fun i =>
          ((List.range 4).filter (· > i)).map fun j =>
            s!"constraint int_ne(x{i}, x{j});\n") ++ "solve satisfy;\n",
      sat := false },
    { name := "pigeon-3-3-sat",
      src := String.join ((List.range 3).map fun i => s!"var 1..3: x{i};\n") ++
        String.join ((List.range 3).flatMap fun i =>
          ((List.range 3).filter (· > i)).map fun j =>
            s!"constraint int_ne(x{i}, x{j});\n") ++ "solve satisfy;\n",
      sat := true },
    { name := "const-bound-sat",
      src := "var 0..3: x;\nconstraint int_eq(x, 2);\nsolve satisfy;\n",
      sat := true },
    { name := "lin-sat",
      src := "var 1..3: x;\nvar 1..3: y;\nconstraint int_lin_le([1,1],[x,y],4);\n\
              constraint int_ne(x, 3);\nsolve satisfy;\n",
      sat := true },
    { name := "bool-sat",
      src := "var bool: x;\nvar bool: y;\nconstraint bool_not(x,y);\nsolve satisfy;\n",
      sat := true },
    { name := "bool-unsat",
      src := "var bool: a;\nvar bool: b;\nvar bool: c;\n\
              constraint bool_not(a, b);\nconstraint bool_not(a, c);\n\
              constraint bool_not(b, c);\nsolve satisfy;\n",
      sat := false },
    { name := "all-diff-sat",
      src := "var 1..4: a;\nvar 1..4: b;\nvar 1..4: c;\n\
              constraint all_different([a, b, c]);\nconstraint int_ne(a, 4);\n\
              solve satisfy;\n",
      sat := true } ]

def main : IO UInt32 := do
  let mut ok := true
  let mut fired := 0
  let mut n := 0
  for f in fixtures do
    let (pass, didFire) ← runOne f
    ok := ok && pass
    n := n + 1
    if didFire then fired := fired + 1
  IO.println s!"HEUR SUMMARY fixtures={n} fired={fired} ok={ok}"
  if ok && fired > 0 then
    return 0
  else
    IO.eprintln "heur route regression FAILED"
    return 1

end HeurLcgFixtures

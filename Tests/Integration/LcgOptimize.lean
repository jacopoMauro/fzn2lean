/-
Purpose: LCG branch-and-bound fixtures compared with chronological solving and exhaustive optimum.
Dependencies: LcgOptimize provides the solver interface; the parser and objective compiler
turn source fixtures into the same finite problems checked by the independent enumeration oracle.
DAG: integration leaves -> this executable test leaf.
-/
import LeanFzn.Integration.LcgOptimize
import LeanFzn.Integration.LcgSeed
import LeanFzn.Parser.Parser

namespace Tests.Integration.LcgOptimize
open LeanFzn LeanFzn.Semantics LeanFzn.Compiler LeanFzn.Integration LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation.DomainFiltering

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

private def improving (spec : ObjectiveSpec) : List (List Value × Int) → Bool
  | [] => true
  | [_] => true
  | s :: t :: rest => betterB spec.dir t.2 s.2 && improving spec (t :: rest)

private def runCase (label src : String) : IO Bool := do
  match Parser.parseModel src with
  | .error e => IO.eprintln s!"FAIL {label}: parse {e}"; return false
  | .ok m =>
      match compileModelOpt m with
      | .error e => IO.eprintln s!"FAIL {label}: compile {e}"; return false
      | .ok (p, spec) =>
          let lr := optLoop lcgSolver p spec none
          let cr := optLoop chronSolver p spec none
          let sr := optLoopSeed lcgSeedSolver p spec none (SeedDb.nil p.domains)
          let opt := oracle p spec
          let lv := lr.sols.getLast?.map Prod.snd
          let cv := cr.sols.getLast?.map Prod.snd
          let sv := sr.1.sols.getLast?.map Prod.snd
          let accepted := lr.sols.all (fun s => accepts p s.1 &&
            decide (s.1 ∈ allAssigns p.domains) && s.1[spec.slot]? == some (.int s.2))
          let acceptedSeed := sr.1.sols.all (fun s => accepts p s.1 &&
            decide (s.1 ∈ allAssigns p.domains) && s.1[spec.slot]? == some (.int s.2))
          -- the seeded driver carries one seed per solve, starting from the
          -- empty seed
          let seedTraceOk := sr.2.length == sr.1.sols.length + 1 && sr.2.head? == some 0
          -- PLAN P2 note: the two drivers share the certified optimum, the
          -- strict-improvement sequence, the witness acceptance and the seed
          -- trace shape, but their PATH LENGTHS may legitimately differ now
          -- that the activity order (LcgHeur) changes which assignment each
          -- solve starts from (e.g. 3 improving steps unseeded vs 5 seeded on
          -- `non-unit maximize` — fewer steps is the heuristic working). The
          -- former `sr.1.sols.length == lr.sols.length` conjunct asserted a
          -- shared-ORDER property, not a correctness one; it is replaced by
          -- the per-driver structural checks below.
          let ok := lr.complete && cr.complete && accepted && improving spec lr.sols &&
            lv == opt && cv == opt && seedTraceOk &&
            sr.1.complete && acceptedSeed &&
            improving spec sr.1.sols && sv == opt
          if !ok then
            IO.eprintln s!"FAIL {label}: LCG {lv}, chronological {cv}, oracle {opt}, seeded {sv}, completed {lr.complete}/{cr.complete}/{sr.1.complete}, seeds {sr.2}"
            IO.eprintln s!"  detail: accepted={accepted} improvingLcg={improving spec lr.sols} lv=opt:{lv == opt} cv=opt:{cv == opt} seedTraceOk={seedTraceOk} lenEq={(sr.1.sols.length == lr.sols.length)} acceptedSeed={acceptedSeed} improvingSeed={improving spec sr.1.sols} sv=opt:{sv == opt} lens lcg={lr.sols.length} seed={sr.1.sols.length} chron={cr.sols.length}"
          return ok

private def directed : List (String × String) := [
  ("non-unit minimize", "var 0..4: x; var 0..4: y; constraint int_lin_le([-1,-1],[x,y],-4); solve minimize y;"),
  ("non-unit maximize", "var 0..4: x; var 0..4: y; constraint int_lin_le([1,1],[x,y],4); solve maximize y;"),
  ("unsat", "var 0..3: x; var 0..3: y; constraint int_lin_le([1,1],[x,y],1); constraint int_lin_le([-1,-1],[x,y],-4); solve minimize x;"),
  ("parameter-array objective", "array [1..3] of int: co=[2,3,-1]; var 0..3: x; var 0..3: y; var 0..15: z; constraint int_lin_eq(co,[x,y,z],0); solve maximize z;"),
  ("fallback times", "var 0..3: x; var 0..3: y; var 0..9: z; constraint int_times(x,y,z); solve maximize z;"),
  ("boolean fallback", "var bool: b; var bool: c; var 0..1: x; constraint bool_not(b,c); solve maximize x;")]

/-- The reuse-evidence instance: a linear program with NO `bool_clause`
    constraint, so `seedClauses p.constraints` is empty and every clause the
    seeded driver carries between rounds is genuinely LEARNED. The kernel
    learns on its first round, so the second solve starts with a nonempty
    database. -/
private def reuseSrc : String :=
  "var 0..4: x; var 0..4: y; constraint int_lin_le([-1,-1],[x,y],-4); solve minimize y;"

/-- PLAN B2 reuse evidence: runs the seeded driver on the reuse instance,
    PRINTS the seed size of every round (the number of learned clauses handed
    to each solve), and asserts that the seed of the first re-solve is
    nonempty (`seedCounts[1] > 0`). The optimum is certified equal to the
    plain LCG run, the chronological run and the exhaustive oracle, and every
    emitted solution is checker-accepted. -/
private def reuseCase : IO Bool := do
  match Parser.parseModel reuseSrc with
  | .error e => IO.eprintln s!"FAIL reuse: parse {e}"; return false
  | .ok m =>
      match compileModelOpt m with
      | .error e => IO.eprintln s!"FAIL reuse: compile {e}"; return false
      | .ok (p, spec) =>
          let sr := optLoopSeed lcgSeedSolver p spec none (SeedDb.nil p.domains)
          let pr := optLoop lcgSolver p spec none
          let cr := optLoop chronSolver p spec none
          let opt := oracle p spec
          let sv := sr.1.sols.getLast?.map Prod.snd
          let pv := pr.sols.getLast?.map Prod.snd
          let cv := cr.sols.getLast?.map Prod.snd
          let accepted := sr.1.sols.all (fun s => accepts p s.1 &&
            decide (s.1 ∈ allAssigns p.domains) && s.1[spec.slot]? == some (.int s.2))
          IO.println s!"reuse: seed sizes per round = {sr.2}"
          IO.println s!"reuse: seed of the first re-solve = {sr.2[1]?.getD 0} learned clauses"
          IO.println s!"reuse: no bool_clause seed in this instance: {(seedClauses p.constraints).isEmpty}"
          let ok := (seedClauses p.constraints).isEmpty &&
            sr.1.complete && accepted && sv == opt && pv == opt && cv == opt &&
            sr.2.length == sr.1.sols.length + 1 && sr.2[1]?.getD 0 > 0
          if !ok then
            IO.eprintln s!"FAIL reuse: seeds {sr.2}, seeded {sv}, plain {pv}, chrono {cv}, oracle {opt}, complete {sr.1.complete}"
          return ok

/-- Directed examples and 100 finite linear cases check optimality, witness acceptance,
strict improvement, completion and agreement with the chronological certified solver. -/
def main : IO UInt32 := do
  let mut passed := 0
  let mut failed := 0
  for (label, src) in directed do
    if ← runCase label src then passed := passed + 1 else failed := failed + 1
  if ← reuseCase then passed := passed + 1 else failed := failed + 1
  for i in [0:100] do
    let hi := i % 4 + 1
    let lo := (i / 4) % (2 * hi + 3)
    let bound := (i / 17) % (2 * hi + 2)
    let dir := if i % 2 == 0 then "minimize" else "maximize"
    let src := s!"var 0..{hi}: x; var 0..{hi}: y; constraint int_lin_le([-1,-1],[x,y],-{lo}); constraint int_lin_le([1,1],[x,y],{bound}); solve {dir} y;"
    if ← runCase s!"linear-{i}" src then passed := passed + 1 else failed := failed + 1
  IO.println s!"LCG optimization: {passed} passed, {failed} failed"
  return if failed == 0 then 0 else 1

end Tests.Integration.LcgOptimize

def main : IO UInt32 := Tests.Integration.LcgOptimize.main

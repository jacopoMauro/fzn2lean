/-
Purpose: Regression checks for OptimizeBnB.
Dependencies: LeanFzn.Cli.Main, LeanFzn.Legacy.Integration.Optimize, LeanFzn.Compiler.Objective, LeanFzn.Parser.Parser, LeanFzn.Checker.Check, LeanFzn.Checker.Objective.
DAG: Historical solver components -> this test leaf.
-/
import LeanFzn.Cli.Main
import LeanFzn.Legacy.Integration.Optimize
import LeanFzn.Compiler.Objective
import LeanFzn.Parser.Parser
import LeanFzn.Checker.Check
import LeanFzn.Checker.Objective
open LeanFzn LeanFzn.Compiler LeanFzn.Checker LeanFzn.Semantics LeanFzn.Integration
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.Core

/-!
# Tests: certified branch-and-bound (O2a)

* CLI end to end (`LeanFzn.Cli.main ["solve", file]`) on small minimize and
  maximize models with parameter arrays: exit code, the `----------` / `==========`
  stream, every printed solution accepted by the checker, objective values
  strictly improving, final optimum equal to an exhaustive brute-force oracle
  over `allAssigns` of the compiled problem (independent of the solver).
* UNSAT optimization model prints `=====UNSATISFIABLE=====`.
* A deterministic random fuzz (200 instances) against the same oracle. Core
  may stop incomplete: every retained witness must pass the checker, objectives
  must improve and no terminal marker may be printed. Completed runs must
  still equal the exhaustive optimum; directed cases must still complete.
-/

private def parseOrPanic (src : String) : Model :=
  match Parser.parseModel src with
  | .ok m => m
  | .error e => panic! s!"unexpected parse error: {e}"

structure St where
  passed : Nat
  failed : Nat
  incomplete : Nat := 0

def St.check (st : St) (name : String) (ok : Bool) : IO St := do
  if ok then
    pure { st with passed := st.passed + 1 }
  else
    IO.eprintln s!"FAIL {name}"
    pure { st with failed := st.failed + 1 }

def runCli (args : List String) : IO (UInt32 × String) := do
  let (out, code) ← IO.FS.withIsolatedStreams (LeanFzn.Cli.main args)
  return (code, out)

/-- Brute-force optimum of the compiled problem (none if infeasible). -/
def bruteOpt (m : Model) : Option Int :=
  match compileModelOpt m with
  | .error _ => none
  | .ok (p, spec) =>
    let vals := ((allAssigns p.domains).filter (accepts p)).filterMap fun a =>
      match a[spec.slot]? with | some (Value.int i) => some i | _ => none
    match vals with
    | [] => none
    | v :: vs => some (match spec.dir with
        | .minimize => vs.foldl min v
        | .maximize => vs.foldl max v)

def strictlyImproving (isMin : Bool) : List Int → Bool
  | a :: b :: rest => (if isMin then b < a else a < b) && strictlyImproving isMin (b :: rest)
  | _ => true

/-- Run the CLI on a model and compare with the brute-force oracle. -/
def runCase (st : St) (label : String) (src : String)
    (allowIncomplete : Bool := false) : IO St := do
  let m := parseOrPanic src
  let dir : System.FilePath := "/tmp/leanfzn_optimize_bnb"
  IO.FS.createDirAll dir
  let path := (dir / "m.fzn").toString
  IO.FS.writeFile path src
  let (code, out) ← runCli ["solve", path]
  let isMin := match m.solve with | .minimize _ _ => true | _ => false
  if code == 4 && allowIncomplete then
    let sols := (out.splitOn "----------").dropLast
    let vals := sols.filterMap (fun text => checkedObjective m (text ++ "\n----------\n"))
    let st := { st with incomplete := st.incomplete + 1 }
    let st ← st.check s!"{label}: incomplete has no terminal proof marker"
      ((out.splitOn "==========").length == 1 &&
       (out.splitOn "=====UNSATISFIABLE=====").length == 1)
    let st ← st.check s!"{label}: all retained incumbents checker-accepted"
      (vals.length == sols.length)
    let st ← st.check s!"{label}: incomplete incumbents strictly improve"
      (strictlyImproving isMin vals)
    let checked ← match bruteOpt m with
    | none => st.check s!"{label}: infeasible partial run has no incumbent" sols.isEmpty
    | some optimum =>
        st.check s!"{label}: partial objectives respect exhaustive optimum"
          (vals.all fun v => if isMin then decide (optimum ≤ v) else decide (v ≤ optimum))
    return checked
  match bruteOpt m with
  | none =>
      st.check s!"{label}: infeasible -> exit 1 + UNSATISFIABLE"
        (code == 1 && (out.splitOn "=====UNSATISFIABLE=====").length == 2)
  | some opt =>
      let sols := (out.splitOn "----------").dropLast
      let vals := sols.filterMap (fun s => checkedObjective m (s ++ "\n----------\n"))
      let ok1 := code == 0
      let ok2 := (out.splitOn "==========").length == 2 &&
        out.trimAscii.toString.endsWith "=========="
      let ok3 := vals.length == sols.length && !sols.isEmpty
      let ok4 := strictlyImproving isMin vals
      let ok5 := vals.getLast? == some opt
      let st ← st.check s!"{label}: exit 0" ok1
      let st ← st.check s!"{label}: optimum marker last" ok2
      let st ← st.check s!"{label}: every solution checker-accepted" ok3
      let st ← st.check s!"{label}: strictly improving {vals}" ok4
      st.check s!"{label}: final = brute-force optimum {opt} (got {vals.getLast?})" ok5

def parArr : String :=
"array [1..3] of int: coef = [3,5,2];
var 0..5: x :: output_var;
var 0..5: y :: output_var;
var 0..5: z :: output_var;
var 0..60: obj :: output_var;
array [1..4] of var int: xs4 :: output_array([1..4]) = [x,y,z,obj];
constraint int_lin_le([1,1,1],[x,y,z],7);
constraint int_lin_eq([3,5,2,-1],[x,y,z,obj],0);
"

def minSrc : String :=
"array [1..2] of int: w = [1,1];
var 0..5: x :: output_var;
var 0..5: y :: output_var;
var -10..10: obj :: output_var;
array [1..2] of var int: xs = [x,y];
constraint int_lin_le(w,xs,8);
constraint int_lin_le([-1,-1],[x,y],-4);
constraint int_lin_eq([2,-3,-1],[x,y,obj],0);
solve minimize obj;
"

def unsatSrc : String :=
"var 0..5: x :: output_var;
var 0..5: y :: output_var;
constraint int_lin_le([1,1],[x,y],1);
constraint int_lin_le([-1,-1],[x,y],-4);
solve minimize x;
"

/-! Deterministic PRNG for the fuzz. -/
def nextRand (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648
def pick (s : Nat) (n : Nat) : Nat × Nat :=
  let s' := nextRand s
  (s', (s' / 65536) % n)

def intStr (i : Int) : String := toString i

/-- A random optimization instance. -/
def genInstance (seed : Nat) : String × Nat := Id.run do
  let mut s := seed
  let mut lines : List String := []
  let (s1, hi) := pick s 4
  s := s1
  let hi := hi + 2
  lines := lines ++ [s!"var 0..{hi}: a :: output_var;", s!"var 0..{hi}: b :: output_var;",
    s!"var 0..{hi}: c :: output_var;", "var -60..60: obj :: output_var;"]
  -- 2..4 random linear constraints over (a,b,c)
  let (s2, nc) := pick s 3
  s := s2
  for _ in [0:nc + 2] do
    let (sa, ca) := pick s 7
    let (sb, cb) := pick sa 7
    let (sc, cc) := pick sb 7
    let (sd, rhs) := pick sc 12
    let (se, kind) := pick sd 4
    s := se
    let co := s!"[{intStr ((ca : Int) - 3)},{intStr ((cb : Int) - 3)},{intStr ((cc : Int) - 3)}]"
    if kind == 0 then
      lines := lines ++ [s!"constraint int_lin_eq({co},[a,b,c],{intStr ((rhs : Int) - 4)});"]
    else
      lines := lines ++ [s!"constraint int_lin_le({co},[a,b,c],{intStr ((rhs : Int) - 2)});"]
  -- objective definition obj = o1*a + o2*b + o3*c, via a parameter array half the time
  let (s3, o1) := pick s 7
  let (s4, o2) := pick s3 7
  let (s5, o3) := pick s4 7
  let (s6, usePar) := pick s5 2
  let (s7, dirB) := pick s6 2
  let (s8, ne) := pick s7 3
  s := s8
  let os := [(o1 : Int) - 3, (o2 : Int) - 3, (o3 : Int) - 3]
  let cs := ",".intercalate (os.map intStr)
  if usePar == 0 then
    lines := lines ++ [s!"constraint int_lin_eq([{cs},-1],[a,b,c,obj],0);"]
  else
    lines := ([s!"array [1..4] of int: oc = [{cs},-1];",
      "array [1..4] of var int: ov = [a,b,c,obj];"] ++ lines) ++
      ["constraint int_lin_eq(oc,ov,0);"]
  if ne == 0 then lines := lines ++ ["constraint int_ne(a,b);"]
  lines := lines ++ [s!"solve {if dirB == 0 then "minimize" else "maximize"} obj;"]
  return ("\n".intercalate lines ++ "\n", s)

def main : IO UInt32 := do
  let mut st : St := { passed := 0, failed := 0 }
  st ← runCase st "par-array maximize" (parArr ++ "solve maximize obj;\n")
  st ← runCase st "par-array minimize" (parArr ++ "solve minimize obj;\n")
  st ← runCase st "minimize with par weights" minSrc
  st ← runCase st "unsat optimize" unsatSrc
  IO.println s!"directed cases: passed {st.passed}, failed {st.failed}"
  -- satisfy models are unchanged
  IO.FS.writeFile "/tmp/leanfzn_optimize_bnb/sat.fzn"
    "var 0..3: x :: output_var;\nconstraint int_le(x,2);\nsolve satisfy;\n"
  let (c, out) ← runCli ["solve", "/tmp/leanfzn_optimize_bnb/sat.fzn"]
  st ← st.check "satisfy model unchanged (one solution, no optimum marker)"
    (c == 0 && (out.splitOn "----------").length == 2 && (out.splitOn "==========").length == 1)
  let mut seed := 20260101
  let mut feasible := 0
  let mut infeasible := 0
  for i in [0:200] do
    seed := nextRand (seed + i)
    let (src, _) := genInstance seed
    let m := parseOrPanic src
    match bruteOpt m with
    | none => infeasible := infeasible + 1
    | some _ => feasible := feasible + 1
    st ← runCase st s!"fuzz#{i}\n{src}" src true
  IO.println s!"fuzz: 200 instances ({feasible} feasible, {infeasible} infeasible), {st.incomplete} incomplete"
  -- Fixed-seed coverage floor: the Core-only baseline completes 186/200.
  -- This keeps random coverage meaningful while checking partial results
  -- explicitly. Improvements may complete more cases without changing the test.
  st ← st.check "fixed-seed Core completion coverage >= 180/200" (st.incomplete ≤ 20)
  -- PLAN E3: streamed optimization output is FLUSHED after every improving
  -- solution. Regression: run the CLI as a subprocess on a model whose
  -- improvement climb takes well over 2 s, kill it with `timeout 2`, and
  -- require that the `----------` lines produced so far are visible. Before
  -- the flush fix the killed process showed 0 separators (stdout block
  -- buffer lost on SIGTERM); with the flush it shows the ones it printed.
  -- The check needs the repo-root-relative `leanfzn` binary; when the test
  -- is run from somewhere else (or without building `leanfzn`), it degrades
  -- to a reported skip instead of a false failure.
  let streamSrc :=
    "var 0..2000: x;\nvar 0..2000: y;\nvar 0..2000: z;\n\
     constraint int_plus(x, y, z);\nconstraint int_le(z, 2000);\n\
     solve maximize x;\n"
  let streamPath := "/tmp/leanfzn_optimize_bnb/stream.fzn"
  IO.FS.writeFile streamPath streamSrc
  if ← System.FilePath.pathExists ".lake/build/bin/leanfzn" then
    let res ← IO.Process.output
      { cmd := "timeout", args := #["2", ".lake/build/bin/leanfzn", "solve", streamPath] }
    let dashes := (res.stdout.splitOn "----------").length - 1
    IO.println s!"E3: killed streaming run shows {dashes} flushed `----------` lines"
    st ← st.check s!"E3: killed streaming run shows flushed `----------` (dashes={dashes})"
      (dashes > 0)
  else
    IO.println "E3: skipped (build `.lake/build/bin/leanfzn` to run the flush regression)"
  IO.println s!"passed {st.passed}, failed {st.failed}"
  return if st.failed == 0 then 0 else 1

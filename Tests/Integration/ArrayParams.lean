import LeanFzn.Compiler.Normalize
import LeanFzn.Compiler.Proofs.Normalize
import LeanFzn.Parser.Parser
import LeanFzn.Checker.Check
import LeanFzn.Integration.Emit
import LeanFzn.Integration.CertifiedSolve
import LeanFzn.Solver.Reference.Search
import LeanFzn.Integration.Chronological
import LeanFzn.Cli.Main
open LeanFzn LeanFzn.Compiler LeanFzn.Checker LeanFzn.Semantics
open LeanFzn.Solver.Propagation.DomainFiltering

/-!
# Regression tests: parameter arrays and variable-array aliases (X1)

`compileModelFull` accepts `array [1..n] of int/bool: p = [..];`
parameter arrays and `array [1..n] of var int/bool: x = [v1,..];`
aliases of declared scalar variables.  Each test compiles a parsed
FlatZinc source, solves the compiled problem with the exhaustive
reference search, and runs the emitted solution (which includes the
array values) through the verified checker `checkModelSolution` against
the ORIGINAL model.  The proofs are `compileFull_exact` and
`compileFull_covers` (`Compiler/Proofs/Normalize.lean`).
-/

private def parseOrPanic (src : String) : Model :=
  match Parser.parseModel src with
  | .ok m => m
  | .error e => panic! s!"unexpected parse error: {e}"

structure St where
  passed : Nat
  failed : Nat

def St.check (st : St) (name : String) (ok : Bool) : IO St := do
  if ok then
    IO.println s!"ok {name}"
    pure { st with passed := st.passed + 1 }
  else
    IO.eprintln s!"FAIL {name}"
    pure { st with failed := st.failed + 1 }

/-- The library emitter (arrays as `array1d(1..n, [..])`). -/
def emitFull (m : Model) (store : Store) : String :=
  LeanFzn.Integration.emitCertifiedSolution m store

/-- Solve through the full front end and the reference search; the
    emitted solution is checked against the original model. -/
def solveFull (m : Model) : Option (Option String) :=
  match compileModelFull m with
  | .error _ => none
  | .ok problem =>
      match LeanFzn.Solver.Reference.solveCompiled problem with
      | some a => some (some (emitFull m (problem.toStore a)))
      | none => some none

/-- The certified chronological LCG route over the full front end
    (the same executable as `solveCertified`, with `compileModelFull`). -/
def solveFullLcg (m : Model) : Option (Option String) :=
  match compileModelFull m with
  | .error _ => none
  | .ok problem =>
      if LeanFzn.Solver.Propagation.gateOk (LeanFzn.Integration.toLCG problem) then
        match LeanFzn.Solver.Chronological.solve (LeanFzn.Integration.toLCG problem)
            DomConstraint.satisfiedB
            (problem.constraints.filterMap LeanFzn.Solver.Propagation.propagatorOfProved)
            (LeanFzn.Solver.Propagation.domPruningKit (LeanFzn.Integration.toLCG problem)) with
        | .sat a => some (some (emitFull m (problem.toStore a)))
        | .unsat => some none
        | .unknown => none
      else none

def satSrc : String :=
"array [1..3] of int: coef = [1,2,3];
array [1..2] of bool: unusedFlags = [true,false];
var 0..5: x :: output_var;
var 0..5: y :: output_var;
var 0..5: z :: output_var;
var bool: b1;
var bool: b2;
array [1..3] of var int: xs :: output_array([1..3]) = [x,y,z];
array [1..2] of var bool: bs :: output_array([1..2]) = [b1,b2];
constraint int_lin_eq(coef,xs,14);
constraint int_lin_le(coef,xs,15);
constraint bool_not(b1,b2);
solve satisfy;
"

def unsatSrc : String :=
"array [1..3] of int: coef = [1,2,3];
var 0..5: x;
var 0..5: y;
var 0..5: z;
array [1..3] of var int: xs :: output_array([1..3]) = [x,y,z];
constraint int_lin_eq(coef,xs,100);
solve satisfy;
"

def restrictedSrc : String :=
"var 0..5: x;
var 0..5: y;
array [1..2] of var 0..3: ys :: output_array([1..2]) = [x,y];
constraint all_different(ys);
solve satisfy;
"

def scalarSrc : String :=
"var 1..3: x;
var 1..3: y;
constraint int_plus(x,y,5);
solve satisfy;
"

/-- Run the real CLI entry point on `args`, capturing stdout/stderr. -/
def runCli (args : List String) : IO (UInt32 × String) := do
  let (out, code) ← IO.FS.withIsolatedStreams (LeanFzn.Cli.main args)
  return (code, out)

def main : IO UInt32 := do
  let mut st : St := { passed := 0, failed := 0 }
  -- CLI end to end: write the models to files, run `solve`, then `check`
  let dir : System.FilePath := "/tmp/leanfzn_arrayparams_test"
  IO.FS.createDirAll dir
  let satPath := (dir / "sat.fzn").toString
  let unsatPath := (dir / "unsat.fzn").toString
  let solPath := (dir / "sat.sol").toString
  IO.FS.writeFile satPath satSrc
  IO.FS.writeFile unsatPath unsatSrc
  let (c1, out1) ← runCli ["solve", satPath]
  IO.println s!"CLI solve (SAT) exit {c1}:\n{out1}"
  st ← st.check "CLI solve: array model SAT exit 0" (c1 == 0)
  st ← st.check "CLI solve: output has array1d for xs and bs"
    ((out1.splitOn "xs = array1d(1..3, [").length == 2 &&
     (out1.splitOn "bs = array1d(1..2, [").length == 2 &&
     (out1.splitOn "<unemittable").length == 1)
  IO.FS.writeFile solPath out1
  let (c2, _) ← runCli ["check", satPath, solPath]
  st ← st.check "CLI check accepts the CLI solve output (arrays)" (c2 == 0)
  let (c3, out3) ← runCli ["solve", unsatPath]
  IO.println s!"CLI solve (UNSAT) exit {c3}:\n{out3}"
  st ← st.check "CLI solve: array model UNSAT prints =====UNSATISFIABLE====="
    (c3 == 1 && (out3.splitOn "=====UNSATISFIABLE=====").length == 2)
  -- SAT: parameter array + variable-array aliases
  let msat := parseOrPanic satSrc
  match solveFull msat with
  | some (some sol) =>
      st ← st.check "par/var arrays: SAT" true
      IO.println s!"witness:\n{sol}\noutcome: {repr (checkModelSolution msat sol)}"
      st ← st.check "par/var arrays: checker accepts the emitted witness"
        (checkModelSolution msat sol == .accepted)
  | _ =>
      st ← st.check "par/var arrays: SAT" false
  -- a corrupted witness is rejected by the same checker
  match solveFull msat with
  | some (some sol) =>
      let bad := sol.replace "xs = array1d(1..3, [" "xs = array1d(1..3, [9,"
      st ← st.check "par/var arrays: corrupted array witness rejected"
        (checkModelSolution msat bad != .accepted)
  | _ => st ← st.check "par/var arrays: corrupted witness" false
  -- the same through the certified chronological LCG route
  match solveFullLcg msat with
  | some (some sol) =>
      st ← st.check "par/var arrays: LCG route SAT, checker accepts"
        (checkModelSolution msat sol == .accepted)
  | _ => st ← st.check "par/var arrays: LCG route SAT" false
  st ← st.check "par/var arrays: LCG route UNSAT"
    (match solveFullLcg (parseOrPanic unsatSrc) with | some none => true | _ => false)
  -- UNSAT
  let munsat := parseOrPanic unsatSrc
  st ← st.check "par/var arrays: UNSAT"
    (match solveFull munsat with | some none => true | _ => false)
  -- the legacy front door still rejects the same models
  st ← st.check "compileModel still rejects array models"
    (match compileModel msat with | .error _ => true | .ok _ => false)
  -- scalar CLI output is unchanged (no array1d, plain `name = v;` lines)
  let scalarPath := (dir / "scalar.fzn").toString
  IO.FS.writeFile scalarPath scalarSrc
  let (c4, out4) ← runCli ["solve", scalarPath]
  st ← st.check "CLI solve: scalar model output shape unchanged"
    (c4 == 0 && out4 == "x = 2;\ny = 3;\n----------\n")
  -- unrestricted-domain gate: restricted array element type is rejected
  st ← st.check "restricted var-array element domain is rejected"
    (match compileModelFull (parseOrPanic restrictedSrc) with
     | .error _ => true | .ok _ => false)
  -- scalar models: the full front end agrees with compileModel
  let ms := parseOrPanic scalarSrc
  st ← st.check "scalar model: compileModelFull accepts like compileModel"
    (match compileModel ms, compileModelFull ms with
     | .ok _, .ok _ => true | _, _ => false)
  IO.println s!"passed {st.passed}, failed {st.failed}"
  return if st.failed == 0 then 0 else 1

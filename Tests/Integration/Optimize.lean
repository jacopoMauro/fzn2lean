import LeanFzn.Compiler.Objective
import LeanFzn.Compiler.Proofs.Objective
import LeanFzn.Parser.Parser
import LeanFzn.Checker.Check
import LeanFzn.Checker.Objective
import LeanFzn.Integration.Emit
import LeanFzn.Integration.CertifiedSolve
open LeanFzn LeanFzn.Compiler LeanFzn.Checker LeanFzn.Semantics
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.Core

/-!
# Regression tests: optimization front end (O1)

`compileModelOpt` compiles `solve minimize/maximize x` into the satisfy
problem plus an `ObjectiveSpec`.  For each model the test enumerates the
finite candidate space and checks, for every accepted assignment, the
objective correspondence of `compileOpt_exact`
(`m.solve.objective (toStore a) = some (a at the objective slot)`); it
finds the optimum by brute force and checks the hypothesis of
`compileOpt_optimal` (no accepted assignment of the problem extended with
`spec.improveBound v`) holds exactly at the optimum and fails above it.
The checker twin `checkedObjective` is run on the emitted solution.
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

def header : String :=
"array [1..4] of int: coef = [1,2,3,-1];
array [1..3] of int: lo = [-1,-1,-1];
array [1..3] of int: hi = [1,1,1];
var 0..4: x :: output_var;
var 0..4: y :: output_var;
var 0..4: z :: output_var;
var 0..40: obj :: output_var;
array [1..3] of var int: xs :: output_array([1..3]) = [x,y,z];
array [1..4] of var int: xs4 :: output_array([1..4]) = [x,y,z,obj];
constraint int_lin_eq(coef,xs4,0);
constraint int_lin_le(lo,xs,-3);
constraint int_lin_le(hi,xs,6);
"

def minSrc : String := header ++ "solve minimize obj;\n"
def maxSrc : String := header ++ "solve maximize obj;\n"

def objOf (a : List Value) (slot : Nat) : Option Int :=
  match a[slot]? with | some (.int i) => some i | _ => none

/-- All accepted assignments. -/
def acceptedOf (p : CompiledProblem DomConstraint) : List (List Value) :=
  (allAssigns p.domains).filter (accepts p)

def runModel (st : St) (label : String) (src : String) (expectOpt : Int) :
    IO St := do
  let m := parseOrPanic src
  let mut st := st
  match compileModelOpt m with
  | .error e => st.check s!"{label}: compiles ({e})" false
  | .ok (p, spec) =>
    st ← st.check s!"{label}: compiles" true
    let acc := acceptedOf p
    st ← st.check s!"{label}: has accepted assignments" (!acc.isEmpty)
    -- (b) objective correspondence on every accepted assignment
    st ← st.check s!"{label}: objective correspondence on all {acc.length} accepted"
      (acc.all fun a =>
        match objOf a spec.slot with
        | some i => m.solve.objective (p.toStore a) == some i
        | none => false)
    let vals := acc.filterMap (objOf · spec.slot)
    let best := match spec.dir with
      | .minimize => vals.foldl min (vals.headD 0)
      | .maximize => vals.foldl max (vals.headD 0)
    st ← st.check s!"{label}: brute-force optimum is {expectOpt} (got {best})"
      (best == expectOpt)
    -- (c) hypothesis of compileOpt_optimal
    let noBetter (v : Int) : Bool :=
      (allAssigns p.domains).all fun b =>
        !(accepts (p.addConstraint (spec.improveBound v)) b)
    st ← st.check s!"{label}: no improving assignment at the optimum" (noBetter best)
    let worse := match spec.dir with | .minimize => best + 1 | .maximize => best - 1
    st ← st.check s!"{label}: improving assignment exists above the optimum"
      (!noBetter worse)
    -- (c) checker twin on an optimal solution
    match acc.find? (fun a => objOf a spec.slot == some best) with
    | none => st.check s!"{label}: optimal witness" false
    | some a =>
        let sol := LeanFzn.Integration.emitCertifiedSolution m (p.toStore a)
        st ← st.check s!"{label}: checker accepts the optimal witness"
          (checkModelSolution m sol == .accepted)
        st.check s!"{label}: checkedObjective = {best}"
          (checkedObjective m sol == some best)

def main : IO UInt32 := do
  let mut st : St := { passed := 0, failed := 0 }
  st ← runModel st "minimize" minSrc 3
  st ← runModel st "maximize" maxSrc 16
  -- rejections
  st ← st.check "satisfy model is not an objective model"
    (match compileModelOpt (parseOrPanic (header ++ "solve satisfy;\n")) with
     | .error _ => true | .ok _ => false)
  st ← st.check "compileModel still rejects optimize items"
    (match compileModel (parseOrPanic (header ++ "solve minimize obj;\n")) with
     | .error _ => true | .ok _ => false)
  st ← st.check "literal objective rejected"
    (match compileModelOpt (parseOrPanic (header ++ "solve minimize 3;\n")) with
     | .error _ => true | .ok _ => false)
  st ← st.check "parameter objective rejected"
    (match compileModelOpt (parseOrPanic ("int: c = 3;\nvar 0..4: x;\nsolve minimize c;\n")) with
     | .error _ => true | .ok _ => false)
  IO.println s!"passed {st.passed}, failed {st.failed}"
  return if st.failed == 0 then 0 else 1

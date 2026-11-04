import LeanFzn.Compiler.Normalize
import LeanFzn.Compiler.Proofs.Normalize
import LeanFzn.Parser.Parser
import LeanFzn.Checker.Check
import LeanFzn.Integration.Emit
import LeanFzn.Legacy.Integration.CertifiedSolve
import LeanFzn.Legacy.Solver.Reference.Search
import LeanFzn.Legacy.Integration.Chronological
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

/-! ## PLAN C0: the Boolean XOR channel (`bool_xor`) -/

/-- A satisfiable XOR channel: the compiler rewrites it into the four
    equivalence clauses, solved through the reference search. -/
def xorSatSrc : String :=
"var bool: x;
var bool: y;
var bool: z;
constraint bool_xor(x,y,z);
solve satisfy;
"

/-- An unsatisfiable XOR channel: `x = y = z = true` violates
    `z = (x ^^ y)`. -/
def xorUnsatSrc : String :=
"var bool: x;
var bool: y;
var bool: z;
constraint bool_not(x,false);
constraint bool_not(y,false);
constraint bool_not(z,false);
constraint bool_xor(x,y,z);
solve satisfy;
"

/-- The four equivalence clauses of `bool_xor(x,y,z)` over the slots
    `[x,y,z]` (positions 0,1,2). -/
def xorClausesB : List DomConstraint → Bool
  | [.boolClauseSlot [0, 1] [2], .boolClauseSlot [] [0, 1, 2],
     .boolClauseSlot [1, 2] [0], .boolClauseSlot [0, 2] [1]] => true
  | _ => false

/-- Run the real CLI entry point on `args`, capturing stdout/stderr. -/
def runCli (args : List String) : IO (UInt32 × String) := do
  let (out, code) ← IO.FS.withIsolatedStreams (LeanFzn.Cli.main args)
  return (code, out)

/-! ## PLAN C0: the value-literal `array_int_element` (`constElemValL`) -/

/-- A satisfiable instance: the all-literal table `[10,20,30]` with the
    literal value `20` (so `i = 2`), plus a scalar constraint. -/
def elemValSatSrc : String :=
"var 1..3: i;
var 1..3: y;
constraint array_int_element(i, [10, 20, 30], 20);
constraint int_eq(y, 3);
solve satisfy;
"

/-- An unsatisfiable instance: no table entry is `99`. -/
def elemValUnsatSrc : String :=
"var 1..3: i;
var 1..3: y;
constraint array_int_element(i, [10, 20, 30], 99);
solve satisfy;
"

/-- PLAN C0 k-literal generalization: a TWO-literal table with the
    literals at the head and tail and a LITERAL value. -/
def varElemFollowUpSrc : String :=
"var 1..3: i;
var 1..3: x;
array [1..3] of var int: t = [1, x, 3];
constraint array_var_int_element(i, t, 2);
constraint int_eq(i, 2);
solve satisfy;
"

/-- A satisfiable k-literal mixed table with a SLOT value and the two
    literals separated by an identifier: the table `[x, 1, 2, v]`, the
    value `v`, forced to `i = 2` (so `v = 1`). -/
def varElemTabKsMultiSrc : String :=
"var 1..3: i;
var 1..3: x;
var 1..3: v;
array [1..4] of var int: t = [x, 1, 2, v];
constraint array_var_int_element(i, t, v);
constraint int_eq(i, 2);
solve satisfy;
"

/-- Unsatisfiable: `i = 2` reads the first literal `1`, but the value is
    forced to `2`. -/
def varElemTabKsMultiUnsatSrc : String :=
"var 1..3: i;
var 1..3: x;
var 1..3: v;
array [1..4] of var int: t = [x, 1, 2, v];
constraint array_var_int_element(i, t, v);
constraint int_eq(i, 2);
constraint int_eq(v, 2);
solve satisfy;
"

/-- A satisfiable k-literal mixed table with a LITERAL value and the two
    literals separated by an identifier: the table `[x, 1, 2, x]` and
    the value `2`, forced to `i = 3`. -/
def varElemValKsMultiSrc : String :=
"var 1..3: i;
var 1..3: x;
array [1..4] of var int: t = [x, 1, 2, x];
constraint array_var_int_element(i, t, 2);
constraint int_eq(i, 3);
solve satisfy;
"

/-- Unsatisfiable: `i = 2` reads the first literal `1`, but the value is
    the literal `2`. -/
def varElemValKsMultiUnsatSrc : String :=
"var 1..3: i;
var 1..3: x;
array [1..4] of var int: t = [x, 1, 2, x];
constraint array_var_int_element(i, t, 2);
constraint int_eq(i, 2);
solve satisfy;
"

/-- PLAN C0 int follow-up: an ALL-SLOT table with a literal value.
    The table `[x, x]` and the value `1`, forced to `x = 1` (so every
    table entry reads `1`). -/
def varElemValLitAllslotSrc : String :=
"var 1..2: i;
var 1..3: x;
array [1..2] of var int: t = [x, x];
constraint array_var_int_element(i, t, 1);
constraint int_eq(x, 1);
solve satisfy;
"

/-- Unsatisfiable: every table entry is `2`, but the value is `1`. -/
def varElemValLitAllslotUnsatSrc : String :=
"var 1..2: i;
var 1..3: x;
array [1..2] of var int: t = [x, x];
constraint array_var_int_element(i, t, 1);
constraint int_eq(x, 2);
solve satisfy;
"

/-! ## PLAN C0: the mixed bool `array_var_bool_element` tables
(`varBoolTabLits` / `varBoolTabValLit`) -/

/-- A satisfiable mixed bool table with one Boolean literal and a slot
    value: the table `[true, b1, v]`, forced to `i = 1` and `v = true`
    (so `t[1] = true = v`). -/
def varBoolTabLitsSrc : String :=
"var 1..3: i;
var bool: b1;
var bool: v;
array [1..3] of var bool: t = [true, b1, v];
constraint array_var_bool_element(i, t, v);
constraint int_eq(i, 1);
constraint bool_not(v, false);
solve satisfy;
"

/-- Unsatisfiable: `i = 1` reads the table literal `true`, but the
    value is forced to `false`. -/
def varBoolTabLitsUnsatSrc : String :=
"var 1..3: i;
var bool: b1;
var bool: v;
array [1..3] of var bool: t = [true, b1, v];
constraint array_var_bool_element(i, t, v);
constraint int_eq(i, 1);
constraint bool_not(v, true);
solve satisfy;
"

/-- A satisfiable mixed bool table with TWO Boolean literals and a
    literal value: the table `[true, b1, false]` and the value `true`,
    forced to `i = 2` (so `b1 = true`). -/
def varBoolTabValLitSrc : String :=
"var 1..3: i;
var bool: b1;
array [1..3] of var bool: t = [true, b1, false];
constraint array_var_bool_element(i, t, true);
constraint int_eq(i, 2);
solve satisfy;
"

/-- Unsatisfiable: `i = 3` reads the table literal `false`, but the
    value is the literal `true`. -/
def varBoolTabValLitUnsatSrc : String :=
"var 1..3: i;
var bool: b1;
array [1..3] of var bool: t = [true, b1, false];
constraint array_var_bool_element(i, t, true);
constraint int_eq(i, 3);
solve satisfy;
"

/-- A satisfiable all-slot bool table with a literal value: the table
    `[b1, b1]` and the value `false`, forced to `b1 = false`. -/
def varBoolValLitAllslotSrc : String :=
"var 1..2: i;
var bool: b1;
array [1..2] of var bool: t = [b1, b1];
constraint array_var_bool_element(i, t, false);
constraint bool_not(b1, true);
solve satisfy;
"

/-- Unsatisfiable: every table entry is `true`, but the value is
    `false`. -/
def varBoolValLitAllslotUnsatSrc : String :=
"var 1..2: i;
var bool: b1;
array [1..2] of var bool: t = [b1, b1];
constraint array_var_bool_element(i, t, false);
constraint bool_not(b1, false);
solve satisfy;
"

/-! ## PLAN C0: the one-literal mixed `array_var_int_element` tables
(`varElemTabLit` / `varElemTabValLit`) -/

/-- A satisfiable one-literal mixed table with a SLOT value: the table
    `[1, x, x]` (one literal at the head) and the value `v`, forced to
    `i = 1`, `v = 1`. -/
def varElemTabSatSrc : String :=
"var 1..3: i;
var 1..3: x;
var 1..3: v;
array [1..3] of var int: t = [1, x, x];
constraint array_var_int_element(i, t, v);
constraint int_eq(i, 1);
constraint int_eq(v, 1);
solve satisfy;
"

/-- Unsatisfiable: `i = 1` reads the table literal `1`, but the value
    is forced to `2`. -/
def varElemTabUnsatSrc : String :=
"var 1..3: i;
var 1..3: x;
var 1..3: v;
array [1..3] of var int: t = [1, x, x];
constraint array_var_int_element(i, t, v);
constraint int_eq(i, 1);
constraint int_eq(v, 2);
solve satisfy;
"

/-- A satisfiable one-literal mixed table with a LITERAL value: the
    table `[1, x, x]` and the value `1`, forced to `i = 2` (so
    `x = 1`). -/
def varElemValLitSatSrc : String :=
"var 1..3: i;
var 1..3: x;
array [1..3] of var int: t = [1, x, x];
constraint array_var_int_element(i, t, 1);
constraint int_eq(i, 2);
solve satisfy;
"

/-- Unsatisfiable: `i = 1` reads the table literal `1`, but the value
    is the literal `2`. -/
def varElemValLitUnsatSrc : String :=
"var 1..3: i;
var 1..3: x;
array [1..3] of var int: t = [1, x, x];
constraint array_var_int_element(i, t, 2);
constraint int_eq(i, 1);
solve satisfy;
"

/-- Does the compiled list contain the pinned all-slot table element
    over the expected position list (the aux table's positions, the
    index position, the value position)? -/
def varElemCompiledB (is : List Nat) (i k : Nat) :
    List DomConstraint → Bool
  | [] => false
  | .arrayVarIntElementSlot is' i' k' :: _ =>
      (is' == is) && (i' == i) && (k' == k)
  | _ :: rest => varElemCompiledB is i k rest

/-- The bool-table twin of `varElemCompiledB`. -/
def varBoolElemCompiledB (is : List Nat) (i k : Nat) :
    List DomConstraint → Bool
  | [] => false
  | .arrayVarBoolElementSlot is' i' k' :: _ =>
      (is' == is) && (i' == i) && (k' == k)
  | _ :: rest => varBoolElemCompiledB is i k rest

/-- Does the compiled list contain the pinned slot-table element
    constraint over the literal table? -/
def elemValCompiledB : List DomConstraint → Bool
  | [] => false
  | .arrayIntElementSlot [10, 20, 30] _ _ :: _ => true
  | _ :: rest => elemValCompiledB rest

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
  -- PLAN C0: the Boolean XOR channel compiles to the four clauses,
  -- solves SAT through the reference search, and its witness is
  -- checker-accepted; the UNSAT instance is refuted
  let mxor := parseOrPanic xorSatSrc
  st ← st.check "bool_xor: compileModelFull accepts the channel"
    (match compileModelFull mxor with | .ok _ => true | .error _ => false)
  st ← st.check "bool_xor: the compiled form IS the four clauses"
    (match compileModelFull mxor with
     | .ok p => xorClausesB p.constraints
     | .error _ => false)
  match solveFull mxor with
  | some (some sol) =>
      st ← st.check "bool_xor: SAT witness accepted by the checker"
        (checkModelSolution mxor sol == .accepted)
  | _ => st ← st.check "bool_xor: SAT" false
  match solveFullLcg mxor with
  | some (some sol) =>
      st ← st.check "bool_xor: LCG route SAT, checker accepts"
        (checkModelSolution mxor sol == .accepted)
  | _ => st ← st.check "bool_xor: LCG route SAT" false
  st ← st.check "bool_xor: UNSAT instance refuted"
    (match solveFull (parseOrPanic xorUnsatSrc) with
     | some none => true | _ => false)
  st ← st.check "bool_xor: UNSAT through the LCG route"
    (match solveFullLcg (parseOrPanic xorUnsatSrc) with
     | some none => true | _ => false)
  -- PLAN C0 element values: the value-literal `array_int_element`
  -- over an all-literal table (constElemValL)
  let meu := parseOrPanic elemValSatSrc
  st ← st.check "constElemValL: compileModelFull accepts the shape"
    (match compileModelFull meu with | .ok _ => true | .error _ => false)
  st ← st.check "constElemValL: the compiled form IS the slot-table element"
    (match compileModelFull meu with
     | .ok p => elemValCompiledB p.constraints
     | .error _ => false)
  match solveFull meu with
  | some (some sol) =>
      st ← st.check "constElemValL: SAT witness accepted by the checker"
        (checkModelSolution meu sol == .accepted)
  | _ => st ← st.check "constElemValL: SAT" false
  match solveFullLcg meu with
  | some (some sol) =>
      st ← st.check "constElemValL: LCG route SAT, checker accepts"
        (checkModelSolution meu sol == .accepted)
  | _ => st ← st.check "constElemValL: LCG route SAT" false
  st ← st.check "constElemValL: UNSAT instance refuted"
    (match solveFull (parseOrPanic elemValUnsatSrc) with
     | some none => true | _ => false)
  st ← st.check "constElemValL: UNSAT through the LCG route"
    (match solveFullLcg (parseOrPanic elemValUnsatSrc) with
     | some none => true | _ => false)
  -- PLAN C0 element values: the one-literal mixed
  -- `array_var_int_element` table with a slot value (`varElemTabLit`)
  let mvt := parseOrPanic varElemTabSatSrc
  st ← st.check "varElemTabLit: compileModelFull accepts the shape"
    (match compileModelFull mvt with | .ok _ => true | .error _ => false)
  st ← st.check "varElemTabLit: the compiled form IS the slot-table element"
    (match compileModelFull mvt with
     | .ok p => varElemCompiledB [3, 1, 1] 0 2 p.constraints
     | .error _ => false)
  match solveFull mvt with
  | some (some sol) =>
      st ← st.check "varElemTabLit: SAT witness accepted by the checker"
        (checkModelSolution mvt sol == .accepted)
  | _ => st ← st.check "varElemTabLit: SAT" false
  match solveFullLcg mvt with
  | some (some sol) =>
      st ← st.check "varElemTabLit: LCG route SAT, checker accepts"
        (checkModelSolution mvt sol == .accepted)
  | _ => st ← st.check "varElemTabLit: LCG route SAT" false
  st ← st.check "varElemTabLit: UNSAT instance refuted"
    (match solveFull (parseOrPanic varElemTabUnsatSrc) with
     | some none => true | _ => false)
  st ← st.check "varElemTabLit: UNSAT through the LCG route"
    (match solveFullLcg (parseOrPanic varElemTabUnsatSrc) with
     | some none => true | _ => false)
  -- the same with a LITERAL value (`varElemTabValLit`)
  let mvv := parseOrPanic varElemValLitSatSrc
  st ← st.check "varElemTabValLit: compileModelFull accepts the shape"
    (match compileModelFull mvv with | .ok _ => true | .error _ => false)
  st ← st.check "varElemTabValLit: the compiled form IS the slot-table element"
    (match compileModelFull mvv with
     | .ok p => varElemCompiledB [2, 1, 1] 0 3 p.constraints
     | .error _ => false)
  match solveFull mvv with
  | some (some sol) =>
      st ← st.check "varElemTabValLit: SAT witness accepted by the checker"
        (checkModelSolution mvv sol == .accepted)
  | _ => st ← st.check "varElemTabValLit: SAT" false
  match solveFullLcg mvv with
  | some (some sol) =>
      st ← st.check "varElemTabValLit: LCG route SAT, checker accepts"
        (checkModelSolution mvv sol == .accepted)
  | _ => st ← st.check "varElemTabValLit: LCG route SAT" false
  st ← st.check "varElemTabValLit: UNSAT instance refuted"
    (match solveFull (parseOrPanic varElemValLitUnsatSrc) with
     | some none => true | _ => false)
  st ← st.check "varElemTabValLit: UNSAT through the LCG route"
    (match solveFullLcg (parseOrPanic varElemValLitUnsatSrc) with
     | some none => true | _ => false)
  -- multi-literal mixed tables are outside the classifier: still
  -- rejected
  -- PLAN C0 k-literal generalization: two-literal mixed tables (both
  -- value variants, literals separated by identifiers)
  let mkm := parseOrPanic varElemTabKsMultiSrc
  st ← st.check "varElemTabKs (k=2): compileModelFull accepts the shape"
    (match compileModelFull mkm with | .ok _ => true | .error _ => false)
  st ← st.check "varElemTabKs (k=2): the compiled form IS the slot-table element"
    (match compileModelFull mkm with
     | .ok p => varElemCompiledB [1, 3, 4, 2] 0 2 p.constraints
     | .error _ => false)
  match solveFull mkm with
  | some (some sol) =>
      st ← st.check "varElemTabKs (k=2): SAT witness accepted by the checker"
        (checkModelSolution mkm sol == .accepted)
  | _ => st ← st.check "varElemTabKs (k=2): SAT" false
  match solveFullLcg mkm with
  | some (some sol) =>
      st ← st.check "varElemTabKs (k=2): LCG route SAT, checker accepts"
        (checkModelSolution mkm sol == .accepted)
  | _ => st ← st.check "varElemTabKs (k=2): LCG route SAT" false
  st ← st.check "varElemTabKs (k=2): UNSAT instance refuted"
    (match solveFull (parseOrPanic varElemTabKsMultiUnsatSrc) with
     | some none => true | _ => false)
  st ← st.check "varElemTabKs (k=2): UNSAT through the LCG route"
    (match solveFullLcg (parseOrPanic varElemTabKsMultiUnsatSrc) with
     | some none => true | _ => false)
  let mvm := parseOrPanic varElemValKsMultiSrc
  st ← st.check "varElemTabValKs (k=2): compileModelFull accepts the shape"
    (match compileModelFull mvm with | .ok _ => true | .error _ => false)
  st ← st.check
    "varElemTabValKs (k=2): the compiled form IS the slot-table element"
    (match compileModelFull mvm with
     | .ok p => varElemCompiledB [1, 2, 3, 1] 0 4 p.constraints
     | .error _ => false)
  match solveFull mvm with
  | some (some sol) =>
      st ← st.check
        "varElemTabValKs (k=2): SAT witness accepted by the checker"
        (checkModelSolution mvm sol == .accepted)
  | _ => st ← st.check "varElemTabValKs (k=2): SAT" false
  match solveFullLcg mvm with
  | some (some sol) =>
      st ← st.check "varElemTabValKs (k=2): LCG route SAT, checker accepts"
        (checkModelSolution mvm sol == .accepted)
  | _ => st ← st.check "varElemTabValKs (k=2): LCG route SAT" false
  st ← st.check "varElemTabValKs (k=2): UNSAT instance refuted"
    (match solveFull (parseOrPanic varElemValKsMultiUnsatSrc) with
     | some none => true | _ => false)
  st ← st.check "varElemTabValKs (k=2): UNSAT through the LCG route"
    (match solveFullLcg (parseOrPanic varElemValKsMultiUnsatSrc) with
     | some none => true | _ => false)
  -- the head/tail two-literal table `[1, x, 3]` with the literal value
  -- `2` now compiles too (regression: it used to be rejected)
  let mhf := parseOrPanic varElemFollowUpSrc
  st ← st.check "varElem k=2 (head/tail literals): accepted"
    (match compileModelFull mhf with | .ok _ => true | .error _ => false)
  st ← st.check
    "varElem k=2 (head/tail literals): the compiled form IS the slot-table element"
    (match compileModelFull mhf with
     | .ok p => varElemCompiledB [2, 1, 3] 0 4 p.constraints
     | .error _ => false)
  -- PLAN C0 int follow-up: the all-slot table with a literal value
  let mva := parseOrPanic varElemValLitAllslotSrc
  st ← st.check "varElemTabValKs (all-slot table): compileModelFull accepts"
    (match compileModelFull mva with | .ok _ => true | .error _ => false)
  st ← st.check
    "varElemTabValKs (all-slot table): the compiled form IS the slot-table element"
    (match compileModelFull mva with
     | .ok p => varElemCompiledB [1, 1] 0 2 p.constraints
     | .error _ => false)
  match solveFull mva with
  | some (some sol) =>
      st ← st.check
        "varElemTabValKs (all-slot table): SAT witness checker-accepted"
        (checkModelSolution mva sol == .accepted)
  | _ => st ← st.check "varElemTabValKs (all-slot table): SAT" false
  match solveFullLcg mva with
  | some (some sol) =>
      st ← st.check
        "varElemTabValKs (all-slot table): LCG route SAT, checker accepts"
        (checkModelSolution mva sol == .accepted)
  | _ => st ← st.check "varElemTabValKs (all-slot table): LCG route SAT" false
  st ← st.check "varElemTabValKs (all-slot table): UNSAT refuted"
    (match solveFull (parseOrPanic varElemValLitAllslotUnsatSrc) with
     | some none => true | _ => false)
  st ← st.check
    "varElemTabValKs (all-slot table): UNSAT through the LCG route"
    (match solveFullLcg (parseOrPanic varElemValLitAllslotUnsatSrc) with
     | some none => true | _ => false)
  -- PLAN C0 bool tables: mixed bool tables (slot and literal values)
  -- and the all-slot table with a bool-literal value
  let mbl := parseOrPanic varBoolTabLitsSrc
  st ← st.check "varBoolTabLits: compileModelFull accepts the shape"
    (match compileModelFull mbl with | .ok _ => true | .error _ => false)
  st ← st.check
    "varBoolTabLits: the compiled form IS the bool slot-table element"
    (match compileModelFull mbl with
     | .ok p => varBoolElemCompiledB [3, 1, 2] 0 2 p.constraints
     | .error _ => false)
  match solveFull mbl with
  | some (some sol) =>
      st ← st.check "varBoolTabLits: SAT witness accepted by the checker"
        (checkModelSolution mbl sol == .accepted)
  | _ => st ← st.check "varBoolTabLits: SAT" false
  match solveFullLcg mbl with
  | some (some sol) =>
      st ← st.check "varBoolTabLits: LCG route SAT, checker accepts"
        (checkModelSolution mbl sol == .accepted)
  | _ => st ← st.check "varBoolTabLits: LCG route SAT" false
  st ← st.check "varBoolTabLits: UNSAT instance refuted"
    (match solveFull (parseOrPanic varBoolTabLitsUnsatSrc) with
     | some none => true | _ => false)
  st ← st.check "varBoolTabLits: UNSAT through the LCG route"
    (match solveFullLcg (parseOrPanic varBoolTabLitsUnsatSrc) with
     | some none => true | _ => false)
  let mbv := parseOrPanic varBoolTabValLitSrc
  st ← st.check "varBoolTabValLit: compileModelFull accepts the shape"
    (match compileModelFull mbv with | .ok _ => true | .error _ => false)
  st ← st.check
    "varBoolTabValLit: the compiled form IS the bool slot-table element"
    (match compileModelFull mbv with
     | .ok p => varBoolElemCompiledB [2, 1, 3] 0 4 p.constraints
     | .error _ => false)
  match solveFull mbv with
  | some (some sol) =>
      st ← st.check "varBoolTabValLit: SAT witness accepted by the checker"
        (checkModelSolution mbv sol == .accepted)
  | _ => st ← st.check "varBoolTabValLit: SAT" false
  match solveFullLcg mbv with
  | some (some sol) =>
      st ← st.check "varBoolTabValLit: LCG route SAT, checker accepts"
        (checkModelSolution mbv sol == .accepted)
  | _ => st ← st.check "varBoolTabValLit: LCG route SAT" false
  st ← st.check "varBoolTabValLit: UNSAT instance refuted"
    (match solveFull (parseOrPanic varBoolTabValLitUnsatSrc) with
     | some none => true | _ => false)
  st ← st.check "varBoolTabValLit: UNSAT through the LCG route"
    (match solveFullLcg (parseOrPanic varBoolTabValLitUnsatSrc) with
     | some none => true | _ => false)
  let mbv0 := parseOrPanic varBoolValLitAllslotSrc
  st ← st.check "varBoolTabValLit (all-slot table): accepted"
    (match compileModelFull mbv0 with | .ok _ => true | .error _ => false)
  st ← st.check
    "varBoolTabValLit (all-slot table): the compiled form IS the bool slot-table element"
    (match compileModelFull mbv0 with
     | .ok p => varBoolElemCompiledB [1, 1] 0 2 p.constraints
     | .error _ => false)
  match solveFull mbv0 with
  | some (some sol) =>
      st ← st.check
        "varBoolTabValLit (all-slot table): SAT witness checker-accepted"
        (checkModelSolution mbv0 sol == .accepted)
  | _ => st ← st.check "varBoolTabValLit (all-slot table): SAT" false
  match solveFullLcg mbv0 with
  | some (some sol) =>
      st ← st.check
        "varBoolTabValLit (all-slot table): LCG route SAT, checker accepts"
        (checkModelSolution mbv0 sol == .accepted)
  | _ => st ← st.check "varBoolTabValLit (all-slot table): LCG route SAT" false
  st ← st.check "varBoolTabValLit (all-slot table): UNSAT refuted"
    (match solveFull (parseOrPanic varBoolValLitAllslotUnsatSrc) with
     | some none => true | _ => false)
  st ← st.check "varBoolTabValLit (all-slot table): UNSAT through the LCG route"
    (match solveFullLcg (parseOrPanic varBoolValLitAllslotUnsatSrc) with
     | some none => true | _ => false)
  -- scalar models: the full front end agrees with compileModel
  let ms := parseOrPanic scalarSrc
  st ← st.check "scalar model: compileModelFull accepts like compileModel"
    (match compileModel ms, compileModelFull ms with
     | .ok _, .ok _ => true | _, _ => false)
  IO.println s!"passed {st.passed}, failed {st.failed}"
  return if st.failed == 0 then 0 else 1

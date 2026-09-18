import solver.Solver

/-!
# Solver smoke benchmark (PLAN.md 6.8)

A small performance sanity check for the phase-1 solver stack, in the
spirit of PLAN 6.8's "one benchmark per solver layer":

* **Correctness (the PASS criteria)** — the propagating solver
  (`solveModelProp`) and the MRV solver (`solveModelHeur`) agree with
  the reference solver (`solveModel`) on the verdict of every
  benchmark model, and every `.sat` text they return is accepted by
  the verified checker.  These are regression criteria.

* **Timings (informational only)** — reference vs. propagated vs.
  MRV wall-clock times on the same models, printed with
  `IO.monoMsNow`.  Absolute times are machine-dependent and are NOT
  regression thresholds; the printed numbers only make the pruning
  effect visible (on the pigeonhole model the propagating solver
  refutes at the root while the reference solver enumerates).

* **A generous wall-clock guard** — the whole benchmark must finish
  within 10 seconds, to catch pathological blowups only (a broken
  search looping, a fuel explosion), not slow machines.

The models: a pigeonhole UNSAT instance (4 variables over 3 values
with all pairwise `int_ne` — every constraint extracted, so the
propagating solver prunes), a satisfiable chain model
(`int_eq`/`int_le` chains), a larger satisfiable pigeonhole (5 over 4),
and a global-only model (`fzn_all_different_int`, nothing extracted —
the fallback path).
-/

open LeanFzn LeanFzn.Solver LeanFzn.Check LeanFzn.Solution LeanFzn.Globals

private def parseOrPanic (src : String) : Model :=
  match Parser.parseModel src with
  | .ok m => m
  | .error e => panic! s!"unexpected parse error: {e}"

/-- One benchmark run: solve with all three entry points, print the
    timings, and check verdict agreement plus checker acceptance of
    any returned text. -/
private def runBench (st : IO.Ref Nat) (name : String) (src : String)
    (fuel : Nat) : IO Bool := do
  let m := parseOrPanic src
  -- reference
  let t0 ← IO.monoMsNow
  let rref := solveModel m
  let t1 ← IO.monoMsNow
  -- propagated
  let t2 ← IO.monoMsNow
  let rprop := solveModelProp fuel m
  let t3 ← IO.monoMsNow
  -- MRV
  let t4 ← IO.monoMsNow
  let rheur := solveModelHeur m
  let t5 ← IO.monoMsNow
  IO.println s!"bench {name}: reference {t1 - t0} ms, propagated {t3 - t2} ms, \
mrv {t5 - t4} ms"
  -- verdict agreement: same sat/unsat classification
  let verdict (r : SolveResult) : String :=
    match r with | .sat _ => "sat" | .unsat => "unsat" | .unsupported _ => "unsupported"
  let okAgree := verdict rref == verdict rprop && verdict rref == verdict rheur
  if !okAgree then
    IO.eprintln s!"FAIL bench {name}: verdicts disagree \
({verdict rref} / {verdict rprop} / {verdict rheur})"
  -- sat texts are checker-accepted
  let mut okSat := true
  match rref with
  | .sat text => if checkModelSolution m text != .accepted then okSat := false
  | _ => pure ()
  match rprop with
  | .sat text => if checkModelSolution m text != .accepted then okSat := false
  | _ => pure ()
  match rheur with
  | .sat text => if checkModelSolution m text != .accepted then okSat := false
  | _ => pure ()
  if !okSat then
    IO.eprintln s!"FAIL bench {name}: a returned sat text was rejected"
  if okAgree && okSat then
    IO.println s!"ok bench {name} ({verdict rref})"
    st.modify (· + 1)
  return okAgree && okSat

/-- Build `n` variables over `1..k` with all pairwise `int_ne`. -/
private def pigeonholeSrc (n k : Nat) : String :=
  let pairs := (List.range n).flatMap (fun i =>
    (List.range n).filterMap (fun j => if i < j then some (i, j) else none))
  let decls := (List.range n).foldl (fun acc i =>
    acc ++ s!"var 1..{k}: p{i};\n") ""
  let cons := pairs.foldl (fun acc p =>
    acc ++ s!"constraint int_ne(p{p.1}, p{p.2});\n") ""
  decls ++ cons ++ "solve satisfy;"

def main : IO UInt32 := do
  let start ← IO.monoMsNow
  let passed ← IO.mkRef 0
  let mut allOk := true

  -- pigeonhole 4 pigeons / 3 holes: UNSAT, all constraints extracted
  let ok1 ← runBench passed "pigeonhole-4-3 (unsat)"
    (pigeonholeSrc 4 3) 50
  allOk := allOk && ok1

  -- satisfiable chain: x = y, x ≤ y, y = z on 1..40
  let chain :=
    "var 1..40: x;\nvar 1..40: y;\nvar 1..40: z;\n\
     constraint int_eq(x, y);\nconstraint int_le(x, y);\n\
     constraint int_eq(y, z);\nsolve satisfy;"
  let ok2 ← runBench passed "chain (sat)" chain 50
  allOk := allOk && ok2

  -- pigeonhole 5 pigeons / 4 holes: UNSAT, bigger
  let ok3 ← runBench passed "pigeonhole-5-4 (unsat)"
    (pigeonholeSrc 5 4) 50
  allOk := allOk && ok3

  -- global-only model: nothing extracted (the fallback path)
  let alldiff :=
    "var 1..6: x;\nvar 1..6: y;\nvar 1..6: z;\nvar 1..6: w;\n\
     constraint fzn_all_different_int([x, y, z, w]);\nsolve satisfy;"
  let ok4 ← runBench passed "alldiff-only (sat, fallback)" alldiff 50
  allOk := allOk && ok4

  let elapsed ← IO.monoMsNow
  let total := elapsed - start
  IO.println s!"bench total wall clock: {total} ms"
  if !allOk then
    IO.eprintln "solver benchmark FAILED"
    return 1
  -- generous wall-clock guard: 10 seconds to catch pathological blowups
  if total > 10000 then
    IO.eprintln s!"solver benchmark FAILED: {total} ms exceeds the 10000 ms guard"
    return 1
  let n ← passed.get
  IO.println s!"passed {n} solver benchmark checks"
  return 0

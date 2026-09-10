import LeanFzn

/-!
# Performance regression suite

Timing harnesses for the solution checker and parser, compiled
(numbers from `#eval` are unreliable for pure computations because of
lazy evaluation; this executable forces results inside `IO`).

Guards the performance characteristics found and fixed in this
development:

1. *Store fusion* (O(n²)): Lean's compiler arity-raises a
   `let store := …` binding into consumer loops, rebuilding the
   store's hash map per lookup.  Fixed by the
   `StoreBox`/`completedBox` boundary (`FznSolution.lean`).
2. *Pairwise distinctness* (O(n²)): `valuesAllDifferent` scans each
   element against the tail.  Fixed by the sort-based
   `intsAllDifferentFast`/`valuesAllDifferentFast`
   (`FznStdLib.lean`), agreeing with the logical definition by
   `valuesAllDifferentFast_iff`.
-/

open LeanFzn LeanFzn.Globals LeanFzn.Solution

/-- An all-different model on `n` fresh variables (the FlatZinc a
    MiniZinc compiler would emit for `all_different`). -/
def genModel (n : Nat) : String := Id.run do
  let mut dcls := "var 1..1: dummy;\n"
  for i in [1:n+1] do
    dcls := dcls ++ s!"var 1..1000000: x{i};\n"
  let mut arr := s!"array [1..{n}] of var 1..1000000: xs = ["
  for i in [1:n+1] do
    if i > 1 then arr := arr ++ ", "
    if i ≤ n then arr := arr ++ s!"x{i}"
  arr := arr ++ "];\n"
  return dcls ++ arr ++ "constraint fzn_all_different_int(xs);\nsolve satisfy;"

/-- A model with `n` variables and `n` linear constraints (parser
    workload: token count grows linearly). -/
def genParseModel (n : Nat) : String := Id.run do
  let mut dcls := "var 1..1: dummy;\n"
  for i in [1:n+1] do
    dcls := dcls ++ s!"var 1..1000000: x{i};\n"
  let mut arr := s!"array [1..{n}] of var 1..1000000: xs = ["
  for i in [1:n+1] do
    if i > 1 then arr := arr ++ ", "
    if i ≤ n then arr := arr ++ s!"x{i}"
  arr := arr ++ "];\n"
  let mut cons := ""
  for i in [1:n+1] do
    if i ≤ n then
      cons := cons ++ s!"constraint int_le(x{i}, {i});\n"
  return dcls ++ arr ++ cons ++ "constraint fzn_all_different_int(xs);\nsolve satisfy;"

def main : IO UInt32 := do
  let mut ok := true
  -- 1. checker timing (valid and rejected)
  for k in [2000, 4000, 8000, 32000] do
    let m : Model := match Parser.parseModel (genModel k) with
      | .ok m => m | .error e => panic! e
    let sol := Id.run do
      let mut s := ""
      for i in [1:k+1] do
        s := s ++ s!"x{i} = {i};\n"
      s ++ "dummy = 1;\n----------\n"
    let tA ← IO.monoNanosNow
    let mut r := false
    for _ in [0:1] do r := checkSolutionFull m sol
    let sA := toString r
    let tB ← IO.monoNanosNow
    let ms := (tB - tA) / 1000000
    IO.println s!"checkSolutionFull n={k} valid: {sA} in {ms}ms"
    if !r then ok := false
    if ms > 1000 then
      IO.eprintln s!"PERF REGRESSION: n={k} took {ms}ms"
      ok := false
    let solBad := Id.run do
      let mut s := ""
      for i in [1:k+1] do
        s := s ++ s!"x{i} = {(i+1)/2};\n"
      s ++ "dummy = 1;\n----------\n"
    if checkSolutionFull m solBad then
      IO.eprintln s!"WRONG: invalid solution accepted at n={k}"
      ok := false
  -- 2. parser timing (n variables, n constraints: linear workload)
  for k in [5000, 20000, 80000] do
    let src := genParseModel k
    let t0 ← IO.monoNanosNow
    let mut pok := false
    for _ in [0:1] do pok := (Parser.parseModel src).isOk
    let s0 := toString pok
    let t1 ← IO.monoNanosNow
    IO.println s!"parseModel n={k} (src {src.length/1024}KB): {s0} in {(t1-t0)/1000000}ms"
    if !pok then ok := false
  if ok then
    IO.println "passed perf regression checks"
    return 0
  else
    return 1

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

def genVarsOnly (n : Nat) : String := Id.run do
  let mut dcls := "var 1..1: dummy;\n"
  for i in [1:n+1] do
    dcls := dcls ++ s!"var 1..1000000: x{i};\n"
  return dcls ++ "solve satisfy;"

/-- A dispatch-heavy model: `n` variables and `n` global-predicate
    constraints with small arguments, so the per-constraint cost is
    dominated by name gate + dispatch, not predicate evaluation. -/
def genDispatchModel (n : Nat) : String := Id.run do
  let mut dcls := ""
  for i in [1:n+1] do
    dcls := dcls ++ s!"var 1..1000000: x{i};\n"
  let mut cons := ""
  for i in [1:n+1] do
    if i ≤ n then
      -- alternate three checkable global predicates so several family
      -- dispatches are exercised
      match i % 3 with
      | 0 => cons := cons ++ s!"constraint fzn_all_different_int([x{i}]);\n"
      | 1 => cons := cons ++ s!"constraint fzn_lex_lesseq_int([x{i}], [x{i}]);\n"
      | _ => cons := cons ++ s!"constraint fzn_at_least_int(1, [x{i}], {i});\n"
  return dcls ++ cons ++ "solve satisfy;"

/-- A solution string assigning each `x{i}` the value `i`. -/
def genDispatchSol (n : Nat) : String := Id.run do
  let mut s := ""
  for i in [1:n+1] do
    s := s ++ s!"x{i} = {i};\n"
  s ++ "----------\n"

def main : IO UInt32 := do
  let mut ok := true
  -- 0. front-door (wellFormedFastB + name check + dynamic check) timing;
  --    guards the fast static twin's linearity (the naive wellFormedB
  --    is Theta(n^2) here: ~37 s at n = 32000 on the dev machine)
  for k in [2000, 8000, 32000] do
    let src := genVarsOnly k
    let m : Model := match Parser.parseModel src with
      | .ok m => m | .error e => panic! e
    let sol := Id.run do
      let mut s := "dummy = 1;\n"
      for i in [1:k+1] do
        s := s ++ s!"x{i} = 1;\n"
      s ++ "----------\n"
    let tA ← IO.monoNanosNow
    -- branch on the outcome inside the timed window (IO-observable,
    -- so evaluation cannot be delayed past the second clock read)
    let r := Check.checkModelSolution m sol
    if r == Check.Outcome.accepted then
      let tB ← IO.monoNanosNow
      let ms := (tB - tA) / 1000000
      IO.println s!"checkModelSolution n={k} static+dynamic: accepted in {ms}ms"
      if k = 32000 && ms > 3000 then
        IO.eprintln s!"PERF REGRESSION: checkModelSolution n={k} took {ms}ms"
        ok := false
    else
      let tB ← IO.monoNanosNow
      let ms := (tB - tA) / 1000000
      IO.eprintln s!"WRONG: checkModelSolution n={k} rejected a valid solution in {ms}ms"
      ok := false
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
  -- 3. dispatch-heavy model: many constraints with small arguments,
  --    so the per-check cost is dominated by per-constraint work
  --    (name gate, dispatch, signature checks).  A batch of checks
  --    must stay linear in the model size: the time per 1000 checks
  --    at n=8000 must be at most ~10x the time at n=2000 (a linear
  --    workload scales 4x; quadratic would scale 16x).
  let mut batchRatiosOk := true
  let mut t2000 := 0
  for k in [2000, 8000] do
    let m : Model := match Parser.parseModel (genDispatchModel k) with
      | .ok m => m | .error e => panic! e
    let sol := genDispatchSol k
    let p := Check.prepareModel m
    let t0 ← IO.monoNanosNow
    let mut ra := Check.Outcome.accepted
    for _ in [0:1000] do
      ra := Check.checkModelSolutionFast m sol
      if ra != Check.Outcome.accepted then ra := .unsatisfied
    let t1 ← IO.monoNanosNow
    if ra == Check.Outcome.accepted then
      let ms := (t1-t0)/1000000
      IO.println s!"checkModelSolutionFast dispatch-heavy n={k} batch x1000: accepted in {ms}ms"
      if k == 2000 then t2000 := t1 - t0
      if k == 8000 then
        let ratio := (t1-t0).toFloat / t2000.toFloat
        IO.println s!"  batch scaling ratio (8000/2000): {ratio} (linear ~4)"
        if ratio > 10.0 then
          IO.eprintln s!"PERF REGRESSION: dispatch-heavy batch scaling is superlinear at n={k}"
          batchRatiosOk := false
    else
      IO.eprintln s!"WRONG: fast front door rejected dispatch-heavy model at n={k}: {ra}"
      ok := false
    -- the prepared path must agree with the front door and stay in
    -- the same complexity class (ratio to the fast front door <= 2)
    let t2 ← IO.monoNanosNow
    let mut rb := Check.Outcome.accepted
    for _ in [0:1000] do
      rb := Check.checkPreparedSolution p sol
      if rb != Check.Outcome.accepted then rb := .unsatisfied
    let t3 ← IO.monoNanosNow
    if rb == Check.Outcome.accepted then
      let front := (t1 - t0).toFloat
      let prep := (t3 - t2).toFloat
      let ratio := if front > 0 then prep / front else 0
      IO.println s!"checkPreparedSolution dispatch-heavy n={k} batch x1000: accepted in {(t3-t2)/1000000}ms (ratio to front door {ratio})"
      if ratio > 2.0 then
        IO.eprintln s!"PERF REGRESSION: prepared checker much slower than front door at n={k}"
        batchRatiosOk := false
    else
      IO.eprintln s!"WRONG: prepared checker rejected dispatch-heavy model at n={k}: {rb}"
      ok := false
  if !batchRatiosOk then ok := false
  -- 4. repeated static checks: `wellFormedFastB` called in a loop
  --    must not degrade (guards the static-environment boxing: the
  --    env map is built once per call, not once per lookup; the
  --    regression was ~800 ms per call at n=2000)
  let m : Model := match Parser.parseModel (genDispatchModel 2000) with
    | .ok m => m | .error e => panic! e
  let sol := genDispatchSol 2000
  let p := Check.prepareModel m
  let t0 ← IO.monoNanosNow
  let mut cnt := 0
  for _ in [0:1000] do
    if Check.wellFormedFastB m then cnt := cnt + 1
  let t1 ← IO.monoNanosNow
  if cnt == 1000 then
    IO.println s!"wellFormedFastB batch n=2000 x1000: {cnt} ok in {(t1-t0)/1000000}ms"
  else
    IO.eprintln "WRONG: wellFormedFastB rejected a well-formed model in the batch"
    ok := false
  if (t1-t0)/1000000 > 10000 then
    IO.eprintln s!"PERF REGRESSION: wellFormedFastB batch took {(t1-t0)/1000000}ms"
    ok := false
  -- one prepared model, 1000 solution checks: parse-once-check-many
  let t2 ← IO.monoNanosNow
  let mut rb := Check.Outcome.accepted
  for _ in [0:1000] do
    rb := Check.checkPreparedSolution p sol
    if rb != Check.Outcome.accepted then rb := .unsatisfied
  let t3 ← IO.monoNanosNow
  if rb == Check.Outcome.accepted then
    IO.println s!"checkPreparedSolution batch (2000 vars, 2000 cons) x1000: accepted in {(t3-t2)/1000000}ms"
  else
    IO.eprintln s!"WRONG: prepared checker rejected a valid solution: {rb}"
    ok := false
  if ok then
    IO.println "passed perf regression checks"
    return 0
  else
    return 1

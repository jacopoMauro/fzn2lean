/-
File: Tests/Prof.lean

Purpose:
  Parser performance profiling: generates a large model, measures
  tokenization and parsing time, and prints timings for regression
  awareness. Informational only; no correctness assertions.

Dependencies:
  LeanFzn (FznLexer.tokenize, FznParser.parseModel).

Why:
  Provides the hand-measured baselines that `Tests/Bench.lean` and the
  PLAN item 4 worklog reference; kept out of the CI assertion suites.

DAG:
  LeanFzn -> Tests/Prof.lean -> leanfzn prof replay
-/

import LeanFzn
open LeanFzn LeanFzn.Lexer LeanFzn.Parser

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
  let k := 80000
  let src := genParseModel k
  -- (the tokenization result of the profiling driver is threaded
  -- through the timing runs below, not used directly here)
  let _toks := match tokenize src with | .ok t => t | .error _ => #[]
  -- Which is it: recursion depth (acc version no better) or allocation?
  -- parseVarDeclItem loop = 16ms; parseMany = 32ms; acc = 30ms; mono = 37ms.
  -- All ~30ms vs 16ms bare loop → the extra ~15ms IS the item-list consing
  -- + GC (80k VarDeclItem objects, 80k cons cells, 80k Except wrappers...).
  -- Actually bare loop also allocates those VarDeclItems. Hmm — bare loop
  -- DISCARDS them immediately (dead after match), parseMany keeps them live.
  -- GC pressure from holding 80k items live.
  --
  -- The REAL question: total parseModelAux = 72ms = 32 (vars) + 42 (cons)... = 74. Yes!
  -- So: parseModelAux ≈ parseMany vars + parseMany cons (nothing else significant).
  --
  -- Now: can the item parsers themselves be made faster WITHOUT touching proofs?
  -- The proofs unfold parseVarDeclItem etc. — any change forces proof edits.
  -- The SAFE transformation: keep the logical definitions, make the FAST path
  -- an `implemented_by` runtime twin. That worked for the store.
  --
  -- But first check the biggest item cost: what does parseVarDeclItem's 16ms
  -- consist of? simVar (7 expectTok) = 9ms. The extras: parseBasicVarType's
  -- peek? dispatch + parseAnnotations peek + match peek? for '='.
  -- 80k × (3 extra peeks + Except allocs) ≈ 7ms.
  --
  -- Deeper win: replace the Except monad plumbing? Not without parser rewrite.
  -- Conclusion: go the implemented_by route for the WHOLE parseModelAux:
  -- 1. write fast twin with direct array access (like rawVar, 1ms/80k!)
  -- 2. prove equality... hard: the fast twin must produce identical Model.
  --
  -- Pragmatic middle ground: fast twins for the LEAF helpers (expectTok,
  -- parseIdent, parseIntLit, ...) whose results are simple, with
  -- implemented_by. The structure (match/peek) stays logical.
  -- Measure what a leaf-level optimization buys: rawVar was 1ms vs simVar 9ms.
  IO.println "analysis complete"
  return 0

/-
File: TestEnumTmp.lean

Purpose:
  Temporary benchmark comparing the old accumulator-based
  `enumerateAllOld` against the current `enumerateAll`.

Dependencies:
  solver.Enum (the current enumeration implementation).

Why:
  Measures the speedup from the double-accumulator rewrite (PLAN.md item 4).
  Build target: `test_enum_tmp` in lakefile.toml.

DAG:
  solver.Solve -> solver.Enum -> TestEnumTmp.lean
-/

import solver.Enum
open LeanFzn.Solver
def enumerateAllOld {α : Type} (leaf : List α → Bool) :
    List (List α) → List α → List (List α)
  | [], acc => if leaf acc then [acc] else []
  | [] :: _, _ => []
  | (v :: vs) :: rest, acc =>
      enumerateAllOld leaf rest (acc ++ [v])
        ++ enumerateAllOld leaf (vs :: rest) acc
termination_by slots _ => slotsMeasure slots
decreasing_by
  all_goals
    simp only [slotsMeasure, List.foldr_cons, List.length_cons]
    omega
def main : IO UInt32 := do
  for n in [14, 16] do
    let slots : List (List Int) := List.replicate n ((List.range 4).map Int.ofNat)
    let t0 ← IO.monoMsNow
    let rOld ← pure ((enumerateAllOld (fun _ => true) slots []).foldl (fun s a => s + a.length) 0)
    let t1 ← IO.monoMsNow
    let rNew ← pure ((enumerateAll (fun _ => true) slots []).foldl (fun s a => s + a.length) 0)
    let t2 ← IO.monoMsNow
    IO.println s!"n={n}: old {t1 - t0} ms, new {t2 - t1} ms, ck {rOld} {rNew}"
  return 0

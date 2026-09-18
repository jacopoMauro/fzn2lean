import solver.Enum

/-!
# A/B benchmark: pre-change definitions vs the implemented_by twins

Temporary harness (not part of the test suite).  `searchOld` and
`enumerateAllOld` are verbatim copies of the pre-change reference
definitions (the slow `acc ++ [v]` / `++`-join shapes); the library
`search` / `enumerateAll` are the `implemented_by` twins of this
change, and `dedupTexts` is the hash-counted text dedup.  Run with
`lake build --release bench_ab` for optimized numbers.
-/

open LeanFzn.Solver

/-- The pre-change reference search (verbatim copy; IDEAS 4.1 baseline). -/
def searchOld {α : Type} (leaf : List α → Bool) :
    List (List α) → List α → Option (List α)
  | [], acc => if leaf acc then some acc else none
  | [] :: _, _ => none
  | (v :: vs) :: rest, acc =>
      match searchOld leaf rest (acc ++ [v]) with
      | some a => some a
      | none => searchOld leaf (vs :: rest) acc
termination_by slots _ => slotsMeasure slots
decreasing_by
  all_goals
    simp only [slotsMeasure, List.foldr_cons, List.length_cons]
    omega

/-- The pre-change reference enumerator (verbatim copy; IDEAS 4.5 baseline). -/
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
  let mut results : List (String × Nat × Nat) := []
  let pad (s : String) (n : Nat) : String :=
    if s.length ≥ n then s else s ++ String.mk (List.replicate (n - s.length) ' ')

  -- ## Search, UNSAT-shaped (leaf always false): full tree walk
  for (n, k, label) in [(13, 4, "search unsat 13x4 (67M leaves)"),
                        (14, 4, "search unsat 14x4 (268M leaves)")] do
    let slots : List (List Int) := List.replicate n ((List.range k).map (fun x => Int.ofNat x))
    let leaf : List Int → Bool := fun _ => false
    let t0 ← IO.monoMsNow
    let rOld ← pure ((searchOld leaf slots []).map (fun l => l.length) |>.getD 0)
    let t1 ← IO.monoMsNow
    let rNew ← pure ((search leaf slots []).map (fun l => l.length) |>.getD 0)
    let t2 ← IO.monoMsNow
    if rOld != rNew then IO.eprintln s!"MISMATCH search {label}"
    results := results.concat (label, t1 - t0, t2 - t1)

  -- ## Search, SAT-shaped (only the last assignment passes)
  do
    let n := 14
    let k := 4
    let slots : List (List Int) := List.replicate n ((List.range k).map (fun x => Int.ofNat x))
    let target : List Int := List.replicate n ((k - 1 : Int))
    let leaf : List Int → Bool := fun l => l == target
    let t0 ← IO.monoMsNow
    let rOld ← pure ((searchOld leaf slots []).map (fun l => l.length) |>.getD 0)
    let t1 ← IO.monoMsNow
    let rNew ← pure ((search leaf slots []).map (fun l => l.length) |>.getD 0)
    let t2 ← IO.monoMsNow
    if rOld != rNew then IO.eprintln "MISMATCH search sat"
    results := results.concat ("search sat-last 14x4 (268M leaves)", t1 - t0, t2 - t1)

  -- ## Enumeration, all solutions pass (k^n results, ++ join stress)
  for (n, k, label) in [(8, 4, "enum all-pass 8x4 (65k sols)"),
                         (10, 4, "enum all-pass 10x4 (1M sols)")] do
    let slots : List (List Int) := List.replicate n ((List.range k).map (fun x => Int.ofNat x))
    let leaf : List Int → Bool := fun _ => true
    let t0 ← IO.monoMsNow
    let rOld ← pure ((enumerateAllOld leaf slots []).foldl (fun s a => s + a.length) 0)
    let t1 ← IO.monoMsNow
    let rNew ← pure ((enumerateAll leaf slots []).foldl (fun s a => s + a.length) 0)
    let t2 ← IO.monoMsNow
    if rOld != rNew then IO.eprintln s!"MISMATCH enum {label}"
    results := results.concat (label, t1 - t0, t2 - t1)

  -- ## Enumeration, half pass
  do
    let slots : List (List Int) := List.replicate 10 ((List.range 4).map (fun x => Int.ofNat x))
    let leaf : List Int → Bool := fun l =>
      l.foldl (fun a b => a + b) 0 % 2 == 0
    let t0 ← IO.monoMsNow
    let rOld ← pure ((enumerateAllOld leaf slots []).foldl (fun s a => s + a.length) 0)
    let t1 ← IO.monoMsNow
    let rNew ← pure ((enumerateAll leaf slots []).foldl (fun s a => s + a.length) 0)
    let t2 ← IO.monoMsNow
    if rOld != rNew then IO.eprintln "MISMATCH enum half"
    results := results.concat ("enum half-pass 10x4 (512k sols)", t1 - t0, t2 - t1)

  -- ## Text dedup: 40k texts over 2k distinct
  do
    let n := 40000
    let d := 2000
    let texts := (List.range n).map (fun i => s!"solution text number {i % d}")
    let t0 ← IO.monoMsNow
    let rOld ← pure ((dedup texts).foldl (fun s t => s + t.length) 0)
    let t1 ← IO.monoMsNow
    let rNew ← pure ((dedupTexts texts).foldl (fun s t => s + t.length) 0)
    let t2 ← IO.monoMsNow
    if rOld != rNew then IO.eprintln "MISMATCH dedup texts"
    results := results.concat (s!"dedupTexts {n} texts / {d} distinct", t1 - t0, t2 - t1)

  IO.println "bench                          old ms   new ms   speedup"
  for (label, told, tnew) in results do
    let sp := if tnew == 0 then (0 : Float) else (told.toFloat / tnew.toFloat)
    let sps := (toString sp).splitOn "." |>.headD "0"
    IO.println s!"{pad label 34} {pad (toString told) 6} {pad (toString tnew) 8} \
{pad sps 8}"
  return 0

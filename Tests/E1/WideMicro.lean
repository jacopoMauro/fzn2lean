/-
File: Tests/E1/WideMicro.lean

Purpose (PLAN task M1 closure, TEST-ONLY, UNCERTIFIED): the wide-domain
microbenchmark evidence for the wave-2 fused/cached domain operations
(`Tests/E1/HeurTiming.lean` is the style template) and the measured memory
overhead of the per-scan summaries.

Everything is measured in-process with `IO.monoNanosNow` + `IO.lazyPure`
(nothing is dead-code eliminated) inside the compiled native `tests_wide_micro`.
No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; nothing here is part of
the certified route.

Measured:

  1. LITERAL CHECKS. `literalImpossible` (certified full domain walk) vs
     `literalImpossibleFast` with `sumsOfArray`, on synthetic int/bool/mixed
     domains of width 64/256/1024/39424: ns per check and the number of domain
     values each side examines. Counting twins below mirror the certified
     recursion and `List.all`'s early exit (and the fast O(1) shapes).
  2. CLAUSE CLASSIFICATION. 200 synthetic clauses x 7 order/pin literals over
     four wide int slots (plus bool/mixed slots): `scanDatabase` vs the wired
     hybrid `scanDatabaseFast` (indexed branch above 8 clauses): ns, total
     domain-value visits, event agreement, and a db-size sweep that re-checks
     the 8-clause crossover.
  3. CACHE BUILD OVERHEAD. `sumsOfArray (frameDomainArray f)` alone: ns, its
     share of the fast scan, and the amortisation ratio (reference visits /
     summary-build values).
  4. MEMORY OVERHEAD. Kernel-checked `sizeOf` of a `SlotSum` (structural units;
     the toolchain cannot EXECUTE derived `SizeOf` instances — elaboration
     reports "Failed to find LCNF signature for Option._sizeOf_inst" — so the
     number is checked by `decide` and reported as a literal) plus measured
     RSS deltas: the recorded 1HZ5 shape (169 slots, Σ|d| = 3,272,799, PLAN §1)
     for the frame / slot index / summaries, and a 400k-summary batch for
     bytes per slot. `audits/benchmark_performance.py` separately captures the
     1024-width fixture peak RSS.
  5. HEURISTIC SORT. `sortDom`'s `uniformKeysB` fast path vs the
     `sortDom`-equivalent reference mergeSort on flat-activity wide domains
     (1024/39424), plus a non-uniform hot-pin control.

The 39424-width full walks are kept: the largest single reference scan is ~40M
value visits (~0.5 s, repetition count 3), well inside the 300 s per-process
budget; repetition counts are scaled down with the width so every timed window
stays small (the whole executable runs in ~7 s).

Run compiled:  .lake/build/bin/tests_wide_micro
-/
import LeanFzn.Legacy.Solver.Propagation.DbScanIndex
import LeanFzn.Legacy.Integration.LcgHeur

open LeanFzn.Semantics LeanFzn.Solver.Propagation LeanFzn.Solver.Core
open LeanFzn.Integration.LcgHeur

namespace Tests.E1.WideMicro

abbrev DomC := LeanFzn.Solver.Propagation.DomainFiltering.DomConstraint

/-! ## 1. Clocks, printing, small helpers -/

/-- Flushed print. -/
def say (s : String) : IO Unit := do
  IO.println s
  (← IO.getStdout).flush

/-- Best (minimum) of `windows` timed single executions of `act`, PLUS the
result of the last execution. The result is RETURNED and must be used by the
caller (printed): discarding the result of `IO.lazyPure` lets the optimizer
delete the whole pure call inside the window (observed: 20 ns windows for a
39M-visit scan), so `act i` also receives the window index, which callers use
to vary the workload. -/
def bestNs {α : Type} (windows : Nat) (act : Nat → α) (init : α) : IO (Nat × α) := do
  let mut best := 0
  let mut res := init
  for i in List.range windows do
    let t0 ← IO.monoNanosNow
    let r ← IO.lazyPure (fun _ => act i)
    let t1 ← IO.monoNanosNow
    res := r
    let ns := t1 - t0
    if best == 0 || ns < best then best := ns
  return (best, res)

/-- `l` rotated left by `k % l.length` (fresh list; makes a timed scan
workload depend on the window index so it cannot be hoisted out). -/
def rot {α : Type} (l : List α) (k : Nat) : List α :=
  if l.isEmpty then l else l.drop (k % l.length) ++ l.take (k % l.length)

/-- Current resident set size in KiB from `/proc/self/status` (none when the
file is unreadable). -/
def rssKiB : IO (Option Nat) := do
  try
    let s ← IO.FS.readFile "/proc/self/status"
    let rec go : List String → Option Nat
      | [] => none
      | ln :: rest =>
        if ln.startsWith "VmRSS:" then
          match ((ln.drop 6).toString.trimAscii.toString.splitOn " ").filter (fun x => !x.isEmpty) with
          | n :: _ => n.toNat?
          | [] => none
        else go rest
    return go (s.splitOn "\n")
  catch _ => return none

/-- Non-negative RSS delta in KiB. -/
def rssDelta (r0 r1 : Option Nat) : Nat :=
  match r0, r1 with
  | some a, some b => b - a
  | _, _ => 0

/-! ## 2. Synthetic domains, frames, literals, clauses -/

/-- `[0, 1, ..., w-1]` as integers. -/
def intDom (w : Nat) : Domain :=
  Dom.ofList ((List.range w).map (fun i : Nat => Value.int (i : Int)))

/-- `[off, off+1, ..., off+w-1]` as integers: distinct offsets give distinct
(hence unshareable) lists of the same width. Needed for the RSS phase: repeated
`intDom w` calls with the SAME constant `w` are hoisted by the compiler into a
`lean_obj_once` cell and shared, which would make the frame look like one slot. -/
def intDomAt (w off : Nat) : Domain :=
  Dom.ofList ((List.range w).map (fun i : Nat => Value.int ((i + off : Nat) : Int)))

/-- `[true, false]`. -/
def boolDom : Domain := Dom.ofList [Value.bool true, Value.bool false]

/-- `[true, false, 0, 1, ..., w-1]` (booleans carry `intView` 1/0). -/
def mixedDom (w : Nat) : Domain :=
  Dom.ofList (Value.bool true :: Value.bool false ::
    (List.range w).map (fun i : Nat => Value.int (i : Int)))

/-- A frame with the given pinned pins (slot `0..pins.length-1`) followed by
the remaining domains; slot indices count the pins first, as in
`Frame.domains`. -/
def mkFrame (pins : List Int) (ds : List Domain) : BranchFrame :=
  SparseFrame.ofPrefixFrame (ds, pins.map (fun i => Value.int i))

/-- The literal-check frame: slots 0/1 pinned, 2-5 wide int domains, 6 bool,
7 mixed, 8 a singleton int. -/
def wideFrame (w : Nat) : BranchFrame :=
  mkFrame [0, 1]
    [intDom w, intDom w, intDom w, intDom w, boolDom, mixedDom w,
      Dom.ofList [Value.int 5]]

/-- The literal checks, named. Cheaper-things-first is irrelevant here; the
order only fixes the printed table. -/
def litChecks (w : Nat) : List (String × Literal) :=
  [ ("intLe+ imp (k<min)",         (⟨.intLe 2 (-1), true⟩ : Literal)),
    ("intLe+ poss (k≥max)",        (⟨.intLe 2 ((w + 5 : Nat) : Int), true⟩ : Literal)),
    ("intLe- imp (k≥max)",         (⟨.intLe 3 ((w + 5 : Nat) : Int), false⟩ : Literal)),
    ("intLe- poss (k<min)",        (⟨.intLe 3 (-1), false⟩ : Literal)),
    ("intNe+ poss (v∉domain)",     (⟨.intNe 4 (-7), true⟩ : Literal)),
    ("intNe+ poss (v=mid)",        (⟨.intNe 4 ((w / 2 : Nat) : Int), true⟩ : Literal)),
    ("intNe+ imp (singleton)",     (⟨.intNe 8 5, true⟩ : Literal)),
    ("intNe- fallback (v∉domain)", (⟨.intNe 5 (-7), false⟩ : Literal)),
    ("intNe- fallback (v=max)",    (⟨.intNe 5 ((w - 1 : Nat) : Int), false⟩ : Literal)),
    ("intLe+ imp on mixed slot",   (⟨.intLe 7 (-1), true⟩ : Literal)),
    ("boolEq+ on bool slot",       (⟨.boolEq 6 true, true⟩ : Literal)),
    ("boolEq- on bool slot",       (⟨.boolEq 6 false, false⟩ : Literal)),
    ("boolEq+ on int slot",        (⟨.boolEq 2 true, true⟩ : Literal)) ]

/-- One synthetic clause. The two POSSIBLE literals come first (so the fast
classifier stops at the second remaining literal after 2 summary lookups),
followed by five IMPOSSIBLE order literals, each of which forces the certified
scan into a FULL domain walk of a wide slot. Every clause is a skip (at least
two remaining) for both scans, so each scan visits all clauses. -/
def mkClause (w i : Nat) : Clause :=
  let s0 := 2 + i % 4
  let s1 := 2 + (i + 1) % 4
  let s2 := 2 + (i + 2) % 4
  let s3 := 2 + (i + 3) % 4
  [ (⟨.intLe s1 ((w + 5 : Nat) : Int), true⟩ : Literal),
    (⟨.boolEq 6 true, true⟩ : Literal),
    (⟨.intLe s0 (-1), true⟩ : Literal),
    (⟨.intLe s1 ((w + 7 : Nat) : Int), false⟩ : Literal),
    (⟨.intLe s2 (-2), true⟩ : Literal),
    (⟨.intLe s3 ((w + 3 : Nat) : Int), false⟩ : Literal),
    (⟨.intLe s0 (-3), true⟩ : Literal) ]

/-- `n` synthetic clauses. -/
def mkDb (w n : Nat) : List Clause := (List.range n).map (fun i => mkClause w i)

/-! ## 3. Counting twins

The twins mirror the certified recursions exactly; all counts are per-value
visits of the domain walk (`List.all`'s early exit included). -/

/-- Values `literalImpossible f l` examines, with its early exit. -/
def countLitRef (f : BranchFrame) (l : Literal) : Nat × Bool :=
  let rec go : List Value → Nat → Nat × Bool
    | [], n => (n, true)
    | v :: vs, n => if l.valueHolds v then (n + 1, false) else go vs (n + 1)
  go (Dom.enum ((Frame.domains f).getD l.atom.slot Dom.empty)) 0

/-- Values `literalImpossibleArr a l` examines (the fast fallback walk). -/
def countLitArr (a : Array Domain) (l : Literal) : Nat × Bool :=
  let rec go : List Value → Nat → Nat × Bool
    | [], n => (n, true)
    | v :: vs, n => if l.valueHolds v then (n + 1, false) else go vs (n + 1)
  go (Dom.enum ((a[l.atom.slot]?.getD Dom.empty))) 0

/-- Values `literalImpossibleFast a sums l` examines: 0 for the O(1) summary
shapes, the certified array walk for the negative-`.intNe` fallback. -/
def countLitFast (a : Array Domain) (sums : Array SlotSum) (l : Literal) : Nat × Bool :=
  match l.atom, l.positive with
  | .boolEq s expected, positive =>
    let want := if positive then expected else !expected
    (0, !(if want then (sums[s]?.getD emptySum).hasTrue
          else (sums[s]?.getD emptySum).hasFalse))
  | .intLe s k, true =>
    (0, match (sums[s]?.getD emptySum).minInt with
        | some lo => decide (k < lo)
        | none => true)
  | .intLe s k, false =>
    (0, match (sums[s]?.getD emptySum).maxInt with
        | some hi => decide (hi ≤ k)
        | none => true)
  | .intNe s v, true =>
    let sc := sums[s]?.getD emptySum
    (0, match sc.minInt, sc.maxInt with
        | some lo, some hi => lo == v && hi == v
        | _, _ => true)
  | .intNe _ _, false => countLitArr a l

/-- `clauseRemaining` with a visit counter (filters the WHOLE clause, as the
certified reference does). -/
def clauseRemainingCount (f : BranchFrame) : Clause → Nat × Clause
  | [] => (0, [])
  | l :: ls =>
    let (n, imp) := countLitRef f l
    let (n', rem) := clauseRemainingCount f ls
    (n + n', if imp then rem else l :: rem)

/-- `scanDatabase` with a visit counter. -/
def scanRefCount (original : List Clause) (f : BranchFrame) : List Clause → Nat × PruningEvent
  | [] => (0, .stable)
  | c :: rest =>
    let (n, rem) := clauseRemainingCount f c
    match rem with
    | [] => (n, .conflict [c])
    | [l] =>
      if productive l f then (n, .implied l c false (!(original.contains c)))
      else
        let (n', e) := scanRefCount original f rest
        (n + n', e)
    | _ =>
      let (n', e) := scanRefCount original f rest
      (n + n', e)

/-- `clauseClassifyFast` with a visit counter. -/
def clauseClassifyFastCount (a : Array Domain) (sums : Array SlotSum) :
    List Literal → Option Literal → Nat × Option (Option Literal)
  | [], none => (0, none)
  | [], some l => (0, some (some l))
  | l :: ls, acc =>
    let (n, imp) := countLitFast a sums l
    match imp with
    | true =>
      let (n', r) := clauseClassifyFastCount a sums ls acc
      (n + n', r)
    | false =>
      match acc with
      | none =>
        let (n', r) := clauseClassifyFastCount a sums ls (some l)
        (n + n', r)
      | some _ => (n, some none)

/-- The indexed fast scan with a direct-visit counter (summaries prebuilt). -/
def scanFastCount (original : List Clause) (f : BranchFrame) (a : Array Domain)
    (sums : Array SlotSum) : List Clause → Nat
  | [] => 0
  | c :: rest =>
    let (n, r) := clauseClassifyFastCount a sums c none
    match r with
    | none => n
    | some none => n + scanFastCount original f a sums rest
    | some (some l) =>
      if productiveFast l f then n else n + scanFastCount original f a sums rest

/-- `(reference visits, fast direct visits, fast build values)` for one scan. -/
def scanCounts (original : List Clause) (f : BranchFrame) (db : List Clause) :
    Nat × Nat × Nat :=
  let ref := (scanRefCount original f db).1
  let a := frameDomainArray f
  let sums := sumsOfArray a
  let direct := scanFastCount original f a sums db
  let build := (Frame.domains f).foldl (fun acc d => acc + d.length) 0
  (ref, direct, build)

/-- Exact event comparison (the payloads agree when the constructors do). -/
def evEqB : PruningEvent → PruningEvent → Bool
  | .stable, .stable => true
  | .conflict xs, .conflict ys => xs == ys
  | .implied l c lr fl, .implied l' c' lr' fl' =>
      l == l' && c == c' && (lr == lr') && (fl == fl')
  | _, _ => false

/-- A tag forcing the scan result (for `IO.lazyPure` windows). -/
def evTag : PruningEvent → Nat
  | .stable => 0
  | .conflict _ => 1
  | .implied _ _ _ _ => 2

/-! ## 4. Literal checks -/

/-- `reps` folds over `lits`, rotating the list each iteration so no two
iterations submit the same call sequence (defeats LLVM loop-invariant
hoisting of the whole inner fold). -/
def litFold (fast : Bool) (f : BranchFrame) (a : Array Domain) (sums : Array SlotSum)
    (lits : List Literal) (reps : Nat) : Nat :=
  let rec go : Nat → Nat → Nat
    | 0, acc => acc
    | n + 1, acc =>
      let k := n % lits.length
      let rotated := lits.drop k ++ lits.take k
      let acc := rotated.foldl (fun acc l =>
        acc + (if (if fast then literalImpossibleFast a sums l else literalImpossible f l)
               then 1 else 0)) acc
      go n acc
  go reps 0

def phaseLiterals (w : Nat) (f : BranchFrame) : IO Unit := do
  let lits := (litChecks w).map (·.2)
  let a := frameDomainArray f
  let sums := sumsOfArray a
  let refVisits := (litChecks w).foldl (fun acc (_, l) => acc + (countLitRef f l).1) 0
  let fastVisits := (litChecks w).foldl (fun acc (_, l) => acc + (countLitFast a sums l).1) 0
  let okRef := (litChecks w).all fun (_, l) => (countLitRef f l).2 == literalImpossible f l
  let okFast := (litChecks w).all fun (_, l) => (countLitFast a sums l).2 == literalImpossibleFast a sums l
  let nchecks := lits.length
  let estRef := refVisits + nchecks
  let refInner := max 1 (min 4000 (max 2 (6000000 / estRef)) / 3)
  -- The fast fold still walks for the two negative-`.intNe` fallback checks,
  -- so its repetitions scale with the width as well (budget ~6M visits).
  let fastInner := min 20000 (max 20 (6000000 / (2 * w + nchecks)))
  let (refNs, refSum) ← bestNs 3 (fun _ => litFold false f a sums lits refInner) 0
  let (fastNs, fastSum) ← bestNs 3 (fun _ => litFold true f a sums lits fastInner) 0
  let per (ns inner : Nat) : Nat := ns / (inner * nchecks + 1)
  say s!"LIT w={w} checks={nchecks} refVisits={refVisits} refNsPerCheck={per refNs refInner} \
fastVisits={fastVisits} fastNsPerCheck={per fastNs fastInner} agree={okRef && okFast} \
foldSums={refSum + fastSum}"
  for (name, l) in litChecks w do
    let (rv, rr) := countLitRef f l
    let (fv, fr) := countLitFast a sums l
    say s!"LITSHAPE w={w} {name} refVisits={rv} fastVisits={fv} same={rr == fr}"

/-! ## 5. Clause classification and cache build -/

def phaseScan (w : Nat) (f : BranchFrame) : IO Unit := do
  let db := mkDb w 200
  let original := db
  let (refVisits, fastDirect, fastBuild) := scanCounts original f db
  let agree := evEqB (scanDatabase original f db) (scanDatabaseFast original f db)
  let refWindows := min 100 (max 3 (20000000 / (refVisits + 1)))
  let fastWindows := min 200 (max 3 (20000000 / (fastBuild + 1)))
  let (refNs, refTag) ← bestNs refWindows (fun i =>
    let dbr := rot db i
    evTag (scanDatabase dbr f dbr)) 0
  let (fastNs, fastTag) ← bestNs fastWindows (fun i =>
    let dbr := rot db i
    evTag (scanDatabaseFast dbr f dbr)) 0
  let (buildNs, buildSize) ← bestNs fastWindows
    (fun _ => (sumsOfArray (frameDomainArray f)).size) 0
  let fastTotal := fastDirect + fastBuild
  let share := 100 * buildNs / (fastNs + 1)
  let amort := refVisits * 100 / (fastBuild + 1)
  let verdict := if fastBuild < refVisits && fastNs < refNs then "amortised" else "NOT amortised"
  say s!"SCAN w={w} clauses=200 refNs={refNs} fastNs={fastNs} speedupPct={100 * refNs / (fastNs + 1)} \
refVisits={refVisits} fastDirectVisits={fastDirect} fastBuildVisits={fastBuild} fastTotalVisits={fastTotal} \
visitReductionX={(refVisits + 1) / (fastTotal + 1)} agree={agree} chk={refTag + fastTag}"
  say s!"BUILD w={w} buildNs={buildNs} fastScanNs={fastNs} buildSharePct={share} \
refVisitsPerBuildX={amort} verdict={verdict} buildChk={buildSize}"

def phaseDbSweep : IO Unit := do
  let w := 1024
  let f := wideFrame w
  let full := mkDb w 200
  for n in [2, 4, 8, 12, 16, 32, 64, 200] do
    let db := full.take n
    let original := db
    let refVisits := (scanRefCount original f db).1
    let windows := min 100 (max 3 (4000000 / (refVisits + 1)))
    let agree := evEqB (scanDatabase original f db) (scanDatabaseFast original f db)
    let (refNs, refTag) ← bestNs windows (fun i =>
      let dbr := rot db i
      evTag (scanDatabase dbr f dbr)) 0
    let (fastNs, fastTag) ← bestNs windows (fun i =>
      let dbr := rot db i
      evTag (scanDatabaseFast dbr f dbr)) 0
    say s!"DBSWEEP w={w} dbClauses={n} refNs={refNs} fastNs={fastNs} \
ratioPct={100 * fastNs / (refNs + 1)} agree={agree} chk={refTag + fastTag}"

/-! ## 6. Memory overhead -/

/-- `sizeOf` of a representative `SlotSum` (both int views populated), in the
STRUCTURAL units of Lean's derived `SizeOf` measure. The derived instance is not
executable in this toolchain (elaboration reports "Failed to find LCNF signature
for Option._sizeOf_inst"), so the value is kernel-checked below and reported as
a literal; `Nat`'s `sizeOf` is the number itself, so these units are not bytes
(which is why the RSS delta measurement below is also reported). -/
def slotSumSizeOfUnits : Nat := 112

theorem slotSum_sizeOf_units :
    sizeOf (⟨some 5, some 100, true, false⟩ : SlotSum) = slotSumSizeOfUnits := by
  decide

theorem emptySum_sizeOf_units : sizeOf (emptySum : SlotSum) = 5 := by
  decide

/-- The recorded wide instance shape of PLAN §1: 1HZ5, 169 slots and
Σ|d| = 3,272,799 values. The synthetic frame below reproduces that shape
exactly (168 x 19366 + 19311). -/
def recordedShapeSlots : Nat := 169

def recordedShapeValues : Nat := 3272799

/-- Materialisation barrier for the recorded-shape frame: `noinline` keeps the
compiler from proving the per-value boxes never escape, and the distinct
per-slot offsets stop it from sharing one hoisted `intDom` list across slots
(both observed: 2.8 MB measured for a frame that must hold ~100 MB). -/
@[noinline] def buildRecordedShape (s0 : Nat) : BranchFrame :=
  { doms := (List.range 168).map (fun j => intDomAt 19366 (j + 1 + s0))
    ++ [intDomAt (19311 - s0) 300000], order := [] }

/-- Materialisation barrier for the 400k-summary batch. -/
@[noinline] def buildSummaryBatch (n s1 : Nat) : Array SlotSum :=
  (Array.range n).map fun i =>
    (⟨some (((i % 977) + s1 : Nat) : Int),
      some ((((i % 977) + 3) + s1 : Nat) : Int), true, false⟩ : SlotSum)

/-- The RSS phase. Each construction is seeded by a FRESH clock reading taken
after the preceding RSS read, so the (pure) construction depends on a runtime
value produced after that read and cannot be floated above it by the compiler;
each construction is forced by a checksum that is PRINTED (an IO use) before
the next RSS read. The 400k-summary batch is measured FIRST, while the heap
still has nothing large to reuse; the recorded-shape frame (with its index and
summaries) is measured second. -/
def phaseMemory : IO Unit := do
  let r0 ← rssKiB
  let t0 ← IO.monoNanosNow
  let s0 := t0 % 3
  let batchN := 400000
  let batch := buildSummaryBatch batchN s0
  let bchk := batch.foldl (fun acc s => acc + ((s.minInt.getD 0).toNat % 7)) 0
  say s!"MEM batchChecksum={bchk} batchSlots={batch.size}"
  let r1 ← rssKiB
  let batchKiB := rssDelta r0 r1
  let t1 ← IO.monoNanosNow
  let s1 := t1 % 2
  let f := buildRecordedShape s1
  let ds := f.doms
  let a := frameDomainArray f
  let sums := sumsOfArray a
  let vals := ds.foldl (fun acc d => acc + d.length) 0
  let chk := (a.foldl (fun acc d =>
      acc + (Dom.enum d).foldl (fun acc v => acc + (v.intView.getD 0).toNat % 7) 0) 0)
    + (sums.foldl (fun acc s => acc + s.hasTrue.toNat + s.hasFalse.toNat +
        ((s.minInt.getD 0).toNat % 7)) 0)
  say s!"MEM frameChecksum={chk} frameValues={vals} frameSlots={ds.length} \
summarySlots={sums.size} indexSlots={a.size}"
  let r2 ← rssKiB
  let frameKiB := rssDelta r1 r2
  let bytesPerSlot := batchKiB * 1024 / batchN
  let bytesPerFrameValue := frameKiB * 1024 / (vals + 1)
  say s!"MEM sizeOfUnitsPerSlot={slotSumSizeOfUnits} (kernel-checked `by decide`; empty=5; structural units, not bytes)"
  say s!"MEM rss0KiB={r0} batchKiB={batchKiB} batchSlots={batchN} bytesPerSlotMeasured={bytesPerSlot}"
  say s!"MEM frameIndexSumsKiB={frameKiB} bytesPerFrameValue={bytesPerFrameValue}"
  let instanceBytes := recordedShapeSlots * bytesPerSlot
  say s!"MEM instance1HZ5 slots={recordedShapeSlots} values={recordedShapeValues} \
summaryBytes={instanceBytes} summaryKiB={(instanceBytes + 1023) / 1024} \
summarySharePpm={1000000 * instanceBytes / ((max 1 bytesPerFrameValue) * (recordedShapeValues + 1) + 1)} \
(frameSlotsKept={ds.length} indexSlotsKept={a.size} summarySlotsKept={sums.size})"

/-! ## 7. Heuristic sort fast path -/

/-- The pre-fast-path `sortDom`: always the sorted projection of the
`(activity, position)` keys. -/
def sortDomRef (dcs : List DomC) (db : List Clause) (s : Nat) (d : Domain) : Domain :=
  Dom.ofList (((keyAux dcs db s 0 (Dom.enum d)).mergeSort
    fun p q => decide (p.1 ≤ q.1)).map fun p => p.2.2)

/-- Rotate a compact domain's enumeration (same rotation as `rot`). -/
def rotDom (d : Domain) (k : Nat) : Domain := Dom.ofList (rot (Dom.enum d) k)

/-- `sortDomRef` behind a `noinline` barrier (the sort length is the forced
result): the timed call cannot be hoisted out of the window loop. -/
@[noinline] def sortRefTimed (dcs : List DomC) (db : List Clause) (s : Nat) (d : Domain) : Nat :=
  (sortDomRef dcs db s d).length

/-- The `uniformKeysB` fast path of `sortDom` behind the same barrier. -/
@[noinline] def sortFastTimed (dcs : List DomC) (db : List Clause) (s : Nat) (d : Domain) : Nat :=
  (sortDom dcs db s d).length

def phaseSort : IO Unit := do
  for w in [1024, 39424] do
    let d := intDom w
    let ref := sortDomRef ([] : List DomC) ([] : List Clause) 0 d
    let fast := sortDom ([] : List DomC) ([] : List Clause) 0 d
    let same := ref == fast
    let windows := if w ≤ 1024 then 100 else 10
    let (refNs, refLen) ← bestNs windows (fun i =>
      sortRefTimed ([] : List DomC) ([] : List Clause) 0 (rotDom d i)) 0
    let (fastNs, fastLen) ← bestNs windows (fun i =>
      sortFastTimed ([] : List DomC) ([] : List Clause) 0 (rotDom d i)) 0
    say s!"SORT w={w} flat refNs={refNs} fastNs={fastNs} speedupPct={100 * refNs / (fastNs + 1)} \
same={same} chk={refLen + fastLen}"
  let d := intDom 1024
  let dbHot : List Clause := [[(⟨.intNe 0 0, true⟩ : Literal)]]
  let ref := sortDomRef ([] : List DomC) dbHot 0 d
  let fast := sortDom ([] : List DomC) dbHot 0 d
  let same := ref == fast
  let (refNs, refLen) ← bestNs 100 (fun i =>
    sortRefTimed ([] : List DomC) dbHot 0 (rotDom d i)) 0
  let (fastNs, fastLen) ← bestNs 100 (fun i =>
    sortFastTimed ([] : List DomC) dbHot 0 (rotDom d i)) 0
  say s!"SORT w=1024 hot refNs={refNs} fastNs={fastNs} speedupPct={100 * refNs / (fastNs + 1)} \
same={same} chk={refLen + fastLen} (non-uniform keys: fast path not taken)"

/-! ## 8. Driver -/

def run (_args : List String) : IO UInt32 := do
  say "== M1 wide-domain microbenchmark (test-only, uncertified) =="
  phaseMemory
  for w in [64, 256, 1024, 39424] do
    let f := wideFrame w
    phaseLiterals w f
    phaseScan w f
  phaseDbSweep
  phaseSort
  say "== done =="
  return 0

end Tests.E1.WideMicro

def main (args : List String) : IO UInt32 := Tests.E1.WideMicro.run args

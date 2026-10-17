/-
File: Tests/UIP/LcgHarnessRunner.lean

Purpose (PLAN task E0; TEST-ONLY, UNCERTIFIED): the instance battery and the
`main` of the `tests_lcg_harness` executable. The bounded loop, observers and
invariant checkers live in `Tests.UIP.LcgHarness`. Every battery instance is a
FlatZinc SOURCE STRING parsed by the real parser and compiled by the real
compiler (so SAT witnesses go through the verified Checker); the T1 family
battery (hand-built `Problem` records) is added for oracle-checked coverage.

Exit code: 0 iff no instance has a wrong verdict, a rejected witness, or
exceeded the bound; 1 otherwise (invariant violations are reported separately,
they do not change the exit code - they are observations).
-/

import Tests.UIP.LcgHarnessBattery
open LeanFzn.Compiler.Domains
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler LeanFzn.Integration
open LeanFzn LeanFzn.Solver LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Integration LeanFzn.Solver.Core
open T1Oracle LcgHarness

namespace LcgHarness

structure FuzzAgg where
  n : Nat := 0
  rejected : Nat := 0
  sat : Nat := 0
  unsat : Nat := 0
  bad : Nat := 0
  boundEx : Nat := 0
  withAnalyze : Nat := 0
  withLearn : Nat := 0
  withAnaSome : Nat := 0
  sumAnalyze : Nat := 0
  sumLearn : Nat := 0
  sumAnaSome : Nat := 0
  sumFallbackAfter : Nat := 0
  invSem : Nat := 0
  invExact : Nat := 0
  kinds : Array Nat := #[0,0,0,0,0,0,0,0,0,0]
  maxLvl : Nat := 0
  maxJump : Nat := 0
  skipJumps : Nat := 0
  nonunit : Nat := 0
  causes : Array (String × Nat) := #[]
  learnedSizes : Array Nat := #[]
  ms : Nat := 0

/-! ## Command line -/

structure Opts where
  bound : Nat := 200000
  oracleCap : Nat := 20000
  inv : Bool := true
  chrono : Bool := true
  only : Bool := false
  heavy : Bool := false
  scan : Bool := false
  fixtures : Bool := false
  scanMax : Nat := 6000
  files : List String := []

def parseArgs : List String → Opts → Opts
  | [], o => o
  | "--bound" :: n :: rest, o => parseArgs rest { o with bound := n.toNat?.getD o.bound }
  | "--oracle" :: n :: rest, o => parseArgs rest { o with oracleCap := n.toNat?.getD o.oracleCap }
  | "--scanmax" :: n :: rest, o => parseArgs rest { o with scanMax := n.toNat?.getD o.scanMax }
  | "--no-inv" :: rest, o => parseArgs rest { o with inv := false }
  | "--no-chrono" :: rest, o => parseArgs rest { o with chrono := false }
  | "--only" :: rest, o => parseArgs rest { o with only := true }
  | "--heavy" :: rest, o => parseArgs rest { o with heavy := true }
  | "--fixtures" :: rest, o => parseArgs rest { o with fixtures := true }
  | "--scan" :: rest, o => parseArgs rest { o with scan := true }
  | f :: rest, o => parseArgs rest { o with files := o.files ++ [f] }

/-- Summary line, for the compact table. -/
def tableLine (r : Row) : String :=
  let o := r.obs
  let skipped := (o.jumpDists.filter (· > 1)).size
  s!"{r.name} | {r.size} | {r.verdict} | or={r.oracle} ch={r.chrono} | {r.witness} | ph {o.ph.str} raw {o.raw.str} | anaNone={o.anaNone} noCp={o.noCheckpoint} jump/fb/ex={o.rawJump}/{o.rawFallback}/{o.rawExclude} | learned {hist o.learnedSizes} | res={o.lastEvents.reasonResolutions} skipJumps={skipped} lvl={o.maxLevel} | steps={o.steps} | {r.ms}ms (bare {r.bareMs}) ch={r.chronoMs}ms | viol a={o.nA} b={o.nB} c={o.nC} d={o.nD}"

end LcgHarness

open LcgHarness in
def runAll (opts : Opts) (insts : List (Except String Inst)) : IO UInt32 := do
  let mut bad := 0
  let mut table : Array String := #[]
  let mut totA := (0, 0)
  let mut totB := (0, 0)
  let mut totC := (0, 0)
  let mut totD := (0, 0)
  for i in insts do
    match i with
    | .error e =>
        IO.println s!"== (rejected by parser/compiler: {e})"
        bad := bad + 1
    | .ok inst =>
        let r ← runInst opts.bound opts.oracleCap opts.inv opts.chrono inst
        printRow r
        table := table.push (tableLine r)
        let o := r.obs
        totA := (totA.1 + o.nA.1, totA.2 + o.nA.2)
        totB := (totB.1 + o.nB.1, totB.2 + o.nB.2)
        totC := (totC.1 + o.nC.1, totC.2 + o.nC.2)
        totD := (totD.1 + o.nD.1, totD.2 + o.nD.2)
        if !r.agree then bad := bad + 1
  IO.println "\n===== SUMMARY TABLE ====="
  for l in table do IO.println l
  IO.println s!"\nviolation totals (configs with >=1 violation; exact,sem): a={totA} b={totB} c={totC} d={totD}"
  if bad == 0 then
    IO.println s!"ALL {table.size} INSTANCES: verdicts agree, witnesses accepted"
    return 0
  else
    IO.eprintln s!"{bad} INSTANCE(S) WITH WRONG VERDICT / REJECTED WITNESS / BOUND EXCEEDED"
    return 1

partial def collectFzn (dir : System.FilePath) (maxBytes : Nat) : IO (Array System.FilePath) := do
  let mut out := #[]
  for ent in (← dir.readDir) do
    let md ← ent.path.metadata
    if md.type == .dir then
      out := out ++ (← collectFzn ent.path maxBytes)
    else if ent.path.extension == some "fzn" && md.byteSize.toNat ≤ maxBytes then
      out := out.push ent.path
  return out

def runFuzz (opts : Opts) (count seed : Nat) : IO UInt32 := do
  let mut g : FuzzAgg := {}
  for k in [0:count] do
    let sd := seed + k
    let src := fuzzSrc sd
    match LcgHarness.ofSource s!"fuzz{sd}" src with
    | .error _ => g := { g with rejected := g.rejected + 1 }
    | .ok inst =>
        let r ← runInst opts.bound opts.oracleCap opts.inv opts.chrono inst
        let o := r.obs
        g := { g with
                 n := g.n + 1,
                 sat := g.sat + (if r.verdict == "SAT" then 1 else 0),
                 unsat := g.unsat + (if r.verdict == "UNSAT" then 1 else 0),
                 bad := g.bad + (if r.agree then 0 else 1),
                 boundEx := g.boundEx + (if r.verdict == "BOUND" then 1 else 0),
                 withAnalyze := g.withAnalyze + (if o.raw.analyze > 0 then 1 else 0),
                 withLearn := g.withLearn + (if o.rawJump > 0 then 1 else 0),
                 withAnaSome := g.withAnaSome + (if o.anaSome > 0 then 1 else 0),
                 sumAnalyze := g.sumAnalyze + o.raw.analyze,
                 sumLearn := g.sumLearn + o.rawJump,
                 sumAnaSome := g.sumAnaSome + o.anaSome,
                 invSem := g.invSem + o.nE + o.nF + o.nA.2 + o.nB.2 + o.nC.2 + o.nD.2,
                 invExact := g.invExact + o.nA.1 + o.nB.1 + o.nC.1 + o.nD.1,
                 kinds := #[g.kinds[0]! + o.nA.1, g.kinds[1]! + o.nA.2, g.kinds[2]! + o.nB.1, g.kinds[3]! + o.nB.2,
                            g.kinds[4]! + o.nC.1, g.kinds[5]! + o.nC.2, g.kinds[6]! + o.nD.1, g.kinds[7]! + o.nD.2, g.kinds[8]! + o.nE, g.kinds[9]! + o.nF],
                 maxLvl := max g.maxLvl o.maxLevel,
                 maxJump := max g.maxJump (o.jumpDists.foldl max 0),
                 skipJumps := g.skipJumps + (o.jumpDists.filter (· > 1)).size,
                 learnedSizes := g.learnedSizes ++ o.learnedSizes,
                 ms := g.ms + r.ms }
        for (c, k) in o.causes.toList do
          g := { g with causes :=
            if g.causes.any (·.1 == c) then g.causes.map fun p => if p.1 == c then (p.1, p.2 + k) else p
            else g.causes.push (c, k) }
        if (o.nE + o.nF > 0) && g.kinds[8]! + g.kinds[9]! - o.nE - o.nF < 400 then
          for v in o.viols do
            if v.kind == "e-entailed" || v.kind == "f-align" then
              IO.println s!"   VIOLATION {v.kind} seed {sd} @step {v.step}: {v.detail}"
        for v in o.viols do
          if v.kind == "novelty" then
            IO.println s!"   NOVELTY-VIOLATION seed {sd} @step {v.step}: {v.detail}"
        let interesting := !r.agree || o.rawJump > 0 || o.anaSome > 0 || o.nE + o.nF + o.nA.2 + o.nB.2 + o.nC.2 + o.nD.2 > 0
        if interesting then
          IO.println s!"[fuzz seed {sd}] {tableLine r} causes={o.causes.toList}"
          if !r.agree || o.rawJump > 0 || o.causes.any (·.1 == "fuel-exhausted") || o.nA.2 + o.nB.2 + o.nC.2 + o.nD.2 > 0 then
            IO.println s!"----- source of seed {sd} -----\n{src}-----"
  IO.println s!"\nFUZZ SUMMARY seeds {seed}..{seed + count - 1}: instances={g.n} rejected={g.rejected} SAT={g.sat} UNSAT={g.unsat} wrong/boundEx/rejectedWitness={g.bad} (bound exceeded {g.boundEx})"
  IO.println s!"  instances with raw analyzeConflict: {g.withAnalyze} (sites {g.sumAnalyze}); with analysis=some: {g.withAnaSome} (sites {g.sumAnaSome}); with a learn/backjump: {g.withLearn} (sites {g.sumLearn})"
  IO.println s!"  learned sizes {hist g.learnedSizes}; skipped-level jumps {g.skipJumps}; maxJump {g.maxJump}; maxLevel {g.maxLvl}"
  IO.println s!"  analysis=none causes: {g.causes.toList}"
  IO.println s!"  invariant violations (config counts) exact={g.invExact} semantic={g.invSem}; total instrumented ms={g.ms}"
  IO.println s!"  per-invariant config counts (a-exact,a-sem,b-exact,b-sem,c-exact,c-sem,d-exact,d-sem,e-entailed,f-align) = {g.kinds.toList}"
  return (if g.bad == 0 then 0 else 1)

def main (args : List String) : IO UInt32 := do
  let args' := args
  let opts := parseArgs args' {}
  match args' with
  | "--fuzz" :: cnt :: sd :: rest =>
      return (← runFuzz (parseArgs rest {}) (cnt.toNat?.getD 100) (sd.toNat?.getD 1))
  | _ => pure ()
  if opts.scan then
    -- scan mode: parse+compile every small .fzn under each given directory
    let mut ok := #[]
    let mut rej : Std.HashMap String Nat := {}
    let mut total := 0
    for d in opts.files do
      for f in (← collectFzn d opts.scanMax) do
        total := total + 1
        let src ← IO.FS.readFile f
        match LcgHarness.ofSource f.toString src with
        | .ok inst => ok := ok.push inst.name
        | .error e =>
            let key := ((e.splitOn ": ").drop 1 |> ": ".intercalate |>.take 90).toString
            rej := rej.insert key (rej.getD key 0 + 1)
    IO.println s!"scanned {total} files (<= {opts.scanMax} bytes): {ok.size} accepted"
    for n in ok do IO.println s!"  accepted {n}"
    for (k, v) in rej.toList do IO.println s!"  rejected x{v}: {k}"
    return 0
  let mut insts : List (Except String Inst) := []
  if !opts.only then
    insts := insts ++ (battery ++ (if opts.heavy then heavy else [])).map fun (n, s) => LcgHarness.ofSource n s
    insts := insts ++ familyBattery.map fun (n, p, _) => .ok (LcgHarness.ofProblem s!"T1:{n}" p)
  if opts.fixtures then
    let fs ← collectFzn "Tests/UIP/LcgHarnessFixtures" 1000000
    for f in fs.qsort (fun a b => a.toString < b.toString) do
      let src ← IO.FS.readFile f
      insts := insts ++ [LcgHarness.ofSource f.toString src]
  for f in opts.files do
    let src ← IO.FS.readFile f
    insts := insts ++ [LcgHarness.ofSource f src]
  runAll opts insts

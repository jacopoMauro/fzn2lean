/-
File: Tests/Legacy/Solver/UIP/LcgProtoRunner.lean

Purpose (PLAN task R0; TEST-ONLY, UNCERTIFIED): the ablation driver of the
R0 prototype (`Tests.Legacy.Solver.UIP.LcgProto`). For every instance the oracle verdict
(small boxes), the chronological verdict and the oracle solution list are
computed ONCE; then every requested fix configuration is run with a step
bound (a test parameter) and aggregated: conflict sites, analysis success,
learn sites, learned clause sizes, skipped-level jumps, consumes by cause,
invariant violations (a)-(d) in the E0 checkers' exact and semantic forms,
entailment of every learned clause and every reason the prototype creates
(checked against the oracle's solution list), wrong verdicts, time.

Run: `lake build tests_lcg_proto && .lake/build/bin/tests_lcg_proto SET [opts]`
  SET:  --fixtures | --battery | --fuzz N SEED | FILE...
  --cfg SPEC   (repeatable) none | all | +a,b | -a,b (all minus) | a,b (only)
  --ablation   base, each fix alone, all, all-minus-each
  --bound N    step bound (default 50000);  --oracle N  oracle cap (20000)
  --no-inv     skip the invariant checkers;  --no-chrono  skip chronological
  --verbose    per-instance lines
Exit code 0 iff no wrong verdict / rejected witness / bound overrun /
entailment violation in any configuration.
-/

import Tests.Legacy.Solver.UIP.LcgProto
import Tests.Legacy.Solver.UIP.LcgHarnessBattery
open LeanFzn.Compiler.Domains
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler LeanFzn.Integration
open LeanFzn LeanFzn.Solver LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Integration LeanFzn.Solver.Core
open T1Oracle LcgHarness

namespace LcgProto

def bump (xs : Array (String × Nat)) (k : String) (n : Nat := 1) : Array (String × Nat) :=
  if xs.any (·.1 == k) then xs.map fun p => if p.1 == k then (p.1, p.2 + n) else p
  else xs.push (k, n)

structure Agg where
  insts : Nat := 0
  sat : Nat := 0
  unsat : Nat := 0
  wrong : Nat := 0
  boundEx : Nat := 0
  steps : Nat := 0
  sites : Nat := 0
  anaOk : Nat := 0
  learn : Nat := 0
  learnedN : Nat := 0
  nonunit : Nat := 0
  sizeSum : Nat := 0
  sizeMax : Nat := 0
  skipJumps : Nat := 0
  maxJump : Nat := 0
  dropped : Nat := 0
  consumes : Nat := 0
  rootUnsat : Nat := 0
  causes : Array (String × Nat) := #[]
  consumeCauses : Array (String × Nat) := #[]
  inv : Array Nat := #[0,0,0,0,0,0,0,0]
  checkedA : Nat := 0
  checkedB : Nat := 0
  checkedC : Nat := 0
  entail : Nat := 0
  entailChecked : Nat := 0
  ms : Nat := 0
  bareMs : Nat := 0
  examples : Array String := #[]

instance : Inhabited Agg := ⟨{}⟩

def Agg.add (g h : Agg) : Agg :=
  { insts := g.insts + h.insts, sat := g.sat + h.sat, unsat := g.unsat + h.unsat,
    wrong := g.wrong + h.wrong, boundEx := g.boundEx + h.boundEx, steps := g.steps + h.steps,
    sites := g.sites + h.sites, anaOk := g.anaOk + h.anaOk, learn := g.learn + h.learn,
    learnedN := g.learnedN + h.learnedN, nonunit := g.nonunit + h.nonunit,
    sizeSum := g.sizeSum + h.sizeSum, sizeMax := max g.sizeMax h.sizeMax,
    skipJumps := g.skipJumps + h.skipJumps, maxJump := max g.maxJump h.maxJump,
    dropped := g.dropped + h.dropped, consumes := g.consumes + h.consumes,
    rootUnsat := g.rootUnsat + h.rootUnsat,
    causes := h.causes.foldl (fun a p => bump a p.1 p.2) g.causes,
    consumeCauses := h.consumeCauses.foldl (fun a p => bump a p.1 p.2) g.consumeCauses,
    inv := (List.range 8).toArray.map fun i => g.inv[i]! + h.inv[i]!,
    checkedA := g.checkedA + h.checkedA, checkedB := g.checkedB + h.checkedB,
    checkedC := g.checkedC + h.checkedC,
    entail := g.entail + h.entail, entailChecked := g.entailChecked + h.entailChecked,
    ms := g.ms + h.ms, bareMs := g.bareMs + h.bareMs,
    examples := if g.examples.size ≥ 6 then g.examples else g.examples ++ h.examples.extract 0 (6 - g.examples.size) }

def entailed (sols : Option (List Assignment)) (c : Clause) : Bool :=
  match sols with
  | none => true
  | some ss => ss.all fun a => c.any fun l => l.eval a == some true

def Agg.ex (g : Agg) (s : String) : Agg :=
  if g.examples.size < 6 then { g with examples := g.examples.push s } else g

/-- Observe one configuration (invariants), before the step `t`. -/
def observe {leaf : Assignment → Bool} (inv : Bool) (sols : Option (List Assignment))
    (cfg : SchedulerConfig leaf) (t : PStep leaf) (g : Agg) : Agg :=
  let g := { g with steps := g.steps + 1 }
  -- entailment of everything the prototype creates
  let created : List Clause :=
    match t with
    | .propagate _ r => r
    | .learn _ s _ _ _ r => s.learned :: r
    | .consume _ _ _ r => r
    | _ => []
  let g := if sols.isSome && !created.isEmpty then
      let bad := created.filter fun c => !entailed sols c
      let g := { g with entailChecked := g.entailChecked + created.length, entail := g.entail + bad.length }
      match bad with
      | c :: _ => g.ex s!"NOT ENTAILED: {fmtClause c}"
      | [] => g
    else g
  -- conflict sites
  let site? : Option Site :=
    match t with
    | .learn _ s _ _ _ _ => some s
    | .consume _ _ s _ => s
    | .unsat _ s => s
    | _ => none
  let g :=
    match site? with
    | some s =>
        if s.level == 0 then { g with rootUnsat := g.rootUnsat + 1 } else
        let g := { g with sites := g.sites + 1 }
        if s.outcome == "ok" then { g with anaOk := g.anaOk + 1 }
        else if s.outcome == "root" then { g with anaOk := g.anaOk + 1, rootUnsat := g.rootUnsat + 1 }
        else { g with causes := bump g.causes s.outcome }
    | none => g
  let g :=
    match t with
    | .learn _ s src tgt dr _ =>
        let sz := s.learned.length
        { g with learn := g.learn + 1, learnedN := g.learnedN + 1,
                 nonunit := g.nonunit + (if sz > 1 then 1 else 0),
                 sizeSum := g.sizeSum + sz, sizeMax := max g.sizeMax sz,
                 skipJumps := g.skipJumps + (if src - tgt > 1 then 1 else 0),
                 maxJump := max g.maxJump (src - tgt), dropped := g.dropped + dr }
    | .consume _ cause _ _ =>
        { g with consumes := g.consumes + 1, consumeCauses := bump g.consumeCauses cause }
    | _ => g
  if !inv then g else
  -- (a) trail reasons
  let g := { g with checkedA := g.checkedA + 1 }
  let g := match reasonViolations false cfg.orig cfg.branch.trail with
    | [] => g | _ => { g with inv := g.inv.modify 0 (· + 1) }
  let g := match reasonViolations true cfg.orig cfg.branch.trail with
    | [] => g | d :: _ => ({ g with inv := g.inv.modify 1 (· + 1) }).ex s!"a-sem: {d}"
  -- (b) closure points
  let isDec := match t with | .decide _ => true | _ => false
  let g := if isDec then
      let g := { g with checkedB := g.checkedB + 1 }
      let g := match dbFalsifiedClauses false cfg.branch.trail cfg.branch.learned with
        | [] => g | _ => { g with inv := g.inv.modify 2 (· + 1) }
      match dbFalsifiedClauses true cfg.branch.trail cfg.branch.learned with
        | [] => g | c :: _ => ({ g with inv := g.inv.modify 3 (· + 1) }).ex s!"b-sem: {fmtClause c}"
    else g
  -- (c) unit learned clauses
  let g := if cfg.status == .active then
      let g := { g with checkedC := g.checkedC + 1 }
      let g := match unitViolations false cfg with
        | [] => g | _ => { g with inv := g.inv.modify 4 (· + 1) }
      match unitViolations true cfg with
        | [] => g
        | (c, l, bad) :: _ => ({ g with inv := g.inv.modify 5 (· + 1) }).ex
            s!"c-sem: unit {fmtClause c} pivot {fmtLit l} bad {fmtClause bad}"
    else g
  -- (d) conflict clause
  match site? with
  | some s =>
      let g := match conflictViolations false cfg.orig cfg.branch.trail s.clause with
        | [] => g | _ => { g with inv := g.inv.modify 6 (· + 1) }
      match conflictViolations true cfg.orig cfg.branch.trail s.clause with
        | [] => g
        | b => ({ g with inv := g.inv.modify 7 (· + 1) }).ex
            s!"d-sem: conflict {fmtClause s.clause} unfalsified {fmtClause b}"
  | none => g

inductive V where | sat (w : Assignment) | unsat | bound

def loop {leaf : Assignment → Bool} (fx : Fixes) (inv : Bool) (sols : Option (List Assignment)) :
    Nat → SchedulerConfig leaf → Agg → Agg × V
  | 0, _, g => (g, .bound)
  | n + 1, cfg, g =>
      let t := protoStep fx cfg
      let g := observe inv sols cfg t g
      match t with
      | .sat w => (g, .sat w)
      | .unsat _ _ => (g, .unsat)
      | .propagate c _ | .decide c | .skipDecide c | .learn c _ _ _ _ _ | .consume c _ _ _ =>
          loop fx inv sols n c g

def bare {leaf : Assignment → Bool} (fx : Fixes) : Nat → SchedulerConfig leaf → Nat
  | 0, _ => 0
  | n + 1, cfg =>
      match protoStep fx cfg with
      | .sat _ => 1
      | .unsat _ _ => 2
      | .propagate c _ | .decide c | .skipDecide c | .learn c _ _ _ _ _ | .consume c _ _ _ =>
          bare fx n c

structure Prep where
  inst : Inst
  orSat : Option Bool
  sols : Option (List Assignment)
  chSat : Option Bool

def prep (oracleCap : Nat) (chrono : Bool) (inst : Inst) : IO Prep := do
  let p := inst.problem
  let sols := if boxSize p ≤ oracleCap then some (oracleSolutions p) else none
  let ch : Option Bool ←
    if chrono then
      let r ← IO.lazyPure fun _ => solveDomWithStats p
      pure (match r.1 with | .sat _ => some true | .unsat => some false | _ => none)
    else pure none
  return { inst, orSat := sols.map (!·.isEmpty), sols, chSat := ch }

def runOne (fx : Fixes) (bound : Nat) (inv : Bool) (pr : Prep) : IO Agg := do
  let p := pr.inst.problem
  let leaf := leafOf p
  let props := if fx.expl then explainedProps p.domains p.constraints else propsOf p
  let cfg0 : SchedulerConfig leaf := SchedulerConfig.init p.domains p.clauses props
  let t0 ← IO.monoMsNow
  let code ← IO.lazyPure fun _ => bare (leaf := leaf) fx bound cfg0
  let t1 ← IO.monoMsNow
  let (g, v) ← IO.lazyPure fun _ => loop (leaf := leaf) fx inv pr.sols bound cfg0 {}
  let t2 ← IO.monoMsNow
  let _ := code
  let vSat : Option Bool := match v with | .sat _ => some true | .unsat => some false | .bound => none
  let wit := match v with | .sat a => witnessCheck pr.inst a pr.sols.isSome | _ => "-"
  let okOr := match vSat, pr.orSat with | some a, some b => a == b | _, _ => true
  let okCh := match vSat, pr.chSat with | some a, some b => a == b | _, _ => true
  let okWit := !(wit.endsWith "REJECTED") && wit != "checker:ERR"
  let wrong := !(okOr && okCh && okWit) || vSat.isNone
  let g := { g with insts := 1, ms := t2 - t1, bareMs := t1 - t0,
                    sat := if vSat == some true then 1 else 0,
                    unsat := if vSat == some false then 1 else 0,
                    wrong := if wrong then 1 else 0,
                    boundEx := if vSat.isNone then 1 else 0 }
  return if wrong then g.ex s!"WRONG/BOUND on {pr.inst.name}" else g

def pct (a b : Nat) : String :=
  if b == 0 then "-" else
  let x := a * 1000 / b
  s!"{x / 10}.{x % 10}%"

def Agg.line (g : Agg) : String :=
  let mean := if g.learnedN == 0 then "-" else
    let m := g.sizeSum * 10 / g.learnedN
    s!"{m / 10}.{m % 10}"
  s!"inst={g.insts} SAT={g.sat} UNSAT={g.unsat} wrong={g.wrong} boundEx={g.boundEx} | sites={g.sites} anaOk={g.anaOk} ({pct g.anaOk g.sites}) learn={g.learn} ({pct g.learn g.sites}) nonunit={g.nonunit} meanSize={mean} maxSize={g.sizeMax} skipJumps={g.skipJumps} maxJump={g.maxJump} droppedPending={g.dropped} consumes={g.consumes} rootUnsat={g.rootUnsat} | inv(aE,aS,bE,bS,cE,cS,dE,dS)={g.inv.toList} @a{g.checkedA}/b{g.checkedB}/c{g.checkedC} | entailViol={g.entail}/{g.entailChecked} | steps={g.steps} ms={g.ms} bareMs={g.bareMs}"

def parseSpec (s : String) : Fixes :=
  if s == "none" || s == "base" then {} else
  if s == "all" then Fixes.all else
  if s.startsWith "-" then
    ((s.drop 1).toString.splitOn ",").foldl (fun fx n => fx.set n false) Fixes.all
  else
    let body := if s.startsWith "+" then (s.drop 1).toString else s
    (body.splitOn ",").foldl (fun fx n => fx.set n true) {}

def ablation : List String :=
  ["none"] ++ Fixes.names ++ ["all"] ++ Fixes.names.map ("-" ++ ·)

structure Opts where
  bound : Nat := 50000
  oracleCap : Nat := 20000
  inv : Bool := true
  chrono : Bool := true
  verbose : Bool := false
  cfgs : List String := []
  fixtures : Bool := false
  battery : Bool := false
  fuzz : Option (Nat × Nat) := none
  files : List String := []

def parseArgs : List String → Opts → Opts
  | [], o => o
  | "--bound" :: n :: r, o => parseArgs r { o with bound := n.toNat?.getD o.bound }
  | "--oracle" :: n :: r, o => parseArgs r { o with oracleCap := n.toNat?.getD o.oracleCap }
  | "--no-inv" :: r, o => parseArgs r { o with inv := false }
  | "--no-chrono" :: r, o => parseArgs r { o with chrono := false }
  | "--verbose" :: r, o => parseArgs r { o with verbose := true }
  | "--cfg" :: c :: r, o => parseArgs r { o with cfgs := o.cfgs ++ [c] }
  | "--ablation" :: r, o => parseArgs r { o with cfgs := o.cfgs ++ ablation }
  | "--fixtures" :: r, o => parseArgs r { o with fixtures := true }
  | "--battery" :: r, o => parseArgs r { o with battery := true }
  | "--fuzz" :: n :: s :: r, o => parseArgs r { o with fuzz := some (n.toNat?.getD 100, s.toNat?.getD 1) }
  | f :: r, o => parseArgs r { o with files := o.files ++ [f] }

end LcgProto

open LcgProto in
partial def collectFznP (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for ent in (← dir.readDir) do
    let md ← ent.path.metadata
    if md.type == .dir then out := out ++ (← collectFznP ent.path)
    else if ent.path.extension == some "fzn" then out := out.push ent.path
  return out

open LcgProto in
def main (args : List String) : IO UInt32 := do
  let o := parseArgs args {}
  let cfgs := if o.cfgs.isEmpty then ["none", "all"] else o.cfgs
  let fxs := cfgs.map fun c => (c, parseSpec c)
  -- instance stream (lazy for fuzz)
  let mut srcs : Array (String × String) := #[]
  if o.fixtures then
    let fs ← collectFznP "Tests/Fixtures/Solver"
    for f in fs.qsort (fun a b => a.toString < b.toString) do
      srcs := srcs.push (f.toString, ← IO.FS.readFile f)
  if o.battery then
    srcs := srcs ++ battery.toArray
  for f in o.files do
    srcs := srcs.push (f, ← IO.FS.readFile f)
  let mut insts : Array Inst := #[]
  let mut rejected := 0
  for (n, s) in srcs do
    match LcgHarness.ofSource n s with
    | .ok i => insts := insts.push i
    | .error _ => rejected := rejected + 1
  if o.battery then
    insts := insts ++ (familyBattery.map fun (n, p, _) => LcgHarness.ofProblem s!"T1:{n}" p).toArray
  let fuzzRange : List Nat := match o.fuzz with
    | some (n, s) => (List.range n).map (s + ·)
    | none => []
  let mut aggs : Array Agg := fxs.toArray.map fun _ => {}
  let mut prepMs := 0
  let total := insts.size + fuzzRange.length
  let mut k := 0
  for idx in [0:total] do
    let inst? : Option Inst :=
      if h : idx < insts.size then some insts[idx]
      else
        let sd := fuzzRange.getD (idx - insts.size) 0
        match LcgHarness.ofSource s!"fuzz{sd}" (fuzzSrc sd) with
        | .ok i => some i
        | .error _ => none
    match inst? with
    | none => rejected := rejected + 1
    | some inst =>
      k := k + 1
      let tp0 ← IO.monoMsNow
      let pr ← prep o.oracleCap o.chrono inst
      let tp1 ← IO.monoMsNow
      prepMs := prepMs + (tp1 - tp0)
      let mut j := 0
      for (cn, fx) in fxs do
        let g ← runOne fx o.bound o.inv pr
        if o.verbose then IO.println s!"[{cn}] {inst.name}: {g.line}"
        aggs := aggs.modify j (·.add g)
        j := j + 1
  let mut bad := 0
  IO.println s!"\n===== R0 ABLATION (instances run={k}, rejected by parser/compiler={rejected}, bound={o.bound}, oracle/chrono prep ms={prepMs}) ====="
  let mut j := 0
  for (cn, fx) in fxs do
    let g := aggs[j]!
    IO.println s!"[{cn}] fixes={fx.str}\n   {g.line}"
    IO.println s!"   analysis-failure causes: {g.causes.toList}"
    IO.println s!"   consume causes: {g.consumeCauses.toList}"
    for e in g.examples do IO.println s!"   e.g. {e}"
    if g.wrong + g.entail > 0 then bad := bad + 1
    j := j + 1
  return (if bad == 0 then 0 else 1)

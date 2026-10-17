/-
File: Tests/UIP/LcgHarness.lean

Purpose (PLAN task E0; TEST-ONLY, UNCERTIFIED):
  A step-bounded execution harness that runs the REAL first-UIP scheduler step
  function `LeanFzn.Solver.UIP.C3b.phaseNext` from `SchedulerConfig.init`, so we
  can observe how the scheduler behaves end to end. The loop (`LcgHarness.loop`)
  only calls `phaseNext` and follows `.successor`; NO dispatcher logic is copied.
  The step bound is a TEST PARAMETER; it is never part of a public or certified
  path and nothing here is claimed as a theorem.

  Per instance it reports: verdict (sat / unsat / bound-exceeded), comparison
  with the exhaustive oracle (`Tests.UIP.OracleFixtures`, where the box is
  small enough) and with the chronological reference (`solveDomWithStats`), the
  SAT witness through the verified Checker (`checkModelSolutionFast`, for
  parsed-source instances), counts per transition kind (both of the real
  `phaseNext` and of the raw `schedulerNext` it wraps), the runtime events
  (`RuntimeEvents`), the counted analyzer events (`EventCounts`), learned clause
  sizes, maximum decision level, skipped-level jumps, steps and wall time.

  Executable Bool checkers (never proofs) of the U0 candidate invariants are
  evaluated on every visited configuration:
    (a) every non-pivot literal of every trail reason is falsified by an
        earlier trail entry or by the original domains (root fact);
    (b) `DatabaseUnfalsified` at closure points (the step is a decision);
    (c) every learned clause that is unit under the current frame has its
        non-pivot literals falsified on the trail or by the original domains;
    (d) the reported conflict clause is falsified by the trail or the root.
  Each is evaluated in an EXACT variant (literal-for-literal on the trail, as
  `FalsifiedByTrailNorm`) and a SEMANTIC variant (an earlier trail literal
  IMPLIES the falsification, e.g. `x <= 2` falsifies `x > 5`).

Dependencies: Tests.UIP.OracleFixtures (oracle; imported and REUSED),
LeanFzn.Integration.CertifiedSolve (parser/compiler plumbing, emitter),
LeanFzn.Checker.Check (verified checker), `Proofs.Scheduler` (`phaseNext`).
No `sorry`, no axioms, no `native_decide`.

Run: `lake build tests_lcg_harness && .lake/build/bin/tests_lcg_harness [opts] [files]`
  --bound N    step bound (default 200000)
  --oracle N   oracle cap on the product of domain sizes (default 20000)
  --no-inv     skip the invariant checkers
  --no-chrono  skip the chronological baseline
  FILE...      FlatZinc files run in addition to the built-in battery
  --only       run only the FILE arguments
-/

import Tests.UIP.OracleFixtures
import LeanFzn.Integration.CertifiedSolve
import LeanFzn.Checker.Check
import LeanFzn.Solver.Propagation.LiteralClamp
import LeanFzn.Solver.UIP.Proofs.Scheduler
import LeanFzn.Solver.UIP.AnalysisEvents
open LeanFzn.Compiler.Domains
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler LeanFzn.Integration
open LeanFzn LeanFzn.Solver LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Integration LeanFzn.Solver.Core
open LeanFzn.Solver.UIP.C3b
open T1Oracle

namespace LcgHarness

abbrev LProblem := LeanFzn.Solver.Propagation.Problem DomConstraint Unit


/-! ### Compact printing -/

def fmtLit (l : Literal) : String :=
  match l.atom, l.positive with
  | .boolEq s b, true => s!"b{s}={b}"
  | .boolEq s b, false => s!"b{s}!={b}"
  | .intLe s k, true => s!"x{s}<={k}"
  | .intLe s k, false => s!"x{s}>{k}"
  | .intNe s v, true => s!"x{s}!={v}"
  | .intNe s v, false => s!"x{s}={v}"

def fmtClause (c : Clause) : String := "[" ++ " | ".intercalate (c.map fmtLit) ++ "]"

def fmtEntry (e : TrailEntry) : String :=
  match e.reason with
  | none => s!"{fmtLit e.literal}@{e.level}:DEC"
  | some r => s!"{fmtLit e.literal}@{e.level}:{fmtClause r.clause}"

def fmtTrail (t : List TrailEntry) : String := "\n      ".intercalate (t.map fmtEntry)

/-! ## 1. Literal vocabulary for the executable checkers -/

/-- The literal is never TRUE at any value of the original domain of its slot
(a root fact: no trail entry needed). `Literal.eval = none` (an atom of the
wrong sort, e.g. a `boolEq` literal on an int slot, which the propagators put
into reason clauses) is NOT `some true`, so it counts as falsified (the earlier
conservative reading, which flagged these as violations, was a harness artefact). -/
def litFalseAtRoot (orig : List Domain) (q : Literal) : Bool :=
  (orig.getD q.atom.slot []).all fun v =>
    match q.atom.evalAtValue v with
    | some b => (if q.positive then b else !b) == false
    | none => true

/-- Exact trail falsification of `q`: the trail records `(q.negate).norm`
(the shape of `FalsifiedByTrailNorm`). -/
def exactFalsified (entries : List TrailEntry) (q : Literal) : Bool :=
  entries.any fun e => litEqB e.literal q.negate.norm

/-- Syntactic bound implication between NORMALIZED literals: `t` implies `g`. -/
def impliesLit (t g : Literal) : Bool :=
  if litEqB t g then true
  else if t.atom.slot != g.atom.slot then false
  else
    match t.atom, t.positive, g.atom, g.positive with
    -- x <= k  implies  x <= k'  (k <= k'),  x /= v  (v > k)
    | .intLe _ k, true, .intLe _ k', true => decide (k ≤ k')
    | .intLe _ k, true, .intNe _ v, true => decide (k < v)
    -- x > k  implies  x > k'  (k' <= k),  x /= v  (v <= k)
    | .intLe _ k, false, .intLe _ k', false => decide (k' ≤ k)
    | .intLe _ k, false, .intNe _ v, true => decide (v ≤ k)
    -- x = v  implies  x <= k (v <= k),  x > k (v > k),  x /= w (w /= v)
    | .intNe _ v, false, .intLe _ k, true => decide (v ≤ k)
    | .intNe _ v, false, .intLe _ k, false => decide (k < v)
    | .intNe _ v, false, .intNe _ w, true => decide (w ≠ v)
    | _, _, _, _ => false

/-- Semantic trail falsification: some listed entry implies the negation. -/
def semFalsified (entries : List TrailEntry) (q : Literal) : Bool :=
  entries.any fun e => impliesLit e.literal q.negate.norm

/-- Is `q` the pivot (same normalized literal) of a given entry literal? -/
def isPivot (e : TrailEntry) (q : Literal) : Bool := litEqB q.norm e.literal.norm

/-! ### (a) trail reasons -/

/-- One violation record. -/
structure Viol where
  kind : String
  step : Nat
  detail : String

/-- Walk the trail; for each entry with a reason, every non-pivot reason literal
must be falsified by an EARLIER entry or the root. `mode` selects exact (false)
or semantic (true) falsification. Also reports a missing pivot. -/
def reasonViolations (mode : Bool) (orig : List Domain) (trail : List TrailEntry) :
    List String :=
  let rec go : List TrailEntry → List TrailEntry → List String
    | _, [] => []
    | pre, e :: rest =>
        let here :=
          match e.reason with
          | none => []
          | some r =>
              let pivotMissing :=
                if r.clause.any (isPivot e) then [] else
                  [s!"pivot {fmtLit e.literal} not in its reason {fmtClause r.clause}"]
              let bad := r.clause.filter fun q =>
                !(isPivot e q) &&
                !((if mode then semFalsified pre q else exactFalsified pre q)
                  || litFalseAtRoot orig q)
              pivotMissing ++ bad.map fun q =>
                s!"entry {fmtEntry e}: non-pivot {fmtLit q} not falsified earlier/root"
        here ++ go (pre ++ [e]) rest
  go [] trail

/-! ### (b) database unfalsified -/

def dbFalsifiedClauses (mode : Bool) (trail : List TrailEntry) (db : List Clause) :
    List Clause :=
  db.filter fun c =>
    c.all fun q => if mode then semFalsified trail q else exactFalsified trail q

/-! ### (c) unit learned clauses -/

/-- Learned clauses unit under the frame whose non-pivot literals are NOT all
falsified on the trail / root. Returns the offending (clause, unit literal). -/
def unitViolations (mode : Bool) {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) : List (Clause × Literal × List Literal) :=
  cfg.branch.learned.filterMap fun c =>
    match clauseRemaining cfg.branch.frame c with
    | [l] =>
        let bad := c.filter fun q =>
          !(litEqB q.norm l.norm) &&
          !((if mode then semFalsified cfg.branch.trail q
              else exactFalsified cfg.branch.trail q)
            || litFalseAtRoot cfg.orig q)
        if bad.isEmpty then none else some (c, l, bad)
    | _ => none

/-! ### (d) conflict clause -/

def conflictViolations (mode : Bool) (orig : List Domain) (trail : List TrailEntry)
    (c : Clause) : List Literal :=
  c.filter fun q =>
    !((if mode then semFalsified trail q else exactFalsified trail q)
      || litFalseAtRoot orig q)


/-- Where does the REAL analyzer (`analyzeNext`, stepped manually) give up?
Pure observation: re-runs the analyzer's own transitions and classifies the
state at `.done none`. -/
def failCause (orig : List Domain) (trail : List TrailEntry) (lvl : Nat) :
    Nat → AnalyzerState → String
  | 0, _ => "fuel-exhausted"
  | f + 1, st =>
      match analyzeNext orig trail lvl st with
      | .next st' => failCause orig trail lvl f st'
      | .done (some _) => "ok"
      | .done none =>
          let where_ := if st.skip.isNone then "conflict-clause" else "reason-clause"
          match st.work with
          | [] =>
              match st.marks.max? with
              | none => "no-current-level-mark"
              | some _ => "pivot-is-decision-but-other-marks"
          | c :: _ =>
              match c with
              | q0 :: _ =>
                  if litFalseAtRoot orig q0 then s!"literal-falsified-only-at-root({where_})"
                  else if semFalsified trail q0.norm then s!"literal-semantic-only({where_})"
                  else s!"literal-unfalsified({where_})"
              | [] => "empty-clause?"

/-! ## 2. Observations along a run -/

structure Counts where
  propagate : Nat := 0
  decide : Nat := 0
  analyze : Nat := 0
  learn : Nat := 0
  exclude : Nat := 0
  fallback : Nat := 0
  deriving Repr

def Counts.bump {leaf : Assignment → Bool} (c : Counts) : SchedulerTransition leaf → Counts
  | .propagate _ => { c with propagate := c.propagate + 1 }
  | .decide _ _ => { c with decide := c.decide + 1 }
  | .analyzeConflict _ _ => { c with analyze := c.analyze + 1 }
  | .learnBackjumpAssert _ _ _ => { c with learn := c.learn + 1 }
  | .localExclude _ => { c with exclude := c.exclude + 1 }
  | .chronologicalFallback _ => { c with fallback := c.fallback + 1 }
  | _ => c

structure Obs where
  steps : Nat := 0
  ph : Counts := {}
  raw : Counts := {}
  /-- sizes of UIP-learned clauses (`ConflictAnalysis.learned`) -/
  learnedSizes : Array Nat := #[]
  maxLevel : Nat := 0
  /-- backjump distances (source level - target level), per learn step -/
  jumpDists : Array Nat := #[]
  /-- counted analyzer events summed over analyze steps -/
  expansions : Nat := 0
  scans : Nat := 0
  marks : Nat := 0
  /-- at raw `.analyzeConflict` sites: how the recorded evidence resolves -/
  anaNone : Nat := 0       -- `ev.analysis = none` (no asserting result)
  anaSome : Nat := 0
  noCheckpoint : Nat := 0  -- `checkpointAt cfg.checkpoints an.backjumpLevel = none`
  rawJump : Nat := 0       -- `backjumpStep` landed on `.learnBackjumpAssert`
  rawFallback : Nat := 0   -- ... on `.chronologicalFallback`
  rawExclude : Nat := 0    -- ... on `.localExclude` (assertion rejected)
  /-- backjump levels recorded by `ConflictAnalysis` at analyze sites -/
  anaBackjumpLevels : Array Nat := #[]
  anaLearnedSizes : Array Nat := #[]
  anaSrcLevels : Array Nat := #[]
  /-- propagate steps immediately following a learn step (post-assertion) -/
  postAssertProps : Nat := 0
  inPost : Bool := false
  lastEvents : RuntimeEvents := {}
  lastDB : Nat := 0
  lastTrail : Nat := 0
  lastLog : Nat := 0
  maxDB : Nat := 0
  maxTrail : Nat := 0
  viols : Array Viol := #[]
  notes : Array String := #[]
  causes : Array (String × Nat) := #[]
  nA : Nat × Nat := (0, 0)   -- (exact, semantic) violation counts for (a)
  nB : Nat × Nat := (0, 0)
  nC : Nat × Nat := (0, 0)
  nD : Nat × Nat := (0, 0)
  /-- number of configs on which (b) / (c) were evaluated -/
  checkedB : Nat := 0
  checkedC : Nat := 0
  /-- U0 extra checkers: (e) learned entailed by oracle solutions, (f) pool alignment -/
  nE : Nat := 0
  nF : Nat := 0
  checkedE : Nat := 0
  nRoot : Nat := 0
  checkedRoot : Nat := 0

def Obs.addViol (o : Obs) (kind : String) (step : Nat) (detail : String) : Obs :=
  if (o.viols.filter (·.kind == kind)).size < 3 then
    { o with viols := o.viols.push { kind, step, detail } }
  else o

def isDecide {leaf : Assignment → Bool} : SchedulerTransition leaf → Bool
  | .decide _ _ => true
  | _ => false

def isPropagate {leaf : Assignment → Bool} : SchedulerTransition leaf → Bool
  | .propagate _ => true
  | _ => false

/-- Observe one configuration and the real step taken from it. -/
def learnedEntailedB (sols : List Assignment) (db : List Clause) : List Clause :=
  db.filter fun c => sols.any fun a => !(c.any fun q => q.eval a == some true)

def alignViolations (orig : List Domain) (db : List Clause) : List Literal :=
  db.flatMap fun c => c.filter fun q => !(decide (q.norm ∈ litPool orig))

def observe {leaf : Assignment → Bool} (inv raw : Bool) (sols : Option (List Assignment)) (i : Nat)
    (cfg : SchedulerConfig leaf) (t : SchedulerTransition leaf) (o : Obs) : Obs :=
  let o := { o with steps := o.steps + 1, ph := o.ph.bump t,
                    maxLevel := max o.maxLevel cfg.branch.level,
                    lastEvents := cfg.events,
                    lastDB := cfg.branch.learned.length,
                    lastTrail := cfg.branch.trail.length,
                    maxDB := max o.maxDB cfg.branch.learned.length,
                    maxTrail := max o.maxTrail cfg.branch.trail.length }
  let o := if raw then { o with raw := o.raw.bump (schedulerNext cfg) } else o
  -- post-assertion propagation accounting
  let o :=
    match t with
    | .propagate _ => if o.inPost then { o with postAssertProps := o.postAssertProps + 1 } else o
    | .learnBackjumpAssert _ _ _ => { o with inPost := true }
    | _ => { o with inPost := false }
  -- per-step event data
  let o :=
    match t with
    | .learnBackjumpAssert _ p an =>
        let o1 := { o with learnedSizes := o.learnedSizes.push an.learned.length,
                           jumpDists := o.jumpDists.push (cfg.branch.level - p.target) }
        -- H2c probe: the asserting enqueue duplicates a literal of the checkpoint trail
        if p.checkpoint.trail.any (fun e => litEqB e.literal an.asserting.norm) then
          o1.addViol "freshJump" i
            s!"asserting {fmtLit an.asserting} already in checkpoint trail; frame uncovered? {cfg.branch.frame.1.any (·.isEmpty)}"
        else o1
    | _ => o
  -- raw `.analyzeConflict` sites (the phase step collapses them into the jump)
  let o :=
    match schedulerNext cfg with
    | .analyzeConflict n c =>
        let o :=
          match analyzeEvents cfg.orig cfg.branch.trail cfg.branch.level
              (analysisFuel cfg.branch.trail c) (initAnalysisState c) with
          | some (ec, _) => { o with expansions := o.expansions + ec.expansions,
                                     scans := o.scans + ec.scans, marks := o.marks + ec.marks }
          | none => o
        match n.conflict with
        | none => o
        | some ev =>
            let o :=
              match ev.analysis with
              | none =>
                  let fuel := analysisFuel cfg.branch.trail c
                  let cause0 := failCause cfg.orig cfg.branch.trail cfg.branch.level
                    fuel (initAnalysisState c)
                  -- if the real fuel ran out, retry with 1000x fuel to tell a
                  -- too-small allowance from a cycling analyzer
                  let cause :=
                    if cause0 == "fuel-exhausted" then
                      "fuel-exhausted; at 1000x fuel: " ++
                        failCause cfg.orig cfg.branch.trail cfg.branch.level
                          (1000 * fuel) (initAnalysisState c)
                    else cause0
                  let causes' :=
                    if o.causes.any (·.1 == cause) then
                      o.causes.map fun p => if p.1 == cause then (p.1, p.2 + 1) else p
                    else o.causes.push (cause, 1)
                  let o : Obs := { o with anaNone := o.anaNone + 1, causes := causes' }
                  if o.notes.size < 3 then
                    let msg := s!"step {i}: analysis=none; level {cfg.branch.level}; conflict {fmtClause c}\n      trail:\n      {fmtTrail cfg.branch.trail}"
                    { o with notes := o.notes.push msg }
                  else o
              | some an =>
                  let o := { o with
                               anaSome := o.anaSome + 1,
                               anaBackjumpLevels := o.anaBackjumpLevels.push (an.backjumpLevel),
                               anaLearnedSizes := o.anaLearnedSizes.push (an.learned.length),
                               anaSrcLevels := o.anaSrcLevels.push (cfg.branch.level) }
                  let o :=
                    if decide (canonicalSorted cfg.orig an.learned ∈
                        P4.canonicalDBSorted cfg.orig cfg.branch.learned) then
                      o.addViol "novelty" i s!"learned {fmtClause an.learned} already in DB"
                    else o
                  match checkpointAt n.checkpoints an.backjumpLevel with
                  | none => { o with noCheckpoint := o.noCheckpoint + 1 }
                  | some _ => o
            match backjumpStep n ev with
            | .learnBackjumpAssert _ _ _ => { o with rawJump := o.rawJump + 1 }
            | .chronologicalFallback _ => { o with rawFallback := o.rawFallback + 1 }
            | .localExclude _ => { o with rawExclude := o.rawExclude + 1 }
            | _ => o
    | _ => o
  if !inv then o else
  -- (e) learned clauses entailed by every oracle solution; (f) pool alignment
  let o :=
    match sols with
    | none => o
    | some ss =>
        let o := { o with checkedE := o.checkedE + 1 }
        match learnedEntailedB ss cfg.branch.learned with
        | [] => o
        | c :: _ => ({ o with nE := o.nE + 1 }).addViol "e-entailed" i
            s!"learned clause {fmtClause c} excludes an oracle solution"
  -- H2f probe: ConsumeRootRun -- level-0 canonical falsifiers of the pending head hold at all solutions
  let o :=
    match sols, cfg.status, cfg.pending with
    | some ss, .dead, f :: _ =>
        let bad := (canonicalFalsifiers cfg.orig f).filter fun (e : TrailEntry) =>
          e.level == 0 && ss.any fun a => e.literal.eval a != some true
        if bad.isEmpty then { o with checkedRoot := o.checkedRoot + 1 }
        else ({ o with nRoot := o.nRoot + 1 }).addViol "consumeRoot" i
          s!"falsifier {bad.map (fun (e : TrailEntry) => fmtLit e.literal)} fails at a solution; pending frame prefix length {f.2.length}"
    | _, _, _ => o
  let o :=
    match alignViolations cfg.orig cfg.branch.learned with
    | [] => o
    | q :: _ => ({ o with nF := o.nF + 1 }).addViol "f-align" i
        s!"learned literal {fmtLit q} outside litPool"
  -- (a) trail reasons
  let o :=
    match reasonViolations false cfg.orig cfg.branch.trail with
    | [] => o
    | d :: _ => (({ o with nA := (o.nA.1 + 1, o.nA.2) }).addViol "a-exact" i d)
  let o :=
    match reasonViolations true cfg.orig cfg.branch.trail with
    | [] => o
    | d :: _ => (({ o with nA := (o.nA.1, o.nA.2 + 1) }).addViol "a-sem" i d)
  -- (b) at closure points
  let o :=
    if isDecide t then
      let o := { o with checkedB := o.checkedB + 1 }
      let o :=
        match dbFalsifiedClauses false cfg.branch.trail cfg.branch.learned with
        | [] => o
        | c :: _ => ({ o with nB := (o.nB.1 + 1, o.nB.2) }).addViol "b-exact" i
            s!"learned clause {fmtClause c} falsified at closure"
      match dbFalsifiedClauses true cfg.branch.trail cfg.branch.learned with
      | [] => o
      | c :: _ => ({ o with nB := (o.nB.1, o.nB.2 + 1) }).addViol "b-sem" i
          s!"learned clause {fmtClause c} semantically falsified at closure"
    else o
  -- (c) unit learned clauses, evaluated where the dispatcher looks at the
  -- frame (active, no pending conflict evidence)
  let o :=
    if cfg.conflict.isNone && cfg.status == .active then
      let o := { o with checkedC := o.checkedC + 1 }
      let o :=
        match unitViolations false cfg with
        | [] => o
        | (c, l, bad) :: _ => ({ o with nC := (o.nC.1 + 1, o.nC.2) }).addViol "c-exact" i
            s!"unit learned {fmtClause c} (pivot {fmtLit l}): non-pivot {fmtClause bad} not falsified"
      match unitViolations true cfg with
      | [] => o
      | (c, l, bad) :: _ => ({ o with nC := (o.nC.1, o.nC.2 + 1) }).addViol "c-sem" i
          s!"unit learned {fmtClause c} (pivot {fmtLit l}): non-pivot {fmtClause bad} not semantically falsified"
    else o
  -- (d) conflict clause
  match schedulerNext cfg with
  | .analyzeConflict _ c =>
      let o :=
        match conflictViolations false cfg.orig cfg.branch.trail c with
        | [] => o
        | b => ({ o with nD := (o.nD.1 + 1, o.nD.2) }).addViol "d-exact" i
            s!"conflict {fmtClause c}: not trail-falsified: {fmtClause b}"
      match conflictViolations true cfg.orig cfg.branch.trail c with
      | [] => o
      | b => ({ o with nD := (o.nD.1, o.nD.2 + 1) }).addViol "d-sem" i
          s!"conflict {fmtClause c}: not semantically falsified: {fmtClause b}"
  | _ => o

inductive Verdict where
  | sat (w : Assignment)
  | unsat
  | bound

/-- THE STEP-BOUNDED LOOP over the real `phaseNext` (test parameter `fuel`). -/
def loop {leaf : Assignment → Bool} (inv raw : Bool) (sols : Option (List Assignment)) :
    Nat → Nat → SchedulerConfig leaf → Obs → Obs × Verdict
  | 0, _, cfg, o => ({ o with lastLog := cfg.log.regions.length }, .bound)
  | fuel + 1, i, cfg, o =>
      let t := phaseNext cfg
      let o := observe inv raw sols i cfg t o
      match t with
      | .sat w => ({ o with lastLog := cfg.log.regions.length }, .sat w)
      | .unsat => ({ o with lastLog := cfg.log.regions.length }, .unsat)
      | _ =>
          match t.successor with
          | some n => loop inv raw sols fuel (i + 1) n o
          | none => (o, .bound)

/-- Bare loop (no observation): step count and verdict code, for honest timing
of the scheduler itself (0 = bound, 1 = sat, 2 = unsat). -/
def bare {leaf : Assignment → Bool} :
    Nat → Nat → SchedulerConfig leaf → Nat × Nat
  | 0, i, _ => (i, 0)
  | fuel + 1, i, cfg =>
      match phaseNext cfg with
      | .sat _ => (i + 1, 1)
      | .unsat => (i + 1, 2)
      | t =>
          match t.successor with
          | some n => bare fuel (i + 1) n
          | none => (i + 1, 0)

/-! ## 3. Instances -/

structure Inst where
  name : String
  problem : LProblem
  model : Option Model := none
  compiled : Option (CompiledProblem DomConstraint) := none

/-- Parse and normalize a FlatZinc source for feasibility observations.
Optimization directives are replaced by satisfy: the harness compares search
verdicts and witnesses, never claims optimality. Public optimization is measured
separately through its certified branch-and-bound route. -/
def ofSource (name src : String) : Except String Inst :=
  match Parser.parseModel src with
  | .error e => .error s!"{name}: parse: {e}"
  | .ok m =>
      let feasibility := { m with solve := .satisfy [] }
      match compileModelFull feasibility with
      | .error e => .error s!"{name}: compile: {e}"
      | .ok p => .ok { name, problem := toLCG p, model := some feasibility, compiled := some p }

def ofProblem (name : String) (p : LProblem) : Inst := { name, problem := p }

/-- Product of the domain sizes (oracle enumeration size). -/
def boxSize (p : LProblem) : Nat := p.domains.foldl (fun a d => a * d.length) 1

def sizeStr (p : LProblem) : String :=
  s!"{p.domains.length}v/{p.constraints.length}c"

/-- The scheduler's leaf predicate: the chronological solver's own leaf. -/
def leafOf (p : LProblem) : Assignment → Bool :=
  chronologicalLeaf p DomConstraint.satisfiedB

def propsOf (p : LProblem) : List Propagator :=
  clampProps p.domains (p.constraints.filterMap propagatorOfProved)

/-- Witness check via the verified checker (parsed instances) or the oracle. -/
def witnessCheck (inst : Inst) (a : Assignment) (oracle : Bool) : String :=
  match inst.model, inst.compiled with
  | some m, some cp =>
      let text := emitCertifiedSolution m (cp.toStore a)
      match LeanFzn.Checker.checkModelSolutionFast m text with
      | .accepted => "checker:OK"
      | .unsatisfied => "checker:REJECTED"
      | _ => "checker:ERR"
  | _, _ => if oracle then (if oracleWitnessOk inst.problem a then "oracle:OK" else "oracle:REJECTED")
            else (if (leafOf inst.problem) a then "leaf:OK" else "leaf:REJECTED")

def hist (xs : Array Nat) : String :=
  if xs.isEmpty then "n=0" else
  let mx := xs.foldl max 0
  let sum := xs.foldl (· + ·) 0
  let nonunit := (xs.filter (· > 1)).size
  -- mean with one decimal
  let m10 := sum * 10 / xs.size
  s!"n={xs.size} max={mx} mean={m10 / 10}.{m10 % 10} nonunit={nonunit}"

structure Row where
  name : String
  size : String
  verdict : String
  oracle : String
  chrono : String
  witness : String
  obs : Obs
  ms : Nat
  bareMs : Nat
  chronoMs : Nat
  agree : Bool   -- no wrong verdict

def runInst (bound oracleCap : Nat) (inv chrono : Bool) (inst : Inst) : IO Row := do
  let p := inst.problem
  let leaf := leafOf p
  let cfg0 : SchedulerConfig leaf := SchedulerConfig.init p.domains p.clauses (propsOf p)
  -- bare timing
  let t0 ← IO.monoMsNow
  let (bsteps, bcode) ← IO.lazyPure fun _ => bare (leaf := leaf) bound 0 cfg0
  let t1 ← IO.monoMsNow
  -- instrumented run
  let sols : Option (List Assignment) :=
    if inv && boxSize p ≤ oracleCap then some (oracleSolutions p) else none
  let (o, v) ← IO.lazyPure fun _ => loop (leaf := leaf) inv true sols bound 0 cfg0 {}
  let t2 ← IO.monoMsNow
  let _ := bsteps; let _ := bcode
  -- oracle
  let orSat? : Option Bool :=
    if boxSize p ≤ oracleCap then some (oracleSat p) else none
  -- chronological
  let t3 ← IO.monoMsNow
  let ch : Option (SearchResult × SearchStats) ←
    if chrono then (do let r ← IO.lazyPure fun _ => solveDomWithStats p; pure (some r))
    else pure none
  let t4 ← IO.monoMsNow
  let vstr := match v with | .sat _ => "SAT" | .unsat => "UNSAT" | .bound => "BOUND"
  let chStr := match ch with
    | some (.sat _, st) => s!"SAT(conf={st.conflicts},dec={st.decisions})"
    | some (.unsat, st) => s!"UNSAT(conf={st.conflicts},dec={st.decisions})"
    | some (.unknown, _) => "UNKNOWN"
    | none => "-"
  let orStr := match orSat? with
    | some b => (if b then "SAT" else "UNSAT")
    | none => "-"
  let wit := match v with
    | .sat a => witnessCheck inst a orSat?.isSome
    | _ => "-"
  -- agreement: verdicts must match oracle (when available) and chronological
  let chSat? : Option Bool := match ch with
    | some (.sat _, _) => some true | some (.unsat, _) => some false
    | some (.unknown, _) => none | none => none
  let vSat? : Option Bool := match v with
    | .sat _ => some true | .unsat => some false | .bound => none
  let okOr := match vSat?, orSat? with | some a, some b => a == b | _, _ => true
  let okCh := match vSat?, chSat? with | some a, some b => a == b | _, _ => true
  let okWit := !(wit.endsWith "REJECTED") && wit != "checker:ERR"
  return { name := inst.name, size := sizeStr p, verdict := vstr, oracle := orStr,
           chrono := chStr, witness := wit, obs := o, ms := t2 - t1,
           bareMs := t1 - t0, chronoMs := t4 - t3,
           agree := okOr && okCh && okWit && (match v with | .bound => false | _ => true) }

def Counts.str (c : Counts) : String :=
  s!"P{c.propagate}/D{c.decide}/A{c.analyze}/L{c.learn}/X{c.exclude}/F{c.fallback}"

def printRow (r : Row) : IO Unit := do
  let o := r.obs
  IO.println s!"== {r.name} [{r.size}] verdict={r.verdict} oracle={r.oracle} chrono={r.chrono} witness={r.witness} agree={r.agree}"
  IO.println s!"   steps={o.steps} phaseKinds(P/D/A/L/X/F)={o.ph.str} rawKinds={o.raw.str}"
  IO.println s!"   learned(UIP)={hist o.learnedSizes} DBend={o.lastDB} DBmax={o.maxDB} trailMax={o.maxTrail} maxLevel={o.maxLevel} logRegions={o.lastLog}"
  let skipped := (o.jumpDists.filter (· > 1)).size
  let maxd := o.jumpDists.foldl max 0
  IO.println s!"   backjumps={o.lastEvents.backjumps} skippedLevelJumps(dist>1)={skipped} maxJump={maxd} resolutions(rt)={o.lastEvents.reasonResolutions} asserts={o.lastEvents.assertingEnqueues} lastSrc={o.lastEvents.sourceLevel} lastTgt={o.lastEvents.targetLevel}"
  IO.println s!"   analyze sites (raw): {o.raw.analyze}  evidence analysis none={o.anaNone} some={o.anaSome} noCheckpoint={o.noCheckpoint} -> backjumpStep landed: jump={o.rawJump} fallback={o.rawFallback} exclude={o.rawExclude}; analysisBackjumpLevel={hist o.anaBackjumpLevels} analysisLearned={hist o.anaLearnedSizes} srcLevelMax={o.anaSrcLevels.foldl max 0}"
  IO.println s!"   analyzerEvents: expansions={o.expansions} scans={o.scans} marks={o.marks} postAssertPropagations={o.postAssertProps}"
  IO.println s!"   time: scheduler(bare)={r.bareMs}ms instrumented={r.ms}ms chrono={r.chronoMs}ms"
  IO.println s!"   invariants (exact,sem) e={o.nE}(@{o.checkedE}) f={o.nF} a={o.nA} b={o.nB}(@{o.checkedB}) c={o.nC}(@{o.checkedC}) d={o.nD} consumeRoot={o.nRoot}(@{o.checkedRoot})"
  if !o.causes.isEmpty then
    IO.println s!"   analysis=none causes: {o.causes.toList}"
  for n in o.notes do
    IO.println s!"   NOTE {n}"
  for v in o.viols do
    IO.println s!"   VIOLATION {v.kind} @step {v.step}: {v.detail}"

end LcgHarness

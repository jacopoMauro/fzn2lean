/-
File: Tests/Legacy/Solver/UIP/LcgProto.lean

Purpose (PLAN task R0; TEST-ONLY, UNCERTIFIED PROTOTYPE): a literal-complete
LCG scheduler step, built from test-local copies of the runtime pieces R0
changes, with every repair behind a flag so each one can be measured alone
(ablation). Everything else (propagators, `explainedDeduction`, `narrowState`,
`stepDecide`, `stepDecideSkip`, `splitData`, `leafWitness`, `canonicalPins`,
`canonicalFalsifiers`, `checkpointAt`, `filterFrame`, `ConflictAnalysis.ofUIP`,
the real analyzer `analyzeAtAllowance`) is IMPORTED and reused verbatim.

With every flag off, `protoStep` reproduces the real `phaseNext` route
(same arms, the real analyzer, the real canonical resume), except that the
post-assertion propagation runs as ordinary `propagate` steps instead of
inside `BackjumpPlan.perform` (same deductions, more steps).

Flags (the PLAN R0 fixes; names used in the ablation table):
  root   (1) analyzer: a working-clause literal false under the ORIGINAL
             domains is dropped like a level-0 falsifier.
  sem    (2) analyzer: the falsifier is the trail entry whose literal
             IMPLIES the negation (`impliesP`: bounds, `intNe` vs bounds,
             Booleans as 0/1); the learned literal is that entry's negation
             (LCG weakening, so the clause stays entailed and falsified).
  sync   (3) frame/trail synchronisation: after every frame tightening
             (propagation, assertion, resume) the implied bound literals
             (`x > lo-1`, `x <= hi`) and the fixing literal (`x = v`) of the
             touched slot are pushed with a domain explanation clause built
             from the trail literals that removed the values (+ root domain).
  resume (4) the canonical resume's falsifier entries get a reason: the
             decision-negation clause `[x_j != w, neg pin_0, ..., neg pin_{p-1}]`
             (entailed: the pinned prefix's other values were refuted or pruned).
  cycle  (5) analyzer: the falsifier of a REASON literal is searched only
             among trail entries strictly before the pivot being resolved
             (earliest such entry); the conflict clause may use any entry.
  route  (6) conflict routing: a falsified database clause, an implied
             literal rejected by the prefix, and a domain wipe-out are
             analysed as conflicts (with the falsified clause / the domain
             explanation clause) instead of being locally excluded.
  drop   (7) on a successful jump, drop the pending alternatives pushed at or
             after the restored checkpoint (they are covered by the restored
             frame plus the learned clause: standard CDCL, no sibling resume).
  late   (8) analyzer: a conflict with no literal at the current level is
             analysed at the highest level that falsifies it (or reported as
             a root contradiction when every falsifier is at the root).
  expl   (9) explained propagator conflicts: `int_ne` with both sides fixed
             to the same value reports `[x != c, y != c]` and the
             `all_different` pigeonhole reports its Hall clause (every
             slot takes a value outside the union of the current domains),
             instead of the EMPTY conflict clause (`propNe`/`propAllDiffLCG`).

Pure functions only; the analyzer loop is fuel-bounded (prototype). No
`sorry`, no axioms, no `native_decide`, no `partial` in the step pieces.
-/

import Tests.Legacy.Solver.UIP.LcgHarness
open LeanFzn.Compiler.Domains
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler LeanFzn.Integration
open LeanFzn LeanFzn.Solver LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Integration LeanFzn.Solver.Core

namespace LcgProto
open LcgHarness

structure Fixes where
  root : Bool := false
  sem : Bool := false
  sync : Bool := false
  resume : Bool := false
  cycle : Bool := false
  route : Bool := false
  drop : Bool := false
  late : Bool := false
  expl : Bool := false
  deriving Repr, BEq

def Fixes.analyzerOn (fx : Fixes) : Bool := fx.root || fx.sem || fx.cycle || fx.late

def Fixes.all : Fixes :=
  { root := true, sem := true, sync := true, resume := true, cycle := true,
    route := true, drop := true, late := true, expl := true }

def Fixes.names : List String := ["root", "sem", "sync", "resume", "cycle", "route", "drop", "late", "expl"]

def Fixes.set (fx : Fixes) (n : String) (b : Bool) : Fixes :=
  match n with
  | "root" => { fx with root := b }
  | "sem" => { fx with sem := b }
  | "sync" => { fx with sync := b }
  | "resume" => { fx with resume := b }
  | "cycle" => { fx with cycle := b }
  | "route" => { fx with route := b }
  | "drop" => { fx with drop := b }
  | "late" => { fx with late := b }
  | "expl" => { fx with expl := b }
  | _ => fx

def Fixes.str (fx : Fixes) : String :=
  let on := Fixes.names.filter fun n =>
    match n with
    | "root" => fx.root | "sem" => fx.sem | "sync" => fx.sync | "resume" => fx.resume
    | "cycle" => fx.cycle | "route" => fx.route | "drop" => fx.drop | "late" => fx.late | "expl" => fx.expl
    | _ => false
  if on.isEmpty then "none" else ",".intercalate on

/-! ## 1. Literal implication (fix 2) -/

/-- Booleans in their 0/1 order form: `b = true` is `x > 0`, `b = false` is
`x <= 0` (the `Value.intView` of a Boolean). -/
def intForm (l : Literal) : Literal :=
  match l.atom with
  | .boolEq s b =>
      let pos : Literal := if b then negLe s 0 else posLe s 0
      if l.positive then pos else pos.negate
  | _ => l

/-- `t` implies `g` (both normalized), syntactically, Booleans bridged. -/
def impliesP (t g : Literal) : Bool :=
  litEqB t g || LcgHarness.impliesLit (intForm t) (intForm g)

/-! ## 2. Domain explanations (fixes 3 and 6) -/

/-- The remaining domain of slot `s` (none for a decided slot). -/
def remDom (f : BranchFrame) (s : Nat) : Option Domain :=
  if s ∈ f.order then none else some (f.doms.getD s Dom.empty)

def maxOpt (acc : Option Int) (k : Int) : Option Int :=
  match acc with | none => some k | some a => some (if a < k then k else a)

def minOpt (acc : Option Int) (k : Int) : Option Int :=
  match acc with | none => some k | some a => some (if k < a then k else a)

/-- The negations of a set of trail literals on slot `s` that together remove
every value of `W`: the strongest lower-bound entry, the strongest upper-bound
entry, and one remover per value they do not cover. `none` if some value has
no remover (the frame and the trail disagree). -/
def explainRemoved (trail : List TrailEntry) (s : Nat) (W : List Value) :
    Option (List Literal) :=
  let kLo : Option Int := trail.foldl (fun acc e =>
    match e.literal.atom, e.literal.positive with
    | .intLe s' k, false => if s' == s then maxOpt acc k else acc
    | _, _ => acc) none
  let kHi : Option Int := trail.foldl (fun acc e =>
    match e.literal.atom, e.literal.positive with
    | .intLe s' k, true => if s' == s then minOpt acc k else acc
    | _, _ => acc) none
  let covLo (w : Value) : Bool :=
    match kLo, w.intView with | some k, some i => decide (i ≤ k) | _, _ => false
  let covHi (w : Value) : Bool :=
    match kHi, w.intView with | some k, some i => decide (k < i) | _, _ => false
  let rest := W.filter fun w => !covLo w && !covHi w
  let indiv : List (Option Literal) := rest.map fun w =>
    (trail.find? fun e => e.literal.atom.slot == s && !e.literal.valueHolds w).map
      fun e => e.literal.negate.norm
  if indiv.any (·.isNone) then none else
  let lo : List Literal :=
    match kLo with | some k => if W.any covLo then [posLe s k] else [] | none => []
  let hi : List Literal :=
    match kHi with | some k => if W.any covHi then [negLe s k] else [] | none => []
  some (lo ++ hi ++ indiv.filterMap id).eraseDups

/-- The entries `sync` pushes for slot `s` of frame `f` (fix 3): new lower
bound, new upper bound, fixing literal — each only when the trail does not
already imply it, each with its domain explanation clause. -/
def syncSlot (orig : List Domain) (trail : List TrailEntry) (lvl : Nat)
    (f : BranchFrame) (s : Nat) : List TrailEntry :=
  match remDom f s with
  | none => []
  | some d =>
    let ints := (Dom.enum d).filterMap Value.intView
    match ints with
    | [] => []
    | i0 :: is =>
      if ints.length != d.length then [] else
      let lo := is.foldl (fun a i => if i < a then i else a) i0
      let hi := is.foldl (fun a i => if a < i then i else a) i0
      let od := orig.getD s Dom.empty
      let push (tr : List TrailEntry) (lit : Literal) (W : List Value) : List TrailEntry :=
        if W.isEmpty then [] else
        if tr.any (fun e => impliesP e.literal lit) then [] else
        match explainRemoved tr s W with
        | none => []
        | some ex => [{ literal := lit, level := lvl, reason := some { clause := lit :: ex } }]
      let t1 := push trail (negLe s (lo - 1))
        ((Dom.enum od).filter fun w => match w.intView with | some i => decide (i < lo) | none => false)
      let tr1 := trail ++ t1
      let t2 := push tr1 (posLe s hi)
        ((Dom.enum od).filter fun w => match w.intView with | some i => decide (hi < i) | none => false)
      let tr2 := tr1 ++ t2
      let t3 : List TrailEntry :=
        match Dom.enum d with
        | [v] =>
            match valueLiteral s v with
            | some pin => push tr2 pin.norm ((Dom.enum od).filter fun w => w != v)
            | none => []
        | _ => []
      t1 ++ t2 ++ t3

/-- `syncSlot` over every remaining slot (used after a resume). -/
def syncAll (orig : List Domain) (trail : List TrailEntry) (lvl : Nat)
    (f : BranchFrame) : List TrailEntry :=
  (List.range f.doms.length).foldl (fun acc i =>
    acc ++ syncSlot orig (trail ++ acc) lvl f i) []

/-- The wipe-out clause of the first remaining slot whose domain is empty: the
negations of the removers of every original value (a VALID clause given the
original domain; falsified literal-for-literal by the trail). -/
def wipeoutClause (orig : List Domain) (trail : List TrailEntry) (f : BranchFrame) :
    Option Clause :=
  f.doms.zipIdx.findSome? fun p =>
    if p.1.isEmpty then explainRemoved trail p.2 (Dom.enum (orig.getD p.2 Dom.empty))
    else none

/-! ## 2b. Explained propagator conflicts (fix 9) -/

def neConflict (st : State) (i j : Nat) : Clause :=
  match Dom.enum (st.domains.getD i Dom.empty), Dom.enum (st.domains.getD j Dom.empty) with
  | [x], [_] =>
      match x with
      | .int c => [posNe i c, posNe j c]
      | .bool b => [posBool i (!b), posBool j (!b)]
      | _ => []
  | _, _ => []

/-- Hall clause of an `all_different` pigeonhole over the current domains. -/
def hallClause (orig : List Domain) (st : State) (is : List Nat) : Clause :=
  let ins := (is.filter (· < st.domains.length)).eraseDups
  let U : List Value := (ins.flatMap fun s => Dom.enum (st.domains.getD s Dom.empty)).foldl
    (fun acc v => if acc.any (·.eqB v) then acc else acc ++ [v]) []
  if ins.length ≤ U.length then [] else
  (ins.flatMap fun s =>
    ((Dom.enum (orig.getD s Dom.empty)).filter fun v => !U.any (·.eqB v)).filterMap fun v =>
      (valueLiteral s v).map (·.norm)).eraseDups

def explainedProps (orig : List Domain) (cs : List DomConstraint) : List Propagator :=
  cs.filterMap fun dc =>
    match dc with
    | .neSlot i j => some { watches := [], run := fun st =>
        (match propNe st i j with
         | .conflict [] => .conflict (neConflict st i j)
         | r => r) }
    | .allDiff is => some { watches := [], run := fun st =>
        (match propAllDiffLCG st is with
         | .conflict [] => .conflict (hallClause orig st is)
         | r => r) }
    | dc => propagatorOfProved dc

/-! ## 3. The analyzer (fixes 1, 2, 5, 8) -/

instance : Inhabited TrailEntry := ⟨{ literal := posLe 0 0, level := 0, reason := none }⟩

structure AState where
  work : List Clause
  skip : Option Literal
  /-- falsifiers of the clause being scanned must sit strictly before this index -/
  bound : Nat
  /-- marked current-level trail INDICES -/
  marks : List Nat
  learnt : List (Literal × Nat)

inductive ARes where
  | ok (below : List (Literal × Nat)) (uip : Literal)
  | root
  | fail (cause : String)

def firstIdx (tr : Array TrailEntry) (lim : Nat) (p : Literal → Bool) : Option Nat :=
  (List.range (min lim tr.size)).find? fun i => p tr[i]!.literal

def lastIdx (tr : Array TrailEntry) (lim : Nat) (p : Literal → Bool) : Option Nat :=
  (List.range (min lim tr.size)).reverse.find? fun i => p tr[i]!.literal

/-- The falsifier of working literal `q` (normalized). -/
def findFalsifier (fx : Fixes) (tr : Array TrailEntry) (bound : Nat) (q : Literal) :
    Option Nat :=
  let qn := q.negate.norm
  let lim := if fx.cycle then bound else tr.size
  let pick := if fx.cycle then firstIdx tr lim else lastIdx tr lim
  if fx.sem then pick fun l => impliesP l qn
  else
    match pick fun l => litEqB l qn with
    | some i => some i
    | none =>
        let q' := orderUpgrade ((tr.extract 0 lim).toList) q
        pick fun l => litEqB l q'.negate.norm

def failClass (orig : List Domain) (tr : Array TrailEntry) (q : Literal) (inReason : Bool) : String :=
  let w := if inReason then "reason" else "conflict"
  if LcgHarness.litFalseAtRoot orig q then s!"root-only({w})"
  else if semFalsified tr.toList q then s!"semantic-only({w})"
  else s!"unfalsified({w})"

inductive Mark where
  | ok (marks : List Nat) (learnt : List (Literal × Nat))
  | fail (cause : String)

def markP (fx : Fixes) (orig : List Domain) (tr : Array TrailEntry) (lvl : Nat)
    (st : AState) (q0 : Literal) : Mark :=
  let q := q0.norm
  if fx.root && LcgHarness.litFalseAtRoot orig q then .ok st.marks st.learnt
  else
    match findFalsifier fx tr st.bound q with
    | none => .fail (failClass orig tr q st.skip.isSome)
    | some i =>
        let e := tr[i]!
        let wl := e.literal.negate.norm
        if e.level == 0 then .ok st.marks st.learnt
        else if e.level == lvl then
          (if st.marks.contains i then .ok st.marks st.learnt else .ok (i :: st.marks) st.learnt)
        else if e.level > lvl then .fail "falsifier-above-level"
        else if st.learnt.any (fun p => litEqB p.1 wl) then .ok st.marks st.learnt
        else .ok st.marks ((wl, e.level) :: st.learnt)

inductive AStep where
  | done (r : ARes)
  | next (st : AState)

def analyzeNextP (fx : Fixes) (orig : List Domain) (tr : Array TrailEntry) (lvl : Nat)
    (st : AState) : AStep :=
  match st.work with
  | [] =>
      match st.marks.max? with
      | none => .done (.fail "no-current-level-mark")
      | some i =>
          let marks' := st.marks.filter (· != i)
          let e := tr[i]!
          if marks'.isEmpty then .done (.ok st.learnt e.literal)
          else
            match e.reason with
            | none => .done (.fail "pivot-is-decision-but-other-marks")
            | some r => .next { work := [r.clause], skip := some e.literal, bound := i,
                                marks := marks', learnt := st.learnt }
  | [] :: cs => .next { st with work := cs }
  | (q0 :: qs) :: cs =>
      let q := q0.norm
      if skipEq st.skip q then .next { st with work := qs :: cs }
      else
        match markP fx orig tr lvl st q with
        | .fail c => .done (.fail c)
        | .ok m l => .next { st with work := qs :: cs, marks := m, learnt := l }

def analyzeLoopP (fx : Fixes) (orig : List Domain) (tr : Array TrailEntry) (lvl : Nat) :
    Nat → AState → ARes
  | 0, _ => .fail "fuel-exhausted"
  | n + 1, st =>
      match analyzeNextP fx orig tr lvl st with
      | .done r => r
      | .next st' => analyzeLoopP fx orig tr lvl n st'

def protoFuel (n : Nat) (c : Clause) : Nat := 4 * n * n + 4 * c.length + 256

/-- The prototype analysis of conflict clause `c` at level `lvl`. -/
def analyzeP (fx : Fixes) (orig : List Domain) (trail : List TrailEntry) (lvl : Nat)
    (c : Clause) : ARes :=
  let tr := trail.toArray
  let run (l : Nat) (bound : Nat) : ARes :=
    analyzeLoopP fx orig tr l (protoFuel tr.size c)
      { work := [c], skip := none, bound := bound, marks := [], learnt := [] }
  match run lvl tr.size with
  | .fail "no-current-level-mark" =>
      if !fx.late then .fail "no-current-level-mark" else
      -- every falsifier sits below `lvl`: re-run at the highest falsifying level
      let lv : List (Option Nat) := c.filterMap fun q =>
        if fx.root && LcgHarness.litFalseAtRoot orig q.norm then none
        else some ((findFalsifier fx tr tr.size q.norm).map fun i => tr[i]!.level)
      if lv.any (·.isNone) then .fail "late-unfalsified" else
      let m := (lv.filterMap id).foldl max 0
      if m == 0 then .root
      else
        let bnd := ((List.range tr.size).find? fun i => tr[i]!.level > m).getD tr.size
        match analyzeLoopP fx orig tr m (protoFuel tr.size c)
            { work := [c], skip := none, bound := bnd, marks := [], learnt := [] } with
        | .ok b u => .ok b u
        | .root => .root
        | .fail x => .fail ("late:" ++ x)
  | r => r

/-! ## 4. The prototype scheduler step -/

/-- Copy of `scanDatabase` reporting the falsified clause when `route`. -/
def scanDatabaseP (route : Bool) (original : List Clause) (f : BranchFrame) :
    List Clause → PruningEvent
  | [] => .stable
  | c :: rest =>
    match clauseRemaining f c with
    | [] => .conflict (if route then [c] else [])
    | [l] => if productive l f then .implied l c false (!(original.contains c))
             else scanDatabaseP route original f rest
    | _ => scanDatabaseP route original f rest

/-- Copy of `nextPruningEvent` over `scanDatabaseP` (identical except for the
conflict payload, so `explainedDeduction` is reused unchanged). -/
def nextPruningEventP (route : Bool) (original : List Clause) (props : List Propagator)
    (f : BranchFrame) (db : List Clause) : PruningEvent :=
  match scanDatabaseP route original f db with
  | .stable => if frameViewedB f then scanPropagators f props else .stable
  | .conflict cs => .conflict cs
  | .implied l c learnReason fromLearned =>
      if frameLiveB f then .implied l c learnReason fromLearned else .stable

/-- One conflict site, as observed. -/
structure Site where
  clause : Clause
  level : Nat
  outcome : String      -- "ok", "root", or the failure cause
  learned : Clause := []
  target : Nat := 0

inductive PStep (leaf : Assignment → Bool) where
  | propagate (n : SchedulerConfig leaf) (newReasons : List Clause)
  | decide (n : SchedulerConfig leaf)
  | skipDecide (n : SchedulerConfig leaf)
  | sat (w : Assignment)
  | unsat (why : String) (site : Option Site)
  | learn (n : SchedulerConfig leaf) (site : Site) (src tgt dropped : Nat)
      (newReasons : List Clause)
  | consume (n : SchedulerConfig leaf) (cause : String) (site : Option Site)
      (newReasons : List Clause)

/-- Copy of the canonical resume (`resumePending`) with the optional
falsifier reasons (fix 4) and synchronised bounds (fix 3). -/
def resumeP (fx : Fixes) (orig : List Domain) (bs : BranchState leaf) (f : BranchFrame) :
    BranchState leaf × List Clause :=
  let pins := canonicalPins f
  let fals := canonicalFalsifiers orig f
  let pinNegs := pins.map fun e => e.literal.negate.norm
  let fals' := if fx.resume then
      fals.map fun e => { e with reason := some { clause := e.literal :: pinNegs } }
    else fals
  let tr := pins ++ fals'
  let lvl := f.level
  let extra := if fx.sync then syncAll orig tr lvl f else []
  let newR := (fals' ++ extra).filterMap fun e => e.reason.map (·.clause)
  ({ frame := f, trail := tr ++ extra, level := lvl, learned := bs.learned }, newR)

/-- Resume the next pending alternative (the real `stepConsume` with
`resumeP`). -/
def consumeP (fx : Fixes) (cfg : SchedulerConfig leaf) (cause : String)
    (site : Option Site) : PStep leaf :=
  match cfg.pending with
  | [] => .unsat ("exhausted after " ++ cause) site
  | f :: rest =>
      let (bs, newR) := resumeP fx cfg.orig cfg.branch f
      .consume { cfg with branch := bs, checkpoints := [], pending := rest,
                          status := .active, conflict := none } cause site newR

/-- The conflict site: analyse, then jump (learn/backjump/assert) or fall back. -/
def conflictP (fx : Fixes) (cfg : SchedulerConfig leaf) (c : Clause)
    (learned : List Clause) : PStep leaf :=
  let lvl := cfg.branch.level
  if lvl = 0 then .unsat "root-level conflict" (some { clause := c, level := 0, outcome := "root" })
  else
  let res : ARes :=
    if fx.analyzerOn then analyzeP fx cfg.orig cfg.branch.trail lvl c
    else
      match analyzeAtAllowance cfg.orig cfg.branch.trail lvl c with
      | some (b, u) => .ok b u
      | none => .fail "real-analyzer-none"
  let fallback (why : String) (site : Site) : PStep leaf :=
    consumeP fx (stepChronologicalFallback cfg (branchRegion cfg)) ("fallback:" ++ why) (some site)
  match res with
  | .root => .unsat "late root contradiction" (some { clause := c, level := lvl, outcome := "root" })
  | .fail why => fallback why { clause := c, level := lvl, outcome := why }
  | .ok below uip =>
      let an := (ConflictAnalysis.ofUIP below uip).normalized
      let site : Site := { clause := c, level := lvl, outcome := "ok", learned := an.learned,
                           target := an.backjumpLevel }
      match checkpointAt cfg.checkpoints an.backjumpLevel with
      | none => fallback "noCheckpoint" site
      | some cp =>
          match filterFrame an.asserting cp.frame with
          | none => consumeP fx (stepLocalExclude cfg learned (checkpointRegion cp)) "assertReject" (some site)
          | some g =>
              let tgt := an.backjumpLevel
              let tr0 := cp.trail ++ [{ literal := an.asserting.norm, level := tgt,
                                        reason := some { clause := an.learned } }]
              let ex := if fx.sync then syncSlot cfg.orig tr0 tgt g an.asserting.atom.slot else []
              let pend := if fx.drop then cfg.pending.dropWhile (fun f => f.level ≥ cp.frame.level)
                          else cfg.pending
              let n : SchedulerConfig leaf :=
                { cfg with
                  branch := { frame := g, trail := tr0 ++ ex, level := tgt,
                              learned := learned ++ (an.learned :: cfg.branch.learned) }
                  checkpoints := cfg.checkpoints.filter fun cp => cp.level ≤ tgt
                  pending := pend
                  status := .active
                  conflict := none
                  events := cfg.events.recordBackjump lvl tgt
                  stats := cfg.stats.add { learnedClauses := learned.length + 1 } }
              .learn n site lvl tgt (cfg.pending.length - pend.length)
                (ex.filterMap fun e => e.reason.map (·.clause))

/-- THE PROTOTYPE STEP (phase level: fallbacks/exclusions are composed with
the consume, as `phaseNext` does). -/
def protoStep (fx : Fixes) (cfg : SchedulerConfig leaf) : PStep leaf :=
  match cfg.status with
  | .dead => consumeP fx cfg "dead" none
  | .active =>
    let wipe : Option Clause :=
      if fx.route then wipeoutClause cfg.orig cfg.branch.trail cfg.branch.frame else none
    match wipe with
    | some c => conflictP fx cfg c []
    | none =>
    match explainedDeduction cfg.original cfg.props cfg.branch with
    | some d =>
        let bs1 := narrowState cfg.branch d.frame d.literal d.reason d.learned
        let ex := if fx.sync then syncSlot cfg.orig bs1.trail bs1.level d.frame d.literal.atom.slot
                  else []
        .propagate { cfg with branch := { bs1 with trail := bs1.trail ++ ex }, status := .active,
                              stats := cfg.stats.add { propagations := 1 } }
          (ex.filterMap fun e => e.reason.map (·.clause))
    | none =>
      match nextPruningEventP fx.route cfg.original cfg.props cfg.branch.frame cfg.branch.learned with
      | .conflict cs =>
          let learned := cs.filter fun c => !(cfg.branch.learned.contains c)
          match cs with
          | [] => consumeP fx (stepLocalExclude cfg learned (branchRegion cfg)) "exclude:emptyConflict"
              (if cfg.branch.level = 0 then none
               else some { clause := [], level := cfg.branch.level, outcome := "empty-conflict-clause" })
          | c :: _ => conflictP fx cfg c learned
      | .implied l c lr _ =>
          let learned := if lr && !(cfg.branch.learned.contains c) then [c] else []
          match filterFrame l cfg.branch.frame with
          | none =>
              if fx.route then conflictP fx cfg c learned
              else consumeP fx (stepLocalExclude cfg learned (branchRegion cfg)) "exclude:filter" none
          | some _ => stableP cfg
      | .stable => stableP cfg
where
  stableP (cfg : SchedulerConfig leaf) : PStep leaf :=
    match leafWitness leaf cfg with
    | some w => .sat w
    | none =>
        match splitData cfg.branch.frame cfg.prio with
        | some (l, k, v, vs) =>
            if TrailRedundant cfg.branch.trail l then .skipDecide (stepDecideSkip cfg k v)
            else .decide (stepDecide cfg k v vs l)
        | none => consumeP fx (stepLocalExclude cfg [] (branchRegion cfg)) "exclude:split" none

end LcgProto

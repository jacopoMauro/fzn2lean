/-
Runtime tests for N12 dynamic search: conflict activity, weighted degree,
phase saving and restarts.

Run with:
  lake env lean --run Tests/Engine/DynamicTest.lean

The synthetic instances are evaluated in-process through the certified
`coreSolve` entry; the checks are deterministic (no wall-clock caps).
Benchmark strength is measured by the matrix runner, not by this test.
-/
import LeanFzn.Engine.Search

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Engine LeanFzn.Integration

namespace Tests.Engine

/-- Abort with a diagnostic on the first failing check. -/
def fail (msg : String) : IO Unit := do
  IO.eprintln s!"DynamicTest FAIL: {msg}"
  IO.Process.exit 1

def check (msg : String) (b : Bool) : IO Unit :=
  if b then pure () else fail msg

/-! ## Synthetic compiled problems -/

/-- A compiled problem with the supplied domains and constraints. -/
def mkProblem (ds : List Dom) (dcs : List DomConstraint) :
    CompiledProblem DomConstraint :=
  { names := []
    domains := ds
    constraints := dcs
    objective := ()
    source := default
    toStore := fun _ _ => none }

/-- Pigeonhole `P` pigeons into `H` holes, as a Boolean clause problem.
    `act` reduces the refutation tree on PHP(4,3) and PHP(5,4). -/
def php (P H : Nat) : CompiledProblem DomConstraint :=
  let ds := List.replicate (P * H) ⟨.small true 0 0b11⟩
  let pos := (List.range P).map fun p =>
    .boolClauseSlot ((List.range H).map fun h => p * H + h) []
  let neg := (List.range H).foldr (fun h acc =>
    (List.range P).foldr (fun p acc2 =>
      ((List.range P).filter fun q => p < q).foldr (fun q acc3 =>
        .boolClauseSlot [] [p * H + h, q * H + h] :: acc3) acc2) acc) []
  mkProblem ds (pos ++ neg)

/-- Two ternary slots multiplied into a fixed 1: a decision conflict forces
    first-UIP learning and a backjump, so the SAT branch exercises activity
    and phase storage as well as value selection. -/
def conflictProblem : CompiledProblem DomConstraint :=
  mkProblem
    [⟨.small false 0 0b111⟩, ⟨.small false 0 0b111⟩, ⟨.small false 0 0b10⟩]
    [.timesSlot 0 1 2]

/-- A mixed-domain 5-clique: unsat, with one slot of four values and four of
    three values, so `domwdeg` weights the learned-clause slots differently
    from `act` even though the tiny search tree is largely propagation-driven. -/
def mixedClique : CompiledProblem DomConstraint :=
  let ds : List Dom :=
    [⟨.small false 0 0b1111⟩, ⟨.small false 0 0b111⟩, ⟨.small false 0 0b111⟩,
     ⟨.small false 0 0b111⟩, ⟨.small false 0 0b111⟩]
  let idx := List.range 5
  let dcs := idx.foldr (fun i acc =>
    idx.foldr (fun j acc2 => if i < j then .neSlot i j :: acc2 else acc2) acc) []
  mkProblem ds dcs

def cfg (v : VarStrategy) (vl : ValStrategy) (r : RestartStrategy := .none)
    (b : Nat := 100) : SearchConfig :=
  { var := v, val := vl, restart := r, restartBase := b }

def verdictName : CoreResult → String
  | .sat _ => "sat"
  | .unsat => "unsat"
  | .gaveUp => "gaveUp"

def engineStatsLine (s : EngineStats) : String :=
  s!"decisions={s.decisions} conflicts={s.conflicts} \
propagations={s.propagations} learned={s.learned} gaveUp={s.gaveUp}"

def statsLine {p : CompiledProblem DomConstraint} {T : LitTable}
    (st : EngineState p T) : String :=
  s!"{engineStatsLine st.stats} restarts={st.restarts}"

def checkSatAnswer (label : String) (p : CompiledProblem DomConstraint)
    (a : List Value) : IO Unit := do
  check s!"{label}: SAT assignment in allAssigns"
    ((allAssigns p.domains).contains a)
  check s!"{label}: SAT assignment accepted" (accepts p a)

/-- No enumerated box member is accepted. -/
def noAccepted (p : CompiledProblem DomConstraint) : Bool :=
  (allAssigns p.domains).all fun a => !accepts p a

/-! ## Entry copy with observable `EngineState`

`coreSolveFull` reports only `EngineStats`, which has no restart counter.
This copy repeats the certified entry verbatim up to the `search` call and
returns the final state, so the tests can observe `st.restarts` and (with the
optional `phases` argument) the effect of carried saved phases. -/

def emptyTable : LitTable := {}

def searchWithPhases (p : CompiledProblem DomConstraint) (o : SearchConfig)
    (fuel : Nat) (phases : Array Value) :
    Option (CoreResult × EngineState p emptyTable) :=
  let T : LitTable := emptyTable
  match initState p T with
  | none => none
  | some st0 =>
      let prio := annotPrioArray p
      let orders := Engine.configOrders p o
      let st0 := { st0 with phases := phases }
      match addSeedClauses p T st0 with
      | (st, some _) =>
          some (.unsat, { st with
            stats := { st.stats with conflicts := st.stats.conflicts + 1 } })
      | (st, none) =>
          match st.db.emptyConflict? with
          | some _ => some (.unsat, st)
          | none =>
              let (db, out) := st.db.propagateUnits p T st.doms
              match out with
              | .none =>
                  let st := { st with db := db }
                  some (search p T st.doms o prio orders st #[] fuel)
              | .prune ps =>
                  let st := { st with db := db }
                  some (search p T st.doms o prio orders st
                    (pushClausePrunes #[] ps) fuel)
              | .conflict ec _ =>
                  let a := analyze p T st.doms st ec fuel
                  let st := { st with db := db }
                  if !a.ok then
                    some (.gaveUp, { st with stats := { st.stats with gaveUp := 1 } })
                  else
                    match a.learned with
                    | none =>
                        some (.gaveUp, { st with stats := { st.stats with gaveUp := 1 } })
                    | some lc =>
                        if lc.lits.isEmpty then some (.unsat, st)
                        else some (.gaveUp, { st with
                          stats := { st.stats with gaveUp := 1 } })

def coreSolveState (p : CompiledProblem DomConstraint) (o : SearchConfig)
    (fuel : Nat) : Option (CoreResult × EngineState p emptyTable) :=
  searchWithPhases p o fuel #[]

/-! ## Activity, weighted degree and selection -/

def activityChecks : IO Unit := do
  match initState conflictProblem emptyTable with
  | none => fail "activity: entry rejected"
  | some st0 =>
      -- Domain sizes 2, 4 and 10; activity starts at zero.
      let st : EngineState conflictProblem emptyTable :=
        { st0 with
          doms := #[.bounds 0 1, .bounds 0 3, .bounds 0 9]
          activity := #[0.0, 0.0, 0.0] }
      let lits : Array PLit :=
        #[pLit (negNe 0 0), pLit (negNe 1 0), pLit (negNe 2 0)]
      let oAct := cfg .act .act
      let oDom := cfg .domwdeg .act
      let a := bumpActivity st oAct lits
      check "activity: act bumps every learned slot by 1"
        (a.activity.getD 0 0 == 1.0 && a.activity.getD 1 0 == 1.0 &&
         a.activity.getD 2 0 == 1.0)
      let d := bumpActivity st oDom lits
      let d0 := d.activity.getD 0 0
      let d1 := d.activity.getD 1 0
      let d2 := d.activity.getD 2 0
      check "activity: domwdeg weights by 1/|dom|"
        (0.4999 < d0 && d0 < 0.5001 &&
         0.2499 < d1 && d1 < 0.2501 &&
         0.0999 < d2 && d2 < 0.1001)
      let a2 := bumpActivity a oAct #[pLit (negNe 0 0)]
      let a20 := a2.activity.getD 0 0
      check "activity: decay 0.95 before the next bump"
        (1.9499 < a20 && a20 < 1.9501)
      let untouched := bumpActivityIf st (cfg .minc .act) lits
      check "activity: non-activity strategies leave the array untouched"
        (untouched.activity.all fun x => x == 0.0)
      -- Highest activity wins; ties fall back to the minc rule.
      let stSel : EngineState conflictProblem emptyTable :=
        { st with activity := #[0.1, 2.0, 0.5] }
      check "selectSlot: act picks the highest activity"
        (selectSlot conflictProblem stSel oAct #[] == some 1)
      check "selectSlot: minc picks the smallest domain"
        (selectSlot conflictProblem stSel (cfg .minc .act) #[] == some 0)
      let stDom : EngineState conflictProblem emptyTable :=
        { st with activity := #[0.1, 0.05, 0.2] }
      check "selectSlot: domwdeg reads the weighted scores"
        (selectSlot conflictProblem stDom oDom #[] == some 2)
      -- Cached tie-breaks: equal activity falls back to the smaller domain,
      -- equal activity and size keeps the lowest index; equal annotation
      -- priority follows the same two rules.
      let stTieAct : EngineState conflictProblem emptyTable :=
        { st with activity := #[1.0, 1.0, 1.0] }
      check "selectSlot: act ties fall back to the smallest domain"
        (selectSlot conflictProblem stTieAct oAct #[] == some 0)
      let stTieSize : EngineState conflictProblem emptyTable :=
        { st with
          doms := #[.bounds 0 3, .bounds 0 3, .bounds 0 3]
          activity := #[1.0, 1.0, 1.0] }
      check "selectSlot: act ties keep the lowest index"
        (selectSlot conflictProblem stTieSize oAct #[] == some 0)
      let stTieUpdate : EngineState conflictProblem emptyTable :=
        { st with
          doms := #[.bounds 0 1, .bounds 0 9, .bounds 0 3]
          activity := #[0.5, 2.0, 2.0] }
      check "selectSlot: act tie uses the cached best size"
        (selectSlot conflictProblem stTieUpdate oAct #[] == some 2)
      let stTieDom : EngineState conflictProblem emptyTable :=
        { st with activity := #[0.5, 0.5, 0.1] }
      check "selectSlot: domwdeg ties fall back to the smallest domain"
        (selectSlot conflictProblem stTieDom oDom #[] == some 0)
      let oAnnot := cfg .annot .act
      check "selectSlot: annot priority wins"
        (selectSlot conflictProblem st oAnnot #[0, 2, 1] == some 1)
      check "selectSlot: annot ties fall back to the smallest domain"
        (selectSlot conflictProblem st oAnnot #[2, 2, 0] == some 0)
      -- Search selects before it checks for a fixed leaf, so a fixed state
      -- must report no selectable slot while still yielding its assignment.
      let stFixed : EngineState conflictProblem emptyTable :=
        { st with doms := #[.bounds 0 0, .bounds 1 1, .bounds 2 2] }
      check "selectDecision: no selectable slot at a fixed leaf"
        (selectDecision conflictProblem stFixed oAct #[] [] == none)
      check "fixedAssignment: fixed leaf still yields its assignment"
        (fixedAssignment stFixed == some [.int 0, .int 1, .int 2])
      -- Fixed (slot 0) and empty (slot 1) slots are never selected, even
      -- with the highest scores.
      let stSkip : EngineState conflictProblem emptyTable :=
        { st with
          doms := #[.bounds 0 0, .bounds 1 0, .bounds 0 3]
          activity := #[100.0, 100.0, 1.0] }
      check "selectSlot: never picks a fixed or empty slot"
        (selectSlot conflictProblem stSkip oAct #[] == some 2)

/-! ## Phase saving -/

def phaseChecks : IO Unit := do
  check "phase: saved integer member is reused"
    (phaseLiteral 0 (.bounds 0 2) (.int 2) == some (negLe 0 1))
  check "phase: saved minimum keeps the ascending form"
    (phaseLiteral 0 (.bounds 0 2) (.int 0) == some (posLe 0 0))
  check "phase: saved interior value uses negNe"
    (phaseLiteral 0 (.bounds 0 4) (.int 2) == some (negNe 0 2))
  check "phase: removed integer is rejected"
    (phaseLiteral 0 (.bounds 0 1) (.int 2) == none)
  check "phase: saved Boolean member is reused"
    (phaseLiteral 0 (.bool 3) (.bool true) == some (posBool 0 true))
  check "phase: decidedValue maps an equality literal"
    (decidedValue? (negNe 0 2) == some (.int 2))
  check "phase: decidedValue maps the Boolean literal"
    (decidedValue? (posBool 0 false) == some (.bool false))
  check "phase: val=act tries the saved integer"
    (selectValue 0 (.bounds 0 2) (cfg .act .act) .none (some (.int 2)) ==
      some (negLe 0 1))
  check "phase: val=act falls back when the saved value is gone"
    (selectValue 0 (.bounds 0 1) (cfg .act .act) .none (some (.int 2)) ==
      some (posLe 0 0))
  check "phase: val=min ignores the saved phase"
    (selectValue 0 (.bounds 0 2) (cfg .minc .min) .none (some (.int 2)) ==
      some (posLe 0 0))
  check "phase: static var=minc keeps pre-N12 act behaviour"
    (selectValue 0 (.bounds 0 2) (cfg .minc .act) .none (some (.int 2)) ==
      some (posLe 0 0))
  -- Carried phases are what make saving active: `coreSolveFull` starts with
  -- an empty phase array and ascending decisions only ever store the minimum,
  -- so a fresh run is observably inert.  A state seeded with the opposite
  -- phase (the incremental-round use case) changes the refutation tree.
  let allTrue : Array Value := (List.replicate 12 (.bool true)).toArray
  match coreSolveFull (php 4 3) (cfg .act .act) 10000,
        searchWithPhases (php 4 3) (cfg .act .act) 10000 allTrue,
        searchWithPhases (php 4 3) (cfg .act .min) 10000 allTrue with
  | (.unsat, base), some (.unsat, saved), some (.unsat, ignored) =>
      IO.println s!"phase saving: fresh(act/act) {engineStatsLine base}; \
seeded(act/act) {statsLine saved}; seeded(act/min) {statsLine ignored}"
      check "phase: seeded saved phases change the search tree"
        (saved.stats.decisions != base.decisions)
      check "phase: val=min still ignores seeded phases"
        (ignored.stats.decisions == base.decisions)
  | (.unsat, _), _, _ => fail "phase: seeded phase run did not finish UNSAT"
  | _, _, _ => fail "phase: baseline did not finish UNSAT"

/-! ## Restart schedules -/

def restartChecks : IO Unit := do
  let seq := [luby 1, luby 2, luby 3, luby 4, luby 5, luby 6, luby 7,
              luby 8, luby 9, luby 10, luby 11, luby 12, luby 13, luby 14, luby 15]
  check s!"restart: Luby prefix is wrong: {seq}"
    (seq == [1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8])
  check "restart: geometric thresholds double"
    (restartThreshold (cfg .minc .act .geom 2) 0 == 2 &&
     restartThreshold (cfg .minc .act .geom 2) 1 == 4 &&
     restartThreshold (cfg .minc .act .geom 2) 3 == 16)
  check "restart: Luby thresholds use the sequence"
    (restartThreshold (cfg .minc .act .luby 3) 0 == 3 &&
     restartThreshold (cfg .minc .act .luby 3) 2 == 6 &&
     restartThreshold (cfg .minc .act .luby 3) 6 == 12)
  match coreSolveFull (php 4 3) (cfg .act .act) 10000 with
  | (.unsat, base) =>
      match coreSolveState (php 4 3) (cfg .act .act .geom 2) 10000 with
      | some (.unsat, st) =>
          IO.println s!"restart: geom base 2 on PHP(4,3): {statsLine st} \
(no-restart {engineStatsLine base})"
          check "restart: geometric schedule actually restarts" (st.restarts > 0)
          check "restart: geometric schedule changes the search tree"
            (st.stats.decisions != base.decisions ||
             st.stats.conflicts != base.conflicts)
      | _ => fail "restart: geometric run did not finish UNSAT"
      match coreSolveState (php 4 3) (cfg .act .act .luby 2) 10000 with
      | some (.unsat, st) =>
          IO.println s!"restart: Luby base 2 on PHP(4,3): {statsLine st}"
          check "restart: Luby schedule actually restarts" (st.restarts > 0)
      | _ => fail "restart: Luby run did not finish UNSAT"
  | _ => fail "restart: no-restart baseline did not finish UNSAT"

/-! ## Verdict agreement on the synthetic family -/

def checkAgreement (label : String) (p : CompiledProblem DomConstraint)
    (base : CoreResult) (r : CoreResult) : IO Unit := do
  match base, r with
  | .sat a, .sat b =>
      checkSatAnswer s!"{label} (base)" p a
      checkSatAnswer s!"{label} (config)" p b
  | .unsat, .unsat =>
      check s!"{label}: UNSAT leaves no accepted assignment" (noAccepted p)
  | _, .gaveUp => fail s!"{label}: unexpected give-up"
  | _, _ => fail s!"{label}: verdict disagreement (base={verdictName base}, \
config={verdictName r})"

def agreementChecks : IO Unit := do
  let configs : List (String × SearchConfig) := [
    ("act/act", cfg .act .act),
    ("act/min", cfg .act .min),
    ("domwdeg/act", cfg .domwdeg .act),
    ("domwdeg/min", cfg .domwdeg .min),
    ("act/geom2", cfg .act .act .geom 2),
    ("act/luby2", cfg .act .act .luby 2)]
  for (name, p) in
      [("php4_3", php 4 3), ("php5_4", php 5 4),
       ("mixed-clique", mixedClique), ("conflict", conflictProblem)] do
    let (base, baseSt) := coreSolveFull p (cfg .minc .act) 10000
    IO.println s!"synthetic {name} minc/act: {verdictName base} {engineStatsLine baseSt}"
    for (label, o) in configs do
      let (r, st) := coreSolveFull p o 10000
      IO.println s!"synthetic {name} {label}: {verdictName r} {engineStatsLine st}"
      checkAgreement s!"{name} {label}" p base r

def run : IO UInt32 := do
  IO.println "DynamicTest: N12 activity, domwdeg, phase saving, restarts"
  activityChecks
  phaseChecks
  restartChecks
  agreementChecks
  IO.println "DynamicTest: OK"
  return 0

end Tests.Engine

open Tests.Engine in
def main : IO UInt32 := Tests.Engine.run

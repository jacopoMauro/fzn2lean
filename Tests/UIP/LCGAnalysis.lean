import LeanFzn.Integration.Chronological
import LeanFzn.Solver
open LeanFzn.Compiler.Domains
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler LeanFzn.Integration


/-!
# P1 analysis/backjump regression tests (PLAN P1.E)

Executable fixtures for the first-UIP / backjumping work packages. These
tests *assert that the new operations occurred* — an analysis that
actually resolves multiple reasons, an actual jump over an irrelevant
decision level, exact restoration with a single asserting enqueue,
permanent exhaustion — rather than only checking verdicts.

Checked here:

* `analyzeTrail` on a hand-built trail with two current-level marks
  resolves the pivot's reason, records the below-level falsifier, and
  selects the first UIP (multiple reason resolutions, not just one
  literal);
* the computed `backjumpLevel` jumps over an irrelevant decision level
  (3 → 1, skipping level 2) and the learned clause contains exactly one
  current-level literal;
* `ConflicShape` classification: a level-0 falsified clause is a root
  conflict, an empty clause is a local explanation (never global UNSAT);
* sparse-domain singleton collapse through `removedValues` /
  `derivedLowerWitnesses` (`{0,2,5}` minus `0` and `2`);
* Boolean/int decision-literal distinction (`valueLiteral`);
* duplicate values and repeated deductions: a stable frame records
  nothing (`explainedTrail` adds no entry without a mass decrease);
* exact restoration: `BackjumpPlan.execute` restores the checkpoint's
  trail and appends exactly one asserting entry, keeping the global
  learned database;
* permanent exhaustion: registered prefixes survive further
  registrations;
* the input-dependent `analysisAllowance` covers a clause length the
  historical constant cannot.
-/

open LeanFzn LeanFzn.Solver LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Integration LeanFzn.Solver.Core

private structure TestState where
  passed : Nat
  failed : Nat

private def TestState.check (st : TestState) (name : String) (ok : Bool) :
    IO TestState := do
  if ok then
    IO.println s!"ok {name}"
    pure { st with passed := st.passed + 1 }
  else
    IO.eprintln s!"FAIL {name}"
    pure { st with failed := st.failed + 1 }

private def vi (i : Int) : Value := .int i

/-- Structural comparison for literals and trail entries (the core
types derive only `Repr`). -/
private def litEq (a b : Literal) : Bool := decide (a = b)

private def entryEq (a b : TrailEntry) : Bool :=
  litEq a.literal b.literal && a.level == b.level

private def trailEq (a b : List TrailEntry) : Bool :=
  a.length == b.length && (a.zip b).all (fun p => entryEq p.1 p.2)

/-- Structural comparison for clauses (core `Clause` is a list of
literals and has no `BEq` at this level). -/
private def litEqs (a b : Clause) : Bool :=
  a.length == b.length && (a.zip b).all (fun p => litEq p.1 p.2)

/-- Structural comparison for branch states (the structure has no `BEq`
because it carries `Option Reason`). -/
private def stateEq (a b : BranchState (fun _ => true)) : Bool :=
  a.frame == b.frame && trailEq a.trail b.trail && a.level == b.level &&
  (a.learned.length == b.learned.length &&
   (a.learned.zip b.learned).all (fun p => litEqs p.1 p.2))

/-- A trail entry with no reason (a decision). -/
private def dec (l : Literal) (lvl : Nat) : TrailEntry :=
  { literal := l, level := lvl, reason := none }

/-- A trail entry with a reason clause. -/
private def imp (l : Literal) (lvl : Nat) (c : Clause) : TrailEntry :=
  { literal := l, level := lvl, reason := some { clause := c } }

/-- THE multi-resolution fixture.

Trail (chronological):
  A = level 1 decision  `x0 ≤ 5`
  D = level 2 decision  `x3 ≠ 1`     (irrelevant level: never used)
  B = level 3 decision  `x1 ≤ 7`
  C = level 3 implication `x2 ≤ 9`, reason `[x2 ≤ 9, ¬(x0 ≤ 5)]`

Conflict clause `[¬(x1 ≤ 7), ¬(x2 ≤ 9)]`: both literals are falsified at
level 3, and resolving the latest mark C against its reason records the
below-level falsifier `¬(x0 ≤ 5)` (level 1). The first UIP is B's
literal `x1 ≤ 7`, so the analysis jumps 3 → 1 over the irrelevant level
2. -/
private def multiTrail : List TrailEntry :=
  [ dec (posLe 0 5) 1
  , dec (posNe 3 1) 2
  , dec (posLe 1 7) 3
  , imp (posLe 2 9) 3 [posLe 2 9, negLe 0 5] ]

private def multiConflict : Clause := [negLe 1 7, negLe 2 9]

/-- How many literals of `c` are falsified by a level-`lvl` trail entry. -/
private def currentLevelLits (trail : List TrailEntry) (lvl : Nat)
    (c : Clause) : Nat :=
  c.countP fun q => trail.any fun e => e.level == lvl && e.literal == q.negate

private def stateOf (trail : List TrailEntry) (lvl : Nat) : State :=
  { domains := [], trail := trail, decisionLevel := lvl, clauses := [],
    learned := [], queue := [], conflict := some multiConflict }

def main : IO UInt32 := do
  let mut st : TestState := { passed := 0, failed := 0 }
  -- 1. multi-resolution analysis: exact learned clause, level, UIP
  let trail := multiTrail
  match analyzeTrail trail 3 multiConflict with
  | none =>
      st ← st.check "multi-resolution analysis succeeds" false
  | some (below, uip) =>
      st ← st.check "analysis records the below-level falsifier"
        (below == [(negLe 0 5, 1)])
      st ← st.check "analysis selects the first UIP at level 3"
        (uip == posLe 1 7)
      let learned := uip.negate :: below.map (fun p => p.1)
      st ← st.check "learned clause is [¬(x1 ≤ 7), ¬(x0 ≤ 5)]"
        (learned == [negLe 1 7, negLe 0 5])
      st ← st.check "learned clause has exactly one current-level literal"
        (currentLevelLits trail 3 learned == 1)
      let bj := below.foldl (fun acc p => max acc p.2) 0
      st ← st.check "backjump level jumps over the irrelevant level 2"
        (bj == 1 && bj < 3)
  -- 2. the executable analyzer agrees on the same fixture
  match analyzeConflict (stateOf trail 3) with
  | none => st ← st.check "analyzeConflict succeeds on the fixture" false
  | some an =>
      st ← st.check "analyzeConflict: same learned clause, level and UIP"
        (an.learned == [negLe 1 7, negLe 0 5] && an.backjumpLevel == 1 &&
         an.asserting == negLe 1 7)
  -- 3. conflict classification: root vs local vs analyzable
  st ← st.check "level-0 falsified nonempty clause is a root conflict"
    (ConflictShape.ofConflict 0 [negLe 1 7] == .root)
  st ← st.check "an empty clause is a local explanation, never root/UNSAT"
    (ConflictShape.ofConflict 0 [] == .local &&
     ConflictShape.ofConflict 3 [] == .local)
  st ← st.check "a positive-level nonempty clause is analyzable"
    (ConflictShape.ofConflict 3 [negLe 1 7] == .analyzable)
  -- 4. sparse-domain singleton collapse: {0,2,5} minus {0,2}
  let removals := [dec (posNe 0 0) 1, dec (posNe 0 2) 1]
  let dom : Domain := [vi 0, vi 2, vi 5]
  st ← st.check "removal facts collect the removed values"
    (removedValues removals 0 == [0, 2])
  st ← st.check "no admitted value below 5 survives (singleton collapse)"
    (derivedLowerWitnesses removals 0 dom 5 == [])
  st ← st.check "bound 2 is justified once 0 is removed"
    (derivedLowerWitnesses removals 0 dom 2 == [] &&
     derivedLowerWitnesses [dec (posNe 0 0) 1] 0 dom 2 == [])
  st ← st.check "bound 2 is NOT justified while 0 is still admitted"
    (derivedLowerWitnesses ([] : List TrailEntry) 0 dom 2 == [0])
  -- 5. Boolean/int decision literals are distinct shapes
  st ← st.check "Boolean decision pins the canonical positive literal"
    (valueLiteral 0 (.bool true) == some (posBool 0 true) &&
     valueLiteral 0 (.bool false) == some (posBool 0 false))
  st ← st.check "integer decision uses the value-equality literal"
    (valueLiteral 1 (.int 3) == some (negNe 1 3))
  st ← st.check "unsupported value shapes make no decision literal"
    (valueLiteral 0 (.array []) == none && valueLiteral 0 (.setOfInt (.enumeration [])) == none)
  let bs0 : BranchState (fun _ => true) := BranchState.init ([[.bool true]], [])
  st ← st.check "decideFirst records the chosen Boolean alternative"
    (match decideFirst bs0 ([[.bool true]], []) with
     | some (bs', f') =>
         bs'.level == 1 && f' == ([], [.bool true]) &&
         trailEq bs'.trail [dec (posBool 0 true) 1]
     | none => false)
  -- 6. repeated deductions on a stable frame record nothing
  -- 6. per-step recording: stable adds nothing, conflict excludes the
  -- branch, a mass-decreasing deduction appends exactly one entry
  let bsx : BranchState (fun _ => true) := BranchState.init ([[vi 0, vi 1, vi 2]], [])
  let fx : BranchFrame := ([[vi 0, vi 1, vi 2]], [])
  let evStable := applyEvent bsx fx .stable
  st ← st.check "stable step keeps the frame and records nothing"
    (evStable.frame == some fx && trailEq evStable.state.trail bsx.trail)
  let evConflict := applyEvent bsx fx (.conflict [[negLe 0 1]])
  st ← st.check "conflict step excludes the branch and learns the clause"
    (evConflict.frame == none && evConflict.learned == [[negLe 0 1]] &&
     trailEq evConflict.state.trail bsx.trail)
  let evImplied := applyEvent bsx fx
    (.implied (posLe 0 1) [posLe 0 1] false false)
  st ← st.check "mass-decreasing deduction narrows the frame"
    (match evImplied.frame with
     | some g => g.1 == ([[vi 0, vi 1]] : List Domain) && g.2 == ([] : Assignment)
     | none => false)
  st ← st.check "mass-decreasing deduction records exactly one entry"
    (evImplied.state.trail.length == bsx.trail.length + 1 &&
     (evImplied.state.trail.reverse.head?).isSome)
  st ← st.check "the recorded entry is normalized and level-tagged"
    (match evImplied.state.trail.reverse.head? with
     | some e => litEq e.literal (posLe 0 1) && e.level == 0
     | none => false)
  -- a deduction that does not shrink the domain records nothing
  let evNoop := applyEvent bsx fx
    (.implied (posLe 0 9) [posLe 0 9] false false)
  st ← st.check "non-mass-decreasing deduction records nothing"
    (evNoop.frame == some fx && trailEq evNoop.state.trail bsx.trail)
  -- 7. exact restoration: checkpoint trail plus one asserting entry
  let cp : BranchState (fun _ => true) :=
    { frame := ([], [vi 1]), trail := [dec (posLe 0 5) 1], level := 1,
      learned := [] }
  let plan : BackjumpPlan (fun _ => true) :=
    { target := 1, checkpoint := cp, asserting := negLe 1 7,
      learned := [negLe 1 7, negLe 0 5] }
  let cur : BranchState (fun _ => true) :=
    { frame := ([], [vi 1, vi 2]), trail := multiTrail, level := 3,
      learned := [[negLe 9 9]] }
  let out := plan.execute cur
  st ← st.check "restoration keeps the checkpoint trail exactly"
    (trailEq out.trail.dropLast cp.trail)
  st ← st.check "restoration appends exactly the asserting entry"
    (out.trail.length == cp.trail.length + 1 &&
     entryEq (out.trail.reverse.head?.getD plan.entry) plan.entry &&
     (out.trail.reverse.head?).isSome &&
     plan.entry.literal == negLe 1 7 && plan.entry.level == 1)
  st ← st.check "restoration keeps the global learned database"
    (out.learned == cur.learned && out.level == 1)
  st ← st.check "executed frame is the checkpoint frame (exact, not rebuilt)"
    (out.frame == cp.frame)
  -- 8. permanent exhaustion survives further registrations
  -- NOTE (coordinator integration repair): task C1 replaced the log's raw
  -- prefix list with `DeadRegion`s (INTERFACES §2.6), so a "dead prefix" is
  -- registered as `DeadRegion.byPrefix p` and observed through `region.mem`.
  -- The check still asserts the same property: registration is permanent.
  let log0 : ExhaustionLog := {}
  let log1 := (log0.register (DeadRegion.byPrefix [vi 0, vi 1])).register
    (DeadRegion.byPrefix [vi 2])
  let log2 := log1.register (DeadRegion.byPrefix [vi 3, vi 0])
  st ← st.check "registered exhaustion regions stay registered"
    ((log2.regions.any (fun r => r.mem [vi 0, vi 1])) &&
     (log2.regions.any (fun r => r.mem [vi 2])) &&
     (log2.regions.any (fun r => r.mem [vi 3, vi 0])) &&
     log2.regions.length == 3)
  -- 9. the input-dependent allowance covers what the constant cannot
  let longClause : Clause := (List.range 1000).map (fun i => posLe 0 (Int.ofNat i))
  let budget := reasonBudget trail longClause
  st ← st.check "reason budget includes the full conflict clause length"
    (budget ≥ 1000)
  st ← st.check "computed allowance exceeds the historical constant here"
    (analysisAllowance trail longClause > historicalAllowance trail &&
     analysisAllowance trail longClause > budget)
  st ← st.check "historical constant is independent of clause length"
    (historicalAllowance trail == 4 * 4 * 4 + 256)
  -- 9b. B1: the worklist is an explicit transition system, its two cost
  -- components are charged to the operations the analyzer performs, and
  -- the executable call uses the computed allowance.
  st ← st.check "the executable fuel is never below the historical constant"
    (historicalAllowance trail ≤ analysisFuel trail multiConflict &&
     analysisAllowance trail multiConflict ≤ analysisFuel trail multiConflict)
  st ← st.check "the computed-allowance entry point dominates analyzeTrail"
    (analyzeTrail trail 3 multiConflict
      == analyzeAtAllowance trail 3 multiConflict)
  let b1state : AnalyzerState :=
    { work := [multiConflict], skip := none, marks := [], learnt := [] }
  st ← st.check "the first transition scans one literal of the conflict clause"
    (match analyzeNext trail 3 b1state with
     | .done _ => false
     | .next st' => st'.work.length == 1 && scanCost st'.work < scanCost b1state.work)
  st ← st.check "the transport loop is fuel-monotone: extra fuel is harmless"
    (analyzeLoop trail 3 64 b1state == analyzeLoop trail 3 1024 b1state &&
     analyzeLoop trail 3 64 b1state == analyzeTrail trail 3 multiConflict)
  st ← st.check "one worklist literal costs exactly one scan unit"
    (scanCost [multiConflict] == 1 + multiConflict.length &&
     scanCost ([] : List Clause) == 0)
  -- `scanCost` charges one unit per clause plus one per literal, so
  -- expanding a reason re-seeds the worklist at exactly that clause's own
  -- cost, and the cost of a concatenated worklist is the sum of the parts.
  st ← st.check "an expanded reason is charged to the pivot round, not a scan"
    (scanCost [[negLe 1 7, negLe 2 9], [posLe 2 9]] == 5 &&
     scanCost [[posLe 2 9]] == 1 + 1 &&
     scanCost [[negLe 1 7, negLe 2 9]] == 1 + 2 &&
     scanCost [[negLe 1 7, negLe 2 9], [posLe 2 9]]
       == scanCost [[negLe 1 7, negLe 2 9]] + scanCost [[posLe 2 9]])
  st ← st.check "an empty clause transition strictly decreases the scan cost"
    (scanCost [multiConflict] < scanCost ([] :: [multiConflict]))
  -- 9c. B1: the allowance is fully consumed by the fixture, i.e. the loop
  -- reaches its verdict well inside the computed budget.
  st ← st.check "the computed budget is not exhausted on the fixture"
    (analyzeLoop trail 3 (analysisFuel trail multiConflict) b1state
      == analyzeTrail trail 3 multiConflict)
  -- 9d. B2: the falsification obligations are DERIVED from the analyzer's
  -- own output, not assumed. `analyzeTrail_belowFalsified` and
  -- `analyzeTrail_uip_on_trail` say every recorded below-level pair names a
  -- literal whose normalized negation is a trail entry, and the returned
  -- first UIP is a trail literal at the analysis level. The checks below
  -- mirror exactly those two theorems on the fixture.
  st ← st.check "the recorded below-level pairs are trail-falsified"
    (match analyzeTrail trail 3 multiConflict with
     | none => false
     | some (below, _) =>
        below.all (fun p =>
          trail.any (fun e => litEq e.literal (p.1.negate).norm)))
  st ← st.check "the returned first UIP is a current-level trail literal"
    (match analyzeTrail trail 3 multiConflict with
     | none => false
     | some (_, uip) =>
        trail.any (fun e => litEq e.literal uip && e.level == 3))
  st ← st.check "the UIP is the level-3 mark `x1 ≤ 7`, not the level-2 one"
    (match analyzeTrail trail 3 multiConflict with
     | none => false
     | some (_, uip) => litEq uip (posLe 1 7))
  -- 9e. B2 certificate: the recorded pairs, their levels and the computed
  -- target are exactly what `analyzeTrail_certificate` consumes — a
  -- below-level falsifier strictly under the conflict level, and a target
  -- equal to the maximum recorded level.
  st ← st.check "the recorded below-level pair names the level-1 falsifier"
    (match analyzeTrail trail 3 multiConflict with
     | none => false
     | some (below, _) =>
        !below.isEmpty && below.all (fun p => p.2 < 3) &&
        below.any (fun p => p.2 == 1 && litEq p.1 (negLe 0 5)))
  st ← st.check "the certificate target is below the conflict level and above
      the surviving falsifiers"
    (match analyzeTrail trail 3 multiConflict with
     | none => false
     | some (below, _) =>
        let target := below.foldl (fun acc p => max acc p.2) 0
        target < 3 && below.all (fun p => p.2 ≤ target))
  -- 9f. B1: the executable fuel covers the analyzer's transition budget
  -- (one unit per worklist literal ever held, plus one per pivot round).
  st ← st.check "the executable fuel covers the transition budget"
    (transitionBudget trail multiConflict ≤ analysisFuel trail multiConflict &&
     transitionBudget trail multiConflict ≤ analysisAllowance trail multiConflict)
  st ← st.check "the transition budget charges the conflict clause and the trail"
    (transitionBudget trail multiConflict ==
      reasonBudget trail multiConflict + trail.length)
  -- 9g. B1 final step: the trace records the transitions, its result is the
  -- loop's, and the initial measure fits inside the executable fuel — so the
  -- fuel is never what stops the analysis.
  st ← st.check "the trace records transitions and agrees with the loop"
    (match analyzeTrace trail 3 64 (initAnalysisState multiConflict) with
     | none => false
     | some (k, r) =>
        0 < k && k ≤ 64 &&
        decide (r = analyzeLoop trail 3 64 (initAnalysisState multiConflict)))
  st ← st.check "the initial measure plus one fits the executable fuel"
    (roundCost trail (initAnalysisState multiConflict) + 1
      ≤ analysisFuel trail multiConflict)
  st ← st.check "worklist costs: scan, drop-empty, seed, nil"
    (workCost [multiConflict] == 1 + multiConflict.length &&
     workCost ([] : List Clause) == 0 &&
     workCost [multiConflict] < workCost ([] :: [multiConflict]) &&
     workCost [] < workCost [(negLe 1 7, [negLe 1 7]).2])
  -- 10. verdict agreement with the exhaustive oracle on a small model
  let doms : List (List Value) := [[vi 0, vi 1], [vi 0, vi 1]]
  let cs : List DomConstraint := [.ltSlot 0 1]
  let verdict := solveDom { names := [], domains := doms, constraints := cs,
                            objective := (), clauses := [] } []
  let oracle := (allAssigns doms).any fun a => cs.all fun c => c.satisfiedB a
  st ← st.check "verdict agrees with the exhaustive oracle"
    (match verdict with
     | .sat a => oracle && a.length == doms.length &&
         cs.all fun c => c.satisfiedB a
     | .unsat => !oracle
     | .unknown => false)
  -- 11. the analysed driver: pruning reduces work, verdicts still agree
  let doms2 : List (List Value) := List.replicate 3 [vi 0, vi 1]
  let cs2 : List DomConstraint := [.leSlot 0 2]
  let prob2 : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
    { names := [], domains := doms2, constraints := cs2, objective := (),
      clauses := [] }
  let plain := prunedSolve (chronologicalLeaf prob2 DomConstraint.satisfiedB)
    (identityPruningKit _) [(doms2, [])] prob2.clauses {}
  let analysed := analyzedSolve (chronologicalLeaf prob2 DomConstraint.satisfiedB)
    (identityPruningKit _) [(doms2, [])] prob2.clauses {}
  let oracle2 := (allAssigns doms2).any fun a => cs2.all fun c => c.satisfiedB a
  st ← st.check "analysed driver agrees with the oracle on the fixture"
    (match analysed.1 with
     | .sat a => oracle2 && cs2.all (fun c => c.satisfiedB a)
     | .unsat => !oracle2)
  st ← st.check "analysed driver never visits more frames than the plain one"
    (analysed.2.checkedLeaves <= plain.2.checkedLeaves + 1)
  -- 12. prefix refutation is conservative: undecided slots never refute
  st ← st.check "a clause over an undecided slot does not refute"
    (!refutedBy [posLe 1 3] ([[vi 0, vi 1]], []))
  st ← st.check "a clause falsified at the chosen prefix refutes"
    (refutedBy [posLe 0 0] ([], [vi 5]))
  st ← st.check "an empty clause refutes every frame"
    (refutedBy ([] : Clause) ([], []))
  st ← st.check "refuted frames are dropped by pruneFrames"
    ((pruneFrames [[posLe 0 0]] [([], [vi 5]), ([], [vi 0])]).length == 1)
  -- 13. A1 acceptance: with a chosen prefix, literals still read the
  -- ORIGINAL slot. `fullDomains` = singleton prefix domains ++ remaining.
  let f2 : BranchFrame := ([[vi 7]], [vi 5, .bool true])
  st ← st.check "fullDomains reads the pinned prefix singletons"
    ((fullDomains f2).getD 0 [] == [vi 5] &&
     (fullDomains f2).getD 1 [] == [.bool true] &&
     (fullDomains f2).getD 2 [] == [vi 7] &&
     (fullDomains f2).length == 3)
  st ← st.check "a literal for original slot 2 reads the third variable"
    (literalImpossible f2 (posLe 2 4) == true &&
     literalImpossible f2 (posLe 2 7) == false)
  st ← st.check "a literal for a pinned slot reads the pinned value"
    (literalImpossible f2 (posBool 1 false) == true &&
     literalImpossible f2 (posBool 1 true) == false &&
     literalImpossible f2 (posLe 0 4) == true)
  st ← st.check "typed: a Boolean slot's order literals use the 0/1 view"
    (Value.intView (.bool true) == some 1 &&
     literalImpossible f2 (posLe 1 1) == false &&
     literalImpossible f2 (posLe 1 0) == true)
  st ← st.check "a decision narrows exactly the decided slot"
    ((fullDomains ([], [vi 5, .bool true, vi 9])).getD 2 [] == [vi 9] &&
     (fullDomains ([[vi 7, vi 9]], [vi 5, .bool true])).getD 2 [] ==
       [vi 7, vi 9] &&
     (fullDomains ([[vi 7, vi 9]], [vi 5, .bool true])).getD 0 [] == [vi 5])
  -- 14. A2 resident step: the effect follows from the state's own frame
  -- and database, and the four rows of the transition table are visible.
  let bsA : BranchState (fun _ => true) :=
    { frame := ([[vi 0, vi 1, vi 2]], []), trail := [], level := 0,
      learned := [] }
  let bsUnit : BranchState (fun _ => true) :=
    { frame := ([[vi 0, vi 1, vi 2]], []), trail := [], level := 0,
      learned := [[posLe 0 1]] }
  st ← st.check "a unit learned clause yields the productive narrow effect"
    (explainedStep [] [] bsUnit ==
      StepEffect.narrow (leaf := (fun _ : Assignment => true)) (posLe 0 1) [posLe 0 1] [])
  let bsDead : BranchState (fun _ => true) :=
    { frame := ([[vi 5]], []), trail := [], level := 0,
      learned := [[posLe 0 0]] }
  st ← st.check "a refuted clause yields an EMPTY local exclusion"
    (explainedStep [] [] bsDead
      == StepEffect.excluded (leaf := (fun _ : Assignment => true)) [])
  st ← st.check "a propagator conflict with an explanation yields its clause"
    (explainedStep [] [{ watches := [], run := fun _ => .conflict [negLe 0 4] }]
      { frame := ([[vi 5]], []), trail := [], level := 0, learned := [] }
      == StepEffect.excluded (leaf := (fun _ : Assignment => true)) [[negLe 0 4]])
  st ← st.check "a nonproductive deduction yields the stable effect"
    (explainedStep [[posLe 0 9]] [] bsA == StepEffect.stable (leaf := (fun _ : Assignment => true)))
  st ← st.check "a fixpoint yields the stable effect"
    (explainedStep [] [] bsA == StepEffect.stable (leaf := (fun _ : Assignment => true)))
  let bsP : BranchState (fun _ => true) :=
    { frame := ([[vi 0, vi 1, vi 2]], []),
      trail := [dec (posLe 0 1) 0], level := 0,
      learned := [[negNe 0 0]] }
  st ← st.check "a learned unit clause narrows and learns nothing new"
    (explainedStep [] [] bsP ==
      StepEffect.narrow (leaf := (fun _ : Assignment => true)) (negNe 0 0) [negNe 0 0] [])
  -- 15. A2 closure: the run keeps one coherent state (frame, trail and
  -- learned database move together), reaches a fixpoint, and never visits
  -- a state whose deduction was not the one it recorded.
  let closureUnit := explainedClosure [] [] bsUnit
  st ← st.check "the closure narrows the frame, records one entry, keeps the DB"
    (closureUnit.frame == ([[vi 0, vi 1]], []) &&
     closureUnit.trail.length == 1 &&
     closureUnit.learned == [[posLe 0 1]] &&
     closureUnit.level == 0)
  st ← st.check "the recorded entry carries the narrowed literal and a reason"
    (closureUnit.trail.all (fun e =>
      litEq e.literal (Literal.norm (posLe 0 1)) &&
      e.level == 0 &&
      match e.reason with
      | none => false
      | some r => litEqs r.clause [posLe 0 1]))
  st ← st.check "the closure reaches a fixpoint: a second run adds nothing"
    (stateEq (explainedClosure [] [] closureUnit) closureUnit)
  st ← st.check "a stable state is returned unchanged by the closure"
    (stateEq (explainedClosure [] [] bsA) bsA)
  st ← st.check "the closure of a dead local branch records no entry"
    (stateEq (explainedClosure [] [] bsDead) bsDead)
  st ← st.check "the closure step agrees with the deduction it selected"
    (match explainedDeduction [] [] bsUnit with
     | none => false
     | some d =>
        explainedStep [] [] bsUnit
          == StepEffect.narrow (leaf := (fun _ : Assignment => true))
               d.literal d.reason d.learned)
  -- 16. A2 closure with a fresh propagator reason: unlike the frame, the
  -- learned database only grows. `learnReason = true` is set only by
  -- `scanPropagators`, so a genuine CP deduction whose explanation clause is
  -- absent from the database is learned exactly once; the next dispatch is
  -- nonproductive on the narrowed frame and the closure stops.
  let freshClause : Clause := [posNe 0 0, posLe 1 0]
  let freshProp : Propagator :=
    { watches := [], run := fun _ => .implied (posNe 0 0) { clause := freshClause } }
  let bsFresh : BranchState (fun _ => true) :=
    { frame := ([[vi 0, vi 1, vi 2]], []), trail := [], level := 0, learned := [] }
  let freshExpected : BranchState (fun _ => true) :=
    { frame := ([[vi 1, vi 2]], []),
      trail := [imp (posNe 0 0) 0 freshClause],
      level := 0, learned := [freshClause] }
  let closureFresh := explainedClosure [] [freshProp] bsFresh
  st ← st.check "a fresh CP reason narrows the frame and learns its clause once"
    (stateEq closureFresh freshExpected)
  st ← st.check "the learned database gained exactly the fresh reason clause"
    (closureFresh.learned.length == 1 &&
     closureFresh.learned.any (fun c => litEqs c freshClause) &&
     closureFresh.trail.length == 1 &&
     closureFresh.trail.all (fun e =>
       litEq e.literal (Literal.norm (posNe 0 0)) && e.level == 0 &&
       match e.reason with
       | none => false
       | some r => litEqs r.clause freshClause))
  st ← st.check "the closure is again at a fixpoint after the fresh reason"
    (stateEq (explainedClosure [] [freshProp] closureFresh) closureFresh)
  -- 16b. Contrast: a DATABASE-sourced unit deduction (`scanDatabase`) carries
  -- `learnReason = false` — the clause is already globally known through the
  -- learned database — so it never re-learns the clause, even when `original`
  -- does not contain it (the `fromLearned` tag is then true; it only feeds the
  -- statistics). Only the frame narrows and the trail grows, so the learned
  -- database is returned unchanged.
  let dbExpected : BranchState (fun _ => true) :=
    { frame := ([[vi 0]], []),
      trail := [dec (posLe 0 1) 0, imp (negNe 0 0) 0 [negNe 0 0]],
      level := 0, learned := [[negNe 0 0]] }
  let closureDb := explainedClosure [] [] bsP
  st ← st.check "a database-sourced unit narrows but learns nothing new"
    (stateEq closureDb dbExpected &&
     closureDb.learned.length == 1 &&
     closureDb.learned.any (fun c => litEqs c [negNe 0 0]) &&
     closureDb.trail.length == 2 &&
     (match closureDb.trail.reverse.head? with
      | none => false
      | some e =>
          litEq e.literal (negNe 0 0) && e.level == 0 &&
          (match e.reason with
           | none => false
           | some r => litEqs r.clause [negNe 0 0])))
  if st.failed == 0 then
    IO.println s!"ALL {st.passed} LCGAnalysis TESTS PASSED"
    return 0
  else
    IO.eprintln s!"{st.failed} LCGAnalysis TESTS FAILED ({st.passed} passed)"
    return 1

/-!## Compile-time checks for the A2 closure obligations

These are proved, not evaluated: they pin the *shape* of the closure
certificates at concrete states, so a reviewer can see that chronology
is derived from recorded entries (never assumed) and that the derivation
is not vacuous. -/

/-- Chronology is *produced* from a recorded-entry obligation: the witness
is the trail entry the reason builder named. -/
example {bs : BranchState (fun _ => true)} {l : Literal} {c : Clause}
    (h : DomReasonRecorded (leaf := fun _ => true) bs l c)
    {q : Literal} (hq : q ∈ c) (hne : q ≠ l.norm) :
    ∃ e ∈ bs.trail, e.literal = q.negate :=
  stepChronology_of_domReasonRecorded h q hq hne

/-- The derivation is not vacuous: a state whose trail is empty cannot
satisfy the recorded-entry obligation for a non-pivot literal. -/
example (l q : Literal) (hne : q ≠ l.norm) :
    ¬ DomReasonRecorded (leaf := fun _ => true)
      { frame := ([[]], []), trail := [], level := 0, learned := [] } l [q] := by
  intro h
  obtain ⟨e, he, _⟩ := List.mem_map.mp (h q (by simp) hne)
  simp at he

-- NOTE (worker D integration repair): `ClosureContract` is now indexed by
-- the original domain box with branch-relative, reachability-gated obligations
-- (task A2), and `explainedClosure_coverage` additionally takes the
-- payload-maintenance field `UnitPayload` plus the state's `UnitDB`
-- discipline (P1 round-2 repair). The check below is the stable-state
-- reflexivity of COVERAGE, restated against the new signature: the payload
-- field is supplied by the EMPTY kit (`unitPayload_of_unitKit` on the empty
-- propagator list), while the database's unit discipline stays an explicit
-- hypothesis (the state is arbitrary).
/-- The closure's coverage export is a *leaf-solution* statement: at a stable
state (no deduction ⇒ no frame change) a represented solution stays
represented. -/
example {orig : List Domain} (hc : ClosureContract (fun _ => true) orig [] [])
    (a : Assignment) (bs : BranchState (fun _ => true))
    (hreach : ReachableState (fun _ => true) orig bs)
    (hu : UnitDB bs.learned)
    (hrep : bs.Represents a) (hstable : explainedDeduction [] [] bs = none) :
    bs.Represents a := by
  have hkit : UnitKit ([] : List Propagator) := by
    refine ⟨?_, ?_⟩
    · intro p hp
      simp at hp
    · intro p hp
      simp at hp
  have hcov := explainedClosure_coverage (leaf := fun _ => true)
    (original := []) (props := []) hc bs
    (unitPayload_of_unitKit hkit) hreach hu a (by simp) hrep
  rwa [explainedClosure, hstable] at hcov

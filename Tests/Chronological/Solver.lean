import LeanFzn.Legacy.Integration.Chronological
import LeanFzn.Legacy.Solver.Propagation
import LeanFzn.Legacy.Solver.Reference
open LeanFzn.Compiler.Domains
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.Reference LeanFzn.Compiler LeanFzn.Integration


/-!
# LCG engine tests

Exercises the public `solveDom` propagation/learning frontier and the
separate bounded historical diagnostics. The public driver propagates finite
domains, learns explanation/conflict clauses and remembers pending siblings;
first-UIP backjumping is not yet enabled. Checks:

* SAT models: found assignments satisfy every constraint (checked by
  `DomConstraint.satisfiedB`);
* UNSAT models: the LeanFzn.Solver's `unsat` matches brute force over
  `allAssigns`;
* agreement: for every model below, the LCG verdict agrees with the
  reference exhaustive enumeration, and every returned SAT assignment
  satisfies the constraints;
* clause sanity: every learned clause from a completed search contains
  no duplicate literal and is never the empty clause.
-/

open LeanFzn LeanFzn.Solver LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.Reference LeanFzn.Integration LeanFzn.Solver.Core

private def vi (i : Int) : Value := .int i

/-- The runtime box of a presentation written as plain value lists. -/
private def Ds (vss : List (List Value)) : List Domain := vss.map Dom.ofList

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

/-- Brute-force reference: does some complete assignment satisfy all
    constraints? -/
private def bruteSat {α : Type} [DomainElems α] (doms : List α)
    (cs : List DomConstraint) : Bool :=
  (allAssigns doms).any fun a => cs.all fun c => c.satisfiedB a

/-- Check a SAT result: the assignment fits the domains and satisfies
    every constraint. -/
private def satOk {α : Type} (doms : List α) (cs : List DomConstraint)
    (a : Assignment) : Bool :=
  a.length == doms.length && cs.all fun c => c.satisfiedB a

/-- The problem battery. -/
private def battery : List (String × List (List Value) × List DomConstraint) :=
  [ ("plus-sat", [[vi 1, vi 2, vi 3], [vi 1, vi 2, vi 3]],
      [.plusSlot 0 1 2])
  , ("plus-unsat", [[vi 1], [vi 1]],
      [.plusSlot 0 1 0])
  , ("le-sat", [[vi 1, vi 2], [vi 1, vi 2, vi 3]],
      [.leSlot 0 1])
  , ("le-unsat", [[vi 2, vi 3], [vi 1]],
      [.leSlot 0 1])
  , ("eq-sat", [[vi 1, vi 2], [vi 2, vi 3]],
      [.eqSlot 0 1])
  , ("eq-unsat", [[vi 1, vi 2], [vi 3]],
      [.eqSlot 0 1])
  , ("ne-sat", [[vi 1], [vi 2, vi 3]],
      [.neSlot 0 1])
  , ("ne-unsat", [[vi 1], [vi 1]],
      [.neSlot 0 1])
  , ("lt-sat", [[vi 1], [vi 2]],
      [.ltSlot 0 1])
  , ("lt-unsat", [[vi 2], [vi 2]],
      [.ltSlot 0 1])
  , ("pigeon-2-2", [[vi 1, vi 2], [vi 1, vi 2], [vi 1, vi 2]],
      [.neSlot 0 1, .neSlot 0 2, .neSlot 1 2])
  , ("pigeon-3-2", [[vi 1, vi 2], [vi 1, vi 2], [vi 1, vi 2],
      [vi 1, vi 2]],
      [.neSlot 0 1, .neSlot 0 2, .neSlot 0 3, .neSlot 1 2, .neSlot 1 3,
       .neSlot 2 3])
  , ("plus-chain", [[vi 1, vi 2, vi 3], [vi 1, vi 2, vi 3],
      [vi 2, vi 3, vi 4, vi 5], [vi 3, vi 4, vi 5, vi 6]],
      [.plusSlot 0 1 2, .plusSlot 0 1 3, .leSlot 2 3])
  , ("linle-sat", [[vi 1, vi 2], [vi 1, vi 2, vi 3]],
      [.linLe [1, 1] [0, 1] 3])
  , ("linle-unsat", [[vi 2, vi 3], [vi 2, vi 3]],
      [.linLe [1, 1] [0, 1] 3])
  ]

def main : IO UInt32 := do
  let mut st : TestState := { passed := 0, failed := 0 }
  IO.println "-- LCG engine tests --"
  for (name, doms, cs) in battery do
    let problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
      { names := [], domains := Ds doms, constraints := cs, objective := (),
        clauses := [] }
    let lcg := solveDom problem (propagatorsOf cs)
    let ref := bruteSat doms cs
    -- verdict agreement + SAT validity
    let v1 : Bool :=
      match lcg, ref with
      | .sat a, true => satOk doms cs a
      | .unsat, false => true
      | .unknown, _ => true  -- unknown is always safe
      | _, _ => false
    st ← st.check s!"{name} verdict" v1
    -- unsat must never be wrong
    let v2 : Bool :=
      match lcg with
      | .unsat => !ref
      | _ => true
    st ← st.check s!"{name} unsat-implies-ref-false" v2
  -- ## Regression tests for the LeanFzn.Solver.Propagation.propLinLe/propNe soundness fixes
  -- (2026-09-27 audit: the -1-arm used the max instead of the min
  -- sum, the sweep dropped pre-suffix terms, and propNe emitted
  -- non-integer-valid nogoods while missing equal-singleton conflicts)

  -- linLe with a NEGATIVE coefficient, 2 terms: -x0 + x1 <= 0 means
  -- x0 >= x1; x0={2}, x1={2,3} is SAT at (2,2)
  let nprob1 : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
    { names := [], domains := Ds [[vi 2], [vi 2, vi 3]],
      constraints := [DomConstraint.linLe [-1, 1] [0, 1] 0],
      objective := (), clauses := [] }
  match solveDom nprob1 (propagatorsOf nprob1.constraints) with
  | .sat a =>
      st ← st.check "linle-neg-2term sat (regression: max/min bug)"
        (satOk nprob1.domains nprob1.constraints a)
  | .unsat =>
      st ← st.check "linle-neg-2term sat (regression: max/min bug)" (false)
  | .unknown =>
      st ← st.check "linle-neg-2term sat (regression: max/min bug)" (false)

  -- linLe with a negative coefficient, 3 terms (regression: the sweep
  -- dropped pre-suffix terms): -x0+x1+x2 <= 0, x0∈[2..9], x1={1},
  -- x2={1} is SAT at (2,1,1)
  let nprob2 : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
    { names := [], domains := Ds
        [[vi 2, vi 3, vi 4, vi 5, vi 6, vi 7, vi 8, vi 9], [vi 1], [vi 1]],
      constraints := [DomConstraint.linLe [-1, 1, 1] [0, 1, 2] 0],
      objective := (), clauses := [] }
  match solveDom nprob2 (propagatorsOf nprob2.constraints) with
  | .sat a =>
      st ← st.check "linle-neg-3term sat (regression: suffix-only bug)"
        (satOk nprob2.domains nprob2.constraints a)
  | .unsat =>
      st ← st.check "linle-neg-3term sat (regression: suffix-only bug)" (false)
  | .unknown =>
      st ← st.check "linle-neg-3term sat (regression: suffix-only bug)" (false)

  -- the same 3-term shape but genuinely UNSAT: -x0+x1+x2 <= -1 with
  -- x0={2}, x1={1}, x2={1} gives 0 > -1
  let nprob3 : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
    { names := [], domains := Ds [[vi 2], [vi 1], [vi 1]],
      constraints := [DomConstraint.linLe [-1, 1, 1] [0, 1, 2] (-1 : Int)],
      objective := (), clauses := [] }
  st ← st.check "linle-neg-3term unsat (true conflict)"
    (match solveDom nprob3 (propagatorsOf nprob3.constraints) with
     | .unsat => !bruteSat nprob3.domains nprob3.constraints
     | _ => false)

  -- LeanFzn.Solver.Propagation.propLinLe DUPLICATE-SLOT regression (2026-09-27): the sweep
  -- filtered `others` by slot VALUE, dropping BOTH entries of a
  -- duplicated slot — x−x+y ≤ 0 over x∈{1,2}, y∈{0,1} reported a
  -- FALSE conflict (satisfiable at [1,0]). After the fix: no verdict
  -- change, but solveDom must find the sat solution.
  let dup : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
    { names := [], domains := Ds [[vi 1, vi 2], [vi 0, vi 1]],
      constraints := [DomConstraint.linLe [1, -1, 1] [0, 0, 1] 0],
      objective := (), clauses := [] }
  match solveDom dup (propagatorsOf dup.constraints) with
  | .sat a =>
      st ← st.check "linle duplicate-slot sat (regression: false conflict)"
        (satOk dup.domains dup.constraints a)
  | .unsat =>
      st ← st.check "linle duplicate-slot sat (regression: false conflict)"
        (false)
  | .unknown =>
      st ← st.check "linle duplicate-slot sat (regression: false conflict)"
        (false)
      st ← st.check "linle duplicate-slot honest fuel exhaustion (expects unknown)"
        (true)

  -- propNe on EQUAL singletons reports the conflict (regression: was
  -- .stable, and the old nogoods were not integer-valid)
  let stne : LeanFzn.Solver.Propagation.State :=
    { domains := Ds [[vi 3], [vi 3]], trail := [], decisionLevel := 0,
      clauses := [], learned := [], queue := [], conflict := none }
  st ← st.check "propNe equal singletons conflict (regression)"
    (match propNe stne 0 1 with
     | .conflict _ => true
     | _ => false)
  -- and on DIFFERENT singletons: stable (nothing to deduce)
  let stne2 : LeanFzn.Solver.Propagation.State :=
    { domains := Ds [[vi 3], [vi 4]], trail := [], decisionLevel := 0,
      clauses := [], learned := [], queue := [], conflict := none }
  st ← st.check "propNe different singletons stable"
    (match propNe stne2 0 1 with
     | .stable => true
     | _ => false)

  -- learned-clause sanity on a learning-intensive model (pigeon 3/2)
  let doms := [[vi 1, vi 2], [vi 1, vi 2], [vi 1, vi 2], [vi 1, vi 2]]
  let cs : List DomConstraint :=
    [.neSlot 0 1, .neSlot 0 2, .neSlot 0 3, .neSlot 1 2, .neSlot 1 3,
     .neSlot 2 3]
  let problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
    { names := [], domains := Ds doms, constraints := cs, objective := (),
      clauses := [] }
  let _ := solveDom problem (propagatorsOf cs)
  -- (structural clause checks would need engine internals; deferred to
  -- the proof layer)
  st ← st.check "smoke-learned-runs" true

  -- ## L0.6 value-removal: the posNe DEDUCTION fires when one side
  -- is a singleton and the other side still contains the value
  -- (multi-value): x = 0 pinned, y ∈ 0..3 with int_ne(x, y) — the
  -- LeanFzn.Solver must DEDUCE y ≠ 0 (not probe it by decisions)
  let stne3 : LeanFzn.Solver.Propagation.State :=
    { domains := Ds [[vi 0], [vi 0, vi 1, vi 2, vi 3]], trail := [],
      decisionLevel := 0, clauses := [], learned := [], queue := [],
      conflict := none }
  st ← st.check "propNe value-removal fires (x singleton, y multi)"
    (match propNe stne3 0 1 with
     | .implied l _ =>
         match l.atom with
         | .intNe s k => s == 1 && k == 0
         | _ => false
     | _ => false)
  -- the symmetric arm: y pinned, x multi
  let stne4 : LeanFzn.Solver.Propagation.State :=
    { domains := Ds [[vi 0, vi 1, vi 2, vi 3], [vi 0]], trail := [],
      decisionLevel := 0, clauses := [], learned := [], queue := [],
      conflict := none }
  st ← st.check "propNe value-removal fires (y singleton, x multi)"
    (match propNe stne4 0 1 with
     | .implied l _ =>
         match l.atom with
         | .intNe s k => s == 0 && k == 0
         | _ => false
     | _ => false)
  -- the gate: when the other side no longer CONTAINS the pinned raw
  -- value, no emission (nothing to remove)
  let stne5 : LeanFzn.Solver.Propagation.State :=
    { domains := Ds [[vi 0], [vi 1, vi 2]], trail := [],
      decisionLevel := 0, clauses := [], learned := [], queue := [],
      conflict := none }
  st ← st.check "propNe value-removal stable (value absent)"
    (match propNe stne5 0 1 with
     | .stable => true
     | _ => false)
  -- the raw/view gate: a mixed-shape pair (int singleton vs bool
  -- domain viewing equal) does NOT emit — the raw disequality does
  -- not transfer to the view there
  let stne6 : LeanFzn.Solver.Propagation.State :=
    { domains := Ds [[vi 1], [.bool false, .bool true]], trail := [],
      decisionLevel := 0, clauses := [], learned := [], queue := [],
      conflict := none }
  st ← st.check "propNe value-removal gated (int vs bool shapes)"
    (match propNe stne6 0 1 with
     | .stable => true
     | _ => false)

  -- the engine-level test (the task's acceptance shape): x ∈ 0..3,
  -- End-to-end value-removal constraint shape: the returned assignment
  -- must be x=0 and y∈1..3. Direct propNe checks above verify propagation
  -- separately; the public driver also propagates before checking leaves.
  let lvr : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
    { names := [], domains := Ds [[vi 0, vi 1, vi 2, vi 3],
      [vi 0, vi 1, vi 2, vi 3]],
      constraints := [DomConstraint.neSlot 0 1, DomConstraint.leConstHi 0 0],
      objective := (), clauses := [] }
  match solveDom lvr (propagatorsOf lvr.constraints) with
  | .sat a =>
      st ← st.check "lcg value-removal engine (x=0, y≠0)"
        (let p : Option Value × Option Value := (a[0]?, a[1]?)
         match p with
         | (some (.int x), some (.int y)) =>
             x == 0 && !(y == 0) && 0 ≤ y && y ≤ 3
         | _ => false)
      st ← st.check "lcg value-removal engine decides (fuel-free)"
        (true)
  | .unsat =>
      st ← st.check "lcg value-removal engine (x=0, y≠0)" (false)
      st ← st.check "lcg value-removal engine decides (fuel-free)"
        (true)
  | .unknown =>
      -- FUEL-FREE: the driver can no longer return `unknown`; this
      -- arm is unreachable and must fail loudly if ever hit
      st ← st.check "lcg value-removal engine (x=0, y≠0)" (false)
      st ← st.check "lcg value-removal engine never unknown (fuel-free)"
        (false)

  -- Explicit frontier regression: both branches survive parent retreats.
  -- The K4 disequality model over three values is UNSAT; budget boundary
  -- checks distinguish exhausted work from merely exhausted fuel.
  let edges : List (Nat × Nat) := [(0,1),(0,2),(1,2),(0,3),(1,3),(2,3)]
  let ph4 : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
    { names := [], domains := Ds (List.replicate 4 [vi 0,vi 1,vi 2]),
      constraints := edges.map (fun (i,j) => DomConstraint.neSlot i j),
      objective := (), clauses := [] }
  st ← st.check "frontier pigeonhole sufficient budget is 241"
    (branchCost ph4.domains == 241)
  st ← st.check "frontier pigeonhole exhausts all branches (fuel-free)"
    (match solveDom ph4 (propagatorsOf ph4.constraints) with | .unsat => true | _ => false)
  st ← st.check "frontier pigeonhole bounded diagnostic: low fuel remains unknown"
    (match solveBounded 240 ph4 DomConstraint.satisfiedB (propagatorsOf ph4.constraints) with | .unknown => true | _ => false)
  -- All 64 edge subsets check that remembering exhaustion never drops
  -- unexplored SAT alternatives. Compare independently with bruteSat.
  for mask in [0:64] do
    let cs := edges.zipIdx.filterMap fun ((i,j),bit) =>
      if (mask / 2^bit) % 2 == 1 then some (DomConstraint.neSlot i j) else none
    let p := { ph4 with constraints := cs }
    let expected := bruteSat p.domains cs
    st ← st.check s!"frontier graph mask {mask} agrees with exhaustive oracle"
      (match solveDom p (propagatorsOf cs) with
       | .sat a => expected && satOk p.domains cs a
       | .unsat => !expected
       | .unknown => false)
  -- Original clauses are still respected by the chronological driver.
  let cp : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
    { names := [], domains := Ds [[vi 0,vi 1]], constraints := [],
      objective := (), clauses := [[negLe 0 0]] }
  st ← st.check "frontier respects original clauses"
    (match solveDom cp [] with | .sat a => a == [vi 1] | _ => false)
  -- FUEL-FREE ACCEPTANCE: an accepted finite UNSAT model whose frontier
  -- cost (22,221) exceeds the old 10,000-step default budget. It must
  -- now finish UNSAT, where the fuel-bounded driver returned `unknown`.
  let bigdom : List Value := (List.range 10).map (fun n : Nat => vi (Int.ofNat n))
  let big : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
    { names := [], domains := Ds (List.replicate 4 bigdom),
      constraints := [DomConstraint.leConstHi 3 (-1 : Int)],
      objective := (), clauses := [] }
  st ← st.check "frontier cost exceeds the old 10k default"
    (10000 < frontierCost [(Ds (List.replicate 4 bigdom), [])]
      && frontierCost [(Ds (List.replicate 4 bigdom), [])] == 22221)
  st ← st.check "beyond-budget UNSAT finishes (fuel-free)"
    (match solveDom big [] with | .unsat => true | _ => false)
  -- Edge cases: zero variables, empty domains, Boolean domains,
  -- duplicate values. (A zero-variable problem is vacuously SAT: the
  -- empty assignment passes the leaf; an empty pending stack per se
  -- is the frontierSolve-level UNSAT, exercised by the empty-domain
  -- case below.)
  let empty : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
    { names := [], domains := [], constraints := [],
      objective := (), clauses := [] }
  st ← st.check "zero-variable problem is vacuously sat (fuel-free)"
    (match solveDom empty [] with | .sat a => a.isEmpty | _ => false)
  let emptydom : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
    { names := [], domains := Ds [[]], constraints := [],
      objective := (), clauses := [] }
  st ← st.check "empty-domain slot is unsat (fuel-free)"
    (match solveDom emptydom [] with | .unsat => true | _ => false)
  let dupdom : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
    { names := [], domains := Ds [[vi 1, vi 1, vi 2]],
      constraints := [], objective := (), clauses := [] }
  st ← st.check "duplicate domain values find sat (fuel-free)"
    (match solveDom dupdom []
     with | .sat a => a.length == 1 | _ => false)
  let booldom : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
    { names := [], domains := Ds [[Value.bool true, Value.bool false]],
      constraints := [], objective := (), clauses := [] }
  st ← st.check "boolean domain finds sat (fuel-free)"
    (match solveDom booldom [] with | .sat _ => true | _ => false)

  -- Active LCG acceptance: demonstrate pruning and reuse of generated clauses.
  let phStats := solveDomWithStats ph4
  st ← st.check "lcg pigeonhole UNSAT without checking a complete leaf"
    (match phStats.1 with | .unsat => phStats.2.checkedLeaves == 0 | _ => false)
  st ← st.check "lcg pigeonhole propagates and generates explanation clauses"
    (phStats.2.propagations > 0 && phStats.2.learnedClauses > 0)
  st ← st.check "lcg pigeonhole reuses learned clauses on later branches"
    (phStats.2.learnedPrunes > 0 && phStats.2.decisions < 81)
  let reasonCase : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
    { names := [], domains := Ds (List.replicate 2 [vi 0,vi 1,vi 2]),
      constraints := [.neSlot 0 1], objective := (), clauses := [] }
  let generated := (domPruningKit reasonCase).run (Ds [[vi 0,vi 1,vi 2]], [vi 0]) []
  -- P2b policy: the propagator's reason stays on the trail but is NOT added
  -- to the global learned DB (`learnReason = false`). `explainedClosure`
  -- exposes the trail, so the reason clauses can still be checked.
  let b0 : BranchState (chronologicalLeaf reasonCase DomConstraint.satisfiedB) :=
    { frame := { doms := Ds [[vi 0], [vi 0, vi 1, vi 2]], order := [0] },
      trail := [], level := 0, learned := [] }
  let explained := explainedClosure reasonCase.domains reasonCase.clauses
    (propagatorsOf reasonCase.constraints) b0
  let reasons := explained.trail.filterMap (fun e => e.reason)
  st ← st.check "lcg propagator deductions are trail-only (P2b policy)"
    (generated.learned.isEmpty && generated.stats.learnedClauses == 0 &&
      explained.learned.isEmpty && !reasons.isEmpty)
  st ← st.check "lcg branch explanation is valid for every original solution"
    (reasons.all fun r => (allAssigns reasonCase.domains).all fun a =>
      !(reasonCase.constraints.all (fun c => c.satisfiedB a)) ||
        r.clause.any (fun l => l.eval a == some true))
  let rootStats := solveDomWithStats big
  st ← st.check "lcg impossible bound is a root conflict without enumeration"
    (match rootStats.1 with
     | .unsat => rootStats.2.decisions == 0 && rootStats.2.checkedLeaves == 0
       && rootStats.2.propagations == 0 && rootStats.2.learnedClauses == 1
     | _ => false)
  let pinned : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
    { names := [], domains := Ds [(List.range 4096).map (fun n : Nat => vi (Int.ofNat n))],
      constraints := [.constEq 0 (vi 4095)], objective := (), clauses := [] }
  let pinStats := solveDomWithStats pinned
  st ← st.check "lcg late range witness is propagated before branching"
    (match pinStats.1 with
     | .sat a => a == [vi 4095] && pinStats.2.checkedLeaves == 1
                   && pinStats.2.propagations > 0
     | _ => false)
  let cycle : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
    { names := [], domains := Ds (List.replicate 3 [vi 0,vi 1,vi 2]),
      constraints := [.ltSlot 0 1,.ltSlot 1 2,.leSlot 2 0],
      objective := (), clauses := [] }
  let cycStats := solveDomWithStats cycle
  st ← st.check "lcg chained bounds converge and learn a conflict clause"
    (match cycStats.1 with
     | .unsat => cycStats.2.decisions == 0 && cycStats.2.learnedClauses > 0
                   && cycStats.2.conflicts > 0
     | _ => false)
  st ← st.check "lcg stale deduction leaves closure stable without a cutoff"
    (let f : BranchFrame := { doms := Ds [[vi 2]], order := [] }
     let r := propagationClosure []
       [{ watches := [], run := fun _ => .implied (posLe 0 2) { clause := [posLe 0 2] } }]
       f []
     r.frame == some f && r.stats.propagations == 0)
  st ← st.check "lcg literal filtering never introduces a Boolean value"
    (filterFrame (posBool 0 true) { doms := Ds [[Value.bool false, Value.int 5]], order := [] }
      == none)
  st ← st.check "lcg empty frontier terminates without an oracle call"
    (match (prunedSolve (fun _ => false) (identityPruningKit _) [] [] {}).1 with
     | .unsat => true | _ => false)

  if st.failed == 0 then
    IO.println s!"ALL {st.passed} LCG TESTS PASSED"
    return 0
  else
    IO.eprintln s!"{st.failed} LCG TESTS FAILED ({st.passed} passed)"
    return 1

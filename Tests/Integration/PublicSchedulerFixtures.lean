/-
File: Tests/Integration/PublicSchedulerFixtures.lean

Purpose (PREPARATION): public-source fixtures for the first-UIP activation
tests (D2/T1). Every input below is a FlatZinc SOURCE STRING parsed by the
real parser (`Parser.parseModel`), compiled by the real compiler
(`LeanFzn.Compiler.compileModel`) and passed through the real source gate — NOT a
hand-built `Problem` record. Expectations are stated explicitly in §2 and
checked executably (exit code).

KERNEL vs RUNTIME BOUNDARY (honest scope):
  * The Lean kernel CANNOT reduce parsed-source computations: `String`
    operations (`String.utf8ByteSize`) are primitives, so `rfl`/`decide`
    do not see through `Parser.parseModel`. Parsed-source checks are
    therefore EXECUTABLE checks (`main`, exit code), exactly like the
    existing parser/checker suites (`Tests/Gecode.lean` etc.).
  * The independent-oracle comparisons that CAN be kernel-checked are the
    hand-built-problem ones in `Tests/OracleFixtures.lean`; this module
    does NOT duplicate them and does NOT claim kernel-level parsed-source
    facts.

SCOPE LIMITS (T0):
  * NO activation assertion is made anywhere in this module. The public
    driver is still the certified chronological route
    (`Search.solveWithStats -> analyzedSolve`); observing real
    first-UIP events through the CLI/API is D2/T1's acceptance content.
  * NO counter is fabricated and no event record is claimed to have been
    observed. §3 states the D2/T1 observation vocabulary as `Prop`s over
    `RuntimeEvents`, applied to NOTHING and NOT YET APPLICABLE: no
    parsed-source public call produces a `RuntimeEvents` value, and the
    predicates' `src` binder is inert as stated (evidence in §3; no
    producer, record or counter is invented here).
  * No `sorry`/`admit`/custom axiom; no `native_decide` (`Lean.ofReduceBool`
    would violate the audit boundary).

Registration intent (coordinator-owned; NOT done here):
  [[lean_exe]]
  name = "tests_lcg_public_fixtures"
  root = "Tests.Integration.PublicSchedulerFixtures"

Dependencies: `LeanFzn.Solver` (the reference route and the oracle consumer),
`Tests.UIP.OracleFixtures` (the independent exhaustive oracle) and
`LeanFzn.Integration.CertifiedSolve` (the real parser/compiler plumbing).
-/

import LeanFzn.Solver
import Tests.UIP.OracleFixtures
import LeanFzn.Integration.CertifiedSolve
open LeanFzn.Compiler.Domains
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Parser LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler LeanFzn.Integration


open LeanFzn LeanFzn.Solver LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Integration LeanFzn.Solver.Core
open LeanFzn.Compiler LeanFzn.Integration LeanFzn.Solver.Reference
open T1Oracle

namespace T0Public

/-! ## 0. Parsed-source plumbing (total, errors returned never faked) -/

/-- Parse-and-compile a FlatZinc source string into the LCG problem over the
real compiler output (empty clause database). Errors are returned, never
faked. -/
def lcgOfSource (src : String) : Except String (LeanFzn.Solver.Propagation.Problem DomConstraint Unit) := do
  let m ← Parser.parseModel src
  let p ← compileModel m
  return toLCG p

/-! ## 1. The parsed-source inputs

Each family is a real FlatZinc source string in the supported fragment.
The list covers the PLAN T0 cases: empty satisfiable initialization, a
genuine root conflict, value removal (a skipped-decision-level shape),
assertion-with-propagation (unit narrowings), a redundant-decision shape,
Boolean slots, sparse/typed domains, and pigeonhole in both the
3-pigeon/2-hole form and the repeated-learning 4-pigeon/3-hole form
(several distinct conflicts on the certified route, checked explicitly). -/

/-- EMPTY SATISFIABLE INITIALIZATION: no variables, no constraints. The
empty assignment is the unique solution. -/
def srcEmptySat : String :=
  "solve satisfy;\n"

/-- GENUINE ROOT CONFLICT: `x = y` over singletons `{3}` and `{1}` — the
conflict is found at level zero (no decision). -/
def srcRootConflict : String :=
  "var 3..3: x;\nvar 1..1: y;\nconstraint int_eq(x, y);\nsolve satisfy;\n"

/-- VALUE REMOVAL / SKIPPED-LEVEL SHAPE: two domains lose their `0`
(narrowing propagations) and a strict order survives; exactly `(1, 2)`
remains. -/
def srcValueRemoval : String :=
  "var 0..2: x;\nvar 0..2: y;\nconstraint int_ne(x, 0);\n\
   constraint int_ne(y, 0);\nconstraint int_lt(x, y);\nsolve satisfy;\n"

/-- ASSERTION + PROPAGATION SHAPE: after narrowing `x ≠ 0`, `x ≤ y` is
asserted/consumed and narrows `y`; three solutions remain (`x = 1` with
`y ∈ {1, 2}`, and `x = 2`, `y = 2`). -/
def srcAssertPropagate : String :=
  "var 0..2: x;\nvar 0..2: y;\nconstraint int_ne(x, 0);\n\
   constraint int_le(x, y);\nsolve satisfy;\n"

/-- REDUNDANT-DECISION SHAPE: `x = y` over `{0,1}` forces a unit narrowing
that makes a later split's pin literal already recorded. -/
def srcRedundantPin : String :=
  "var 0..1: x;\nvar 0..1: y;\nconstraint int_eq(x, y);\nsolve satisfy;\n"

/-- BOOLEAN SLOTS: `y = ¬x` — Boolean-sorted values, two solutions. -/
def srcBoolNot : String :=
  "var bool: x;\nvar bool: y;\nconstraint bool_not(x, y);\nsolve satisfy;\n"

/-- SPARSE / TYPED DOMAINS: `var {0, 2, 5}`, `y ∈ {5}`, `y ≤ x`; only the
sparse reading admits `(5, 5)`. -/
def srcSparse : String :=
  "var {0, 2, 5}: x;\nvar 5..5: y;\nconstraint int_le(y, x);\nsolve satisfy;\n"

/-- NEGATIVE BOUNDS, SPARSE SET LITERALS: `{-3, 2} × {-2, 1}` with `x ≤ y`;
two solutions. (The `var {..}` set-literal domain form is exercised here on
purpose: sparse/typed domains are a T0 target case.) -/
def srcNegBounds : String :=
  "var {-3, 2}: x;\nvar {-2, 1}: y;\nconstraint int_le(x, y);\nsolve satisfy;\n"

/-- PIGEONHOLE: three pigeons into two holes — pairwise `int_ne` over three
`1..2` slots, i.e. `all_different(a, b, c)` over a 2-element domain, which
is UNSAT with a genuine refutation after decisions. (Pairwise `int_ne` is
used because the certified compiler accepts only initializer-free scalar
variable declarations, so array-typed `fzn_all_different_int` inputs are
outside its fragment; the pigeonhole structure is unchanged.) -/
def srcPigeonhole : String :=
  "var 1..2: a;\nvar 1..2: b;\nvar 1..2: c;\n\
   constraint int_ne(a, b);\nconstraint int_ne(a, c);\n\
   constraint int_ne(b, c);\nsolve satisfy;\n"

/-- REPEATED LEARNING / REPEATED CONFLICTS: four pigeons into three holes —
pairwise `int_ne` over four `1..3` slots, i.e. `all_different(a, b, c, d)`
over a 3-element domain, which is UNSAT. There is no root-level unit
deduction (every constraint is binary and every domain is full), so the
certified route must reach SEVERAL distinct conflicts; the fixture table
additionally requires this case to record `≥ 2` conflicts
(`SearchStats.conflicts`), which the 3-pigeon/2-hole case above does not
state. Pairwise `int_ne` is used for the same fragment reason as
`srcPigeonhole` (array-typed `fzn_all_different_int` is outside the
accepted fragment); the pigeonhole structure is unchanged. Expected
verdict: UNSAT, oracle count 0 (checked against the independent oracle
exactly like the other cases). -/
def srcRepeatedLearning : String :=
  "var 1..3: a;\nvar 1..3: b;\nvar 1..3: c;\nvar 1..3: d;\n\
   constraint int_ne(a, b);\nconstraint int_ne(a, c);\n\
   constraint int_ne(a, d);\nconstraint int_ne(b, c);\n\
   constraint int_ne(b, d);\nconstraint int_ne(c, d);\nsolve satisfy;\n"

/-- The fixture table: label, source string, expected oracle solution
count, expected SAT flag (`count > 0`; retained for readability — the oracle
count already pins the verdict), and the minimum number of conflicts the
certified route must record while solving the fixture (`SearchStats.conflicts`
of `solveDomWithStats`, a real counter of the certified route; `0` = no
conflict-count expectation). Only the repeated-learning case states a
minimum (`≥ 2`, i.e. genuinely repeated conflict-driven work — a
single-refutation shortcut would fail its check). -/
def fixtures : List (String × String × Nat × Bool × Nat) :=
  [ ("empty-sat", srcEmptySat, 1, true, 0)
  , ("root-conflict", srcRootConflict, 0, false, 0)
  , ("value-removal", srcValueRemoval, 1, true, 0)
  , ("assert-propagate", srcAssertPropagate, 3, true, 0)
  , ("redundant-pin", srcRedundantPin, 2, true, 0)
  , ("bool-not", srcBoolNot, 2, true, 0)
  , ("sparse", srcSparse, 1, true, 0)
  , ("neg-bounds", srcNegBounds, 2, true, 0)
  , ("pigeonhole-3-2", srcPigeonhole, 0, false, 0)
  , ("repeated-learning-4-3", srcRepeatedLearning, 0, false, 2) ]

/-! ## 2. Explicit expectations (executable, exit-code evidence)

The oracle is `Tests/OracleFixtures.lean`'s independent enumeration over
`allAssigns`; it never calls the LeanFzn.Solver's propagation, learning or
backjumping. §2 leaves the expectations as the `fixtures` table of §1 and
checks them executably in `runFixtures`: parse+compile accepted, oracle
count matches the expectation, the certified route records at least the
row's minimum of conflicts (`SearchStats.conflicts`), and the CURRENT
certified route (`solveDomWithStats` over the same parsed+compiled problem)
agrees with the oracle (SAT witness validated by `oracleWitnessOk`, UNSAT
required to be oracle-UNSAT). -/

/-- One fixture's full runtime check: parse+compile accepted, oracle count
matches the expectation, the certified route records at least `minConflicts`
conflicts (`SearchStats.conflicts`; `≥ 2` is what marks the repeated-learning
case as repeated, so a single-refutation shortcut would fail here), and the
certified route's verdict agrees with the oracle. Returns
`ok (oracleCount, conflicts)` on success, `error reason` on failure. -/
def checkFixture (label src : String) (expected minConflicts : Nat)
    (_expectedSat : Bool) : Except String (Nat × Nat) :=
  match lcgOfSource src with
  | .error e => .error s!"{label}: parse/compile rejected: {e}"
  | .ok p =>
      let cnt := oracleCount p
      if cnt ≠ expected then
        .error s!"{label}: oracle count {cnt} ≠ expected {expected}"
      else
        let r := solveDomWithStats p
        let conflicts := r.2.conflicts
        if conflicts < minConflicts then
          .error s!"{label}: certified route recorded {conflicts} conflicts, \
            expected ≥ {minConflicts}"
        else
          match r.1 with
          | .sat a =>
              if oracleWitnessOk p a then .ok (cnt, conflicts)
              else .error s!"{label}: certified SAT witness rejected by the oracle"
          | .unsat =>
              if oracleSat p then .error s!"{label}: certified UNSAT but oracle SAT"
              else .ok (cnt, conflicts)
          | .unknown => .error s!"{label}: certified route returned unknown"

/-- Run every fixture; returns the pass/fail counts. -/
def runFixtures : IO (Nat × Nat) := do
  let mut passed := 0
  let mut failed := 0
  for (label, src, expected, expectedSat, minConflicts) in fixtures do
    match checkFixture label src expected minConflicts expectedSat with
    | .ok (cnt, conflicts) =>
        IO.println s!"ok public fixture {label} \
          (oracle count {cnt}, certified conflicts {conflicts})"
        passed := passed + 1
    | .error reason =>
        IO.eprintln s!"FAIL {reason}"
        failed := failed + 1
  return (passed, failed)

/-! ## 3. PENDING D2/T1 observation vocabulary — STATED, NOT APPLIED, and
NOT YET APPLICABLE

T0 round-1 status (verified in-tree): the four predicates below are the
D2/T1 observation vocabulary. They are STATED but applied to NO value here,
and they are NOT YET APPLICABLE to a parsed-source run, for exactly these
reasons:

  * the parsed-source public route (`solveDomWithStats` -> `solveWithStats`
    -> `analyzedSolve`; LeanFzn.Solver/LCG/DomPruning.lean, LeanFzn.Solver/LCG/Search.lean,
    LeanFzn.Solver/LCG/AnalysisDriver.lean) returns `SearchResult × SearchStats`, and
    `SearchStats` (LeanFzn.Solver/LCG/Pruned.lean) has NO `events` field; no
    parsed-source public call produces a `RuntimeEvents` value at all;
  * the in-tree event producers `runPhaseEvents` / `solveWithEvents`
    (LeanFzn.Solver/LCG/Scheduler.lean, LeanFzn.Solver/LCG/DomPruning.lean) are
    `noncomputable` and require the explicitly open phase obligation
    (`C3b.PhaseProgress`, with the named `hpool`/`hdb`/`hbr` residuals), so
    they yield no executable observation on any fixture today;
  * `Tests/SchedulerActivation.lean` DOES observe real `RuntimeEvents` from
    the real dispatcher, but on CONCRETE fixture configurations
    (dispatcher-stepped `SchedulerConfig`s), not from parsed source; T0/T1
    forbid substituting that constructed-state observation here.

Additional precision — why even a D2 producer could not be applied through
these predicates AS STATED: the `src : String` parameter is INERT. Every
body quantifies over `RuntimeEvents` only (the Lean linter reports the
unused binders; they are named `_src` below to make the inertness explicit).
The predicates therefore witness "some event record has this shape", not
"the public run of THIS source observed this event". D2/T1 must thread a
public producer (a function `String → RuntimeEvents` supplied by the public
API) through the predicates, or restate them against it. This module
deliberately does not invent that producer, any record value, or any
counter. The resolution / skipped-level-jump / assertion expectations
therefore remain REQUIREMENTS on D2/T1, not facts asserted here; no record
is constructed and no counter is fabricated. -/

/-- D2/T1 must observe a run where the counted analyzer resolved at least
`k ≥ 2` pivots (multiple reason resolutions) on this source. -/
def ObservesMultiResolution (_src : String) (k : Nat) : Prop :=
  ∃ (e : RuntimeEvents) (r : Nat),
    r = e.reasonResolutions ∧ k ≤ r

/-- D2/T1 must observe a jump whose target level is strictly below the
source level (a skipped decision level). -/
def ObservesSkippedLevel (_src : String) : Prop :=
  ∃ (e : RuntimeEvents) (src' tgt : Nat),
    e.sourceLevel = some src' ∧ e.targetLevel = some tgt ∧ tgt < src'

/-- D2/T1 must observe an asserting enqueue after the jump. -/
def ObservesAssertion (_src : String) : Prop :=
  ∃ e : RuntimeEvents, 1 ≤ e.assertingEnqueues

/-- D2/T1 must observe a real backjump event. -/
def ObservesBackjump (_src : String) : Prop :=
  ∃ e : RuntimeEvents, 1 ≤ e.backjumps

end T0Public

open T0Public in
def main : IO UInt32 := do
  let (passed, failed) ← T0Public.runFixtures
  IO.println "PENDING D2/T1 activation (no parsed-source RuntimeEvents producer yet; predicates stated, NOT applied — see §3):"
  IO.println "  T0Public.ObservesMultiResolution"
  IO.println "  T0Public.ObservesSkippedLevel"
  IO.println "  T0Public.ObservesAssertion"
  IO.println "  T0Public.ObservesBackjump"
  if failed == 0 then
    IO.println s!"ALL {passed} PUBLIC-SOURCE FIXTURE CHECKS PASSED"
    return 0
  else
    IO.eprintln s!"{failed} PUBLIC-SOURCE FIXTURE CHECKS FAILED ({passed} passed)"
    return 1

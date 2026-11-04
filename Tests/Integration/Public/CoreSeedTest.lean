/-
Public Core integration test: the carried Core clause database.

The test exercises the two properties that the incremental seam adds:

* `optLoopCoreSeed` on a small optimization model: the run completes, its
  solutions fit and are accepted, the seed trace has one entry per solve and
  every later round starts from a nonempty carried database.

* `coreSolveSeed` on the same small model: the first round returns a SAT
  witness and a terminal seed with more live clauses than the empty input
  seed; that seed is rebased onto the strictly stronger bound and handed
  to a second round without re-installing the seed clauses.  The second
  verdict is SAT or UNSAT, and a SAT answer must strictly improve the
  objective.  The small model keeps the test well inside the 300 s gate
  cap; the earlier corpus-scale variant on `fir_4_2` was removed because
  a full-fuel first round exceeded it.

The test prints `CoreSeedTest: OK` and exits 0 exactly when every check
passes.
-/
import LeanFzn.Integration.Public.Seed
import LeanFzn.Parser.Parser
import LeanFzn.Checker.Check

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Integration
open LeanFzn.Engine
open LeanFzn.Core

namespace Tests.Integration.Public.CoreSeedTest

private def parseOrPanic (src : String) : Model :=
  match Parser.parseModel src with
  | .ok m => m
  | .error e => panic! s!"unexpected parse error: {e}"

structure St where
  passed : Nat
  failed : Nat

def St.check (st : St) (name : String) (ok : Bool) : IO St := do
  if ok then
    IO.println s!"ok {name}"
    pure { st with passed := st.passed + 1 }
  else
    IO.eprintln s!"FAIL {name}"
    pure { st with failed := st.failed + 1 }

def header : String :=
"array [1..4] of int: coef = [1,2,3,-1];
array [1..3] of int: lo = [-1,-1,-1];
array [1..3] of int: hi = [1,1,1];
var 0..4: x :: output_var;
var 0..4: y :: output_var;
var 0..4: z :: output_var;
var 0..40: obj :: output_var;
var bool: flag;
array [1..3] of var int: xs :: output_array([1..3]) = [x,y,z];
array [1..4] of var int: xs4 :: output_array([1..4]) = [x,y,z,obj];
constraint int_lin_eq(coef,xs4,0);
constraint int_lin_le(lo,xs,-3);
constraint int_lin_le(hi,xs,6);
constraint bool_clause([flag],[]);
"

def minSrc : String := header ++ "solve minimize obj;\n"

def objOf (a : List Value) (slot : Nat) : Option Int :=
  match a[slot]? with | some (.int i) => some i | _ => none

/-- The small model: a completed run, optimal last value 3, a seed trace
with an empty first seed and nonempty later seeds, and every solution a
fitting accepted store with the reported objective value. -/
def tinyTest (st : St) : IO St := do
  let m := parseOrPanic minSrc
  match optimizeCoreSeed ({} : SearchConfig) m with
  | .error e =>
      st.check s!"tiny: compiles ({e})" false
  | .ok sum =>
      let mut st := st
      st ← st.check "tiny: run completes" sum.run.complete
      st ← st.check "tiny: finds a solution" (!sum.run.sols.isEmpty)
      st ← st.check "tiny: optimum is 3"
        (sum.run.sols.getLast?.map (fun t => t.2) == some 3)
      st ← st.check "tiny: one seed per solve"
        (sum.seeds.length == sum.run.sols.length + 1)
      st ← st.check "tiny: first seed is the empty seed"
        (sum.seeds.head? == some 0)
      st ← st.check "tiny: later rounds carry a nonempty database"
        (sum.seeds.tail.all (fun n => n > 0))
      st ← st.check "tiny: solutions fit, are accepted and read their value"
        (sum.run.sols.all fun t =>
          fitsB (propagationProblem sum.p) t.1 &&
          accepts sum.p t.1 &&
          (m.solve.objective (sum.p.toStore t.1) == some t.2))
      pure st

/-- Two manually chained objective-bound rounds on the small model: the first
round's terminal seed is rebased to the stronger bound and reused without
re-installing the seed clauses. -/
def chainTest (st : St) : IO St := do
  let m := parseOrPanic minSrc
  match compileModelOpt m with
  | .error e =>
      st.check s!"chain: model compiles ({e})" false
  | .ok (p, spec) =>
      let mut st := st
      match coreSolveSeed p ({} : SearchConfig) coreFuel (CoreSeed.initial p) with
      | (.sat a1, _, s1) =>
          st ← st.check "chain: first round is SAT" true
          st ← st.check "chain: first witness fits the box"
            (fitsB (propagationProblem p) a1)
          st ← st.check "chain: first witness is accepted"
            (accepts p a1)
          st ← st.check "chain: first round installed seed clauses"
            (s1.db.live > (CoreSeed.initial p).db.live)
          st ← st.check "chain: returned seed is marked seeded" s1.seeded
          match objOf a1 spec.slot with
          | none =>
              st.check "chain: first witness reads an integer objective" false
          | some v1 =>
              -- Rebase the carried database onto the strictly stronger
              -- bound `some v1`; the box is unchanged.
              let hdoms : (curP p spec (some v1)).domains = p.domains := by
                rw [curP_domains]
              let hacc : ∀ b, accepts (curP p spec (some v1)) b = true →
                  accepts p b = true := by
                intro b hb
                exact (accepts_add.mp hb).1
              let s2 : CoreSeed (curP p spec (some v1)) :=
                s1.rebase hdoms hacc
              st ← st.check "chain: rebase preserves the live database"
                (s2.db.live == s1.db.live)
              st ← st.check "chain: rebased seed is still marked seeded"
                s2.seeded
              match coreSolveSeed (curP p spec (some v1))
                  ({} : SearchConfig) coreFuel s2 with
              | (.sat a2, _, s2') =>
                  st ← st.check "chain: second round finds an improvement"
                    true
                  st ← st.check "chain: second witness fits the box"
                    (fitsB (propagationProblem (curP p spec (some v1))) a2)
                  st ← st.check "chain: second witness is accepted at the bound"
                    (accepts (curP p spec (some v1)) a2)
                  st ← st.check "chain: second round keeps the database alive"
                    (s2'.db.live > 0)
                  match objOf a2 spec.slot with
                  | none =>
                      st.check "chain: second witness reads an integer objective"
                        false
                  | some v2 =>
                      st.check "chain: second objective strictly improves"
                        (betterB spec.dir v2 v1)
              | (.unsat, _, s2') =>
                  st ← st.check "chain: second round closes the bound" true
                  st ← st.check "chain: UNSAT round keeps the database alive"
                    (s2'.db.live > 0)
                  pure st
              | (.gaveUp, _, _) =>
                  st.check "chain: second round does not give up" false
      | (.unsat, _, _) =>
          st.check "chain: first round is SAT" false
      | (.gaveUp, _, _) =>
          st.check "chain: first round is SAT" false

def main : IO UInt32 := do
  let mut st : St := { passed := 0, failed := 0 }
  st ← tinyTest st
  st ← chainTest st
  IO.println s!"passed {st.passed}, failed {st.failed}"
  if st.failed == 0 then
    IO.println "CoreSeedTest: OK"
    return 0
  else
    IO.eprintln "CoreSeedTest: FAILED"
    return 1

end Tests.Integration.Public.CoreSeedTest

def main : IO UInt32 := Tests.Integration.Public.CoreSeedTest.main

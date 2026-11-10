/-
Purpose: Regression tests for the T2 verified rank-decomposition checker
and its proved clause-entailment theorem (PLAN.md phase 5).

The synthetic three-node problem is a hand-built compiled `circuit`
decomposition: one element row per node, two reified successor rows per
non-folded node and the two Boolean linkage clauses, with `rank[1] = 1`
and `rank[1] = 2` pinned by singleton domains.  It checks the recognizer,
the checker's refusal of every planted mutation, the generated clause
count, the false-ground 2-cycle UNSAT and the certified UNSAT verdict.

The real-file group replays the same checks on all five Gecode `tsptw`
decompositions (n = 21, 81, 101): recognition succeeds, the checker
accepts, the clause count is `n * (n - 1) / 2`, and altering, deleting or
widening one checked row is refused.  The generated clauses are proved
entailed but are not registered by the default search (T3's runtime
experiments were rejected; see tmp/design/t2-rank-circuit.md).

Dependencies: Compiler.Objective/RankCircuit, parser, Engine.Search,
Engine.Proofs.RankCircuit; no Legacy imports.
DAG: certified compiler + engine proofs -> this regression executable.
-/
import LeanFzn.Compiler.Objective
import LeanFzn.Compiler.RankCircuit
import LeanFzn.Parser.Parser
import LeanFzn.Engine.Search
import LeanFzn.Engine.Proofs.RankCircuit

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics
open LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace Tests.Compiler.RankCircuitTest

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

/-! ## The synthetic three-node rank decomposition -/

def d123 : Dom := Dom.ofList [.int 1, .int 2, .int 3]
def dBool : Dom := Dom.ofList [.bool false, .bool true]
def d1 : Dom := Dom.ofList [.int 1]
def d2 : Dom := Dom.ofList [.int 2]

/-- Slots: 0..2 predecessors, 3..5 ranks, 6..8 per-row pins,
    9..11 element results, 12..17 the six reification slots. -/
def synthDoms : List Dom :=
  [d123, d123, d123,
   d1, d123, d123,
   d1, d1, d1,
   d2, d123, d123,
   dBool, dBool, dBool,
   dBool, dBool, dBool]

def synthConstraints : List DomConstraint :=
  [.arrayVarIntElementSlot [3, 4, 5] 0 9,
   .arrayVarIntElementSlot [7, 4, 5] 1 10,
   .arrayVarIntElementSlot [8, 4, 5] 2 11,
   .linEqReif [1] [4] 3 12,
   .linEqReif [1] [10] 1 13,
   .linEqReif [1, -1] [10, 4] 1 14,
   .boolClauseSlot [13] [12],
   .boolClauseSlot [12, 14] [],
   .linEqReif [1] [5] 3 15,
   .linEqReif [1] [11] 1 16,
   .linEqReif [1, -1] [11, 5] 1 17,
   .boolClauseSlot [16] [15],
   .boolClauseSlot [15, 17] []]

def synthProblem : CompiledProblem DomConstraint :=
  { names := (List.range synthDoms.length).map (fun i => s!"s{i}")
    domains := synthDoms
    constraints := synthConstraints
    objective := ()
    source := default
    toStore := fun _ _ => none
    domainsArray := synthDoms.toArray
    domainsArray_toList := by simp }

/-- Replace a domain while keeping the array mirror in sync. -/
def setDomAt (p : CompiledProblem DomConstraint) (s : Nat) (d : Dom) :
    CompiledProblem DomConstraint :=
  let ds := p.domains.set s d
  { p with domains := ds
           domainsArray := ds.toArray
           domainsArray_toList := by simp }

/-- Force a slot to the integer `k` by a checked pair of bounds. -/
def forceEq (p : CompiledProblem DomConstraint) (s : Nat) (k : Int) :
    CompiledProblem DomConstraint :=
  { p with constraints := p.constraints ++ [.leConstHi s k, .leConstLo s k] }

/-- Drop the first variable-element row. -/
def dropFirstElemRow (p : CompiledProblem DomConstraint) :
    CompiledProblem DomConstraint :=
  let rec go : List DomConstraint → List DomConstraint
    | [] => []
    | dc :: rest =>
        match dc with
        | .arrayVarIntElementSlot _ _ _ => rest
        | _ => dc :: go rest
  { p with constraints := go p.constraints }

/-- Change the predecessor slot of the first variable-element row. -/
def alterFirstElemRow (p : CompiledProblem DomConstraint) :
    CompiledProblem DomConstraint :=
  let rec go : List DomConstraint → List DomConstraint
    | [] => []
    | dc :: rest =>
        match dc with
        | .arrayVarIntElementSlot is _ k =>
            .arrayVarIntElementSlot is 2 k :: rest
        | _ => dc :: go rest
  { p with constraints := go p.constraints }

/-- Remove the first occurrence of an exact constraint. -/
def dropExact (p : CompiledProblem DomConstraint) (target : DomConstraint) :
    CompiledProblem DomConstraint :=
  let rec go : List DomConstraint → List DomConstraint
    | [] => []
    | dc :: rest => if dc == target then rest else dc :: go rest
  { p with constraints := go p.constraints }

/-- Retarget the predecessor slot of one exact variable-element row. -/
def retargetPred (p : CompiledProblem DomConstraint) (target : DomConstraint)
    (newPred : Nat) : CompiledProblem DomConstraint :=
  let rec go : List DomConstraint → List DomConstraint
    | [] => []
    | dc :: rest =>
        match dc with
        | .arrayVarIntElementSlot is _ k =>
            if dc == target then .arrayVarIntElementSlot is newPred k :: rest
            else dc :: go rest
        | _ => dc :: go rest
  { p with constraints := go p.constraints }

/-- A certificate is refused when the recognizer gives up or the checker
    rejects the proposal. -/
def refused (p : CompiledProblem DomConstraint) : Bool :=
  match recognizeRankCircuit p with
  | none => true
  | some c => !checkRankCircuit p c

def synthChecks (st : St) : IO St := do
  let mut st := st
  match recognizeRankCircuit synthProblem with
  | none =>
      st ← st.check "synth recognizer" false
      pure st
  | some c =>
      st ← st.check "synth recognizer n=3" (c.n == 3)
      st ← st.check "synth checker accepts" (checkRankCircuit synthProblem c)
      st ← st.check "synth clause count"
        ((rankCircuitClauses c).length == 3)
      st ← st.check "synth seed count"
        ((rankCircuitSeeds synthProblem).length == 3)
      let certs : List (String × RankCert) :=
        [("unit pred", { c with units := c.units.set 1 { (c.units[1]!) with pred := 0 } }),
         ("unit result", { c with units := c.units.set 1 { (c.units[1]!) with y := 11 } }),
         ("unit b1", { c with units := c.units.set 1 { (c.units[1]!) with b1 := 13 } }),
         ("unit b2", { c with units := c.units.set 1 { (c.units[1]!) with b2 := 14 } }),
         ("unit b3", { c with units := c.units.set 1 { (c.units[1]!) with b3 := 12 } }),
         ("unit pin", { c with units := c.units.set 1 { (c.units[1]!) with pin := 6 } }),
         ("folded flag", { c with units := c.units.set 0 { (c.units[0]!) with folded := false } }),
         ("nonfolded flag", { c with units := c.units.set 1 { (c.units[1]!) with folded := true } }),
         ("rank alignment", { c with ranks := [4, 3, 5] }),
         ("n too small", { c with n := 2 }),
         ("n too large", { c with n := 4 }),
         ("missing unit", { c with units := c.units.drop 1, n := 2 })]
      for (name, c') in certs do
        st ← st.check s!"synth checker rejects {name}"
          (!checkRankCircuit synthProblem c')
      -- Planted problem mutations: the genuine certificate no longer fits.
      let widened : Dom := Dom.ofList [.int 1, .int 2, .int 3, .int 4]
      st ← st.check "synth rejects widened rank domain"
        (!checkRankCircuit (setDomAt synthProblem 4 widened) c)
      st ← st.check "synth rejects changed pin domain"
        (!checkRankCircuit (setDomAt synthProblem 7 d2) c)
      st ← st.check "synth rejects widened folded result"
        (!checkRankCircuit (setDomAt synthProblem 9 d123) c)
      st ← st.check "synth rejects dropped element row"
        (!checkRankCircuit (dropFirstElemRow synthProblem) c)
      st ← st.check "synth rejects altered element row"
        (!checkRankCircuit (alterFirstElemRow synthProblem) c)
      -- Two-node 2-cycle: false ground, certified UNSAT.  The extra
      -- forcing rows do not affect the rank certificate, so recognition
      -- still succeeds; the seeded exclusion clauses do the work.
      let cycle := forceEq (forceEq synthProblem 0 2) 1 1
      let accs := (allAssigns cycle.domains).filter (accepts cycle)
      st ← st.check "synth 2-cycle has no accepting assignment" accs.isEmpty
      match LeanFzn.Engine.coreSolve cycle { var := .act, val := .min }
          LeanFzn.Engine.coreFuel with
      | .unsat => st ← st.check "synth 2-cycle certified UNSAT" true
      | _ => st ← st.check "synth 2-cycle certified UNSAT" false
      pure st

/-! ## Real Gecode rank decompositions -/

def realFiles : List String :=
  ["minizinc-challenge/2025fzn/tsptw/n20w140.005.fzn",
   "minizinc-challenge/2025fzn/tsptw/n20w160.001.fzn",
   "minizinc-challenge/2025fzn/tsptw/n20w180.004.fzn",
   "minizinc-challenge/2025fzn/tsptw/n80w180.003.fzn",
   "minizinc-challenge/2025fzn/tsptw/n100w120.003.fzn"]

def loadCompiled (path : String) : IO (Option (CompiledProblem DomConstraint)) := do
  let src ← IO.FS.readFile path
  match Parser.parseModel src with
  | .error e =>
      IO.eprintln s!"{path}: parse error: {e}"
      pure none
  | .ok m =>
      match compileModelOpt m with
      | .error e =>
          IO.eprintln s!"{path}: compile error: {e}"
          pure none
      | .ok (p, _) => pure (some p)

def realChecks (st : St) : IO St := do
  let mut st := st
  for path in realFiles do
    match ← loadCompiled path with
    | none => st ← st.check s!"{path}: loads" false
    | some p =>
        match recognizeRankCircuit p with
        | none =>
            st ← st.check s!"{path}: recognizer" false
        | some c =>
            st ← st.check s!"{path}: n={c.n} checker"
              (2 < c.n && checkRankCircuit p c)
            st ← st.check s!"{path}: clause count"
              ((rankCircuitClauses c).length == c.n * (c.n - 1) / 2)
            st ← st.check s!"{path}: seeds" ((rankCircuitSeeds p).length > 0)
            let wideList := (List.range (c.n + 1)).map fun k => Value.int (Int.ofNat k + 1)
            let widened := setDomAt p c.ranks[1]! (Dom.ofList wideList)
            st ← st.check s!"{path}: rejects widened rank domain"
              (!checkRankCircuit widened c)
            -- Mutate a row the certificate actually uses: the first
            -- non-folded unit's variable-element row.  The compiled model
            -- also has a cost array with the same row shape, so the
            -- first element row in the list is not necessarily a rank row.
            let i := if c.units[0]!.folded then 1 else 0
            let u := c.units[i]!
            let target := DomConstraint.arrayVarIntElementSlot
              (u.pin :: c.ranks.tail) u.pred u.y
            st ← st.check s!"{path}: rejects dropped rank row"
              (refused (dropExact p target))
            st ← st.check s!"{path}: rejects altered rank row"
              (refused (retargetPred p target ((u.pred + 1) % c.n)))
  pure st

def run : IO UInt32 := do
  let mut st : St := { passed := 0, failed := 0 }
  st ← synthChecks st
  st ← realChecks st
  IO.println s!"RankCircuitTest: {st.passed} passed, {st.failed} failed"
  if st.failed == 0 then
    IO.println "RankCircuitTest: OK"
    return 0
  else
    return 1

end Tests.Compiler.RankCircuitTest

def main : IO UInt32 := Tests.Compiler.RankCircuitTest.run

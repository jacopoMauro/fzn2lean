/- Diagnostic replay of the current engine: dependencies are Direct.Cli for
compilation/proved propagators and Direct.Search for the exhaustive oracle.
Generated mechanically from lcgSearch.go; production code is unchanged.
Run: lake env lean -j2 --run audits/pigeonhole_trace.lean
Snapshot Engine.lean SHA256: 7fefdf673c6d3787c85cee9aa63a1b1001207157ff48552d4a4f64c9fe27eb9f
The repeated signature omits reason clauses and the learned database; it is
a branch-configuration repeat, not equality of complete solver states. -/
import solver.Direct.Cli
import solver.Direct.Search
namespace LeanFzn.Solver.LCG
open LeanFzn LeanFzn.Solver LeanFzn.Solver.Core
inductive TraceStep where
  | next (st : State)
  | done (r : SearchResult)
def traceStep (problem : Problem DomConstraint Unit)
    (constraintHoldsB : DomConstraint → Assignment → Bool)
    (props : List Propagator) (st : State) : TraceStep :=
  let st1 := propagateLoop (32 + 8 * st.domains.length + 4 * st.trail.length)
    props st
  match st1.conflict, st1.decisionLevel with
  | some _, 0 => .done .unsat
  | some _, _ =>
      match analyzeConflict st1 with
      | none =>
          match st1.conflict with
          | some [] =>
              if trailBoolPinsOk problem st1.trail then
                let ng := (st1.trail.filter fun e => e.level > 0).map
                  fun e => e.literal.negate.norm
                let lvls := st1.trail.filter fun e => e.level > 0
                let maxL := lvls.foldl (fun acc e => max acc e.level) 0
                let bjL := lvls.foldl (fun acc e =>
                  if e.level == maxL then acc else max acc e.level) 0
                let d := st1.trail.find? fun e => e.level == maxL
                let st2 := repairAfterBackjump problem bjL
                  { st1 with learned := ng :: st1.learned }
                match d with
                | some de =>
                    if bjL == 0 then
                      TraceStep.next (enqueueNorm (newDecisionLevel st2)
                        de.literal.negate (some { clause := ng }))
                    else
                      TraceStep.next (enqueueNorm st2 de.literal.negate
                        (some { clause := ng }))
                | none => TraceStep.next st2
              else
                TraceStep.next (repairAfterBackjump problem (st1.decisionLevel - 1) st1)
          | _ =>
              TraceStep.next (repairAfterBackjump problem (st1.decisionLevel - 1) st1)
      | some an =>
          let learnt := an.learned.map (fun l => l.norm)
          let st2 := repairAfterBackjump problem an.backjumpLevel st1
          let st3 := { st2 with learned := learnt :: st2.learned }
          let st4 :=
            enqueueNorm st3 an.asserting (some { clause := learnt })
          TraceStep.next st4
  | none, _ =>
      if allSingleton st1 then
        match singletonAssignment st1 with
        | some a =>
            if fitsB problem a &&
                problem.constraints.all (fun c => constraintHoldsB c a) then
              .done (.sat a)
            else
              if st1.decisionLevel == 0 then .done .unsat
              else if trailBoolPinsOk problem st1.trail then
                let leafNg := (st1.trail.filter fun e => e.level > 0).map
                  fun e => e.literal.negate.norm
                TraceStep.next (repairAfterBackjump problem (st1.decisionLevel - 1)
                  { st1 with learned := leafNg :: st1.learned })
              else
                TraceStep.next (repairAfterBackjump problem (st1.decisionLevel - 1) st1)
        | none => .done .unknown
      else
        match decideLiteral st1 with
        | none => .done .unknown
        | some l => TraceStep.next (enqueueNorm (newDecisionLevel st1) l none)

def litText (l : Literal) : String :=
  let atom := match l.atom with
    | .intLe s k => s!"x{s}≤{k}"
    | .intNe s k => s!"x{s}≠{k}"
    | .boolEq s b => s!"x{s}={b}"
  if l.positive then atom else s!"¬({atom})"
def trailText (st : State) : String :=
  String.intercalate "," (st.trail.map fun e =>
    s!"{litText e.literal}@{e.level}{if e.reason.isSome then "r" else "d"}")
def replay (p : Problem DomConstraint Unit) (ps : List Propagator)
    (fuel : Nat) (st : State) : SearchResult :=
  match fuel with
  | 0 => .unknown
  | n+1 => match traceStep p DomConstraint.satisfiedB ps st with
    | .next s => replay p ps n s
    | .done r => r
end LeanFzn.Solver.LCG
open LeanFzn LeanFzn.Solver LeanFzn.Solver.Core LeanFzn.Solver.LCG
def main : IO Unit := do
  let src := "var 0..2: x;\nvar 0..2: y;\nvar 0..2: z;\nvar 0..2: w;\nconstraint int_ne(x,y);\nconstraint int_ne(x,z);\nconstraint int_ne(y,z);\nconstraint int_ne(x,w);\nconstraint int_ne(y,w);\nconstraint int_ne(z,w);\nsolve satisfy;"
  let .ok m := Parser.parseModel src | throw (IO.userError "parse failed")
  let .ok compiled := Direct.compileModel m | throw (IO.userError "compile failed")
  let p := Direct.toLCG compiled
  let ps := compiled.constraints.filterMap propagatorOfProved
  IO.println s!"oracle assignment: {reprStr (Direct.solveCompiled compiled)}"
  for n in [0,1,5,20,50,100] do
    let actual := lcgSearch.go p DomConstraint.satisfiedB ps n (initialStateWithRoots p)
    let copied := replay p ps n (initialStateWithRoots p)
    unless reprStr actual == reprStr copied do
      throw (IO.userError s!"replay disagrees with production at fuel {n}")
    IO.println s!"fuel={n} legacy={reprStr actual} replay={reprStr copied}"
  let mut st := initialStateWithRoots p
  let mut seen : List (String × Nat) := []
  for n in [0:25] do
    let post := propagateLoop (32+8*st.domains.length+4*st.trail.length) ps st
    let key := s!"{st.decisionLevel}:{trailText st}:{reprStr st.domains}"
    let repeated := seen.find? (fun e => e.1 == key)
    IO.println s!"STEP {n} entry L={st.decisionLevel} trail=[{trailText st}] learned={st.learned.length} unique={(st.learned.foldl (fun cs c => if decide (c ∈ cs) then cs else c::cs) ([] : List Clause)).length} repeat={reprStr (repeated.map Prod.snd)}"
    IO.println s!"  propagated L={post.decisionLevel} trail=[{trailText post}] conflict={reprStr (post.conflict.map (fun c => c.map litText))} analysis={reprStr (analyzeConflict post)}"
    if decide (post.conflict = some []) then
      match scanAll post with
      | some (.inl c) =>
          IO.println s!"  MASKED learned conflict: {reprStr (c.map litText)} analysis={reprStr (analyzeConflict {post with conflict := some c})}"
      | _ => pure ()
    if n == 12 then
      for e in post.trail.reverse do
        if e.level == post.decisionLevel then
          match e.reason with
          | some r =>
              let bad := r.clause.filter fun q =>
                !skipEq (some e.literal) q.norm &&
                  (markLit post.trail post.decisionLevel [] [] q).isNone
              IO.println s!"  reason pivot={litText e.literal}: {reprStr (r.clause.map litText)} unmarkable={reprStr (bad.map litText)}"
          | none => pure ()
    if n == 14 then
      IO.println s!"  learned: {reprStr (st.learned.map (fun c => c.map litText))}"
      IO.println s!"  clause scans: {reprStr (st.learned.map (fun c => (c.map litText, (c.filter fun l => !post.negOnTrail l).map litText, (scanClause post c).isSome)))}"
    seen := (key,n)::seen
    match traceStep p DomConstraint.satisfiedB ps st with
    | .next next => st := next
    | .done r => IO.println s!"terminal={reprStr r}"; return

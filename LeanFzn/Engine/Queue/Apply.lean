/-
Purpose: Apply pending literals and build pending propagator/clause prunings.
Dependencies: LeanFzn.Engine.Queue.Worklist
DAG: Definitions/specifications -> queue proofs -> compatibility Engine.Queue.
-/
import LeanFzn.Engine.Queue.Worklist

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

def insertPending (st : EngineState p T) (item : Pending) :
    EngineState p T × Option (EClause p T) × Option PLit × Bool :=
  let (l, st) := canonLit st item.lit
  let slot := l.slot
  let d := st.doms.getD slot DomC.empty
  match d.evalLit l.lit with
  | some true => (st, none, none, false)
  | some false =>
      match reasonClause? st item.reason with
      | some ec =>
          let (ec, st) := canonClause st ec
          (st, some ec, none, false)
      | none => (st, none, none, true)
  | none =>
      let d' := d.applyLit l.lit
      if d'.isEmpty then
        match reasonClause? st item.reason with
        | some ec =>
            let (ec, st) := canonClause st ec
            (st, some ec, none, false)
        | none => (st, none, none, true)
      else
        let st := { st with
          doms := st.doms.set! slot d'
          stats := { st.stats with
            propagations := st.stats.propagations + (if item.count then 1 else 0) } }
        let st := trailPush st
          { lit := l, level := st.level, reason := item.reason, slot := slot, prev := d }
        let st := emitSlot st slot d d'
        let (neg, st) := canonNegLit st l
        (st, none, some neg, false)

/-- Turn a propagator's `prune` array into pending assignments, interning
each target and each reason clause.  The reason is stored in the transient
`reasons` array and referenced as `.reason id`. -/
def pushPropPrunes (st : EngineState p T) (pending : Array Pending)
    (ps : Array (PLit × EClause p T)) :
    EngineState p T × Array Pending × Bool :=
  ps.foldl (fun (acc : EngineState p T × Array Pending × Bool) pe =>
    let (st, pend, failed) := acc
    if failed then acc
    else
      let (l, st) := canonLit st pe.1
      let (ec, st) := canonClause st pe.2
      let rid := st.reasons.size
      let st := { st with reasons := st.reasons.push ec }
      (st, pend.push { lit := l, reason := .reason rid, count := true }, false))
    (st, pending, false)

/-- Turn clause-unit prunes into pending assignments.  Clause ids are the
reasons (`ReasonRef.learned`); the stored clause is already canonical. -/
def pushClausePrunes (pending : Array Pending) (ps : Array (PLit × Nat)) :
    Array Pending :=
  ps.foldl (fun acc (l, id) =>
    acc.push { lit := l, reason := .learned id, count := true }) pending

def pushPropStep (acc : EngineState p T × Array Pending × Bool) (pe : PLit × EClause p T) :
    EngineState p T × Array Pending × Bool :=
  let (st, pend, failed) := acc
  if failed then acc
  else
    let (l, st) := canonLit st pe.1
    let (ec, st) := canonClause st pe.2
    let rid := st.reasons.size
    let st := { st with reasons := st.reasons.push ec }
    (st, pend.push { lit := l, reason := .reason rid, count := true }, false)

end LeanFzn.Engine

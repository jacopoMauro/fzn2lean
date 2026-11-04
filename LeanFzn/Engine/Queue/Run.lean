/-
Purpose: Fuel-bounded priority propagation fixpoint and public propagation entry.
Dependencies: LeanFzn.Engine.Queue.Apply
DAG: Definitions/specifications -> queue proofs -> compatibility Engine.Queue.
-/
import LeanFzn.Engine.Queue.Apply

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

/-- Drain the pending literals, then the high worklist, then the low
worklist, until no work remains or a conflict is found.  Every recursive
call is on a structurally smaller fuel, so the loop is total without any
`partial`/`unsafe` escape hatch. -/
def drain (p : CompiledProblem DomConstraint) (T : LitTable)
    (st : EngineState p T) (pending : Array Pending) : Nat → PRes p T
  | 0 => { st, conflict := none, fuel := 0, failed := false }
  | f + 1 =>
    match pending.back? with
    | some item =>
        let pending := pending.pop
        let (st, conf, neg, failed) := insertPending st item
        match conf with
        | some c => { st, conflict := some c, fuel := f, failed := false }
        | none =>
          if failed then { st, conflict := none, fuel := f, failed := true }
          else
            match neg with
            | none => drain p T st pending f
            | some nl =>
                let (db, out) := st.db.propagateLiteral p T st.doms nl
                let st := { st with db := db }
                match out with
                | .none => drain p T st pending f
                | .conflict ec _ =>
                    let (ec, st) := canonClause st ec
                    { st, conflict := some ec, fuel := f, failed := false }
                | .prune ps => drain p T st (pushClausePrunes pending ps) f
    | none =>
        if st.queueHigh.size > 0 then
          let id := st.queueHigh[st.queueHigh.size - 1]!
          let st := setInQueue { st with queueHigh := st.queueHigh.pop } id 0
          match st.props[id]? with
          | none => drain p T st pending f
          | some pr =>
            match pr.run { doms := st.doms, level := st.level } with
            | .fix => drain p T st pending f
            | .conflict ec =>
                let (ec, st) := canonClause st ec
                { st, conflict := some ec, fuel := f, failed := false }
            | .prune ps =>
                let (st, pending, failed) := pushPropPrunes st pending ps
                if failed then { st, conflict := none, fuel := f, failed := true }
                else drain p T st pending f
        else if st.queueLow.size > 0 then
          let id := st.queueLow[st.queueLow.size - 1]!
          let st := setInQueue { st with queueLow := st.queueLow.pop } id 0
          match st.props[id]? with
          | none => drain p T st pending f
          | some pr =>
            match pr.run { doms := st.doms, level := st.level } with
            | .fix => drain p T st pending f
            | .conflict ec =>
                let (ec, st) := canonClause st ec
                { st, conflict := some ec, fuel := f, failed := false }
            | .prune ps =>
                let (st, pending, failed) := pushPropPrunes st pending ps
                if failed then { st, conflict := none, fuel := f, failed := true }
                else drain p T st pending f
        else { st, conflict := none, fuel := f + 1, failed := false }

/-- Run propagation to fixpoint from an empty pending worklist. -/
def propagate (p : CompiledProblem DomConstraint) (T : LitTable)
    (st : EngineState p T) (fuel : Nat) : PRes p T :=
  drain p T st #[] fuel

end LeanFzn.Engine

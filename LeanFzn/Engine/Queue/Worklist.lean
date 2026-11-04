/-
Purpose: Event subscriptions, worklist registration and enqueue operations.
Dependencies: LeanFzn.Engine.Queue.Types
DAG: Definitions/specifications -> queue proofs -> compatibility Engine.Queue.
-/
import LeanFzn.Engine.Queue.Types

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

/-- Grow the subscription array to at least `n` rows. -/
def ensureSubs (st : EngineState p T) (n : Nat) : EngineState p T :=
  if st.subs.size < n then
    { st with subs := st.subs ++ Array.replicate (n - st.subs.size) #[] }
  else st

/-- Grow the `inQueue` byte array to at least `n` bytes. -/
def ensureInQueue (st : EngineState p T) (n : Nat) : EngineState p T :=
  let rec go (b : ByteArray) : ByteArray :=
    if b.size < n then go (b.push 0) else b
  termination_by n - b.size
  { st with inQueue := go st.inQueue }

/-- Priority class of a registered propagator: binary constraints and
clause-like props first, wider global constraints second.  This is a
performance choice only. -/
def propIsHigh (pr : PropV2 p T) : Bool := pr.vars.size ≤ 2

/-- Set one `inQueue` byte, if the slot exists. -/
def setInQueue (st : EngineState p T) (id : Nat) (v : UInt8) : EngineState p T :=
  if id < st.inQueue.size then { st with inQueue := st.inQueue.set! id v } else st

/-- Enqueue a propagator unless it is already pending. -/
def enqueueProp (st : EngineState p T) (id : Nat) : EngineState p T :=
  if h : id < st.props.size then
    let pr := st.props[id]
    let st := ensureInQueue st (id + 1)
    if st.inQueue.get! id == 0 then
      if propIsHigh pr then
        { st with
          queueHigh := st.queueHigh.push id
          inQueue := st.inQueue.set! id 1 }
      else
        { st with
          queueLow := st.queueLow.push id
          inQueue := st.inQueue.set! id 2 }
    else st
  else st

/-- Enqueue the subscribers of `(slot, kind)`. -/
def enqueueSubs (st : EngineState p T) (s : Slot) (k : EventKind) : EngineState p T :=
  let idx := s * 3 + k.toNat
  if h : idx < st.subs.size then
    (st.subs[idx]).foldl (fun st id => enqueueProp st id) st
  else st

/-- Did a bound change between two domains? -/
def boundsChanged (a b : DomC) : Bool :=
  a.lo? != b.lo? || a.hi? != b.hi?

/-- Emit the monotone event triple of §6: always `domain`, plus `bounds`
when a bound moved, plus `fix` when the domain just became a singleton. -/
def emitSlot (st : EngineState p T) (s : Slot) (old new : DomC) : EngineState p T :=
  if old == new then st
  else
    let st := enqueueSubs st s .domain
    let st := if boundsChanged old new then enqueueSubs st s .bounds else st
    if !old.isFixed && new.isFixed then enqueueSubs st s .fix else st

/-- Register every propagator in `state.props` into `state.subs`. -/
def registerProps (st : EngineState p T) : EngineState p T :=
  let rec go (n : Nat) (id : Nat) (st : EngineState p T) : EngineState p T :=
    if h : id < n then
      match st.props[id]? with
      | some pr =>
        let st := pr.events.foldl (fun st (s, k) =>
          let idx := s * 3 + k.toNat
          let st := ensureSubs st (idx + 1)
          let lst := st.subs.getD idx #[]
          { st with subs := st.subs.set! idx (lst.push id) }) st
        go n (id + 1) st
      | none => st
    else st
  termination_by n - id
  decreasing_by omega
  go st.props.size 0 st

end LeanFzn.Engine

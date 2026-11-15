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

/-! ### Compiled form of `registerProps`

`registerProps` reads a subscriber list with `getD` and writes back the
pushed copy, so the list is shared while it is pushed and every push
copies it: quadratic in the length of one slot's list (a pinned slot
shared by a million rows).  The twin pushes through `Array.modify`, which
moves the list out first.  `registerProps_eq_fast` proves the two equal and
`@[csimp]` runs the twin. -/

/-- One subscription step of `registerProps`, pushing in place. -/
def registerStepFast (id : Nat) (st : EngineState p T) (e : Slot × EventKind) :
    EngineState p T :=
  let idx := e.1 * 3 + e.2.toNat
  let st := ensureSubs st (idx + 1)
  { st with subs := st.subs.modify idx (·.push id) }

/-- `registerProps` with the in-place subscription step. -/
def registerPropsFast (st : EngineState p T) : EngineState p T :=
  let rec go (n : Nat) (id : Nat) (st : EngineState p T) : EngineState p T :=
    if h : id < n then
      match st.props[id]? with
      | some pr => go n (id + 1) (pr.events.foldl (registerStepFast id) st)
      | none => st
    else st
  termination_by n - id
  decreasing_by omega
  go st.props.size 0 st

theorem array_modify_eq_set! {α : Type} [Inhabited α] (a : Array α) (i : Nat)
    (f : α → α) : a.modify i f = a.set! i (f (a.getD i default)) := by
  apply Array.ext_getElem?
  intro j
  rw [Array.getElem?_modify, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i < a.size
    · simp [hi, Array.getD_eq_getD_getElem?]
    · simp [hi, Array.getElem?_eq_none (Nat.le_of_not_lt hi)]
  · simp [hij]

theorem registerStepFast_eq (id : Nat) (st : EngineState p T) (e : Slot × EventKind) :
    registerStepFast id st e =
      (let idx := e.1 * 3 + e.2.toNat
       let st := ensureSubs st (idx + 1)
       let lst := st.subs.getD idx #[]
       { st with subs := st.subs.set! idx (lst.push id) }) := by
  simp only [registerStepFast, array_modify_eq_set!]
  rfl

theorem registerPropsFast_go_eq (n : Nat) :
    ∀ id (st : EngineState p T), registerPropsFast.go n id st = registerProps.go n id st := by
  intro id
  induction h : n - id using Nat.strongRecOn generalizing id with
  | ind k ih =>
    intro st
    rw [registerPropsFast.go.eq_def, registerProps.go.eq_def]
    by_cases hid : id < n
    · simp only [dif_pos hid]
      cases st.props[id]? with
      | none => rfl
      | some pr =>
        dsimp only
        rw [ih (n - (id + 1)) (by omega) (id + 1) rfl]
        congr 1
        congr 1
        funext st' e
        rcases e with ⟨s, k'⟩
        exact registerStepFast_eq id st' (s, k')
    · simp only [dif_neg hid]

@[csimp] theorem registerProps_eq_fast :
    @registerProps = @registerPropsFast := by
  funext p T st
  exact (registerPropsFast_go_eq st.props.size 0 st).symm

end LeanFzn.Engine

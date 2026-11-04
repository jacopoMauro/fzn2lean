/-
Purpose: Pending results and declarative queue/history/frame invariants; no preservation proofs.
Dependencies: LeanFzn.Engine.Trail, LeanFzn.Engine.Prop, LeanFzn.Engine.Clauses
DAG: Definitions/specifications -> queue proofs -> compatibility Engine.Queue.
-/
import LeanFzn.Engine.Trail
import LeanFzn.Engine.Prop
import LeanFzn.Engine.Clauses

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

/-- One pending assignment.  `count` is false for decisions, so
`stats.propagations` matches the kernel's per-implied-literal counter. -/
structure Pending where
  lit : PLit
  reason : ReasonRef
  count : Bool
  deriving Repr

/-- Result of a propagation/fixpoint run.  `fuel = 0` means the caller ran
out of budget; `failed` is a defensive internal-failure flag, never a
verdict. -/
structure PRes (p : CompiledProblem DomConstraint) (T : LitTable) where
  st : EngineState p T
  conflict : Option (EClause p T)
  fuel : Nat
  failed : Bool := false

/-- One fold step of `domAfter`: apply the literal of the trail entry at
`pos`.  Missing positions are inert (they never occur under `TrailInv`). -/
def domStep (tr : Array Entry) (d : DomC) (pos : Nat) : DomC :=
  match tr[pos]? with
  | some e => d.applyLit e.lit.lit
  | none => d

/-- Domain of slot `s` after the first `k` entries of its change list,
starting from the converted initial domain `init[s]`. -/
def domAfter (init : Array DomC) (st : EngineState p T) (s k : Nat) : DomC :=
  ((st.changeList s).extract 0 k).foldl (domStep st.trail)
    (init.getD s DomC.empty)

/-- The initial domains are the conversions of the compiled domains. -/
def InitInv (p : CompiledProblem DomConstraint) (init : Array DomC) : Prop :=
  ∀ s, init.getD s DomC.empty =
    (DomC.ofDom? (p.domains.getD s Dom.empty)).getD DomC.empty

instance : Inhabited Entry where
  default :=
    { lit := ⟨0, ⟨.intLe 0 0, true⟩⟩
      level := 0
      reason := .decision
      slot := 0
      prev := DomC.empty }

/-- The slot-domain history invariant.  `doms_eq` relates the live domain
to the replay of the whole change list; `prev_eq` relates every entry's
undo image to the replay of the prefix strictly before it. -/
structure SlotHistory (init : Array DomC) (st : EngineState p T) : Prop where
  doms_eq : ∀ s, st.doms.getD s DomC.empty =
    domAfter init st s (st.changeList s).size
  prev_eq : ∀ s k, k < (st.changeList s).size →
    let pos := (st.changeList s).getD k 0
    let e := (st.trail.getD pos default)
    e.prev = domAfter init st s k

def DomsWF (st : EngineState p T) : Prop :=
  ∀ s, s < st.doms.size → (st.doms.getD s DomC.empty).WF

def HistInv (init : Array DomC) (st : EngineState p T) : Prop :=
  SlotHistory init st ∧ TrailInv st

def Good (init : Array DomC) (st : EngineState p T) : Prop :=
  SlotHistory init st ∧ TrailInv st ∧ DomsWF st

/-- Per-step bookkeeping: the failed flag stays false, reasons grow by one
push, pending grows by the new item, and new pending items resolve against
the new reasons array. -/
structure PropStepOK (a b : EngineState p T × Array Pending × Bool) : Prop where
  failed : b.2.2 = false
  reasons_pre : a.1.reasons.toList <+: b.1.reasons.toList
  pending_pre : a.2.1.toList <+: b.2.1.toList
  new_pending : ∀ item ∈ b.2.1.toList, item ∉ a.2.1.toList →
    ∃ rid c, item.reason = .reason rid ∧ item.count = true ∧ b.1.reasons[rid]? = some c
  old_reasons : ∀ (i : Nat) (x : EClause p T), a.1.reasons[i]? = some x → b.1.reasons[i]? = some x

/-- Bundle of the "shape" facts preserved by the propagation loop: the
scheduler fields are untouched, the intern table and reason store only
grow, the trail only grows, and the clause database keeps the same
carried clauses and size (and its invariant). -/
structure Frame (st0 st : EngineState p T) : Prop where
  props : st0.props = st.props
  subs : st0.subs = st.subs
  level : st0.level = st.level
  levelStart : st0.levelStart = st.levelStart
  table_pre : st0.table.lits.toList <+: st.table.lits.toList
  tableWF : st0.table.TableWF → st.table.TableWF
  reasons_pre : st0.reasons.toList <+: st.reasons.toList
  trail_pre : st0.trail.toList <+: st.trail.toList
  db_e : ∀ (id : Nat), (st0.db.clauses[id]?).map (fun sc : StoredClause p T => sc.e) =
      (st.db.clauses[id]?).map (fun sc : StoredClause p T => sc.e)
  db_size : st0.db.clauses.size = st.db.clauses.size
  db_inv : st0.db.Inv → st.db.Inv

end LeanFzn.Engine

/-
Purpose: finite-domain propagation closure and lazy explanation-clause generation.
Dependencies: FrameFilter narrows branches; ClausePropagation interprets clauses;
PruningTypes provides certified refinement contracts and search statistics.
DAG: frame/clauses -> Pruning -> certified kits -> public solve entry.
-/
import LeanFzn.Solver.Propagation.FrameFilter
import LeanFzn.Solver.Propagation.ClausePropagation
import LeanFzn.Solver.Propagation.PruningTypes
open LeanFzn.Semantics LeanFzn.Solver.Propagation



namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-- Domain-only observation: registered family propagators read the current box. -/
def frameState (f : BranchFrame) : State :=
  { domains := Frame.domains f, trail := [], decisionLevel := 0,
    clauses := [], learned := [], queue := [], conflict := none }

def frameViewedB (f : BranchFrame) : Bool :=
  (Frame.domains f).all (fun d => d.all (fun v => v.intView != none))

/-- FRAME LIVENESS (P1 S1′): every remaining domain is nonempty —
equivalently (P1's `exists_frameCovers_iff`) the frame covers some
assignment. Coverless frames admit no leaf solution inside them, so no
PROPAGATION EVENT may be selected there: the deduction path's semantic
obligations (contract `chronology`, `WellFormed` reason chronology) are
only well-posed at live frames. -/
def frameLiveB (f : BranchFrame) : Bool :=
  f.1.all (fun d => !d.isEmpty)

/-- Only a genuine domain reduction triggers another propagation round. -/
def productive (l : Literal) (f : BranchFrame) : Bool :=
  match filterFrame l f with
  | none => true
  | some g => decide (Frame.mass g < Frame.mass f)

inductive PruningEvent where
  | stable
  | conflict (clauses : List Clause)
  | implied (literal : Literal) (clause : Clause) (learnReason fromLearned : Bool)

/-- Clauses are unit relative to the finite domains, not merely syntactic trail pins. -/
def scanDatabase (original : List Clause) (f : BranchFrame) : List Clause → PruningEvent
  | [] => .stable
  | c :: rest =>
    match clauseRemaining f c with
    | [] => .conflict []
    | [l] => if productive l f then .implied l c false (!(original.contains c))
             else scanDatabase original f rest
    | _ => scanDatabase original f rest

/-- Skip repeated deductions that do not remove a value; they cannot loop. -/
def scanPropagators (f : BranchFrame) : List Propagator → PruningEvent
  | [] => .stable
  | p :: rest =>
    match p.run (frameState f) with
    | .stable => scanPropagators f rest
    | .conflict c => .conflict (if c.isEmpty then [] else [c])
    | .implied l r => if productive l f then .implied l r.clause true false
                      else scanPropagators f rest

/-- The next pruning event. IMPLIED events are LIVENESS-GATED (P1 S1′): at
a coverless frame the extended event is `.stable`, because a coverless
frame holds no leaf solution and its semantic deduction obligations are
not well-posed (the `ClosureContract`'s implied-antecedent fields would be
refuted there — kernel witness in the P1 audit). Conflicts are NOT gated
(their obligations are branch-relative/vacuous at coverless frames, and
the conflict route stays the sound dead-branch handler). -/
def nextPruningEvent (original : List Clause) (props : List Propagator)
    (f : BranchFrame) (db : List Clause) : PruningEvent :=
  match scanDatabase original f db with
  | .stable => if frameViewedB f then scanPropagators f props else .stable
  | .conflict cs => .conflict cs
  | .implied l c learnReason fromLearned =>
      if frameLiveB f then .implied l c learnReason fromLearned else .stable

/-- Saturate a branch. Every recursive call removes a finite-domain value.
Explanations are generated only when needed and shared with later branches.
No timeout or iteration allowance is used. -/
def propagationClosure (original : List Clause) (props : List Propagator)
    (f : BranchFrame) (db : List Clause) : Refinement :=
  match nextPruningEvent original props f db with
  | .stable => { frame := some f }
  | .conflict cs =>
    let learned := cs.filter (fun c => !(db.contains c))
    { frame := none, learned, stats := { conflicts := 1, learnedClauses := learned.length } }
  | .implied l c learnReason fromLearned =>
    let fresh := learnReason && !(db.contains c)
    let learned := if fresh then [c] else []
    let stats : SearchStats :=
      { propagations := 1
        learnedClauses := if fresh then 1 else 0
        learnedPrunes := if fromLearned then 1 else 0 }
    match filterFrame l f with
    | none => { frame := none, learned, stats := stats.add { conflicts := 1 } }
    | some g =>
      if h : Frame.mass g < Frame.mass f then
        let r := propagationClosure original props g (learned ++ db)
        { frame := r.frame, learned := learned ++ r.learned, stats := stats.add r.stats }
      else { frame := some f, learned, stats }
termination_by Frame.mass f

/-- The semantic interface to registered propagators; no trail chronology is assumed. -/
structure PropagationContract (leaf : Assignment → Bool) (props : List Propagator) : Prop where
  implied : ∀ f, frameViewedB f = true → ∀ p ∈ props, ∀ l r,
    p.run (frameState f) = .implied l r →
    ∀ a, leaf a = true → FrameCovers f a → l.eval a = some true
  conflict : ∀ f, frameViewedB f = true → ∀ p ∈ props, ∀ c,
    p.run (frameState f) = .conflict c →
    ∀ a, leaf a = true → FrameCovers f a → False
  reason : ∀ f, frameViewedB f = true → ∀ p ∈ props, ∀ l r,
    p.run (frameState f) = .implied l r →
    ∀ a, leaf a = true → r.clause.SatisfiedBy a

  conflictReason : ∀ f, frameViewedB f = true → ∀ p ∈ props, ∀ c,
    p.run (frameState f) = .conflict c → c ≠ [] →
    ∀ a, leaf a = true → c.SatisfiedBy a

end LeanFzn.Solver.Propagation

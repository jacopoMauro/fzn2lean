/-
File: solver/LCG/Engine.lean

Purpose:
  The propagation engine and the LCG search-loop driver (PLAN.md
  L0.2–L0.5 executable half).

  Boolean side: reference clause scanning. Every active clause (original ++
  learned) must hold; a clause whose literals are all trail-false is the
  conflict clause; a clause with exactly one non-false literal is unit and
  that literal is enqueued with the clause as its reason. Watched literals
  and incremental schedules are the later refinement (L0.6); this scan is
  the semantics they must refine.

  Integer side: on every trail change (new decision, unit enqueue, or
  propagator deduction), all registered propagators run; each `.implied`
  result is enqueued through `enqueueNorm` with its nogood as the reason.
  Domains are a pure function of the trail (`domOfLit`), so backjumping
  rebuilds them consistently (`repairAfterBackjump`). A propagated literal
  that opposes a trail fact produces the two-literal conflict; a
  propagator-reported conflict sets `state.conflict` directly.

  Search loop: propagate to fixpoint; on conflict at level 0 report
  UNSAT; otherwise analyze (first-UIP, `analyzeConflict`), backjump,
  learn the analysis clause, and enqueue the asserting literal. When
  propagation quiesces without conflict: if all domains are singletons,
  the leaf check decides SAT (or backtracks chronologically — leaf
  nogoods are pending L0.3 work); otherwise a bisection decision
  `¬(s ≤ mid)` opens the next level on the first undecided slot.

  Fuel bounds every search iteration; exhaustion reports `unknown`,
  never `unsat` (the unknown/unsat distinction is the contract in
  `solver/LCG/Proofs/Search.lean`).

Dependencies:
  - solver.LCG.Propagate: explanation-carrying propagators.
  - solver.LCG.TrailEval (via Propagate): trail queries, 1-UIP analysis.

DAG:
  solver.LCG.Propagate -> solver.LCG.Engine
-/

import solver.LCG.Propagate

namespace LeanFzn.Solver.LCG

open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Solver (setSlot DomConstraint)

/-! ## Boolean clause scanning -/

/-- All active clauses: original and learned. -/
def State.allClauses (st : State) : List Clause := st.clauses ++ st.learned

/-- Scan one clause under the current state: `some (.inl c)` — every
    literal is trail-false (conflict clause `c`); `some (.inr (l, r))` —
    exactly one non-false literal remains (unit: enqueue `l` with reason
    clause `r`); `none` — satisfied, or two-or-more open literals. -/
def scanClause (st : State) (c : Clause) :
    Option (Sum Clause (Literal × Reason)) :=
  if c.any fun l => st.litOnTrail l then none
  else
    match c.filter fun l => !st.negOnTrail l with
    | [] => some (.inl c)
    | [l] => some (.inr (l, { clause := c }))
    | _ => none

/-- One pass over every active clause: first conflict, else first unit. -/
def scanAll (st : State) : Option (Sum Clause (Literal × Reason)) :=
  let rec go (cs : List Clause) : Option (Sum Clause (Literal × Reason)) :=
    match cs with
    | [] => none
    | c :: rest =>
        match scanClause st c with
        | none => go rest
        | some r => some r
  go st.allClauses

/-! ## Enqueue and domain maintenance -/

/-- Keep only domain values whose integer view passes `keep`. -/
def domFilterInt (keep : Int → Bool) (d : List Value) : List Value :=
  d.filter fun v =>
    match v with
    | .int i => keep i
    | .bool b => keep (if b then 1 else 0)
    | _ => true

/-- Replace slot `s`'s domain by `f` applied to its current value
    (identity past the end of the slot list). -/
def updateSlot (doms : List (List Value)) (s : Nat)
    (f : List Value → List Value) : List (List Value) :=
  setSlot doms s (f (doms.getD s []))

/-- Apply the domain filter implied by literal `l`: Boolean atoms fix the
    slot to the forced value; positive order literals keep `≤ k`;
    negative ones keep `> k`. -/
def domOfLit (doms : List (List Value)) (l : Literal) : List (List Value) :=
  match l.atom with
  | .intLe s k =>
      if l.positive then
        updateSlot doms s (fun d => domFilterInt (fun p => p ≤ k) d)
      else
        updateSlot doms s (fun d => domFilterInt (fun p => p > k) d)
  | .boolEq s b =>
      updateSlot doms s (fun _ => [.bool (if l.positive then b else !b)])

/-- Normalize and enqueue a literal with its reason, skipping
    re-assertions of trail facts. Opposite-fact enqueues (asserting the
    negation of a trail fact) set the two-literal conflict `[l, ¬l]`. -/
def enqueueNorm (st : State) (l0 : Literal) (reason : Option Reason) : State :=
  let l := l0.norm
  if st.litOnTrail l then st
  else if st.negOnTrail l then
    { st with conflict := some [l, l.negate] }
  else
    let st' := enqueue st l reason
    { st' with domains := domOfLit st'.domains l }

/-- Run every propagator, applying implied literals immediately and
    recording the first reported conflict. -/
def runPropagators (props : List Propagator) (st : State) : State :=
  let rec go (ps : List Propagator) (acc : State) : State :=
    match ps with
    | [] => acc
    | p :: rest =>
        if acc.conflict.isSome then acc
        else
          match p.run acc with
          | .stable => go rest acc
          | .conflict c => { acc with conflict := some c }
          | .implied l r => go rest (enqueueNorm acc l (some r))
  go props st

/-- Propagation to fixpoint: unit clause enqueue, then propagator sweep.
    A propagator trail extension restarts the scan; a quiescent state is
    returned unchanged. Fuel bounds the loop (each continuing iteration
    strictly extends the trail). -/
def propagateLoop (fuel : Nat) (props : List Propagator) (st : State) : State :=
  match fuel with
  | 0 => st
  | fuel + 1 =>
      if st.conflict.isSome then st
      else
        match scanAll st with
        | some (.inl c) => { st with conflict := some c }
        | some (.inr (l, r)) => propagateLoop fuel props (enqueueNorm st l (some r))
        | none =>
            let st' := runPropagators props st
            if st'.trail.length == st.trail.length then st'
            else propagateLoop fuel props st'

/-- Rebuild the state after a backjump: drop entries above `level`,
    recompute the domains from the kept trail order, and clear the
    conflict. -/
def repairAfterBackjump (problem : Problem Constraint Objective)
    (level : Nat) (st : State) : State :=
  let kept := st.trail.filter fun e => e.level ≤ level
  let doms := kept.foldl (fun acc e => domOfLit acc e.literal) problem.domains
  { st with trail := kept, domains := doms, decisionLevel := level, conflict := none }

/-- Decide assignment fit: right length and every value in its original
    problem domain. -/
def fitsB (problem : Problem Constraint Objective)
    (a : Assignment) : Bool :=
  a.length == problem.domains.length &&
    (List.range a.length).all fun s =>
      match a[s]? with
      | some v => valueMemB v (problem.domains.getD s [])
      | none => true

/-- `fitsB` decides `Fits`. -/
theorem fitsB_iff {problem : Problem Constraint Objective} {a : Assignment} :
    fitsB problem a = true ↔ a.Fits problem.domains := by
  constructor
  · intro h
    simp only [fitsB, beq_iff_eq, Bool.and_eq_true] at h
    obtain ⟨hlen, hall⟩ := h
    refine ⟨hlen, ?_⟩
    intro slot value hval
    have hlt : slot < a.length := by
      rw [List.getElem?_eq_some_iff] at hval
      exact hval.1
    have hmemr : slot ∈ List.range a.length := List.mem_range.mpr hlt
    have hall' := List.all_eq_true.mp hall slot hmemr
    cases hget : a[slot]? with
    | none => rw [hget] at hval; exact absurd hval (by simp)
    | some v =>
      rw [hget] at hall'
      rw [hget] at hval
      injection hval with hval
      subst hval
      exact valueMemB_iff.mp hall'
  · intro h
    obtain ⟨hlen, hmem⟩ := h
    simp only [fitsB, beq_iff_eq, Bool.and_eq_true]
    refine ⟨hlen, ?_⟩
    rw [List.all_eq_true]
    intro slot hslot
    rw [List.mem_range] at hslot
    cases hget : a[slot]? with
    | none => simp only [hget]
    | some v =>
      simp only [hget]
      exact valueMemB_iff.mpr (hmem slot v hget)

/-! ## The search loop -/

/-- Root facts of the initial domains: for every slot with at least one
    integer value, the two order literals pinning its initial
    integer-view bounds (`¬(s ≤ min−1)` and `s ≤ max`). Enqueued at
    level 0, they witness every cause literal built from initial domain
    extrema, so conflict analysis can resolve domain-derived causes, and
    `trailLo`/`trailHi` reproduce the initial bounds before any
    decision. -/
def rootFacts (doms : List (List Value)) : List Literal :=
  let rec go (s : Nat) (ds : List (List Value)) : List Literal :=
    match ds with
    | [] => []
    | d :: rest =>
        match domMinI d, domMaxI d with
        | some mn, some mx => negLe s (mn - 1) :: posLe s mx :: go (s + 1) rest
        | _, _ => go (s + 1) rest
  go 0 doms

/-- The initial state with root facts enqueued (level 0, no reasons). -/
def initialStateWithRoots (problem : Problem Constraint Objective) : State :=
  let st0 := initialState problem
  rootFacts problem.domains |>.foldl (fun st l =>
    if st.litOnTrail l then st else enqueue st l none) st0


/-- Pick a branching literal: `¬(s ≤ mid)` bisection on the first slot
    whose domain still has at least two integer values. -/
def decideLiteral (st : State) : Option Literal :=
  let rec go (s : Nat) (doms : List (List Value)) : Option Literal :=
    match doms with
    | [] => none
    | d :: rest =>
        match domMinI d, domMaxI d with
        | some mn, some mx =>
            if mn < mx then some (negLe s ((mn + mx) / 2))
            else go (s + 1) rest
        | _, _ => go (s + 1) rest
  go 0 st.domains

/-- Is every slot domain a singleton (a complete assignment)? -/
def allSingleton (st : State) : Bool :=
  st.domains.all fun d => d.length == 1

/-- The complete assignment under all-singleton domains. -/
def singletonAssignment (st : State) : Option Assignment :=
  st.domains.mapM fun d =>
    match d with
    | [v] => some v
    | _ => none

/-- The LCG search loop (see the module docstring). `fuel` bounds the
    number of decisions/conflicts; exhaustion reports `unknown`. -/
def lcgSearch (fuel : Nat)
    (problem : Problem Constraint Objective)
    (constraintHoldsB : Constraint → Assignment → Bool)
    (props : List Propagator) : SearchResult :=
  let st0 := initialStateWithRoots problem
  let rec go (fuel : Nat) (st : State) : SearchResult :=
    match fuel with
    | 0 => .unknown
    | fuel + 1 =>
        let st1 := propagateLoop (32 + 8 * st.domains.length + 4 * st.trail.length)
          props st
        match st1.conflict, st1.decisionLevel with
        | some _, 0 => .unsat
        | some _, _ =>
            match analyzeConflict st1 with
            | none =>
                -- chronological fallback when analysis cannot resolve;
                -- domains are rebuilt to the retained trail
                go fuel (repairAfterBackjump problem (st1.decisionLevel - 1) st1)
            | some an =>
                -- normalize the learned clause: normalization preserves
                -- evaluation (`Literal.norm_eval`), so search behavior is
                -- unchanged, while canonical Booleans keep the clause DB
                -- and the asserting reason norm-normalized (reachability)
                let learnt := an.learned.map (fun l => l.norm)
                let st2 := repairAfterBackjump problem an.backjumpLevel st1
                let st3 := { st2 with learned := learnt :: st2.learned }
                let st4 :=
                  enqueueNorm st3 an.asserting (some { clause := learnt })
                go fuel st4
        | none, _ =>
            if allSingleton st1 then
              match singletonAssignment st1 with
              | some a =>
                  if fitsB problem a &&
                      problem.constraints.all (fun c => constraintHoldsB c a) then
                    .sat a
                  else
                    -- leaf violation under a complete assignment: retreat
                    -- chronologically (leaf nogoods are L0.3 work); domains
                    -- are rebuilt to the retained trail
                    if st1.decisionLevel == 0 then .unsat
                    else go fuel (repairAfterBackjump problem (st1.decisionLevel - 1) st1)
              | none => .unknown
            else
              match decideLiteral st1 with
              | none => .unknown
              | some l => go fuel (enqueueNorm (newDecisionLevel st1) l none)
  go fuel st0

end LeanFzn.Solver.LCG

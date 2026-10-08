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

  Public search uses an explicit chronological frontier of unvisited
  value alternatives (Frontier). Every transition consumes pending work;
  an empty frontier yields UNSAT and budget exhaustion yields unknown.
  The nested `lcgSearch.go` retains the historical analysis/flip loop for
  its established proofs and diagnostics; it is not called by the driver.
  Propagation and conflict analysis are available primitives, but the
  chronological driver checks complete leaves without propagation pruning.

Dependencies:
  - solver.LCG.Propagate: explanation-carrying propagators.
  - solver.LCG.Frontier: explicit pending alternatives and finite work budget.
  - solver.LCG.TrailEval (via Propagate): trail queries, 1-UIP analysis.

DAG:
  solver.LCG.Propagate -> solver.LCG.Engine
-/

import solver.LCG.Propagate
import solver.LCG.Frontier

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
    negative ones keep `> k`; positive value-removal literals remove
    exactly `k` (keeping every other value, sets/arrays included);
    negative ones pin to the singleton `k`. -/
def domOfLit (doms : List (List Value)) (l : Literal) : List (List Value) :=
  match l.atom with
  | .intLe s k =>
      if l.positive then
        updateSlot doms s (fun d => domFilterInt (fun p => p ≤ k) d)
      else
        updateSlot doms s (fun d => domFilterInt (fun p => p > k) d)
  | .boolEq s b =>
      updateSlot doms s (fun _ => [.bool (if l.positive then b else !b)])
  | .intNe s k =>
      if l.positive then
        updateSlot doms s (fun d => domFilterInt (fun p => p ≠ k) d)
      else
        updateSlot doms s (fun d => domFilterInt (fun p => p = k) d)

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

/-- The executable `TrailBoolPins` gate: every Boolean-pin trail
    entry sits on a slot whose PROBLEM domain is all-Bool. Vacuously
    true for trails without Boolean pins (compiled models' order-
    literal trails and the constEq-Bool family's domain-gated
    pins). -/
def trailBoolPinsOk (problem : Problem Constraint Objective)
    (trail : List TrailEntry) : Bool :=
  trail.all fun e =>
    match e.literal.atom with
    | .boolEq s _ =>
        problem.domains.getD s [] |>.all fun v =>
          match v with
          | .bool _ => true
          | _ => false
    | _ => true

/-- The complete assignment under all-singleton domains. -/
def singletonAssignment (st : State) : Option Assignment :=
  st.domains.mapM fun d =>
    match d with
    | [v] => some v
    | _ => none

/-- The leaf predicate of the chronological traversal: original-domain
    fit, every compiled constraint, and every original clause. -/
def chronologicalLeaf (problem : Problem Constraint Objective)
    (constraintHoldsB : Constraint → Assignment → Bool) :
    Assignment → Bool :=
  fun a => fitsB problem a &&
    (problem.constraints.all (fun c => constraintHoldsB c a) &&
      problem.clauses.all (fun c => c.any (fun l => decide (l.eval a = some true))))

/-- Certified chronological traversal of the original finite search space.
    Pending siblings retain unused values, independently of conflict-analysis
    success. Propagator/analysis primitives remain available for refinement;
    this driver deliberately does not prune with unresolvable explanations.
    FUEL-FREE: the traversal terminates by the kernel-checked
    `frontierCost` measure; there is no search budget, so an accepted
    finite model always receives a verdict (SAT or UNSAT, never
    `unknown`). -/
def chronologicalSearch (problem : Problem Constraint Objective)
    (constraintHoldsB : Constraint → Assignment → Bool) : SearchResult :=
  match frontierSolve (chronologicalLeaf problem constraintHoldsB)
      [(problem.domains, [])] with
  | .sat a => .sat a
  | .unsat => .unsat

/-- The historical fuel-bounded chronological traversal, retained as an
    explicitly named diagnostic reference (budget exhaustion reports
    `unknown`). NOT the driver: the public path uses the fuel-free
    `chronologicalSearch` above. -/
def chronologicalSearchBounded (fuel : Nat)
    (problem : Problem Constraint Objective)
    (constraintHoldsB : Constraint → Assignment → Bool) : SearchResult :=
  frontierSearch (chronologicalLeaf problem constraintHoldsB) fuel
    [(problem.domains, [])]

/-- Public search uses the loop-free chronological frontier. The nested
    `go` is the historical analysis/flip implementation retained for proof
    compatibility and diagnostic comparison, not the executed entry path.
    FUEL-FREE: the verdict comes from the kernel-checked traversal. -/
def lcgSearch (problem : Problem Constraint Objective)
    (constraintHoldsB : Constraint → Assignment → Bool)
    (props : List Propagator) : SearchResult :=
  chronologicalSearch problem constraintHoldsB

/-- The historical fuel-bounded analysis/flip loop, retained as an
    explicitly named diagnostic reference for its established proofs.
    NOT the driver: the public path uses the fuel-free `lcgSearch`.
    The loop body is a TOP-LEVEL definition (`lcgSearchGo`) so the
    retained proofs' `lcgSearch.go` references resolve to it. -/
def lcgSearchGo (problem : Problem Constraint Objective)
    (constraintHoldsB : Constraint → Assignment → Bool)
    (props : List Propagator) : Nat → State → SearchResult
  | 0, _ => .unknown
  | fuel + 1, st =>
      let st1 := propagateLoop (32 + 8 * st.domains.length + 4 * st.trail.length)
          props st
      match st1.conflict, st1.decisionLevel with
      | some _, 0 => .unsat
      | some _, _ =>
          match analyzeConflict st1 with
          | none =>
                -- chronological fallback when analysis cannot resolve;
                -- domains are rebuilt to the retained trail. When the
                -- conflict clause is EMPTY (the propagator-origin
                -- shape — e.g. propNe's both-singleton report; scan
                -- and opposing-pair conflicts are never empty), LEARN
                -- THE TRAIL NOGOOD (the failed branch's positive-level
                -- literals, negated and normalized — the same shape
                -- as the leaf nogood below, gated the same way on
                -- `trailBoolPinsOk`): without it the retreat is
                -- indistinguishable from an unexplored branch and
                -- `decideLiteral` re-derives the same decision forever
                -- (the fuel-exhaustion cycle on `int_ne` pigeonholes,
                -- PLAN §5 items 4–5). Entitlement
                -- (`fallbackNogood_entailed`, Proofs/Reason.lean +
                -- `propagateLoop_conflict_nofit_empty`,
                -- Proofs/FallbackFit.lean): every internal solution
                -- either falsifies a positive-level trail literal
                -- (witnessed in the nogood) or fits the conflicted
                -- state's domains — and the empty conflict's origin
                -- excludes every fitting solution from being an
                -- internal solution. The learning is deliberately NOT
                -- done for nonempty unanalyzable conflicts (scan-origin
                -- trail-relative refutations): their fits-exclusion is
                -- false and the nogood would be unsound — those take
                -- the plain retreat. This arm is reachable only at a
                -- POSITIVE decision level (level 0 conflicts terminate
                -- in the `.unsat` arm above).
                match st1.conflict with
                | some [] =>
                    if trailBoolPinsOk problem st1.trail then
                      let ng := (st1.trail.filter fun e => e.level > 0).map
                        fun e => e.literal.negate.norm
                      -- P3b SECOND-MAX BACKJUMP + FLIP (2026-10-06):
                      -- the empirical ph4 trace showed the
                      -- chronological retreat to L-1 re-derives the
                      -- same decision forever (the learned trail
                      -- nogood never becomes unit). Instead: learn
                      -- the nogood, retreat to the SECOND-highest
                      -- falsifier level (dropping ALL max-level
                      -- entries, in particular the max-level
                      -- decision), and — at a positive backjump
                      -- level — FLIP the earliest max-level entry's
                      -- literal by enqueueing its negation with the
                      -- nogood as reason. The flip excludes the
                      -- just-refuted max-level prefix from the
                      -- re-descent (the progress argument: the
                      -- re-derived level-maxL decision cannot equal
                      -- the refuted one, because the flip's literal
                      -- now contradicts it on the trail). Verdict
                      -- soundness is untouched: `.unsat` requires a
                      -- level-0 conflict over entailed clauses;
                      -- `.sat` is revalidated by the leaf check.
                      -- (An asserting enqueue justified by UNIT-ness
                      -- of the trail nogood is impossible here — with
                      -- several max-level entries the nogood has
                      -- several open members; the flip is a
                      -- branch-exclusion device, not a unit
                      -- consequence. Completeness of the flip is P4's
                      -- contract; exhaustiveness is not claimed.)
                      -- The flip fires at EVERY positive bjL —
                      -- INCLUDING bjL = 0: the first empirical run
                      -- (85/85, ph4 UNSAT at 10k compiled) had the
                      -- unconditional flip, and gating it at bjL = 0
                      -- reintroduced the fuel-exhaustion cycle (the
                      -- level-1 conflicts in ph4 are exactly the
                      -- bjL = 0 shape, and their flips are what
                      -- exclude the re-descended branches). RootFacts
                      -- at a 0-stamped flip entry is P4-level proof
                      -- work (the flip's literal is justified at the
                      -- level-0 projection only for the branch the
                      -- nogood excludes); the flip's level-0 entry is
                      -- therefore marked as a DECISION-shaped entry by
                      -- keeping its reason — same as the analyzed
                      -- arm's enqueue at backjump 0, whose
                      -- justification (asserting_true_at_solutions)
                      -- this arm's proof arm must mirror.
                      let lvls := st1.trail.filter fun e => e.level > 0
                      let maxL := lvls.foldl (fun acc e => max acc e.level) 0
                      let bjL := lvls.foldl (fun acc e =>
                        if e.level == maxL then acc else max acc e.level) 0
                      let d := st1.trail.find? fun e => e.level == maxL
                      let st2 := repairAfterBackjump problem bjL
                        { st1 with learned := ng :: st1.learned }
                      match d with
                      | some de =>
                          -- SOUNDNESS FIX (P3b proof side, 2026-10-06):
                          -- at bjL = 0 the flip MUST NOT land at level 0.
                          -- A level-0 entry is a ROOT FACT — true at every
                          -- internal solution — and the flip literal is a
                          -- branch-exclusion device, not a unit consequence
                          -- of the nogood (with several positive entries
                          -- the nogood only entails that SOME entry is
                          -- false). Enqueuing it at level 0 would poison
                          -- RootFacts/Level0Solved and could certify a
                          -- WRONG `.unsat`. Instead, at bjL = 0 enqueue the
                          -- flip on a FRESH decision level (decision-shaped:
                          -- positive-level entries carry no root-fact
                          -- obligation, and the level-0 projection drops
                          -- them); the branch-exclusion effect is identical
                          -- (the flip literal still contradicts the
                          -- refuted branch on the trail). At bjL > 0 the
                          -- entry already sits at a positive level and the
                          -- enqueue stays on st2 (empirically validated
                          -- shape: the 85/85 run's bjL > 0 flips).
                          if bjL == 0 then
                            lcgSearchGo problem constraintHoldsB props fuel (enqueueNorm (newDecisionLevel st2)
                              de.literal.negate (some { clause := ng }))
                          else
                            lcgSearchGo problem constraintHoldsB props fuel (enqueueNorm st2 de.literal.negate
                              (some { clause := ng }))
                      | none => lcgSearchGo problem constraintHoldsB props fuel st2
                    else
                      lcgSearchGo problem constraintHoldsB props fuel (repairAfterBackjump problem (st1.decisionLevel - 1) st1)
                | _ =>
                    lcgSearchGo problem constraintHoldsB props fuel (repairAfterBackjump problem (st1.decisionLevel - 1) st1)
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
                lcgSearchGo problem constraintHoldsB props fuel st4
        | none, _ =>
            if allSingleton st1 then
              match singletonAssignment st1 with
              | some a =>
                  if fitsB problem a &&
                      problem.constraints.all (fun c => constraintHoldsB c a) then
                    .sat a
                  else
                    -- leaf violation under a complete assignment: learn
                    -- the LEAF NOGOOD (the failed assignment's positive-
                    -- level trail literals, negated and normalized —
                    -- entailed because every solution satisfying the
                    -- trail would equal the failed assignment and pass
                    -- the leaf check), then retreat chronologically.
                    -- When the search re-enters the same branch, the
                    -- scan reports the learned clause as a conflict and
                    -- the standard 1-UIP analysis takes over.
                    -- The learning is GATED on `trailBoolPinsOk`: the
                    -- nogood's entitlement needs every Boolean-pin
                    -- trail entry to sit on an all-Bool problem slot
                    -- (vacuous for compiled models — their pins are
                    -- domain-gated; the gate keeps abstract problems
                    -- on the plain-retreat path, honestly `unknown`).
                    if st1.decisionLevel == 0 then .unsat
                    else if trailBoolPinsOk problem st1.trail then
                      let leafNg := (st1.trail.filter fun e => e.level > 0).map
                        fun e => e.literal.negate.norm
                      lcgSearchGo problem constraintHoldsB props fuel (repairAfterBackjump problem (st1.decisionLevel - 1)
                        { st1 with learned := leafNg :: st1.learned })
                    else
                      lcgSearchGo problem constraintHoldsB props fuel (repairAfterBackjump problem (st1.decisionLevel - 1) st1)
              | none => .unknown
            else
              match decideLiteral st1 with
              | none => .unknown
              | some l => lcgSearchGo problem constraintHoldsB props fuel
                  (enqueueNorm (newDecisionLevel st1) l none)

/-- The historical fuel-bounded entry over the analysis/flip loop. -/
def lcgSearchBounded (fuel : Nat)
    (problem : Problem Constraint Objective)
    (constraintHoldsB : Constraint → Assignment → Bool)
    (props : List Propagator) : SearchResult :=
  lcgSearchGo problem constraintHoldsB props fuel (initialStateWithRoots problem)

namespace lcgSearch

/-- Compatibility alias: the historical `lcgSearch.go` name now resolves
    to the top-level `lcgSearchGo` loop (transparent definition; the
    retained proofs unfold it exactly as before). -/
abbrev go := @lcgSearchGo

end lcgSearch

end LeanFzn.Solver.LCG

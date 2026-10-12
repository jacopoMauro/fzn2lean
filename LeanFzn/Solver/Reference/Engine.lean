/- Historical and diagnostic search drivers. -/
import LeanFzn.Solver.Propagation.EngineCore
import LeanFzn.Solver.Propagation.Frontier


namespace LeanFzn.Solver.Reference
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-- Certified chronological traversal of the original finite search space.
    Pending siblings retain unused values, independently of conflict-analysis
    success. Propagator/analysis primitives remain available for refinement;
    this driver deliberately does not prune with unresolvable explanations.
    FUEL-FREE: the traversal terminates by the kernel-checked
    `frontierCost` measure; there is no search budget, so an accepted
    finite model always receives a verdict (SAT or UNSAT, never
    `unknown`). -/
def chronologicalSearch (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
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
    (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
    (constraintHoldsB : Constraint → Assignment → Bool) : SearchResult :=
  frontierSearch (chronologicalLeaf problem constraintHoldsB) fuel
    [(problem.domains, [])]

/-- Public search uses the loop-free chronological frontier. The nested
    `go` is the historical analysis/flip implementation retained for proof
    compatibility and diagnostic comparison, not the executed entry path.
    FUEL-FREE: the verdict comes from the kernel-checked traversal. -/
def lcgSearch (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
    (constraintHoldsB : Constraint → Assignment → Bool)
    (props : List Propagator) : SearchResult :=
  chronologicalSearch problem constraintHoldsB

/-- The historical fuel-bounded analysis/flip loop, retained as an
    explicitly named diagnostic reference for its established proofs.
    NOT the driver: the public path uses the fuel-free `lcgSearch`.
    The loop body is a TOP-LEVEL definition (`lcgSearchGo`) so the
    retained proofs' `lcgSearch.go` references resolve to it. -/
def lcgSearchGo (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
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
    (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
    (constraintHoldsB : Constraint → Assignment → Bool)
    (props : List Propagator) : SearchResult :=
  lcgSearchGo problem constraintHoldsB props fuel (initialStateWithRoots problem)

namespace lcgSearch

/-- Compatibility alias: the historical `lcgSearch.go` name now resolves
    to the top-level `lcgSearchGo` loop (transparent definition; the
    retained proofs unfold it exactly as before). -/
abbrev go := @lcgSearchGo

end lcgSearch

end LeanFzn.Solver.Reference

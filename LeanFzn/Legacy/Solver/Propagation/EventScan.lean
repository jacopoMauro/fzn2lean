/-
File: LeanFzn/Solver/Propagation/EventScan.lean

Purpose (PLAN task K2): make the scheduled propagator scan cheaper WITHOUT
changing its selection. `stampMatchAt` fuses the reference scan's two hot
steps — build `watchVersions v p.watches`, then compare it with
`stampNatEqB` — into ONE allocation-free recursion over the watch list. The
reference allocates a fresh `List Nat` (one cons cell per watched slot) on
EVERY propagator, clean or dirty, and throws it away immediately; the fused
walk reads `SchedVersions.getD` directly and short-circuits at the first
moved counter. `stampMatchAt_eq` proves the fused test is EXACTLY the
reference test for every stamp list and footprint (also the unaligned ones,
where both sides are `false`).

`scanPropagatorsSchedAuxFast` is the reference recursion with only that test
replaced; `scanPropagatorsSchedAuxFast_eq` proves it equals
`scanPropagatorsSchedAux` on the nose, and `scanPropagatorsSchedFast_eq`
lifts the equality to the wired scan (same event AND same returned
scheduler), so the coordinator's policy switch needs no new soundness
argument: `nextPruningEventFastSched_eq` proves the fast prompt IS the wired
`nextPruningEventSched`, and `_fst_eq` / `_OK` follow from the existing P1
theorems.

Why the scan still touches every propagator (and what the residual measured
cost is): the skip decision is keyed by the per-slot version vector
(`SchedVersions`), and the version vector has no slot->units index in the
carrier (`PropScheduler`), so a clean unit can only be certified clean by
reading its recorded stamps against the current counters. The fused walk
makes that certification one array read per watched slot and no
allocation; the alternative — a real dirty-set walk that SKIPS clean units
without reading their stamps — needs a slot-keyed occurrence index in the
scheduler (a `PropScheduler` field or an equal per-run structure); the
design and the proof obligation for that field are reported in the K2
handoff (coordinator-owned carrier change, not edited here).

DAG: ScheduledPropagation -> this file -> SchedulerStepSched (the dispatcher
wiring, coordinator-owned).
-/
import LeanFzn.Legacy.Solver.Propagation.ScheduledPropagation
open LeanFzn.Semantics LeanFzn.Solver.Core

set_option linter.unusedVariables false

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-! ## 1. Allocation-free version-stamp comparison -/

/-- Fused skip test: walk the recorded stamps and the watched atoms together,
reading the current per-slot counter directly. Same result as
`stampNatEqB stamps (watchVersions v watches)`, but no intermediate list. -/
def stampMatchAt (v : SchedVersions) : List Nat → List Atom → Bool
  | [], [] => true
  | x :: xs, a :: as => (x == v.getD a.slot 0) && stampMatchAt v xs as
  | _, _ => false

/-- **EQUIVALENCE (fused stamp test)**: for every stamp list and footprint
(including the unaligned cases, where both sides are `false`), the fused walk
is the reference projection-then-compare test. -/
theorem stampMatchAt_eq (v : SchedVersions) (stamps : List Nat) (ws : List Atom) :
    stampMatchAt v stamps ws = stampNatEqB stamps (watchVersions v ws) := by
  induction ws generalizing stamps with
  | nil =>
      cases stamps with
      | nil => rfl
      | cons x xs => rfl
  | cons a as ih =>
      cases stamps with
      | nil => rfl
      | cons x xs =>
          simp only [stampMatchAt, watchVersions, List.map_cons, stampNatEqB, ih xs]

/-- The two forms of the scan's skip test are the same Boolean, in the same
conjunct order (`&&` commutes). -/
theorem stampTest_eq (v : SchedVersions) (e : SchedEntry) (p : Propagator) :
    (!p.watches.isEmpty && stampMatchAt v e.stamps p.watches)
      = (stampNatEqB e.stamps (watchVersions v p.watches) && !p.watches.isEmpty) := by
  rw [Bool.and_comm, stampMatchAt_eq]

/-! ## 2. The fused scheduled scan -/

/-- `scanPropagatorsSchedAux` with the fused skip test. Verbatim otherwise
(same continuation logic, same early exit, same recording). -/
def scanPropagatorsSchedAuxFast (f : BranchFrame) (v : SchedVersions) :
    List (Option SchedEntry) → List Propagator →
      PruningEvent × List (Option SchedEntry)
  | seens, [] => (.stable, seens)
  | [], p :: ps =>
      match p.run (frameState f) with
      | .stable =>
          let (ev, seens') := scanPropagatorsSchedAuxFast f v [] ps
          (ev, some (freshEntry v f p .stable) :: seens')
      | .conflict c => (.conflict (if c.isEmpty then [] else [c]), [])
      | .implied l r =>
          if productive l f then
            (.implied l r.clause false false, [])
          else
            let (ev, seens') := scanPropagatorsSchedAuxFast f v [] ps
            (ev, some (freshEntry v f p (.implied l r)) :: seens')
  | some e :: seens, p :: ps =>
      if !p.watches.isEmpty && stampMatchAt v e.stamps p.watches then
        match e.result with
        | .stable =>
            let (ev, seens') := scanPropagatorsSchedAuxFast f v seens ps
            (ev, some e :: seens')
        | .conflict c => (.conflict (if c.isEmpty then [] else [c]), some e :: seens)
        | .implied l r' =>
            if productive l f then
              (.implied l r'.clause false false, some e :: seens)
            else
              let (ev, seens') := scanPropagatorsSchedAuxFast f v seens ps
              (ev, some e :: seens')
      else
        match p.run (frameState f) with
        | .stable =>
            let (ev, seens') := scanPropagatorsSchedAuxFast f v seens ps
            (ev, some (freshEntry v f p .stable) :: seens')
        | .conflict c => (.conflict (if c.isEmpty then [] else [c]), some e :: seens)
        | .implied l r' =>
            if productive l f then
              (.implied l r'.clause false false, some e :: seens)
            else
              let (ev, seens') := scanPropagatorsSchedAuxFast f v seens ps
              (ev, some (freshEntry v f p (.implied l r')) :: seens')
  | none :: seens, p :: ps =>
      match p.run (frameState f) with
      | .stable =>
          let (ev, seens') := scanPropagatorsSchedAuxFast f v seens ps
          (ev, some (freshEntry v f p .stable) :: seens')
      | .conflict c => (.conflict (if c.isEmpty then [] else [c]), none :: seens)
      | .implied l r =>
          if productive l f then
            (.implied l r.clause false false, none :: seens)
          else
            let (ev, seens') := scanPropagatorsSchedAuxFast f v seens ps
            (ev, some (freshEntry v f p (.implied l r)) :: seens')

/-- **EQUIVALENCE (fused scheduled scan core)**: the fused aux is the
reference aux for every table. No invariant is needed: the two skip tests are
equal for every entry. -/
theorem scanPropagatorsSchedAuxFast_eq (f : BranchFrame) (v : SchedVersions)
    (seens : List (Option SchedEntry)) (props : List Propagator) :
    scanPropagatorsSchedAuxFast f v seens props
      = scanPropagatorsSchedAux f v seens props := by
  induction props generalizing seens with
  | nil => cases seens <;> rfl
  | cons p ps ih =>
      cases seens with
      | nil =>
          cases hrun : p.run (frameState f) with
          | stable =>
              simp only [scanPropagatorsSchedAuxFast, scanPropagatorsSchedAux, hrun, ih]
          | conflict c =>
              simp only [scanPropagatorsSchedAuxFast, scanPropagatorsSchedAux, hrun]
          | implied l r =>
              by_cases hprod : productive l f = true
              · simp only [scanPropagatorsSchedAuxFast, scanPropagatorsSchedAux, hrun,
                  if_pos hprod]
              · simp only [scanPropagatorsSchedAuxFast, scanPropagatorsSchedAux, hrun,
                  if_neg hprod, ih]
      | cons s ss =>
          cases s with
          | none =>
              cases hrun : p.run (frameState f) with
              | stable =>
                  simp only [scanPropagatorsSchedAuxFast, scanPropagatorsSchedAux, hrun, ih]
              | conflict c =>
                  simp only [scanPropagatorsSchedAuxFast, scanPropagatorsSchedAux, hrun]
              | implied l r =>
                  by_cases hprod : productive l f = true
                  · simp only [scanPropagatorsSchedAuxFast, scanPropagatorsSchedAux, hrun,
                      if_pos hprod]
                  · simp only [scanPropagatorsSchedAuxFast, scanPropagatorsSchedAux, hrun,
                      if_neg hprod, ih]
          | some e =>
              have htest := stampTest_eq v e p
              cases hb : (!p.watches.isEmpty && stampMatchAt v e.stamps p.watches) with
              | true =>
                  have hb' : (stampNatEqB e.stamps (watchVersions v p.watches)
                        && !p.watches.isEmpty) = true := by
                    rw [← htest]; exact hb
                  cases hres : e.result with
                  | stable =>
                      simp only [scanPropagatorsSchedAuxFast, scanPropagatorsSchedAux, hb,
                        hb', if_pos, hres, ih]
                  | conflict c =>
                      simp only [scanPropagatorsSchedAuxFast, scanPropagatorsSchedAux, hb,
                        hb', if_pos, hres]
                  | implied l r =>
                      by_cases hprod : productive l f = true
                      · simp only [scanPropagatorsSchedAuxFast, scanPropagatorsSchedAux, hb,
                          hb', if_pos, hres, if_pos hprod]
                      · simp only [scanPropagatorsSchedAuxFast, scanPropagatorsSchedAux, hb,
                          hb', if_pos, hres, if_neg hprod, ih]
              | false =>
                  have hb' : (stampNatEqB e.stamps (watchVersions v p.watches)
                        && !p.watches.isEmpty) = false := by
                    rw [← htest]; exact hb
                  cases hrun : p.run (frameState f) with
                  | stable =>
                      simp only [scanPropagatorsSchedAuxFast, scanPropagatorsSchedAux, hb,
                        hb', Bool.false_eq_true, if_false, hrun, ih]
                  | conflict c =>
                      simp only [scanPropagatorsSchedAuxFast, scanPropagatorsSchedAux, hb,
                        hb', Bool.false_eq_true, if_false, hrun]
                  | implied l r =>
                      by_cases hprod : productive l f = true
                      · simp only [scanPropagatorsSchedAuxFast, scanPropagatorsSchedAux, hb,
                          hb', Bool.false_eq_true, if_false, hrun, if_pos hprod]
                      · simp only [scanPropagatorsSchedAuxFast, scanPropagatorsSchedAux, hb,
                          hb', Bool.false_eq_true, if_false, hrun, if_neg hprod, ih]

/-- The fused scheduled scan: sync, fused aux, store the table. -/
def scanPropagatorsSchedFast (f : BranchFrame) (sched : PropScheduler)
    (props : List Propagator) : PruningEvent × PropScheduler :=
  let sched' := sched.sync f
  let (ev, seen) := scanPropagatorsSchedAuxFast f sched'.versions sched'.seen props
  (ev, { sched' with seen := seen })

/-- **EQUIVALENCE (fused scheduled scan)**: the fused scan is exactly the
wired `scanPropagatorsSched` (same event, same returned scheduler). -/
theorem scanPropagatorsSchedFast_eq (f : BranchFrame) (sched : PropScheduler)
    (props : List Propagator) :
    scanPropagatorsSchedFast f sched props = scanPropagatorsSched f sched props := by
  simp only [scanPropagatorsSchedFast, scanPropagatorsSched,
    scanPropagatorsSchedAuxFast_eq]

/-! ## 3. The fused event prompt -/

/-- The scheduled event selection with the fused propagator scan. Only the
propagator scan changed; the certified DB scan and the liveness gates are the
ones of `nextPruningEventSched`. -/
def nextPruningEventFastSched (original : List Clause) (props : List Propagator)
    (sched : PropScheduler) (f : BranchFrame) (db : List Clause) :
    PruningEvent × PropScheduler :=
  match scanDatabaseFast original f db with
  | .stable =>
      if frameViewedB f then scanPropagatorsSchedFast f sched props else (.stable, sched)
  | .conflict cs => (.conflict cs, sched)
  | .implied l c learnReason fromLearned =>
      if frameLiveB f then (.implied l c learnReason fromLearned, sched) else (.stable, sched)

/-- **EQUIVALENCE (whole prompt)**: the fused prompt IS the wired
`nextPruningEventSched`, event and scheduler state. -/
theorem nextPruningEventFastSched_eq (original : List Clause) (props : List Propagator)
    (sched : PropScheduler) (f : BranchFrame) (db : List Clause) :
    nextPruningEventFastSched original props sched f db
      = nextPruningEventSched original props sched f db := by
  unfold nextPruningEventFastSched nextPruningEventSched
  rw [scanPropagatorsSchedFast_eq]
  rfl

/-- The fused prompt produces the certified event. -/
theorem nextPruningEventFastSched_fst_eq (original : List Clause)
    (props : List Propagator) (sched : PropScheduler) (f : BranchFrame)
    (db : List Clause) (hok : PropSchedulerOK props sched) (hloc : PropLocal props) :
    (nextPruningEventFastSched original props sched f db).1
      = nextPruningEvent original props f db := by
  rw [nextPruningEventFastSched_eq]
  exact nextPruningEventSched_fst_eq original props sched f db hok hloc

/-- The fused prompt keeps the scheduler invariant. This is the
`nextPruningEventSched_OK` argument (the same proof, restated here because
that theorem lives downstream in the dispatcher file, which imports this
module). -/
theorem nextPruningEventFastSched_OK (original : List Clause)
    (props : List Propagator) (sched : PropScheduler) (f : BranchFrame)
    (db : List Clause) (hok : PropSchedulerOK props sched) (hloc : PropLocal props) :
    PropSchedulerOK props (nextPruningEventFastSched original props sched f db).2 := by
  rw [nextPruningEventFastSched_eq]
  unfold nextPruningEventSched
  split
  · split
    · exact scanPropagatorsSched_OK hok hloc
    · exact hok
  · exact hok
  · split <;> exact hok

end LeanFzn.Solver.Propagation

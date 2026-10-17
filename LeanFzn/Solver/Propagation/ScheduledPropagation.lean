/-
File: LeanFzn/Solver/Propagation/ScheduledPropagation.lean

Purpose (PLAN task P1): INCREMENTAL PROPAGATOR SCHEDULING with a proved
REFINEMENT theorem. The full scan `scanPropagators` re-runs every registered
propagator at every propagation step; the scheduled scan
`scanPropagatorsSched` memorizes, per propagator, the WATCH PROJECTION of the
frame (the current domain of every slot in `p.watches`) together with the
result the run produced there, and re-uses the memorized result while the
projection is unchanged — re-running the propagator only when one of its
watched slots changed.

The equivalence is a REFINEMENT, not a weakening:

* `scanPropagatorsSched_fst_eq` — the scheduled scan produces EXACTLY the
  same `PruningEvent` as the full `scanPropagators` (same list, same order,
  same early exit), provided the memorized table is consistent
  (`PropSchedulerOK`).
* `scanPropagatorsSched_OK` — the table stays consistent across scans: a
  recording is justified by the static per-propagator locality hypothesis
  `PropLocal`, which the concrete LCG registrations discharge in
  `ScheduledFamilies.lean`.
* `nextPruningEventSched_fst_eq` — the event-selection entry point
  (`scanDatabase` unchanged, the same liveness gates) agrees with the
  certified `nextPruningEvent` under the same table consistency.

The table is keyed by the CONTENT of the watched slots (not by a version
counter), so the consistency invariant is frame-free
(`∀ g, w = watchStamp g p.watches → p.run (frameState g) = r`): it is
preserved by every frame narrowing without any bookkeeping, and only
the recording site needs the static locality hypothesis. The projection
test itself (`stampEqB`, a first-order recursion — no `zip`/`length`
intermediate lists) is on the hot path of the one-scan-per-step dispatch, so
its constant factor is part of the design, not an accident.

Dependencies: Pruning/Propagate (the scan and the propagator interface),
`LeanFzn.Semantics.ValueEquality` (sound Boolean value equality — `Value`
has no `DecidableEq`).

DAG: Pruning -> ScheduledPropagation -> ScheduledFamilies (concrete
locality) -> the certified runtime driver.
-/
import LeanFzn.Solver.Propagation.Pruning
import LeanFzn.Solver.Propagation.Propagate
import LeanFzn.Solver.Propagation.DbScanIndex
import LeanFzn.Semantics.ValueEquality
open LeanFzn.Semantics LeanFzn.Solver.Core


namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-! ## Watch projections -/

/-- The watch projection of a frame: the current domain of every watched
slot, in watch order. Only `.slot` of a watch atom is read. -/
def watchStamp (f : BranchFrame) (watches : List Atom) : List Domain :=
  watches.map fun a => (Frame.domains f).getD a.slot []

/-- Soundness of the Boolean domain equality (`valuesEqB`). -/
theorem valuesEqB_sound {xs ys : List Value} (h : valuesEqB xs ys = true) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp [valuesEqB] at h
  | cons x xs ih =>
      cases ys with
      | nil => simp [valuesEqB] at h
      | cons y ys =>
          simp only [valuesEqB, Bool.and_eq_true] at h
          rw [LeanFzn.Semantics.Evaluation.value_eqB_iff.mp h.1, ih h.2]

/-- Computable equality of watch projections (`Value` has no
`DecidableEq`; `Value.eqB`/`valuesEqB` are its sound Boolean twins).
FIRST-ORDER recursion: no `zip`/`length` intermediate lists — this test is
on the scheduled scan's hot path, and it is the reason the path is worth
taking (the pure `List` library shape allocates two lists per position). -/
def stampEqB : List Domain → List Domain → Bool
  | [], [] => true
  | x :: xs, y :: ys => valuesEqB x y && stampEqB xs ys
  | _, _ => false

theorem stampEqB_sound {xs ys : List Domain} (h : stampEqB xs ys = true) :
    xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [stampEqB]
  | cons x xs ih =>
      cases ys with
      | nil => simp [stampEqB] at h
      | cons y ys =>
          simp only [stampEqB, Bool.and_eq_true] at h
          rw [valuesEqB_sound h.1, ih h.2]

/-! ## The scheduler state -/

/-- The scheduled scan's memorized table, aligned with the propagator list:
entry `i` records the watch projection at which propagator `i` last ran
together with the result observed there. -/
structure PropScheduler where
  seen : List (Option (List Domain × PropagationResult))

/-- The empty scheduler: nothing memorized (the full scan's behaviour). -/
def PropScheduler.init (props : List Propagator) : PropScheduler :=
  { seen := props.map fun _ => none }

/-- Consistency of ONE memorized entry: an entry recorded at watch
projection `w` with result `r` by a propagator with a NONEMPTY declared
footprint reports the run's result at EVERY frame whose watch projection is
`w`. (A propagator that declares no footprint is never reused; its entries
obligation is vacuous.) -/
def EntryOK (p : Propagator) (w : List Domain) (r : PropagationResult) : Prop :=
  p.watches ≠ [] → ∀ g : BranchFrame, w = watchStamp g p.watches → p.run (frameState g) = r

/-- Consistency of a memorized table with the runs. -/
def TableOK (props : List Propagator)
    (seen : List (Option (List Domain × PropagationResult))) : Prop :=
  ∀ (j : Nat) (p : Propagator) (w : List Domain) (r : PropagationResult),
    props[j]? = some p → seen[j]? = some (some (w, r)) → EntryOK p w r

/-- Consistency of a scheduler's table. -/
def PropSchedulerOK (props : List Propagator) (sched : PropScheduler) : Prop :=
  TableOK props sched.seen

/-- Table consistency transports along equal propagator lists. -/
theorem TableOK.of_props_eq {props props' : List Propagator}
    {seen : List (Option (List Domain × PropagationResult))} (h : props' = props)
    (hok : TableOK props seen) : TableOK props' seen := by
  intro j p w r hj he
  exact hok j p w r (by simpa [h] using hj) he

/-- Scheduler consistency transports along equal propagator lists. -/
theorem PropSchedulerOK.of_props_eq {props props' : List Propagator}
    {sched : PropScheduler} (h : props' = props) (hok : PropSchedulerOK props sched) :
    PropSchedulerOK props' sched :=
  TableOK.of_props_eq h hok

/-- The empty scheduler is consistent (every entry is `none`, so its
obligations are vacuous). -/
theorem PropSchedulerOK.init (props : List Propagator) :
    PropSchedulerOK props (PropScheduler.init props) := by
  intro j p w r _ he
  simp only [PropScheduler.init, List.getElem?_map, Option.map_eq_some_iff] at he
  obtain ⟨a, _, ha⟩ := he
  exact absurd ha (by simp)

/-- The per-propagator STATIC locality hypothesis: the run depends only on
the current domains of its watched slots. This is the (honest) semantic
content the scheduling consumes; it is discharged per family for the
concrete registrations (`ScheduledFamilies.lean`). -/
def PropLocalOne (p : Propagator) : Prop :=
  ∀ f g : BranchFrame, watchStamp f p.watches = watchStamp g p.watches →
    p.run (frameState f) = p.run (frameState g)

def PropLocal (props : List Propagator) : Prop :=
  ∀ p ∈ props, p.watches ≠ [] → PropLocalOne p

theorem PropLocal.tail {p : Propagator} {ps : List Propagator}
    (h : PropLocal (p :: ps)) : PropLocal ps :=
  fun q hq => h q (List.mem_cons_of_mem _ hq)

/-- Locality transports along equal propagator lists. -/
theorem PropLocal.of_props_eq {props props' : List Propagator} (h : props' = props)
    (hloc : PropLocal props) : PropLocal props' :=
  fun q hq hne => hloc q (by simpa [h] using hq) hne

/-! ## The scheduled scan -/

/-- The scheduled propagator scan (table-aligned recursion). For each
propagator in order: if the memorized watch projection equals the current
one, re-use the memorized result (the run is skipped); otherwise run the
propagator and memorize its result when the scan continues past it. The
continuation logic (conflict report, productivity gate, early exit) is the
verbatim `scanPropagators` logic. -/
def scanPropagatorsSchedAux (f : BranchFrame) :
    List (Option (List Domain × PropagationResult)) → List Propagator →
      PruningEvent × List (Option (List Domain × PropagationResult))
  | seens, [] => (.stable, seens)
  | [], p :: ps =>
      match p.run (frameState f) with
      | .stable =>
          let (ev, seens') := scanPropagatorsSchedAux f [] ps
          (ev, some (watchStamp f p.watches, .stable) :: seens')
      | .conflict c => (.conflict (if c.isEmpty then [] else [c]), [])
      | .implied l r =>
          if productive l f then
            (.implied l r.clause true false, [])
          else
            let (ev, seens') := scanPropagatorsSchedAux f [] ps
            (ev, some (watchStamp f p.watches, .implied l r) :: seens')
  | some (w, r) :: seens, p :: ps =>
      if stampEqB w (watchStamp f p.watches) && !p.watches.isEmpty then
        match r with
        | .stable =>
            let (ev, seens') := scanPropagatorsSchedAux f seens ps
            (ev, some (w, r) :: seens')
        | .conflict c => (.conflict (if c.isEmpty then [] else [c]), some (w, r) :: seens)
        | .implied l r' =>
            if productive l f then
              (.implied l r'.clause true false, some (w, r) :: seens)
            else
              let (ev, seens') := scanPropagatorsSchedAux f seens ps
              (ev, some (w, r) :: seens')
      else
        match p.run (frameState f) with
        | .stable =>
            let (ev, seens') := scanPropagatorsSchedAux f seens ps
            (ev, some (watchStamp f p.watches, .stable) :: seens')
        | .conflict c => (.conflict (if c.isEmpty then [] else [c]), some (w, r) :: seens)
        | .implied l r' =>
            if productive l f then
              (.implied l r'.clause true false, some (w, r) :: seens)
            else
              let (ev, seens') := scanPropagatorsSchedAux f seens ps
              (ev, some (watchStamp f p.watches, .implied l r') :: seens')
  | none :: seens, p :: ps =>
      match p.run (frameState f) with
      | .stable =>
          let (ev, seens') := scanPropagatorsSchedAux f seens ps
          (ev, some (watchStamp f p.watches, .stable) :: seens')
      | .conflict c => (.conflict (if c.isEmpty then [] else [c]), none :: seens)
      | .implied l r =>
          if productive l f then
            (.implied l r.clause true false, none :: seens)
          else
            let (ev, seens') := scanPropagatorsSchedAux f seens ps
            (ev, some (watchStamp f p.watches, .implied l r) :: seens')

/-- The scheduled scan of a frame against a scheduler. -/
def scanPropagatorsSched (f : BranchFrame) (sched : PropScheduler)
    (props : List Propagator) : PruningEvent × PropScheduler :=
  let (ev, seen) := scanPropagatorsSchedAux f sched.seen props
  (ev, { seen := seen })

/-- The scheduled event selection: the DB scan is the optimised `scanDatabaseFast`
(proved equal to the certified `scanDatabase` by `scanDatabaseFast_eq`, so the
certified equivalence below is unaffected) and the liveness gates are the
certified ones; only the propagator scan is scheduled. -/
def nextPruningEventSched (original : List Clause) (props : List Propagator)
    (sched : PropScheduler) (f : BranchFrame) (db : List Clause) :
    PruningEvent × PropScheduler :=
  match scanDatabaseFast original f db with
  | .stable =>
      if frameViewedB f then scanPropagatorsSched f sched props else (.stable, sched)
  | .conflict cs => (.conflict cs, sched)
  | .implied l c learnReason fromLearned =>
      if frameLiveB f then (.implied l c learnReason fromLearned, sched) else (.stable, sched)

/-! ## Table algebra -/

/-- Locality at an entry: a memorized head entry is consistent at its own
frame. -/
theorem PropLocalOne.toEntry {p : Propagator} (h : PropLocalOne p)
    {f : BranchFrame} : EntryOK p (watchStamp f p.watches) (p.run (frameState f)) :=
  fun _ g hg => (h f g hg).symm

/-- An entry produced by a locally-sound propagator at a frame. -/
theorem EntryOK.of_local_run {p : Propagator} {f : BranchFrame} {r : PropagationResult}
    (h : p.watches ≠ [] → PropLocalOne p) (hrun : p.run (frameState f) = r) :
    EntryOK p (watchStamp f p.watches) r :=
  fun hne g hg => ((h hne f g hg).symm).trans hrun

/-- An entry observed at a frame, transported to the run's actual result. -/
theorem EntryOK.of_run_eq {p : Propagator} {f : BranchFrame} {r : PropagationResult}
    (hl : EntryOK p (watchStamp f p.watches) (p.run (frameState f)))
    (hrun : p.run (frameState f) = r) : EntryOK p (watchStamp f p.watches) r :=
  fun hne g hg => (hl hne g hg).trans hrun

/-- The empty table is consistent at any nonempty propagator list. -/
theorem TableOK.nil_cons {p : Propagator} {ps : List Propagator} :
    TableOK (p :: ps) ([] : List (Option (List Domain × PropagationResult))) :=
  fun j q w r hq he => by simp at he

/-- The tail of a consistent table is consistent. -/
theorem TableOK.tail {p : Propagator} {e : Option (List Domain × PropagationResult)}
    {ps : List Propagator} {seens : List (Option (List Domain × PropagationResult))}
    (h : TableOK (p :: ps) (e :: seens)) : TableOK ps seens := by
  intro j q w r hq he
  exact h (j + 1) q w r (by simpa using hq) (by simpa using he)

/-- The head entry of a consistent table is consistent. -/
theorem TableOK.head {p : Propagator} {w0 : List Domain} {r0 : PropagationResult}
    {ps : List Propagator} {seens : List (Option (List Domain × PropagationResult))}
    (h : TableOK (p :: ps) (some (w0, r0) :: seens)) : EntryOK p w0 r0 := by
  intro g hg
  exact h 0 p w0 r0 rfl (by simp) g hg

/-- Rebuild a consistent table with a recorded head entry. -/
theorem TableOK.cons_head {p : Propagator} {ps : List Propagator}
    {w0 : List Domain} {r0 : PropagationResult} {seens : List (Option (List Domain × PropagationResult))}
    (h0 : EntryOK p w0 r0) (htail : TableOK ps seens) :
    TableOK (p :: ps) (some (w0, r0) :: seens) := by
  intro j q w r hq he
  cases j with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hq he
      subst hq
      obtain ⟨rfl, rfl⟩ := he
      exact h0
  | succ j =>
      exact htail j q w r (by simpa using hq) (by simpa using he)

/-- Rebuild a consistent table with a vacuous head entry. -/
theorem TableOK.cons_none {p : Propagator} {ps : List Propagator}
    {seens : List (Option (List Domain × PropagationResult))}
    (htail : TableOK ps seens) : TableOK (p :: ps) (none :: seens) := by
  intro j q w r hq he
  cases j with
  | zero => simp only [List.getElem?_cons_zero] at he; cases he
  | succ j =>
      exact htail j q w r (by simpa using hq) (by simpa using he)

/-! ## Equation lemmas for the scheduled scan -/

section Equations

variable (f : BranchFrame)

theorem schedAux_nil_nil : scanPropagatorsSchedAux f [] [] = (.stable, []) := rfl

theorem schedAux_nil_stable (p : Propagator) (ps : List Propagator)
    (h : p.run (frameState f) = .stable) :
    scanPropagatorsSchedAux f [] (p :: ps)
      = ((scanPropagatorsSchedAux f [] ps).1,
         some (watchStamp f p.watches, .stable) :: (scanPropagatorsSchedAux f [] ps).2) := by
  cases hrec : scanPropagatorsSchedAux f [] ps with
  | mk ev seens' =>
      simp only [scanPropagatorsSchedAux, h, hrec]

theorem schedAux_nil_conflict (p : Propagator) (ps : List Propagator) (c : Clause)
    (h : p.run (frameState f) = .conflict c) :
    scanPropagatorsSchedAux f [] (p :: ps)
      = (.conflict (if c.isEmpty then [] else [c]), []) := by
  simp only [scanPropagatorsSchedAux, h]

theorem schedAux_nil_implied_hit (p : Propagator) (ps : List Propagator)
    (l : Literal) (r : Reason)
    (h : p.run (frameState f) = .implied l r) (hp : productive l f = true) :
    scanPropagatorsSchedAux f [] (p :: ps)
      = (.implied l r.clause true false, []) := by
  simp only [scanPropagatorsSchedAux, h, hp, if_pos]

theorem schedAux_nil_implied_miss (p : Propagator) (ps : List Propagator)
    (l : Literal) (r : Reason)
    (h : p.run (frameState f) = .implied l r) (hp : ¬ productive l f = true) :
    scanPropagatorsSchedAux f [] (p :: ps)
      = ((scanPropagatorsSchedAux f [] ps).1,
         some (watchStamp f p.watches, .implied l r) :: (scanPropagatorsSchedAux f [] ps).2) := by
  cases hrec : scanPropagatorsSchedAux f [] ps with
  | mk ev seens' =>
      simp only [scanPropagatorsSchedAux, h, hp, Bool.false_eq_true, hrec]
      rfl

theorem schedAux_some_stable (p : Propagator) (ps : List Propagator)
    (w : List Domain) (r : PropagationResult)
    (seens : List (Option (List Domain × PropagationResult)))
    (hm : (stampEqB w (watchStamp f p.watches) && !p.watches.isEmpty) = true) (hr : r = .stable) :
    scanPropagatorsSchedAux f (some (w, r) :: seens) (p :: ps)
      = ((scanPropagatorsSchedAux f seens ps).1,
         some (w, r) :: (scanPropagatorsSchedAux f seens ps).2) := by
  subst hr
  cases hrec : scanPropagatorsSchedAux f seens ps with
  | mk ev seens' =>
      simp only [scanPropagatorsSchedAux, hm, if_pos, hrec]

theorem schedAux_some_conflict (p : Propagator) (ps : List Propagator)
    (w : List Domain) (c : Clause)
    (seens : List (Option (List Domain × PropagationResult)))
    (hm : (stampEqB w (watchStamp f p.watches) && !p.watches.isEmpty) = true) :
    scanPropagatorsSchedAux f (some (w, .conflict c) :: seens) (p :: ps)
      = (.conflict (if c.isEmpty then [] else [c]), some (w, .conflict c) :: seens) := by
  simp only [scanPropagatorsSchedAux, hm, if_pos]

theorem schedAux_some_implied_hit (p : Propagator) (ps : List Propagator)
    (w : List Domain) (l : Literal) (r : Reason)
    (seens : List (Option (List Domain × PropagationResult)))
    (hm : (stampEqB w (watchStamp f p.watches) && !p.watches.isEmpty) = true) (hp : productive l f = true) :
    scanPropagatorsSchedAux f (some (w, .implied l r) :: seens) (p :: ps)
      = (.implied l r.clause true false, some (w, .implied l r) :: seens) := by
  simp only [scanPropagatorsSchedAux, hm, if_pos, hp, if_pos]

theorem schedAux_some_implied_miss (p : Propagator) (ps : List Propagator)
    (w : List Domain) (l : Literal) (r : Reason)
    (seens : List (Option (List Domain × PropagationResult)))
    (hm : (stampEqB w (watchStamp f p.watches) && !p.watches.isEmpty) = true) (hp : ¬ productive l f = true) :
    scanPropagatorsSchedAux f (some (w, .implied l r) :: seens) (p :: ps)
      = ((scanPropagatorsSchedAux f seens ps).1,
         some (w, .implied l r) :: (scanPropagatorsSchedAux f seens ps).2) := by
  cases hrec : scanPropagatorsSchedAux f seens ps with
  | mk ev seens' =>
      simp only [scanPropagatorsSchedAux, hm, if_pos, hp, Bool.false_eq_true, hrec]
      rfl

theorem schedAux_miss_stable (p : Propagator) (ps : List Propagator)
    (w : List Domain) (r : PropagationResult)
    (seens : List (Option (List Domain × PropagationResult)))
    (hm : (stampEqB w (watchStamp f p.watches) && !p.watches.isEmpty) = false)
    (h : p.run (frameState f) = .stable) :
    scanPropagatorsSchedAux f (some (w, r) :: seens) (p :: ps)
      = ((scanPropagatorsSchedAux f seens ps).1,
         some (watchStamp f p.watches, .stable) :: (scanPropagatorsSchedAux f seens ps).2) := by
  cases hrec : scanPropagatorsSchedAux f seens ps with
  | mk ev seens' =>
      simp only [scanPropagatorsSchedAux, hm, Bool.false_eq_true, h, hrec]
      rfl

theorem schedAux_miss_conflict (p : Propagator) (ps : List Propagator)
    (w : List Domain) (r : PropagationResult)
    (seens : List (Option (List Domain × PropagationResult)))
    (hm : (stampEqB w (watchStamp f p.watches) && !p.watches.isEmpty) = false) (c : Clause)
    (h : p.run (frameState f) = .conflict c) :
    scanPropagatorsSchedAux f (some (w, r) :: seens) (p :: ps)
      = (.conflict (if c.isEmpty then [] else [c]), some (w, r) :: seens) := by
  simp only [scanPropagatorsSchedAux, hm, Bool.false_eq_true, h]
  rfl

theorem schedAux_miss_implied_hit (p : Propagator) (ps : List Propagator)
    (w : List Domain) (r : PropagationResult)
    (seens : List (Option (List Domain × PropagationResult)))
    (hm : (stampEqB w (watchStamp f p.watches) && !p.watches.isEmpty) = false) (l : Literal) (r' : Reason)
    (h : p.run (frameState f) = .implied l r') (hp : productive l f = true) :
    scanPropagatorsSchedAux f (some (w, r) :: seens) (p :: ps)
      = (.implied l r'.clause true false, some (w, r) :: seens) := by
  simp only [scanPropagatorsSchedAux, hm, Bool.false_eq_true, h, hp, if_pos]
  rfl

theorem schedAux_miss_implied_miss (p : Propagator) (ps : List Propagator)
    (w : List Domain) (r : PropagationResult)
    (seens : List (Option (List Domain × PropagationResult)))
    (hm : (stampEqB w (watchStamp f p.watches) && !p.watches.isEmpty) = false) (l : Literal) (r' : Reason)
    (h : p.run (frameState f) = .implied l r') (hp : ¬ productive l f = true) :
    scanPropagatorsSchedAux f (some (w, r) :: seens) (p :: ps)
      = ((scanPropagatorsSchedAux f seens ps).1,
         some (watchStamp f p.watches, .implied l r') :: (scanPropagatorsSchedAux f seens ps).2) := by
  cases hrec : scanPropagatorsSchedAux f seens ps with
  | mk ev seens' =>
      simp only [scanPropagatorsSchedAux, hm, Bool.false_eq_true, h, hp, hrec]
      rfl

theorem schedAux_none_stable (p : Propagator) (ps : List Propagator)
    (seens : List (Option (List Domain × PropagationResult)))
    (h : p.run (frameState f) = .stable) :
    scanPropagatorsSchedAux f (none :: seens) (p :: ps)
      = ((scanPropagatorsSchedAux f seens ps).1,
         some (watchStamp f p.watches, .stable) :: (scanPropagatorsSchedAux f seens ps).2) := by
  cases hrec : scanPropagatorsSchedAux f seens ps with
  | mk ev seens' =>
      simp only [scanPropagatorsSchedAux, h, hrec]

theorem schedAux_none_conflict (p : Propagator) (ps : List Propagator)
    (seens : List (Option (List Domain × PropagationResult))) (c : Clause)
    (h : p.run (frameState f) = .conflict c) :
    scanPropagatorsSchedAux f (none :: seens) (p :: ps)
      = (.conflict (if c.isEmpty then [] else [c]), none :: seens) := by
  simp only [scanPropagatorsSchedAux, h]

theorem schedAux_none_implied_hit (p : Propagator) (ps : List Propagator)
    (seens : List (Option (List Domain × PropagationResult)))
    (l : Literal) (r : Reason)
    (h : p.run (frameState f) = .implied l r) (hp : productive l f = true) :
    scanPropagatorsSchedAux f (none :: seens) (p :: ps)
      = (.implied l r.clause true false, none :: seens) := by
  simp only [scanPropagatorsSchedAux, h, hp, if_pos]

theorem schedAux_none_implied_miss (p : Propagator) (ps : List Propagator)
    (seens : List (Option (List Domain × PropagationResult)))
    (l : Literal) (r : Reason)
    (h : p.run (frameState f) = .implied l r) (hp : ¬ productive l f = true) :
    scanPropagatorsSchedAux f (none :: seens) (p :: ps)
      = ((scanPropagatorsSchedAux f seens ps).1,
         some (watchStamp f p.watches, .implied l r) :: (scanPropagatorsSchedAux f seens ps).2) := by
  cases hrec : scanPropagatorsSchedAux f seens ps with
  | mk ev seens' =>
      simp only [scanPropagatorsSchedAux, h, hp, Bool.false_eq_true, hrec]
      rfl

end Equations

/-! ## The equivalence theorems -/

/-- **THE EQUIVALENCE (scan level)**: a consistent table makes the scheduled
scan produce EXACTLY the event of the full `scanPropagators`, and the table
returned by the scan stays consistent. -/
theorem scanPropagatorsSchedAux_spec {f : BranchFrame} :
    ∀ (ps : List Propagator) (seens : List (Option (List Domain × PropagationResult))),
      TableOK ps seens → PropLocal ps →
      (scanPropagatorsSchedAux f seens ps).1 = scanPropagators f ps ∧
      TableOK ps (scanPropagatorsSchedAux f seens ps).2 := by
  intro ps
  induction ps with
  | nil =>
      intro seens _ _
      exact ⟨by first | rfl | trivial, by assumption⟩
  | cons p ps ih =>
      intro seens hok hloc
      have hlocp : p.watches ≠ [] → PropLocalOne p := hloc p (List.mem_cons_self ..)
      cases seens with
      | nil =>
          have hoktail : TableOK ps [] := fun j q w r hq he => by simp at he
          have ih' := ih [] hoktail hloc.tail
          cases hrun : p.run (frameState f) with
          | stable =>
              rw [schedAux_nil_stable f p ps hrun, scanPropagators, hrun]
              exact ⟨ih'.1, TableOK.cons_head (EntryOK.of_local_run hlocp hrun) ih'.2⟩
          | conflict c =>
              simp only [schedAux_nil_conflict f p ps c hrun, scanPropagators, hrun]
              exact ⟨by first | rfl | trivial, TableOK.nil_cons⟩
          | implied l r =>
              by_cases hprod : productive l f = true
              · simp only [schedAux_nil_implied_hit f p ps l r hrun hprod, scanPropagators, hrun,
                  if_pos hprod]
                exact ⟨by first | rfl | trivial, TableOK.nil_cons⟩
              · simp only [schedAux_nil_implied_miss f p ps l r hrun hprod, scanPropagators, hrun,
                  if_neg hprod]
                exact ⟨ih'.1, TableOK.cons_head (EntryOK.of_local_run hlocp hrun) ih'.2⟩
      | cons e seens =>
          cases e with
          | none =>
              have hoktail : TableOK ps seens := TableOK.tail hok
              have ih' := ih seens hoktail hloc.tail
              cases hrun : p.run (frameState f) with
              | stable =>
                  simp only [schedAux_none_stable f p ps seens hrun, scanPropagators, hrun]
                  exact ⟨ih'.1, TableOK.cons_head (EntryOK.of_local_run hlocp hrun) ih'.2⟩
              | conflict c =>
                  simp only [schedAux_none_conflict f p ps seens c hrun, scanPropagators, hrun]
                  exact ⟨by first | rfl | trivial, TableOK.cons_none hoktail⟩
              | implied l r =>
                  by_cases hprod : productive l f = true
                  · simp only [schedAux_none_implied_hit f p ps seens l r hrun hprod, scanPropagators,
                      hrun, if_pos hprod]
                    exact ⟨by first | rfl | trivial, TableOK.cons_none hoktail⟩
                  · simp only [schedAux_none_implied_miss f p ps seens l r hrun hprod, scanPropagators,
                      hrun, if_neg hprod]
                    exact ⟨ih'.1, TableOK.cons_head (EntryOK.of_local_run hlocp hrun) ih'.2⟩
          | some wr =>
              obtain ⟨w, r⟩ := wr
              have hok0 : EntryOK p w r := hok 0 p w r rfl (by simp)
              have hoktail : TableOK ps seens := TableOK.tail hok
              have ih' := ih seens hoktail hloc.tail
              by_cases hmatch : (stampEqB w (watchStamp f p.watches) && !p.watches.isEmpty) = true
              · have hboth := hmatch
                simp only [Bool.and_eq_true] at hboth
                have hstamp : stampEqB w (watchStamp f p.watches) = true := hboth.1
                have hne : p.watches ≠ [] := by
                  have h2 := hboth.2
                  simpa using h2
                have hrun_eq : p.run (frameState f) = r := hok0 hne f (stampEqB_sound hstamp)
                cases r with
                | stable =>
                    simp only [schedAux_some_stable f p ps w .stable seens hmatch rfl,
                        scanPropagators, hrun_eq]
                    exact ⟨ih'.1, TableOK.cons_head hok0 ih'.2⟩
                | conflict c =>
                    simp only [schedAux_some_conflict f p ps w c seens hmatch, scanPropagators, hrun_eq]
                    exact ⟨by first | rfl | trivial, TableOK.cons_head hok0 hoktail⟩
                | implied l r' =>
                    by_cases hprod : productive l f = true
                    · simp only [schedAux_some_implied_hit f p ps w l r' seens hmatch hprod,
                        scanPropagators, hrun_eq, if_pos hprod]
                      exact ⟨by first | rfl | trivial, TableOK.cons_head hok0 hoktail⟩
                    · simp only [schedAux_some_implied_miss f p ps w l r' seens hmatch hprod,
                        scanPropagators, hrun_eq, if_neg hprod]
                      exact ⟨ih'.1, TableOK.cons_head hok0 ih'.2⟩
              · have hmatch' : (stampEqB w (watchStamp f p.watches) && !p.watches.isEmpty) = false := by
                  cases h : (stampEqB w (watchStamp f p.watches) && !p.watches.isEmpty) with
                  | false => rfl
                  | true => exact absurd h hmatch
                cases hrun : p.run (frameState f) with
                | stable =>
                    simp only [schedAux_miss_stable f p ps w r seens hmatch' hrun, scanPropagators, hrun]
                    exact ⟨ih'.1, TableOK.cons_head (EntryOK.of_local_run hlocp hrun) ih'.2⟩
                | conflict c =>
                    simp only [schedAux_miss_conflict f p ps w r seens hmatch' c hrun, scanPropagators,
                        hrun]
                    exact ⟨by first | rfl | trivial, TableOK.cons_head hok0 hoktail⟩
                | implied l r' =>
                    by_cases hprod : productive l f = true
                    · simp only [schedAux_miss_implied_hit f p ps w r seens hmatch' l r' hrun hprod,
                        scanPropagators, hrun, if_pos hprod]
                      exact ⟨by first | rfl | trivial, TableOK.cons_head hok0 hoktail⟩
                    · simp only [schedAux_miss_implied_miss f p ps w r seens hmatch' l r' hrun hprod,
                        scanPropagators, hrun, if_neg hprod]
                      exact ⟨ih'.1, TableOK.cons_head (EntryOK.of_local_run hlocp hrun) ih'.2⟩

/-- **THE EQUIVALENCE (public scan form)**: consistency of the scheduler's
table makes the scheduled scan return exactly the full scan's event. -/
theorem scanPropagatorsSched_fst_eq {f : BranchFrame} {sched : PropScheduler}
    {props : List Propagator} (hok : PropSchedulerOK props sched)
    (hloc : PropLocal props) :
    (scanPropagatorsSched f sched props).1 = scanPropagators f props := by
  simp only [scanPropagatorsSched]
  exact (scanPropagatorsSchedAux_spec props sched.seen hok hloc).1

/-- The table returned by a scheduled scan of a locally-sound propagator
list stays consistent. -/
theorem scanPropagatorsSched_OK {f : BranchFrame} {sched : PropScheduler}
    {props : List Propagator} (hok : PropSchedulerOK props sched)
    (hloc : PropLocal props) : PropSchedulerOK props (scanPropagatorsSched f sched props).2 := by
  simp only [scanPropagatorsSched, PropSchedulerOK]
  exact (scanPropagatorsSchedAux_spec props sched.seen hok hloc).2

/-- **THE EQUIVALENCE (event-selection form)**: the scheduled event selection
agrees with the certified `nextPruningEvent` (database scan — through
`scanDatabaseFast_eq` — and liveness gates unchanged). -/
theorem nextPruningEventSched_fst_eq (original : List Clause) (props : List Propagator)
    (sched : PropScheduler) (f : BranchFrame) (db : List Clause)
    (hok : PropSchedulerOK props sched) (hloc : PropLocal props) :
    (nextPruningEventSched original props sched f db).1
      = nextPruningEvent original props f db := by
  rw [nextPruningEventSched, scanDatabaseFast_eq]
  cases hdb : scanDatabase original f db with
  | stable =>
      simp only [nextPruningEvent, hdb]
      split
      · exact scanPropagatorsSched_fst_eq hok hloc
      · rfl
  | conflict cs => simp only [nextPruningEvent, hdb]
  | implied l c lr fl =>
      simp only [nextPruningEvent, hdb]
      split <;> rfl

end LeanFzn.Solver.Propagation

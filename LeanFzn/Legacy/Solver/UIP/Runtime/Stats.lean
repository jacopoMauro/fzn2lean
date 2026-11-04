/-
File: LeanFzn/Solver/UIP/Runtime/Stats.lean

Purpose (PLAN §3 K0, rewired by K0b): expose the scheduled certified
driver's non-semantic work counters (`SchedulerConfig.stats`) beside its
verdict, so the IO driver can print real `--stats` engine counters without
changing any certified definition.

The scheduled DB-producing driver `runSchedDb` (`LcgPhaseSchedDb.lean`) runs
exactly the scheduled recursion of `runSched` and returns the terminal
`SchedulerConfig`.  `solve_schedDbStats` is the verdict together with that
terminal record's `stats`; its first component is proved equal to
`solve_sched` by `solve_schedDbStats_fst` (which rests only on the
`runSchedDb_fst` verdict agreement).  Because the driver's kernel step is
`phaseNextSched` (the scheduled dispatcher over `promptOf`), the stats route
and the default satisfaction CLI exercise the scheduled propagation path.

The pre-K0b route read the counters off the unscheduled reference driver
(`runSupportedPhaseDb`, whose kernel step is `phaseNext`); that route is kept
unchanged in `LcgPhaseRunDb.lean` for its seeded/DB consumers, but it is no
longer used here.

Counters are accumulated by the `step…` functions into `cfg.stats`; the
terminal record is returned as-is.  No logical definition changes and no
search step is affected (`stats` is observation only).

DAG: LcgPhaseSchedDb + LcgPhaseRunDb -> this file -> Integration.LcgHeur /
Integration.Annot / Integration.CertifiedSolve.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgPhaseRunDb
import LeanFzn.Legacy.Solver.UIP.Runtime.ScheduledDb
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.UIP
open LeanFzn LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.C3b
open LeanFzn.Solver.UIP.LcgPhaseSchedDb

/-- **THE INSTRUMENTED SCHEDULED DRIVER**: the scheduled verdict together with
the terminal work counters of the identical scheduled run.  The counters are
observations only; the verdict component is the certified driver's (see
`solve_schedStats_fst`). -/
def solve_schedStats {leaf : Assignment → Bool} (orig : List Domain)
    (original : List Clause) (props : List Propagator)
    (hent : LearnedEntailed leaf original) (sched : PropScheduler)
    (hloc : PropLocal props) (hok : PropSchedulerOK props sched)
    (hgate : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → FrameNonempty cfg)
    (prio : List Nat := []) (actBump : Bool := false) :
    DriverResult leaf × SearchStats :=
  solve_schedDbStats orig original props hent sched hloc hok hgate prio actBump

/-- **THE INSTRUMENTED ENTRY DECIDES EXACTLY THE CERTIFIED DRIVER**: the first
component of `solve_schedStats` is `solve_sched`. -/
theorem solve_schedStats_fst {leaf : Assignment → Bool} (orig : List Domain)
    (original : List Clause) (props : List Propagator)
    (hent : LearnedEntailed leaf original) (sched : PropScheduler)
    (hloc : PropLocal props) (hok : PropSchedulerOK props sched)
    (hgate : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → FrameNonempty cfg)
    (prio : List Nat := []) (actBump : Bool := false) :
    (solve_schedStats orig original props hent sched hloc hok hgate prio actBump).1
      = solve_sched orig original props hent sched hloc hok hgate prio actBump :=
  solve_schedDbStats_fst orig original props hent sched hloc hok hgate prio actBump

/-- **THE TERMINAL COUNTER RECORD**: the second component is the stats field
of the terminal configuration of the scheduled DB-producing run. -/
theorem solve_schedStats_snd {leaf : Assignment → Bool} (orig : List Domain)
    (original : List Clause) (props : List Propagator)
    (hent : LearnedEntailed leaf original) (sched : PropScheduler)
    (hloc : PropLocal props) (hok : PropSchedulerOK props sched)
    (hgate : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → FrameNonempty cfg)
    (prio : List Nat := []) (actBump : Bool := false) :
    (solve_schedStats orig original props hent sched hloc hok hgate prio actBump).2
      = (runSchedDb
          (LeanFzn.Solver.UIP.LcgPhaseKernel.supportedPhaseKernel orig original props hgate)
          hloc (SchedulerConfig.init orig original props prio actBump) sched
          (SupportedReach.init hent) hok).2.stats :=
  solve_schedDbStats_snd orig original props hent sched hloc hok hgate prio actBump

end LeanFzn.Solver.UIP

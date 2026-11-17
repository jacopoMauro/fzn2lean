/-
File: LeanFzn/Integration/Report/T8.lean

Purpose:
  A2.5 streaming correspondence for the two real stats-aware optimization
  routes.  The seed twin is `LeanFzn.Core.optimizeStreamCoreSeed_eq` and is
  not restated here.

  The frozen stats statement in `tmp/design/p0-contracts.md` omits the
  `IO.monoMsNow`/`--stats` instrumentation that the actual entry performs.
  Equality of `IO` actions cannot discard an arbitrary effect (`monoMsNow` is
  an opaque primitive), so the statement below keeps that instrumentation on
  the right-hand side and replaces only the search loop by its pure-twin
  correspondence.  The emitted callback sequence and the returned `OptRun`
  are those of `optLoopCoreStatsWith`, in order.

Dependencies:
  Report.Proofs (pure report layer and source-result bridges).

DAG:
  Report.Basic -> Report.Codec -> Report.Proofs -> Report.T8.
-/
import LeanFzn.Integration.Report.Proofs

namespace LeanFzn.Integration.Report

open LeanFzn LeanFzn.Semantics LeanFzn.Compiler
open LeanFzn.Semantics.Globals
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Integration
open LeanFzn.Engine
open LeanFzn.Core

/-! ## IO associativity helpers

The development files keep private copies of these small monad identities;
they are pure `IO` bookkeeping and introduce no computational content. -/

private theorem t8_est_bind_assoc {ε σ α β γ : Type} (x : EST ε σ α)
    (f : α → EST ε σ β) (g : β → EST ε σ γ) :
    (x >>= f) >>= g = x >>= fun y => f y >>= g := by
  funext s
  dsimp only [Bind.bind, EST.bind]
  cases h : x s <;> rfl

private theorem t8_io_bind_assoc {α β γ : Type} (x : IO α) (f : α → IO β)
    (g : β → IO γ) :
    (x >>= f) >>= g = x >>= fun y => f y >>= g :=
  t8_est_bind_assoc x f g

private theorem t8_io_pure_bind {α β : Type} (a : α) (f : α → IO β) :
    (pure a >>= f) = f a := rfl

/-! ## The stats streaming loop -/

/-- The stats-aware streaming loop emits exactly the source stores of the
    pure run's improving solutions, in order, and returns that pure run with
    the accumulated counters.  The domain-conversion branch is handled by the
    caller; this lemma is the branch-agnostic core. -/
private theorem optimizeStreamCoreStatsLoop_emitted_eq
    (o : SearchConfig) (p : CompiledProblem DomConstraint) (spec : ObjectiveSpec)
    (emit : Store → IO Unit) (prev : Option (List Value)) (bo : Option Int) :
    optimizeStreamCoreStatsLoop o coreFuel p spec (fun a => p.toStore a) emit prev bo =
      (let run := (optLoopCoreStatsWith o coreFuel p spec prev bo).1
       let st := (optLoopCoreStatsWith o coreFuel p spec prev bo).2
       emitAll emit (run.sols.map fun s => p.toStore s.1) >>= fun _ =>
         pure (run, run.sols.map fun s => p.toStore s.1, st)) := by
  let run := (optLoopCoreStatsWith o coreFuel p spec prev bo).1
  let st := (optLoopCoreStatsWith o coreFuel p spec prev bo).2
  have hfst : run = optLoopWith (coreSolver o coreFuel) p spec prev bo :=
    optLoopCoreStatsWith_fst o coreFuel p spec (meas p spec bo) prev bo rfl
  rw [optimizeStreamCoreStatsLoop_eq]
  rw [optimizeStreamLoopWith_emit]
  rw [optLoopEmitWith_eq (S := coreSolver o coreFuel) p spec
    (fun a => p.toStore a) _ prev bo rfl]
  simp only [streamSpec]
  simp only [t8_io_bind_assoc, t8_io_pure_bind]
  rw [← hfst]

/-! ## T8 — stats route -/

/-- **T8 (stats route), instrumentation-preserving form.**  The real
    `optimizeStreamCoreStats` entry has a `convertDomains` fast branch and a
    timing/`--stats` wrapper.  This theorem is the frozen correspondence with
    that wrapper preserved and the prepared/fallback branch split made
    explicit, so it is true of the actual implementation rather than an
    idealized twin. -/
theorem optimizeStreamCoreStats_emitted_eq (o : SearchConfig) (m : Model)
    (emit : Store → IO Unit) :
    optimizeStreamCoreStats o m emit =
      (do
        let t0 ← IO.monoMsNow
        match compileModelOpt m with
        | .error e => pure (.error e)
        | .ok (p, spec) =>
            let t1 ← IO.monoMsNow
            let run := (optLoopCoreStatsWith o coreFuel p spec none none).1
            let st := (optLoopCoreStatsWith o coreFuel p spec none none).2
            emitAll emit (run.sols.map fun s => p.toStore s.1) >>= fun _ => do
              let t2 ← IO.monoMsNow
              if o.stats then
                IO.eprintln s!"leanfzn: timing: compile_ms={t1 - t0} search_ms={t2 - t1}"
              pure (.ok (⟨p, run, run.sols.map fun s => p.toStore s.1⟩, st))) := by
  unfold optimizeStreamCoreStats
  cases hc : compileModelOpt m with
  | error e => rfl
  | ok u =>
      obtain ⟨p, spec⟩ := u
      simp only []
      split
      · rename_i doms hdoms
        rw [optimizeStreamCoreStatsLoopPrepared_eq o coreFuel p spec doms hdoms
          (fun a => p.toStore a) emit none none]
        rw [optimizeStreamCoreStatsLoop_emitted_eq o p spec emit none none]
        simp only [t8_io_bind_assoc, t8_io_pure_bind]
      · rw [optimizeStreamCoreStatsLoop_emitted_eq o p spec emit none none]
        simp only [t8_io_bind_assoc, t8_io_pure_bind]

/-! ## T8 — LNS route -/

/-- The actual counters returned by the streaming LNS route.  The frozen
    statement existentially quantifies the counters because it does not name
    them; this is the concrete witness used below. -/
private def lnsStreamStats (o : SearchConfig) (m : Model) : EngineStats :=
  match compileModelOpt m with
  | .error _ => {}
  | .ok (p, spec) =>
      match lnsStart o p spec none with
      | (none, st) =>
          st.add (optLoopCoreStatsWith o coreFuel p spec none none).2
      | (some (best, vbest), st) =>
          st.add (optLoopCoreStatsWith o coreFuel p spec (some best) (some vbest)).2

/-- **T8 (LNS route).**  The real `optimizeStreamCoreLns` emits the checked
    start candidate first and then exactly the source stores of the pure
    `lnsSearch` run's improving sequence, and returns that run.  The counters
    are the actual accumulated `EngineStats`; they are existentially
    quantified only to match the frozen statement, which does not name them. -/
theorem optimizeStreamCoreLns_emitted_eq (o : SearchConfig) (m : Model)
    (emit : Store → IO Unit) :
    ∃ st : EngineStats,
      optimizeStreamCoreLns o m emit =
        (match compileModelOpt m with
         | .error e => pure (.error e)
         | .ok (p, spec) =>
             let run := (lnsSearch o p spec none).1
             emitAll emit (run.sols.map fun s => p.toStore s.1) >>= fun _ =>
               pure (.ok (⟨p, run, run.sols.map fun s => p.toStore s.1⟩, st))) := by
  refine ⟨lnsStreamStats o m, ?_⟩
  unfold optimizeStreamCoreLns lnsStreamStats
  cases hc : compileModelOpt m with
  | error e => rfl
  | ok u =>
      obtain ⟨p, spec⟩ := u
      simp only []
      cases hs : lnsStart o p spec none with
      | mk start st0 =>
          cases start with
          | none =>
              unfold lnsSearch
              rw [hs]
              simp only []
              rw [optimizeStreamCoreStatsLoop_emitted_eq o p spec emit none none]
              simp only [t8_io_bind_assoc, t8_io_pure_bind]
          | some w =>
              obtain ⟨best, vbest⟩ := w
              unfold lnsSearch
              rw [hs]
              simp only []
              rw [optimizeStreamCoreStatsLoop_emitted_eq o p spec emit
                (some best) (some vbest)]
              simp only [emitAll, t8_io_bind_assoc, t8_io_pure_bind, List.map_cons]

end LeanFzn.Integration.Report

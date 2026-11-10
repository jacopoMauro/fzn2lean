/-
Purpose: Common search enums and configuration record, independent of either engine.
Dependencies: Std
DAG: Common configuration -> parsing / engine adapters.
-/
import Std

namespace LeanFzn.Integration

/-! ## Option enums (PLAN §2.2) -/

/-- Slot-selection strategy (`--var`). -/
inductive VarStrategy where
  /-- Minimum cardinality over all slots: today's default (S1). -/
  | minc
  /-- Follow the model's `int_search`/`seq_search` annotations (F2). -/
  | annot
  /-- Conflict-driven activity (F7). -/
  | act
  /-- Domain-size weighted degree (F7). -/
  | domwdeg
  /-- Conflict-weighted degree: minimise `size / (weight + 1)` where the
  weight counts conflict-explanation occurrences (P5.2). -/
  | wdeg
  /-- Objective slot first; the legacy `--heur-obj-prio` (implemented). -/
  | obj
  deriving Repr, DecidableEq, Inhabited

/-- Value-presentation strategy (`--val`). -/
inductive ValStrategy where
  /-- Ascending order (F3). -/
  | min
  /-- Descending order (F3). -/
  | max
  /-- Median-first then alternating (F3). -/
  | median
  /-- Binary interval split `x ≤ m` versus `x > m` (P2). -/
  | split
  /-- Today's static activity order. -/
  | act
  /-- Annotation-directed order (F2). -/
  | annot
  /-- Previous-round incumbent value first (F3). -/
  | incumbent
  deriving Repr, DecidableEq, Inhabited

/-- Branch-and-bound bound strategy (`--opt`). -/
inductive OptStrategy where
  /-- Today's streamed strict-improvement descent. -/
  | linear
  /-- Keep the learned clause database between bound rounds (F4). -/
  | seeded
  /-- Binary search on the objective bound (F4). -/
  | bisect
  deriving Repr, DecidableEq, Inhabited

/-- Driver restart schedule (`--restart`). -/
inductive RestartStrategy where
  /-- No restarts: today's complete run. -/
  | none
  /-- Luby restart sequence (F5). -/
  | luby
  /-- Geometric restart sequence (F5). -/
  | geom
  deriving Repr, DecidableEq, Inhabited

/-- Witness-checked primal heuristic (`--primal`). -/
inductive PrimalStrategy where
  /-- No primal heuristic. -/
  | none
  /-- Random/annotated dive with witness checking (F6). -/
  | dive
  /-- Large-neighbourhood search around the incumbent (F6). -/
  | lns
  deriving Repr, DecidableEq, Inhabited

/-- Propagation scheduling (`--prop`). -/
inductive PropStrategy where
  /-- Today's scheduled dispatch. -/
  | auto
  /-- Queue scheduling (E1). -/
  | queue
  /-- Stamp scheduling (E1). -/
  | stamp
  deriving Repr, DecidableEq, Inhabited

/-- Root presolve (`--presolve`). -/
inductive PresolveStrategy where
  /-- No presolve. -/
  | none
  /-- Root fixpoint sweep (E2). -/
  | root
  /-- Certified duplicate-constraint canonicalisation (P7.1). -/
  | dedup
  deriving Repr, DecidableEq, Inhabited

/-- Search engine (`--engine`).  `core` is the default (N14); `kernel` is
    the list-based certified engine, kept for the options Core does not
    implement and as Core's `gaveUp` fallback. -/
inductive EngineKind where
  /-- The certified list-based kernel route. -/
  | kernel
  /-- The array-based mutable Core engine (the default since N14). -/
  | core
  deriving Repr, DecidableEq, Inhabited

/-! ## The configuration record -/

/-- PLAN §2.2 search configuration. The three legacy `HeurOpts` toggles are
    kept as named fields so old invocations stay exact aliases; every other
    field defaults to today's complete behaviour.

    Unimplemented values are rejected by `checkImplemented` in the CLI. The
    pure entry points map only the implemented fields (`toHeurOpts`), so any
    configuration that reaches them still runs a certified entry. -/
structure SearchConfig where
  /-- Search engine.  Core is the public engine. The kernel tag is retained for explicit
      legacy development APIs; the public parser rejects it. -/
  engine : EngineKind := .core
  var : VarStrategy := .minc
  val : ValStrategy := .act
  opt : OptStrategy := .linear
  restart : RestartStrategy := .none
  /-- Restart base budget in steps (F5). -/
  restartBase : Nat := 100
  /-- Whether the restart schedule was chosen explicitly, either by
      `--restart` or by a preset.  The linear driver's after-incumbent Luby
      policy only fills an otherwise unset schedule. -/
  restartExplicit : Bool := false
  primal : PrimalStrategy := .none
  prop : PropStrategy := .auto
  presolve : PresolveStrategy := .none
  /-- Total wall budget in milliseconds; `none` is a complete run. -/
  timeLimit : Option Nat := none
  /-- Per-round conflict budget for the Core loop (`none` is unlimited).
      This is a diagnostic measurement cap, not a wall-clock limit: a run
      that reaches it exits 4 with cause "conflict limit reached". -/
  conflictLimit : Option Nat := none
  /-- Opt-in parallel portfolio (`--threads=N`, 1..8), for linear
      optimization and satisfaction models.  `1` keeps the ordinary
      single-threaded driver; `N > 1` runs the built-in independent-worker
      portfolio described in `Integration/Public/Driver`. -/
  threads : Nat := 1
  /-- Nominal step budget of each primal (dive/LNS) slice, in nominal
      milliseconds; `Primal.primalStepsPerMs` converts it to kernel steps
      (F6).  It is not a wall-clock promise. -/
  primalTime : Nat := 1000
  /-- Raw `CFG:MS,...` portfolio string (F5). -/
  portfolio : Option String := none
  /-- Seed for randomized options (F5/F6). -/
  seed : Option Nat := none
  /-- Print driver counters to stderr. -/
  stats : Bool := false
  /-- Legacy `--heur-obj-prio`: objective slot first. -/
  objPrio : Bool := false
  /-- Legacy `--heur-obj-bias`: objective-biased value presentation. -/
  objBias : Bool := false
  /-- Legacy `--heur-act`: conflict-driven activity bumps. -/
  actBump : Bool := false
  deriving Repr, DecidableEq, Inhabited


/-- Restart policy for one optimization round.  Before the first incumbent
the configured schedule is used; afterwards the complete linear driver fills
the default `--restart=none` with Luby.  An explicit `--restart` (including
`none`) or a preset schedule is honoured unchanged. -/
def roundConfig {α : Type} (o : SearchConfig) (prev : Option α) : SearchConfig :=
  if prev.isSome && !o.restartExplicit && o.restart == .none then
    { o with restart := .luby }
  else o

end LeanFzn.Integration

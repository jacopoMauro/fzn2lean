/-
Purpose: Search presets and engine compatibility validation.
Dependencies: LeanFzn.Integration.Config.Types
DAG: Common configuration -> parsing / engine adapters.
-/
import LeanFzn.Integration.Config.Types

namespace LeanFzn.Integration

/-! ## Presets (frozen in F1) -/

/-- A named preset bundle (`--strategy`). -/
inductive Preset where
  | default
  | annot
  | optFast
  | restarts
  | lns
  | auto
  deriving Repr, DecidableEq, Inhabited

/-- Resolve a preset name. -/
def Preset.ofName : String → Option Preset
  | "default" => some .default
  | "annot" => some .annot
  | "opt-fast" => some .optFast
  | "restarts" => some .restarts
  | "lns" => some .lns
  | "auto" => some .auto
  | _ => none

/-- The frozen preset contents. `auto` is feature-selected at run time (F9),
    so it has no static configuration. -/
def Preset.toConfig : Preset → Option SearchConfig
  | .default => some {}
  | .annot => some { var := .annot, val := .annot }
  | .optFast => some { var := .annot, val := .incumbent, opt := .seeded }
  | .restarts => some
      { var := .annot, val := .incumbent, opt := .seeded, restart := .luby }
  | .lns => some
      { var := .annot, val := .incumbent, opt := .seeded, primal := .lns }
  | .auto => none

/-! ## Implementation gate -/

/-- The option subset implemented by the array-based Core engine.  The Core
    loop honours `--var=minc|annot|act|domwdeg`, every integer/Boolean value
    presentation in `--val=act|min|max|median|annot|incumbent` (the incumbent
    route seeds the saved phases from the previous round under the linear
    driver), the complete linear driver and the seeded driver (which carries
    the learned clause database across objective-bound rounds).  Every other
    value is refused rather than silently degraded to a different policy in
    Core (the kernel route keeps its full option surface). -/
def SearchConfig.checkCoreImplemented (c : SearchConfig) : Except String Unit := do
  if c.var == .obj then
    throw "option '--var=obj' is not supported by '--engine=core' yet"
  if c.val == .incumbent && c.opt == .seeded then
    throw "option '--val=incumbent' is not supported by '--engine=core --opt=seeded' yet (the seeded entry has no phase seed)"
  if c.opt == .bisect then
    throw "option '--opt=bisect' is not supported by '--engine=core' yet (only '--opt=linear|seeded' is wired)"
  if c.primal != .none then
    throw "option '--primal' is not supported by '--engine=core' yet"
  if c.portfolio.isSome then
    throw "option '--portfolio' is not supported by '--engine=core' yet"
  if c.timeLimit.isSome then
    -- Core is a complete engine: a wall budget cannot stop it mid-search, so
    -- accepting the flag would silently weaken the requested budget.
    throw "option '--time-limit' is not supported by '--engine=core' yet"
  if c.seed.isSome then
    throw "option '--seed' is not supported by '--engine=core' yet"
  if c.presolve != .none then
    throw "option '--presolve' is not supported by '--engine=core' yet"
  if c.objPrio || c.objBias || c.actBump then
    throw "the legacy '--heur-*' toggles are not supported by '--engine=core' yet"

/-- Reject configuration values whose implementation has not landed. This is
    the only place that decides whether a flag has an effect; the CLI calls it
    before running, so no accepted option is silently ignored.

    `checkImplementedBase` is the portfolio-entry check: it validates every
    non-portfolio field but deliberately does not recurse into a nested
    `--portfolio`.  `checkImplemented` adds the outer portfolio constraints. -/
def SearchConfig.checkImplementedBase (c : SearchConfig) : Except String Unit := do
  match c.var with
  | .minc => pure ()
  | .obj => pure ()
  | .annot => pure ()
  | .act | .domwdeg =>
      if c.engine == .core then pure ()
      else
        throw "option '--var=act|domwdeg' is not implemented yet (F7 conflict-driven variable selection)"
  match c.val with
  | .act => pure ()
  | .annot => pure ()
  | .min => pure ()
  | .max => pure ()
  | .median => pure ()
  | .incumbent => pure ()
  match c.opt with
  | .linear => pure ()
  | .seeded =>
      if c.timeLimit.isSome then
        throw "option '--time-limit' with '--opt=seeded' is not implemented yet (timed seeded loop; F4)"
      else pure ()
  | .bisect =>
      if c.timeLimit.isSome then
        throw "option '--time-limit' with '--opt=bisect' is not implemented yet (the F4 bisection route has no timed recursion)"
      else pure ()
  match c.restart with
  | .none => pure ()
  | .luby => pure ()
  | .geom => pure ()
  -- F6: the primal/restart conflict is checked before the generic
  -- restart/opt rule so the primal-specific message wins (design §1.3).
  if c.primal != .none && c.restart != .none then
    throw "option '--primal=dive|lns' cannot be combined with '--restart=luby|geom' (the F5 restart driver owns the budget)"
  if c.primal != .none && c.portfolio.isSome then
    throw "option '--primal=dive|lns' cannot be combined with '--portfolio' (per-entry primal heuristics are not implemented)"
  if c.restart != .none && c.opt != .seeded && c.engine != .core then
    throw "option '--restart=luby|geom' requires '--opt=seeded' (the F5 restart driver is seeded)"
  if c.restart == .none && c.restartBase != 100 then
    throw "option '--restart-base' requires '--restart=luby|geom'"
  if c.restart != .none && c.restartBase == 0 then
    throw "option '--restart-base' must be positive (it is a step budget)"
  if c.primal == .none && c.primalTime != 1000 then
    throw "option '--primal-time' requires '--primal=dive|lns'"
  if c.primal != .none && c.primalTime == 0 then
    throw "option '--primal-time' must be positive (it is a step budget)"
  if c.primal != .none && c.opt == .linear && c.timeLimit.isSome then
    throw "option '--primal=dive|lns' with '--opt=linear' cannot be combined with '--time-limit' until the timed branch-and-bound adapter is proved (F6)"
  if c.primal != .none && c.opt == .bisect then
    throw "option '--primal=dive|lns' cannot be combined with '--opt=bisect' (the F4 bisection driver has no initial-bound adapter)"
  if c.primal != .none && c.opt == .seeded then
    throw "option '--primal=dive|lns' with '--opt=seeded' is not implemented yet (F6.1 wires the linear branch-and-bound only)"
  match c.primal with
  | .none => pure ()
  | .dive => pure ()
  | .lns =>
      throw "option '--primal=lns' is not implemented yet (F6.2 LNS driver)"
  match c.prop with
  | .auto => pure ()
  | .queue =>
      throw "option '--prop=queue' is not implemented yet (E1 propagation scheduling)"
  | .stamp =>
      throw "option '--prop=stamp' is not implemented yet (E1 propagation scheduling)"
  match c.presolve with
  | .none => pure ()
  | .root =>
      throw "option '--presolve=root' is not implemented yet (E2 root presolve)"
  if c.seed.isSome then
    throw "option '--seed' is not implemented yet (F5/F6 randomized strategies)"
  if (c.var == .annot || c.val != .act) && c.objBias then
    throw "option '--heur-obj-bias' cannot be combined with '--var=annot' or a non-act '--val': the annotation/presentation route does not implement the objective-biased presentation"
  if c.opt == .seeded && c.objBias then
    throw "option '--heur-obj-bias' cannot be combined with '--opt=seeded': the seeded presentation is static (first-round activity order)"
  if c.engine == .core then
    c.checkCoreImplemented


end LeanFzn.Integration

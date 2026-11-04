/-
Purpose: CLI and portfolio parsing and the complete implementation gate.
Dependencies: LeanFzn.Integration.Config.Validate
DAG: Common configuration -> parsing / engine adapters.
-/
import LeanFzn.Integration.Config.Validate

namespace LeanFzn.Integration

/-! ## Flag parsing -/

/-- The value of `--flag=value`, if `arg` has exactly that shape. -/
private def flagValue? (arg flag : String) : Option String :=
  let head := flag ++ "="
  if arg.startsWith head then
    some ((arg.drop head.length).toString)
  else
    none

private def parseNatValue (flag value : String) : Except String Nat :=
  match value.toNat? with
  | some n => .ok n
  | none => .error s!"invalid value '{value}' for {flag}: expected a natural number"

private def parseEngineValue (value : String) : Except String EngineKind :=
  match value with
  | "kernel" => .ok .kernel
  | "core" => .ok .core
  | _ => .error s!"invalid value '{value}' for --engine: expected kernel or core"

private def parseVarValue (value : String) : Except String VarStrategy :=
  match value with
  | "minc" => .ok .minc
  | "annot" => .ok .annot
  | "act" => .ok .act
  | "domwdeg" => .ok .domwdeg
  | "obj" => .ok .obj
  | _ => .error s!"invalid value '{value}' for --var: expected minc, annot, act, domwdeg or obj"

private def parseValValue (value : String) : Except String ValStrategy :=
  match value with
  | "min" => .ok .min
  | "max" => .ok .max
  | "median" => .ok .median
  | "act" => .ok .act
  | "annot" => .ok .annot
  | "incumbent" => .ok .incumbent
  | _ => .error s!"invalid value '{value}' for --val: expected min, max, median, act, annot or incumbent"

private def parseOptValue (value : String) : Except String OptStrategy :=
  match value with
  | "linear" => .ok .linear
  | "seeded" => .ok .seeded
  | "bisect" => .ok .bisect
  | _ => .error s!"invalid value '{value}' for --opt: expected linear, seeded or bisect"

private def parseRestartValue (value : String) : Except String RestartStrategy :=
  match value with
  | "none" => .ok .none
  | "luby" => .ok .luby
  | "geom" => .ok .geom
  | _ => .error s!"invalid value '{value}' for --restart: expected none, luby or geom"

private def parsePrimalValue (value : String) : Except String PrimalStrategy :=
  match value with
  | "none" => .ok .none
  | "dive" => .ok .dive
  | "lns" => .ok .lns
  | _ => .error s!"invalid value '{value}' for --primal: expected none, dive or lns"

private def parsePropValue (value : String) : Except String PropStrategy :=
  match value with
  | "auto" => .ok .auto
  | "queue" => .ok .queue
  | "stamp" => .ok .stamp
  | _ => .error s!"invalid value '{value}' for --prop: expected auto, queue or stamp"

private def parsePresolveValue (value : String) : Except String PresolveStrategy :=
  match value with
  | "none" => .ok .none
  | "root" => .ok .root
  | _ => .error s!"invalid value '{value}' for --presolve: expected none or root"

private def markSeen (seen : List String) (flag : String) : Except String (List String) :=
  if seen.contains flag then
    .error s!"option '{flag}' given more than once"
  else
    .ok (flag :: seen)

/-- Apply one flag. `none` means "not a recognised flag" (the caller decides
    whether it is a source argument or an unknown option). -/
private def applyFlag (seen : List String) (c : SearchConfig) (arg : String) :
    Except String (Option (SearchConfig × List String)) := do
  if let some value := flagValue? arg "--engine" then
    let seen ← markSeen seen "--engine"
    let engine ← parseEngineValue value
    return some ({ c with engine := engine }, seen)
  else if let some value := flagValue? arg "--var" then
    let seen ← markSeen seen "--var"
    let var ← parseVarValue value
    return some ({ c with var := var }, seen)
  else if let some value := flagValue? arg "--val" then
    let seen ← markSeen seen "--val"
    let val ← parseValValue value
    return some ({ c with val := val }, seen)
  else if let some value := flagValue? arg "--opt" then
    let seen ← markSeen seen "--opt"
    let opt ← parseOptValue value
    return some ({ c with opt := opt }, seen)
  else if let some value := flagValue? arg "--restart" then
    let seen ← markSeen seen "--restart"
    let restart ← parseRestartValue value
    return some ({ c with restart := restart }, seen)
  else if let some value := flagValue? arg "--restart-base" then
    let seen ← markSeen seen "--restart-base"
    let restartBase ← parseNatValue "--restart-base" value
    return some ({ c with restartBase := restartBase }, seen)
  else if let some value := flagValue? arg "--primal" then
    let seen ← markSeen seen "--primal"
    let primal ← parsePrimalValue value
    return some ({ c with primal := primal }, seen)
  else if let some value := flagValue? arg "--primal-time" then
    let seen ← markSeen seen "--primal-time"
    let primalTime ← parseNatValue "--primal-time" value
    return some ({ c with primalTime := primalTime }, seen)
  else if let some value := flagValue? arg "--prop" then
    let seen ← markSeen seen "--prop"
    let prop ← parsePropValue value
    return some ({ c with prop := prop }, seen)
  else if let some value := flagValue? arg "--presolve" then
    let seen ← markSeen seen "--presolve"
    let presolve ← parsePresolveValue value
    return some ({ c with presolve := presolve }, seen)
  else if let some value := flagValue? arg "--time-limit" then
    let seen ← markSeen seen "--time-limit"
    let timeLimit ← parseNatValue "--time-limit" value
    return some ({ c with timeLimit := some timeLimit }, seen)
  else if let some value := flagValue? arg "--portfolio" then
    let seen ← markSeen seen "--portfolio"
    if value.isEmpty then
      throw "option '--portfolio' requires a nonempty CFG:MS,... list"
    return some ({ c with portfolio := some value }, seen)
  else if let some value := flagValue? arg "--seed" then
    let seen ← markSeen seen "--seed"
    let seed ← parseNatValue "--seed" value
    return some ({ c with seed := some seed }, seen)
  else if arg == "--stats" then
    return some ({ c with stats := true }, seen)
  else if arg == "--certified" then
    -- accepted legacy alias; the command is certified with or without it
    return some (c, seen)
  else if arg == "--heur-obj-prio" then
    return some ({ c with objPrio := true }, seen)
  else if arg == "--heur-obj-bias" then
    return some ({ c with objBias := true }, seen)
  else if arg == "--heur-act" then
    return some ({ c with actBump := true }, seen)
  else if arg == "--strategy" then
    throw "option '--strategy' requires a value (--strategy=NAME)"
  else if (flagValue? arg "--strategy").isSome then
    -- applied by the preset pass; explicit flags after it still override
    return some (c, seen)
  else if ["--engine", "--var", "--val", "--opt", "--restart", "--restart-base", "--primal",
           "--primal-time", "--prop", "--presolve", "--time-limit",
           "--portfolio", "--seed"].contains arg then
    throw s!"option '{arg}' requires a value ('{arg}=...')"
  else
    return none

/-- Locate the single `--strategy=NAME` occurrence before the main pass. -/
private def findStrategy (args : List String) : Except String (Option String) :=
  let rec go (found : Option String) : List String → Except String (Option String)
    | [] => .ok found
    | arg :: rest =>
        match flagValue? arg "--strategy" with
        | some name =>
            match found with
            | some _ => .error "option '--strategy' given more than once"
            | none => go (some name) rest
        | none => go found rest
  go none args

/-- A parsed `--portfolio` value: the probe segments (configuration and
nominal millisecond slice) followed by the final complete configuration. -/
structure PortfolioSpec where
  probes : List (SearchConfig × Nat)
  final : SearchConfig
  deriving Repr

/-- Parse a configuration word list with no source arguments.  Presets are
applied first, explicit flags override them, and the non-portfolio fields are
checked by `checkImplementedBase`. -/
private def parseConfigWords (args : List String) (defaultEngine : EngineKind)
    (allowLegacyRouting : Bool := true) :
    Except String (SearchConfig × List String) := do
  let presetName ← findStrategy args
  let base : SearchConfig ←
    match presetName with
    | none => pure {}
    | some name =>
        match Preset.ofName name with
        | none =>
            throw s!"unknown strategy preset '{name}' (expected default, annot, opt-fast, restarts, lns or auto)"
        | some preset =>
            match preset.toConfig with
            | some c => pure c
            | none => throw "strategy preset 'auto' is not implemented yet (F9 strategy guide)"
  let base := { base with engine := defaultEngine }
  let rec go (seen : List String) (c : SearchConfig) :
      List String → Except String (SearchConfig × List String)
    | [] => .ok (c, [])
    | arg :: rest => do
        match ← applyFlag seen c arg with
        | some (c', seen') => go seen' c' rest
        | none =>
            if arg.startsWith "--" then
              .error s!"unknown option '{arg}'"
            else
              match go seen c rest with
              | .ok (c', src) => .ok (c', arg :: src)
              | .error e => .error e
  let (c, src) ← go [] base args
  -- N14: Core is the default engine.  Without an explicit `--engine`, a
  -- configuration Core does not implement resolves to the kernel, so every
  -- kernel-only option keeps its pre-N14 meaning and error messages.
  let explicitEngine := args.any (fun a => (flagValue? a "--engine").isSome)
  let c :=
    if !allowLegacyRouting || explicitEngine || c.checkImplementedBase matches .ok _ then c
    else { c with engine := .kernel }
  -- S7: a Core run with no `--var`, `--val`, preset or portfolio uses the
  -- best measured Core configuration `act/min`.  The record default stays
  -- `minc/act`, so the kernel route and the presets keep their meaning.
  let explicitVarVal := args.any (fun a =>
    (flagValue? a "--var").isSome || (flagValue? a "--val").isSome)
  let c :=
    if c.engine == .core && !explicitVarVal && presetName.isNone && c.portfolio.isNone then
      { c with var := .act, val := .min }
    else c
  match c.checkImplementedBase with
  | .error e =>
      match presetName with
      | some name => .error s!"strategy preset '{name}': {e}"
      | none => .error e
  | .ok _ => return (c, src)

/-- One `CFG[:MS]` portfolio entry.  The configuration part is a stand-alone
preset/flag expression; a bare first word that names a preset (for example
`opt-fast`) is the same as `--strategy=opt-fast`; `MS` is the nominal slice in
milliseconds. -/
private def parsePortfolioEntry (entry : String) :
    Except String (SearchConfig × Option Nat) := do
  let (cfg, ms?) ←
    match entry.splitOn ":" with
    | [cfg] => pure (cfg, none)
    | [cfg, ms] => pure (cfg, some ms)
    | _ => throw s!"invalid portfolio entry '{entry}': expected CFG[:MS]"
  let words := (cfg.splitOn " ").filter (fun w => !w.isEmpty)
  let words ←
    match words with
    | w :: rest =>
        if w.startsWith "--" || (Preset.ofName w).isNone then
          pure words
        else pure (s!"--strategy={w}" :: rest)
    | [] => pure []
  -- The F5 portfolio driver runs every entry on the kernel.
  let (c, src) ← parseConfigWords words .kernel
  if c.engine == .core then
    throw s!"portfolio entry '{cfg}' cannot set '--engine=core'; the portfolio driver runs on the kernel"
  if !src.isEmpty then
    throw s!"invalid portfolio configuration '{cfg}': source arguments are not allowed"
  if c.portfolio.isSome then
    throw "option '--portfolio' cannot be nested"
  if c.primal != .none then
    throw s!"portfolio entry '{cfg}' cannot set '--primal'; per-entry primal heuristics are not implemented yet (F6)"
  if c.restart != .none then
    throw s!"portfolio entry '{cfg}' cannot set '--restart'; the portfolio driver is a sequence of seeded configurations"
  if c.timeLimit.isSome then
    throw s!"portfolio entry '{cfg}' cannot set '--time-limit'; slices are step budgets, not wall-clock limits"
  if c.stats then
    throw s!"portfolio entry '{cfg}' cannot set '--stats'; it is an outer driver flag"
  if c.opt != .seeded then
    throw s!"portfolio entry '{cfg}' must select '--opt=seeded' (for example the opt-fast preset)"
  let ms ←
    match ms? with
    | none => pure none
    | some value =>
        match value.toNat? with
        | some n => pure (some n)
        | none =>
            throw s!"invalid slice '{value}' in portfolio entry '{entry}': expected milliseconds"
  pure (c, ms)

/-- Parse `--portfolio=CFG[:MS],...,FINAL[:MS]`.  Every entry is a
self-contained configuration.  Non-final entries need a positive millisecond
slice; the final entry is the unlimited complete segment (omit `:MS` or write
`:0`). -/
def parsePortfolio (value : String) : Except String PortfolioSpec := do
  let rec go : List String → List (SearchConfig × Nat) →
      Except String PortfolioSpec
    | [], _ => throw "option '--portfolio' requires at least one entry"
    | [last], probes => do
        let (c, ms?) ← parsePortfolioEntry last
        match ms? with
        | none => pure ⟨probes.reverse, c⟩
        | some 0 => pure ⟨probes.reverse, c⟩
        | some _ =>
            throw "the last portfolio entry is the unlimited complete segment: omit ':MS' or use ':0'"
    | entry :: rest, probes => do
        let (c, ms?) ← parsePortfolioEntry entry
        let ms ←
          match ms? with
          | some n => pure n
          | none =>
              throw s!"portfolio entry '{entry}' needs a positive ':MS' slice"
        if ms == 0 then
          throw s!"portfolio entry '{entry}' needs a positive ':MS' slice"
        go rest ((c, ms) :: probes)
  let spec ← go (value.splitOn ",") []
  match spec.probes.find? (fun p => p.1.val != spec.final.val) with
  | some _ =>
      throw "portfolio probe entries share the final entry's value presentation: give every entry the same '--val'"
  | none => pure spec

/-- The full implementation gate: the base checks plus the outer portfolio
constraints and syntax.  The CLI calls this before loading the model, so a
malformed or ignored flag is a usage error. -/
def SearchConfig.checkImplemented (c : SearchConfig) : Except String Unit := do
  c.checkImplementedBase
  match c.portfolio with
  | none => pure ()
  | some value =>
      if c.opt != .seeded then
        throw "option '--portfolio' requires '--opt=seeded' (the F5 portfolio driver is seeded)"
      if c.restart != .none then
        throw "option '--portfolio' cannot be combined with '--restart'"
      if c.timeLimit.isSome then
        throw "option '--portfolio' cannot be combined with '--time-limit': slices are step budgets, not wall-clock limits"
      if c.var != .minc || c.val != .act || c.objPrio || c.objBias || c.actBump then
        throw "option '--portfolio' entries are self-contained: put '--var', '--val' and '--heur-*' inside each CFG entry"
      let _ ← parsePortfolio value
      pure ()

/-- Parse the `solve` flags into a configuration and the remaining source
    arguments. Presets are applied first, explicit flags override them, and
    the result is checked by `checkImplemented`. -/
def parseSolveFlags (args : List String) : Except String (SearchConfig × List String) := do
  let (c, src) ← parseConfigWords args .core
  let presetName ← findStrategy args
  match c.checkImplemented with
  | .error e =>
      match presetName with
      | some name => .error s!"strategy preset '{name}': {e}"
      | none => .error e
  | .ok _ => return (c, src)


/-- Production Core-only parsing: kernel-only options are errors, never routing requests. -/
def parseCoreSolveFlags (args : List String) : Except String (SearchConfig × List String) := do
  let (c, src) ← parseConfigWords args .core false
  if c.engine != .core then
    throw "the list-based kernel is isolated in LeanFzn/Legacy and is unavailable in the public CLI"
  c.checkCoreImplemented
  c.checkImplemented
  pure (c, src)

end LeanFzn.Integration

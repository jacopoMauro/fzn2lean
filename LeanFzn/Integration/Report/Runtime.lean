/-
File: LeanFzn/Integration/Report/Runtime.lean

Purpose:
  Runtime side of the frozen `jsonl-v1` report: the output mode, the sink
  state (handshake/ids/failure only), and the text/JSON event I/O used by the
  driver.  It contains no proofs and imports only `Report.Codec` plus core IO.

Dependencies:
  Report.Codec (pure events, classifiers, model metadata and canonical text).

DAG:
  Report.Basic -> Report.Codec -> Report.Runtime -> Public.Driver -> Cli.Main.
  This module must never import Report.Proofs or any solver implementation
  beyond what the codec already re-exports.

Notes:
  The sink keeps no solution text: only the started flag, the next/last ids,
  the emitted count and the failure flag.  A failed checked emission is never
  followed by a success terminal; the driver consults `failed`.
-/
import LeanFzn.Integration.Report.Codec

namespace LeanFzn.Integration.Report

open Lean LeanFzn LeanFzn.Semantics LeanFzn.Integration

/-- Output selection.  `text` is the default FlatZinc text stream; `jsonlV1`
    is the frozen `--report=jsonl-v1` protocol. -/
inductive ReportMode where
  | text
  | jsonlV1
  deriving DecidableEq, Repr

/-- Sink bookkeeping.  No historical solution text is retained. -/
structure ReportSinkState where
  /-- The JSONL handshake has been written. -/
  started : Bool := false
  /-- Next 1-based solution id. -/
  nextId : Nat := 1
  /-- Last successfully emitted solution id. -/
  lastId : Option Nat := none
  /-- Number of successfully emitted solutions. -/
  emitted : Nat := 0
  /-- A checked emission or a write failed. -/
  failed : Bool := false
  deriving Inhabited

/-- The driver's report sink.  One sink is shared by all workers of a route. -/
structure ReportSink where
  mode : ReportMode
  state : IO.Ref ReportSinkState

namespace ReportSink

/-- Create an empty sink for the selected mode. -/
def new (mode : ReportMode) : IO ReportSink := do
  return { mode := mode, state := ← IO.mkRef ({} : ReportSinkState) }

/-- Record a sink failure without changing the mode or the last id. -/
def markFailed (s : ReportSink) : IO Unit :=
  s.state.modify fun st => { st with failed := true }

/-- Write one protocol record.  `Json.compress` is the trusted printer; the
    record is flushed before the next one is constructed. -/
private def writeEvent (e : Event) : IO Unit := do
  IO.println (Json.compress (Event.toJson e))
  (← IO.getStdout).flush

/-- Write the handshake exactly once in JSONL mode.  Text mode is a no-op. -/
def start (s : ReportSink) : IO Unit := do
  if s.mode == .jsonlV1 then
    let st ← s.state.get
    if !st.started then
      writeEvent .handshake
      s.state.set { st with started := true }

/-- Emit the parsed-model metadata (JSONL only), after validation and before
    any solution. -/
def model (s : ReportSink) (m : Model) : IO Unit := do
  if s.mode == .jsonlV1 then
    try
      writeEvent (.model (modelInfo m))
    catch _ =>
      s.markFailed

/-- Emit one checked solution.  The store must cover every declared variable;
    an optimization store must also carry its objective value.  Any failure
    marks the sink failed, emits nothing and returns `false`. -/
def solution (s : ReportSink) (m : Model) (store : Store) : IO Bool := do
  try
    let prior ← s.state.get
    if prior.failed then
      return false
    let pairs := certifiedEntryPairs m store
    if pairs.length != m.variables.length then
      s.markFailed
      return false
    let objective? : Option (Option Int) :=
      match m.solve with
      | .satisfy _ => some none
      | .minimize _ _ | .maximize _ _ => (m.solve.objective store).map some
    match objective? with
    | none =>
        s.markFailed
        return false
    | some objective =>
        let st ← s.state.get
        let id := st.nextId
        match s.mode with
        | .text =>
            IO.println (renderSolutionText m store)
            (← IO.getStdout).flush
        | .jsonlV1 =>
            writeEvent (.solution id pairs objective)
        s.state.set { st with
          nextId := id + 1
          lastId := some id
          emitted := st.emitted + 1 }
        return true
  catch _ =>
    s.markFailed
    return false

/-- Emit the terminal record.  In text mode only UNSAT/optimal print a marker
    (each line of `renderTerminalText`).  `optimal` requires the last solution
    id; a missing id is a report-internal failure and emits nothing. -/
def terminal (s : ReportSink) (kind : TerminalKind) (last : Option Nat)
    (reason : Option String) : IO Unit := do
  if kind == .optimal && last.isNone then
    s.markFailed
  else
    match s.mode with
    | .text =>
        for line in renderTerminalText kind do
          IO.println line
        (← IO.getStdout).flush
    | .jsonlV1 =>
        writeEvent (.terminal kind last reason)

/-- Emit a typed early error.  Text mode keeps stdout empty (the driver keeps
    its existing stderr diagnostic); JSONL writes the error record. -/
def error (s : ReportSink) (kind : ErrorKind) (message : String) : IO Unit := do
  match s.mode with
  | .text => pure ()
  | .jsonlV1 => writeEvent (.error kind message)

/-- Emit the terminal record and return its exit code.  Drivers end a run
    with this, so the process status is always `kind.exitCode` and never a
    separately written literal. -/
def finishTerminal (s : ReportSink) (kind : TerminalKind) (last : Option Nat)
    (reason : Option String) : IO UInt32 := do
  s.terminal kind last reason
  return kind.exitCode

/-- Emit a typed error and return its exit code `kind.exitCode`. -/
def finishError (s : ReportSink) (kind : ErrorKind) (message : String) : IO UInt32 := do
  s.error kind message
  return kind.exitCode

/-- Whether a checked emission or a write failed. -/
def failed (s : ReportSink) : IO Bool := do
  return (← s.state.get).failed

/-- Last successfully emitted solution id. -/
def lastId (s : ReportSink) : IO (Option Nat) := do
  return (← s.state.get).lastId

/-- Number of successfully emitted solutions. -/
def emitted (s : ReportSink) : IO Nat := do
  return (← s.state.get).emitted

end ReportSink

end LeanFzn.Integration.Report

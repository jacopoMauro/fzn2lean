/-
File: LeanFzn/Integration/Report/Codec.lean

Purpose:
  Structured report events and their pure `Lean.Data.Json` encoding for the
  frozen `jsonl-v1` protocol (specification/solver_protocol.md §3).  Solver
  integers and objective values are canonical decimal strings; ids, protocol
  version and exit codes are JSON numbers.

Dependencies:
  - Report.Basic: classification, terminal kinds, model metadata, error kinds.
  - Lean.Data.Json: Lean core's JSON values.  The printer/parser and byte
    output are trusted; this module only builds the value tree.

DAG:
  Report.Basic -> Report.Codec -> Report.Proofs; the runtime driver may import
  this module, but nothing in Integration/Public may import Report.Proofs.
-/
import LeanFzn.Integration.Report.Basic
import Lean.Data.Json

namespace LeanFzn.Integration.Report
open Lean

/-- The protocol tag of a terminal kind (solver_protocol.md §3.4). -/
def TerminalKind.tag : TerminalKind → String
  | .sat => "sat"
  | .unsat => "unsat"
  | .optimal => "optimal"
  | .incomplete => "incomplete"
  | .unsupported => "unsupported"
  | .error => "error"

/-- The protocol tag of an error kind (solver_protocol.md §3.5).  The tag is
    finer than the exit code: `io`/`model_parse`/`internal` all exit 2. -/
def ErrorKind.tag : ErrorKind → String
  | .usage => "usage"
  | .fileIO => "io"
  | .modelParse => "model_parse"
  | .unsupportedScope => "unsupported"
  | .compileReject => "compile"
  | .reportInternal => "internal"

/-- The protocol tag of a solve mode (solver_protocol.md §3.2). -/
def SolveMode.tag : SolveMode → String
  | .satisfy => "satisfy"
  | .minimize => "minimize"
  | .maximize => "maximize"

/-- One protocol record. -/
inductive Event where
  | handshake
  | model (info : ModelInfo)
  | solution (id : Nat) (entries : List (String × String)) (objective : Option Int)
  | terminal (kind : TerminalKind) (lastSolution : Option Nat) (reason : Option String)
  | error (kind : ErrorKind) (message : String)
  deriving Repr

namespace Event

/-- An optional object member: absent, not `null`, when there is no value. -/
def optField (key : String) : Option Json → List (String × Json)
  | none => []
  | some v => [(key, v)]

/-- The ordered members of a protocol record.  The member order is the
    protocol's presentation order; readers ignore it. -/
def fields : Event → List (String × Json)
  | .handshake =>
      [("event", .str "handshake"),
       ("protocol", .str "leanfzn-report"),
       ("version", .num (1 : Nat))]
  | .model info =>
      [("event", .str "model"), ("mode", .str info.mode.tag)] ++
        (match info.mode with
         | .satisfy => []
         | .minimize | .maximize =>
             [("objective",
               match info.objective with
               | some name => .str name
               | none => .null)]) ++
        [("outputs", .arr (info.outputs.map Json.str).toArray)]
  | .solution id entries objective =>
      [("event", .str "solution"),
       ("id", .num id),
       ("entries", .arr (entries.map fun p =>
         Json.mkObj [("name", .str p.1), ("text", .str p.2)]).toArray)] ++
        optField "objective" (objective.map fun i => .str (toString i))
  | .terminal kind last reason =>
      [("event", .str "terminal"),
       ("kind", .str kind.tag),
       ("exit", .num kind.exitCode.toNat)] ++
        optField "solution" (last.map fun n => .num n) ++
        optField "reason" (reason.map fun s => .str s)
  | .error kind message =>
      [("event", .str "error"),
       ("kind", .str kind.tag),
       ("exit", .num kind.exitCode.toNat),
       ("message", .str message)]

end Event

/-- The pure JSON value of one protocol record.  Records are printed with
    `Json.compress` by the trusted printer; this function never concatenates
    strings to build JSON. -/
def Event.toJson (e : Event) : Json :=
  Json.mkObj e.fields

end LeanFzn.Integration.Report

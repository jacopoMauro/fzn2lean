/-
File: LeanFzn/Integration/Report/Basic.lean

Purpose:
  Pure report layer for the certification boundary: terminal classification of
  the actual certified source results, the frozen exit-code and text-marker
  tables, the truth predicates stated on the source semantics, the model
  metadata derived from the parsed AST, and the canonical solution text.

Dependencies:
  - Public.Solve: the certified satisfaction entry and its `Result`.
  - Optimization.Basic: `OptRun`, the compiled optimization problem and `Store`.
  - Emit.Basic: canonical declaration rendering and the status markers.

DAG:
  certified source results -> Report.Basic -> Report.Codec -> Report.Proofs
  Runtime report construction must not import Report.Proofs.
-/
import LeanFzn.Integration.Public.Solve
import LeanFzn.Integration.Optimization.Basic
import LeanFzn.Integration.Emit.Basic

namespace LeanFzn.Integration.Report
open LeanFzn LeanFzn.Semantics LeanFzn.Compiler
open LeanFzn.Semantics.Globals
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Integration

/-! ## Terminal kinds -/

/-- The terminal outcomes of the frozen protocol table.  `sat`/`optimal` are
    positive answers, `unsat` is a certified refutation, `incomplete`,
    `unsupported` and `error` make no proof claim. -/
inductive TerminalKind where
  | sat | unsat | optimal | incomplete | unsupported | error
  deriving DecidableEq, Repr

/-- CLI exit code of a terminal kind (specification/solver_protocol.md §4):
    satisfaction/optimality 0, unsatisfiability 1, error 2, unsupported 3,
    unknown/incomplete 4. -/
def TerminalKind.exitCode : TerminalKind → UInt32
  | .sat => 0
  | .unsat => 1
  | .optimal => 0
  | .incomplete => 4
  | .unsupported => 3
  | .error => 2

/-- The text-mode proof marker printed for a terminal kind.  Only a certified
    UNSAT or a proved optimum prints a proof marker. -/
def TerminalKind.textMarker? : TerminalKind → Option String
  | .unsat => some unsatMarker
  | .optimal => some optimumMarker
  | _ => none

/-- The proof marker of a terminal kind, if any.  The terminal text renderer
    and the protocol use the same table. -/
def TerminalKind.marker? : TerminalKind → Option String :=
  TerminalKind.textMarker?

/-- Whether the terminal kind claims a certified result.  Exactly UNSAT and
    optimal do. -/
def TerminalKind.hasProofClaim : TerminalKind → Bool
  | .unsat => true
  | .optimal => true
  | _ => false

/-- The text lines printed after the last solution for a terminal kind.
    `sat`'s solution text already ends with `----------`, so it prints no
    additional line; incomplete/unsupported/error print no proof marker. -/
def renderTerminalText : TerminalKind → List String
  | .unsat => [unsatMarker]
  | .optimal => [optimumMarker]
  | _ => []

/-! ## Satisfaction classification -/

/-- The report classification of the certified satisfaction entry. -/
inductive SatisfactionClass where
  | sat (store : Store)
  | unsat
  | unsupported (reason : String)
  | unknown (reason : String)
  -- no `deriving Repr`: `Store` is a function type and has no `Repr` instance.

/-- Classify the actual single-worker satisfaction result.  No search outcome
    is reinterpreted: the constructor is the source result's constructor. -/
def classifySatisfaction : LeanFzn.Core.Result → SatisfactionClass
  | .sat store => .sat store
  | .unsat => .unsat
  | .unsupported reason => .unsupported reason
  | .unknown reason => .unknown reason

/-- The terminal kind of a satisfaction classification. -/
def SatisfactionClass.kind : SatisfactionClass → TerminalKind
  | .sat _ => .sat
  | .unsat => .unsat
  | .unsupported _ => .unsupported
  | .unknown _ => .incomplete

/-- The CLI exit code of a satisfaction classification. -/
def SatisfactionClass.exitCode : SatisfactionClass → UInt32
  | c => c.kind.exitCode

/-! ## Optimization classification -/

/-- The report classification of a certified branch-and-bound run. -/
inductive OptimizationClass where
  | optimal (last : List Value × Int)
  | unsat
  | incomplete
  deriving Repr

/-- `if !run.complete then incomplete else match run.sols.getLast? with
    | some s => optimal s | none => unsat`. -/
def classifyOptimization (run : OptRun) : OptimizationClass :=
  if !run.complete then .incomplete
  else
    match run.sols.getLast? with
    | some s => .optimal s
    | none => .unsat

/-- The terminal kind of an optimization classification. -/
def OptimizationClass.kind : OptimizationClass → TerminalKind
  | .optimal _ => .optimal
  | .unsat => .unsat
  | .incomplete => .incomplete

/-- The CLI exit code of an optimization classification. -/
def OptimizationClass.exitCode : OptimizationClass → UInt32
  | c => c.kind.exitCode

/-! ## Truth predicates -/

/-- Truth is stated on the source semantics, not by agreement with the
classifier: `sat` needs `Satisfies`, `unsat` needs absence of a
parameter-honest satisfying store, and every non-answer is `True`. -/
def SatisfactionClass.Truthful (m : Model) : SatisfactionClass → Prop
  | .sat store => Satisfies fullSig fullInterp m store
  | .unsat => ¬ ∃ store, Satisfies fullSig fullInterp m store ∧
      LeanFzn.Semantics.ParamHonest m store
  | .unsupported _ => True
  | .unknown _ => True

/-- `optimal s` carries the source solution `p.toStore s.1`; `unsat` carries
    the absence of a parameter-honest satisfying store; `incomplete` makes no
    claim. -/
def OptimizationClass.Truthful (m : Model) (p : CompiledProblem DomConstraint) :
    OptimizationClass → Prop
  | .optimal s => IsSolution fullSig fullInterp m (p.toStore s.1)
  | .unsat => ¬ ∃ store, Satisfies fullSig fullInterp m store ∧
      LeanFzn.Semantics.ParamHonest m store
  | .incomplete => True

/-! ## Model metadata -/

/-- The parsed solve item's mode. -/
inductive SolveMode where
  | satisfy | minimize | maximize
  deriving DecidableEq, Repr

/-- Metadata of a successfully loaded model (protocol §3.2).  `objective` is
    the objective variable name only when the objective expression is a bare
    identifier; it is `none` for satisfaction models and for compound
    objectives. -/
structure ModelInfo where
  mode : SolveMode
  objective : Option String
  outputs : List String
  deriving Repr

/-- The annotation list of a variable declaration. -/
private def varDeclAnns : VarDeclItem → List Annotation
  | .basic _ _ anns _ | .array _ _ anns _ => anns

/-- An annotation marks a declared variable for output when its name is
    `output_var` or `output_array`, in identifier or call form.  Annotation
    arguments are never inspected. -/
private def isOutputAnnotation : Annotation → Bool
  | .ident x => x.name == "output_var" || x.name == "output_array"
  | .call x _ => x.name == "output_var" || x.name == "output_array"

/-- Build the protocol metadata from the parsed AST: the solve mode, the bare
    identifier objective (if any), and the `output_var`/`output_array`
    annotated variable names in declaration order without duplicates. -/
def modelInfo (m : Model) : ModelInfo :=
  let mode : SolveMode :=
    match m.solve with
    | .satisfy _ => .satisfy
    | .minimize _ _ => .minimize
    | .maximize _ _ => .maximize
  let objective : Option String :=
    match m.solve with
    | .satisfy _ => none
    | .minimize _ obj => match obj with
        | .ident x => some x.name
        | .lit _ => none
    | .maximize _ obj => match obj with
        | .ident x => some x.name
        | .lit _ => none
  let outputs : List String :=
    (m.variables.filterMap fun d =>
      if (varDeclAnns d).any isOutputAnnotation then some d.name.name else none).eraseDups
  ⟨mode, objective, outputs⟩

/-! ## Error kinds -/

/-- Protocol error kinds (specification/solver_protocol.md §3.5). -/
inductive ErrorKind where
  | usage | fileIO | modelParse | unsupportedScope | compileReject | reportInternal
  deriving DecidableEq, Repr

/-- CLI exit code of an error kind: usage, I/O, model parse and internal
    failures are 2; unsupported scope and compiler/domain rejections are 3. -/
def ErrorKind.exitCode : ErrorKind → UInt32
  | .usage => 2
  | .fileIO => 2
  | .modelParse => 2
  | .unsupportedScope => 3
  | .compileReject => 3
  | .reportInternal => 2

/-! ## Canonical solution text -/

/-- One protocol solution entry per declared variable, in declaration order:
    the declaration name paired with the exact canonical assignment line the
    text driver prints.  A missing store lookup contributes no entry. -/
def certifiedEntryPairs (m : Model) (store : Store) : List (String × String) :=
  m.variables.filterMap fun d =>
    (store d.name).map fun v => (d.name.name, emitDeclEntry d v)

/-- Run-time gate for the emitter round trip: every declared variable has a
    name printable as one solution identifier token.  The driver refuses a
    model that fails it before searching (`outputNamesPrintableB_sound`). -/
def outputNamesPrintableB (m : Model) : Bool :=
  m.variables.all fun d => LeanFzn.Parser.Lexer.printableSolutionNameB d.name.name

/-- The canonical text of one solution: the declaration lines in order, then
    the FlatZinc solution separator.  This is the text-mode solution block the
    protocol's `text` members repeat. -/
def renderSolutionText (m : Model) (store : Store) : String :=
  let entries := (certifiedEntryPairs m store).map Prod.snd
  "\n".intercalate entries ++ (if entries.isEmpty then "" else "\n") ++ solutionSeparator

end LeanFzn.Integration.Report

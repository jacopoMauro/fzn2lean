/-
Purpose: The pure source-model gate every verdict-producing public route runs
  first: admission, well-formedness, and printable output names are decided
  once, and the resulting `GatedModel` carries the proofs the verdict theorems
  consume.
Dependencies: Semantics.Admission (the published fragment contract), the
  runtime checker's fast well-formedness twin with its proof, and the report
  emitter's printable-name gate.
DAG: admission + checker gate proof + report names -> this gate -> every
  public solve/optimize/seed/LNS/phased/portfolio entry and the CLI driver.

The gate is the single place a raw `Model` is allowed to cross into the
verdict-producing API.  Its check order and error classes are those the CLI
driver used before the gate was proved: model checks run admission first
(exit 3, unsupported scope), then well-formedness (exit 2, model parse), then
printable output names (exit 3).  `GatedModel.wf` and `GatedModel.admitted`
are proofs, so no solve function re-tests them.

The well-formedness fact is carried as the checker's *fast* predicate
(`Checker.wellFormedFastB m = true`) rather than the declarative `WellFormed`:
that is exactly what the gate evaluates, and the equivalence
`Checker.wellFormedFastB_iff` (a theorem of `Checker.Proofs.Check`, above this
module) turns it into `WellFormed` wherever a verdict theorem needs it.  This
keeps the gate below the report proofs, so the public verdict modules can
import it without a cycle.
-/
import LeanFzn.Semantics.Admission
import LeanFzn.Checker.Runtime.Check
import LeanFzn.Parser.SolutionRender

namespace LeanFzn.Core
open LeanFzn LeanFzn.Semantics
open LeanFzn.Checker.Solution LeanFzn.Parser.Lexer
open LeanFzn.Semantics.Globals (fullSig fullInterp)

/-- A source model that passed the gate, packaged with the proofs every
verdict theorem needs.  There is no way to build one except through `gate`,
so a raw `Model` cannot reach a verdict without the checks. -/
structure GatedModel where
  /-- The raw source model. -/
  model : Model
  /-- Source admission: every constraint meets the published contract. -/
  admitted : LeanFzn.Semantics.Admission.Admitted model
  /-- The model passed the checker's fast well-formedness gate. -/
  wfFast : LeanFzn.Checker.wellFormedFastB model = true
  /-- Every declared variable name is printable as one solution identifier. -/
  printables : (model.variables.all fun d => LeanFzn.Parser.Lexer.printableSolutionNameB d.name.name) = true

/-- Why the gate refused a model.  The three kinds keep the CLI's exit
classes: `notAdmitted` and `unprintableName` are unsupported scope (3), and
`notWellFormed` is a model-parse failure (2). -/
inductive GateError where
  | /-- A constraint is outside the admitted FlatZinc fragment; the carried
    string is `Admission.firstFailure`. -/
    notAdmitted (reason : String)
  | /-- The model is not well-formed. -/
    notWellFormed
  | /-- A variable name cannot be printed as a solution identifier. -/
    unprintableName

/-- The gate's verdict class, one per `GateError`, so the CLI exit code is a
function of the gate's answer and cannot drift from it.  `notAdmitted` and
`unprintableName` are unsupported inputs (exit 3); `notWellFormed` is a model
parse failure (exit 2). -/
inductive GateClass where
  | /-- A constraint is outside the admitted fragment (exit 3). -/
    unsupported
  | /-- The model is not well-formed (exit 2). -/
    notWellFormed
  deriving DecidableEq, Repr

def GateError.classOf : GateError → GateClass
  | .notAdmitted _ => .unsupported
  | .notWellFormed => .notWellFormed
  | .unprintableName => .unsupported

/-- The human-readable reason of a gate failure, identical to the driver's
stderr text before the gate was proved. -/
def GateError.message : GateError → String
  | .notAdmitted reason => reason
  | .notWellFormed => "model is not well-formed"
  | .unprintableName =>
      "a variable name cannot be printed as a solution identifier (reserved word or invalid characters)"

/-- The gate: admit, then check well-formedness, then printable names.  The
order and the error classes are those the CLI driver has always used. -/
def gate (m : Model) : Except GateError GatedModel :=
  match hf : LeanFzn.Semantics.Admission.firstFailure m with
  | some reason => .error (.notAdmitted reason)
  | none =>
      match hwf : LeanFzn.Checker.wellFormedFastB m with
      | false => .error .notWellFormed
      | true =>
          match hp : @(m.variables.all fun d => LeanFzn.Parser.Lexer.printableSolutionNameB d.name.name) with
          | false => .error .unprintableName
          | true =>
              .ok { model := m,
                    admitted := (@LeanFzn.Semantics.Admission.firstFailure_none_iff m).mp hf,
                    wfFast := hwf,
                    printables := hp }

/-- A successful gate yields exactly the three checked facts about the raw
model; this is the direction every caller uses. -/
theorem gate_ok_facts {m : Model} {g : GatedModel} (h : gate m = .ok g) :
    g.model = m ∧ LeanFzn.Semantics.Admission.Admitted m ∧
      LeanFzn.Checker.wellFormedFastB m = true ∧
      (m.variables.all fun d => LeanFzn.Parser.Lexer.printableSolutionNameB d.name.name) = true := by
  unfold gate at h
  split at h
  · cases h
  · next hf =>
      split at h
      · cases h
      · next hwf =>
          split at h
          · cases h
          · cases h
            have h1 := (@LeanFzn.Semantics.Admission.firstFailure_none_iff m).mp hf
            exact ⟨rfl, h1, hwf, by assumption⟩

/-- **THE GATE'S SPEC**: a model can be gated exactly when it is admitted,
well-formed and has printable output names.  The forward direction says the
gate only ever accepts such a model; the backward direction says it accepts
every one of them. -/
theorem gate_ok_iff (m : Model) :
    (∃ g, gate m = .ok g ∧ g.model = m) ↔
      LeanFzn.Semantics.Admission.Admitted m ∧
        LeanFzn.Checker.wellFormedFastB m = true ∧
        (m.variables.all fun d => LeanFzn.Parser.Lexer.printableSolutionNameB d.name.name) = true := by
  constructor
  · rintro ⟨g, h, -⟩
    obtain ⟨-, h1, h2, h3⟩ := gate_ok_facts h
    exact ⟨h1, h2, h3⟩
  · rintro ⟨hadm, hwf, hp⟩
    have hf : LeanFzn.Semantics.Admission.firstFailure m = none :=
      (@LeanFzn.Semantics.Admission.firstFailure_none_iff m).mpr hadm
    let hgmk : GatedModel := ⟨m, hadm, hwf, hp⟩
    have hgate : gate m = .ok hgmk := by
      unfold gate
      split
      · next reason hr => rw [hf] at hr; cases hr
      · next hr =>
          split
          · next hf' => rw [hwf] at hf'; cases hf'
          · next hf' =>
              split
              · next hp' => rw [hp] at hp'; cases hp'
              · next hp' => rfl
    exact ⟨hgmk, hgate, rfl⟩

/-- The driver's convenience form: a successful gate yields the model with all
three facts, so a raw input never needs a separate check. -/
theorem gate_success {m : Model} {g : GatedModel} (h : gate m = .ok g) :
    g.model = m ∧ LeanFzn.Semantics.Admission.Admitted m ∧
      LeanFzn.Checker.wellFormedFastB m = true ∧
      (m.variables.all fun d => LeanFzn.Parser.Lexer.printableSolutionNameB d.name.name) = true :=
  gate_ok_facts h

/-- A gate failure is one of the three checks, and never a silent rejection:
the driver can always name the failing kind. -/
theorem gate_error_inv {m : Model} {e : GateError} (h : gate m = .error e) :
    e = .notAdmitted ((LeanFzn.Semantics.Admission.firstFailure m).getD "") ∨
    (LeanFzn.Semantics.Admission.firstFailure m = none ∧
      (e = .notWellFormed ∨ e = .unprintableName)) := by
  unfold gate at h
  split at h
  · next reason hf =>
      cases h
      left
      rw [hf]
      rfl
  · next hf =>
      split at h
      · cases h; exact Or.inr ⟨hf, Or.inl rfl⟩
      · next hwf =>
          split at h
          · cases h; exact Or.inr ⟨hf, Or.inr rfl⟩
          · cases h

end LeanFzn.Core

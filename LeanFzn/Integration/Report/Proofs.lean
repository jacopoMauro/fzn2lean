/-
File: LeanFzn/Integration/Report/Proofs.lean

Purpose:
  Kernel-checked bridges between the pure report layer and the certified source
  results: classifier inversion, satisfaction/optimization soundness, the
  terminal exit/marker table, the JSON event codec, and the canonical solution
  entry/text binding.

Dependencies:
  - Report.Codec: Event encoding and the pure classifiers.
  - Public.Seed / Public.Lns: stateful and LNS optimization source results.
  - Emit.RoundTrip: the actual emitter's parser/denotation round trip.

DAG:
  Report.Basic -> Report.Codec -> Report.Proofs.  Runtime report construction
  must not import this module; only certified proof development does.

Notes:
  `Json.getObjVal?` in Lean 4.35 returns `Except String Json`, so the codec
  theorems below state their result with `.ok` (the `.toOption` of the frozen
  `some` form).  See the A1/A2 migration note.
-/
import LeanFzn.Integration.Report.Codec
import LeanFzn.Integration.Public.Seed
import LeanFzn.Integration.Public.Lns
import LeanFzn.Integration.Emit.RoundTrip

namespace LeanFzn.Integration.Report
open LeanFzn LeanFzn.Semantics LeanFzn.Compiler
open LeanFzn.Semantics.Globals
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Integration
open LeanFzn.Engine
open LeanFzn.Checker.Solution LeanFzn.Parser.Lexer

/-! ## Classifier inversion

The classifiers read only the actual result's constructor, the completion bit
and the last witness.  These lemmas expose exactly that information; no
theorem assumes its own conclusion. -/

theorem classifyOptimization_eq_incomplete {run : OptRun} (h : run.complete = false) :
    classifyOptimization run = .incomplete := by
  simp [classifyOptimization, h]

theorem classifyOptimization_eq_optimal {run : OptRun} (hcomp : run.complete = true)
    {s : List Value × Int} (hlast : run.sols.getLast? = some s) :
    classifyOptimization run = .optimal s := by
  simp [classifyOptimization, hcomp, hlast]

theorem classifyOptimization_eq_unsat {run : OptRun} (hcomp : run.complete = true)
    (hnil : run.sols = []) :
    classifyOptimization run = .unsat := by
  simp [classifyOptimization, hcomp, hnil]

theorem classifyOptimization_optimal_inv {run : OptRun} {s : List Value × Int}
    (h : classifyOptimization run = .optimal s) :
    run.complete = true ∧ run.sols.getLast? = some s := by
  cases hcomp : run.complete with
  | false =>
      rw [classifyOptimization_eq_incomplete hcomp] at h
      cases h
  | true =>
      cases hlast : run.sols.getLast? with
      | none =>
          have hnil : run.sols = [] := List.getLast?_eq_none_iff.mp hlast
          rw [classifyOptimization_eq_unsat hcomp hnil] at h
          cases h
      | some s' =>
          rw [classifyOptimization_eq_optimal hcomp hlast] at h
          cases h
          exact ⟨rfl, rfl⟩

theorem classifyOptimization_unsat_inv {run : OptRun}
    (h : classifyOptimization run = .unsat) :
    run.complete = true ∧ run.sols = [] := by
  cases hcomp : run.complete with
  | false =>
      rw [classifyOptimization_eq_incomplete hcomp] at h
      cases h
  | true =>
      cases hlast : run.sols.getLast? with
      | none => exact ⟨rfl, List.getLast?_eq_none_iff.mp hlast⟩
      | some s' =>
          rw [classifyOptimization_eq_optimal hcomp hlast] at h
          cases h

/-! ## T1 — classification safety (no proof claim without completion) -/

theorem classifyOptimization_incomplete (run : OptRun) (h : run.complete = false) :
    (classifyOptimization run).kind ≠ .optimal := by
  rw [classifyOptimization_eq_incomplete h]
  simp [OptimizationClass.kind]

theorem classifySatisfaction_unknown_no_proof_claim (reason : String) :
    (classifySatisfaction (.unknown reason)).kind.hasProofClaim = false := rfl

theorem classifySatisfaction_unsupported_no_proof_claim (reason : String) :
    (classifySatisfaction (.unsupported reason)).kind.hasProofClaim = false := rfl

theorem classifyOptimization_incomplete_no_proof_claim (run : OptRun)
    (h : run.complete = false) :
    (classifyOptimization run).kind.hasProofClaim = false := by
  rw [classifyOptimization_eq_incomplete h]
  rfl

/-! ## T2 — satisfaction UNSAT bridge -/

theorem satisfaction_unsat_sound {m : Model} {o : SearchConfig} {fuel : Nat}
    (hwf : WellFormed fullSig m)
    (h : (classifySatisfaction (LeanFzn.Core.solveModel m o fuel)).kind = .unsat) :
    ¬ ∃ store, Satisfies fullSig fullInterp m store ∧
      LeanFzn.Semantics.ParamHonest m store := by
  have hres : LeanFzn.Core.solveModel m o fuel = .unsat := by
    cases hc : LeanFzn.Core.solveModel m o fuel with
    | sat store =>
        simp [classifySatisfaction, SatisfactionClass.kind, hc] at h
    | unsat => rfl
    | unsupported reason =>
        simp [classifySatisfaction, SatisfactionClass.kind, hc] at h
    | unknown reason =>
        simp [classifySatisfaction, SatisfactionClass.kind, hc] at h
  exact LeanFzn.Core.solveModel_unsat_correct hwf hres

/-! ## T3 — satisfaction SAT bridge -/

theorem satisfaction_sat_sound {m : Model} {o : SearchConfig} {fuel : Nat}
    {store : Store}
    (hwf : WellFormed fullSig m)
    (h : classifySatisfaction (LeanFzn.Core.solveModel m o fuel) = .sat store) :
    Satisfies fullSig fullInterp m store := by
  have hres : LeanFzn.Core.solveModel m o fuel = .sat store := by
    cases hc : LeanFzn.Core.solveModel m o fuel with
    | sat store' =>
        simp [classifySatisfaction, hc] at h
        rw [h]
    | unsat => simp [classifySatisfaction, hc] at h
    | unsupported reason => simp [classifySatisfaction, hc] at h
    | unknown reason => simp [classifySatisfaction, hc] at h
  exact LeanFzn.Core.solveModel_sat_correct hwf hres

/-! ## T4 — linear optimization optimal bridge -/

theorem optimization_optimal_sound {m : Model} {o : SearchConfig} {fuel : Nat}
    {p : CompiledProblem DomConstraint} {run : OptRun} {s : List Value × Int}
    (h : LeanFzn.Core.optimizeCore m o fuel = .ok (p, run))
    (hwf : WellFormed fullSig m)
    (hc : classifyOptimization run = .optimal s) :
    IsSolution fullSig fullInterp m (p.toStore s.1) := by
  obtain ⟨hcomp, hlast⟩ := classifyOptimization_optimal_inv hc
  exact LeanFzn.Core.optimizeCore_optimal h hwf hcomp hlast

/-! ## T5 — linear optimization UNSAT bridge -/

theorem optimization_unsat_sound {m : Model} {o : SearchConfig} {fuel : Nat}
    {p : CompiledProblem DomConstraint} {run : OptRun}
    (h : LeanFzn.Core.optimizeCore m o fuel = .ok (p, run))
    (hwf : WellFormed fullSig m)
    (hc : classifyOptimization run = .unsat) :
    ¬ ∃ store, Satisfies fullSig fullInterp m store ∧
      LeanFzn.Semantics.ParamHonest m store := by
  obtain ⟨hcomp, hnil⟩ := classifyOptimization_unsat_inv hc
  exact LeanFzn.Core.optimizeCore_unsat h hwf hcomp hnil

/-! ## T6 — seeded optimization bridges -/

theorem seed_optimal_sound {o : SearchConfig} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun} {seeds : List Nat}
    {s : List Value × Int}
    (h : LeanFzn.Core.optimizeCoreSeed o m = .ok ⟨p, run, seeds⟩)
    (hwf : WellFormed fullSig m)
    (hc : classifyOptimization run = .optimal s) :
    IsSolution fullSig fullInterp m (p.toStore s.1) := by
  obtain ⟨hcomp, hlast⟩ := classifyOptimization_optimal_inv hc
  exact LeanFzn.Core.optimizeCoreSeed_optimal h hwf hcomp hlast

theorem seed_unsat_sound {o : SearchConfig} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun} {seeds : List Nat}
    (h : LeanFzn.Core.optimizeCoreSeed o m = .ok ⟨p, run, seeds⟩)
    (hwf : WellFormed fullSig m)
    (hc : classifyOptimization run = .unsat) :
    ¬ ∃ store, Satisfies fullSig fullInterp m store ∧
      LeanFzn.Semantics.ParamHonest m store := by
  obtain ⟨hcomp, hnil⟩ := classifyOptimization_unsat_inv hc
  exact LeanFzn.Core.optimizeCoreSeed_unsat h hwf hcomp hnil

/-! ## T7 — LNS bridges -/

theorem lns_optimal_sound {o : SearchConfig} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun} {s : List Value × Int}
    (h : LeanFzn.Core.optimizeCoreLns o m = .ok (p, run))
    (hwf : WellFormed fullSig m)
    (hc : classifyOptimization run = .optimal s) :
    IsSolution fullSig fullInterp m (p.toStore s.1) := by
  obtain ⟨hcomp, hlast⟩ := classifyOptimization_optimal_inv hc
  exact LeanFzn.Core.optimizeCoreLns_optimal h hwf hcomp hlast

theorem lns_unsat_sound {o : SearchConfig} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun}
    (h : LeanFzn.Core.optimizeCoreLns o m = .ok (p, run))
    (hwf : WellFormed fullSig m)
    (hc : classifyOptimization run = .unsat) :
    ¬ ∃ store, Satisfies fullSig fullInterp m store ∧
      LeanFzn.Semantics.ParamHonest m store := by
  obtain ⟨hcomp, hnil⟩ := classifyOptimization_unsat_inv hc
  exact LeanFzn.Core.optimizeCoreLns_unsat h hwf hcomp hnil

/-! ## T9 — terminal/exit/marker consistency -/

/-- The frozen six-row exit-code decision table. -/
theorem terminalKind_exitCode_table :
    TerminalKind.exitCode .sat = 0 ∧
    TerminalKind.exitCode .unsat = 1 ∧
    TerminalKind.exitCode .optimal = 0 ∧
    TerminalKind.exitCode .incomplete = 4 ∧
    TerminalKind.exitCode .unsupported = 3 ∧
    TerminalKind.exitCode .error = 2 := by
  decide

/-- Only satisfaction and optimality exit successfully. -/
theorem terminalKind_exit_eq (k : TerminalKind) :
    (TerminalKind.exitCode k = 0) ↔ (k = .sat ∨ k = .optimal) := by
  cases k <;> decide

/-- An UNSAT text marker is printed only for `.unsat`. -/
theorem terminalKind_marker_sound (k : TerminalKind) :
    TerminalKind.marker? k = some "=====UNSATISFIABLE=====" → k = .unsat := by
  cases k with
  | sat => intro h; simp [TerminalKind.marker?, TerminalKind.textMarker?] at h
  | unsat => intro _; rfl
  | optimal =>
      intro h
      simp [TerminalKind.marker?, TerminalKind.textMarker?] at h
      exact absurd h (by decide)
  | incomplete => intro h; simp [TerminalKind.marker?, TerminalKind.textMarker?] at h
  | unsupported => intro h; simp [TerminalKind.marker?, TerminalKind.textMarker?] at h
  | error => intro h; simp [TerminalKind.marker?, TerminalKind.textMarker?] at h

/-- The optimum text marker is printed only for `.optimal`. -/
theorem terminalKind_marker_sound_optimal (k : TerminalKind) :
    TerminalKind.marker? k = some "==========" → k = .optimal := by
  cases k with
  | sat => intro h; simp [TerminalKind.marker?, TerminalKind.textMarker?] at h
  | unsat =>
      intro h
      simp [TerminalKind.marker?, TerminalKind.textMarker?] at h
      exact absurd h (by decide)
  | optimal => intro _; rfl
  | incomplete => intro h; simp [TerminalKind.marker?, TerminalKind.textMarker?] at h
  | unsupported => intro h; simp [TerminalKind.marker?, TerminalKind.textMarker?] at h
  | error => intro h; simp [TerminalKind.marker?, TerminalKind.textMarker?] at h

/-- Incomplete, unsupported and error terminals print no proof marker. -/
theorem terminalKind_no_marker_of_incomplete (k : TerminalKind)
    (h : k = .incomplete ∨ k = .unsupported ∨ k = .error) :
    TerminalKind.marker? k = none := by
  rcases h with rfl | rfl | rfl <;> rfl

/-! ## T10 — event codec

`Json.getObjVal?` returns `Except String Json` in Lean 4.35; these are the
frozen statements with `.ok` in place of the unavailable `some`. -/

theorem terminal_toJson_event (k : TerminalKind) (last : Option Nat)
    (reason : Option String) :
    (Event.toJson (.terminal k last reason)).getObjVal? "event" =
      .ok (.str "terminal") := by
  unfold Event.toJson Event.fields
  cases last <;> cases reason <;> rfl

theorem terminal_toJson_exit (k : TerminalKind) (last : Option Nat)
    (reason : Option String) :
    (Event.toJson (.terminal k last reason)).getObjVal? "exit" =
      .ok (.num (TerminalKind.exitCode k).toNat) := by
  unfold Event.toJson Event.fields
  cases last <;> cases reason <;> rfl

theorem error_toJson_exit (k : ErrorKind) (message : String) :
    (Event.toJson (.error k message)).getObjVal? "exit" =
      .ok (.num (ErrorKind.exitCode k).toNat) := by
  unfold Event.toJson Event.fields
  rfl

/-! ## T11 — solution entry name/text binding -/

/-- The snd projection of the protocol entry pairs is the actual certified
    emitter's line list. -/
theorem certifiedEntryPairs_snd (m : Model) (store : Store) :
    (certifiedEntryPairs m store).map Prod.snd = certifiedEntries m store := by
  rw [certifiedEntries_eq_render]
  simp only [certifiedEntryPairs, emittedStoreTokenLines, emitDeclEntry, List.map_filterMap]
  congr 1
  funext d
  cases store d.name <;> rfl

/-- With every declared variable present in the store, the fst projection of
    the protocol entry pairs is the declaration name list in order. -/
private theorem certifiedEntryPairs_fst_aux (ds : List VarDeclItem) (store : Store)
    (h : ∀ d ∈ ds, ∃ v, store d.name = some v) :
    (ds.filterMap fun d =>
      (store d.name).map fun v => (d.name.name, emitDeclEntry d v)).map Prod.fst =
      ds.map (fun d => d.name.name) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
      obtain ⟨v, hv⟩ := h d (by simp)
      simp only [List.filterMap_cons, hv, Option.map_some, List.map_cons]
      rw [ih (fun e he => h e (by simp [he]))]

theorem certifiedEntryPairs_fst {m : Model} {store : Store}
    (h : ∀ d ∈ m.variables, ∃ v, store d.name = some v) :
    (certifiedEntryPairs m store).map Prod.fst =
      m.variables.map (fun d => d.name.name) := by
  simpa only [certifiedEntryPairs] using
    certifiedEntryPairs_fst_aux m.variables store h

/-- The pure text renderer is exactly the actual certified solution text. -/
theorem renderSolutionText_eq_emitCertifiedSolution (m : Model) (store : Store) :
    renderSolutionText m store = emitCertifiedSolution m store := by
  simp [renderSolutionText, emitCertifiedSolution, certifiedEntryPairs_snd]

/-- Every parsed solution entry names a declaration, and its decoded value is
    exactly the store value rendered by the certified emitter. -/
theorem solution_entries_bind {m : Model} {store : Store}
    (hs : Satisfies fullSig fullInterp m store)
    (hn : ∀ d ∈ m.variables, PrintableSolutionName d.name.name) :
    ∃ es,
      parseSolution (stripSeparators (emitCertifiedSolution m store)) = .ok es ∧
      es.map Entry.name = (certifiedEntryPairs m store).map Prod.fst ∧
      (∀ e ∈ es, ∃ d ∈ m.variables, ∃ v,
        e.name = d.name.name ∧ store d.name = some v ∧
        SolValueMatches e.value v) := by
  obtain ⟨es, hparse, hnames, hdenote, -⟩ :=
    emitCertifiedSolution_roundTrip (sig := fullSig) (pred := fullInterp) hs hn
  refine ⟨es, hparse, ?_, hdenote⟩
  rw [hnames]
  have hlook : ∀ d ∈ m.variables, ∃ v, store d.name = some v := by
    intro d hd
    obtain ⟨v, hv, -⟩ := declValueFits_of_satisfiesDyn hs.2 hd
    exact ⟨v, hv⟩
  rw [certifiedEntryPairs_fst hlook]

/-- The driver's name gate establishes the emitter's name premise. -/
theorem outputNamesPrintableB_sound {m : Model} (h : outputNamesPrintableB m = true) :
    ∀ d ∈ m.variables, PrintableSolutionName d.name.name := by
  intro d hd
  exact (printableSolutionNameB_iff _).mp (List.all_eq_true.mp h d hd)

/-- `solution_entries_bind` with the name premise discharged by the gate the
    driver actually runs, so only `Satisfies` remains. -/
theorem solution_entries_bind_of_gate {m : Model} {store : Store}
    (hs : Satisfies fullSig fullInterp m store)
    (hg : outputNamesPrintableB m = true) :
    ∃ es,
      parseSolution (stripSeparators (emitCertifiedSolution m store)) = .ok es ∧
      es.map Entry.name = (certifiedEntryPairs m store).map Prod.fst ∧
      (∀ e ∈ es, ∃ d ∈ m.variables, ∃ v,
        e.name = d.name.name ∧ store d.name = some v ∧
        SolValueMatches e.value v) :=
  solution_entries_bind hs (outputNamesPrintableB_sound hg)

/-! ## T12 — report truth composes with the classifier -/

theorem satisfaction_report_truthful {m : Model} {o : SearchConfig} {fuel : Nat}
    (hwf : WellFormed fullSig m) :
    (classifySatisfaction (LeanFzn.Core.solveModel m o fuel)).Truthful m := by
  cases hc : LeanFzn.Core.solveModel m o fuel with
  | sat store =>
      have hclass : classifySatisfaction (LeanFzn.Core.solveModel m o fuel) =
          .sat store := by
        simp [classifySatisfaction, hc]
      exact satisfaction_sat_sound hwf hclass
  | unsat =>
      have hclass : classifySatisfaction (LeanFzn.Core.solveModel m o fuel) =
          .unsat := by
        simp [classifySatisfaction, hc]
      have hkind : (classifySatisfaction (LeanFzn.Core.solveModel m o fuel)).kind =
          .unsat := by
        rw [hclass]
        rfl
      exact satisfaction_unsat_sound hwf hkind
  | unsupported _ => trivial
  | unknown _ => trivial

theorem optimization_report_truthful {m : Model} {o : SearchConfig} {fuel : Nat}
    {p : CompiledProblem DomConstraint} {run : OptRun}
    (h : LeanFzn.Core.optimizeCore m o fuel = .ok (p, run))
    (hwf : WellFormed fullSig m) :
    (classifyOptimization run).Truthful m p := by
  cases hcomp : run.complete with
  | false =>
      have hclass : classifyOptimization run = .incomplete :=
        classifyOptimization_eq_incomplete hcomp
      rw [hclass]
      trivial
  | true =>
      cases hlast : run.sols.getLast? with
      | none =>
          have hnil : run.sols = [] := List.getLast?_eq_none_iff.mp hlast
          have hclass : classifyOptimization run = .unsat :=
            classifyOptimization_eq_unsat hcomp hnil
          rw [hclass]
          exact optimization_unsat_sound h hwf hclass
      | some s =>
          have hclass : classifyOptimization run = .optimal s :=
            classifyOptimization_eq_optimal hcomp hlast
          rw [hclass]
          exact optimization_optimal_sound h hwf hclass

/-! ## A3.5 — checked emission completeness -/

private theorem length_filterMap_eq_of_forall_isSome {α β : Type} (l : List α)
    (f : α → Option β) (h : ∀ a ∈ l, (f a).isSome) :
    (l.filterMap f).length = l.length := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      have ha : (f a).isSome := h a (by simp)
      have htail : ∀ b ∈ as, (f b).isSome := fun b hb => h b (by simp [hb])
      cases hfa : f a with
      | none => simp [hfa] at ha
      | some b =>
          simp only [List.filterMap_cons, hfa, List.length_cons]
          rw [ih htail]

/-- Every certified satisfying store has a value for every declared variable,
    so the checked text/JSON emission takes its successful branch. -/
theorem certifiedEntryPairs_length_eq_of_satisfies {m : Model} {store : Store}
    (hs : Satisfies fullSig fullInterp m store) :
    (certifiedEntryPairs m store).length = m.variables.length := by
  unfold certifiedEntryPairs
  apply length_filterMap_eq_of_forall_isSome
  intro d hd
  obtain ⟨v, hv, -⟩ := declValueFits_of_satisfiesDyn hs.2 hd
  simp [hv]

end LeanFzn.Integration.Report

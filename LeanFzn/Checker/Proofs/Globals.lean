/-
Purpose: Correctness and equivalence theorems for the globals checker.
Dependencies: Checker.Runtime.Globals and correctness of earlier checker layers.
DAG: Runtime.Globals -> Proofs.Globals -> public Checker.Globals import.
-/
import LeanFzn.Checker.Runtime.Globals
import LeanFzn.Checker.Proofs.Solution
import LeanFzn.Checker.Proofs.SolutionParser

open LeanFzn.Semantics LeanFzn.Parser LeanFzn.Semantics.Evaluation

namespace LeanFzn.Checker.Globals

open LeanFzn LeanFzn.Semantics.Globals LeanFzn.Checker.Solution
open Internal

/-- `constraintHoldsFullB` decides `Holds fullInterp` for checkable
    predicates. -/
private theorem constraintHoldsFullB_iff {store : Store} {c : ConstraintItem}
    (hname : c.name.name ∈ fullCheckableNames) :
    constraintHoldsFullB store c = true ↔ c.Holds fullInterp store := by
  unfold constraintHoldsFullB ConstraintItem.Holds
  cases hargs : c.args.mapM (Expr.eval store) with
  | none =>
      constructor
      · intro hfalse
        exact absurd hfalse (by intro hc; cases hc)
      · rintro ⟨args, hnone, _⟩
        cases hnone
  | some args =>
      constructor
      · intro h
        refine ⟨args, rfl, ?_⟩
        have hred : fullInterpB c.name args = true := h
        cases hc : c.name with
        | mk n' =>
            rw [hc] at hred hname
            exact (fullInterpB_iff (n := n') hname).mp hred
      · rintro ⟨args', hargs', hinterp⟩
        have hargs_eq : args = args' := Option.some.inj hargs'
        subst hargs_eq
        show fullInterpB c.name args = true
        cases hc : c.name with
        | mk n' =>
            rw [hc] at hinterp hname
            exact (fullInterpB_iff (n := n') hname).mpr hinterp

/-- **Correctness of the full checker.**  For a model whose
    constraints all use checkable predicates (the 138 `fzn_*` global
    constraints or the standard library), `checkSolutionFull` returns
    `true` if and only if the solution string parses and the candidate
    store it describes satisfies every dynamic condition of
    `Satisfies fullSig fullInterp`: the constraint reading of `Holds`,
    the variable-domain conditions, and the initializer conditions. -/
theorem checkSolutionFull_correct_parse (m : Model) (sol : String)
    (hnames : ∀ c ∈ m.constraints, c.name.name ∈ fullCheckableNames) :
    checkSolutionFull m sol = true ↔
      ∃ es, LeanFzn.Checker.Solution.parseSolution
          (LeanFzn.Checker.Solution.stripSeparators sol) = .ok es ∧
        SatisfiesDyn fullInterp m (LeanFzn.Checker.Solution.completedStore m es) := by
  constructor
  · intro htrue
    unfold checkSolutionFull at htrue
    cases hparse : LeanFzn.Checker.Solution.parseSolution
        (LeanFzn.Checker.Solution.stripSeparators sol) with
    | error _ =>
        rw [hparse] at htrue
        exact absurd htrue (by simp)
    | ok es =>
        rw [hparse] at htrue
        simp only [Bool.and_eq_true, List.all_eq_true] at htrue
        obtain ⟨⟨hassign, hvars⟩, hcons⟩ := htrue
        rw [LeanFzn.Checker.Solution.allAssignedB, List.all_eq_true] at hassign
        rw [LeanFzn.Checker.Solution.varDeclsOkB, List.all_eq_true] at hvars
        refine ⟨es, hparse.symm ▸ rfl, ?_⟩
        refine ⟨?_, ?_, ?_⟩
        · intro c hc
          exact (constraintHoldsFullB_iff (hnames c hc)).mp (hcons c hc)
        · -- variable-domain conditions from allAssignedB + varDeclsOkB
          intro d hd
          have hall := hassign d hd
          have hok := hvars d hd
          cases d with
          | basic ty n _anns _opt =>
              cases hstore : (LeanFzn.Checker.Solution.completedStore m es) n with
              | none =>
                  have hred : (LeanFzn.Checker.Solution.completedStore m es n).isSome = true := hall
                  rw [hstore] at hred
                  exact absurd hred (by simp)
              | some v =>
                  have hred : (match LeanFzn.Checker.Solution.completedStore m es n with
                      | some v => LeanFzn.Checker.Solution.varTypeContainsB ty v &&
                          LeanFzn.Checker.Solution.initializerHoldsB
                            (LeanFzn.Checker.Solution.completedStore m es)
                            (VarDeclItem.basic ty n _anns _opt)
                      | none => false) = true := hok
                  rw [hstore] at hred
                  simp only [Bool.and_eq_true] at hred
                  exact ⟨v, hstore, LeanFzn.Checker.Solution.varTypeContainsB_iff.mp hred.1⟩
          | array ty n _anns _elems =>
              cases hstore : (LeanFzn.Checker.Solution.completedStore m es) n with
              | none =>
                  have hred : (LeanFzn.Checker.Solution.completedStore m es n).isSome = true := hall
                  rw [hstore] at hred
                  exact absurd hred (by simp)
              | some v =>
                  have hred : (match LeanFzn.Checker.Solution.completedStore m es n with
                      | some (.array vs) =>
                          (decide (vs.length = ty.idx.length) &&
                            vs.all (fun v =>
                              LeanFzn.Checker.Solution.varTypeContainsB ty.elem v)) &&
                          LeanFzn.Checker.Solution.initializerHoldsB
                            (LeanFzn.Checker.Solution.completedStore m es)
                            (VarDeclItem.array ty n _anns _elems)
                      | _ => false) = true := hok
                  rw [hstore] at hred
                  cases v with
                  | bool _ | int _ | setOfInt _ => exact absurd hred (by simp)
                  | array vs =>
                      simp only [Bool.and_eq_true, decide_eq_true_eq,
                        List.all_eq_true] at hred
                      obtain ⟨⟨hlen, helems⟩, _⟩ := hred
                      exact ⟨vs, hstore, hlen, fun v hv =>
                        LeanFzn.Checker.Solution.varTypeContainsB_iff.mp (helems v hv)⟩
        · -- initializer conditions from varDeclsOkB
          intro d hd
          have hok := hvars d hd
          have hinit : LeanFzn.Checker.Solution.initializerHoldsB
              (LeanFzn.Checker.Solution.completedStore m es) d = true := by
            cases d with
            | basic _ty n _anns _opt =>
                cases hstore : (LeanFzn.Checker.Solution.completedStore m es) n with
                | none =>
                    have hred : (match LeanFzn.Checker.Solution.completedStore m es n with
                        | some v =>
                            LeanFzn.Checker.Solution.varTypeContainsB _ty v &&
                              LeanFzn.Checker.Solution.initializerHoldsB
                                (LeanFzn.Checker.Solution.completedStore m es)
                                (VarDeclItem.basic _ty n _anns _opt)
                        | none => false) = true := hok
                    rw [hstore] at hred
                    exact absurd hred (by simp)
                | some _v =>
                    have hred : (match LeanFzn.Checker.Solution.completedStore m es n with
                        | some v =>
                            LeanFzn.Checker.Solution.varTypeContainsB _ty v &&
                              LeanFzn.Checker.Solution.initializerHoldsB
                                (LeanFzn.Checker.Solution.completedStore m es)
                                (VarDeclItem.basic _ty n _anns _opt)
                        | none => false) = true := hok
                    rw [hstore] at hred
                    simp only [Bool.and_eq_true] at hred
                    exact hred.2
            | array _ty n _anns _elems =>
                cases hstore : (LeanFzn.Checker.Solution.completedStore m es) n with
                | none =>
                    have hred : (match LeanFzn.Checker.Solution.completedStore m es n with
                        | some (.array vs) =>
                            (decide (vs.length = _ty.idx.length) &&
                              vs.all (fun v =>
                                LeanFzn.Checker.Solution.varTypeContainsB _ty.elem v)) &&
                            LeanFzn.Checker.Solution.initializerHoldsB
                              (LeanFzn.Checker.Solution.completedStore m es)
                              (VarDeclItem.array _ty n _anns _elems)
                        | _ => false) = true := hok
                    rw [hstore] at hred
                    exact absurd hred (by simp)
                | some v =>
                    have hred : (match LeanFzn.Checker.Solution.completedStore m es n with
                        | some (.array vs) =>
                            (decide (vs.length = _ty.idx.length) &&
                              vs.all (fun v =>
                                LeanFzn.Checker.Solution.varTypeContainsB _ty.elem v)) &&
                            LeanFzn.Checker.Solution.initializerHoldsB
                              (LeanFzn.Checker.Solution.completedStore m es)
                              (VarDeclItem.array _ty n _anns _elems)
                        | _ => false) = true := hok
                    rw [hstore] at hred
                    cases v with
                    | bool _ | int _ | setOfInt _ => exact absurd hred (by simp)
                    | array _vs =>
                        simp only [Bool.and_eq_true] at hred
                        exact hred.2
          exact LeanFzn.Checker.Solution.initializerHoldsB_iff.mp hinit
  · rintro ⟨es, hparse, hcons, hvars, hinit⟩
    unfold checkSolutionFull
    rw [hparse]
    simp only [Bool.and_eq_true, List.all_eq_true]
    refine ⟨⟨List.all_eq_true.mpr ?_, List.all_eq_true.mpr ?_⟩, ?_⟩
    · -- allAssignedB
      intro d hd
      have hdecl := hvars d hd
      cases d with
      | basic _ty n _anns _opt =>
          obtain ⟨v, hstore, _⟩ := hdecl
          have hred : (LeanFzn.Checker.Solution.completedStore m es n).isSome = true := by
            rw [hstore]; simp
          show ((LeanFzn.Checker.Solution.completedStore m es)
            (VarDeclItem.basic _ty n _anns _opt).name).isSome = true
          exact hred
      | array _ty n _anns _elems =>
          obtain ⟨vs, hstore, _, _⟩ := hdecl
          have hred : (LeanFzn.Checker.Solution.completedStore m es n).isSome = true := by
            rw [hstore]; simp
          show ((LeanFzn.Checker.Solution.completedStore m es)
            (VarDeclItem.array _ty n _anns _elems).name).isSome = true
          exact hred
    · -- varDeclsOkB
      intro d hd
      have hdecl := hvars d hd
      have hinitd := hinit d hd
      have hinitB : LeanFzn.Checker.Solution.initializerHoldsB
          (LeanFzn.Checker.Solution.completedStore m es) d = true :=
        LeanFzn.Checker.Solution.initializerHoldsB_iff.mpr hinitd
      cases d with
      | basic ty n _anns _opt =>
          cases hstore : (LeanFzn.Checker.Solution.completedStore m es) n with
          | none =>
              have hred : ∃ v, LeanFzn.Checker.Solution.completedStore m es n = some v ∧
                  ty.contains v := hdecl
              exact absurd hred (by
                intro ⟨v, hn, _⟩
                rw [hstore] at hn
                cases hn)
          | some v =>
              obtain ⟨v', hstore', hcontains⟩ := hdecl
              rw [hstore] at hstore'
              have hvv : v = v' := Option.some.inj hstore'
              show (match LeanFzn.Checker.Solution.completedStore m es n with
                | some v => LeanFzn.Checker.Solution.varTypeContainsB ty v &&
                    LeanFzn.Checker.Solution.initializerHoldsB
                      (LeanFzn.Checker.Solution.completedStore m es)
                      (VarDeclItem.basic ty n _anns _opt)
                | none => false) = true
              rw [hstore]
              simp only [Bool.and_eq_true]
              rw [hvv]
              exact ⟨LeanFzn.Checker.Solution.varTypeContainsB_iff.mpr hcontains, hinitB⟩
      | array ty n _anns _elems =>
          cases hstore : (LeanFzn.Checker.Solution.completedStore m es) n with
          | none =>
              have hred : ∃ vs, LeanFzn.Checker.Solution.completedStore m es n =
                  some (Value.array vs) ∧ vs.length = ty.idx.length ∧
                ∀ v ∈ vs, ty.elem.contains v := hdecl
              exact absurd hred (by
                intro ⟨_, hn, _, _⟩
                rw [hstore] at hn
                cases hn)
          | some v =>
              obtain ⟨vs, hstore', hlen, helems⟩ := hdecl
              rw [hstore] at hstore'
              cases v with
              | bool _ | int _ | setOfInt _ =>
                  cases Option.some.inj hstore'
              | array vs' =>
                  have hvs : vs' = vs := by
                    have h1 : Value.array vs' = Value.array vs :=
                      Option.some.inj hstore'
                    exact (Value.array.injEq vs' vs).mp h1
                  have hgoal : (match LeanFzn.Checker.Solution.completedStore m es n with
                      | some (.array vs') =>
                          (decide (vs'.length = ty.idx.length) &&
                            vs'.all (fun v =>
                              LeanFzn.Checker.Solution.varTypeContainsB ty.elem v)) &&
                          LeanFzn.Checker.Solution.initializerHoldsB
                            (LeanFzn.Checker.Solution.completedStore m es)
                            (VarDeclItem.array ty n _anns _elems)
                      | _ => false) = true := by
                    rw [hstore]
                    simp only [Bool.and_eq_true, decide_eq_true_eq,
                      List.all_eq_true]
                    have hlen' : vs'.length = ty.idx.length := hvs ▸ hlen
                    have helems' : ∀ v ∈ vs',
                        LeanFzn.Checker.Solution.varTypeContainsB ty.elem v = true := by
                      intro v hv
                      exact LeanFzn.Checker.Solution.varTypeContainsB_iff.mpr
                        (helems v (hvs ▸ hv))
                    exact ⟨⟨hlen', helems'⟩, hinitB⟩
                  exact hgoal
    · -- constraints
      intro c hc
      exact (constraintHoldsFullB_iff (hnames c hc)).mpr (hcons c hc)

/-- Correctness against the independently specified solution grammar.
    The right-hand side describes the values written in a grammatical
    solution, rather than defining valid syntax by parser success.
    `stripSeparators` selects the assignment text of one solution. -/
theorem checkSolutionFull_correct (m : Model) (sol : String)
    (hnames : ∀ c ∈ m.constraints, c.name.name ∈ fullCheckableNames) :
    checkSolutionFull m sol = true ↔
      ∃ es, SolutionGrammar (stripSeparators sol) es ∧
        SatisfiesDyn fullInterp m (completedStore m es) := by
  rw [checkSolutionFull_correct_parse m sol hnames]
  constructor
  · rintro ⟨es, hp, hs⟩
    exact ⟨es, parseSolution_eq_ok_iff_grammar.mp hp, hs⟩
  · rintro ⟨es, hg, hs⟩
    exact ⟨es, parseSolution_eq_ok_iff_grammar.mpr hg, hs⟩

/-- The fast constraint twin agrees with the slow one on checkable
    predicate names (the map lookup agrees with `fullInterpB` by
    `preparedInterpB_iff`). -/
private theorem constraintHoldsFullFastB_iff {store : Store} {c : ConstraintItem}
    (hname : c.name.name ∈ fullCheckableNames) :
    constraintHoldsFullFastB store c = constraintHoldsFullB store c := by
  unfold constraintHoldsFullFastB constraintHoldsFullB
  cases hargs : c.args.mapM (Expr.eval store) with
  | none => rfl
  | some args =>
      show preparedInterpB c.name args = fullInterpB c.name args
      exact preparedInterpB_iff hname

/-- `List.all` is preserved pointwise. -/
private theorem all_eq_of_forall {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ x ∈ l, p x = q x) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      simp only [List.all_cons, h a List.mem_cons_self,
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- **The fast dynamic checker returns the same verdict as
    `checkSolutionFull`** whenever every constraint name is checkable
    (the scope the front door's name gate establishes). -/
theorem checkSolutionFullFast_eq (m : Model) (sol : String)
    (hnames : ∀ c ∈ m.constraints, c.name.name ∈ fullCheckableNames) :
    checkSolutionFullFast m sol = checkSolutionFull m sol := by
  unfold checkSolutionFullFast checkSolutionFull
  cases LeanFzn.Checker.Solution.parseSolution
      (LeanFzn.Checker.Solution.stripSeparators sol) with
  | error _ => rfl
  | ok es =>
      have hthird : m.constraints.all (fun c =>
          constraintHoldsFullFastB (LeanFzn.Checker.Solution.completedBox m es).f c) =
          m.constraints.all (fun c =>
            constraintHoldsFullB (LeanFzn.Checker.Solution.completedBox m es).f c) :=
        all_eq_of_forall _ _ _
          (fun c hc => constraintHoldsFullFastB_iff (hnames c hc))
      show (LeanFzn.Checker.Solution.allAssignedB
          (LeanFzn.Checker.Solution.completedBox m es).f m.variables &&
          LeanFzn.Checker.Solution.varDeclsOkB
            (LeanFzn.Checker.Solution.completedBox m es).f m.variables &&
          m.constraints.all (fun c =>
            constraintHoldsFullFastB (LeanFzn.Checker.Solution.completedBox m es).f c)) =
        (LeanFzn.Checker.Solution.allAssignedB
          (LeanFzn.Checker.Solution.completedBox m es).f m.variables &&
          LeanFzn.Checker.Solution.varDeclsOkB
            (LeanFzn.Checker.Solution.completedBox m es).f m.variables &&
          m.constraints.all (fun c =>
            constraintHoldsFullB (LeanFzn.Checker.Solution.completedBox m es).f c))
      rw [hthird]

end LeanFzn.Checker.Globals

/-
Purpose: Order propagators: bounds definitions and their required entailment proofs.
Dependencies: LeanFzn.Engine.Props.Ne, LeanFzn.Engine.Props.Linear
DAG: shared propagator foundations -> LeanFzn.Engine.Props.Order.Bounds.
-/
import LeanFzn.Engine.Props.Ne
import LeanFzn.Engine.Props.Linear

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

/-! ## Domain bounds -/

/-- The current interval of a compact domain, or `none` when it is empty
(no lower/upper bound readable). -/
def domBounds (d : DomC) : Option (Int × Int) :=
  match d.lo?, d.hi? with
  | some lo, some hi => some (lo, hi)
  | _, _ => none

theorem domBounds_spec {d : DomC} {lo hi : Int} (h : domBounds d = some (lo, hi)) :
    d.lo? = some lo ∧ d.hi? = some hi := by
  cases h1 : d.lo? with
  | none => simp [domBounds, h1] at h
  | some lo' =>
      cases h2 : d.hi? with
      | none => simp [domBounds, h1, h2] at h
      | some hi' =>
          simp only [domBounds, h1, h2, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hlo, hhi⟩ := h
          exact ⟨by rw [hlo], by rw [hhi]⟩

/-- A `posLe` literal is false on a domain whose lower bound exceeds the
bound and whose upper bound does not lie below it. -/
theorem evalLit_posLe_false_of_lo_gt {d : DomC} {s : Nat} {k lo hi : Int}
    (hlo : d.lo? = some lo) (hhi : d.hi? = some hi) (hk : k < lo)
    (hhi' : ¬ hi ≤ k) :
    d.evalLit (posLe s k) = some false := by
  simp only [DomC.evalLit, posLe, hlo, hhi, ↓reduceIte]
  rw [if_neg hhi', if_pos (by omega)]

/-- A `negLe` literal is false on a domain whose upper bound is at most
the bound and whose lower bound does not exceed it. -/
theorem evalLit_negLe_false_of_hi_le {d : DomC} {s : Nat} {k lo hi : Int}
    (hlo : d.lo? = some lo) (hhi : d.hi? = some hi) (hk : hi ≤ k)
    (hlo' : ¬ k < lo) :
    d.evalLit (negLe s k) = some false := by
  simp only [DomC.evalLit, negLe, hlo, hhi, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg hlo', if_pos hk]

/-- A `posLe` literal is true on a domain whose upper bound is at most the
bound. -/
theorem evalLit_posLe_true_of_hi_le {d : DomC} {s : Nat} {k lo hi : Int}
    (hlo : d.lo? = some lo) (hhi : d.hi? = some hi) (hk : hi ≤ k) :
    d.evalLit (posLe s k) = some true := by
  simp only [DomC.evalLit, posLe, hlo, hhi, ↓reduceIte]
  rw [if_pos hk]

/-- A `negLe` literal is true on a domain whose lower bound exceeds the
bound. -/
theorem evalLit_negLe_true_of_lo_gt {d : DomC} {s : Nat} {k lo hi : Int}
    (hlo : d.lo? = some lo) (hhi : d.hi? = some hi) (hk : k < lo) :
    d.evalLit (negLe s k) = some true := by
  simp only [DomC.evalLit, negLe, hlo, hhi, Bool.false_eq_true, ↓reduceIte]
  rw [if_pos hk]

/-- Negating a literal negates its compact-domain evaluation.  The
well-formedness hypothesis is needed for empty order intervals, where
`evalLit` may otherwise report both signs as true. -/
theorem DomC.evalLit_negate (d : DomC) (hWF : d.WF) (l : Literal) :
    d.evalLit l.negate = (d.evalLit l).map (fun b => !b) := by
  obtain ⟨atom, pos⟩ := l
  cases atom with
  | intNe s v =>
      cases pos <;>
        (cases hf : d.fixedValue <;>
          simp only [DomC.evalLit, Literal.negate, hf, Bool.not_true, Bool.not_false] <;>
          split <;> simp_all)
  | intLe s k =>
      cases pos
      · -- `l = negLe`, so `l.negate = posLe`
        cases hlo : d.lo? with
        | none => simp [DomC.evalLit, Literal.negate, hlo]
        | some lo =>
            cases hhi : d.hi? with
            | none => simp [DomC.evalLit, Literal.negate, hlo, hhi]
            | some hi =>
                have hle : lo ≤ hi := DomC.lo?_le_hi? d hWF hlo hhi
                simp only [DomC.evalLit, Literal.negate, hlo, hhi, Bool.not_false]
                by_cases h1 : hi ≤ k
                · have h2 : ¬ lo > k := by omega
                  simp [h1, h2]
                · by_cases h2 : lo > k
                  · simp [h1, h2]
                  · simp [h1, h2]
      · -- `l = posLe`, so `l.negate = negLe`
        cases hlo : d.lo? with
        | none => simp [DomC.evalLit, Literal.negate, hlo]
        | some lo =>
            cases hhi : d.hi? with
            | none => simp [DomC.evalLit, Literal.negate, hlo, hhi]
            | some hi =>
                have hle : lo ≤ hi := DomC.lo?_le_hi? d hWF hlo hhi
                simp only [DomC.evalLit, Literal.negate, hlo, hhi, Bool.not_true]
                by_cases h1 : hi ≤ k
                · have h2 : ¬ lo > k := by omega
                  simp [h1, h2]
                · by_cases h2 : lo > k
                  · simp [h1, h2]
                  · simp [h1, h2]
  | boolEq s b =>
      cases pos
      · cases hf : d.fixedValue with
        | none => simp [DomC.evalLit, Literal.negate, hf]
        | some v =>
            cases v with
            | bool actual => simp [DomC.evalLit, Literal.negate, hf]; cases actual <;> cases b <;> rfl
            | int x => simp [DomC.evalLit, Literal.negate, hf]
            | setOfInt x => simp [DomC.evalLit, Literal.negate, hf]
            | array xs => simp [DomC.evalLit, Literal.negate, hf]
      · cases hf : d.fixedValue with
        | none => simp [DomC.evalLit, Literal.negate, hf]
        | some v =>
            cases v with
            | bool actual => simp [DomC.evalLit, Literal.negate, hf]; cases actual <;> cases b <;> rfl
            | int x => simp [DomC.evalLit, Literal.negate, hf]
            | setOfInt x => simp [DomC.evalLit, Literal.negate, hf]
            | array xs => simp [DomC.evalLit, Literal.negate, hf]

/-! ## Value-equality literals

`eqLit s v` is the value-equality literal "slot `s` carries `v`", the
negation of `neLit` from `Ne.lean`.  On a kind-homogeneous initial domain
containing the witness, it is exact. -/

/-- The value-equality literal "slot `s` carries `v`". -/
def eqLit (s : Nat) (v : Value) : Literal := (neLit s v).negate

theorem atomSlot_neLit (s : Nat) (v : Value) : atomSlot (neLit s v).atom = s := by
  cases v <;> rfl

theorem atomSlot_eqLit (s : Nat) (v : Value) : atomSlot (eqLit s v).atom = s := by
  cases v <;> rfl

/-- `neLit` evaluates to `some` (never `none`) on a member of a
kind-homogeneous initial domain. -/
theorem neLit_eval_isSome_of_mem {init : DomC} {vi w : Value} {s : Nat}
    {a : List Value} (hvi : init.mem vi = true) (hw : init.mem w = true)
    (ha : a[s]? = some w) :
    ∃ z, (neLit s vi).eval a = some z := by
  cases vi with
  | int x =>
      obtain ⟨y, rfl⟩ := DomC.mem_int_kind hvi hw
      have hsy : slotInt a s = some y := by simp [slotInt, ha, Value.intView]
      by_cases hyx : y = x
      · exact ⟨false, by
          rw [show neLit s (.int x) = posNe s x from rfl, eval_posNe]
          simp [hsy, hyx]⟩
      · exact ⟨true, (eval_posNe_iff a s x).mpr ⟨y, hsy, hyx⟩⟩
  | bool b =>
      obtain ⟨y, rfl⟩ := DomC.mem_bool_kind hvi hw
      exact ⟨y == !b, by simp [neLit, posBool, Literal.eval, Atom.eval, ha]⟩
  | setOfInt x => simp [DomC.mem] at hvi
  | array xs => simp [DomC.mem] at hvi

theorem eqLit_eval_true_iff_of_mem {init : DomC} {vi w : Value} {s : Nat}
    {a : List Value} (hvi : init.mem vi = true) (hw : init.mem w = true)
    (ha : a[s]? = some w) :
    (eqLit s vi).eval a = some true ↔ w = vi := by
  unfold eqLit
  rw [Literal.eval_negate_false_iff]
  have hne := neLit_eval_true_iff_of_mem (init := init) (vi := vi) (w := w) hvi hw ha
  obtain ⟨z, hz⟩ := neLit_eval_isSome_of_mem (init := init) (vi := vi) (w := w) hvi hw ha
  constructor
  · intro hfalse
    apply Classical.byContradiction
    intro h
    have htrue : (neLit s vi).eval a = some true := hne.mpr h
    rw [hfalse] at htrue
    cases htrue
  · intro heq
    have hnot : ¬ (neLit s vi).eval a = some true := by
      intro htrue
      exact (hne.mp htrue) heq
    rw [hz] at hnot ⊢
    cases z with
    | false => rfl
    | true => exact absurd rfl hnot

/-- `eqLit` is true on a domain fixed to its value. -/
theorem DomC.evalLit_eqLit_fixed_true {d : DomC} {s : Nat} {v : Value}
    (hWF : d.WF) (h : d.fixedValue = some v) :
    d.evalLit (eqLit s v) = some true := by
  unfold eqLit
  rw [DomC.evalLit_negate d hWF, DomC.evalLit_neLit_fixed_false hWF h]
  rfl

/-- `eqLit` is unassigned on an unfixed domain containing its value. -/
theorem DomC.evalLit_eqLit_none_of_not_fixed {d : DomC} {s : Nat} {v : Value}
    (hWF : d.WF) (hfv : d.fixedValue = none) (hmem : d.mem v = true) :
    d.evalLit (eqLit s v) = none := by
  unfold eqLit
  rw [DomC.evalLit_negate d hWF, DomC.evalLit_neLit_none_of_not_fixed hfv hmem]
  rfl

/-- `posNe` at an integer view that is the fixed value's view is false. -/
theorem DomC.evalLit_posNe_false_of_fixed_intView {d : DomC} (hWF : d.WF)
    {s : Nat} {c : Int} {v : Value} (h : d.fixedValue = some v)
    (hv : Value.intView v = some c) :
    d.evalLit (posNe s c) = some false := by
  cases v with
  | int x =>
      have hxc : x = c := by simpa [Value.intView] using hv
      subst hxc
      exact DomC.evalLit_posNe_of_fixed h (DomC.fixedValue_sound d hWF h).1
  | bool b =>
      have hc' : (if b then 1 else 0) = c := by simpa [Value.intView] using hv
      have hc : c = if b then 1 else 0 := hc'.symm
      subst hc
      have hm : d.mem (.bool b) = true := (DomC.fixedValue_sound d hWF h).1
      have hmiv : d.memIntView (if b then 1 else 0) = true :=
        DomC.memIntView_true_of_mem hm (by cases b <;> rfl)
      simp [DomC.evalLit, posNe, h, hmiv]
  | setOfInt x => simp [Value.intView] at hv
  | array xs => simp [Value.intView] at hv

/-- `posNe` at an integer view absent from an unfixed domain is true. -/
theorem DomC.evalLit_posNe_true_of_not_mem {d : DomC} {s : Nat} {c : Int}
    (hfv : d.fixedValue = none) (hm : d.memIntView c = false) :
    d.evalLit (posNe s c) = some true := by
  simp [DomC.evalLit, posNe, hfv, hm]

/-- `negNe` at an integer view absent from an unfixed domain is false. -/
theorem DomC.evalLit_negNe_false_of_not_mem {d : DomC} {s : Nat} {c : Int}
    (hfv : d.fixedValue = none) (hm : d.memIntView c = false) :
    d.evalLit (negNe s c) = some false := by
  simp [DomC.evalLit, negNe, hfv, hm]

/-- `negNe` at an integer view present in an unfixed domain is unassigned. -/
theorem DomC.evalLit_negNe_none_of_mem {d : DomC} {s : Nat} {c : Int}
    (hfv : d.fixedValue = none) (hm : d.memIntView c = true) :
    d.evalLit (negNe s c) = none := by
  simp [DomC.evalLit, negNe, hfv, hm]

/-- `posNe` at an integer view present in an unfixed domain is unassigned. -/
theorem DomC.evalLit_posNe_none_of_mem {d : DomC} {s : Nat} {c : Int}
    (hfv : d.fixedValue = none) (hm : d.memIntView c = true) :
    d.evalLit (posNe s c) = none := by
  simp [DomC.evalLit, posNe, hfv, hm]

/-- A Boolean pin is unassigned on an unfixed domain. -/
theorem DomC.evalLit_posBool_none_of_not_fixed {d : DomC} {s : Nat} {b : Bool}
    (hfv : d.fixedValue = none) :
    d.evalLit (posBool s b) = none := by
  simp [DomC.evalLit, posBool, hfv]

/-- A negative Boolean pin is unassigned on an unfixed domain. -/
theorem DomC.evalLit_negBool_none_of_not_fixed {d : DomC} {s : Nat} {b : Bool}
    (hfv : d.fixedValue = none) :
    d.evalLit (Literal.mk (.boolEq s b) false) = none := by
  simp [DomC.evalLit, hfv]

/-- A Boolean pin is false on a domain fixed to the other Boolean. -/
theorem DomC.evalLit_posBool_false_of_fixed_other {d : DomC} {s : Nat} {b c : Bool}
    (h : d.fixedValue = some (.bool c)) (hne : c ≠ b) :
    d.evalLit (posBool s b) = some false := by
  simp only [DomC.evalLit, posBool, h]
  cases c <;> cases b <;> simp_all

/-! ## Constant bounds -/

/-- Generic upper-bound propagator: a constraint entailing `x_i ≤ k`
prunes `i` to `≤ k` and reports a conflict when the current lower bound
already exceeds `k`.  The unit is `posLe i k`; we require an entailment
proof of the singleton clause. -/
def upperBoundPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (i : Nat) (k : Int) (hent : Entailed p [posLe i k]) : PropV2 p T :=
  { vars := #[i]
    events := #[(i, .bounds), (i, .fix)]
    run := fun view =>
      let d := view.doms.getD i DomC.empty
      match domBounds d with
      | none => .fix
      | some (lo, hi) =>
          if hi ≤ k then .fix
          else if lo > k then
            .conflict (EClause.ofLiterals p T [posLe i k] hent)
          else
            .prune #[(pLit (posLe i k), EClause.ofLiterals p T [posLe i k] hent)] }

theorem upperBoundPropWith_run_conflict (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (k : Int) (hent : Entailed p [posLe i k])
    (view : EngineView) {ec : EClause p T}
    (h : (upperBoundPropWith p T i k hent).run view = .conflict ec) :
    ∃ lo hi, (view.doms.getD i DomC.empty).lo? = some lo ∧
      (view.doms.getD i DomC.empty).hi? = some hi ∧ k < lo ∧
      T.decodeClause ec.lits = [posLe i k] ∧
      Entailed p [posLe i k] ∧
      ∀ q ∈ T.decodeClause ec.lits,
        (view.doms.getD (atomSlot q.atom) DomC.empty).evalLit q = some false := by
  unfold upperBoundPropWith at h
  dsimp only at h
  split at h
  · cases h
  · rename_i lo hi hb
    obtain ⟨hlo, hhi⟩ := domBounds_spec hb
    by_cases hhi' : hi ≤ k
    · rw [if_pos hhi'] at h
      cases h
    · rw [if_neg hhi'] at h
      by_cases hlo' : lo > k
      · rw [if_pos hlo'] at h
        cases h
        refine ⟨lo, hi, hlo, hhi, hlo', ?_, hent, ?_⟩
        · change T.decodeClause ([posLe i k].toArray.map pLit) = [posLe i k]
          exact LitTable.decodeClause_map_pLit T [posLe i k]
        · intro q hq
          change q ∈ T.decodeClause ([posLe i k].toArray.map pLit) at hq
          rw [LitTable.decodeClause_map_pLit] at hq
          simp only [List.mem_singleton] at hq
          subst hq
          exact evalLit_posLe_false_of_lo_gt hlo hhi hlo' hhi'
      · rw [if_neg hlo'] at h
        cases h

theorem upperBoundPropWith_run_prune (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (k : Int) (hent : Entailed p [posLe i k])
    (view : EngineView) {ps : Array (PLit × EClause p T)}
    (h : (upperBoundPropWith p T i k hent).run view = .prune ps) :
    ∃ lo hi, (view.doms.getD i DomC.empty).lo? = some lo ∧
      (view.doms.getD i DomC.empty).hi? = some hi ∧ lo ≤ k ∧ k < hi ∧
      (∀ q ∈ ps.toList, q.1.lit = posLe i k ∧
        T.decodeClause q.2.lits = [posLe i k] ∧
        Entailed p [posLe i k] ∧
        (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit = none ∧
        ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
          (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false) := by
  unfold upperBoundPropWith at h
  dsimp only at h
  split at h
  · cases h
  · rename_i lo hi hb
    obtain ⟨hlo, hhi⟩ := domBounds_spec hb
    by_cases hhi' : hi ≤ k
    · rw [if_pos hhi'] at h
      cases h
    · rw [if_neg hhi'] at h
      by_cases hlo' : lo > k
      · rw [if_pos hlo'] at h
        cases h
      · rw [if_neg hlo'] at h
        cases h
        refine ⟨lo, hi, hlo, hhi, by omega, by omega, ?_⟩
        intro q hq
        have hq' : q = (pLit (posLe i k), EClause.ofLiterals p T [posLe i k] hent) := by
          simpa using hq
        subst hq'
        refine ⟨rfl, ?_, hent, ?_, ?_⟩
        · change T.decodeClause ([posLe i k].toArray.map pLit) = [posLe i k]
          exact LitTable.decodeClause_map_pLit T [posLe i k]
        · exact evalLit_posLe_none hlo hhi (by omega) (by omega)
        · intro q' hq' hne
          change q' ∈ T.decodeClause ([posLe i k].toArray.map pLit) at hq'
          rw [LitTable.decodeClause_map_pLit] at hq'
          simp only [List.mem_singleton] at hq'
          exact absurd hq' hne

theorem upperBoundPropWith_run_fix_of_bounds_none
    (p : CompiledProblem DomConstraint) (T : LitTable) (i : Nat) (k : Int)
    (hent : Entailed p [posLe i k]) (view : EngineView)
    (h : domBounds (view.doms.getD i DomC.empty) = none) :
    (upperBoundPropWith p T i k hent).run view = .fix := by
  unfold upperBoundPropWith
  dsimp only
  rw [h]

/-- Generic lower-bound propagator: a constraint entailing `x_i ≥ k`
prunes `i` to `≥ k` and reports a conflict when the current upper bound
is below `k`. -/
def lowerBoundPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (i : Nat) (k : Int) (hent : Entailed p [negLe i k]) : PropV2 p T :=
  { vars := #[i]
    events := #[(i, .bounds), (i, .fix)]
    run := fun view =>
      let d := view.doms.getD i DomC.empty
      match domBounds d with
      | none => .fix
      | some (lo, hi) =>
          if lo > k then .fix
          else if hi ≤ k then
            .conflict (EClause.ofLiterals p T [negLe i k] hent)
          else
            .prune #[(pLit (negLe i k), EClause.ofLiterals p T [negLe i k] hent)] }

theorem lowerBoundPropWith_run_conflict (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (k : Int) (hent : Entailed p [negLe i k])
    (view : EngineView) {ec : EClause p T}
    (h : (lowerBoundPropWith p T i k hent).run view = .conflict ec) :
    ∃ lo hi, (view.doms.getD i DomC.empty).lo? = some lo ∧
      (view.doms.getD i DomC.empty).hi? = some hi ∧ hi ≤ k ∧
      T.decodeClause ec.lits = [negLe i k] ∧
      Entailed p [negLe i k] ∧
      ∀ q ∈ T.decodeClause ec.lits,
        (view.doms.getD (atomSlot q.atom) DomC.empty).evalLit q = some false := by
  unfold lowerBoundPropWith at h
  dsimp only at h
  split at h
  · cases h
  · rename_i lo hi hb
    obtain ⟨hlo, hhi⟩ := domBounds_spec hb
    by_cases hlo' : lo > k
    · rw [if_pos hlo'] at h
      cases h
    · rw [if_neg hlo'] at h
      by_cases hhi' : hi ≤ k
      · rw [if_pos hhi'] at h
        cases h
        refine ⟨lo, hi, hlo, hhi, hhi', ?_, hent, ?_⟩
        · change T.decodeClause ([negLe i k].toArray.map pLit) = [negLe i k]
          exact LitTable.decodeClause_map_pLit T [negLe i k]
        · intro q hq
          change q ∈ T.decodeClause ([negLe i k].toArray.map pLit) at hq
          rw [LitTable.decodeClause_map_pLit] at hq
          simp only [List.mem_singleton] at hq
          subst hq
          exact evalLit_negLe_false_of_hi_le hlo hhi hhi' hlo'
      · rw [if_neg hhi'] at h
        cases h

theorem lowerBoundPropWith_run_prune (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (k : Int) (hent : Entailed p [negLe i k])
    (view : EngineView) {ps : Array (PLit × EClause p T)}
    (h : (lowerBoundPropWith p T i k hent).run view = .prune ps) :
    ∃ lo hi, (view.doms.getD i DomC.empty).lo? = some lo ∧
      (view.doms.getD i DomC.empty).hi? = some hi ∧ lo ≤ k ∧ k < hi ∧
      (∀ q ∈ ps.toList, q.1.lit = negLe i k ∧
        T.decodeClause q.2.lits = [negLe i k] ∧
        Entailed p [negLe i k] ∧
        (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit = none ∧
        ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
          (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false) := by
  unfold lowerBoundPropWith at h
  dsimp only at h
  split at h
  · cases h
  · rename_i lo hi hb
    obtain ⟨hlo, hhi⟩ := domBounds_spec hb
    by_cases hlo' : lo > k
    · rw [if_pos hlo'] at h
      cases h
    · rw [if_neg hlo'] at h
      by_cases hhi' : hi ≤ k
      · rw [if_pos hhi'] at h
        cases h
      · rw [if_neg hhi'] at h
        cases h
        refine ⟨lo, hi, hlo, hhi, by omega, by omega, ?_⟩
        intro q hq
        have hq' : q = (pLit (negLe i k), EClause.ofLiterals p T [negLe i k] hent) := by
          simpa using hq
        subst hq'
        refine ⟨rfl, ?_, hent, ?_, ?_⟩
        · change T.decodeClause ([negLe i k].toArray.map pLit) = [negLe i k]
          exact LitTable.decodeClause_map_pLit T [negLe i k]
        · exact evalLit_negLe_none hlo hhi (by omega) (by omega)
        · intro q' hq' hne
          change q' ∈ T.decodeClause ([negLe i k].toArray.map pLit) at hq'
          rw [LitTable.decodeClause_map_pLit] at hq'
          simp only [List.mem_singleton] at hq'
          exact absurd hq' hne

theorem lowerBoundPropWith_run_fix_of_bounds_none
    (p : CompiledProblem DomConstraint) (T : LitTable) (i : Nat) (k : Int)
    (hent : Entailed p [negLe i k]) (view : EngineView)
    (h : domBounds (view.doms.getD i DomC.empty) = none) :
    (lowerBoundPropWith p T i k hent).run view = .fix := by
  unfold lowerBoundPropWith
  dsimp only
  rw [h]

/-! ### `int_le(x, c)` -/

theorem leConstHi_entailed (p : CompiledProblem DomConstraint) (i : Nat) (c : Int)
    (hmem : DomConstraint.leConstHi i c ∈ p.constraints) :
    Entailed p [posLe i c] := by
  intro a _ha hacc
  have hdc : (DomConstraint.leConstHi i c).satisfiedB a = true :=
    List.all_eq_true.mp hacc _ hmem
  obtain ⟨x, hx, hle⟩ := (DomConstraint.satisfiedB_iff _ _).mp hdc
  exact ⟨posLe i c, by simp,
    (eval_posLe_iff a i c).mpr ⟨x, by simp [slotInt, hx, Value.intView], hle⟩⟩

def leConstHiPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (i : Nat) (c : Int)
    (hmem : DomConstraint.leConstHi i c ∈ p.constraints) : PropV2 p T :=
  upperBoundPropWith p T i c (leConstHi_entailed p i c hmem)

theorem leConstHiPropWith_run_conflict (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (c : Int)
    (hmem : DomConstraint.leConstHi i c ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (leConstHiPropWith p T i c hmem).run view = .conflict ec) :
    ∃ lo hi, (view.doms.getD i DomC.empty).lo? = some lo ∧
      (view.doms.getD i DomC.empty).hi? = some hi ∧ c < lo ∧
      T.decodeClause ec.lits = [posLe i c] ∧
      Entailed p [posLe i c] ∧
      ∀ q ∈ T.decodeClause ec.lits,
        (view.doms.getD (atomSlot q.atom) DomC.empty).evalLit q = some false := by
  simpa [leConstHiPropWith] using
    upperBoundPropWith_run_conflict p T i c (leConstHi_entailed p i c hmem) view h

theorem leConstHiPropWith_run_prune (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (c : Int)
    (hmem : DomConstraint.leConstHi i c ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (leConstHiPropWith p T i c hmem).run view = .prune ps) :
    ∃ lo hi, (view.doms.getD i DomC.empty).lo? = some lo ∧
      (view.doms.getD i DomC.empty).hi? = some hi ∧ lo ≤ c ∧ c < hi ∧
      (∀ q ∈ ps.toList, q.1.lit = posLe i c ∧
        T.decodeClause q.2.lits = [posLe i c] ∧
        Entailed p [posLe i c] ∧
        (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit = none ∧
        ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
          (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false) := by
  simpa [leConstHiPropWith] using
    upperBoundPropWith_run_prune p T i c (leConstHi_entailed p i c hmem) view h

theorem leConstHiPropWith_conflict_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (c : Int)
    (hmem : DomConstraint.leConstHi i c ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (leConstHiPropWith p T i c hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  obtain ⟨_, _, _, _, _, hdec, hent, _⟩ :=
    leConstHiPropWith_run_conflict p T i c hmem view h
  rwa [hdec]

theorem leConstHiPropWith_conflict_lits_false (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (c : Int)
    (hmem : DomConstraint.leConstHi i c ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (leConstHiPropWith p T i c hmem).run view = .conflict ec) :
    ∀ q ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot q.atom) DomC.empty).evalLit q = some false := by
  obtain ⟨_, _, _, _, _, _, _, hfalse⟩ :=
    leConstHiPropWith_run_conflict p T i c hmem view h
  exact hfalse

theorem leConstHiPropWith_prune_reason_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (c : Int)
    (hmem : DomConstraint.leConstHi i c ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (leConstHiPropWith p T i c hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  obtain ⟨_, _, _, _, _, _, hfacts⟩ :=
    leConstHiPropWith_run_prune p T i c hmem view h
  obtain ⟨_, hdec, hent, _, _⟩ := hfacts q hq
  rw [hdec]
  exact hent

theorem leConstHiPropWith_prune_lit_none (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (c : Int)
    (hmem : DomConstraint.leConstHi i c ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (leConstHiPropWith p T i c hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false := by
  obtain ⟨_, _, _, _, _, _, hfacts⟩ :=
    leConstHiPropWith_run_prune p T i c hmem view h
  exact ⟨(hfacts q hq).2.2.2.1, (hfacts q hq).2.2.2.2⟩

theorem leConstHiPropWith_run_fix_of_bounds_none
    (p : CompiledProblem DomConstraint) (T : LitTable) (i : Nat) (c : Int)
    (hmem : DomConstraint.leConstHi i c ∈ p.constraints) (view : EngineView)
    (h : domBounds (view.doms.getD i DomC.empty) = none) :
    (leConstHiPropWith p T i c hmem).run view = .fix := by
  simpa [leConstHiPropWith] using
    upperBoundPropWith_run_fix_of_bounds_none p T i c
      (leConstHi_entailed p i c hmem) view h

/-! ### `int_le(c, x)` -/

theorem leConstLo_entailed (p : CompiledProblem DomConstraint) (i : Nat) (c : Int)
    (hmem : DomConstraint.leConstLo i c ∈ p.constraints) :
    Entailed p [negLe i (c - 1)] := by
  intro a _ha hacc
  have hdc : (DomConstraint.leConstLo i c).satisfiedB a = true :=
    List.all_eq_true.mp hacc _ hmem
  obtain ⟨x, hx, hle⟩ := (DomConstraint.satisfiedB_iff _ _).mp hdc
  exact ⟨negLe i (c - 1), by simp,
    (eval_negLe_iff a i (c - 1)).mpr
      ⟨x, by simp [slotInt, hx, Value.intView], by omega⟩⟩

def leConstLoPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (i : Nat) (c : Int)
    (hmem : DomConstraint.leConstLo i c ∈ p.constraints) : PropV2 p T :=
  lowerBoundPropWith p T i (c - 1) (leConstLo_entailed p i c hmem)

theorem leConstLoPropWith_run_conflict (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (c : Int)
    (hmem : DomConstraint.leConstLo i c ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (leConstLoPropWith p T i c hmem).run view = .conflict ec) :
    ∃ lo hi, (view.doms.getD i DomC.empty).lo? = some lo ∧
      (view.doms.getD i DomC.empty).hi? = some hi ∧ hi ≤ c - 1 ∧
      T.decodeClause ec.lits = [negLe i (c - 1)] ∧
      Entailed p [negLe i (c - 1)] ∧
      ∀ q ∈ T.decodeClause ec.lits,
        (view.doms.getD (atomSlot q.atom) DomC.empty).evalLit q = some false := by
  simpa [leConstLoPropWith] using
    lowerBoundPropWith_run_conflict p T i (c - 1)
      (leConstLo_entailed p i c hmem) view h

theorem leConstLoPropWith_run_prune (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (c : Int)
    (hmem : DomConstraint.leConstLo i c ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (leConstLoPropWith p T i c hmem).run view = .prune ps) :
    ∃ lo hi, (view.doms.getD i DomC.empty).lo? = some lo ∧
      (view.doms.getD i DomC.empty).hi? = some hi ∧
      lo ≤ c - 1 ∧ c - 1 < hi ∧
      (∀ q ∈ ps.toList, q.1.lit = negLe i (c - 1) ∧
        T.decodeClause q.2.lits = [negLe i (c - 1)] ∧
        Entailed p [negLe i (c - 1)] ∧
        (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit = none ∧
        ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
          (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false) := by
  simpa [leConstLoPropWith] using
    lowerBoundPropWith_run_prune p T i (c - 1)
      (leConstLo_entailed p i c hmem) view h

theorem leConstLoPropWith_conflict_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (c : Int)
    (hmem : DomConstraint.leConstLo i c ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (leConstLoPropWith p T i c hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  obtain ⟨_, _, _, _, _, hdec, hent, _⟩ :=
    leConstLoPropWith_run_conflict p T i c hmem view h
  rwa [hdec]

theorem leConstLoPropWith_conflict_lits_false (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (c : Int)
    (hmem : DomConstraint.leConstLo i c ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (leConstLoPropWith p T i c hmem).run view = .conflict ec) :
    ∀ q ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot q.atom) DomC.empty).evalLit q = some false := by
  obtain ⟨_, _, _, _, _, _, _, hfalse⟩ :=
    leConstLoPropWith_run_conflict p T i c hmem view h
  exact hfalse

theorem leConstLoPropWith_prune_reason_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (c : Int)
    (hmem : DomConstraint.leConstLo i c ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (leConstLoPropWith p T i c hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  obtain ⟨_, _, _, _, _, _, hfacts⟩ :=
    leConstLoPropWith_run_prune p T i c hmem view h
  obtain ⟨_, hdec, hent, _, _⟩ := hfacts q hq
  rw [hdec]
  exact hent

theorem leConstLoPropWith_prune_lit_none (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (c : Int)
    (hmem : DomConstraint.leConstLo i c ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (leConstLoPropWith p T i c hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false := by
  obtain ⟨_, _, _, _, _, _, hfacts⟩ :=
    leConstLoPropWith_run_prune p T i c hmem view h
  exact ⟨(hfacts q hq).2.2.2.1, (hfacts q hq).2.2.2.2⟩

theorem leConstLoPropWith_run_fix_of_bounds_none
    (p : CompiledProblem DomConstraint) (T : LitTable) (i : Nat) (c : Int)
    (hmem : DomConstraint.leConstLo i c ∈ p.constraints) (view : EngineView)
    (h : domBounds (view.doms.getD i DomC.empty) = none) :
    (leConstLoPropWith p T i c hmem).run view = .fix := by
  simpa [leConstLoPropWith] using
    lowerBoundPropWith_run_fix_of_bounds_none p T i (c - 1)
      (leConstLo_entailed p i c hmem) view h

/-! ### `int_lt(x, c)` -/

theorem ltConstHi_entailed (p : CompiledProblem DomConstraint) (i : Nat) (c : Int)
    (hmem : DomConstraint.ltConstHi i c ∈ p.constraints) :
    Entailed p [posLe i (c - 1)] := by
  intro a _ha hacc
  have hdc : (DomConstraint.ltConstHi i c).satisfiedB a = true :=
    List.all_eq_true.mp hacc _ hmem
  obtain ⟨x, hx, hlt⟩ := (DomConstraint.satisfiedB_iff _ _).mp hdc
  exact ⟨posLe i (c - 1), by simp,
    (eval_posLe_iff a i (c - 1)).mpr
      ⟨x, by simp [slotInt, hx, Value.intView], by omega⟩⟩

def ltConstHiPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (i : Nat) (c : Int)
    (hmem : DomConstraint.ltConstHi i c ∈ p.constraints) : PropV2 p T :=
  upperBoundPropWith p T i (c - 1) (ltConstHi_entailed p i c hmem)

theorem ltConstHiPropWith_run_conflict (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (c : Int)
    (hmem : DomConstraint.ltConstHi i c ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (ltConstHiPropWith p T i c hmem).run view = .conflict ec) :
    ∃ lo hi, (view.doms.getD i DomC.empty).lo? = some lo ∧
      (view.doms.getD i DomC.empty).hi? = some hi ∧ c - 1 < lo ∧
      T.decodeClause ec.lits = [posLe i (c - 1)] ∧
      Entailed p [posLe i (c - 1)] ∧
      ∀ q ∈ T.decodeClause ec.lits,
        (view.doms.getD (atomSlot q.atom) DomC.empty).evalLit q = some false := by
  simpa [ltConstHiPropWith] using
    upperBoundPropWith_run_conflict p T i (c - 1)
      (ltConstHi_entailed p i c hmem) view h

theorem ltConstHiPropWith_run_prune (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (c : Int)
    (hmem : DomConstraint.ltConstHi i c ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (ltConstHiPropWith p T i c hmem).run view = .prune ps) :
    ∃ lo hi, (view.doms.getD i DomC.empty).lo? = some lo ∧
      (view.doms.getD i DomC.empty).hi? = some hi ∧
      lo ≤ c - 1 ∧ c - 1 < hi ∧
      (∀ q ∈ ps.toList, q.1.lit = posLe i (c - 1) ∧
        T.decodeClause q.2.lits = [posLe i (c - 1)] ∧
        Entailed p [posLe i (c - 1)] ∧
        (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit = none ∧
        ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
          (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false) := by
  simpa [ltConstHiPropWith] using
    upperBoundPropWith_run_prune p T i (c - 1)
      (ltConstHi_entailed p i c hmem) view h

theorem ltConstHiPropWith_conflict_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (c : Int)
    (hmem : DomConstraint.ltConstHi i c ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (ltConstHiPropWith p T i c hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  obtain ⟨_, _, _, _, _, hdec, hent, _⟩ :=
    ltConstHiPropWith_run_conflict p T i c hmem view h
  rwa [hdec]

theorem ltConstHiPropWith_conflict_lits_false (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (c : Int)
    (hmem : DomConstraint.ltConstHi i c ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (ltConstHiPropWith p T i c hmem).run view = .conflict ec) :
    ∀ q ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot q.atom) DomC.empty).evalLit q = some false := by
  obtain ⟨_, _, _, _, _, _, _, hfalse⟩ :=
    ltConstHiPropWith_run_conflict p T i c hmem view h
  exact hfalse

theorem ltConstHiPropWith_prune_reason_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (c : Int)
    (hmem : DomConstraint.ltConstHi i c ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (ltConstHiPropWith p T i c hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  obtain ⟨_, _, _, _, _, _, hfacts⟩ :=
    ltConstHiPropWith_run_prune p T i c hmem view h
  obtain ⟨_, hdec, hent, _, _⟩ := hfacts q hq
  rw [hdec]
  exact hent

theorem ltConstHiPropWith_prune_lit_none (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (c : Int)
    (hmem : DomConstraint.ltConstHi i c ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (ltConstHiPropWith p T i c hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false := by
  obtain ⟨_, _, _, _, _, _, hfacts⟩ :=
    ltConstHiPropWith_run_prune p T i c hmem view h
  exact ⟨(hfacts q hq).2.2.2.1, (hfacts q hq).2.2.2.2⟩

theorem ltConstHiPropWith_run_fix_of_bounds_none
    (p : CompiledProblem DomConstraint) (T : LitTable) (i : Nat) (c : Int)
    (hmem : DomConstraint.ltConstHi i c ∈ p.constraints) (view : EngineView)
    (h : domBounds (view.doms.getD i DomC.empty) = none) :
    (ltConstHiPropWith p T i c hmem).run view = .fix := by
  simpa [ltConstHiPropWith] using
    upperBoundPropWith_run_fix_of_bounds_none p T i (c - 1)
      (ltConstHi_entailed p i c hmem) view h

/-! ### `int_lt(c, x)` -/

theorem ltConstLo_entailed (p : CompiledProblem DomConstraint) (i : Nat) (c : Int)
    (hmem : DomConstraint.ltConstLo i c ∈ p.constraints) :
    Entailed p [negLe i c] := by
  intro a _ha hacc
  have hdc : (DomConstraint.ltConstLo i c).satisfiedB a = true :=
    List.all_eq_true.mp hacc _ hmem
  obtain ⟨x, hx, hlt⟩ := (DomConstraint.satisfiedB_iff _ _).mp hdc
  exact ⟨negLe i c, by simp,
    (eval_negLe_iff a i c).mpr ⟨x, by simp [slotInt, hx, Value.intView], hlt⟩⟩

def ltConstLoPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (i : Nat) (c : Int)
    (hmem : DomConstraint.ltConstLo i c ∈ p.constraints) : PropV2 p T :=
  lowerBoundPropWith p T i c (ltConstLo_entailed p i c hmem)

theorem ltConstLoPropWith_run_conflict (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (c : Int)
    (hmem : DomConstraint.ltConstLo i c ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (ltConstLoPropWith p T i c hmem).run view = .conflict ec) :
    ∃ lo hi, (view.doms.getD i DomC.empty).lo? = some lo ∧
      (view.doms.getD i DomC.empty).hi? = some hi ∧ hi ≤ c ∧
      T.decodeClause ec.lits = [negLe i c] ∧
      Entailed p [negLe i c] ∧
      ∀ q ∈ T.decodeClause ec.lits,
        (view.doms.getD (atomSlot q.atom) DomC.empty).evalLit q = some false := by
  simpa [ltConstLoPropWith] using
    lowerBoundPropWith_run_conflict p T i c (ltConstLo_entailed p i c hmem) view h

theorem ltConstLoPropWith_run_prune (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (c : Int)
    (hmem : DomConstraint.ltConstLo i c ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (ltConstLoPropWith p T i c hmem).run view = .prune ps) :
    ∃ lo hi, (view.doms.getD i DomC.empty).lo? = some lo ∧
      (view.doms.getD i DomC.empty).hi? = some hi ∧ lo ≤ c ∧ c < hi ∧
      (∀ q ∈ ps.toList, q.1.lit = negLe i c ∧
        T.decodeClause q.2.lits = [negLe i c] ∧
        Entailed p [negLe i c] ∧
        (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit = none ∧
        ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
          (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false) := by
  simpa [ltConstLoPropWith] using
    lowerBoundPropWith_run_prune p T i c (ltConstLo_entailed p i c hmem) view h

theorem ltConstLoPropWith_conflict_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (c : Int)
    (hmem : DomConstraint.ltConstLo i c ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (ltConstLoPropWith p T i c hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  obtain ⟨_, _, _, _, _, hdec, hent, _⟩ :=
    ltConstLoPropWith_run_conflict p T i c hmem view h
  rwa [hdec]

theorem ltConstLoPropWith_conflict_lits_false (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (c : Int)
    (hmem : DomConstraint.ltConstLo i c ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (ltConstLoPropWith p T i c hmem).run view = .conflict ec) :
    ∀ q ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot q.atom) DomC.empty).evalLit q = some false := by
  obtain ⟨_, _, _, _, _, _, _, hfalse⟩ :=
    ltConstLoPropWith_run_conflict p T i c hmem view h
  exact hfalse

theorem ltConstLoPropWith_prune_reason_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (c : Int)
    (hmem : DomConstraint.ltConstLo i c ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (ltConstLoPropWith p T i c hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  obtain ⟨_, _, _, _, _, _, hfacts⟩ :=
    ltConstLoPropWith_run_prune p T i c hmem view h
  obtain ⟨_, hdec, hent, _, _⟩ := hfacts q hq
  rw [hdec]
  exact hent

theorem ltConstLoPropWith_prune_lit_none (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (c : Int)
    (hmem : DomConstraint.ltConstLo i c ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (ltConstLoPropWith p T i c hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false := by
  obtain ⟨_, _, _, _, _, _, hfacts⟩ :=
    ltConstLoPropWith_run_prune p T i c hmem view h
  exact ⟨(hfacts q hq).2.2.2.1, (hfacts q hq).2.2.2.2⟩

theorem ltConstLoPropWith_run_fix_of_bounds_none
    (p : CompiledProblem DomConstraint) (T : LitTable) (i : Nat) (c : Int)
    (hmem : DomConstraint.ltConstLo i c ∈ p.constraints) (view : EngineView)
    (h : domBounds (view.doms.getD i DomC.empty) = none) :
    (ltConstLoPropWith p T i c hmem).run view = .fix := by
  simpa [ltConstLoPropWith] using
    lowerBoundPropWith_run_fix_of_bounds_none p T i c
      (ltConstLo_entailed p i c hmem) view h


end LeanFzn.Engine

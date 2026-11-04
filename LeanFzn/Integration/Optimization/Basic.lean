/-
File: LeanFzn/Integration/Optimization/Basic.lean

Purpose:
  Certified branch-and-bound (PLAN.md task O2a).  The driver is
  parametric in a certified problem-level solver interface
  (`CertSolver`: SAT soundness and UNSAT completeness over
  `allAssigns`); the chronological certified solver is one instance
  in the legacy layer. Core uses the same soundness interface and may
  return an incomplete run. This module imports no search implementation.

  `optLoop` solves the satisfy problem, reads the objective value `v`
  of the returned assignment, re-solves the problem extended with
  `spec.improveBound v`, and repeats.  Termination is fuel-free: the
  measure is the number of values of the objective slot's finite
  domain that still improve on the current bound, which strictly
  decreases (`meas_decr`).

  Theorems: every emitted solution satisfies the source model, the
  objective strictly improves along the sequence, a completed run's
  last solution is an optimal `IsSolution` (from the UNSAT of the
  improving bound), a completed run with no solution proves the source
  model unsatisfiable, and a gate-passing run always completes.
-/

import LeanFzn.Compiler.Proofs.Normalize
import LeanFzn.Solver.Propagation.FrameFilter
import LeanFzn.Compiler.Objective
import LeanFzn.Compiler.Proofs.Objective

namespace LeanFzn.Integration
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Compiler
open LeanFzn.Semantics.Globals LeanFzn.Solver.Propagation LeanFzn.Solver.Core LeanFzn.Compiler.Domains

/-- Enumeration membership from compact-domain membership. -/
private theorem enumMem_of_domMem {d : Domain} {v : Value} (h : v ∈ d) :
    v ∈ Dom.enum d :=
  (by
    simpa [LeanFzn.Solver.Propagation.domElems_eq_enum] using
      (LeanFzn.Solver.Core.DomainLike.mem_iff d v).mp h)

/-! ## The certified solver interface -/

/-- Verdicts of a problem-level certified solver. -/
inductive CertVerdict where
  | sat (a : List Value)
  | unsat
  | fail
  deriving Repr

/-- A certified problem-level solver: SAT answers are accepted
    assignments of the box, UNSAT answers exclude every assignment of the
    box, and `fail` is excluded whenever the (extension-stable) `gate`
    holds.  `solveWith` receives the previous round's incumbent for
    solution-guided value presentations (F3); `solve` is its
    no-previous-solution instance. -/
structure CertSolver where
  solve : CompiledProblem DomConstraint → CertVerdict
  solveWith : Option (List Value) → CompiledProblem DomConstraint → CertVerdict
  gate : CompiledProblem DomConstraint → Bool
  sat_sound : ∀ p a, solve p = .sat a →
    a ∈ allAssigns p.domains ∧ accepts p a = true
  solveWith_sat : ∀ p prev a, solveWith prev p = .sat a →
    a ∈ allAssigns p.domains ∧ accepts p a = true
  unsat_complete : ∀ p, solve p = .unsat →
    ∀ b ∈ allAssigns p.domains, accepts p b = false
  solveWith_unsat : ∀ p prev, solveWith prev p = .unsat →
    ∀ b ∈ allAssigns p.domains, accepts p b = false
  gate_add : ∀ p c, gate (p.addConstraint c) = gate p
  total : ∀ p, gate p = true → solve p ≠ .fail
  solveWith_total : ∀ p prev, gate p = true → solveWith prev p ≠ .fail

/-! ## Improvement order and measure -/

/-- `w` strictly improves on `b` in direction `dir`. -/
def betterB (dir : OptDir) (w b : Int) : Bool :=
  match dir with
  | .minimize => decide (w < b)
  | .maximize => decide (b < w)

theorem betterB_trans {dir : OptDir} {x y z : Int}
    (h1 : betterB dir x y = true) (h2 : betterB dir y z = true) :
    betterB dir x z = true := by
  cases dir <;> simp [betterB] at * <;> omega

theorem betterB_irrefl (dir : OptDir) (x : Int) : betterB dir x x = false := by
  cases dir <;> simp [betterB]

/-- The problem solved under the bound `bo` (none: no bound yet). -/
def curP (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec) :
    Option Int → CompiledProblem DomConstraint
  | none => p0
  | some b => p0.addConstraint (spec.improveBound b)

theorem curP_domains (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec)
    (bo : Option Int) : (curP p0 spec bo).domains = p0.domains := by
  cases bo <;> rfl

theorem accepts_add {p : CompiledProblem DomConstraint} {c : DomConstraint}
    {a : List Value} :
    accepts (p.addConstraint c) a = true ↔
      accepts p a = true ∧ c.satisfiedB a = true := by
  simp only [accepts, CompiledProblem.addConstraint, List.all_append,
    List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]

/-- An assignment accepted under the bound `b` is accepted by the base
    problem and reads a strictly better objective. -/
theorem accepts_improve {p : CompiledProblem DomConstraint} {spec : ObjectiveSpec}
    {b : Int} {a : List Value} {w : Int}
    (h : accepts (p.addConstraint (spec.improveBound b)) a = true)
    (hw : a[spec.slot]? = some (.int w)) :
    accepts p a = true ∧ betterB spec.dir w b = true := by
  obtain ⟨h1, h2⟩ := accepts_add.mp h
  refine ⟨h1, ?_⟩
  rw [DomConstraint.satisfiedB_iff] at h2
  cases hd : spec.dir <;>
    simp only [ObjectiveSpec.improveBound, hd, DomConstraint.SatisfiedBy,
      betterB] at h2 ⊢
  · obtain ⟨j, hj, hle⟩ := h2
    rw [hw] at hj
    cases hj
    simp; omega
  · obtain ⟨j, hj, hle⟩ := h2
    rw [hw] at hj
    cases hj
    simp; omega

theorem accepts_curP {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec}
    {bo : Option Int} {a : List Value}
    (h : accepts (curP p0 spec bo) a = true) :
    accepts p0 a = true ∧ ∀ b w, bo = some b →
      a[spec.slot]? = some (.int w) → betterB spec.dir w b = true := by
  cases bo with
  | none => exact ⟨h, fun b w hb => by cases hb⟩
  | some b0 =>
      refine ⟨(accepts_add.mp h).1, ?_⟩
      intro b w hb hw
      cases hb
      exact (accepts_improve h hw).2

/-- Domain values that still improve on the bound. -/
def okVal (dir : OptDir) (b : Int) : Value → Bool
  | .int w => betterB dir w b
  | _ => false

/-- The termination measure: the number of admissible objective values. -/
def meas (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec) :
    Option Int → Nat
  | none => (Dom.enum (p0.domains.getD spec.slot Dom.empty)).length + 1
  | some b =>
      ((Dom.enum (p0.domains.getD spec.slot Dom.empty)).filter
        (okVal spec.dir b)).length

theorem filter_mono_len {α : Type} (l : List α) (p q : α → Bool)
    (hpq : ∀ x ∈ l, p x = true → q x = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons y ys ih =>
      have ih' := ih (fun x hx => hpq x (List.mem_cons_of_mem _ hx))
      have hy := hpq y (List.mem_cons_self ..)
      by_cases hp : p y = true
      · have hq := hy hp
        simp [hp, hq]; omega
      · by_cases hq : q y = true
        · simp [hp, hq]; omega
        · simp [hp, hq]; omega

theorem filter_strict {α : Type} (l : List α) (p q : α → Bool)
    (hpq : ∀ x ∈ l, p x = true → q x = true)
    (hw : ∃ x ∈ l, q x = true ∧ p x = false) :
    (l.filter p).length < (l.filter q).length := by
  induction l with
  | nil => obtain ⟨x, hx, _⟩ := hw; cases hx
  | cons y ys ih =>
      obtain ⟨x, hx, hqx, hpx⟩ := hw
      have hpq' : ∀ z ∈ ys, p z = true → q z = true :=
        fun z hz => hpq z (List.mem_cons_of_mem _ hz)
      have hy := hpq y (List.mem_cons_self ..)
      have hmono := filter_mono_len ys p q hpq'
      by_cases hp : p y = true
      · have hq := hy hp
        have hxs : x ∈ ys := by
          rcases List.mem_cons.mp hx with rfl | h
          · rw [hp] at hpx; cases hpx
          · exact h
        have := ih hpq' ⟨x, hxs, hqx, hpx⟩
        simp [hp, hq]; omega
      · by_cases hq : q y = true
        · simp [hp, hq]; omega
        · have hxs : x ∈ ys := by
            rcases List.mem_cons.mp hx with rfl | h
            · exact absurd hqx hq
            · exact h
          have := ih hpq' ⟨x, hxs, hqx, hpx⟩
          simp [hp, hq]; omega

theorem meas_decr {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec}
    {bo : Option Int} {a : List Value} {v : Int}
    (hmem : a ∈ allAssigns p0.domains)
    (hacc : accepts (curP p0 spec bo) a = true)
    (hv : a[spec.slot]? = some (.int v)) :
    meas p0 spec (some v) < meas p0 spec bo := by
  have hfit : LeanFzn.Solver.Core.Assignment.Fits p0.domains a :=
    LeanFzn.Solver.Propagation.allAssigns_fits p0.domains a hmem
  have hin : Value.int v ∈ Dom.enum (p0.domains.getD spec.slot Dom.empty) :=
    enumMem_of_domMem (by
      simpa only [LeanFzn.Solver.Propagation.domEmpty_eq] using hfit.2 spec.slot _ hv)
  obtain ⟨_, hb⟩ := accepts_curP hacc
  cases bo with
  | none =>
      simp only [meas]
      have := List.length_filter_le (okVal spec.dir v)
        (Dom.enum (p0.domains.getD spec.slot Dom.empty))
      omega
  | some b =>
      have hbv := hb b v rfl hv
      simp only [meas]
      apply filter_strict
      · intro x _ hx
        cases x <;> simp only [okVal] at hx ⊢ <;> try exact hx
        exact betterB_trans hx hbv
      · exact ⟨.int v, hin, by simp [okVal, hbv], by simp [okVal, betterB_irrefl]⟩

/-! ## The driver -/

/-- The outcome of a branch-and-bound run: the emitted solutions in
    order (assignment with its objective value), whether the run
    completed (the last bound was proved infeasible), and the bound
    under which the final solve was made. -/
structure OptRun where
  sols : List (List Value × Int)
  complete : Bool
  lastBound : Option Int

/-- Branch and bound over a certified solver, threading the previous
    incumbent into the next round's solve (`--val=incumbent`).  Fuel-free:
    well-founded on `meas`, which does not mention the incumbent. -/
def optLoopWith (S : CertSolver) (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) (prev : Option (List Value))
    (bo : Option Int) : OptRun :=
  match hs : S.solveWith prev (curP p0 spec bo) with
  | .unsat => ⟨[], true, bo⟩
  | .fail => ⟨[], false, bo⟩
  | .sat a =>
      match hv : a[spec.slot]? with
      | some (.int v) =>
          let r := optLoopWith S p0 spec (some a) (some v)
          ⟨(a, v) :: r.sols, r.complete, r.lastBound⟩
      | _ => ⟨[], false, bo⟩
termination_by meas p0 spec bo
decreasing_by
  have h := S.solveWith_sat _ _ _ hs
  rw [curP_domains] at h
  exact meas_decr h.1 h.2 hv

/-- Branch and bound over a certified solver from the root (no previous
    incumbent). -/
def optLoop (S : CertSolver) (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) (bo : Option Int) : OptRun :=
  optLoopWith S p0 spec none bo

/-- The certified optimizer for a source model. -/
def optimizeCertified (S : CertSolver) (m : Model) :
    Except String (CompiledProblem DomConstraint × OptRun) :=
  match compileModelOpt m with
  | .error e => .error e
  | .ok (p, spec) => .ok (p, optLoop S p spec none)

/-- Loop invariants. -/
structure LoopInv (S : CertSolver) (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) (bo : Option Int) (r : OptRun) : Prop where
  sound : ∀ s ∈ r.sols, s.1 ∈ allAssigns p0.domains ∧ accepts p0 s.1 = true ∧
    s.1[spec.slot]? = some (.int s.2) ∧
    ∀ b, bo = some b → betterB spec.dir s.2 b = true
  pairwise : r.sols.Pairwise (fun s t => betterB spec.dir t.2 s.2 = true)
  optimal : r.complete = true →
    ∀ b ∈ allAssigns p0.domains, accepts (curP p0 spec r.lastBound) b = false
  nil_bound : r.sols = [] → r.lastBound = bo
  last_bound : ∀ s, r.sols.getLast? = some s → r.lastBound = some s.2

theorem optLoopWith_inv (S : CertSolver) (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) :
    ∀ n prev bo, meas p0 spec bo = n →
      LoopInv S p0 spec bo (optLoopWith S p0 spec prev bo) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro prev bo hn
    rw [optLoopWith]
    split
    · rename_i hs
      refine ⟨by simp, by simp, fun _ b hb => ?_, fun _ => rfl, by simp⟩
      rw [← curP_domains p0 spec bo] at hb
      exact S.solveWith_unsat _ _ hs b hb
    · exact ⟨by simp, by simp, by simp, fun _ => rfl, by simp⟩
    · rename_i a hs
      split
      · rename_i v hv
        have hsat := S.solveWith_sat _ _ _ hs
        rw [curP_domains] at hsat
        obtain ⟨hmem, hacc⟩ := hsat
        have hlt := meas_decr hmem hacc hv
        have IH := ih _ (hn ▸ hlt) (some a) (some v) rfl
        obtain ⟨hacc0, hbo⟩ := accepts_curP hacc
        refine ⟨?_, ?_, IH.optimal, ?_, ?_⟩
        · intro s hs'
          rcases List.mem_cons.mp hs' with rfl | hr
          · exact ⟨hmem, hacc0, hv, fun b hb => hbo b _ hb hv⟩
          · obtain ⟨h1, h2, h3, h4⟩ := IH.sound s hr
            exact ⟨h1, h2, h3, fun b hb =>
              betterB_trans (h4 v rfl) (hbo b _ hb hv)⟩
        · refine List.pairwise_cons.mpr ⟨fun t ht => ?_, IH.pairwise⟩
          exact (IH.sound t ht).2.2.2 v rfl
        · intro h; simp at h
        · intro t ht
          dsimp only at ht ⊢
          by_cases hnil : (optLoopWith S p0 spec (some a) (some v)).sols = []
          · rw [hnil] at ht
            simp at ht
            subst ht
            exact IH.nil_bound hnil
          · apply IH.last_bound
            rw [List.getLast?_cons] at ht
            obtain ⟨x, hx⟩ : ∃ x, (optLoopWith S p0 spec (some a) (some v)).sols.getLast? = some x := by
              cases hl : (optLoopWith S p0 spec (some a) (some v)).sols.getLast? with
              | none => exact absurd (List.getLast?_eq_none_iff.mp hl) hnil
              | some x => exact ⟨x, rfl⟩
            rw [hx] at ht ⊢
            simpa using ht
      · exact ⟨by simp, by simp, by simp, fun _ => rfl, by simp⟩

/-- Loop invariants for the root run. -/
theorem optLoop_inv (S : CertSolver) (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) :
    ∀ n bo, meas p0 spec bo = n → LoopInv S p0 spec bo (optLoop S p0 spec bo) := by
  intro n bo hn
  exact optLoopWith_inv S p0 spec n none bo hn

theorem gate_curP (S : CertSolver) (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) (bo : Option Int) :
    S.gate (curP p0 spec bo) = S.gate p0 := by
  cases bo with
  | none => rfl
  | some b => exact S.gate_add _ _

/-- Totality: if the gate holds and every accepted assignment reads an
    integer at the objective slot, the run completes. -/
theorem optLoopWith_complete (S : CertSolver) (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) (hg : S.gate p0 = true)
    (hread : ∀ a ∈ allAssigns p0.domains, accepts p0 a = true →
      ∃ i, a[spec.slot]? = some (.int i)) :
    ∀ n prev bo, meas p0 spec bo = n →
      (optLoopWith S p0 spec prev bo).complete = true := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro prev bo hn
    rw [optLoopWith]
    split
    · rfl
    · rename_i hs
      exact absurd hs (S.solveWith_total _ _ (by rw [gate_curP]; exact hg))
    · rename_i a hs
      split
      · rename_i v hv
        have hsat := S.solveWith_sat _ _ _ hs
        rw [curP_domains] at hsat
        exact ih _ (hn ▸ meas_decr hsat.1 hsat.2 hv) (some a) (some v) rfl
      · rename_i hne
        have hsat := S.solveWith_sat _ _ _ hs
        rw [curP_domains] at hsat
        obtain ⟨i, hi⟩ := hread a hsat.1 (accepts_curP hsat.2).1
        exact absurd hi (by intro h; exact hne i h)

/-- Totality for the root run. -/
theorem optLoop_complete (S : CertSolver) (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) (hg : S.gate p0 = true)
    (hread : ∀ a ∈ allAssigns p0.domains, accepts p0 a = true →
      ∃ i, a[spec.slot]? = some (.int i)) :
    ∀ n bo, meas p0 spec bo = n → (optLoop S p0 spec bo).complete = true := by
  intro n bo hn
  exact optLoopWith_complete S p0 spec hg hread n none bo hn

/-! ## Source-level theorems -/

theorem optimizeCertified_inv {S : CertSolver} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun}
    (h : optimizeCertified S m = .ok (p, run)) :
    ∃ spec, compileModelOpt m = .ok (p, spec) ∧ run = optLoop S p spec none := by
  unfold optimizeCertified at h
  cases hc : compileModelOpt m with
  | error e => rw [hc] at h; cases h
  | ok r =>
      obtain ⟨p', spec⟩ := r
      rw [hc] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨spec, rfl, rfl⟩

/-- Every emitted solution is a store satisfying the source model, with
    the reported objective value. -/
theorem optimizeCertified_solution_sound {S : CertSolver} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun}
    (h : optimizeCertified S m = .ok (p, run)) (hwf : WellFormed fullSig m)
    {s : List Value × Int} (hs : s ∈ run.sols) :
    Satisfies fullSig fullInterp m (p.toStore s.1) ∧
    LeanFzn.Semantics.ParamHonest m (p.toStore s.1) ∧
    m.solve.objective (p.toStore s.1) = some s.2 := by
  obtain ⟨spec, hc, rfl⟩ := optimizeCertified_inv h
  have hinv := optLoop_inv S p spec _ none rfl
  obtain ⟨hmem, hacc, hv, _⟩ := hinv.sound s hs
  obtain ⟨hsat, hpar, i, hi, hai⟩ := compileOpt_exact hc hwf hmem hacc
  rw [hv] at hai
  have : s.2 = i := by simpa using hai
  subst this
  exact ⟨⟨hwf, hsat⟩, hpar, hi⟩

/-- The objective strictly improves along the emitted sequence. -/
theorem optimizeCertified_improving {S : CertSolver} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun}
    (h : optimizeCertified S m = .ok (p, run)) :
    ∃ spec : ObjectiveSpec,
      run.sols.Pairwise (fun s t => betterB spec.dir t.2 s.2 = true) := by
  obtain ⟨spec, hc, rfl⟩ := optimizeCertified_inv h
  exact ⟨spec, (optLoop_inv S p spec _ none rfl).pairwise⟩

/-- A completed run's last solution is an optimal solution of the
    source model (the UNSAT of the improving bound). -/
theorem optimizeCertified_optimal {S : CertSolver} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun}
    (h : optimizeCertified S m = .ok (p, run)) (hwf : WellFormed fullSig m)
    (hcomp : run.complete = true) {s : List Value × Int}
    (hlast : run.sols.getLast? = some s) :
    IsSolution fullSig fullInterp m (p.toStore s.1) := by
  obtain ⟨spec, hc, rfl⟩ := optimizeCertified_inv h
  have hinv := optLoop_inv S p spec _ none rfl
  have hs : s ∈ (optLoop S p spec none).sols := List.mem_of_getLast? hlast
  obtain ⟨hmem, hacc, hv, _⟩ := hinv.sound s hs
  have hlb := hinv.last_bound s hlast
  have hopt := hinv.optimal hcomp
  rw [hlb] at hopt
  exact compileOpt_optimal hc hwf hmem hacc hv hopt

/-- **Bounded B&B optimality (PLAN F6 T2).**  A completed run's last
    solution is an optimal source solution, for an arbitrary previous
    incumbent and initial bound.  This generalizes
    `optimizeCertified_optimal` from `prev = none`, `bo = none` to the
    initial bound a primal phase passes to the certified loop. -/
theorem optLoopWith_optimal {S : CertSolver} {m : Model}
    {p : CompiledProblem DomConstraint} {spec : ObjectiveSpec}
    (hc : compileModelOpt m = .ok (p, spec)) (hwf : WellFormed fullSig m)
    {prev : Option (List Value)} {bo : Option Int} {run : OptRun}
    (hrun : run = optLoopWith S p spec prev bo)
    (hcomp : run.complete = true) {s : List Value × Int}
    (hlast : run.sols.getLast? = some s) :
    IsSolution fullSig fullInterp m (p.toStore s.1) := by
  rw [hrun] at hcomp hlast
  have hinv := optLoopWith_inv S p spec _ prev bo rfl
  have hs : s ∈ (optLoopWith S p spec prev bo).sols :=
    List.mem_of_getLast? hlast
  obtain ⟨hmem, hacc, hv, _⟩ := hinv.sound s hs
  have hlb := hinv.last_bound s hlast
  have hopt := hinv.optimal hcomp
  rw [hlb] at hopt
  exact compileOpt_optimal hc hwf hmem hacc hv hopt

/-- A completed run without solutions proves the source model has no
    parameter-honest satisfying store. -/
theorem optimizeCertified_unsat {S : CertSolver} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun}
    (h : optimizeCertified S m = .ok (p, run)) (hwf : WellFormed fullSig m)
    (hcomp : run.complete = true) (hnil : run.sols = []) :
    ¬ ∃ store, Satisfies fullSig fullInterp m store ∧
      LeanFzn.Semantics.ParamHonest m store := by
  obtain ⟨spec, hc, rfl⟩ := optimizeCertified_inv h
  have hinv := optLoop_inv S p spec _ none rfl
  have hlb := hinv.nil_bound hnil
  have hopt := hinv.optimal hcomp
  rw [hlb] at hopt
  rintro ⟨store, hs, hph⟩
  obtain ⟨b, hb, hbacc, _⟩ := compileOpt_covers hc hwf hs.2 hph
  have : accepts p b = false := hopt b hb
  rw [hbacc] at this
  cases this

/-- Totality: with the solver gate satisfied the run always completes
    (never `fail`, never an unreadable objective). -/
theorem optimizeCertified_total {S : CertSolver} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun}
    (h : optimizeCertified S m = .ok (p, run)) (hwf : WellFormed fullSig m)
    (hg : S.gate p = true) : run.complete = true := by
  obtain ⟨spec, hc, rfl⟩ := optimizeCertified_inv h
  refine optLoop_complete S p spec hg ?_ _ none rfl
  intro a hmem hacc
  obtain ⟨_, _, i, _, hai⟩ := compileOpt_exact hc hwf hmem hacc
  exact ⟨i, hai⟩

/-! ## Streaming emission (PLAN.md B1)

`optLoopEmit` is the pure emit-trace driver: the exact recursion of
`optLoop`, additionally threading the `f`-images of each found solution
in order.  `optimizeStreamLoop` is its IO transliteration: the same
recursion, calling `emit` once per improving solution before the next
solve.  The correspondence theorem `optimizeStreamLoop_trace` states
that the emissions are exactly the `f`-images of the pure run's
solutions, in the same order. -/

/-- Emit a list of values in order. -/
def emitAll {α : Type} (emit : α → IO Unit) : List α → IO Unit
  | [] => pure ()
  | x :: xs => emit x >>= fun _ => emitAll emit xs

private theorem est_bind_assoc {ε σ α β γ : Type} (x : EST ε σ α)
    (f : α → EST ε σ β) (g : β → EST ε σ γ) :
    (x >>= f) >>= g = x >>= fun y => f y >>= g := by
  funext s
  dsimp only [Bind.bind, EST.bind]
  cases h : x s <;> rfl

private theorem io_bind_assoc {α β γ : Type} (x : IO α) (f : α → IO β)
    (g : β → IO γ) :
    (x >>= f) >>= g = x >>= fun y => f y >>= g :=
  est_bind_assoc x f g

private theorem io_pure_bind {α β : Type} (a : α) (f : α → IO β) :
    (pure a >>= f) = f a := rfl

/-- Pure emit-trace driver with the previous incumbent threaded to the next
    solve: the exact recursion of `optLoopWith`, threading the `f`-images of
    the found solutions in order. -/
def optLoopEmitWith {α : Type} (S : CertSolver)
    (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec)
    (prev : Option (List Value)) (bo : Option Int) (f : List Value → α) :
    OptRun × List α :=
  match hs : S.solveWith prev (curP p0 spec bo) with
  | .unsat => (⟨[], true, bo⟩, [])
  | .fail => (⟨[], false, bo⟩, [])
  | .sat a =>
      match hv : a[spec.slot]? with
      | some (.int v) =>
          let r := optLoopEmitWith S p0 spec (some a) (some v) f
          (⟨(a, v) :: r.1.sols, r.1.complete, r.1.lastBound⟩, f a :: r.2)
      | _ => (⟨[], false, bo⟩, [])
termination_by meas p0 spec bo
decreasing_by
  have h := S.solveWith_sat _ _ _ hs
  rw [curP_domains] at h
  exact meas_decr h.1 h.2 hv

/-- Pure emit-trace driver from the root (no previous incumbent). -/
def optLoopEmit {α : Type} (S : CertSolver) (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) (bo : Option Int) (f : List Value → α) :
    OptRun × List α :=
  optLoopEmitWith S p0 spec none bo f

/-! Unfolding equations for `optLoop` and `optLoopEmit`, with the branch
    matches kept explicit: the match-bound variable of an unfolding step
    is not nameable, so the proofs below unfold the left-hand side only
    (`conv => lhs`), rewrite the verdict, and reduce the verdict match
    and the objective read with the explicit hypotheses. -/

private theorem optLoopWith_unsat_eq {S : CertSolver}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)}
    (hs : S.solveWith prev (curP p0 spec bo) = .unsat) :
    optLoopWith S p0 spec prev bo = ⟨[], true, bo⟩ := by
  rw [optLoopWith, hs]

private theorem optLoopWith_fail_eq {S : CertSolver}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)}
    (hs : S.solveWith prev (curP p0 spec bo) = .fail) :
    optLoopWith S p0 spec prev bo = ⟨[], false, bo⟩ := by
  rw [optLoopWith, hs]

private theorem optLoopWith_sat_int_eq {S : CertSolver}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)} {a : List Value} {v : Int}
    (hs : S.solveWith prev (curP p0 spec bo) = .sat a)
    (hv : a[spec.slot]? = some (.int v)) :
    optLoopWith S p0 spec prev bo =
      ⟨(a, v) :: (optLoopWith S p0 spec (some a) (some v)).sols,
        (optLoopWith S p0 spec (some a) (some v)).complete,
        (optLoopWith S p0 spec (some a) (some v)).lastBound⟩ := by
  conv => lhs; rw [optLoopWith]
  rw [hs]
  simp only []
  rw [hv]

private theorem optLoopWith_sat_none_eq {S : CertSolver}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)} {a : List Value}
    (hs : S.solveWith prev (curP p0 spec bo) = .sat a)
    (hn : ∀ i : Int, a[spec.slot]? ≠ some (.int i)) :
    optLoopWith S p0 spec prev bo = ⟨[], false, bo⟩ := by
  conv => lhs; rw [optLoopWith]
  rw [hs]
  simp only []

private theorem optLoopEmitWith_unsat_eq {S : CertSolver}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)} {α : Type} {f : List Value → α}
    (hs : S.solveWith prev (curP p0 spec bo) = .unsat) :
    optLoopEmitWith S p0 spec prev bo f = (⟨[], true, bo⟩, []) := by
  rw [optLoopEmitWith, hs]

private theorem optLoopEmitWith_fail_eq {S : CertSolver}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)} {α : Type} {f : List Value → α}
    (hs : S.solveWith prev (curP p0 spec bo) = .fail) :
    optLoopEmitWith S p0 spec prev bo f = (⟨[], false, bo⟩, []) := by
  rw [optLoopEmitWith, hs]

private theorem optLoopEmitWith_sat_int_eq {S : CertSolver}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)} {a : List Value} {v : Int}
    {α : Type} {f : List Value → α}
    (hs : S.solveWith prev (curP p0 spec bo) = .sat a)
    (hv : a[spec.slot]? = some (.int v)) :
    optLoopEmitWith S p0 spec prev bo f =
      (⟨(a, v) :: (optLoopEmitWith S p0 spec (some a) (some v) f).1.sols,
          (optLoopEmitWith S p0 spec (some a) (some v) f).1.complete,
          (optLoopEmitWith S p0 spec (some a) (some v) f).1.lastBound⟩,
        f a :: (optLoopEmitWith S p0 spec (some a) (some v) f).2) := by
  conv => lhs; rw [optLoopEmitWith]
  rw [hs]
  simp only []
  rw [hv]

private theorem optLoopEmitWith_sat_none_eq {S : CertSolver}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)} {a : List Value} {α : Type} {f : List Value → α}
    (hs : S.solveWith prev (curP p0 spec bo) = .sat a)
    (hn : ∀ i : Int, a[spec.slot]? ≠ some (.int i)) :
    optLoopEmitWith S p0 spec prev bo f = (⟨[], false, bo⟩, []) := by
  conv => lhs; rw [optLoopEmitWith]
  rw [hs]
  simp only []

/-- The emit-trace driver returns the run and the `f`-images of its
    solutions, in order, for every previous incumbent. -/
theorem optLoopEmitWith_eq (S : CertSolver) (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) {α : Type} (f : List Value → α) :
    ∀ n prev bo, meas p0 spec bo = n →
      optLoopEmitWith S p0 spec prev bo f =
        (optLoopWith S p0 spec prev bo,
          (optLoopWith S p0 spec prev bo).sols.map (fun s => f s.1)) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro prev bo hn
    cases hc : S.solveWith prev (curP p0 spec bo) with
    | unsat =>
        rw [optLoopEmitWith_unsat_eq hc, optLoopWith_unsat_eq hc]
        rfl
    | fail =>
        rw [optLoopEmitWith_fail_eq hc, optLoopWith_fail_eq hc]
        rfl
    | sat a =>
        cases hv : a[spec.slot]? with
        | none =>
            have hn' : ∀ i : Int, a[spec.slot]? ≠ some (.int i) := by
              intro i hi
              rw [hv] at hi
              cases hi
            rw [optLoopEmitWith_sat_none_eq hc hn',
              optLoopWith_sat_none_eq hc hn']
            rfl
        | some w =>
            cases w with
            | int v =>
                have hsat := S.solveWith_sat _ _ _ hc
                rw [curP_domains] at hsat
                rw [optLoopEmitWith_sat_int_eq hc hv, optLoopWith_sat_int_eq hc hv]
                rw [ih _ (hn ▸ meas_decr hsat.1 hsat.2 hv) (some a) (some v) rfl]
                simp only [List.map_cons]
            | bool b =>
                have hn' : ∀ i : Int, a[spec.slot]? ≠ some (.int i) := by
                  intro i hi
                  rw [hv] at hi
                  cases hi
                rw [optLoopEmitWith_sat_none_eq hc hn',
                  optLoopWith_sat_none_eq hc hn']
                rfl
            | setOfInt s =>
                have hn' : ∀ i : Int, a[spec.slot]? ≠ some (.int i) := by
                  intro i hi
                  rw [hv] at hi
                  cases hi
                rw [optLoopEmitWith_sat_none_eq hc hn',
                  optLoopWith_sat_none_eq hc hn']
                rfl
            | array arr =>
                have hn' : ∀ i : Int, a[spec.slot]? ≠ some (.int i) := by
                  intro i hi
                  rw [hv] at hi
                  cases hi
                rw [optLoopEmitWith_sat_none_eq hc hn',
                  optLoopWith_sat_none_eq hc hn']
                rfl

/-- The root emit-trace driver returns the run and the `f`-images of its
    solutions, in order. -/
theorem optLoopEmit_eq (S : CertSolver) (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) {α : Type} (f : List Value → α) :
    ∀ n bo, meas p0 spec bo = n →
      optLoopEmit S p0 spec bo f =
        (optLoop S p0 spec bo, (optLoop S p0 spec bo).sols.map (fun s => f s.1)) := by
  intro n bo hn
  exact optLoopEmitWith_eq S p0 spec f n none bo hn

/-- The trace driver's first component is the pure run. -/
theorem optLoopEmit_fst (S : CertSolver) (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) {α : Type} (f : List Value → α) (bo : Option Int) :
    (optLoopEmit S p0 spec bo f).1 = optLoop S p0 spec bo := by
  rw [optLoopEmit_eq S p0 spec f _ bo rfl]

/-- The trace driver's emitted list is the `f`-image of the pure run's
    solutions, in order. -/
theorem optLoopEmit_snd (S : CertSolver) (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) {α : Type} (f : List Value → α) (bo : Option Int) :
    (optLoopEmit S p0 spec bo f).2 =
      (optLoop S p0 spec bo).sols.map (fun s => f s.1) := by
  rw [optLoopEmit_eq S p0 spec f _ bo rfl]

/-! ## The IO streaming driver -/

/-- The streaming specification: emit the whole trace in order, then
    return the pure spec result. -/
def streamSpec {α : Type} (emit : α → IO Unit) (r : OptRun × List α) :
    IO (OptRun × List α) :=
  emitAll emit r.2 >>= fun _ => pure r

/-- Streaming branch and bound with the previous incumbent threaded to the
    next solve: the same recursion as `optLoopWith`, calling `emit` once per
    improving solution, in the same order, before the next solve. -/
def optimizeStreamLoopWith {α : Type} (S : CertSolver)
    (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec)
    (f : List Value → α) (emit : α → IO Unit) :
    Option (List Value) → Option Int → IO (OptRun × List α)
  | prev, bo =>
    match hs : S.solveWith prev (curP p0 spec bo) with
    | .unsat => pure (⟨[], true, bo⟩, [])
    | .fail => pure (⟨[], false, bo⟩, [])
    | .sat a =>
        match hv : a[spec.slot]? with
        | some (.int v) =>
            emit (f a) >>= fun _ =>
              optimizeStreamLoopWith S p0 spec f emit (some a) (some v) >>= fun r =>
                pure (⟨(a, v) :: r.1.sols, r.1.complete, r.1.lastBound⟩,
                  f a :: r.2)
        | _ => pure (⟨[], false, bo⟩, [])
termination_by prev bo => meas p0 spec bo
decreasing_by
  have h := S.solveWith_sat _ _ _ hs
  rw [curP_domains] at h
  exact meas_decr h.1 h.2 hv

/-- Streaming branch and bound from the root (no previous incumbent). -/
def optimizeStreamLoop {α : Type} (S : CertSolver)
    (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec)
    (f : List Value → α) (emit : α → IO Unit) :
    Option Int → IO (OptRun × List α) :=
  optimizeStreamLoopWith S p0 spec f emit none

private theorem optimizeStreamLoopWith_unsat_eq {S : CertSolver}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)}
    {α : Type} {f : List Value → α} {emit : α → IO Unit}
    (hs : S.solveWith prev (curP p0 spec bo) = .unsat) :
    optimizeStreamLoopWith S p0 spec f emit prev bo = pure (⟨[], true, bo⟩, []) := by
  rw [optimizeStreamLoopWith, hs]

private theorem optimizeStreamLoopWith_fail_eq {S : CertSolver}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)}
    {α : Type} {f : List Value → α} {emit : α → IO Unit}
    (hs : S.solveWith prev (curP p0 spec bo) = .fail) :
    optimizeStreamLoopWith S p0 spec f emit prev bo = pure (⟨[], false, bo⟩, []) := by
  rw [optimizeStreamLoopWith, hs]

private theorem optimizeStreamLoopWith_sat_int_eq {S : CertSolver}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)} {a : List Value} {v : Int}
    {α : Type} {f : List Value → α} {emit : α → IO Unit}
    (hs : S.solveWith prev (curP p0 spec bo) = .sat a)
    (hv : a[spec.slot]? = some (.int v)) :
    optimizeStreamLoopWith S p0 spec f emit prev bo =
      (emit (f a) >>= fun _ =>
        optimizeStreamLoopWith S p0 spec f emit (some a) (some v) >>= fun r =>
          pure (⟨(a, v) :: r.1.sols, r.1.complete, r.1.lastBound⟩,
            f a :: r.2)) := by
  conv => lhs; rw [optimizeStreamLoopWith]
  rw [hs]
  simp only []
  rw [hv]

private theorem optimizeStreamLoopWith_sat_none_eq {S : CertSolver}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)} {a : List Value}
    {α : Type} {f : List Value → α} {emit : α → IO Unit}
    (hs : S.solveWith prev (curP p0 spec bo) = .sat a)
    (hn : ∀ i : Int, a[spec.slot]? ≠ some (.int i)) :
    optimizeStreamLoopWith S p0 spec f emit prev bo = pure (⟨[], false, bo⟩, []) := by
  conv => lhs; rw [optimizeStreamLoopWith]
  rw [hs]
  simp only []

/-- The streaming driver performs exactly the emissions of the pure
    driver's trace, in order, and returns the pure driver's result, for
    every previous incumbent. -/
theorem optimizeStreamLoopWith_emit (S : CertSolver)
    (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) {α : Type} (f : List Value → α) (emit : α → IO Unit) :
    ∀ (prev : Option (List Value)) (bo : Option Int),
      optimizeStreamLoopWith S p0 spec f emit prev bo =
        streamSpec emit (optLoopEmitWith S p0 spec prev bo f) := by
  intro prev bo
  suffices h : ∀ n : Nat, ∀ (prev : Option (List Value)) (b : Option Int),
      meas p0 spec b = n →
      optimizeStreamLoopWith S p0 spec f emit prev b =
        streamSpec emit (optLoopEmitWith S p0 spec prev b f) from h _ prev bo rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro prev bo hn
    cases hc : S.solveWith prev (curP p0 spec bo) with
    | unsat =>
        rw [optimizeStreamLoopWith_unsat_eq hc, optLoopEmitWith_unsat_eq hc]
        simp only [streamSpec, emitAll, io_pure_bind]
    | fail =>
        rw [optimizeStreamLoopWith_fail_eq hc, optLoopEmitWith_fail_eq hc]
        simp only [streamSpec, emitAll, io_pure_bind]
    | sat a =>
        cases hv : a[spec.slot]? with
        | none =>
            have hn' : ∀ i : Int, a[spec.slot]? ≠ some (.int i) := by
              intro i hi
              rw [hv] at hi
              cases hi
            rw [optimizeStreamLoopWith_sat_none_eq hc hn',
              optLoopEmitWith_sat_none_eq hc hn']
            simp only [streamSpec, emitAll, io_pure_bind]
        | some w =>
            cases w with
            | int v =>
                have hsat := S.solveWith_sat _ _ _ hc
                rw [curP_domains] at hsat
                have IH := ih _ (hn ▸ meas_decr hsat.1 hsat.2 hv) (some a) (some v) rfl
                rw [optimizeStreamLoopWith_sat_int_eq hc hv,
                  optLoopEmitWith_sat_int_eq hc hv, IH]
                simp only [streamSpec, emitAll, io_bind_assoc, io_pure_bind]
            | bool b =>
                have hn' : ∀ i : Int, a[spec.slot]? ≠ some (.int i) := by
                  intro i hi
                  rw [hv] at hi
                  cases hi
                rw [optimizeStreamLoopWith_sat_none_eq hc hn',
                  optLoopEmitWith_sat_none_eq hc hn']
                simp only [streamSpec, emitAll, io_pure_bind]
            | setOfInt s =>
                have hn' : ∀ i : Int, a[spec.slot]? ≠ some (.int i) := by
                  intro i hi
                  rw [hv] at hi
                  cases hi
                rw [optimizeStreamLoopWith_sat_none_eq hc hn',
                  optLoopEmitWith_sat_none_eq hc hn']
                simp only [streamSpec, emitAll, io_pure_bind]
            | array arr =>
                have hn' : ∀ i : Int, a[spec.slot]? ≠ some (.int i) := by
                  intro i hi
                  rw [hv] at hi
                  cases hi
                rw [optimizeStreamLoopWith_sat_none_eq hc hn',
                  optLoopEmitWith_sat_none_eq hc hn']
                simp only [streamSpec, emitAll, io_pure_bind]

/-- The streaming driver performs exactly the emissions of the pure
    driver's trace, in order, and returns the pure driver's result. -/
theorem optimizeStreamLoop_emit (S : CertSolver) (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) {α : Type} (f : List Value → α) (emit : α → IO Unit) :
    ∀ bo : Option Int,
      optimizeStreamLoop S p0 spec f emit bo =
        streamSpec emit (optLoopEmit S p0 spec bo f) := by
  intro bo
  exact optimizeStreamLoopWith_emit S p0 spec f emit none bo

/-- The streaming driver emits exactly the `f`-images of the pure run's
    solutions, in order, and returns that pure run. -/
theorem optimizeStreamLoop_trace (S : CertSolver) (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) {α : Type} (f : List Value → α) (emit : α → IO Unit)
    (bo : Option Int) :
    optimizeStreamLoop S p0 spec f emit bo =
      (emitAll emit ((optLoop S p0 spec bo).sols.map (fun s => f s.1)) >>= fun _ =>
        pure (optLoop S p0 spec bo,
          (optLoop S p0 spec bo).sols.map (fun s => f s.1))) := by
  have hp : optLoopEmit S p0 spec bo f =
      (optLoop S p0 spec bo, (optLoop S p0 spec bo).sols.map (fun s => f s.1)) := by
    rw [Prod.ext_iff]
    exact ⟨optLoopEmit_fst S p0 spec f bo, optLoopEmit_snd S p0 spec f bo⟩
  rw [optimizeStreamLoop_emit S p0 spec f emit bo, hp, streamSpec]

/-- A streaming optimization run: the compiled problem, the pure run,
    and the emitted stores in order. -/
structure OptSummary where
  p : CompiledProblem DomConstraint
  run : OptRun
  emitted : List Store

/-- Streaming certified branch and bound over a source model: `emit` is
    called on every improving solution as it is found (before the next
    solve).  Returns the same run as `optimizeCertified`. -/
def optimizeStream (S : CertSolver) (m : Model) (emit : Store → IO Unit) :
    IO (Except String OptSummary) :=
  match compileModelOpt m with
  | .error e => pure (.error e)
  | .ok (p, spec) =>
      optimizeStreamLoop S p spec (fun a => p.toStore a) emit none >>= fun r =>
        pure (.ok ⟨p, r.1, r.2⟩)

/-- The streaming optimizer emits exactly the source stores of the pure
    emitted sequence, in order, and returns the pure `optLoop` run. -/
theorem optimizeStream_eq (S : CertSolver) (m : Model) (emit : Store → IO Unit) :
    optimizeStream S m emit =
      (match compileModelOpt m with
       | .error e => pure (.error e)
       | .ok (p, spec) =>
           emitAll emit
               ((optLoop S p spec none).sols.map (fun s => p.toStore s.1)) >>= fun _ =>
             pure (.ok ⟨p, optLoop S p spec none,
               (optLoop S p spec none).sols.map (fun s => p.toStore s.1)⟩)) := by
  unfold optimizeStream
  cases hc : compileModelOpt m with
  | error e => rfl
  | ok u =>
      obtain ⟨p, spec⟩ := u
      simp only []
      rw [optimizeStreamLoop_trace S p spec (fun a => p.toStore a) emit none]
      rw [io_bind_assoc, io_pure_bind]

end LeanFzn.Integration

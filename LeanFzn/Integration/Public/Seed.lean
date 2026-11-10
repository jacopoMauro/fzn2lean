/-
Purpose: Core-only seeded branch-and-bound, carrying certified clauses across bounds.
Dependencies: Engine.Incremental, partial Core optimization and compiler correspondence.
DAG: Core incremental search -> seeded invariant/streaming proofs -> public driver.
A give-up preserves incumbents and returns complete=false. No legacy solver or
unconditional completion theorem is used. Completed results retain soundness,
strict improvement, optimality and UNSAT guarantees.
-/
import LeanFzn.Engine.Incremental
import LeanFzn.Integration.Public.Optimize

namespace LeanFzn.Core

open LeanFzn LeanFzn.Semantics LeanFzn.Semantics.Globals
open LeanFzn.Semantics.Evaluation LeanFzn.Compiler LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Engine LeanFzn.Integration

/-! ## The certified verdict -/

/-- The Core seeded attempt, with explicit incomplete results on a Core
give-up.  On every verdict the returned seed is the Core entry's terminal
seed (its database remains valid at the current problem). -/
def coreSeedVerdict (o : SearchConfig) (fuel : Nat)
    (prev : Option (List Value)) (p : CompiledProblem DomConstraint)
    (s : CoreSeed p) : CertVerdict × CoreSeed p :=
  let r := coreSolveSeed p o prev fuel s
  match r.1 with
  | .sat a => (.sat a, r.2.2)
  | .unsat => (.unsat, r.2.2)
  | .gaveUp => (.fail, r.2.2)

/-- A seeded Core SAT verdict is a box member accepted by the problem. -/
theorem coreSeedVerdict_sat {o : SearchConfig} {fuel : Nat}
    {prev : Option (List Value)} {p : CompiledProblem DomConstraint}
    {s : CoreSeed p} {a : List Value}
    (h : (coreSeedVerdict o fuel prev p s).1 = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  cases hc : (coreSolveSeed p o prev fuel s).1 with
  | sat a' =>
      have h' : CertVerdict.sat a' = CertVerdict.sat a := by
        simpa [coreSeedVerdict, hc] using h
      cases h'
      exact coreSolveSeed_sat hc
  | unsat => simp [coreSeedVerdict, hc] at h
  | gaveUp => simp [coreSeedVerdict, hc] at h

/-- A seeded Core UNSAT verdict excludes every assignment of the box. -/
theorem coreSeedVerdict_unsat {o : SearchConfig} {fuel : Nat}
    {prev : Option (List Value)} {p : CompiledProblem DomConstraint}
    {s : CoreSeed p}
    (h : (coreSeedVerdict o fuel prev p s).1 = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  cases hc : (coreSolveSeed p o prev fuel s).1 with
  | sat a' => simp [coreSeedVerdict, hc] at h
  | unsat => exact coreSolveSeed_unsat hc
  | gaveUp => simp [coreSeedVerdict, hc] at h

/-! ## Bound monotonicity -/

/-- The `improveBound` constraint of a strictly better objective value is
stronger than the one of the worse value.  (The same short proof as
`LcgSeed.improveBound_satisfiedB_mono`, kept local to avoid importing the
LCG module.) -/
theorem coreSeed_improveBound_satisfiedB_mono {spec : ObjectiveSpec} {w b : Int}
    (hwb : betterB spec.dir w b = true) :
    ∀ a, DomConstraint.satisfiedB (spec.improveBound w) a = true →
      DomConstraint.satisfiedB (spec.improveBound b) a = true := by
  intro a h
  rw [DomConstraint.satisfiedB_iff (spec.improveBound w) a] at h
  rw [DomConstraint.satisfiedB_iff (spec.improveBound b) a]
  cases hd : spec.dir <;>
    simp only [ObjectiveSpec.improveBound, hd, DomConstraint.SatisfiedBy, betterB,
      decide_eq_true_eq] at hwb h ⊢
  · obtain ⟨j, hj, hle⟩ := h
    exact ⟨j, hj, by omega⟩
  · obtain ⟨j, hj, hle⟩ := h
    exact ⟨j, hj, by omega⟩

/-- Rebase a seed from the current bound `bo` to the strictly better bound
`some v`.  `hbv` is the objective comparison supplied by the SAT witness. -/
def coreSeedRebaseAfter (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) (bo : Option Int) (v : Int)
    (hbv : ∀ b, bo = some b → betterB spec.dir v b = true)
    (s : CoreSeed (curP p0 spec bo)) :
    CoreSeed (curP p0 spec (some v)) :=
  s.rebase (by rw [curP_domains, curP_domains])
    (by
      intro a ha
      cases bo with
      | none => exact (accepts_add.mp ha).1
      | some b0 =>
          exact accepts_add.mpr
            ⟨(accepts_add.mp ha).1,
              coreSeed_improveBound_satisfiedB_mono (hbv b0 rfl) a
                (accepts_add.mp ha).2⟩)

/-! ## The stateful branch-and-bound loop -/

/-- The bound-comparison proof supplied by a seeded SAT verdict at objective
value `v`: the witness is accepted at the current bound, so it is better than
that bound. -/
theorem coreSeedBetterBound {o : SearchConfig} {fuel : Nat}
    {prev : Option (List Value)} {p0 : CompiledProblem DomConstraint}
    {spec : ObjectiveSpec} {bo : Option Int}
    {s s' : CoreSeed (curP p0 spec bo)} {a : List Value} {v : Int}
    (hs : coreSeedVerdict o fuel prev (curP p0 spec bo) s = (.sat a, s'))
    (hv : a[spec.slot]? = some (.int v)) :
    ∀ b, bo = some b → betterB spec.dir v b = true :=
  fun b hbo =>
    (accepts_curP (coreSeedVerdict_sat (by rw [hs])).2).2 b v hbo hv

/-- Core branch and bound with a carried clause database.  The state type
depends on the current bound: after a SAT round with objective value `v`,
the returned database is rebased to `curP p0 spec (some v)` and the
recursion continues there.  The seed size (`db.live`) of every round is
recorded in order. -/
def optLoopCoreSeed (o : SearchConfig) (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) :
    (bo : Option Int) → (prev : Option (List Value)) →
      CoreSeed (curP p0 spec bo) → OptRun × List Nat
  | bo, prev, s =>
      match hs : coreSeedVerdict o coreFuel prev (curP p0 spec bo) s with
      | (.sat a, s') =>
          match hv : a[spec.slot]? with
          | some (.int v) =>
              let hbv : ∀ b, bo = some b → betterB spec.dir v b = true :=
                coreSeedBetterBound hs hv
              let s'' := coreSeedRebaseAfter p0 spec bo v hbv s'
              let r := optLoopCoreSeed o p0 spec (some v) (some a) s''
              (⟨(a, v) :: r.1.sols, r.1.complete, r.1.lastBound⟩,
                s.db.live :: r.2)
          | _ => (⟨[], false, bo⟩, [s.db.live])
      | (.unsat, _) => (⟨[], true, bo⟩, [s.db.live])
      | (.fail, _) => (⟨[], false, bo⟩, [s.db.live])
  termination_by bo prev s => meas p0 spec bo
  decreasing_by
    have hsat := coreSeedVerdict_sat (p := curP p0 spec bo) (s := s)
      (by rw [hs])
    rw [curP_domains] at hsat
    exact meas_decr hsat.1 hsat.2 hv

/-! Unfolding equations for `optLoopCoreSeed`, with the branch matches kept
explicit (same discipline as the `optLoopSeed` equations of
`Integration/OptimizeSeed.lean`). -/

private theorem optLoopCoreSeed_unsat_eq {o : SearchConfig}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)} {s s' : CoreSeed (curP p0 spec bo)}
    (hs : coreSeedVerdict o coreFuel prev (curP p0 spec bo) s = (.unsat, s')) :
    optLoopCoreSeed o p0 spec bo prev s = (⟨[], true, bo⟩, [s.db.live]) := by
  rw [optLoopCoreSeed]
  split <;> simp_all

private theorem optLoopCoreSeed_fail_eq {o : SearchConfig}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)} {s s' : CoreSeed (curP p0 spec bo)}
    (hs : coreSeedVerdict o coreFuel prev (curP p0 spec bo) s = (.fail, s')) :
    optLoopCoreSeed o p0 spec bo prev s = (⟨[], false, bo⟩, [s.db.live]) := by
  rw [optLoopCoreSeed]
  split <;> simp_all

private theorem optLoopCoreSeed_sat_int_eq {o : SearchConfig}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)} {s s' : CoreSeed (curP p0 spec bo)}
    {a : List Value} {v : Int}
    (hs : coreSeedVerdict o coreFuel prev (curP p0 spec bo) s = (.sat a, s'))
    (hv : a[spec.slot]? = some (.int v)) :
    optLoopCoreSeed o p0 spec bo prev s =
      (⟨(a, v) :: (optLoopCoreSeed o p0 spec (some v) (some a)
          (coreSeedRebaseAfter p0 spec bo v (coreSeedBetterBound hs hv) s')).1.sols,
        (optLoopCoreSeed o p0 spec (some v) (some a)
          (coreSeedRebaseAfter p0 spec bo v (coreSeedBetterBound hs hv) s')).1.complete,
        (optLoopCoreSeed o p0 spec (some v) (some a)
          (coreSeedRebaseAfter p0 spec bo v (coreSeedBetterBound hs hv) s')).1.lastBound⟩,
        s.db.live :: (optLoopCoreSeed o p0 spec (some v) (some a)
          (coreSeedRebaseAfter p0 spec bo v (coreSeedBetterBound hs hv) s')).2) := by
  rw [optLoopCoreSeed]
  split
  · rename_i a' s'0 heq
    have hpair : (CertVerdict.sat a', s'0) = (CertVerdict.sat a, s') := by
      rw [← heq, hs]
    cases hpair
    split
    · rename_i v' hv'
      have hvv : v' = v := by
        rw [hv] at hv'
        injection hv' with h
        cases h
        rfl
      subst hvv
      rfl
    · rename_i hx
      rw [hv] at hx
      exfalso
      exact hx v rfl
  · rename_i s'0 heq
    rw [hs] at heq
    cases heq
  · rename_i s'0 heq
    rw [hs] at heq
    cases heq

private theorem optLoopCoreSeed_sat_none_eq {o : SearchConfig}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)} {s s' : CoreSeed (curP p0 spec bo)}
    {a : List Value}
    (hs : coreSeedVerdict o coreFuel prev (curP p0 spec bo) s = (.sat a, s'))
    (hn : ∀ i : Int, a[spec.slot]? ≠ some (.int i)) :
    optLoopCoreSeed o p0 spec bo prev s = (⟨[], false, bo⟩, [s.db.live]) := by
  rw [optLoopCoreSeed]
  split <;> simp_all

/-! ## The stateful loop invariant -/

/-- A run of the stateful Core loop satisfies every field of the plain
`LoopInv`; the carried `ClauseDB` needs no separate invariant because its
type is already relative to the current problem and `CoreSeed.rebase`
transports it across each bound step. -/
theorem optLoopCoreSeed_inv (o : SearchConfig) (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) :
    ∀ n bo prev s, meas p0 spec bo = n →
      LoopInv (coreSolver o) p0 spec bo
        (optLoopCoreSeed o p0 spec bo prev s).1 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro bo prev s hn
    cases hc : coreSeedVerdict o coreFuel prev (curP p0 spec bo) s with
    | mk v s' =>
      cases v with
      | unsat =>
          rw [optLoopCoreSeed_unsat_eq hc]
          refine ⟨by simp, by simp, fun _ b hb => ?_, fun _ => rfl, by simp⟩
          rw [← curP_domains p0 spec bo] at hb
          exact coreSeedVerdict_unsat (by rw [hc]) b hb
      | fail =>
          rw [optLoopCoreSeed_fail_eq hc]
          exact ⟨by simp, by simp, by simp, fun _ => rfl, by simp⟩
      | sat a =>
          cases hv : a[spec.slot]? with
          | none =>
              rw [optLoopCoreSeed_sat_none_eq hc
                (by intro i hi; rw [hv] at hi; cases hi)]
              exact ⟨by simp, by simp, by simp, fun _ => rfl, by simp⟩
          | some w =>
              cases w with
              | int v =>
                  rw [optLoopCoreSeed_sat_int_eq hc hv]
                  have hsat := coreSeedVerdict_sat (p := curP p0 spec bo)
                    (s := s) (by rw [hc])
                  rw [curP_domains] at hsat
                  obtain ⟨hmem, hacc⟩ := hsat
                  have hlt := meas_decr hmem hacc hv
                  generalize hseed_def :
                    coreSeedRebaseAfter p0 spec bo v (coreSeedBetterBound hc hv) s' = hseed
                  have IH := ih _ (hn ▸ hlt) (some v) (some a) hseed rfl
                  obtain ⟨hacc0, hbo⟩ := accepts_curP hacc
                  refine ⟨?_, ?_, IH.optimal, ?_, ?_⟩
                  · intro t ht
                    rcases List.mem_cons.mp ht with rfl | hr
                    · exact ⟨hmem, hacc0, hv, fun b hb => hbo b _ hb hv⟩
                    · obtain ⟨h1, h2, h3, h4⟩ := IH.sound t hr
                      exact ⟨h1, h2, h3, fun b hb =>
                        betterB_trans (h4 v rfl) (hbo b _ hb hv)⟩
                  · refine List.pairwise_cons.mpr ⟨fun t ht => ?_, IH.pairwise⟩
                    exact (IH.sound t ht).2.2.2 v rfl
                  · intro h
                    simp at h
                  · intro t ht
                    dsimp only at ht ⊢
                    by_cases hnil :
                        (optLoopCoreSeed o p0 spec (some v) (some a) hseed).1.sols
                          = []
                    · rw [hnil] at ht
                      simp at ht
                      subst ht
                      exact IH.nil_bound hnil
                    · apply IH.last_bound
                      rw [List.getLast?_cons] at ht
                      obtain ⟨x, hx⟩ : ∃ x,
                          (optLoopCoreSeed o p0 spec (some v) (some a)
                            hseed).1.sols.getLast? = some x := by
                        cases hl :
                            (optLoopCoreSeed o p0 spec (some v) (some a)
                              hseed).1.sols.getLast? with
                        | none =>
                            exact absurd (List.getLast?_eq_none_iff.mp hl) hnil
                        | some x => exact ⟨x, rfl⟩
                      rw [hx] at ht ⊢
                      simpa using ht
              | bool b =>
                  rw [optLoopCoreSeed_sat_none_eq hc
                    (by intro i hi; rw [hv] at hi; cases hi)]
                  exact ⟨by simp, by simp, by simp, fun _ => rfl, by simp⟩
              | setOfInt st =>
                  rw [optLoopCoreSeed_sat_none_eq hc
                    (by intro i hi; rw [hv] at hi; cases hi)]
                  exact ⟨by simp, by simp, by simp, fun _ => rfl, by simp⟩
              | array arr =>
                  rw [optLoopCoreSeed_sat_none_eq hc
                    (by intro i hi; rw [hv] at hi; cases hi)]
                  exact ⟨by simp, by simp, by simp, fun _ => rfl, by simp⟩

/-! ## Source-level optimizer -/

/-- A stateful Core optimization run: the compiled problem, the run, and
the seed size handed to each round's solve, in round order. -/
structure CoreSeedSummary where
  p : CompiledProblem DomConstraint
  run : OptRun
  seeds : List Nat

/-- The certified stateful Core optimizer for a source model: the
branch-and-bound loop over Core with the learned database carried across
rounds, starting from the empty seed and the unseeded entry. -/
def optimizeCoreSeed (o : SearchConfig) (m : Model) :
    Except String CoreSeedSummary :=
  match compileModelOpt m with
  | .error e => .error e
  | .ok (p, spec) =>
      let r := optLoopCoreSeed o p spec none none (CoreSeed.initial p)
      .ok ⟨p, r.1, r.2⟩

/-- Unfolding of `optimizeCoreSeed` at a successful compile. -/
theorem optimizeCoreSeed_inv {o : SearchConfig} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun} {seeds : List Nat}
    (h : optimizeCoreSeed o m = .ok ⟨p, run, seeds⟩) :
    ∃ spec, compileModelOpt m = .ok (p, spec) ∧
      (optLoopCoreSeed o p spec none none (CoreSeed.initial p)).1 = run ∧
      (optLoopCoreSeed o p spec none none (CoreSeed.initial p)).2 = seeds := by
  unfold optimizeCoreSeed at h
  cases hc : compileModelOpt m with
  | error e => rw [hc] at h; cases h
  | ok r =>
      obtain ⟨p', spec⟩ := r
      rw [hc] at h
      simp only [Except.ok.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨spec, rfl, rfl, rfl⟩

/-- Every emitted solution of a stateful Core run is a store satisfying the
source model, with the reported objective value. -/
theorem optimizeCoreSeed_solution_sound {o : SearchConfig} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun} {seeds : List Nat}
    (h : optimizeCoreSeed o m = .ok ⟨p, run, seeds⟩)
    (hwf : WellFormed fullSig m) {t : List Value × Int}
    (ht : t ∈ run.sols) :
    Satisfies fullSig fullInterp m (p.toStore t.1) ∧
    LeanFzn.Semantics.ParamHonest m (p.toStore t.1) ∧
    m.solve.objective (p.toStore t.1) = some t.2 := by
  obtain ⟨spec, hc, hr, -⟩ := optimizeCoreSeed_inv h
  have hinv := optLoopCoreSeed_inv o p spec _ none none (CoreSeed.initial p) rfl
  rw [← hr] at ht
  obtain ⟨hmem, hacc, hv, -⟩ := hinv.sound t ht
  obtain ⟨hsat, hpar, i, hi, hai⟩ := compileOpt_exact hc hwf hmem hacc
  rw [hv] at hai
  have : t.2 = i := by simpa using hai
  subst this
  exact ⟨⟨hwf, hsat⟩, hpar, hi⟩

/-- The objective strictly improves along a stateful Core run's emitted
sequence. -/
theorem optimizeCoreSeed_improving {o : SearchConfig} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun} {seeds : List Nat}
    (h : optimizeCoreSeed o m = .ok ⟨p, run, seeds⟩) :
    ∃ spec : ObjectiveSpec,
      run.sols.Pairwise (fun t u => betterB spec.dir u.2 t.2 = true) := by
  obtain ⟨spec, -, hr, -⟩ := optimizeCoreSeed_inv h
  refine ⟨spec, ?_⟩
  rw [← hr]
  exact (optLoopCoreSeed_inv o p spec _ none none (CoreSeed.initial p) rfl).pairwise

/-- A completed stateful Core run's last solution is an optimal solution of
the source model. -/
theorem optimizeCoreSeed_optimal {o : SearchConfig} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun} {seeds : List Nat}
    (h : optimizeCoreSeed o m = .ok ⟨p, run, seeds⟩)
    (hwf : WellFormed fullSig m) (hcomp : run.complete = true)
    {t : List Value × Int} (hlast : run.sols.getLast? = some t) :
    IsSolution fullSig fullInterp m (p.toStore t.1) := by
  obtain ⟨spec, hc, hr, -⟩ := optimizeCoreSeed_inv h
  have hinv := optLoopCoreSeed_inv o p spec _ none none (CoreSeed.initial p) rfl
  rw [← hr] at hlast hcomp
  have ht : t ∈ (optLoopCoreSeed o p spec none none
      (CoreSeed.initial p)).1.sols := List.mem_of_getLast? hlast
  obtain ⟨hmem, hacc, hv, -⟩ := hinv.sound t ht
  have hlb := hinv.last_bound t hlast
  have hopt := hinv.optimal hcomp
  rw [hlb] at hopt
  exact compileOpt_optimal hc hwf hmem hacc hv hopt

/-- A completed stateful Core run without solutions proves the source model
has no parameter-honest satisfying store. -/
theorem optimizeCoreSeed_unsat {o : SearchConfig} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun} {seeds : List Nat}
    (h : optimizeCoreSeed o m = .ok ⟨p, run, seeds⟩)
    (hwf : WellFormed fullSig m) (hcomp : run.complete = true)
    (hnil : run.sols = []) :
    ¬ ∃ store, Satisfies fullSig fullInterp m store ∧
      LeanFzn.Semantics.ParamHonest m store := by
  obtain ⟨spec, hc, hr, -⟩ := optimizeCoreSeed_inv h
  have hinv := optLoopCoreSeed_inv o p spec _ none none (CoreSeed.initial p) rfl
  rw [← hr] at hcomp hnil
  have hlb := hinv.nil_bound hnil
  have hopt := hinv.optimal hcomp
  rw [hlb] at hopt
  rintro ⟨store, hs, hph⟩
  obtain ⟨b, hb, hbacc, -⟩ := compileOpt_covers hc hwf hs.2 hph
  have : accepts p b = false := hopt b hb
  rw [hbacc] at this
  cases this

/-! ## Streaming -/

private theorem coreSeed_est_bind_assoc {ε σ α β γ : Type} (x : EST ε σ α)
    (f : α → EST ε σ β) (g : β → EST ε σ γ) :
    (x >>= f) >>= g = x >>= fun y => f y >>= g := by
  funext s
  dsimp only [Bind.bind, EST.bind]
  cases h : x s <;> rfl

private theorem coreSeed_io_bind_assoc {α β γ : Type} (x : IO α)
    (f : α → IO β) (g : β → IO γ) :
    (x >>= f) >>= g = x >>= fun y => f y >>= g :=
  coreSeed_est_bind_assoc x f g

private theorem coreSeed_io_pure_bind {α β : Type} (a : α) (f : α → IO β) :
    (pure a >>= f) = f a := rfl

/-- Streaming stateful Core branch and bound: the exact recursion of
`optLoopCoreSeed`, calling `emit` on every improving solution before the
next round and carrying the returned database into that round. -/
def optimizeStreamCoreSeedLoop {α : Type} (o : SearchConfig)
    (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec)
    (f : List Value → α) (emit : α → IO Unit) :
    (bo : Option Int) → (prev : Option (List Value)) →
      CoreSeed (curP p0 spec bo) → IO (OptRun × List Nat)
  | bo, prev, s =>
      match hs : coreSeedVerdict o coreFuel prev (curP p0 spec bo) s with
      | (.sat a, s') =>
          match hv : a[spec.slot]? with
          | some (.int v) =>
              let hbv : ∀ b, bo = some b → betterB spec.dir v b = true :=
                coreSeedBetterBound hs hv
              let s'' := coreSeedRebaseAfter p0 spec bo v hbv s'
              emit (f a) >>= fun _ =>
                optimizeStreamCoreSeedLoop o p0 spec f emit (some v) (some a) s'' >>=
                  fun r =>
                    pure (⟨(a, v) :: r.1.sols, r.1.complete, r.1.lastBound⟩,
                      s.db.live :: r.2)
          | _ => pure (⟨[], false, bo⟩, [s.db.live])
      | (.unsat, _) => pure (⟨[], true, bo⟩, [s.db.live])
      | (.fail, _) => pure (⟨[], false, bo⟩, [s.db.live])
  termination_by bo prev s => meas p0 spec bo
  decreasing_by
    have hsat := coreSeedVerdict_sat (p := curP p0 spec bo) (s := s)
      (by rw [hs])
    rw [curP_domains] at hsat
    exact meas_decr hsat.1 hsat.2 hv

private theorem optimizeStreamCoreSeedLoop_unsat_eq {o : SearchConfig}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)} {s s' : CoreSeed (curP p0 spec bo)}
    {α : Type} {f : List Value → α} {emit : α → IO Unit}
    (hs : coreSeedVerdict o coreFuel prev (curP p0 spec bo) s = (.unsat, s')) :
    optimizeStreamCoreSeedLoop o p0 spec f emit bo prev s
      = pure (⟨[], true, bo⟩, [s.db.live]) := by
  rw [optimizeStreamCoreSeedLoop]
  split <;> simp_all

private theorem optimizeStreamCoreSeedLoop_fail_eq {o : SearchConfig}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)} {s s' : CoreSeed (curP p0 spec bo)}
    {α : Type} {f : List Value → α} {emit : α → IO Unit}
    (hs : coreSeedVerdict o coreFuel prev (curP p0 spec bo) s = (.fail, s')) :
    optimizeStreamCoreSeedLoop o p0 spec f emit bo prev s
      = pure (⟨[], false, bo⟩, [s.db.live]) := by
  rw [optimizeStreamCoreSeedLoop]
  split <;> simp_all

private theorem optimizeStreamCoreSeedLoop_sat_int_eq {o : SearchConfig}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)} {s s' : CoreSeed (curP p0 spec bo)}
    {a : List Value} {v : Int}
    {α : Type} {f : List Value → α} {emit : α → IO Unit}
    (hs : coreSeedVerdict o coreFuel prev (curP p0 spec bo) s = (.sat a, s'))
    (hv : a[spec.slot]? = some (.int v)) :
    optimizeStreamCoreSeedLoop o p0 spec f emit bo prev s =
      (emit (f a) >>= fun _ =>
        optimizeStreamCoreSeedLoop o p0 spec f emit (some v) (some a)
            (coreSeedRebaseAfter p0 spec bo v (coreSeedBetterBound hs hv) s') >>= fun r =>
          pure (⟨(a, v) :: r.1.sols, r.1.complete, r.1.lastBound⟩,
            s.db.live :: r.2)) := by
  rw [optimizeStreamCoreSeedLoop]
  split
  · rename_i a' s'0 heq
    have hpair : (CertVerdict.sat a', s'0) = (CertVerdict.sat a, s') := by
      rw [← heq, hs]
    cases hpair
    split
    · rename_i v' hv'
      have hvv : v' = v := by
        rw [hv] at hv'
        injection hv' with h
        cases h
        rfl
      subst hvv
      rfl
    · rename_i hx
      rw [hv] at hx
      exfalso
      exact hx v rfl
  · rename_i s'0 heq
    rw [hs] at heq
    cases heq
  · rename_i s'0 heq
    rw [hs] at heq
    cases heq

private theorem optimizeStreamCoreSeedLoop_sat_none_eq {o : SearchConfig}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)} {s s' : CoreSeed (curP p0 spec bo)}
    {a : List Value}
    {α : Type} {f : List Value → α} {emit : α → IO Unit}
    (hs : coreSeedVerdict o coreFuel prev (curP p0 spec bo) s = (.sat a, s'))
    (hn : ∀ i : Int, a[spec.slot]? ≠ some (.int i)) :
    optimizeStreamCoreSeedLoop o p0 spec f emit bo prev s
      = pure (⟨[], false, bo⟩, [s.db.live]) := by
  rw [optimizeStreamCoreSeedLoop]
  split <;> simp_all

/-- The streaming spec at a non-integer objective read. -/
private theorem optimizeStreamCoreSeedLoop_spec_none {o : SearchConfig}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)} {s s' : CoreSeed (curP p0 spec bo)}
    {a : List Value}
    {α : Type} {f : List Value → α} {emit : α → IO Unit}
    (hs : coreSeedVerdict o coreFuel prev (curP p0 spec bo) s = (.sat a, s'))
    (hn : ∀ i : Int, a[spec.slot]? ≠ some (.int i)) :
    optimizeStreamCoreSeedLoop o p0 spec f emit bo prev s =
      (emitAll emit
          ((optLoopCoreSeed o p0 spec bo prev s).1.sols.map
            (fun u => f u.1)) >>= fun _ =>
        pure (optLoopCoreSeed o p0 spec bo prev s)) := by
  rw [optimizeStreamCoreSeedLoop_sat_none_eq hs hn,
    optLoopCoreSeed_sat_none_eq hs hn]
  simp only [emitAll, coreSeed_io_pure_bind, List.map_nil]

/-- **THE STREAMING STATEFUL CORE DRIVER'S SPEC**: it emits exactly the
`f`-images of the pure run's solutions, in order, and returns that pure run
with its per-round seed sizes. -/
theorem optimizeStreamCoreSeedLoop_emit {α : Type} (o : SearchConfig)
    (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec)
    (f : List Value → α) (emit : α → IO Unit) :
    ∀ (bo : Option Int) (prev : Option (List Value))
      (s : CoreSeed (curP p0 spec bo)),
      optimizeStreamCoreSeedLoop o p0 spec f emit bo prev s =
        (emitAll emit
            ((optLoopCoreSeed o p0 spec bo prev s).1.sols.map
              (fun t => f t.1)) >>=
          fun _ => pure (optLoopCoreSeed o p0 spec bo prev s)) := by
  intro bo prev s
  suffices h : ∀ n : Nat, ∀ (b : Option Int) (prev : Option (List Value))
      (t : CoreSeed (curP p0 spec b)), meas p0 spec b = n →
      optimizeStreamCoreSeedLoop o p0 spec f emit b prev t =
        (emitAll emit
            ((optLoopCoreSeed o p0 spec b prev t).1.sols.map
              (fun u => f u.1)) >>=
          fun _ => pure (optLoopCoreSeed o p0 spec b prev t)) from h _ bo prev s rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro bo prev s hn
    cases hc : coreSeedVerdict o coreFuel prev (curP p0 spec bo) s with
    | mk v s' =>
      cases v with
      | unsat =>
          rw [optimizeStreamCoreSeedLoop_unsat_eq hc,
            optLoopCoreSeed_unsat_eq hc]
          simp only [emitAll, coreSeed_io_pure_bind, List.map_nil]
      | fail =>
          rw [optimizeStreamCoreSeedLoop_fail_eq hc,
            optLoopCoreSeed_fail_eq hc]
          simp only [emitAll, coreSeed_io_pure_bind, List.map_nil]
      | sat a =>
          cases hv : a[spec.slot]? with
          | none =>
              exact optimizeStreamCoreSeedLoop_spec_none hc
                (by intro i hi; rw [hv] at hi; cases hi)
          | some w =>
              cases w with
              | int v =>
                  have hsat := coreSeedVerdict_sat (p := curP p0 spec bo)
                    (s := s) (by rw [hc])
                  rw [curP_domains] at hsat
                  rw [optimizeStreamCoreSeedLoop_sat_int_eq hc hv,
                    optLoopCoreSeed_sat_int_eq hc hv]
                  generalize hseed_def :
                    coreSeedRebaseAfter p0 spec bo v (coreSeedBetterBound hc hv) s' = hseed
                  have IH := ih _ (hn ▸ meas_decr hsat.1 hsat.2 hv) (some v)
                    (some a) hseed rfl
                  rw [IH]
                  simp only [emitAll, coreSeed_io_bind_assoc,
                    coreSeed_io_pure_bind, List.map_cons]
              | bool b =>
                  exact optimizeStreamCoreSeedLoop_spec_none hc
                    (by intro i hi; rw [hv] at hi; cases hi)
              | setOfInt st =>
                  exact optimizeStreamCoreSeedLoop_spec_none hc
                    (by intro i hi; rw [hv] at hi; cases hi)
              | array arr =>
                  exact optimizeStreamCoreSeedLoop_spec_none hc
                    (by intro i hi; rw [hv] at hi; cases hi)

/-- Streaming certified stateful Core branch and bound over a source model:
`emit` is called on every improving solution as it is found (before the
next solve).  Returns the same run as `optimizeCoreSeed`. -/
def optimizeStreamCoreSeed (o : SearchConfig) (m : Model)
    (emit : Store → IO Unit) : IO (Except String CoreSeedSummary) :=
  match compileModelOpt m with
  | .error e => pure (.error e)
  | .ok (p, spec) =>
      optimizeStreamCoreSeedLoop o p spec (fun a => p.toStore a) emit
        none none (CoreSeed.initial p) >>= fun r =>
        pure (.ok ⟨p, r.1, r.2⟩)

/-- **THE STREAMING STATEFUL CORE RUNNER'S SPEC**: it emits exactly the
source stores of the pure run's solutions, in order, and returns that run
with its per-round seed sizes. -/
theorem optimizeStreamCoreSeed_eq {o : SearchConfig} {m : Model}
    (emit : Store → IO Unit) :
    optimizeStreamCoreSeed o m emit =
      (match compileModelOpt m with
       | .error e => pure (.error e)
       | .ok (p, spec) =>
           emitAll emit
               ((optLoopCoreSeed o p spec none none
                 (CoreSeed.initial p)).1.sols.map (fun t => p.toStore t.1)) >>=
             fun _ =>
             pure (.ok ⟨p,
               (optLoopCoreSeed o p spec none none
                 (CoreSeed.initial p)).1,
               (optLoopCoreSeed o p spec none none
                 (CoreSeed.initial p)).2⟩)) := by
  unfold optimizeStreamCoreSeed
  cases hc : compileModelOpt m with
  | error e => rfl
  | ok u =>
      obtain ⟨p, spec⟩ := u
      simp only []
      rw [optimizeStreamCoreSeedLoop_emit o p spec (fun a => p.toStore a)
        emit none none (CoreSeed.initial p)]
      rw [coreSeed_io_bind_assoc, coreSeed_io_pure_bind]

end LeanFzn.Core

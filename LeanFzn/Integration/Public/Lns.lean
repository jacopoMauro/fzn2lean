/-
Purpose: Core-only large-neighbourhood improvement around a checked incumbent
(PLAN.md P8), layered on the complete linear branch-and-bound driver.
Dependencies: Integration.Public.Optimize and the certified objective
correspondence.
DAG: bounded restricted Core solves -> checked incumbent improvements ->
     unrestricted certified bound search -> public optimization driver.

The neighborhood phase never proves UNSAT or optimality: it only proposes
candidate incumbents by solving a problem that fixes most variables to a
known accepted assignment and asks for a strictly better objective value.
Every candidate is re-checked by the certified Core entry for the restricted
problem, so the refinement only changes the starting incumbent/bound of the
ordinary complete loop (or the retained incumbent when that loop gives up).
-/
import LeanFzn.Integration.Public.Optimize

namespace LeanFzn.Core

open LeanFzn LeanFzn.Semantics LeanFzn.Semantics.Globals
open LeanFzn.Semantics.Evaluation LeanFzn.Compiler LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Engine LeanFzn.Integration

/-! ## Neighborhoods and domain restriction -/

/-- Size of the neighbourhood at attempt `k`: start with sixteen released
slots and grow by one per attempt, capped at the whole box. -/
def lnsSize (n k : Nat) : Nat := min n (16 + k)

/-- A deterministic rotating window of slots, always including the objective
slot.  `n = 0` yields the empty neighbourhood. -/
def lnsKeep (p : CompiledProblem DomConstraint) (spec : ObjectiveSpec)
    (k : Nat) : List Nat :=
  let n := p.domains.length
  let size := lnsSize n k
  let start := if n == 0 then 0 else (k * size) % n
  (List.range n).filter (fun i =>
    decide (((i + n - start) % n) < size) || decide (i == spec.slot))

/-- Replace the domain of every slot outside `keep` by the singleton incumbent
value.  Restricting the search box instead of appending one `constEq` per
fixed slot keeps the restricted solve small; the incumbent's values are known
members of their original domains. -/
def lnsNarrowFrom (a : List Value) (keep : List Nat) : Nat → List Dom → List Dom
  | _, [] => []
  | i, d :: ds =>
      (if keep.contains i then d
       else match a[i]? with
         | some v => Dom.ofList [v]
         | none => Dom.empty) ::
      lnsNarrowFrom a keep (i + 1) ds

/-- The whole-box restriction used by one neighborhood. -/
def lnsNarrow (a : List Value) (keep : List Nat) (ds : List Dom) : List Dom :=
  lnsNarrowFrom a keep 0 ds

@[simp] theorem lnsNarrowFrom_length (a : List Value) (keep : List Nat) :
    ∀ (ds : List Dom) (i : Nat), (lnsNarrowFrom a keep i ds).length = ds.length := by
  intro ds
  induction ds with
  | nil => intro i; rfl
  | cons d ds ih => intro i; simp [lnsNarrowFrom, ih]

@[simp] theorem lnsNarrow_length (a : List Value) (keep : List Nat)
    (ds : List Dom) : (lnsNarrow a keep ds).length = ds.length := by
  simp [lnsNarrow]

/-- Every value in a narrowed slot was already in the original slot. -/
theorem lnsNarrowFrom_getD_subset (a : List Value) (keep : List Nat) :
    ∀ (ds : List Dom) (i j : Nat),
      (∀ k v, a[i + k]? = some v → v ∈ ds.getD k DomainLike.empty) →
      ∀ v, v ∈ (lnsNarrowFrom a keep i ds).getD j DomainLike.empty →
        v ∈ ds.getD j DomainLike.empty := by
  intro ds
  induction ds with
  | nil =>
      intro i j hfit v hv
      simp [lnsNarrowFrom] at hv
  | cons d0 ds ih =>
      intro i j hfit v hv
      cases j with
      | zero =>
          simp only [lnsNarrowFrom, List.getD_cons_zero] at hv ⊢
          split at hv
          · exact hv
          · split at hv
            · rw [mem_ofList_iff, List.mem_singleton] at hv
              subst hv
              exact hfit 0 _ (by assumption)
            · exact absurd hv (by simp)
      | succ j =>
          simp only [lnsNarrowFrom, List.getD_cons_succ] at hv ⊢
          exact ih (i + 1) j (fun k w hw => by
            have h := hfit (k + 1) w
              (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw)
            simpa using h) v hv

/-- Membership in the narrowed box implies membership in the original box. -/
theorem mem_allAssigns_narrow {ds : List Dom} {a b : List Value}
    {keep : List Nat} (hfit : Assignment.Fits ds a)
    (hb : b ∈ allAssigns (lnsNarrow a keep ds)) :
    b ∈ allAssigns ds := by
  obtain ⟨hlen, hmem⟩ := allAssigns_fits (lnsNarrow a keep ds) b hb
  rw [lnsNarrow_length] at hlen
  refine mem_allAssigns_of_getElem? (α := Dom) (ds := ds) (tail := b) hlen ?_
  intro j v hv
  exact lnsNarrowFrom_getD_subset a keep ds 0 j
    (fun k w hw => hfit.2 k w (by simpa using hw)) v (hmem j v hv)

/-- The original problem with every slot outside `keep` fixed to the
incumbent's value through the search box. -/
def lnsRestrict (p : CompiledProblem DomConstraint) (a : List Value)
    (keep : List Nat) : CompiledProblem DomConstraint :=
  let ds := lnsNarrow a keep p.domains
  { p with
    domains := ds
    domainsArray := ds.toArray
    domainsArray_toList := List.toList_toArray }

/-- The restricted problem: the narrowed box plus a strictly improving
objective bound.  Earlier rounds added one `constEq` per fixed slot; doing
the restriction in the domains removes those rows from propagation and
conflict analysis. -/
def lnsProblem (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec)
    (a : List Value) (v : Int) (keep : List Nat) : CompiledProblem DomConstraint :=
  (lnsRestrict p0 a keep).addConstraint (spec.improveBound v)

/-- The restricted search box is the incumbent fixings inside the original
box; the improving bound adds no domain change. -/
@[simp] theorem lnsProblem_domains (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) (a : List Value) (v : Int) (keep : List Nat) :
    (lnsProblem p0 spec a v keep).domains = lnsNarrow a keep p0.domains := by
  unfold lnsProblem lnsRestrict CompiledProblem.addConstraint
  rfl

/-- A better objective value satisfies the improving-bound constraint. -/
theorem improveBound_satisfiedB_of_better {spec : ObjectiveSpec}
    {a : List Value} {w b : Int}
    (hread : a[spec.slot]? = some (.int w))
    (hbetter : betterB spec.dir w b = true) :
    (spec.improveBound b).satisfiedB a = true := by
  rw [DomConstraint.satisfiedB_iff]
  cases hd : spec.dir
  · have h : w < b := by
      rw [hd] at hbetter
      simpa [betterB] using hbetter
    simp only [ObjectiveSpec.improveBound, hd, DomConstraint.SatisfiedBy]
    exact ⟨w, hread, by omega⟩
  · have h : b < w := by
      rw [hd] at hbetter
      simpa [betterB] using hbetter
    simp only [ObjectiveSpec.improveBound, hd, DomConstraint.SatisfiedBy]
    exact ⟨w, hread, by omega⟩

/-- Accepted assignments of the restricted LNS problem are accepted by the
base problem and read a strictly better objective value than `v`. -/
theorem lnsProblem_accepts {p0 : CompiledProblem DomConstraint}
    {spec : ObjectiveSpec} {a b : List Value} {v : Int} {keep : List Nat}
    (h : accepts (lnsProblem p0 spec a v keep) b = true) :
    accepts p0 b = true ∧
      ∀ w, b[spec.slot]? = some (.int w) → betterB spec.dir w v = true := by
  unfold lnsProblem at h
  rw [accepts_add] at h
  obtain ⟨hacc, hbnd⟩ := h
  have hacc0 : accepts p0 b = true := by
    simpa [accepts, lnsRestrict] using hacc
  exact ⟨hacc0, fun w hw =>
    (accepts_improve (p := lnsRestrict p0 a keep) (spec := spec) (b := v)
      (accepts_add.mpr ⟨hacc, hbnd⟩) hw).2⟩

/-- Construct acceptance under a bound from base acceptance, a readable
objective value and the bound comparison. -/
theorem accepts_curP_of_better {p0 : CompiledProblem DomConstraint}
    {spec : ObjectiveSpec} {bo : Option Int} {a : List Value} {w : Int}
    (hacc : accepts p0 a = true)
    (hread : a[spec.slot]? = some (.int w))
    (hbetter : ∀ b, bo = some b → betterB spec.dir w b = true) :
    accepts (curP p0 spec bo) a = true := by
  cases bo with
  | none => simpa [curP] using hacc
  | some b =>
      rw [curP, accepts_add]
      exact ⟨hacc, improveBound_satisfiedB_of_better hread (hbetter b rfl)⟩

/-! ## The bounded neighborhood loop -/

/-- Try `remaining` neighborhoods, starting at `attempt`, and return the last
(hence best) improving candidate together with the diagnostic counters. -/
def lnsLoop (o : SearchConfig) (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) (fuel : Nat) :
    Nat → Nat → List Value → Int → Option (List Value × Int) × EngineStats
  | 0, _, _, _ => (none, {})
  | remaining + 1, attempt, a, v =>
      let keep := lnsKeep p0 spec attempt
      let p := lnsProblem p0 spec a v keep
      match coreSolveFullPre p o (some a) fuel with
      | (.sat b, st) =>
          match hb : b[spec.slot]? with
          | some (.int w) =>
              if hbetter : betterB spec.dir w v = true then
                match lnsLoop o p0 spec fuel remaining (attempt + 1) b w with
                | (some best, st') => (some best, st.add st')
                | (none, st') => (some (b, w), st.add st')
              else (none, st)
          | _ => (none, st)
      | (.unsat, st) => (none, st)
      | (.gaveUp, st) => (none, st)

/-- Every candidate returned by the neighborhood loop is accepted by the
base problem, reads its reported integer value and strictly improves the
value supplied on entry. -/
theorem lnsLoop_sound {o : SearchConfig} {p0 : CompiledProblem DomConstraint}
    {spec : ObjectiveSpec} {fuel : Nat} :
    ∀ remaining attempt a v, Assignment.Fits p0.domains a →
      ∀ b w st,
      lnsLoop o p0 spec fuel remaining attempt a v = (some (b, w), st) →
      b ∈ allAssigns p0.domains ∧ accepts p0 b = true ∧
        b[spec.slot]? = some (.int w) ∧
        betterB spec.dir w v = true := by
  intro remaining
  induction remaining with
  | zero =>
      intro attempt a v hfit b w st h
      simp [lnsLoop] at h
  | succ r ih =>
      intro attempt a v hfit b w st h
      rw [lnsLoop] at h
      split at h
      · rename_i bb st0 hs
        split at h
        · rename_i ww hb
          split at h
          · rename_i hbetter
            have hsat := coreSolveFullPre_sat hs
            have hbAll : bb ∈ allAssigns
                (lnsNarrow a (lnsKeep p0 spec attempt) p0.domains) := by
              simpa [lnsProblem_domains] using hsat.1
            have hfitBB : Assignment.Fits p0.domains bb :=
              allAssigns_fits p0.domains bb (mem_allAssigns_narrow hfit hbAll)
            split at h
            · rename_i best st' heq
              obtain ⟨bestA, bestV⟩ := best
              obtain ⟨hmem, hacc, hread, hstep⟩ :=
                ih (attempt + 1) bb ww hfitBB bestA bestV st' heq
              cases h
              exact ⟨hmem, hacc, hread, betterB_trans hstep hbetter⟩
            · rename_i st' heq
              obtain ⟨hacc, hall⟩ := lnsProblem_accepts (p0 := p0)
                (spec := spec) (a := a) (b := bb) (v := v) (keep := lnsKeep p0 spec attempt)
                hsat.2
              cases h
              exact ⟨mem_allAssigns_narrow hfit hbAll, hacc, hb, hall w hb⟩
          · -- not better
            simp at h
        · -- non-integer objective
          simp at h
      · -- unsat
        simp at h
      · -- gave up
        simp at h

/-! ## Starting the phase from the first full round -/

/-- Run one complete round at the current bound and then the bounded
neighborhood loop.  With no incumbent to start from, the phase simply
falls back to the ordinary complete loop. -/
def lnsStart (o : SearchConfig) (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) (bo : Option Int) :
    Option (List Value × Int) × EngineStats :=
  match coreSolveFullPre (curP p0 spec bo) o none coreFuel with
  | (.sat a, st) =>
      match hv : a[spec.slot]? with
      | some (.int v) =>
          match hloop : lnsLoop o p0 spec o.primalTime p0.domains.length 0 a v with
          | (some best, st') =>
              (some best, st.add { st' with gaveUp := 0, gaveUpCause := "" })
          | (none, st') =>
              (some (a, v), st.add { st' with gaveUp := 0, gaveUpCause := "" })
      | _ => (none, st)
  | (.unsat, st) => (none, st)
  | (.gaveUp, st) => (none, st)

/-- A starting candidate returned by `lnsStart` is accepted under the
original bound and reads its reported integer value. -/
theorem lnsStart_sound {o : SearchConfig} {p0 : CompiledProblem DomConstraint}
    {spec : ObjectiveSpec} {bo : Option Int} {b : List Value} {w : Int}
    {st : EngineStats}
    (h : lnsStart o p0 spec bo = (some (b, w), st)) :
    b ∈ allAssigns p0.domains ∧ accepts (curP p0 spec bo) b = true ∧
      b[spec.slot]? = some (.int w) := by
  unfold lnsStart at h
  split at h
  · rename_i a st0 hs
    split at h
    · rename_i v hv
      split at h
      · rename_i best st' heq
        obtain ⟨bestA, bestV⟩ := best
        have hsat := coreSolveFullPre_sat hs
        have hfitA : Assignment.Fits p0.domains a :=
          allAssigns_fits p0.domains a (by simpa [curP_domains] using hsat.1)
        obtain ⟨hmem, hacc, hread, hstep⟩ := lnsLoop_sound
          (o := o) (p0 := p0) (spec := spec) (fuel := o.primalTime)
          p0.domains.length 0 a v hfitA bestA bestV st' heq
        cases h
        obtain ⟨hacc0, hbetter0⟩ := accepts_curP hsat.2
        exact ⟨hmem, accepts_curP_of_better hacc hread
            (fun b hb => betterB_trans hstep (hbetter0 b v hb hv)), hread⟩
      · rename_i st' heq
        cases h
        have hsat := coreSolveFullPre_sat hs
        exact ⟨by simpa [curP_domains] using hsat.1, hsat.2, hv⟩
    · simp at h
  · simp at h
  · simp at h

/-! ## The augmented certified run -/

/-- The neighborhood phase followed by the ordinary complete linear loop,
with the starting candidate retained in the emitted sequence. -/
def lnsSearch (o : SearchConfig) (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) (bo : Option Int) : OptRun × EngineStats :=
  match hs : lnsStart o p0 spec bo with
  | (none, st) => optLoopCoreStatsWith o coreFuel p0 spec none bo
  | (some (best, vbest), st) =>
      let loop := optLoopCoreStatsWith o coreFuel p0 spec (some best) (some vbest)
      (⟨(best, vbest) :: loop.1.sols, loop.1.complete, loop.1.lastBound⟩,
        st.add loop.2)

/-- Adding the checked starting candidate in front of a loop run preserves
the loop invariant, including optimality of the last bound. -/
theorem lnsAugmented_inv {S : CertSolver} {p0 : CompiledProblem DomConstraint}
    {spec : ObjectiveSpec} {bo : Option Int} {best : List Value × Int}
    {loop : OptRun}
    (hbest : best.1 ∈ allAssigns p0.domains ∧
      accepts (curP p0 spec bo) best.1 = true ∧
      best.1[spec.slot]? = some (.int best.2))
    (hloop : LoopInv S p0 spec (some best.2) loop) :
    LoopInv S p0 spec bo
      ⟨(best.1, best.2) :: loop.sols, loop.complete, loop.lastBound⟩ := by
  obtain ⟨hmemBest, haccBest, hreadBest⟩ := hbest
  obtain ⟨hacc0, hbetter0⟩ := accepts_curP haccBest
  have hbetterBest : ∀ b, bo = some b → betterB spec.dir best.2 b = true :=
    fun b hb => hbetter0 b best.2 hb hreadBest
  refine ⟨?_, ?_, hloop.optimal, ?_, ?_⟩
  · intro s hs
    rcases List.mem_cons.mp hs with rfl | hr
    · exact ⟨hmemBest, hacc0, hreadBest, hbetterBest⟩
    · obtain ⟨h1, h2, h3, h4⟩ := hloop.sound s hr
      exact ⟨h1, h2, h3, fun b hb =>
        betterB_trans (h4 best.2 rfl) (hbetter0 b best.2 hb hreadBest)⟩
  · refine List.pairwise_cons.mpr ⟨fun t ht => ?_, hloop.pairwise⟩
    exact (hloop.sound t ht).2.2.2 best.2 rfl
  · simp
  · intro t ht
    dsimp only at ht ⊢
    by_cases hnil : loop.sols = []
    · rw [hnil] at ht
      simp at ht
      subst ht
      exact hloop.nil_bound hnil
    · apply hloop.last_bound
      rw [List.getLast?_cons] at ht
      obtain ⟨x, hx⟩ : ∃ x, loop.sols.getLast? = some x := by
        cases hl : loop.sols.getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.mp hl) hnil
        | some x => exact ⟨x, rfl⟩
      rw [hx] at ht ⊢
      simpa using ht

/-- The augmented run's invariant. -/
theorem lnsSearch_inv (o : SearchConfig) (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) (bo : Option Int) :
    LoopInv (coreSolver o coreFuel) p0 spec bo
      (lnsSearch o p0 spec bo).1 := by
  unfold lnsSearch
  split
  · rename_i st hs
    rw [optLoopCoreStatsWith_fst o coreFuel p0 spec (meas p0 spec bo) none bo rfl]
    exact optLoopWith_inv (coreSolver o coreFuel) p0 spec
      (meas p0 spec bo) none bo rfl
  · rename_i best vbest st hs
    have hbest := lnsStart_sound hs
    have hloop := optLoopWith_inv (coreSolver o coreFuel) p0 spec
      (meas p0 spec (some vbest)) (some best) (some vbest) rfl
    dsimp only
    rw [optLoopCoreStatsWith_fst o coreFuel p0 spec
      (meas p0 spec (some vbest)) (some best) (some vbest) rfl]
    exact lnsAugmented_inv (best := (best, vbest)) hbest hloop

/-- Core-only LNS optimization entry on a source model.  Neighborhood
failures never become global claims; the complete loop still decides
optimality or UNSAT. -/
def optimizeCoreLns (o : SearchConfig) (m : Model) :
    Except String (CompiledProblem DomConstraint × OptRun) :=
  match compileModelOpt m with
  | .error e => .error e
  | .ok (p, spec) => .ok (p, (lnsSearch o p spec none).1)

/-- Every emitted solution of the LNS entry is a satisfying source store with
its reported objective value. -/
theorem optimizeCoreLns_solution_sound {o : SearchConfig} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun}
    (h : optimizeCoreLns o m = .ok (p, run)) (hwf : WellFormed fullSig m)
    {s : List Value × Int} (hs : s ∈ run.sols) :
    Satisfies fullSig fullInterp m (p.toStore s.1) ∧
      LeanFzn.Semantics.ParamHonest m (p.toStore s.1) ∧
      m.solve.objective (p.toStore s.1) = some s.2 := by
  unfold optimizeCoreLns at h
  cases hc : compileModelOpt m with
  | error e => rw [hc] at h; cases h
  | ok r =>
      obtain ⟨p', spec⟩ := r
      rw [hc] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hinv := lnsSearch_inv o p' spec none
      obtain ⟨hmem, hacc, hv, _⟩ := hinv.sound s hs
      obtain ⟨hsat, hpar, i, hi, hai⟩ := compileOpt_exact hc hwf hmem hacc
      rw [hv] at hai
      have : s.2 = i := by simpa using hai
      subst this
      exact ⟨⟨hwf, hsat⟩, hpar, hi⟩

/-- The objective strictly improves along the LNS sequence. -/
theorem optimizeCoreLns_improving {o : SearchConfig} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun}
    (h : optimizeCoreLns o m = .ok (p, run)) :
    ∃ spec : ObjectiveSpec,
      run.sols.Pairwise (fun s t => betterB spec.dir t.2 s.2 = true) := by
  unfold optimizeCoreLns at h
  cases hc : compileModelOpt m with
  | error e => rw [hc] at h; cases h
  | ok r =>
      obtain ⟨p', spec⟩ := r
      rw [hc] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨spec, (lnsSearch_inv o p' spec none).pairwise⟩

/-- A completed LNS run's last solution is optimal for the source model. -/
theorem optimizeCoreLns_optimal {o : SearchConfig} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun}
    (h : optimizeCoreLns o m = .ok (p, run)) (hwf : WellFormed fullSig m)
    (hcomp : run.complete = true) {s : List Value × Int}
    (hlast : run.sols.getLast? = some s) :
    IsSolution fullSig fullInterp m (p.toStore s.1) := by
  unfold optimizeCoreLns at h
  cases hc : compileModelOpt m with
  | error e => rw [hc] at h; cases h
  | ok r =>
      obtain ⟨p', spec⟩ := r
      rw [hc] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hp, hrun⟩ := h
      subst hp
      have hrun' : (lnsSearch o p' spec none).1 = run := hrun
      rw [← hrun'] at hlast hcomp
      have hs : s ∈ (lnsSearch o p' spec none).1.sols := List.mem_of_getLast? hlast
      have hinv := lnsSearch_inv o p' spec none
      obtain ⟨hmem, hacc, hv, _⟩ := hinv.sound s hs
      have hlb := hinv.last_bound s hlast
      have hopt := hinv.optimal hcomp
      rw [hlb] at hopt
      exact compileOpt_optimal hc hwf hmem hacc hv hopt

/-- A completed empty LNS run proves the source model unsatisfiable. -/
theorem optimizeCoreLns_unsat {o : SearchConfig} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun}
    (h : optimizeCoreLns o m = .ok (p, run)) (hwf : WellFormed fullSig m)
    (hcomp : run.complete = true) (hnil : run.sols = []) :
    ¬ ∃ store, Satisfies fullSig fullInterp m store ∧
      LeanFzn.Semantics.ParamHonest m store := by
  unfold optimizeCoreLns at h
  cases hc : compileModelOpt m with
  | error e => rw [hc] at h; cases h
  | ok r =>
      obtain ⟨p', spec⟩ := r
      rw [hc] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hinv := lnsSearch_inv o p' spec none
      have hlb := hinv.nil_bound hnil
      have hopt := hinv.optimal hcomp
      rw [hlb] at hopt
      rintro ⟨store, hs, hph⟩
      obtain ⟨b, hb, hbacc, _⟩ := compileOpt_covers hc hwf hs.2 hph
      have : accepts p' b = false := hopt b hb
      rw [hbacc] at this
      cases this

/-! ## Streaming driver entry

The driver streams the starting candidate and every later improvement as it
is found.  The pure run it corresponds to is `(lnsSearch o p spec bo).1`; the
streaming loop below reuses the existing stats-aware streaming recursion for
the complete second phase. -/

/-- Streaming Core LNS entry: emit the checked start candidate, then stream
the complete linear loop from the refined incumbent. -/
def optimizeStreamCoreLns (o : SearchConfig) (m : Model)
    (emit : Store → IO Unit) : IO (Except String (OptSummary × EngineStats)) :=
  match compileModelOpt m with
  | .error e => pure (.error e)
  | .ok (p, spec) =>
      match hs : lnsStart o p spec none with
      | (none, st) =>
          optimizeStreamCoreStatsLoop o coreFuel p spec
              (fun a => p.toStore a) emit none none >>= fun r =>
            pure (.ok (⟨p, r.1, r.2.1⟩, st.add r.2.2))
      | (some (best, vbest), st) =>
          emit (p.toStore best) >>= fun _ =>
            optimizeStreamCoreStatsLoop o coreFuel p spec
                (fun a => p.toStore a) emit (some best) (some vbest) >>= fun r =>
              pure (.ok (⟨p,
                ⟨(best, vbest) :: r.1.sols, r.1.complete, r.1.lastBound⟩,
                p.toStore best :: r.2.1⟩, st.add r.2.2))

end LeanFzn.Core

/-
File: LeanFzn/Integration/Optimization/Bisect.lean

Purpose:
  Certified objective bisection (PLAN.md task F4, `--opt=bisect`).

  The driver keeps a half-open interval `[lo, hi)` of direction-normalized
  objective keys (`optKey`).  A probe asks whether the problem has a feasible
  assignment whose objective key is at most `mid`; that is exactly the
  bounded problem `curP p0 spec (some (optVal dir (mid+1)))`, whose improving
  bound is `obj <= mid` in key space for both directions.  A certified SAT
  probe contributes an incumbent and moves `hi` down to its key; a certified
  UNSAT probe moves `lo` up to `mid+1`; the interval is terminal when
  `lo >= hi`.  The accumulator is kept in reverse-chronological order (best
  first), so the terminal incumbent is its head and the emitted run is its
  reverse.

  A probe may also return `.exhausted` (R1 budgets).  In that case the driver
  falls back to the existing complete linear descent, from the current best
  incumbent when there is one.  The fallback is a certified complete run, so
  it can still support the ordinary optimality/UNSAT claims; the bisection
  itself makes no partial claim.

  All probes are certified solver results over the compiled box.  The source
  wrapper `optimizeBisect` compiles the model, uses the root objective bounds
  from `Dom.minInt?`/`Dom.maxInt?`, and otherwise falls back to the complete
  linear route (a missing bound is never guessed).

DAG:
  Optimize + LcgOptimize + SearchConfig -> OptimizeBisect -> StrategyDriver

Claim discipline (PLAN §2.1): every emitted solution is a SAT witness of
`p0` (`BisectRunInv.sound`); the terminal incumbent is optimal when the run
is complete (`BisectRunInv.optimal_last`); a completed empty run proves that
no accepted assignment with an integer objective read exists
(`BisectRunInv.unsat_complete`); the source corollaries are the only claims
the CLI may print.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`.
-/

import LeanFzn.Legacy.Integration.Optimization.Kernel
import LeanFzn.Legacy.Integration.SearchConfig

namespace LeanFzn.Integration
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Compiler
open LeanFzn.Semantics.Globals LeanFzn.Solver.Propagation LeanFzn.Solver.Core
open LeanFzn.Compiler.Domains

/-! ## Small IO/list helpers for the streaming wrapper -/

private theorem bisect_est_bind_assoc {ε σ α β γ : Type} (x : EST ε σ α)
    (f : α → EST ε σ β) (g : β → EST ε σ γ) :
    (x >>= f) >>= g = x >>= fun y => f y >>= g := by
  funext s
  dsimp only [Bind.bind, EST.bind]
  cases h : x s <;> rfl

private theorem bisect_io_bind_assoc {α β γ : Type} (x : IO α) (f : α → IO β)
    (g : β → IO γ) :
    (x >>= f) >>= g = x >>= fun y => f y >>= g :=
  bisect_est_bind_assoc x f g

private theorem bisect_io_pure_bind {α β : Type} (a : α) (f : α → IO β) :
    (pure a >>= f) = f a := rfl

/-! ## Direction-normalized objective keys -/

/-- The normalized key of an objective value: smaller is better. -/
def optKey (dir : OptDir) (v : Int) : Int :=
  match dir with
  | .minimize => v
  | .maximize => -v

/-- The objective value with normalized key `k` (the inverse of `optKey`). -/
def optVal (dir : OptDir) (k : Int) : Int :=
  match dir with
  | .minimize => k
  | .maximize => -k

@[simp] theorem optKey_optVal (dir : OptDir) (k : Int) :
    optKey dir (optVal dir k) = k := by
  cases dir <;> dsimp only [optKey, optVal] <;> omega

@[simp] theorem optVal_optKey (dir : OptDir) (v : Int) :
    optVal dir (optKey dir v) = v := by
  cases dir <;> dsimp only [optKey, optVal] <;> omega

/-- `betterB` is strict comparison of normalized keys. -/
theorem betterB_iff_optKey_lt (dir : OptDir) (w b : Int) :
    betterB dir w b = true ↔ optKey dir w < optKey dir b := by
  cases dir <;> dsimp only [betterB, optKey] <;>
    rw [decide_eq_true_iff] <;> omega

/-- Asking `optKey w <= mid` is the improving bound at
    `optVal dir (mid+1)` in both directions. -/
theorem betterB_optVal_succ (dir : OptDir) (w mid : Int) :
    betterB dir w (optVal dir (mid + 1)) = true ↔ optKey dir w ≤ mid := by
  cases dir <;> dsimp only [betterB, optVal, optKey] <;>
    rw [decide_eq_true_iff] <;> omega

/-- If `w` improves on `b`, the assignment satisfies the corresponding
    improving bound.  This is the reverse direction of `accepts_improve`. -/
theorem accepts_improve_of_betterB
    {p : CompiledProblem DomConstraint} {spec : ObjectiveSpec}
    {b w : Int} {a : List Value}
    (hacc : accepts p a = true) (hw : a[spec.slot]? = some (.int w))
    (hb : betterB spec.dir w b = true) :
    accepts (p.addConstraint (spec.improveBound b)) a = true := by
  rw [accepts_add]
  refine ⟨hacc, ?_⟩
  rw [DomConstraint.satisfiedB_iff]
  cases hd : spec.dir <;>
    simp only [ObjectiveSpec.improveBound, hd, DomConstraint.SatisfiedBy,
      betterB, decide_eq_true_eq] at hb ⊢
  · exact ⟨w, hw, by omega⟩
  · exact ⟨w, hw, by omega⟩

/-- An accepted improving-bound assignment reads an integer objective. -/
theorem read_of_accepts_curP_some
    {p : CompiledProblem DomConstraint} {spec : ObjectiveSpec}
    {b : Int} {a : List Value}
    (h : accepts (p.addConstraint (spec.improveBound b)) a = true) :
    ∃ w : Int, a[spec.slot]? = some (.int w) := by
  have hsat := (accepts_add.mp h).2
  rw [DomConstraint.satisfiedB_iff] at hsat
  cases hd : spec.dir <;>
    simp only [ObjectiveSpec.improveBound, hd, DomConstraint.SatisfiedBy] at hsat
  · obtain ⟨w, hw, -⟩ := hsat
    exact ⟨w, hw⟩
  · obtain ⟨w, hw, -⟩ := hsat
    exact ⟨w, hw⟩

/-! ## Root objective bounds -/

/-- The root interval of normalized objective keys, when the objective
    slot's domain has both integer extremes.  `hi` is exclusive. -/
def rootBounds? (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec) :
    Option (Int × Int) :=
  let d := p0.domains.getD spec.slot Dom.empty
  match Dom.minInt? d, Dom.maxInt? d with
  | some mn, some mx =>
      match spec.dir with
      | .minimize => some (mn, mx + 1)
      | .maximize => some (-mx, -mn + 1)
  | _, _ => none

/-- Enumeration membership from compact-domain membership. -/
private theorem enumMem_of_domMem {d : Domain} {v : Value} (h : v ∈ d) :
    v ∈ Dom.enum d :=
  (by
    simpa [LeanFzn.Solver.Propagation.domElems_eq_enum] using
      (LeanFzn.Solver.Core.DomainLike.mem_iff d v).mp h)

/-- Every accepted assignment's integer objective key lies in the root
    interval. -/
theorem rootBounds?_sound {p0 : CompiledProblem DomConstraint}
    {spec : ObjectiveSpec} {lo hi : Int}
    (h : rootBounds? p0 spec = some (lo, hi)) :
    ∀ a ∈ allAssigns p0.domains, accepts p0 a = true →
      ∀ w : Int, a[spec.slot]? = some (.int w) →
        lo ≤ optKey spec.dir w ∧ optKey spec.dir w < hi := by
  intro a hmem _ w hw
  let d := p0.domains.getD spec.slot Dom.empty
  have hd : d = p0.domains.getD spec.slot Dom.empty := rfl
  unfold rootBounds? at h
  dsimp only at h
  rw [← hd] at h
  cases hmin : Dom.minInt? d with
  | none =>
      rw [hmin] at h
      cases h
  | some mn =>
      cases hmax : Dom.maxInt? d with
      | none =>
          rw [hmin, hmax] at h
          cases h
      | some mx =>
          rw [hmin, hmax] at h
          have hfit : Assignment.Fits p0.domains a :=
            LeanFzn.Solver.Propagation.allAssigns_fits p0.domains a hmem
          have hmemD : Value.int w ∈ d := by
            dsimp only [d]
            simpa only [LeanFzn.Solver.Propagation.domEmpty_eq] using
              hfit.2 spec.slot (.int w) hw
          have hin : Value.int w ∈ Dom.enum d := enumMem_of_domMem hmemD
          have hmn_le : mn ≤ w :=
            ((Dom.minInt?_eq_some_iff.mp hmin).2 (.int w) hin w rfl)
          have hmx_ge : w ≤ mx :=
            ((Dom.maxInt?_eq_some_iff.mp hmax).2 (.int w) hin w rfl)
          cases hd : spec.dir with
          | minimize =>
              simp only [hd] at h
              cases h
              constructor <;> simp [optKey] <;> omega
          | maximize =>
              simp only [hd] at h
              cases h
              constructor <;> simp [optKey] <;> omega

/-! ## Midpoints -/

/-- The bisection midpoint in key space. -/
def midKey (lo hi : Int) : Int := lo + (hi - lo) / 2

theorem midKey_ge {lo hi : Int} (h : lo < hi) : lo ≤ midKey lo hi := by
  unfold midKey
  have hd : 0 ≤ hi - lo := by omega
  have hq : 0 ≤ (hi - lo) / 2 := Int.ediv_nonneg hd (by decide)
  omega

theorem midKey_lt {lo hi : Int} (h : lo < hi) : midKey lo hi < hi := by
  unfold midKey
  have hd : 0 < hi - lo := by omega
  have hq : (hi - lo) / 2 < hi - lo :=
    Int.ediv_lt_self_of_pos_of_ne_one hd (by decide)
  omega

theorem midKey_succ_le {lo hi : Int} (h : lo < hi) : midKey lo hi + 1 ≤ hi := by
  have := midKey_lt h
  omega

/-! ## The probe interface -/

/-- A probe outcome.  `.exhausted` is a budget prefix and supports no claim;
    it triggers the complete linear fallback. -/
inductive BisectVerdict where
  | sat (a : List Value) (v : Int)
  | unsat
  | exhausted

/-- A certified bisection probe: `sat` carries a source-feasible assignment
    whose key is at most `mid`; `unsat` excludes every source-feasible
    integer-read key at most `mid`. -/
structure BisectProbe (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec) where
  probe : Option (List Value) → Int → BisectVerdict
  sat_sound : ∀ (prev : Option (List Value)) (mid : Int) (a : List Value) (v : Int),
    probe prev mid = .sat a v →
      a ∈ allAssigns p0.domains ∧ accepts p0 a = true ∧
        a[spec.slot]? = some (.int v) ∧ optKey spec.dir v ≤ mid
  unsat_sound : ∀ (prev : Option (List Value)) (mid : Int),
    probe prev mid = .unsat →
      ∀ b ∈ allAssigns p0.domains, accepts p0 b = true →
        ∀ w : Int, b[spec.slot]? = some (.int w) → mid < optKey spec.dir w

/-- The probe function of a complete certified solver.  An unreadable SAT
    result or a certified-solver `fail` is treated as `.exhausted` (no
    claim); the `fail` case cannot occur under the solver gate. -/
def certProbeFn (S : CertSolver) (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) (prev : Option (List Value)) (mid : Int) :
    BisectVerdict :=
  match S.solveWith prev (curP p0 spec (some (optVal spec.dir (mid + 1)))) with
  | .sat a =>
      match a[spec.slot]? with
      | some (.int v) => .sat a v
      | _ => .exhausted
  | .unsat => .unsat
  | .fail => .exhausted

/-- A complete certified probe is sound: its SAT witness reads an objective
    key at most `mid`. -/
theorem certProbeFn_sat {S : CertSolver} {p0 : CompiledProblem DomConstraint}
    {spec : ObjectiveSpec} {prev : Option (List Value)} {mid : Int}
    {a : List Value} {v : Int}
    (h : certProbeFn S p0 spec prev mid = .sat a v) :
    a ∈ allAssigns p0.domains ∧ accepts p0 a = true ∧
      a[spec.slot]? = some (.int v) ∧ optKey spec.dir v ≤ mid := by
  unfold certProbeFn at h
  split at h
  · rename_i a0 hsat
    split at h
    · rename_i v0 hv
      injection h with ha hv'
      have hsat' := S.solveWith_sat _ prev _ hsat
      rw [curP_domains] at hsat'
      have hb := (accepts_curP hsat'.2).2
        (optVal spec.dir (mid + 1)) v0 rfl hv
      rw [← ha, ← hv']
      exact ⟨hsat'.1, (accepts_curP hsat'.2).1, hv,
        (betterB_optVal_succ spec.dir v0 mid).mp hb⟩
    · cases h
  · cases h
  · cases h

/-- A complete certified probe is complete: UNSAT excludes every feasible
    integer objective key at most `mid`. -/
theorem certProbeFn_unsat {S : CertSolver} {p0 : CompiledProblem DomConstraint}
    {spec : ObjectiveSpec} {prev : Option (List Value)} {mid : Int}
    (h : certProbeFn S p0 spec prev mid = .unsat) :
    ∀ b ∈ allAssigns p0.domains, accepts p0 b = true →
      ∀ w : Int, b[spec.slot]? = some (.int w) → mid < optKey spec.dir w := by
  intro b hb hacc w hw
  by_cases hle : optKey spec.dir w ≤ mid
  · unfold certProbeFn at h
    split at h
    · split at h <;> cases h
    · rename_i hunsat
      have hbnd : accepts
          (p0.addConstraint (spec.improveBound (optVal spec.dir (mid + 1)))) b = true :=
        accepts_improve_of_betterB hacc hw
          ((betterB_optVal_succ spec.dir w mid).mpr hle)
      have hbmem : b ∈ allAssigns
          (curP p0 spec (some (optVal spec.dir (mid + 1)))).domains := by
        rw [curP_domains]
        exact hb
      have hno := S.solveWith_unsat
        (curP p0 spec (some (optVal spec.dir (mid + 1)))) prev hunsat b hbmem
      have hbnd' : accepts
          (curP p0 spec (some (optVal spec.dir (mid + 1)))) b = true := by
        simpa [curP] using hbnd
      rw [hbnd'] at hno
      cases hno
    · cases h
  · omega

/-- The complete LCG/linear probe. -/
def certProbe (S : CertSolver) (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) : BisectProbe p0 spec where
  probe := certProbeFn S p0 spec
  sat_sound := by
    intro prev mid a v h
    exact certProbeFn_sat h
  unsat_sound := by
    intro prev mid h
    exact certProbeFn_unsat h

/-! ## Driver state and invariants -/

/-- The result of a bisection run.  `sols` is chronological (worst to best),
    `probes` counts bisection probe attempts; linear fallback rounds are not
    counted as bisection probes. -/
structure BisectRun where
  sols : List (List Value × Int)
  complete : Bool
  lastBound : Option Int
  probes : Nat

/-- Forget the bisection bookkeeping for the common optimization summary. -/
def BisectRun.toOptRun (r : BisectRun) : OptRun :=
  ⟨r.sols, r.complete, r.lastBound⟩

/-- The result of a streaming bisection invocation: the same final run as the
    pure loop, plus the incumbents this invocation emitted (chronological).
    The emitted list is a suffix of `run.sols`; the accumulator prefix was
    emitted by an earlier recursive call. -/
structure BisectEmitRun where
  run : BisectRun
  emitted : List (List Value × Int)

/-- The reverse-chronological accumulator invariant.

    `lower` says every feasible integer objective key is at least `lo`.
    `upper_none` says an empty accumulator certifies that every feasible key
    is below `hi` (the initial root interval); when the accumulator is
    nonempty, `head_hi` instead records that its best incumbent sits exactly
    at the exclusive upper endpoint. -/
structure BisectAccInv (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec)
    (lo hi : Int) (acc : List (List Value × Int)) : Prop where
  sound : ∀ s ∈ acc, s.1 ∈ allAssigns p0.domains ∧ accepts p0 s.1 = true ∧
    s.1[spec.slot]? = some (.int s.2)
  pairwise : acc.Pairwise (fun s t => betterB spec.dir s.2 t.2 = true)
  lower : ∀ b ∈ allAssigns p0.domains, accepts p0 b = true →
    ∀ w : Int, b[spec.slot]? = some (.int w) → lo ≤ optKey spec.dir w
  upper_none : acc = [] →
    ∀ b ∈ allAssigns p0.domains, accepts p0 b = true →
      ∀ w : Int, b[spec.slot]? = some (.int w) → optKey spec.dir w < hi
  head_hi : ∀ s, acc.head? = some s → optKey spec.dir s.2 = hi

/-- The public run invariant: all incumbents are source-feasible, a complete
    run's last incumbent is optimal among feasible integer objective reads,
    and a complete empty run excludes every such read. -/
structure BisectRunInv (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec)
    (r : BisectRun) : Prop where
  sound : ∀ s ∈ r.sols, s.1 ∈ allAssigns p0.domains ∧ accepts p0 s.1 = true ∧
    s.1[spec.slot]? = some (.int s.2)
  pairwise : r.sols.Pairwise (fun s t => betterB spec.dir t.2 s.2 = true)
  optimal_last : r.complete = true → ∀ s, r.sols.getLast? = some s →
    ∀ b ∈ allAssigns p0.domains, accepts p0 b = true →
      ∀ w : Int, b[spec.slot]? = some (.int w) →
        ¬ betterB spec.dir w s.2
  unsat_complete : r.complete = true → r.sols = [] →
    ∀ b ∈ allAssigns p0.domains, accepts p0 b = true →
      ∀ i : Int, b[spec.slot]? = some (.int i) → False

/-! ## Invariant steps -/

theorem bisectAccInv_sat {p0 : CompiledProblem DomConstraint}
    {spec : ObjectiveSpec} {lo hi mid : Int}
    {acc : List (List Value × Int)} {a : List Value} {v : Int}
    (hinv : BisectAccInv p0 spec lo hi acc)
    (hsat : a ∈ allAssigns p0.domains ∧ accepts p0 a = true ∧
      a[spec.slot]? = some (.int v) ∧ optKey spec.dir v ≤ mid)
    (hmid : mid < hi) :
    BisectAccInv p0 spec lo (optKey spec.dir v) ((a, v) :: acc) := by
  obtain ⟨hmem, hacc, hread, hle⟩ := hsat
  refine ⟨?_, ?_, hinv.lower, ?_, ?_⟩
  · intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ⟨hmem, hacc, hread⟩
    · exact hinv.sound s hs
  · cases acc with
    | nil => simp
    | cons s rest =>
        have hs_hi : optKey spec.dir s.2 = hi := hinv.head_hi s rfl
        have hlt : optKey spec.dir v < optKey spec.dir s.2 := by
          rw [hs_hi]
          omega
        have hb : betterB spec.dir v s.2 = true :=
          (betterB_iff_optKey_lt spec.dir v s.2).mpr hlt
        refine List.pairwise_cons.mpr ⟨?_, hinv.pairwise⟩
        intro t ht
        rcases List.mem_cons.mp ht with rfl | htrest
        · exact hb
        · exact betterB_trans hb ((List.pairwise_cons.mp hinv.pairwise).1 t htrest)
  · intro hnil
    cases hnil
  · intro s hs
    simp only [List.head?_cons, Option.some.injEq] at hs
    cases hs
    rfl

theorem bisectAccInv_unsat {p0 : CompiledProblem DomConstraint}
    {spec : ObjectiveSpec} {lo hi mid : Int}
    {acc : List (List Value × Int)}
    (hinv : BisectAccInv p0 spec lo hi acc)
    (hunsat : ∀ b ∈ allAssigns p0.domains, accepts p0 b = true →
      ∀ w : Int, b[spec.slot]? = some (.int w) → mid < optKey spec.dir w) :
    BisectAccInv p0 spec (mid + 1) hi acc := by
  refine ⟨hinv.sound, hinv.pairwise, ?_, hinv.upper_none, hinv.head_hi⟩
  intro b hb hacc w hw
  have := hunsat b hb hacc w hw
  omega

/-- The terminal state: the interval is empty, so the accumulator's head
    (if any) is optimal, or the empty accumulator proves infeasibility. -/
def bisectTerminal (acc : List (List Value × Int)) (probes : Nat) : BisectRun :=
  { sols := acc.reverse
    complete := true
    lastBound := acc.head?.map Prod.snd
    probes := probes }

theorem bisectTerminal_inv {p0 : CompiledProblem DomConstraint}
    {spec : ObjectiveSpec} {lo hi : Int}
    {acc : List (List Value × Int)} {probes : Nat}
    (hinv : BisectAccInv p0 spec lo hi acc) (hterm : hi ≤ lo) :
    BisectRunInv p0 spec (bisectTerminal acc probes) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    have hs' : s ∈ acc.reverse := by simpa [bisectTerminal] using hs
    exact hinv.sound s (List.mem_reverse.mp hs')
  · have hp : acc.reverse.Pairwise
        (fun s t => betterB spec.dir t.2 s.2 = true) :=
      List.pairwise_reverse.mpr hinv.pairwise
    simpa [bisectTerminal] using hp
  · intro _ s hlast b hb hacc w hw
    have hhead : acc.head? = some s := by
      have hlast' : acc.reverse.getLast? = some s := by
        simpa [bisectTerminal] using hlast
      simpa using hlast'
    have hs_hi := hinv.head_hi s hhead
    have hlow := hinv.lower b hb hacc w hw
    have hge : optKey spec.dir s.2 ≤ optKey spec.dir w := by
      rw [hs_hi]
      omega
    intro hbetter
    have := (betterB_iff_optKey_lt spec.dir w s.2).mp hbetter
    omega
  · intro _ hnil b hb hacc i hi
    have hnil' : acc.reverse = [] := by simpa [bisectTerminal] using hnil
    have haccnil : acc = [] := List.reverse_eq_nil_iff.mp hnil'
    have hupper := hinv.upper_none haccnil b hb hacc i hi
    have hlower := hinv.lower b hb hacc i hi
    omega

/-! ## Linear fallback -/

/-- Complete linear descent from the current best incumbent (or from the
    root when the accumulator is empty).  The accumulator is emitted in
    chronological order. -/
def bisectFallback (F : CertSolver) (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) (acc : List (List Value × Int)) (probes : Nat) :
    BisectRun :=
  match acc with
  | [] =>
      let r := optLoop F p0 spec none
      ⟨r.sols, r.complete, r.lastBound, probes⟩
  | s :: _ =>
      let r := optLoopWith F p0 spec (some s.1) (some s.2)
      ⟨acc.reverse ++ r.sols, r.complete, r.lastBound, probes⟩

/-- A plain linear run is a bisection run invariant with an empty prefix. -/
theorem loopInv_to_bisectRunInv {S : CertSolver}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec}
    {r : OptRun} {probes : Nat}
    (hinv : LoopInv S p0 spec none r) :
    BisectRunInv p0 spec ⟨r.sols, r.complete, r.lastBound, probes⟩ := by
  refine ⟨?_, hinv.pairwise, ?_, ?_⟩
  · intro s hs
    obtain ⟨hmem, hacc, hv, -⟩ := hinv.sound s hs
    exact ⟨hmem, hacc, hv⟩
  · intro hcomp s hlast b hb hacc w hw hbetter
    have hlb := hinv.last_bound s hlast
    have hnone := hinv.optimal hcomp
    rw [hlb] at hnone
    have hbnd : accepts (curP p0 spec (some s.2)) b = true := by
      simpa [curP] using accepts_improve_of_betterB hacc hw hbetter
    have hthis := hnone b hb
    rw [hbnd] at hthis
    cases hthis
  · intro hcomp hnil b hb hacc i hi
    have hlb := hinv.nil_bound hnil
    have hnone := hinv.optimal hcomp
    rw [hlb] at hnone
    have hthis := hnone b hb
    have hfalse : accepts p0 b = false := by simpa [curP] using hthis
    rw [hacc] at hfalse
    cases hfalse

/-- Extending a linear descent from the best prefix incumbent preserves all
    public claims. -/
theorem loopInvWith_prefix_to_bisectRunInv {S : CertSolver}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec}
    {head : List Value × Int} {rest : List (List Value × Int)}
    {r : OptRun} {probes : Nat}
    (hsound : ∀ t ∈ head :: rest, t.1 ∈ allAssigns p0.domains ∧
      accepts p0 t.1 = true ∧ t.1[spec.slot]? = some (.int t.2))
    (hpw : (head :: rest).Pairwise
      (fun s t => betterB spec.dir s.2 t.2 = true))
    (hinv : LoopInv S p0 spec (some head.2) r) :
    BisectRunInv p0 spec
      ⟨(head :: rest).reverse ++ r.sols, r.complete, r.lastBound, probes⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hsound t (List.mem_reverse.mp ht)
    · obtain ⟨hmem, hacc, hv, -⟩ := hinv.sound t ht
      exact ⟨hmem, hacc, hv⟩
  · rw [List.pairwise_append]
    refine ⟨?_, hinv.pairwise, ?_⟩
    · exact List.pairwise_reverse.mpr hpw
    · intro a ha b hb
      have hb_head : betterB spec.dir b.2 head.2 = true :=
        (hinv.sound b hb).2.2.2 head.2 rfl
      have ha_acc : a ∈ head :: rest := List.mem_reverse.mp ha
      by_cases hae : a = head
      · rw [hae]
        exact hb_head
      · have ha_rest : a ∈ rest := by
          rcases List.mem_cons.mp ha_acc with h | h
          · exact absurd h hae
          · exact h
        exact betterB_trans hb_head ((List.pairwise_cons.mp hpw).1 a ha_rest)
  · intro hcomp t hlast b hb hacc w hw
    by_cases hr : r.sols = []
    · have hrev : ((head :: rest).reverse).getLast? = some t := by
        have hlast' : (((head :: rest).reverse ++ r.sols)).getLast? = some t := hlast
        rw [List.getLast?_append, hr] at hlast'
        simpa using hlast'
      have hhead : (head :: rest).head? = some t := by simpa using hrev
      have hhead' : head = t := by simpa using hhead
      subst t
      have hlb := hinv.nil_bound hr
      have hnone := hinv.optimal hcomp
      rw [hlb] at hnone
      intro hbetter
      have hbnd : accepts (curP p0 spec (some head.2)) b = true := by
        simpa [curP] using accepts_improve_of_betterB hacc hw hbetter
      have hthis := hnone b hb
      rw [hbnd] at hthis
      cases hthis
    · have hnon : r.sols.getLast? ≠ none := by
        intro hl
        exact hr (List.getLast?_eq_none_iff.mp hl)
      have hlast' : r.sols.getLast? = some t := by
        rw [List.getLast?_append] at hlast
        cases hl : r.sols.getLast? with
        | none => exact absurd hl hnon
        | some u =>
            simp only [hl, Option.some_or] at hlast
            have htu : u = t := Option.some.inj hlast
            exact congrArg some htu
      have hlb := hinv.last_bound t hlast'
      have hnone := hinv.optimal hcomp
      rw [hlb] at hnone
      intro hbetter
      have hbnd : accepts (curP p0 spec (some t.2)) b = true := by
        simpa [curP] using accepts_improve_of_betterB hacc hw hbetter
      have hthis := hnone b hb
      rw [hbnd] at hthis
      cases hthis
  · intro hcomp hnil b hb hacc i hi
    have hnil' : (head :: rest).reverse ++ r.sols = [] := hnil
    have hrevnil : (head :: rest).reverse = [] :=
      (List.append_eq_nil_iff.mp hnil').1
    exact absurd hrevnil (by simp)

theorem bisectFallback_inv (F : CertSolver)
    (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec)
    {lo hi : Int} {acc : List (List Value × Int)} (probes : Nat)
    (hinv : BisectAccInv p0 spec lo hi acc) :
    BisectRunInv p0 spec (bisectFallback F p0 spec acc probes) := by
  cases acc with
  | nil =>
      simpa [bisectFallback] using
        (loopInv_to_bisectRunInv (p0 := p0) (spec := spec)
          (probes := probes) (hinv := optLoop_inv F p0 spec _ none rfl))
  | cons s rest =>
      simpa [bisectFallback] using
        (loopInvWith_prefix_to_bisectRunInv (S := F) (p0 := p0) (spec := spec)
          (head := s) (rest := rest) (probes := probes)
          (hsound := hinv.sound)
          (hpw := hinv.pairwise)
          (hinv := optLoopWith_inv F p0 spec _ (some s.1) (some s.2) rfl))

theorem bisectFallback_complete (F : CertSolver)
    (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec)
    (hg : F.gate p0 = true)
    (hread : ∀ a ∈ allAssigns p0.domains, accepts p0 a = true →
      ∃ i : Int, a[spec.slot]? = some (.int i))
    (acc : List (List Value × Int)) (probes : Nat) :
    (bisectFallback F p0 spec acc probes).complete = true := by
  cases acc with
  | nil =>
      simpa [bisectFallback] using
        (optLoop_complete F p0 spec hg hread _ none rfl)
  | cons s rest =>
      simpa [bisectFallback] using
        (optLoopWith_complete F p0 spec hg hread _ (some s.1) (some s.2) rfl)

/-! ## The bisection loop -/

/-- Fuel-structural bisection.  The terminal check precedes the zero-fuel
    fallback.  SAT updates the exclusive upper key and prepends the
    incumbent; UNSAT updates the lower key; `.exhausted` falls back to the
    complete linear descent. -/
def bisectLoop (P : BisectProbe p0 spec) (F : CertSolver) :
    Nat → Int → Int → List (List Value × Int) → Option (List Value) → Nat →
      BisectRun
  | 0, lo, hi, acc, _, probes =>
      if lo ≥ hi then
        bisectTerminal acc probes
      else
        bisectFallback F p0 spec acc probes
  | fuel + 1, lo, hi, acc, prev, probes =>
      if lo ≥ hi then
        bisectTerminal acc probes
      else
        let mid := midKey lo hi
        match P.probe prev mid with
        | .sat a v =>
            bisectLoop P F fuel lo (optKey spec.dir v) ((a, v) :: acc)
              (some a) (probes + 1)
        | .unsat =>
            bisectLoop P F fuel (mid + 1) hi acc prev (probes + 1)
        | .exhausted => bisectFallback F p0 spec acc probes

/-! ## Streaming emission

The pure driver above returns only after the run.  The phase-2a emission
review replaces the CLI's post-run printing by an IO transliteration that
calls `emit` on each SAT-probe witness before the next probe.  `bisectLoopEmitSpec`
is the pure trace of that transliteration; `bisectLoopEmit_eq` proves the IO
loop emits exactly the trace and returns the trace's run.  Markers remain the
caller's responsibility and are emitted only after the loop returns. -/

/-- Pure trace of the streaming bisection loop.  `emitted` lists the new
    incumbents of this invocation in chronological order; `run` is the same
    run as `bisectLoop`.  A nonempty accumulator was already emitted by the
    caller, so only the fallback tail is new. -/
def bisectLoopEmitSpec (P : BisectProbe p0 spec) (F : CertSolver) :
    Nat → Int → Int → List (List Value × Int) → Option (List Value) → Nat →
      BisectEmitRun
  | 0, lo, hi, acc, _, probes =>
      if lo ≥ hi then
        ⟨bisectTerminal acc probes, []⟩
      else
        let r := bisectFallback F p0 spec acc probes
        ⟨r, r.sols.drop acc.length⟩
  | fuel + 1, lo, hi, acc, prev, probes =>
      if lo ≥ hi then
        ⟨bisectTerminal acc probes, []⟩
      else
        let mid := midKey lo hi
        match P.probe prev mid with
        | .sat a v =>
            let r := bisectLoopEmitSpec P F fuel lo (optKey spec.dir v)
              ((a, v) :: acc) (some a) (probes + 1)
            ⟨r.run, (a, v) :: r.emitted⟩
        | .unsat =>
            bisectLoopEmitSpec P F fuel (mid + 1) hi acc prev (probes + 1)
        | .exhausted =>
            let r := bisectFallback F p0 spec acc probes
            ⟨r, r.sols.drop acc.length⟩

/-- IO transliteration of `bisectLoopEmitSpec`: emit each SAT-probe witness
    immediately, then continue with the narrowed interval.  A fallback is a
    complete linear run; its fresh tail is emitted when it finishes. -/
def bisectLoopEmit (P : BisectProbe p0 spec) (F : CertSolver)
    (emit : List Value → IO Unit) :
    Nat → Int → Int → List (List Value × Int) → Option (List Value) → Nat →
      IO BisectEmitRun
  | 0, lo, hi, acc, _, probes =>
      if lo ≥ hi then
        pure ⟨bisectTerminal acc probes, []⟩
      else
        let r := bisectFallback F p0 spec acc probes
        let fresh := r.sols.drop acc.length
        emitAll (fun t : List Value × Int => emit t.1) fresh >>= fun _ =>
          pure ⟨r, fresh⟩
  | fuel + 1, lo, hi, acc, prev, probes =>
      if lo ≥ hi then
        pure ⟨bisectTerminal acc probes, []⟩
      else
        let mid := midKey lo hi
        match P.probe prev mid with
        | .sat a v =>
            emit a >>= fun _ =>
              bisectLoopEmit P F emit fuel lo (optKey spec.dir v) ((a, v) :: acc)
                (some a) (probes + 1) >>= fun r =>
                pure ⟨r.run, (a, v) :: r.emitted⟩
        | .unsat =>
            bisectLoopEmit P F emit fuel (mid + 1) hi acc prev (probes + 1)
        | .exhausted =>
            let r := bisectFallback F p0 spec acc probes
            let fresh := r.sols.drop acc.length
            emitAll (fun t : List Value × Int => emit t.1) fresh >>= fun _ =>
              pure ⟨r, fresh⟩

/-- The streaming trace returns exactly the pure loop's run. -/
theorem bisectLoopEmitSpec_run (P : BisectProbe p0 spec) (F : CertSolver) :
    ∀ fuel lo hi acc prev probes,
      (bisectLoopEmitSpec P F fuel lo hi acc prev probes).run =
        bisectLoop P F fuel lo hi acc prev probes := by
  intro fuel
  induction fuel with
  | zero =>
      intro lo hi acc prev probes
      by_cases hterm : lo ≥ hi
      · rw [bisectLoopEmitSpec, if_pos hterm, bisectLoop, if_pos hterm]
      · rw [bisectLoopEmitSpec, if_neg hterm, bisectLoop, if_neg hterm]
  | succ n ih =>
      intro lo hi acc prev probes
      by_cases hterm : lo ≥ hi
      · rw [bisectLoopEmitSpec, if_pos hterm, bisectLoop, if_pos hterm]
      · have hlt : lo < hi := by omega
        rw [bisectLoopEmitSpec, if_neg hterm, bisectLoop, if_neg hterm]
        cases hp : P.probe prev (midKey lo hi) with
        | sat a v =>
            simp only [hp]
            exact ih lo (optKey spec.dir v) ((a, v) :: acc) (some a) (probes + 1)
        | unsat =>
            simp only [hp]
            exact ih (midKey lo hi + 1) hi acc prev (probes + 1)
        | exhausted =>
            simp only [hp]

/-- Every incumbent emitted by the streaming trace is source-feasible. -/
theorem bisectLoopEmitSpec_sound (P : BisectProbe p0 spec) (F : CertSolver) :
    ∀ fuel lo hi acc prev probes,
      BisectAccInv p0 spec lo hi acc →
        ∀ t ∈ (bisectLoopEmitSpec P F fuel lo hi acc prev probes).emitted,
          t.1 ∈ allAssigns p0.domains ∧ accepts p0 t.1 = true ∧
            t.1[spec.slot]? = some (.int t.2) := by
  intro fuel
  induction fuel with
  | zero =>
      intro lo hi acc prev probes hinv t ht
      by_cases hterm : lo ≥ hi
      · simp [bisectLoopEmitSpec, hterm] at ht
      · have ht' : t ∈ (bisectFallback F p0 spec acc probes).sols.drop acc.length := by
          simpa [bisectLoopEmitSpec, hterm] using ht
        exact (bisectFallback_inv F p0 spec probes hinv).sound t
          (List.mem_of_mem_drop ht')
  | succ n ih =>
      intro lo hi acc prev probes hinv t ht
      by_cases hterm : lo ≥ hi
      · simp [bisectLoopEmitSpec, hterm] at ht
      · have hlt : lo < hi := by omega
        simp only [bisectLoopEmitSpec, if_neg hterm] at ht
        cases hp : P.probe prev (midKey lo hi) with
        | sat a v =>
            simp only [hp] at ht
            rcases List.mem_cons.mp ht with hhead | htail
            · subst hhead
              obtain ⟨hmem, hacc, hread, -⟩ :=
                P.sat_sound prev (midKey lo hi) a v hp
              exact ⟨hmem, hacc, hread⟩
            · exact ih lo (optKey spec.dir v) ((a, v) :: acc) (some a)
                (probes + 1)
                (bisectAccInv_sat hinv
                  (P.sat_sound prev (midKey lo hi) a v hp) (midKey_lt hlt))
                t htail
        | unsat =>
            simp only [hp] at ht
            exact ih (midKey lo hi + 1) hi acc prev (probes + 1)
              (bisectAccInv_unsat hinv
                (P.unsat_sound prev (midKey lo hi) hp)) t ht
        | exhausted =>
            simp only [hp] at ht
            exact (bisectFallback_inv F p0 spec probes hinv).sound t
              (List.mem_of_mem_drop ht)

/-- The IO streaming loop emits exactly the pure trace, in order, and returns
    the trace's run. -/
theorem bisectLoopEmit_eq (P : BisectProbe p0 spec) (F : CertSolver)
    (emit : List Value → IO Unit) :
    ∀ fuel lo hi acc prev probes,
      bisectLoopEmit P F emit fuel lo hi acc prev probes =
        (emitAll (fun t : List Value × Int => emit t.1)
            (bisectLoopEmitSpec P F fuel lo hi acc prev probes).emitted >>= fun _ =>
          pure (bisectLoopEmitSpec P F fuel lo hi acc prev probes)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro lo hi acc prev probes
      by_cases hterm : lo ≥ hi
      · rw [bisectLoopEmit, if_pos hterm, bisectLoopEmitSpec, if_pos hterm]
        simp only [emitAll, bisect_io_pure_bind]
      · rw [bisectLoopEmit, if_neg hterm, bisectLoopEmitSpec, if_neg hterm]
  | succ n ih =>
      intro lo hi acc prev probes
      by_cases hterm : lo ≥ hi
      · rw [bisectLoopEmit, if_pos hterm, bisectLoopEmitSpec, if_pos hterm]
        simp only [emitAll, bisect_io_pure_bind]
      · rw [bisectLoopEmit, if_neg hterm, bisectLoopEmitSpec, if_neg hterm]
        cases hp : P.probe prev (midKey lo hi) with
        | sat a v =>
            simp only [hp]
            rw [ih lo (optKey spec.dir v) ((a, v) :: acc) (some a) (probes + 1)]
            simp only [emitAll, bisect_io_bind_assoc, bisect_io_pure_bind]
        | unsat =>
            simp only [hp]
            exact ih (midKey lo hi + 1) hi acc prev (probes + 1)
        | exhausted =>
            simp only [hp]

theorem bisectLoop_inv (P : BisectProbe p0 spec) (F : CertSolver) :
    ∀ fuel lo hi acc prev probes,
      BisectAccInv p0 spec lo hi acc →
        BisectRunInv p0 spec (bisectLoop P F fuel lo hi acc prev probes) := by
  intro fuel
  induction fuel with
  | zero =>
      intro lo hi acc prev probes hinv
      by_cases hterm : lo ≥ hi
      · rw [bisectLoop, if_pos hterm]
        exact bisectTerminal_inv hinv (by omega)
      · rw [bisectLoop, if_neg hterm]
        exact bisectFallback_inv F p0 spec probes hinv
  | succ n ih =>
      intro lo hi acc prev probes hinv
      by_cases hterm : lo ≥ hi
      · rw [bisectLoop, if_pos hterm]
        exact bisectTerminal_inv hinv (by omega)
      · have hlt : lo < hi := by omega
        rw [bisectLoop, if_neg hterm]
        cases hp : P.probe prev (midKey lo hi) with
        | sat a v =>
            simp only [hp]
            exact ih lo (optKey spec.dir v) ((a, v) :: acc) (some a)
              (probes + 1)
              (bisectAccInv_sat hinv
                (P.sat_sound prev (midKey lo hi) a v hp) (midKey_lt hlt))
        | unsat =>
            simp only [hp]
            exact ih (midKey lo hi + 1) hi acc prev (probes + 1)
              (bisectAccInv_unsat hinv
                (P.unsat_sound prev (midKey lo hi) hp))
        | exhausted =>
            simp only [hp]
            exact bisectFallback_inv F p0 spec probes hinv

theorem bisectLoop_complete (P : BisectProbe p0 spec) (F : CertSolver)
    (hg : F.gate p0 = true)
    (hread : ∀ a ∈ allAssigns p0.domains, accepts p0 a = true →
      ∃ i : Int, a[spec.slot]? = some (.int i)) :
    ∀ fuel lo hi acc prev probes,
      (bisectLoop P F fuel lo hi acc prev probes).complete = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro lo hi acc prev probes
      by_cases hterm : lo ≥ hi
      · rw [bisectLoop, if_pos hterm]
        rfl
      · rw [bisectLoop, if_neg hterm]
        exact bisectFallback_complete F p0 spec hg hread acc probes
  | succ n ih =>
      intro lo hi acc prev probes
      by_cases hterm : lo ≥ hi
      · rw [bisectLoop, if_pos hterm]
        rfl
      · rw [bisectLoop, if_neg hterm]
        cases hp : P.probe prev (midKey lo hi) with
        | sat a v =>
            simp only [hp]
            exact ih lo (optKey spec.dir v) ((a, v) :: acc) (some a)
              (probes + 1)
        | unsat =>
            simp only [hp]
            exact ih (midKey lo hi + 1) hi acc prev (probes + 1)
        | exhausted =>
            simp only [hp]
            exact bisectFallback_complete F p0 spec hg hread acc probes

/-! ## The compiled-model driver -/

/-- The initial accumulator invariant from the root interval. -/
theorem rootBoundsInv {p0 : CompiledProblem DomConstraint}
    {spec : ObjectiveSpec} {lo hi : Int}
    (h : rootBounds? p0 spec = some (lo, hi)) :
    BisectAccInv p0 spec lo hi [] := by
  have hs := rootBounds?_sound h
  refine ⟨by simp, by simp, ?_, ?_, by simp⟩
  · intro b hb hacc w hw
    exact (hs b hb hacc w hw).1
  · intro _ b hb hacc w hw
    exact (hs b hb hacc w hw).2

/-- The pure bisection run for a compiled problem.  When the root bounds are
    unavailable, use the complete linear route `optLoop`. -/
def bisectRunFor (o : SearchConfig) (p0 : CompiledProblem DomConstraint)
    (spec : ObjectiveSpec) : BisectRun :=
  match rootBounds? p0 spec with
  | none =>
      let r := optLoop (lcgSolver o) p0 spec none
      ⟨r.sols, r.complete, r.lastBound, 0⟩
  | some (lo, hi) =>
      let S := lcgSolver o
      bisectLoop (certProbe S p0 spec) S ((hi - lo).toNat + 1) lo hi [] none 0

theorem bisectRunFor_inv (o : SearchConfig)
    (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec) :
    BisectRunInv p0 spec (bisectRunFor o p0 spec) := by
  unfold bisectRunFor
  split
  · rename_i hnone
    simpa using
      (loopInv_to_bisectRunInv (S := lcgSolver o) (p0 := p0) (spec := spec)
        (probes := 0) (hinv := optLoop_inv (lcgSolver o) p0 spec _ none rfl))
  · rename_i lo hi hsome
    exact bisectLoop_inv (certProbe (lcgSolver o) p0 spec) (lcgSolver o)
      _ lo hi [] none 0 (rootBoundsInv hsome)

theorem bisectRunFor_complete (o : SearchConfig)
    (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec)
    (hg : (lcgSolver o).gate p0 = true)
    (hread : ∀ a ∈ allAssigns p0.domains, accepts p0 a = true →
      ∃ i : Int, a[spec.slot]? = some (.int i)) :
    (bisectRunFor o p0 spec).complete = true := by
  unfold bisectRunFor
  split
  · exact optLoop_complete (lcgSolver o) p0 spec hg hread _ none rfl
  · exact bisectLoop_complete (certProbe (lcgSolver o) p0 spec) (lcgSolver o)
      hg hread _ _ _ [] none 0

/-- The source-level result of `--opt=bisect`. -/
structure BisectSummary where
  p : CompiledProblem DomConstraint
  run : OptRun
  probes : Nat

/-- The streaming source-level result.  `emitted` is the chronological list
    of incumbents already written by the streaming wrapper; it is a suffix of
    `run.sols` (the prefix, if any, was emitted by an earlier recursive
    call). -/
structure BisectStreamSummary where
  p : CompiledProblem DomConstraint
  run : OptRun
  probes : Nat
  emitted : List (List Value × Int)

/-- The certified bisection optimizer for a source model. -/
def optimizeBisect (o : SearchConfig) (m : Model) :
    Except String BisectSummary :=
  match compileModelOpt m with
  | .error e => .error e
  | .ok (p, spec) =>
      let r := bisectRunFor o p spec
      .ok ⟨p, r.toOptRun, r.probes⟩

theorem optimizeBisect_inv {o : SearchConfig} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun} {probes : Nat}
    (h : optimizeBisect o m = .ok ⟨p, run, probes⟩) :
    ∃ spec : ObjectiveSpec, compileModelOpt m = .ok (p, spec) ∧
      run = (bisectRunFor o p spec).toOptRun ∧
      probes = (bisectRunFor o p spec).probes := by
  unfold optimizeBisect at h
  cases hc : compileModelOpt m with
  | error e => rw [hc] at h; cases h
  | ok r =>
      obtain ⟨p', spec⟩ := r
      rw [hc] at h
      simp only [Except.ok.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨spec, rfl, rfl, rfl⟩

/-- The streaming certified bisection optimizer.  `emit` is called on each
    SAT-probe witness immediately, before the next probe.  The markers are
    not printed here; the CLI prints them only after this action returns and
    `run.complete` is true.  When the root objective bounds are unavailable
    the complete linear route is used; its solutions are emitted after that
    complete run returns. -/
def optimizeBisectStream (o : SearchConfig) (m : Model)
    (emit : Store → IO Unit) : IO (Except String BisectStreamSummary) :=
  match compileModelOpt m with
  | .error e => pure (.error e)
  | .ok (p, spec) =>
      match rootBounds? p spec with
      | none =>
          let r := optLoop (lcgSolver o) p spec none
          emitAll (fun t : List Value × Int => emit (p.toStore t.1)) r.sols >>= fun _ =>
            pure (.ok ⟨p, r, 0, r.sols⟩)
      | some (lo, hi) =>
          let S := lcgSolver o
          bisectLoopEmit (certProbe S p spec) S
              (fun a => emit (p.toStore a)) ((hi - lo).toNat + 1) lo hi [] none 0
            >>= fun r =>
              pure (.ok ⟨p, r.run.toOptRun, r.run.probes, r.emitted⟩)

/-- The streaming wrapper emits exactly the pure trace's incumbents, in order,
    and returns the trace's run.  This is the streaming analogue of
    `optimizeStream_eq`; the root-bounds fallback emits the complete linear
    run's solutions. -/
theorem optimizeBisectStream_eq (o : SearchConfig) (m : Model)
    (emit : Store → IO Unit) :
    optimizeBisectStream o m emit =
      (match compileModelOpt m with
       | .error e => pure (.error e)
       | .ok (p, spec) =>
           match rootBounds? p spec with
           | none =>
               let r := optLoop (lcgSolver o) p spec none
               emitAll (fun t : List Value × Int => emit (p.toStore t.1)) r.sols >>= fun _ =>
                 pure (.ok ⟨p, r, 0, r.sols⟩)
           | some (lo, hi) =>
               let S := lcgSolver o
               let r := bisectLoopEmitSpec (certProbe S p spec) S
                 ((hi - lo).toNat + 1) lo hi [] none 0
               emitAll (fun t : List Value × Int => emit (p.toStore t.1)) r.emitted >>= fun _ =>
                 pure (.ok ⟨p, r.run.toOptRun, r.run.probes, r.emitted⟩)) := by
  unfold optimizeBisectStream
  cases hc : compileModelOpt m with
  | error e => rfl
  | ok u =>
      obtain ⟨p, spec⟩ := u
      dsimp only
      cases hb : rootBounds? p spec with
      | none => rfl
      | some b =>
          obtain ⟨lo, hi⟩ := b
          dsimp only
          rw [bisectLoopEmit_eq (certProbe (lcgSolver o) p spec) (lcgSolver o)
            (fun a : List Value => emit (p.toStore a)) ((hi - lo).toNat + 1) lo hi [] none 0]
          simp only [bisect_io_bind_assoc, bisect_io_pure_bind]

/-! ## Source-level claims -/

theorem optimizeBisect_solution_sound {o : SearchConfig} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun} {probes : Nat}
    (h : optimizeBisect o m = .ok ⟨p, run, probes⟩)
    (hwf : WellFormed fullSig m) {t : List Value × Int}
    (ht : t ∈ run.sols) :
    Satisfies fullSig fullInterp m (p.toStore t.1) ∧
    LeanFzn.Semantics.ParamHonest m (p.toStore t.1) ∧
    m.solve.objective (p.toStore t.1) = some t.2 := by
  obtain ⟨spec, hc, hr, -⟩ := optimizeBisect_inv h
  have hinv := bisectRunFor_inv o p spec
  have ht' : t ∈ (bisectRunFor o p spec).sols := by
    simpa [BisectRun.toOptRun, hr] using ht
  obtain ⟨hmem, hacc, hv⟩ := hinv.sound t ht'
  obtain ⟨hsat, hpar, i, hi, hai⟩ := compileOpt_exact hc hwf hmem hacc
  rw [hv] at hai
  have : t.2 = i := by simpa using hai
  subst this
  exact ⟨⟨hwf, hsat⟩, hpar, hi⟩

theorem optimizeBisect_improving {o : SearchConfig} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun} {probes : Nat}
    (h : optimizeBisect o m = .ok ⟨p, run, probes⟩) :
    ∃ spec : ObjectiveSpec,
      run.sols.Pairwise (fun s t => betterB spec.dir t.2 s.2 = true) := by
  obtain ⟨spec, -, hr, -⟩ := optimizeBisect_inv h
  refine ⟨spec, ?_⟩
  rw [hr]
  simpa [BisectRun.toOptRun] using (bisectRunFor_inv o p spec).pairwise

/-- Every incumbent in the pure emission trace of a root-bounded bisection run
    is a source-satisfying store with the reported objective value.  Together
    with `optimizeBisectStream_eq`, this justifies every store the streaming
    CLI writes before the run returns. -/
theorem bisectLoopEmitSpec_solution_sound {o : SearchConfig} {m : Model}
    {p : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {lo hi : Int}
    (hc : compileModelOpt m = .ok (p, spec))
    (hroot : rootBounds? p spec = some (lo, hi))
    (hwf : WellFormed fullSig m) {t : List Value × Int}
    (ht : t ∈ (bisectLoopEmitSpec (certProbe (lcgSolver o) p spec) (lcgSolver o)
      ((hi - lo).toNat + 1) lo hi [] none 0).emitted) :
    Satisfies fullSig fullInterp m (p.toStore t.1) ∧
    LeanFzn.Semantics.ParamHonest m (p.toStore t.1) ∧
    m.solve.objective (p.toStore t.1) = some t.2 := by
  have hs := bisectLoopEmitSpec_sound (certProbe (lcgSolver o) p spec)
    (lcgSolver o) ((hi - lo).toNat + 1) lo hi [] none 0
    (rootBoundsInv hroot) t ht
  obtain ⟨hmem, hacc, hread⟩ := hs
  obtain ⟨hsat, hpar, i, hiobj, hai⟩ := compileOpt_exact hc hwf hmem hacc
  rw [hread] at hai
  have : t.2 = i := by simpa using hai
  subst this
  exact ⟨⟨hwf, hsat⟩, hpar, hiobj⟩

theorem optimizeBisect_optimal {o : SearchConfig} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun} {probes : Nat}
    (h : optimizeBisect o m = .ok ⟨p, run, probes⟩)
    (hwf : WellFormed fullSig m) (hcomp : run.complete = true)
    {t : List Value × Int} (hlast : run.sols.getLast? = some t) :
    IsSolution fullSig fullInterp m (p.toStore t.1) := by
  obtain ⟨spec, hc, hr, -⟩ := optimizeBisect_inv h
  have hinv := bisectRunFor_inv o p spec
  have hcomp' : (bisectRunFor o p spec).complete = true := by
    simpa [BisectRun.toOptRun, hr] using hcomp
  have hlast' : (bisectRunFor o p spec).sols.getLast? = some t := by
    simpa [BisectRun.toOptRun, hr] using hlast
  have ht : t ∈ (bisectRunFor o p spec).sols := List.mem_of_getLast? hlast'
  obtain ⟨hmem, hacc, hv⟩ := hinv.sound t ht
  have hopt := hinv.optimal_last hcomp' t hlast'
  refine compileOpt_optimal hc hwf hmem hacc hv ?_
  intro b hb
  cases hbnd : accepts (p.addConstraint (spec.improveBound t.2)) b with
  | false => rfl
  | true =>
      obtain ⟨w, hw⟩ := read_of_accepts_curP_some hbnd
      have haccb : accepts p b = true := (accepts_add.mp hbnd).1
      have hbetter : betterB spec.dir w t.2 = true :=
        (accepts_improve hbnd hw).2
      exact absurd hbetter (hopt b hb haccb w hw)

theorem optimizeBisect_unsat {o : SearchConfig} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun} {probes : Nat}
    (h : optimizeBisect o m = .ok ⟨p, run, probes⟩)
    (hwf : WellFormed fullSig m) (hcomp : run.complete = true)
    (hnil : run.sols = []) :
    ¬ ∃ store, Satisfies fullSig fullInterp m store ∧
      LeanFzn.Semantics.ParamHonest m store := by
  obtain ⟨spec, hc, hr, -⟩ := optimizeBisect_inv h
  have hinv := bisectRunFor_inv o p spec
  have hcomp' : (bisectRunFor o p spec).complete = true := by
    simpa [BisectRun.toOptRun, hr] using hcomp
  have hnil' : (bisectRunFor o p spec).sols = [] := by
    simpa [BisectRun.toOptRun, hr] using hnil
  rintro ⟨store, hs, hph⟩
  obtain ⟨b, hb, hbacc, -⟩ := compileOpt_covers hc hwf hs.2 hph
  obtain ⟨-, -, i, -, hi⟩ := compileOpt_exact hc hwf hb hbacc
  exact hinv.unsat_complete hcomp' hnil' b hb hbacc i hi

theorem optimizeBisect_total {o : SearchConfig} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun} {probes : Nat}
    (h : optimizeBisect o m = .ok ⟨p, run, probes⟩)
    (hwf : WellFormed fullSig m) (hg : (lcgSolver o).gate p = true) :
    run.complete = true := by
  obtain ⟨spec, hc, hr, -⟩ := optimizeBisect_inv h
  have hread : ∀ a ∈ allAssigns p.domains, accepts p a = true →
      ∃ i : Int, a[spec.slot]? = some (.int i) := by
    intro a hmem hacc
    obtain ⟨-, -, i, -, hai⟩ := compileOpt_exact hc hwf hmem hacc
    exact ⟨i, hai⟩
  rw [hr]
  simpa [BisectRun.toOptRun] using
    (bisectRunFor_complete o p spec hg hread)

end LeanFzn.Integration

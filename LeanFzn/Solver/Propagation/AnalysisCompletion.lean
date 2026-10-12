/-
File: LeanFzn/Solver/Propagation/AnalysisCompletion.lean

Purpose:
  B1 — the FINAL step: the analyzer's computed allowance cannot be exhausted.

  The measure is stated on the analyzer's own transitions (`analyzeNext`) and
  has two components, one per transition kind:

  * `workCost` — the worklist: one unit per clause plus one per literal it
    holds. Every SCAN transition strictly decreases it (a scanned literal or
    an already-empty clause leaves the worklist).
  * `skipCost` — the reason budget of the trail entries the analyzer has not
    yet reached. The frontier is named by the state's own `skip` literal (the
    pivot of the reason currently being scanned, or the whole trail before the
    first pivot), so no extra state is needed. Every PIVOT transition strictly
    decreases it: the seeded reason clause costs `|r| + 1` in the worklist
    while the frontier loses at least the pivot's own `|r| + 1` AND the
    previous frontier entry's `+1`.

  The INITIAL cost is therefore `1 + |conflict| + Σ(|reason| + 1)` over the
  trail, which the executable fuel covers — and the trace existence theorem
  turns that into "the analysis never runs out of fuel".

  The PIVOT payment is DERIVED, not assumed: `skipCost` is the frontier walk
  (`skipCostFrom`, a simple recursion that makes the stop/walk/bound facts
  definitional inductions), the state invariant `AnalyzerFrontier` names the
  ACTUAL skip/frontier and the initial-conflict case, and
  `skipCost_pivot_of_reachable` reads the retreat off it. Reason scans are
  exact by chronology (the `orderUpgrade` branch of `markLit` provably cannot
  fire while a frontier exists); the only phase where an upgraded falsifier
  can enter the marks is the initial conflict scan, whose payment is against
  the whole trail and needs no ordering at all. The final theorems take the
  reachable class `AnalyzerReachable` (`AnalysisProgress.lean`) instead of a
  per-state decrease hypothesis, and distinguish a semantic `none` (root
  contradiction / unsupported local explanation) from budget truncation on
  `analyzeAtAllowance`.

Dependencies:
  - LeanFzn.Solver.Propagation.RestorationCertificate: `TrailLiteralsDistinct`,
    `findEntryOf_isSome`, `findEntryOf_last_match`, `norm_negate_norm_local`.
  - LeanFzn.Solver.Propagation.AnalysisProgress: `AnalyzerState`, `AnalyzerStep`,
    `analyzeNext`, `analyzeLoop`, `initAnalysisState`, `AnalyzerTrailOk`,
    `AnalyzerReachable`, `AnalyzerInput`, `AnalysisOutcome`,
    `analyzeClassified`.
  - LeanFzn.Solver.Propagation.AnalysisInvariants: `BelowFalsified`, `markLit_invariants`.
  - LeanFzn.Solver.Propagation.Proofs.BranchState: `ReachableState` (trail discipline).

DAG:
  RestorationCertificate + AnalysisProgress + AnalysisInvariants
    -> LeanFzn.Solver.UIP.AnalysisCompletion
-/

import LeanFzn.Solver.Propagation.RestorationCertificate

open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-! ## The transition trace

`analyzeTrace` records how many transitions the loop takes before it stops,
and `none` when the fuel runs out first. It is the instrument that separates
"stopped" from "cut off by the fuel". -/

/-- Number of transitions performed, and the result, when the loop stops
within `fuel`; `none` when the fuel is exhausted first. -/
def analyzeTrace (trail : List TrailEntry) (lvl : Nat) :
    Nat → AnalyzerState → Option (Nat × Option (List (Literal × Nat) × Literal))
  | 0, _ => none
  | fuel + 1, st =>
      match analyzeNext trail lvl st with
      | .done r => some (1, r)
      | .next st' =>
          match analyzeTrace trail lvl fuel st' with
          | none => none
          | some (k, r) => some (k + 1, r)

/-- One step of the trace, with the recursive call's fuel exposed. -/
theorem analyzeTrace_succ (trail : List TrailEntry) (lvl : Nat) (fuel : Nat)
    (st : AnalyzerState) :
    analyzeTrace trail lvl (fuel + 1) st =
      (match analyzeNext trail lvl st with
       | .done res => some (1, res)
       | .next s =>
           match analyzeTrace trail lvl fuel s with
           | none => none
           | some (k, r) => some (k + 1, r)) := by
  simp only [analyzeTrace]

/-- The trace's result IS the loop's result. -/
theorem analyzeTrace_snd (trail : List TrailEntry) (lvl : Nat) :
    ∀ (fuel : Nat) (st : AnalyzerState) (k : Nat)
      (r : Option (List (Literal × Nat) × Literal)),
    analyzeTrace trail lvl fuel st = some (k, r) →
    analyzeLoop trail lvl fuel st = r := by
  intro fuel
  induction fuel with
  | zero => intro st k r h; simp [analyzeTrace] at h
  | succ fuel ih =>
      intro st k r h
      cases hn : analyzeNext trail lvl st with
      | done res => simp only [analyzeTrace, hn, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨-, rfl⟩ := h
                    simp [analyzeLoop, hn]
      | next st' =>
          cases ht : analyzeTrace trail lvl fuel st' with
          | none => simp [analyzeTrace, hn, ht] at h
          | some kr =>
              obtain ⟨k', r'⟩ := kr
              simp only [analyzeTrace, hn, ht, Option.some.injEq,
                Prod.mk.injEq] at h
              obtain ⟨-, rfl⟩ := h
              simp only [analyzeLoop, hn]
              exact ih st' k' r' ht

/-- The trace never overruns its fuel. -/
theorem analyzeTrace_steps_le (trail : List TrailEntry) (lvl : Nat) :
    ∀ (fuel : Nat) (st : AnalyzerState) (k : Nat)
      (r : Option (List (Literal × Nat) × Literal)),
    analyzeTrace trail lvl fuel st = some (k, r) → k ≤ fuel := by
  intro fuel
  induction fuel with
  | zero => intro st k r h; simp [analyzeTrace] at h
  | succ fuel ih =>
      intro st k r h
      cases hn : analyzeNext trail lvl st with
      | done res =>
          simp only [analyzeTrace, hn, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          omega
      | next st' =>
          cases ht : analyzeTrace trail lvl fuel st' with
          | none => simp [analyzeTrace, hn, ht] at h
          | some kr =>
              obtain ⟨k', r'⟩ := kr
              simp only [analyzeTrace, hn, ht, Option.some.injEq,
                Prod.mk.injEq] at h
              obtain ⟨rfl, -⟩ := h
              have hk := ih st' k' r' ht
              omega

/-- The trace is monotone in the fuel, so a stopped run stays stopped. -/
theorem analyzeTrace_mono (trail : List TrailEntry) (lvl : Nat) :
    ∀ (fuel : Nat) (st : AnalyzerState) (k : Nat)
      (r : Option (List (Literal × Nat) × Literal)),
    analyzeTrace trail lvl fuel st = some (k, r) →
    analyzeTrace trail lvl (fuel + 1) st = some (k, r) := by
  intro fuel
  induction fuel with
  | zero => intro st k r h; simp [analyzeTrace] at h
  | succ fuel ih =>
      intro st k r h
      cases hn : analyzeNext trail lvl st with
      | done res =>
          simp only [analyzeTrace, hn, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [analyzeTrace, hn]
      | next st' =>
          cases ht : analyzeTrace trail lvl fuel st' with
          | none => simp [analyzeTrace, hn, ht] at h
          | some kr =>
              obtain ⟨k', r'⟩ := kr
              simp only [analyzeTrace, hn, ht, Option.some.injEq,
                Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have ht' := ih st' k' r' ht
              rw [analyzeTrace_succ, hn]
              dsimp only
              rw [ht']

/-! ## The measure

`workCost` charges the worklist (one unit per clause, one per literal).
`skipCost` charges the reason budget of the entries the analyzer has not
reached yet: the frontier is named by the state's own `skip` literal (the
pivot whose reason is being scanned, or the whole trail before the first
pivot), so no extra state is needed — and crucially `skipCost` depends ONLY
on `trail` and `skip`, so a scan cannot increase it. -/

/-- Worklist cost: one unit per clause plus one unit per literal. -/
def workCost (cs : List Clause) : Nat := cs.length + (cs.map List.length).sum

/-- The reason-budget term charged for one trail entry: its reason clause's
length plus two. The `+2` is the round charge (one unit for the entry, one
for the extra step the loop takes to reach it). -/
def frontierTerm (e : TrailEntry) : Nat :=
  (e.reason.map (fun (r : Reason) => r.clause.length)).getD 0 + 2

/-- The frontier walk: the reason budget of the entries strictly before the
first entry whose literal is (syntactically) the skip literal. This is the
recursive form of the frontier prefix — it makes the three facts the payment
proofs need (`stop`, `walk`, `bound`) definitional inductions instead of
`List.takeWhile` reasoning. -/
def skipCostFrom (sl : Literal) : List TrailEntry → Nat
  | [] => 0
  | e :: es =>
      if litEqB e.literal sl then 0 else frontierTerm e + skipCostFrom sl es

/-- The reason budget of the entries at or before the frontier named by
`skip`: in the INITIAL-CONFLICT phase (`skip = none`) the whole trail is
still ahead of the analyzer; a named skip charges exactly the entries
strictly before the frontier entry. -/
def skipCost (trail : List TrailEntry) (skip : Option Literal) : Nat :=
  match skip with
  | none => (trail.map frontierTerm).sum
  | some sl => skipCostFrom sl trail

/-- THE MEASURE: worklist plus unreached reason budget. -/
def roundCost (trail : List TrailEntry) (st : AnalyzerState) : Nat :=
  workCost st.work + skipCost trail st.skip

/-! ### The frontier walk, arithmetically

The walk is a recursive sum, so the payment proofs are inductions on the
trail prefix rather than `takeWhile` manipulations. -/

/-- The walk stops with cost zero at a matching entry. -/
theorem skipCostFrom_stop (sl : Literal) (e : TrailEntry) (es : List TrailEntry)
    (h : litEqB e.literal sl = true) :
    skipCostFrom sl (e :: es) = 0 := by
  simp only [skipCostFrom, h, if_true]

/-- The walk charges a non-matching entry and continues. -/
theorem skipCostFrom_walk (sl : Literal) (e : TrailEntry) (es : List TrailEntry)
    (h : litEqB e.literal sl = false) :
    skipCostFrom sl (e :: es) = frontierTerm e + skipCostFrom sl es := by
  simp only [skipCostFrom]
  rw [h]
  exact if_neg (by simp)

/-- A prefix none of whose entries matches contributes a plain sum. -/
theorem skipCostFrom_eq_sum_of_no_match {sl : Literal} :
    ∀ {l : List TrailEntry}, (∀ x ∈ l, litEqB x.literal sl = false) →
      skipCostFrom sl l = (l.map frontierTerm).sum
  | [], _ => rfl
  | e :: es, h => by
      rw [skipCostFrom_walk sl e es (h e (List.mem_cons_self ..))]
      rw [skipCostFrom_eq_sum_of_no_match
        (fun x hx => h x (List.mem_cons_of_mem e hx))]
      simp [List.map_cons, List.sum_cons]

/-- A no-match prefix transfers its plain sum to the walk over an appended
rest. -/
theorem skipCostFrom_append_of_no_match {sl : Literal} {l : List TrailEntry}
    (h : ∀ x ∈ l, litEqB x.literal sl = false) (rest : List TrailEntry) :
    skipCostFrom sl (l ++ rest) = (l.map frontierTerm).sum + skipCostFrom sl rest := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.cons_append,
        skipCostFrom_walk sl x (xs ++ rest) (h x (List.mem_cons_self ..))]
      rw [ih (fun y hy => h y (List.mem_cons_of_mem x hy))]
      simp only [List.map_cons, List.sum_cons]
      omega

/-- A no-match prefix followed by a matching entry: the walk is exactly the
plain sum of the prefix. -/
theorem skipCostFrom_eq_sum_of_stop {sl : Literal} {l : List TrailEntry}
    (hno : ∀ x ∈ l, litEqB x.literal sl = false) {e : TrailEntry}
    {rest : List TrailEntry} (hm : litEqB e.literal sl = true) :
    skipCostFrom sl (l ++ e :: rest) = (l.map frontierTerm).sum := by
  rw [skipCostFrom_append_of_no_match hno, skipCostFrom_stop sl e rest hm,
    Nat.add_zero]

/-- The walk never exceeds the plain sum of the entries strictly before a
matching split point. No distinctness is needed: the bound holds for the
walk's early stop too. -/
theorem skipCostFrom_le_sum_of_split {sl : Literal} :
    ∀ {as : List TrailEntry} {e : TrailEntry} {bs : List TrailEntry},
      litEqB e.literal sl = true →
      skipCostFrom sl (as ++ e :: bs) ≤ (as.map frontierTerm).sum
  | [], e, bs, h => by
      rw [List.nil_append, skipCostFrom_stop sl e bs h]
      simp
  | x :: xs, e, bs, h => by
      rw [List.cons_append]
      by_cases hx : litEqB x.literal sl = true
      · rw [skipCostFrom_stop sl x (xs ++ e :: bs) hx, List.map_cons,
          List.sum_cons]
        exact Nat.zero_le _
      · have hxf : litEqB x.literal sl = false := by
          cases hl : litEqB x.literal sl <;> simp_all
        rw [skipCostFrom_walk sl x (xs ++ e :: bs) hxf, List.map_cons,
          List.sum_cons]
        have := skipCostFrom_le_sum_of_split (as := xs) (e := e) (bs := bs) h
        omega

/-! ### Worklist cost arithmetic -/

/-- Scanning a literal strictly decreases the worklist cost. -/
theorem workCost_scan (q : Literal) (qs : Clause) (cs : List Clause) :
    workCost (qs :: cs) < workCost ((q :: qs) :: cs) := by
  simp only [workCost, List.length_cons, List.map_cons, List.sum_cons]
  omega

/-- Dropping an already-empty clause strictly decreases the worklist cost. -/
theorem workCost_drop_empty (cs : List Clause) :
    workCost cs < workCost ([] :: cs) := by
  simp only [workCost, List.length_cons, List.map_cons, List.length_nil,
    List.sum_cons]
  omega

/-- Seeding the worklist with a reason clause costs one plus its length. -/
theorem workCost_seed (r : Clause) : workCost [r] = 1 + r.length := by
  simp [workCost]

/-- An empty worklist costs nothing. -/
theorem workCost_nil : workCost ([] : List Clause) = 0 := rfl

/-! ### The existence theorem

With the measure decreasing at every `analyzeNext` step, the trace of the
loop exists within the fuel the measure promises — i.e. the fuel is never
what stops the analysis. -/

theorem analyzeTrace_exists_of_decrease (trail : List TrailEntry) (lvl : Nat)
    (hstep : ∀ (st st' : AnalyzerState),
      analyzeNext trail lvl st = AnalyzerStep.next st' →
      roundCost trail st' < roundCost trail st) :
    ∀ (fuel : Nat) (st : AnalyzerState), roundCost trail st + 1 ≤ fuel →
      ∃ (k : Nat) (r : Option (List (Literal × Nat) × Literal)),
        analyzeTrace trail lvl fuel st = some (k, r) := by
  intro fuel
  induction fuel with
  | zero =>
      intro st h
      -- a strictly decreasing step is impossible, so the loop stops before cost 0
      cases hn : analyzeNext trail lvl st with
      | done res =>
          have : roundCost trail st + 1 ≤ 0 := h
          omega
      | next st' =>
          have := hstep st st' hn
          omega
  | succ fuel ih =>
      intro st h
      cases hn : analyzeNext trail lvl st with
      | done res => exact ⟨1, res, by rw [analyzeTrace_succ, hn]⟩
      | next st' =>
          have hlt := hstep st st' hn
          obtain ⟨k, r, hk⟩ := ih st' (by omega)
          refine ⟨k + 1, r, ?_⟩
          rw [analyzeTrace_succ, hn]
          dsimp only
          rw [hk]

/-! ### The step lemma

Every transition strictly decreases the measure. The three SCAN transitions
are purely structural: the worklist loses a clause or a literal, and
`skipCost` depends only on `trail` and `skip`, both of which a scan leaves
alone. The PIVOT transition needs the frontier fact: the pivot is at or
before the entry named by the previous `skip`, so the newly seeded reason
clause (`1 + |r|`) is paid for by the frontier losing the pivot's own
`|r| + 2` term. -/

/-- A scan transition strictly decreases the measure. -/
theorem roundCost_scan (q : Literal) (qs : Clause) (cs : List Clause)
    (skip : Option Literal) (marks : List TrailEntry)
    (learnt : List (Literal × Nat)) (marks' : List TrailEntry)
    (learnt' : List (Literal × Nat)) (trail : List TrailEntry) :
    roundCost trail { work := qs :: cs, skip := skip, marks := marks',
                      learnt := learnt' }
      < roundCost trail { work := (q :: qs) :: cs, skip := skip, marks := marks,
                          learnt := learnt } := by
  simp only [roundCost]
  have := workCost_scan q qs cs
  omega

/-- Dropping an already-empty clause strictly decreases the measure. -/
theorem roundCost_drop_empty (cs : List Clause) (skip : Option Literal)
    (marks : List TrailEntry) (learnt : List (Literal × Nat))
    (trail : List TrailEntry) :
    roundCost trail { work := cs, skip := skip, marks := marks, learnt := learnt }
      < roundCost trail { work := [] :: cs, skip := skip, marks := marks,
                          learnt := learnt } := by
  simp only [roundCost]
  have := workCost_drop_empty cs
  omega

/-- The PIVOT transition strictly decreases the measure, GIVEN the frontier
fact that the seeded clause is paid for. -/
theorem roundCost_pivot (r : Clause) (skip : Option Literal)
    (marks : List TrailEntry) (learnt : List (Literal × Nat))
    (e : TrailEntry) (trail : List TrailEntry)
    (hpay : skipCost trail (some e.literal) + (1 + r.length)
      < skipCost trail skip) :
    roundCost trail { work := [r], skip := some e.literal, marks := marks,
                      learnt := learnt }
      < roundCost trail { work := [], skip := skip, marks := marks,
                          learnt := learnt } := by
  simp only [roundCost, workCost_nil, workCost_seed]
  omega

/-! ### The initial cost, and the executable allowance

The initial state's measure is `1 + |conflict|` (the worklist) plus, over
every trail entry, its reason length `+ 2` (the reason budget and the round
charge). That is `1 + reasonBudget + 2 * |trail|`, which the executable
allowance covers for a NON-ROOT conflict — the supported input class the
plan names. -/

/-- The reason lengths of the trail, in `reasonBudget`'s own shape. -/
def reasonLens (trail : List TrailEntry) : List Nat :=
  trail.map fun e => match e.reason with
    | some r => r.clause.length
    | none => 0

/-- Their sum. -/
def reasonLenSum (trail : List TrailEntry) : Nat := (reasonLens trail).sum

/-- `reasonBudget` is the conflict clause plus this sum. -/
theorem reasonBudget_eq (c : Clause) (trail : List TrailEntry) :
    reasonBudget trail c = c.length + reasonLenSum trail := by
  simp only [reasonBudget, reasonLenSum, reasonLens]
  congr 1

/-- A generic list sum, shifted by two per element. -/
theorem sum_map_add_two (l : List Nat) :
    (l.map (fun n => n + 2)).sum = l.sum + 2 * l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
      omega

/-- The trail's `getD`-shaped reason lengths sum to `reasonLenSum`. -/
theorem sum_getD_eq (trail : List TrailEntry) :
    (trail.map (fun (e : TrailEntry) =>
      (e.reason.map (fun (r : Reason) => r.clause.length)).getD 0)).sum
      = reasonLenSum trail := by
  simp only [reasonLenSum, reasonLens]
  congr 1
  refine List.map_congr_left ?_
  intro e _
  cases e.reason <;> rfl

/-- The sum of reason lengths plus two per trail entry: the reason budget plus
the round charge. This is `skipCost trail none`, the initial frontier cost. -/
theorem sum_frontierTerm (trail : List TrailEntry) :
    (trail.map frontierTerm).sum = reasonLenSum trail + 2 * trail.length := by
  have hmap : trail.map frontierTerm
      = (trail.map (fun (e : TrailEntry) =>
          (e.reason.map (fun (r : Reason) => r.clause.length)).getD 0)).map
          (fun n => n + 2) := by
    rw [List.map_map]
    rfl
  rw [hmap, sum_map_add_two, sum_getD_eq, List.length_map]

/-- The initial frontier cost is the full trail sum. -/
theorem skipCost_none (trail : List TrailEntry) :
    skipCost trail none = (trail.map frontierTerm).sum := rfl

/-- The arithmetic of the initial measure: the `+ 2` per trail entry needs two
units per entry, which the conflict clause's own `|c| >= 1` pays for. -/
theorem initCost_arith (c : Clause) (trail : List TrailEntry)
    (hne : 1 ≤ c.length) :
    1 + c.length + (reasonLenSum trail + 2 * trail.length) + 1
      ≤ (c.length + reasonLenSum trail + 1) * (trail.length + 1) + 1 := by
  rw [Nat.mul_succ]
  have hT3 : 2 * trail.length ≤ (c.length + reasonLenSum trail + 1) * trail.length :=
    Nat.mul_le_mul_right trail.length (by omega)
  omega

/-- The executable allowance covers the initial measure plus the one unit the
loop needs to take its first step, on the supported (non-empty conflict)
input class. -/
theorem roundCost_init_add_one_le_analysisFuel (c : Clause)
    (trail : List TrailEntry) (hne : 1 ≤ c.length) :
    roundCost trail (initAnalysisState c) + 1 ≤ analysisFuel trail c := by
  have hsum := sum_frontierTerm trail
  have hmain := initCost_arith c trail hne
  have hlf := analysisAllowance_le_analysisFuel trail c
  have hbud := reasonBudget_eq c trail
  show workCost [c] + skipCost trail none + 1 ≤ analysisFuel trail c
  rw [workCost_seed, skipCost_none, hsum]
  have hmain' : 1 + c.length + (reasonLenSum trail + 2 * trail.length) + 1
      ≤ (c.length + reasonLenSum trail + 1) * (trail.length + 1) + 1 := hmain
  simp only [analysisAllowance] at hlf
  rw [hbud] at hlf
  exact Nat.le_trans hmain' hlf

/-! ### The old conditional restatement (kept)

`analysis_not_fuel_limited` remains as the generic conditional statement; the
reachable-input instantiation below derives its `hstep` from the redesigned
frontier invariant instead of asking for it. -/

/-- B1 COMPLETION (conditional): if every transition decreases the measure,
then the executable allowance cannot be exhausted on the supported input
class — the analysis always STOPS rather than being cut off by the fuel. -/
theorem analysis_not_fuel_limited (c : Clause) {trail : List TrailEntry}
    {lvl : Nat} (hne : 1 ≤ c.length)
    (hstep : ∀ (st st' : AnalyzerState),
      analyzeNext trail lvl st = AnalyzerStep.next st' →
      roundCost trail st' < roundCost trail st) :
    ∃ (k : Nat) (r : Option (List (Literal × Nat) × Literal)),
      analyzeTrace trail lvl (analysisFuel trail c) (initAnalysisState c)
        = some (k, r) :=
  analyzeTrace_exists_of_decrease trail lvl hstep (analysisFuel trail c)
    (initAnalysisState c) (roundCost_init_add_one_le_analysisFuel c trail hne)

/-! ## The redesigned frontier (P1.2 items 1–3)

The completion proof is now about the states the analyzer ACTUALLY reaches,
not about arbitrary worklists, skips and marks:

* the frontier is named by the state's own `skip` literal, and the invariant
  records that this literal is normalized, that its entry is a trail entry at
  the analysis level, and that the worklist is what that entry's reason
  seeded — with an explicit INITIAL-CONFLICT case (`skip = none`) where the
  worklist is what the conflict clause seeded;
* every mark is a trail entry at the analysis level and lies STRICTLY BEFORE
  the frontier entry;
* the learnt list records trail-falsified below-level pairs.

The pivot payment is DERIVED from the frontier retreat. For reason scans the
exact lookup is forced by chronology, so the `orderUpgrade` branch of
`markLit` provably cannot fire while a frontier exists; the only phase where
an upgraded falsifier can enter the marks is the INITIAL conflict scan, whose
payment is against the WHOLE trail and needs no ordering at all. -/

/-- Literal equality is literal equality. -/
theorem litEqB_eq_true_iff {a b : Literal} : litEqB a b = true ↔ a = b := by
  simp only [litEqB, decide_eq_true_eq]

/-- Literal inequality is literal inequality. -/
theorem litEqB_eq_false_iff {a b : Literal} : litEqB a b = false ↔ a ≠ b := by
  simp only [litEqB, decide_eq_false_iff_not]

theorem litEqB_self (l : Literal) : litEqB l l = true := by
  simp [litEqB]

/-- The lookup finds an entry that is on the trail, has the normalized
literal, and is the ONLY such entry (distinctness). -/
theorem findEntryOf_self {trail : List TrailEntry} {e : TrailEntry}
    (hdist : TrailLiteralsDistinct trail)
    (hnorm : ∀ e' ∈ trail, e'.literal = e'.literal.norm) (he : e ∈ trail) :
    findEntryOf trail e.literal = some e := by
  obtain ⟨e₂, h₂⟩ := findEntryOf_isSome he (hnorm e he)
  have heq : e₂ = e := hdist.1 e he e₂ (findEntryOf_mem trail _ e₂ h₂)
    (findEntryOf_literal trail _ e₂ h₂)
  rw [h₂, heq]

/-- Two distinct trail entries never carry the same literal. -/
theorem litEqB_false_of_ne {trail : List TrailEntry}
    (hdist : TrailLiteralsDistinct trail)
    (hnorm : ∀ e ∈ trail, e.literal = e.literal.norm)
    {x e : TrailEntry} (hx : x ∈ trail) (he : e ∈ trail) (hne : x ≠ e) :
    litEqB x.literal e.literal = false := by
  rw [litEqB_eq_false_iff]
  intro hlit
  exact hne (hdist.1 e he x hx (hlit.trans (hnorm e he)))

/-- Chronological order, split form: `a` strictly before `b` on the trail
decomposes the trail as `as ++ a :: mid ++ b :: bs`. This is the form the
frontier-retreat sum comparison consumes. -/
theorem exists_split_of_earlierThan {trail : List TrailEntry} {a b : TrailEntry}
    (h : TrailEntry.earlierThan trail a b) :
    ∃ as mid bs, trail = as ++ a :: mid ++ b :: bs := by
  obtain ⟨i, j, hi, hj, hia, hjb, hij⟩ := h
  refine ⟨trail.take i, (trail.drop (i + 1)).take (j - i - 1),
    trail.drop (j + 1), ?_⟩
  have hdrop : trail.drop i = a :: trail.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hi, hia]
  have hdrop2 : trail.drop j = b :: trail.drop (j + 1) := by
    rw [List.drop_eq_getElem_cons hj, hjb]
  have hji : i + 1 + (j - i - 1) = j := by omega
  calc trail
      = trail.take i ++ trail.drop i := (List.take_append_drop i trail).symm
    _ = trail.take i ++ a :: trail.drop (i + 1) := by rw [hdrop]
    _ = trail.take i
          ++ a :: ((trail.drop (i + 1)).take (j - i - 1)
            ++ (trail.drop (i + 1)).drop (j - i - 1)) := by
          rw [List.take_append_drop]
    _ = trail.take i ++ a :: (trail.drop (i + 1)).take (j - i - 1)
          ++ (trail.drop (i + 1)).drop (j - i - 1) := by
          simp only [List.cons_append, List.append_assoc]
    _ = trail.take i ++ a :: (trail.drop (i + 1)).take (j - i - 1)
          ++ trail.drop j := by
          rw [List.drop_drop, hji]
    _ = trail.take i ++ a :: (trail.drop (i + 1)).take (j - i - 1)
          ++ b :: trail.drop (j + 1) := by
          rw [hdrop2]

/-- In a duplicate-free list split as `as ++ b :: bs`, no prefix element is
`b`. -/
theorem ne_of_mem_of_nodup_split {α : Type} {l : List α} (hnd : l.Nodup)
    {as bs : List α} {b : α} (hs : l = as ++ b :: bs) :
    ∀ x ∈ as, x ≠ b := by
  have h := hnd
  rw [hs] at h
  exact fun x hx => (List.nodup_append.mp h).2.2 x hx b (List.mem_cons_self ..)

/-- Prefix membership transfers into the middle of a three-part split. -/
theorem mem_of_mem_triple {as mid bs : List TrailEntry} {a b x : TrailEntry}
    (hx : x ∈ as ++ a :: mid) : x ∈ as ++ a :: mid ++ b :: bs :=
  List.mem_append.mpr (Or.inl hx)

/-- Entries of a trail strictly after a mark are not marks: `nextPivot`
returns the LATEST matching entry, so everything after it failed the mark
test. -/
theorem nextPivot_after_not_mem {trail marks : List TrailEntry} {e : TrailEntry}
    (h : nextPivot trail marks = some e) :
    ∃ (as bs : List TrailEntry), trail = as ++ e :: bs ∧ ∀ x ∈ bs, x ∉ marks := by
  unfold nextPivot at h
  obtain ⟨-, as, bs, hrw, hno⟩ := List.find?_eq_some_iff_append.mp h
  refine ⟨bs.reverse, as.reverse, ?_, ?_⟩
  · have hsq := congrArg List.reverse hrw
    simpa using hsq
  · intro x hx hxmem
    have h1 : (marks.any fun m => litEqB m.literal x.literal) = false := by
      have := hno x (List.mem_reverse.mp hx)
      simpa using this
    have h2 : (marks.any fun m => litEqB m.literal x.literal) = true :=
      List.any_eq_true.mpr ⟨x, hxmem, by simp [litEqB]⟩
    rw [h2] at h1
    exact Bool.noConfusion h1

/-! ### Pivot payment (item 3): derived, not assumed -/

/-- INITIAL-CONFLICT payment: the first pivot's reason clause is paid for by
the WHOLE unreached trail budget, with no ordering hypothesis at all — which
is exactly why the order-upgrade path is harmless there. -/
theorem skipCost_initial {trail : List TrailEntry} {as bs : List TrailEntry}
    {e_p : TrailEntry} {r : Reason}
    (hsplit : trail = as ++ e_p :: bs) (hr : e_p.reason = some r) :
    skipCost trail (some e_p.literal) + (1 + r.clause.length)
      < skipCost trail none := by
  have hterm : frontierTerm e_p = r.clause.length + 2 := by
    simp [frontierTerm, hr]
  have hbound : skipCostFrom e_p.literal (as ++ e_p :: bs)
      ≤ (as.map frontierTerm).sum :=
    skipCostFrom_le_sum_of_split (litEqB_self _)
  have hsum : ((as ++ e_p :: bs).map frontierTerm).sum
      = (as.map frontierTerm).sum + (frontierTerm e_p
          + (bs.map frontierTerm).sum) := by
    simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons]
  rw [skipCost_none, hsplit]
  change skipCostFrom e_p.literal (as ++ e_p :: bs) + (1 + r.clause.length)
      < ((as ++ e_p :: bs).map frontierTerm).sum
  rw [hsum, hterm]
  omega

/-- FRONTIER-RETREAT payment: if the new pivot lies strictly before the
previous frontier entry, the frontier's budget pays for the seeded reason
clause. The split is the chronological decomposition of the retreat. -/
theorem skipCost_retreat {trail : List TrailEntry} {as mid bs : List TrailEntry}
    {e_p e_f : TrailEntry} {r : Reason}
    (hdist : TrailLiteralsDistinct trail)
    (hnorm : ∀ e ∈ trail, e.literal = e.literal.norm)
    (hsplit : trail = as ++ e_p :: mid ++ e_f :: bs)
    (hr : e_p.reason = some r) :
    skipCost trail (some e_p.literal) + (1 + r.clause.length)
      < skipCost trail (some e_f.literal) := by
  have hterm : frontierTerm e_p = r.clause.length + 2 := by
    simp [frontierTerm, hr]
  -- trail shape with e_f exposed as the tail head
  have hsplit2 : trail = (as ++ e_p :: mid) ++ e_f :: bs := hsplit
  -- trail shape with the tail after `e_p` regrouped
  have hsplit3 : trail = as ++ e_p :: (mid ++ e_f :: bs) := by
    rw [hsplit]
    simp only [List.append_assoc, List.cons_append]
  have hnd : trail.Nodup := hdist.2
  -- everything before e_f is not e_f
  have hne_f : ∀ x ∈ as ++ e_p :: mid, x ≠ e_f :=
    ne_of_mem_of_nodup_split hnd hsplit2
  have he_f_trail : e_f ∈ trail := by rw [hsplit]; simp
  -- the no-match facts for the walk to e_f
  have hno_f : ∀ x ∈ as ++ e_p :: mid, litEqB x.literal e_f.literal = false := by
    intro x hx
    have hxmem : x ∈ trail := by
      rw [hsplit]
      exact mem_of_mem_triple (as := as) (mid := mid) (b := e_f) (bs := bs) hx
    exact litEqB_false_of_ne hdist hnorm hxmem he_f_trail (hne_f x hx)
  -- the walk to e_f passes through all of `as ++ e_p :: mid`
  have hwalk_f : ((as ++ e_p :: mid).map frontierTerm).sum
      ≤ skipCostFrom e_f.literal trail := by
    rw [hsplit]
    rw [skipCostFrom_append_of_no_match hno_f,
      skipCostFrom_stop e_f.literal e_f bs (litEqB_self _), Nat.add_zero]
    exact Nat.le_refl _
  -- the walk to e_p stops inside `as`
  have hwalk_p : skipCostFrom e_p.literal trail ≤ (as.map frontierTerm).sum := by
    rw [hsplit3]
    exact skipCostFrom_le_sum_of_split (as := as) (e := e_p)
      (bs := mid ++ e_f :: bs) (litEqB_self e_p.literal)
  have hsum : ((as ++ e_p :: mid).map frontierTerm).sum
      = (as.map frontierTerm).sum + (frontierTerm e_p
          + (mid.map frontierTerm).sum) := by
    simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons]
  rw [skipCost]
  change skipCostFrom e_p.literal trail + (1 + r.clause.length)
      < skipCostFrom e_f.literal trail
  rw [hsum, hterm] at hwalk_f
  omega

/-! ### The reason scan is exact: the order-upgrade path is excluded -/

/-- On a reason clause scan, chronology supplies an EXACT falsifier of every
non-pivot literal, so the exact lookup of `markLit` succeeds and the
`orderUpgrade` branch cannot fire. The entry the lookup returns is the
chronology witness itself (distinctness makes it unique), so the frontier
retreat covers the mark. -/
theorem reason_lookup_exact {trail : List TrailEntry} {e_f : TrailEntry}
    {r : Reason}
    (hdist : TrailLiteralsDistinct trail)
    (hnorm : ∀ e ∈ trail, e.literal = e.literal.norm)
    (he_f : e_f ∈ trail) (hr : e_f.reason = some r)
    (hchron : ∀ l ∈ r.clause, l ≠ e_f.literal →
      ∃ e' ∈ trail, e'.literal = l.negate ∧ TrailEntry.earlierThan trail e' e_f)
    {q0 : Literal} (hq : q0 ∈ r.clause) (hne : q0.norm ≠ e_f.literal) :
    ∃ e', findEntryOf trail (q0.norm).negate = some e' ∧
      e'.literal = q0.negate ∧ TrailEntry.earlierThan trail e' e_f := by
  have hqne : q0 ≠ e_f.literal := fun hh => hne (by rw [hh]; exact (hnorm e_f he_f).symm)
  obtain ⟨e', he'mem, he'lit, hlt⟩ := hchron q0 hq hqne
  have hnormT : e'.literal = ((q0.norm).negate).norm := by
    calc e'.literal = e'.literal.norm := hnorm e' he'mem
      _ = (q0.negate).norm := by rw [he'lit]
      _ = ((q0.norm).negate).norm := by rw [norm_negate_norm_local q0]
  refine ⟨e', ?_, he'lit, hlt⟩
  obtain ⟨e₂, h₂⟩ := findEntryOf_isSome he'mem hnormT
  have huniq : e₂ = e' := by
    refine hdist.1 e' he'mem e₂ (findEntryOf_mem trail _ e₂ h₂) ?_
    rw [findEntryOf_literal trail _ e₂ h₂, hnormT, norm_norm]
  rw [h₂, huniq]

/-! ### `markLit`'s exact result shape -/

/-- `markLit` with both dedup checks failed and the exact lookup known: its
result is decided by the falsifier's level alone. -/
theorem markLit_eq_of_lookup {trail : List TrailEntry} {lvl : Nat}
    {marks : List TrailEntry} {learnt : List (Literal × Nat)} {q0 : Literal}
    {e : TrailEntry}
    (h1 : (marks.any fun m => litEqB m.literal (q0.norm).negate.norm) = false)
    (h2 : (learnt.any fun p => litEqB p.1 (q0.norm)) = false)
    (hf : findEntryOf trail (q0.norm).negate = some e) :
    markLit trail lvl marks learnt q0.norm =
      (if (e.level == 0) = true then some (marks, learnt)
       else if (e.level == lvl) = true then some (e :: marks, learnt)
       else some (marks, ((q0.norm), e.level) :: learnt)) := by
  simp only [markLit, norm_norm, h1, h2, hf, Bool.false_eq_true, if_false, if_true]

/-- `markLit`'s already-marked shortcut leaves the state alone. -/
theorem markLit_eq_same_of_marks {trail : List TrailEntry} {lvl : Nat}
    {marks : List TrailEntry} {learnt : List (Literal × Nat)} {q0 : Literal}
    (h1 : (marks.any fun m => litEqB m.literal (q0.norm).negate.norm) = true) :
    markLit trail lvl marks learnt q0.norm = some (marks, learnt) := by
  simp only [markLit, norm_norm, h1, Bool.true_eq_false, if_true, if_false]

/-- `markLit`'s already-learnt shortcut leaves the state alone. -/
theorem markLit_eq_same_of_learnt {trail : List TrailEntry} {lvl : Nat}
    {marks : List TrailEntry} {learnt : List (Literal × Nat)} {q0 : Literal}
    (h1 : (marks.any fun m => litEqB m.literal (q0.norm).negate.norm) = false)
    (h2 : (learnt.any fun p => litEqB p.1 (q0.norm)) = true) :
    markLit trail lvl marks learnt q0.norm = some (marks, learnt) := by
  simp only [markLit, norm_norm, h1, h2, Bool.false_eq_true, if_false, if_true]

/-! ### The redesigned frontier invariant -/

/-- THE ANALYZER FRONTIER INVARIANT (P1.2 item 1). It is stated on the
ACTUAL `skip`/frontier and worklist of the transition system:

1. the learnt list records trail-falsified below-level pairs (B2's
   `BelowFalsified`);
2. every mark is a trail entry at the analysis level;
3. when `skip = some sl` names a frontier: `sl` is normalized, the frontier
   entry is findable on the trail, is a trail entry at the analysis level
   with a reason whose clause SUFFIXES the worklist, and every mark lies
   STRICTLY BEFORE it;
4. in the INITIAL-CONFLICT phase (`skip = none`) the worklist suffixes the
   conflict clause. -/
def AnalyzerFrontier (trail : List TrailEntry) (lvl : Nat) (c : Clause)
    (st : AnalyzerState) : Prop :=
  BelowFalsified trail st.learnt ∧
  (∀ m ∈ st.marks, m ∈ trail ∧ m.level = lvl) ∧
  (∀ sl, st.skip = some sl → sl = sl.norm ∧
    ∃ e, findEntryOf trail sl = some e ∧ e ∈ trail ∧ e.level = lvl ∧
      (∃ r, e.reason = some r ∧ ∀ cl ∈ st.work, cl <:+ r.clause) ∧
      ∀ m ∈ st.marks, ∃ as mid bs, trail = as ++ m :: mid ++ e :: bs) ∧
  (st.skip = none → ∀ cl ∈ st.work, cl <:+ c)

/-- Initialization (item 2): the empty worklist state has no marks, no
learnt pairs, and an empty skip, so every conjunct holds vacuously except
the initial-conflict one, which is `c <:+ c`. -/
theorem analyzerFrontier_init {trail : List TrailEntry} {lvl : Nat} {c : Clause}
    (hok : AnalyzerTrailOk trail) :
    AnalyzerFrontier trail lvl c (initAnalysisState c) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    simp [initAnalysisState] at hp
  · intro m hm
    simp [initAnalysisState] at hm
  · intro sl hsl
    simp [initAnalysisState] at hsl
  · intro _ cl hcl
    rw [show cl = c from by simpa [initAnalysisState] using hcl]
    exact List.suffix_refl c

/-- PIVOT preservation (item 2): the frontier retreats to the latest mark.
Every surviving mark was at or before the pivot (`nextPivot` returns the
latest matching entry), the pivot's own literal is filtered out, and
distinctness identifies entries by their literal — so every survivor lies
strictly before the new frontier entry. -/
theorem analyzerFrontier_pivot {trail : List TrailEntry} {lvl : Nat}
    {c : Clause} {skip : Option Literal} {marks : List TrailEntry}
    {learnt : List (Literal × Nat)}
    (hok : AnalyzerTrailOk trail)
    (hinv : AnalyzerFrontier trail lvl c
      { work := [], skip := skip, marks := marks, learnt := learnt })
    {e : TrailEntry} {r : Reason}
    (hnp : nextPivot trail marks = some e) (hr : e.reason = some r) :
    AnalyzerFrontier trail lvl c
      { work := [r.clause], skip := some e.literal,
        marks := marks.filter (fun m => !litEqB m.literal e.literal),
        learnt := learnt } := by
  obtain ⟨hb, hmk, -, -⟩ := hinv
  have he_trail : e ∈ trail := nextPivot_trail_mem trail marks e hnp
  obtain ⟨m₀, hm₀mem, hm₀lit⟩ := nextPivot_mark trail marks e hnp
  have he_marks : e ∈ marks := by
    have hsame : m₀ = e := hok.distinct.1 e he_trail m₀ (hmk m₀ hm₀mem).1
      (hm₀lit.trans (hok.norm e he_trail))
    rw [← hsame]
    exact hm₀mem
  have he_level : e.level = lvl := (hmk e he_marks).2
  obtain ⟨as₀, bs₀, hsplit₀, hafter⟩ := nextPivot_after_not_mem hnp
  refine ⟨hb, ?_, ?_, ?_⟩
  · intro m hm
    exact hmk m (List.mem_filter.mp hm).1
  · intro sl hsl
    rw [Option.some.injEq] at hsl
    subst hsl
    refine ⟨hok.norm e he_trail, ?_⟩
    refine ⟨e, findEntryOf_self hok.distinct hok.norm he_trail, he_trail,
      he_level, ?_, ?_⟩
    · refine ⟨r, hr, ?_⟩
      intro cl hcl
      rw [List.mem_singleton] at hcl
      subst hcl
      exact List.suffix_refl r.clause
    · intro m hm
      have hm' := List.mem_filter.mp hm
      have hm_lit : litEqB m.literal e.literal = false := by simpa using hm'.2
      have hm_trail : m ∈ trail := (hmk m hm'.1).1
      have hme : m ≠ e := by
        intro hh
        rw [hh, litEqB_self] at hm_lit
        exact Bool.noConfusion hm_lit
      have hm_as : m ∈ as₀ := by
        have h2 : m ∈ as₀ ++ e :: bs₀ := by rw [← hsplit₀]; exact hm_trail
        rcases List.mem_append.mp h2 with h | h
        · exact h
        · rcases List.mem_cons.mp h with h' | h'
          · exact absurd h' hme
          · exact absurd hm'.1 (hafter m h')
      obtain ⟨as₁, mid, has⟩ := List.mem_iff_append.mp hm_as
      exact ⟨as₁, mid, bs₀, by rw [hsplit₀, has]⟩
  · intro hcontra
    exact absurd hcontra (by simp)

/-- SUFFIX TRANSFER through a scan: the new worklist's clauses — the tail
`qs` of the scanned head, plus the untouched continuation — are suffixes
whenever the old worklist's were. -/
theorem scan_suffix {q0 : Literal} {qs : Clause} {cs : List Clause}
    {r : Clause} (hwork : ∀ c ∈ (q0 :: qs) :: cs, c <:+ r) :
    ∀ c ∈ qs :: cs, c <:+ r := by
  intro c hc
  rcases List.mem_cons.mp hc with hc | hc
  · rw [hc]
    exact (List.suffix_cons q0 qs).trans
      (hwork (q0 :: qs) (List.mem_cons_self ..))
  · exact hwork c (List.mem_cons_of_mem (q0 :: qs) hc)

/-- DROP-EMPTY preservation: the worklist only shrinks, and only by losing
its head; everything the frontier seeded stays in the tail. -/
theorem analyzerFrontier_dropEmpty {trail : List TrailEntry} {lvl : Nat}
    {c : Clause} {cs : List Clause} {skip : Option Literal}
    {marks : List TrailEntry} {learnt : List (Literal × Nat)}
    (hinv : AnalyzerFrontier trail lvl c
      { work := [] :: cs, skip := skip, marks := marks, learnt := learnt }) :
    AnalyzerFrontier trail lvl c
      { work := cs, skip := skip, marks := marks, learnt := learnt } := by
  obtain ⟨hb, hmk, hfr, hinit⟩ := hinv
  refine ⟨hb, hmk, ?_, ?_⟩
  · intro sl hsl
    obtain ⟨hn, e, hfe, het, hel, ⟨r, hre, hwork⟩, hret⟩ := hfr sl hsl
    exact ⟨hn, e, hfe, het, hel,
      ⟨r, hre, fun cl hcl => hwork cl (List.mem_cons_of_mem _ hcl)⟩, hret⟩
  · intro hskip cl hcl
    exact hinit hskip cl (List.mem_cons_of_mem _ hcl)

/-- SKIP-SCAN preservation: the skipped literal leaves the worklist; the
frontier, marks and learnt list are untouched. -/
theorem analyzerFrontier_skipScan {trail : List TrailEntry} {lvl : Nat}
    {c : Clause} {q0 : Literal} {qs : Clause} {cs : List Clause}
    {skip : Option Literal} {marks : List TrailEntry}
    {learnt : List (Literal × Nat)}
    (hinv : AnalyzerFrontier trail lvl c
      { work := (q0 :: qs) :: cs, skip := skip, marks := marks,
        learnt := learnt }) :
    AnalyzerFrontier trail lvl c
      { work := qs :: cs, skip := skip, marks := marks, learnt := learnt } := by
  obtain ⟨hb, hmk, hfr, hinit⟩ := hinv
  refine ⟨hb, hmk, ?_, ?_⟩
  · intro sl hsl
    obtain ⟨hn, e, hfe, het, hel, ⟨r, hre, hwork⟩, hret⟩ := hfr sl hsl
    exact ⟨hn, e, hfe, het, hel, ⟨r, hre, scan_suffix hwork⟩, hret⟩
  · intro hskip cl hcl
    exact scan_suffix (hinit hskip) cl hcl

/-- MARK-SCAN preservation (item 2): `markLit` may only ADD the exact
falsifier of the scanned literal. In the frontier phase chronology forces
that exact lookup (the `orderUpgrade` branch is provably dead), and the
falsifier lies strictly before the frontier entry — so the new mark does
too. -/
theorem analyzerFrontier_markScan {trail : List TrailEntry} {lvl : Nat}
    {c : Clause} {q0 : Literal} {qs : Clause} {cs : List Clause}
    {skip : Option Literal} {marks marks' : List TrailEntry}
    {learnt learnt' : List (Literal × Nat)}
    (hok : AnalyzerTrailOk trail)
    (hinv : AnalyzerFrontier trail lvl c
      { work := (q0 :: qs) :: cs, skip := skip, marks := marks,
        learnt := learnt })
    (hskip : skipEq skip q0.norm = false)
    (hm : markLit trail lvl marks learnt q0.norm = some (marks', learnt')) :
    AnalyzerFrontier trail lvl c
      { work := qs :: cs, skip := skip, marks := marks', learnt := learnt' } := by
  obtain ⟨hb, hmk, hfr, hinit⟩ := hinv
  obtain ⟨hb', hon', hcur'⟩ :=
    markLit_invariants trail lvl marks learnt q0.norm marks' learnt' hb
      (fun m hm' => (hmk m hm').1) (fun m hm' => (hmk m hm').2) hm
  have hmk' : ∀ m ∈ marks', m ∈ trail ∧ m.level = lvl :=
    fun m hm' => ⟨hon' m hm', hcur' m hm'⟩
  refine ⟨hb', hmk', ?_, ?_⟩
  · intro sl hsl
    obtain ⟨hn, e_f, hfe, hef_trail, hef_lvl, ⟨r_f, hrf, hwork⟩, hret⟩ :=
      hfr sl hsl
    have hq0_f : q0 ∈ r_f.clause := by
      obtain ⟨t, ht⟩ := hwork (q0 :: qs) (List.mem_cons_self ..)
      rw [← ht]
      simp
    have hne_norm : q0.norm ≠ e_f.literal := by
      have hsl' : skip = some sl := hsl
      have h1 : litEqB q0.norm sl = false := by
        have h2 := hskip
        rw [hsl'] at h2
        simpa only [skipEq] using h2
      have h3 : e_f.literal = sl := by
        rw [findEntryOf_literal trail sl e_f hfe, ← hn]
      rw [h3]
      exact litEqB_eq_false_iff.mp h1
    have hchron := hok.chron e_f hef_trail r_f (by rw [hrf]; simp)
    obtain ⟨e', hf', he'lit, hlt⟩ :=
      reason_lookup_exact hok.distinct hok.norm hef_trail hrf hchron hq0_f hne_norm
    refine ⟨hn, e_f, hfe, hef_trail, hef_lvl,
      ⟨r_f, hrf, scan_suffix hwork⟩, ?_⟩
    intro m hm'
    by_cases hmem : m ∈ marks
    · exact hret m hmem
    · have hnew : m = e' := by
        by_cases h1 : (marks.any fun m' => litEqB m'.literal (q0.norm).negate.norm) = true
        · rw [markLit_eq_same_of_marks h1] at hm
          simp only [Option.some.injEq, Prod.mk.injEq] at hm
          exact absurd (hm.1 ▸ hm') hmem
        · have h1f : (marks.any fun m' => litEqB m'.literal (q0.norm).negate.norm) = false := by
            cases hh : (marks.any fun m' => litEqB m'.literal (q0.norm).negate.norm)
            · rfl
            · exact absurd hh h1
          by_cases h2 : (learnt.any fun p => litEqB p.1 (q0.norm)) = true
          · rw [markLit_eq_same_of_learnt h1f h2] at hm
            simp only [Option.some.injEq, Prod.mk.injEq] at hm
            exact absurd (hm.1 ▸ hm') hmem
          · have h2f : (learnt.any fun p => litEqB p.1 (q0.norm)) = false := by
              cases hh : (learnt.any fun p => litEqB p.1 (q0.norm))
              · rfl
              · exact absurd hh h2
            rw [markLit_eq_of_lookup h1f h2f hf'] at hm
            by_cases hl0 : (e'.level == 0) = true
            · rw [if_pos hl0] at hm
              simp only [Option.some.injEq, Prod.mk.injEq] at hm
              exact absurd (hm.1 ▸ hm') hmem
            · rw [if_neg hl0] at hm
              by_cases hl : (e'.level == lvl) = true
              · rw [if_pos hl] at hm
                simp only [Option.some.injEq, Prod.mk.injEq] at hm
                rcases List.mem_cons.mp (hm.1 ▸ hm') with h' | h'
                · exact h'
                · exact absurd h' hmem
              · rw [if_neg hl] at hm
                simp only [Option.some.injEq, Prod.mk.injEq] at hm
                exact absurd (hm.1 ▸ hm') hmem
      rw [hnew]
      exact exists_split_of_earlierThan hlt
  · intro hskip_none cl hcl
    exact scan_suffix (hinit hskip_none) cl hcl

/-! ### `analyzeNext` in explicit shapes

The four `.next` transitions and the three `.done` stops, stated on the
explicit state forms, so the preservation and decrease proofs dispatch on
the transition the state actually takes. -/

theorem analyzeNext_noPivot (trail : List TrailEntry) (lvl : Nat)
    (skip : Option Literal) (marks : List TrailEntry)
    (learnt : List (Literal × Nat)) (hnp : nextPivot trail marks = none) :
    analyzeNext trail lvl
      { work := [], skip := skip, marks := marks, learnt := learnt }
      = AnalyzerStep.done none := by
  simp only [analyzeNext, hnp]

theorem analyzeNext_pivot_done (trail : List TrailEntry) (lvl : Nat)
    (skip : Option Literal) (marks : List TrailEntry)
    (learnt : List (Literal × Nat)) (e : TrailEntry)
    (hnp : nextPivot trail marks = some e)
    (hq : (marks.filter (fun m => !litEqB m.literal e.literal)).isEmpty = true) :
    analyzeNext trail lvl
      { work := [], skip := skip, marks := marks, learnt := learnt }
      = AnalyzerStep.done (some (learnt, e.literal)) := by
  simp only [analyzeNext, hnp, hq, if_true]

theorem analyzeNext_pivot_none_reason (trail : List TrailEntry) (lvl : Nat)
    (skip : Option Literal) (marks : List TrailEntry)
    (learnt : List (Literal × Nat)) (e : TrailEntry)
    (hnp : nextPivot trail marks = some e)
    (hq : ¬((marks.filter (fun m => !litEqB m.literal e.literal)).isEmpty = true))
    (hr : e.reason = none) :
    analyzeNext trail lvl
      { work := [], skip := skip, marks := marks, learnt := learnt }
      = AnalyzerStep.done none := by
  simp only [analyzeNext, hnp, if_neg hq, hr]

theorem analyzeNext_pivot (trail : List TrailEntry) (lvl : Nat)
    (skip : Option Literal) (marks : List TrailEntry)
    (learnt : List (Literal × Nat)) (e : TrailEntry) (r : Reason)
    (hnp : nextPivot trail marks = some e)
    (hq : ¬((marks.filter (fun m => !litEqB m.literal e.literal)).isEmpty = true))
    (hr : e.reason = some r) :
    analyzeNext trail lvl
      { work := [], skip := skip, marks := marks, learnt := learnt }
      = AnalyzerStep.next
          { work := [r.clause], skip := some e.literal,
            marks := marks.filter (fun m => !litEqB m.literal e.literal),
            learnt := learnt } := by
  simp only [analyzeNext, hnp, if_neg hq, hr]

theorem analyzeNext_dropEmpty (trail : List TrailEntry) (lvl : Nat)
    (cs : List Clause) (skip : Option Literal) (marks : List TrailEntry)
    (learnt : List (Literal × Nat)) :
    analyzeNext trail lvl
      { work := [] :: cs, skip := skip, marks := marks, learnt := learnt }
      = AnalyzerStep.next
          { work := cs, skip := skip, marks := marks, learnt := learnt } := by
  simp only [analyzeNext]

theorem analyzeNext_skipScan (trail : List TrailEntry) (lvl : Nat)
    (q0 : Literal) (qs : Clause) (cs : List Clause) (skip : Option Literal)
    (marks : List TrailEntry) (learnt : List (Literal × Nat))
    (hs : skipEq skip q0.norm = true) :
    analyzeNext trail lvl
      { work := (q0 :: qs) :: cs, skip := skip, marks := marks, learnt := learnt }
      = AnalyzerStep.next
          { work := qs :: cs, skip := skip, marks := marks, learnt := learnt } := by
  simp only [analyzeNext, hs, if_true]

theorem analyzeNext_markScan_none (trail : List TrailEntry) (lvl : Nat)
    (q0 : Literal) (qs : Clause) (cs : List Clause) (skip : Option Literal)
    (marks : List TrailEntry) (learnt : List (Literal × Nat))
    (hs : skipEq skip q0.norm = false)
    (hm : markLit trail lvl marks learnt q0.norm = none) :
    analyzeNext trail lvl
      { work := (q0 :: qs) :: cs, skip := skip, marks := marks, learnt := learnt }
      = AnalyzerStep.done none := by
  simp only [analyzeNext, hs, Bool.false_eq_true, if_false, hm]

theorem analyzeNext_markScan (trail : List TrailEntry) (lvl : Nat)
    (q0 : Literal) (qs : Clause) (cs : List Clause) (skip : Option Literal)
    (marks : List TrailEntry) (learnt : List (Literal × Nat))
    (marks' : List TrailEntry) (learnt' : List (Literal × Nat))
    (hs : skipEq skip q0.norm = false)
    (hm : markLit trail lvl marks learnt q0.norm = some (marks', learnt')) :
    analyzeNext trail lvl
      { work := (q0 :: qs) :: cs, skip := skip, marks := marks, learnt := learnt }
      = AnalyzerStep.next
          { work := qs :: cs, skip := skip, marks := marks', learnt := learnt' } := by
  simp only [analyzeNext, hs, Bool.false_eq_true, if_false, hm]

/-! ### Preservation through every `analyzeNext` transition -/

theorem analyzerFrontier_step {trail : List TrailEntry} {lvl : Nat}
    {c : Clause} {st st' : AnalyzerState}
    (hok : AnalyzerTrailOk trail) (hinv : AnalyzerFrontier trail lvl c st)
    (h : analyzeNext trail lvl st = AnalyzerStep.next st') :
    AnalyzerFrontier trail lvl c st' := by
  obtain ⟨work, skip, marks, learnt⟩ := st
  cases work with
  | nil =>
      cases hnp : nextPivot trail marks with
      | none =>
          rw [analyzeNext_noPivot trail lvl skip marks learnt hnp] at h
          exact absurd h (by simp)
      | some e =>
          by_cases hq : (marks.filter (fun m => !litEqB m.literal e.literal)).isEmpty = true
          · rw [analyzeNext_pivot_done trail lvl skip marks learnt e hnp hq] at h
            exact absurd h (by simp)
          · cases hr : e.reason with
            | none =>
                rw [analyzeNext_pivot_none_reason trail lvl skip marks learnt e
                  hnp hq hr] at h
                exact absurd h (by simp)
            | some r =>
                rw [analyzeNext_pivot trail lvl skip marks learnt e r hnp hq hr] at h
                simp only [AnalyzerStep.next.injEq] at h
                subst h
                exact analyzerFrontier_pivot hok hinv hnp hr
  | cons cl cs =>
      cases cl with
      | nil =>
          rw [analyzeNext_dropEmpty trail lvl cs skip marks learnt] at h
          simp only [AnalyzerStep.next.injEq] at h
          subst h
          exact analyzerFrontier_dropEmpty hinv
      | cons q0 qs =>
          by_cases hs : skipEq skip q0.norm = true
          · rw [analyzeNext_skipScan trail lvl q0 qs cs skip marks learnt hs] at h
            simp only [AnalyzerStep.next.injEq] at h
            subst h
            exact analyzerFrontier_skipScan hinv
          · have hsf : skipEq skip q0.norm = false := by
              cases hh : skipEq skip q0.norm <;> simp_all
            cases hmk' : markLit trail lvl marks learnt q0.norm with
            | none =>
                rw [analyzeNext_markScan_none trail lvl q0 qs cs skip marks
                  learnt hsf hmk'] at h
                exact absurd h (by simp)
            | some mp =>
                obtain ⟨marks₂, learnt₂⟩ := mp
                rw [analyzeNext_markScan trail lvl q0 qs cs skip marks learnt
                  marks₂ learnt₂ hsf hmk'] at h
                simp only [AnalyzerStep.next.injEq] at h
                subst h
                exact analyzerFrontier_markScan hok hinv hsf hmk'

/-! ### Derived measure decrease and the completion theorem -/

/-- The reachability closure exports the trail discipline. -/
theorem analyzerReachable_trailOk {trail : List TrailEntry} {lvl : Nat}
    {c : Clause} {st : AnalyzerState} (hr : AnalyzerReachable trail lvl c st) :
    AnalyzerTrailOk trail := by
  induction hr with
  | init hok => exact hok
  | next _ _ ih => exact ih

/-- The invariant holds on every reachable state (initialization +
preservation, items 1–2). -/
theorem analyzerFrontier_of_reachable {trail : List TrailEntry} {lvl : Nat}
    {c : Clause} {st : AnalyzerState} (hr : AnalyzerReachable trail lvl c st) :
    AnalyzerFrontier trail lvl c st := by
  induction hr with
  | init hok => exact analyzerFrontier_init hok
  | next hr' heq ih =>
      exact analyzerFrontier_step (analyzerReachable_trailOk hr') ih heq

/-- The reachable class also exports the falsifier invariants B2's certificate
consumes (`BelowFalsified`, `MarksOnTrail`, `MarksCurrentLevel`), so no
consumer needs to assume them on a reachable state. -/
theorem analyzerReachable_invariants {trail : List TrailEntry} {lvl : Nat}
    {c : Clause} {st : AnalyzerState} (hr : AnalyzerReachable trail lvl c st) :
    BelowFalsified trail st.learnt ∧ MarksOnTrail trail st.marks ∧
      MarksCurrentLevel lvl st.marks :=
  let hf := analyzerFrontier_of_reachable hr
  ⟨hf.1, (fun m hm => (hf.2.1 m hm).1), (fun m hm => (hf.2.1 m hm).2)⟩

/-- PIVOT payment for reachable states: the frontier retreat is read off the
invariant (`skip = none` takes the initial-conflict form), so the payment
inequality `roundCost_pivot` consumes is DERIVED, not assumed. -/
theorem skipCost_pivot_of_reachable {trail : List TrailEntry} {lvl : Nat}
    {c : Clause} {skip : Option Literal} {marks : List TrailEntry}
    {learnt : List (Literal × Nat)} {e : TrailEntry} {r : Reason}
    (hok : AnalyzerTrailOk trail)
    (hinv : AnalyzerFrontier trail lvl c
      { work := [], skip := skip, marks := marks, learnt := learnt })
    (hnp : nextPivot trail marks = some e) (hr : e.reason = some r) :
    skipCost trail (some e.literal) + (1 + r.clause.length)
      < skipCost trail skip := by
  have he_trail : e ∈ trail := nextPivot_trail_mem trail marks e hnp
  obtain ⟨m₀, hm₀mem, hm₀lit⟩ := nextPivot_mark trail marks e hnp
  have he_marks : e ∈ marks := by
    have hsame : m₀ = e := hok.distinct.1 e he_trail m₀ (hinv.2.1 m₀ hm₀mem).1
      (hm₀lit.trans (hok.norm e he_trail))
    rw [← hsame]
    exact hm₀mem
  cases hskip : skip with
  | none =>
      obtain ⟨as, bs, hsplit, -⟩ := nextPivot_after_not_mem hnp
      exact skipCost_initial hsplit hr
  | some sl =>
      obtain ⟨hn, e_f, hfe, hef_trail, -, ⟨r_f, -, -⟩, hret⟩ :=
        hinv.2.2.1 sl hskip
      obtain ⟨as, mid, bs, hsplit⟩ := hret e he_marks
      have hsl : sl = e_f.literal :=
        hn.trans (findEntryOf_literal trail sl e_f hfe).symm
      have hpay := skipCost_retreat hok.distinct hok.norm hsplit hr
      rwa [hsl]

/-- The measure strictly decreases at every transition of a reachable state
(item 3): the three scan transitions are structural, the pivot transition
pays through the derived frontier retreat. -/
theorem roundCost_decrease_step {trail : List TrailEntry} {lvl : Nat}
    {c : Clause} {st st' : AnalyzerState}
    (hok : AnalyzerTrailOk trail) (hinv : AnalyzerFrontier trail lvl c st)
    (h : analyzeNext trail lvl st = AnalyzerStep.next st') :
    roundCost trail st' < roundCost trail st := by
  obtain ⟨work, skip, marks, learnt⟩ := st
  cases work with
  | nil =>
      cases hnp : nextPivot trail marks with
      | none =>
          rw [analyzeNext_noPivot trail lvl skip marks learnt hnp] at h
          exact absurd h (by simp)
      | some e =>
          by_cases hq : (marks.filter (fun m => !litEqB m.literal e.literal)).isEmpty = true
          · rw [analyzeNext_pivot_done trail lvl skip marks learnt e hnp hq] at h
            exact absurd h (by simp)
          · cases hr : e.reason with
            | none =>
                rw [analyzeNext_pivot_none_reason trail lvl skip marks learnt e
                  hnp hq hr] at h
                exact absurd h (by simp)
            | some r =>
                rw [analyzeNext_pivot trail lvl skip marks learnt e r hnp hq hr] at h
                simp only [AnalyzerStep.next.injEq] at h
                subst h
                refine roundCost_pivot r.clause skip marks learnt e trail ?_
                exact skipCost_pivot_of_reachable hok hinv hnp hr
  | cons cl cs =>
      cases cl with
      | nil =>
          rw [analyzeNext_dropEmpty trail lvl cs skip marks learnt] at h
          simp only [AnalyzerStep.next.injEq] at h
          subst h
          exact roundCost_drop_empty cs skip marks learnt trail
      | cons q0 qs =>
          by_cases hs : skipEq skip q0.norm = true
          · rw [analyzeNext_skipScan trail lvl q0 qs cs skip marks learnt hs] at h
            simp only [AnalyzerStep.next.injEq] at h
            subst h
            exact roundCost_scan q0 qs cs skip marks learnt marks learnt trail
          · have hsf : skipEq skip q0.norm = false := by
              cases hh : skipEq skip q0.norm <;> simp_all
            cases hmk' : markLit trail lvl marks learnt q0.norm with
            | none =>
                rw [analyzeNext_markScan_none trail lvl q0 qs cs skip marks
                  learnt hsf hmk'] at h
                exact absurd h (by simp)
            | some mp =>
                obtain ⟨marks₂, learnt₂⟩ := mp
                rw [analyzeNext_markScan trail lvl q0 qs cs skip marks learnt
                  marks₂ learnt₂ hsf hmk'] at h
                simp only [AnalyzerStep.next.injEq] at h
                subst h
                exact roundCost_scan q0 qs cs skip marks learnt marks₂ learnt₂ trail

/-- `hstep`, derived: every `.next` transition of a REACHABLE state strictly
decreases the measure. This is the premise `analysis_not_fuel_limited` used
to assume for arbitrary states. -/
theorem roundCost_decrease_of_reachable {trail : List TrailEntry} {lvl : Nat}
    {c : Clause} {st st' : AnalyzerState}
    (hr : AnalyzerReachable trail lvl c st)
    (h : analyzeNext trail lvl st = AnalyzerStep.next st') :
    roundCost trail st' < roundCost trail st :=
  roundCost_decrease_step (analyzerReachable_trailOk hr)
    (analyzerFrontier_of_reachable hr) h

/-- Trace existence on the REACHABLE class (item 4): the decrease hypothesis
is derived from reachability, so the theorem takes the supported reachable
input invariant instead of `hstep`. -/
theorem analyzeTrace_exists_of_reachable {trail : List TrailEntry} {lvl : Nat}
    {c : Clause} :
    ∀ (fuel : Nat) (st : AnalyzerState), AnalyzerReachable trail lvl c st →
      roundCost trail st + 1 ≤ fuel →
      ∃ (k : Nat) (r : Option (List (Literal × Nat) × Literal)),
        analyzeTrace trail lvl fuel st = some (k, r) := by
  intro fuel
  induction fuel with
  | zero =>
      intro st hr h
      cases hn : analyzeNext trail lvl st with
      | done res => omega
      | next st' =>
          have hlt := roundCost_decrease_of_reachable hr hn
          omega
  | succ fuel ih =>
      intro st hr h
      cases hn : analyzeNext trail lvl st with
      | done res => exact ⟨1, res, by rw [analyzeTrace_succ, hn]⟩
      | next st' =>
          have hlt := roundCost_decrease_of_reachable hr hn
          obtain ⟨k, r, hk⟩ := ih st' (AnalyzerReachable.next hr hn) (by omega)
          refine ⟨k + 1, r, ?_⟩
          rw [analyzeTrace_succ, hn]
          dsimp only
          rw [hk]

/-- THE NO-EXHAUSTION THEOREM on supported reachable inputs (item 4): the
executable allowance cannot be exhausted, so `analyzeTrace` always observes a
semantic stop. -/
theorem analysis_complete_of_reachable (c : Clause) {trail : List TrailEntry}
    {lvl : Nat} (hne : 1 ≤ c.length)
    (hr : AnalyzerReachable trail lvl c (initAnalysisState c)) :
    ∃ (k : Nat) (r : Option (List (Literal × Nat) × Literal)),
      analyzeTrace trail lvl (analysisFuel trail c) (initAnalysisState c)
        = some (k, r) :=
  analyzeTrace_exists_of_reachable (analysisFuel trail c) (initAnalysisState c)
    hr (roundCost_init_add_one_le_analysisFuel c trail hne)

/-! ### Connecting the computed allowance to the executed analysis (item 4)

`analyzeAtAllowance` is the entry point that consumes `analysisFuel`. The
theorems below say that on supported reachable inputs its result IS the
result of a completed trace of `k ≤ analysisFuel` transitions — so a `none`
result is a SEMANTIC stop (root contradiction at level 0, or an unsupported
local explanation), never budget truncation. -/

/-- A completed trace at fuel `k` is the loop at exactly `k` fuel: the
analyzer reached its verdict after `k` transitions. -/
theorem analyzeTrace_loop_at_steps {trail : List TrailEntry} {lvl : Nat} :
    ∀ (fuel k : Nat) (st : AnalyzerState)
      (r : Option (List (Literal × Nat) × Literal)),
      analyzeTrace trail lvl fuel st = some (k, r) →
      analyzeLoop trail lvl k st = r := by
  intro fuel
  induction fuel with
  | zero => intro k st r h; simp [analyzeTrace] at h
  | succ fuel ih =>
      intro k st r h
      cases hn : analyzeNext trail lvl st with
      | done res =>
          simp only [analyzeTrace_succ, hn, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp [analyzeLoop, hn]
      | next st' =>
          cases ht : analyzeTrace trail lvl fuel st' with
          | none => simp [analyzeTrace_succ, hn, ht] at h
          | some kr =>
              obtain ⟨k', r'⟩ := kr
              simp only [analyzeTrace_succ, hn, ht, Option.some.injEq,
                Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have := ih k' st' r' ht
              simp only [analyzeLoop, hn]
              exact this

/-- On a supported reachable input, the executable analysis STOPS: its
result is reached by a completed trace of `k ≤ analysisFuel` transitions. -/
theorem analyzeAtAllowance_stops (c : Clause) {trail : List TrailEntry}
    {lvl : Nat} (hne : 1 ≤ c.length)
    (hr : AnalyzerReachable trail lvl c (initAnalysisState c)) :
    ∃ k, k ≤ analysisFuel trail c ∧
      analyzeTrace trail lvl (analysisFuel trail c) (initAnalysisState c)
        = some (k, analyzeAtAllowance trail lvl c) ∧
      analyzeLoop trail lvl k (initAnalysisState c)
        = analyzeAtAllowance trail lvl c := by
  obtain ⟨k, r, hk⟩ := analysis_complete_of_reachable c hne hr
  have hle := analyzeTrace_steps_le trail lvl (analysisFuel trail c)
    (initAnalysisState c) k r hk
  have hloop := analyzeTrace_loop_at_steps (analysisFuel trail c) k
    (initAnalysisState c) r hk
  have hsnd := analyzeTrace_snd trail lvl (analysisFuel trail c)
    (initAnalysisState c) k r hk
  have hres : r = analyzeAtAllowance trail lvl c := by
    rw [analyzeAtAllowance_fuel_eq]
    exact hsnd.symm
  subst hres
  exact ⟨k, hle, hk, hloop⟩

/-- `analyzeClassified` reports `.success` exactly when the analyzer
returned a result — the classification is a pure relabeling of the
computed-allowance run.

Renamed from `analyzeClassified_eq_success_iff` (O1, 2026-10-09): that
name is also declared by `LeanFzn.Solver.UIP.Proofs.SchedulerConflict:513`
(the certificate-input form). Cross-module homonyms import silently in
Lean 4 with last-import-wins resolution, but any module that *declares*
the name while `AnalysisEvents`/`AnalysisCompletion` is also in its
import cone fails with "has already been declared". This copy is a
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation

pure relabeling of `analyzeAtAllowance` and is the one visible inside
the `AnalysisEvents` cone; the `SchedulerConflict` name is kept for its
consumers. -/
theorem analyzeClassified_eq_success_iff_of_allowance {trail : List TrailEntry}
    {lvl : Nat} {c : Clause} {below : List (Literal × Nat)} {uip : Literal} :
    analyzeClassified trail lvl c = .success below uip ↔
      analyzeAtAllowance trail lvl c = some (below, uip) := by
  unfold analyzeClassified
  cases h : analyzeAtAllowance trail lvl c with
  | some p =>
      obtain ⟨b, u⟩ := p
      simp
  | none =>
      by_cases h0 : lvl = 0 <;> simp [h0]

/-- SEMANTIC `unsupported`, not truncation: `.unsupported` is exactly "no
asserting result above the root". -/
theorem analyzeClassified_unsupported_iff {trail : List TrailEntry} {lvl : Nat}
    {c : Clause} :
    analyzeClassified trail lvl c = .unsupported ↔
      analyzeAtAllowance trail lvl c = none ∧ lvl ≠ 0 := by
  unfold analyzeClassified
  cases h : analyzeAtAllowance trail lvl c with
  | some p =>
      obtain ⟨b, u⟩ := p
      simp
  | none =>
      by_cases h0 : lvl = 0 <;> simp [h0]

/-- The `.unsupported` verdict comes with a COMPLETED trace that stops in
`none` strictly inside the executable allowance: the distinction between a
semantic unsupported analysis and a budget truncation, on supported
reachable inputs. -/
theorem analyzeClassified_unsupported_trace (c : Clause) {trail : List TrailEntry}
    {lvl : Nat} (hne : 1 ≤ c.length)
    (hr : AnalyzerReachable trail lvl c (initAnalysisState c))
    (huns : analyzeClassified trail lvl c = .unsupported) :
    lvl ≠ 0 ∧ ∃ k, k ≤ analysisFuel trail c ∧
      analyzeTrace trail lvl (analysisFuel trail c) (initAnalysisState c)
        = some (k, none) := by
  obtain ⟨hnone, hlvl⟩ := analyzeClassified_unsupported_iff.mp huns
  obtain ⟨k, hk, htr, -⟩ := analyzeAtAllowance_stops c hne hr
  exact ⟨hlvl, k, hk, by rw [hnone] at htr; exact htr⟩

/-- The `.rootContradiction` verdict likewise comes from a completed trace
that stops in `none` at level 0. -/
theorem analyzeClassified_root_trace (c : Clause) {trail : List TrailEntry}
    (hne : 1 ≤ c.length)
    (hr : AnalyzerReachable trail 0 c (initAnalysisState c))
    (hroot : analyzeClassified trail 0 c = .rootContradiction) :
    ∃ k, k ≤ analysisFuel trail c ∧
      analyzeTrace trail 0 (analysisFuel trail c) (initAnalysisState c)
        = some (k, none) := by
  obtain ⟨k, hk, htr, -⟩ := analyzeAtAllowance_stops c hne hr
  have hnone : analyzeAtAllowance trail 0 c = none := by
    unfold analyzeClassified at hroot
    cases h : analyzeAtAllowance trail 0 c with
    | some p => simp [h] at hroot
    | none => rfl
  exact ⟨k, hk, by rw [hnone] at htr; exact htr⟩

/-! ### Instantiation on reachable branch states

The supported inputs of the plan are the reachable branch states A1 supplies:
`ReachableState`'s eighth field is exactly the duplicate-safe discipline, and
its `WellFormed` component supplies normalization and chronology — so the
trail discipline is a theorem, not a hypothesis. -/

/-- `ReachableState` supplies the whole trail discipline (`distinct` is A1's
eighth field; normalization and chronology are `WellFormed`). -/
theorem analyzerTrailOk_of_reachable {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf}
    (h : ReachableState leaf orig bs) : AnalyzerTrailOk bs.trail :=
  ⟨h.distinct, h.wf.2.1, h.wf.2.2.2.1⟩

/-- Every reachable branch state's initial analyzer state is in the reachable
class. -/
theorem analyzerReachable_of_reachable {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf}
    (h : ReachableState leaf orig bs) (c : Clause) :
    AnalyzerReachable bs.trail bs.level c (initAnalysisState c) :=
  AnalyzerReachable.init (analyzerTrailOk_of_reachable h)

/-- `ReachableState` also supplies the SUPPORTED INPUT discipline of
`AnalyzerInput` (A2/A3's `hSupp` gate is a separate, semantic condition). -/
def analyzerInput_of_supported {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf} {c : Clause}
    (h : ReachableState leaf orig bs) (hne : 1 ≤ c.length)
    (hent : LearnedEntailed leaf [c]) (hfals : FalsifiedByTrail bs c) :
    AnalyzerInput leaf bs :=
  ⟨c, hne, hent, hfals⟩

/-- THE SUPPORTED-INPUT NO-EXHAUSTION COROLLARY: a reachable branch state with
a nonempty conflict clause runs the analyzer to a semantic stop inside the
executable allowance. -/
theorem analysis_complete_of_reachable_state {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf} {c : Clause}
    (h : ReachableState leaf orig bs) (hne : 1 ≤ c.length) :
    ∃ (k : Nat) (r : Option (List (Literal × Nat) × Literal)),
      analyzeTrace bs.trail bs.level (analysisFuel bs.trail c)
        (initAnalysisState c) = some (k, r) :=
  analysis_complete_of_reachable c hne (analyzerReachable_of_reachable h c)

/-- The `AnalyzerInput` form: the no-exhaustion theorem consumes the frozen
`AnalyzerInput` structure (its `nonempty` field pays the initial measure). -/
theorem analysis_complete_of_input {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf}
    (hin : AnalyzerInput leaf bs) (h : ReachableState leaf orig bs) :
    ∃ (k : Nat) (r : Option (List (Literal × Nat) × Literal)),
      analyzeTrace bs.trail bs.level (analysisFuel bs.trail hin.conflict)
        (initAnalysisState hin.conflict) = some (k, r) :=
  analysis_complete_of_reachable hin.conflict hin.nonempty
    (analyzerReachable_of_reachable h hin.conflict)

/-! ### Worked examples: COMPLETED traces at the executable allowance

The plan requires examples that exhibit a COMPLETED `analyzeTrace` at
`analysisFuel` — an observed semantic stop, not a numeric allowance
comparison. The long-reason fixture below has a five-literal reason clause,
resolves it in ten transitions, and is proved to be in the reachable class,
so the no-exhaustion theorem applies to it as an instance (not merely to an
abstract statement). -/

/-- A decision entry of the fixtures. -/
private def exDec (l : Literal) (lv : Nat) : TrailEntry :=
  { literal := l, level := lv, reason := none }

/-- An implication entry of the fixtures. -/
private def exImp (l : Literal) (lv : Nat) (cl : Clause) : TrailEntry :=
  { literal := l, level := lv, reason := some { clause := cl } }

/-- THE LONG-REASON TRAIL: four level-1 decisions falsifying the reason's
side literals, a level-2 decision, and a level-2 implication whose reason is
the five-literal clause `[x2 ≤ 3, ¬(x3 ≤ 0), ¬(x3 ≤ 1), ¬(x3 ≤ 2), ¬(x3 ≤ 3)]`. -/
private def exTrail : List TrailEntry :=
  [ exDec (posLe 3 0) 1, exDec (posLe 3 1) 1, exDec (posLe 3 2) 1,
    exDec (posLe 3 3) 1, exDec (posLe 1 5) 2,
    exImp (posLe 2 3) 2
      [posLe 2 3, negLe 3 0, negLe 3 1, negLe 3 2, negLe 3 3] ]

/-- The conflict clause of the fixture: falsified at level 2 by the
implication's pivot and the level-2 decision. -/
private def exConflict : Clause := [negLe 2 3, negLe 1 5]

/-- The below-level falsifiers the fixture records (newest mark first). -/
private def exBelow : List (Literal × Nat) :=
  [(negLe 3 3, 1), (negLe 3 2, 1), (negLe 3 1, 1), (negLe 3 0, 1)]

/-- `Literal.norm` is the identity on all literals of the fixture. -/
private theorem norm_all_of {trail : List TrailEntry}
    (h : trail.all (fun e => decide (e.literal = e.literal.norm)) = true) :
    ∀ e ∈ trail, e.literal = e.literal.norm :=
  fun e he => of_decide_eq_true ((List.all_eq_true.mp h) e he)

/-- A `List.all` check discharges freshness of a literal against a prefix. -/
private theorem fresh_all_of {trail : List TrailEntry} {l : Literal}
    (h : (trail.map (fun e => e.literal)).all (fun l' => !litEqB l' l.norm) = true) :
    ∀ e ∈ trail, e.literal ≠ l.norm := by
  intro e he hcon
  have h1 : (!litEqB e.literal l.norm) = true :=
    (List.all_eq_true.mp h) e.literal (List.mem_map_of_mem he)
  have h2 : litEqB e.literal l.norm = true := by
    rw [litEqB_eq_true_iff]
    exact hcon
  rw [h2] at h1
  exact Bool.noConfusion h1

/-- The fixture trail is duplicate-free (A1's discipline), built by the
absence-checked append combinators. -/
private theorem exTrail_distinct : TrailLiteralsDistinct exTrail := by
  have h0 : TrailLiteralsDistinct ([] : List TrailEntry) := TrailLiteralsDistinct.nil
  have h1 := TrailLiteralsDistinct.decisionEntry (trail := []) (l := posLe 3 0)
    (lvl := 1) h0 (norm_all_of (by decide)) (fresh_all_of (by decide))
  have h2 := TrailLiteralsDistinct.decisionEntry (trail := [exDec (posLe 3 0) 1])
    (l := posLe 3 1) (lvl := 1) h1 (norm_all_of (by decide)) (fresh_all_of (by decide))
  have h3 := TrailLiteralsDistinct.decisionEntry
    (trail := [exDec (posLe 3 0) 1, exDec (posLe 3 1) 1]) (l := posLe 3 2)
    (lvl := 1) h2 (norm_all_of (by decide)) (fresh_all_of (by decide))
  have h4 := TrailLiteralsDistinct.decisionEntry
    (trail := [exDec (posLe 3 0) 1, exDec (posLe 3 1) 1, exDec (posLe 3 2) 1])
    (l := posLe 3 3) (lvl := 1) h3 (norm_all_of (by decide)) (fresh_all_of (by decide))
  have h5 := TrailLiteralsDistinct.decisionEntry
    (trail := [exDec (posLe 3 0) 1, exDec (posLe 3 1) 1, exDec (posLe 3 2) 1,
      exDec (posLe 3 3) 1]) (l := posLe 1 5) (lvl := 2) h4
    (norm_all_of (by decide)) (fresh_all_of (by decide))
  exact TrailLiteralsDistinct.enqueue
    (trail := [exDec (posLe 3 0) 1, exDec (posLe 3 1) 1, exDec (posLe 3 2) 1,
      exDec (posLe 3 3) 1, exDec (posLe 1 5) 2]) (l := posLe 2 3) (lvl := 2)
    (r := ⟨[posLe 2 3, negLe 3 0, negLe 3 1, negLe 3 2, negLe 3 3]⟩) h5
    (norm_all_of (by decide)) (fresh_all_of (by decide))

/-- Chronology WITHOUT exact literals: in `pre ++ [b]` the entry `a ∈ pre`
is strictly before `b`. -/
theorem earlierThan_last_of_mem (pre : List TrailEntry) (b : TrailEntry)
    {a : TrailEntry} (ha : a ∈ pre) :
    TrailEntry.earlierThan (pre ++ [b]) a b := by
  obtain ⟨p, q, hpq⟩ := List.mem_iff_append.mp ha
  have hlt : p.length < pre.length := by rw [hpq]; simp
  refine ⟨p.length, pre.length, ?_, ?_, ?_, ?_, by omega⟩
  · simp only [List.length_append, List.length_singleton]; omega
  · simp only [List.length_append, List.length_singleton]; omega
  · have h1 : (pre ++ [b])[p.length]? = some a := by
      rw [hpq, List.getElem?_append_left (by simp),
        List.getElem?_append_right (Nat.le_refl _)]
      simp
    exact (List.getElem?_eq_some_iff.mp h1).2
  · have h1 : (pre ++ [b])[pre.length]? = some b := by
      rw [List.getElem?_append_right (Nat.le_refl _)]
      simp
    exact (List.getElem?_eq_some_iff.mp h1).2

/-- The fixture's chronology: the only reason is the implication's, and every
non-pivot reason literal is falsified by an earlier decision. -/
private theorem exTrail_chron :
    ∀ e ∈ exTrail, ∀ r ∈ e.reason, ∀ l ∈ r.clause, l ≠ e.literal →
      ∃ e' ∈ exTrail, e'.literal = l.negate ∧ TrailEntry.earlierThan exTrail e' e := by
  intro e he r hr l hl hne
  simp only [exTrail, List.mem_cons, List.mem_nil_iff, List.not_mem_nil,
    or_false] at he
  rcases he with h | h | h | h | h | h
  · subst h
    exact absurd hr (Option.not_mem_none r)
  · subst h
    exact absurd hr (Option.not_mem_none r)
  · subst h
    exact absurd hr (Option.not_mem_none r)
  · subst h
    exact absurd hr (Option.not_mem_none r)
  · subst h
    exact absurd hr (Option.not_mem_none r)
  · subst h
    have hr' : r = { clause := [posLe 2 3, negLe 3 0, negLe 3 1, negLe 3 2,
        negLe 3 3] } := (Option.mem_some_iff.mp hr).symm
    subst hr'
    cases hl with
    | head => exact absurd rfl hne
    | tail _ hl =>
      cases hl with
      | head =>
        exact ⟨exDec (posLe 3 0) 1, by simp [exTrail], rfl,
          earlierThan_last_of_mem
          [exDec (posLe 3 0) 1, exDec (posLe 3 1) 1, exDec (posLe 3 2) 1,
            exDec (posLe 3 3) 1, exDec (posLe 1 5) 2]
          (exImp (posLe 2 3) 2
            [posLe 2 3, negLe 3 0, negLe 3 1, negLe 3 2, negLe 3 3])
          (by simp)⟩
      | tail _ hl =>
        cases hl with
        | head =>
          exact ⟨exDec (posLe 3 1) 1, by simp [exTrail], rfl,
            earlierThan_last_of_mem
          [exDec (posLe 3 0) 1, exDec (posLe 3 1) 1, exDec (posLe 3 2) 1,
            exDec (posLe 3 3) 1, exDec (posLe 1 5) 2]
          (exImp (posLe 2 3) 2
            [posLe 2 3, negLe 3 0, negLe 3 1, negLe 3 2, negLe 3 3])
          (by simp)⟩
        | tail _ hl =>
          cases hl with
          | head =>
            exact ⟨exDec (posLe 3 2) 1, by simp [exTrail], rfl,
              earlierThan_last_of_mem
          [exDec (posLe 3 0) 1, exDec (posLe 3 1) 1, exDec (posLe 3 2) 1,
            exDec (posLe 3 3) 1, exDec (posLe 1 5) 2]
          (exImp (posLe 2 3) 2
            [posLe 2 3, negLe 3 0, negLe 3 1, negLe 3 2, negLe 3 3])
          (by simp)⟩
          | tail _ hl =>
            cases hl with
            | head =>
              exact ⟨exDec (posLe 3 3) 1, by simp [exTrail], rfl,
                earlierThan_last_of_mem
          [exDec (posLe 3 0) 1, exDec (posLe 3 1) 1, exDec (posLe 3 2) 1,
            exDec (posLe 3 3) 1, exDec (posLe 1 5) 2]
          (exImp (posLe 2 3) 2
            [posLe 2 3, negLe 3 0, negLe 3 1, negLe 3 2, negLe 3 3])
          (by simp)⟩
            | tail _ hl => cases hl

/-- The fixture trail meets the supported-input discipline. -/
private theorem exTrail_ok : AnalyzerTrailOk exTrail :=
  ⟨exTrail_distinct, norm_all_of (by decide), exTrail_chron⟩

/-- The fixture is in the REACHABLE analyzer class, so the no-exhaustion
theorem applies to it. -/
private theorem exReachable :
    AnalyzerReachable exTrail 2 exConflict (initAnalysisState exConflict) :=
  AnalyzerReachable.init exTrail_ok

-- THE COMPLETED LONG-REASON TRACE: ten transitions, observed semantically
-- well inside the executable allowance. Not an allowance comparison.
example : analyzeTrace exTrail 2 (analysisFuel exTrail exConflict)
    (initAnalysisState exConflict) = some (11, some (exBelow, posLe 1 5)) := rfl

-- The trace is present, and its step count is strictly inside the fuel.
example : (analyzeTrace exTrail 2 (analysisFuel exTrail exConflict)
    (initAnalysisState exConflict)).isSome = true := rfl
example : 11 ≤ analysisFuel exTrail exConflict := by decide

-- The no-exhaustion theorem INSTANTIATED on the fixture (not a numeric
-- comparison): a completed trace exists at the executable allowance.
example : ∃ (k : Nat) (r : Option (List (Literal × Nat) × Literal)),
    analyzeTrace exTrail 2 (analysisFuel exTrail exConflict)
      (initAnalysisState exConflict) = some (k, r) :=
  analysis_complete_of_reachable exConflict (by decide) exReachable

-- The executable entry point's own verdict is the trace's result, reached
-- after ten transitions — the stop is a semantic stop.
example : ∃ k, k ≤ analysisFuel exTrail exConflict ∧
    analyzeTrace exTrail 2 (analysisFuel exTrail exConflict)
        (initAnalysisState exConflict)
      = some (k, analyzeAtAllowance exTrail 2 exConflict) ∧
    analyzeLoop exTrail 2 k (initAnalysisState exConflict)
      = analyzeAtAllowance exTrail 2 exConflict :=
  analyzeAtAllowance_stops exConflict (by decide) exReachable

-- The classification agrees with the executed analysis.
example : analyzeClassified exTrail 2 exConflict = .success exBelow (posLe 1 5) := by
  rw [analyzeClassified_eq_success_iff_of_allowance]
  rfl

-- The short exact-lookup fixture: a single-level conflict resolves in two
-- transitions with an empty below-level set.
private def exTrail2 : List TrailEntry := [exDec (posLe 0 5) 1]
private def exConflict2 : Clause := [negLe 0 5]

example : analyzeTrace exTrail2 1 (analysisFuel exTrail2 exConflict2)
    (initAnalysisState exConflict2) = some (3, some ([], posLe 0 5)) := rfl

end LeanFzn.Solver.Propagation

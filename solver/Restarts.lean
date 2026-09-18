import solver.Solve

/-!
# Restarts with a resource-bounded `unknown` (PLAN.md item 6.6)

PLAN 6.6 requires that restarts "restore a proved root state while
retaining only globally valid learned facts", and for completeness
either use a fair schedule whose limits eventually exceed every
finite subtree, or expose restarts only in a resource-bounded solver
that may return `unknown`.  This module takes the second route, and
keeps the plan's safety discipline in one place:

> A bounded run may return `unknown`, but it must never turn an
> interrupted search into `unsat`.

This is exactly the `unknown`/`unsat` split that the `SolveResult`
docstring of `solver/Solve.lean` calls for: an interrupted search is
reported as `unknown`, never folded into `unsupported`-or-`unsat`.

## Design

* `BoundedResult` — the plan's three-way SAT/UNSAT/unknown
  discipline: `sat a`, `unsat`, `unknown`.  The crucial invariant,
  proven below: `unsat` is only ever produced from an `exhausted`
  attempt of the budgeted search, and `exhausted` carries
  `search_none`'s complete-exhaustion guarantee — so `unsat` is a
  certificate, not a guess.

* `BudgetResult` — the three-way outcome of ONE budgeted attempt:
  `found` (a solution), `exhausted` (the whole subtree was explored
  empty — a real UNSAT certificate), `budgetOut` (interrupted —
  **no** claim).

* `searchBudget` — the reference `search` of `solver/Search.lean`
  with a node budget: every recursive call consumes one unit, and at
  budget `0` the search stops immediately with `budgetOut` (no
  result claim); otherwise the branching is identical to `search`.
  The budget is consumed per call along each branch (the first
  component of the lexicographic termination measure
  `(budget, slotsMeasure)`): a budget of `b` permits any `b` nested
  calls, so the budget bounds the *depth* of the explored tree.
  `searchNodes slots := slotsMeasure slots + 1` is the proved
  sufficient budget: beyond it the reference tree is never
  truncated.

* `restartSearch` — the resource-bounded solver: try `searchBudget`
  with the schedule's budgets in order, restarting from a FRESH root
  state each time (the original, untouched slot list — nothing is
  retained between attempts, so restoring the proved root state is
  trivial; see *Scoping* below).  The first attempt that makes a
  claim wins: `found` → `sat`, `exhausted` → `unsat`; a `budgetOut`
  attempt claims nothing and retries with the next budget; if every
  attempt runs out, the loop reports `unknown` — the honest verdict
  for "interrupted, don't know".

## The theorems

* `searchBudget_found` — a `found r` outcome gives `search_some`'s
  conclusion: `r` extends the accumulator to a complete assignment
  of the slots passing the leaf predicate.
* `searchBudget_exhausted` — an `exhausted` outcome gives
  `search_none`'s conclusion: every complete assignment of the
  slots fails the leaf predicate.  This is what makes exhaustion a
  real UNSAT certificate.
* `searchBudget_eq` — **the accounting core**: with a sufficient
  budget (`searchNodes slots ≤ b`) the budgeted search is *exactly*
  the reference search, via the three-way adapter `ofOption`.
  Two corollaries restate it as the claim-by-claim agreement
  `searchBudget_search` (found iff some, exhausted iff none) and
  `searchBudget_ne_budgetOut` (a sufficient budget never runs out).
* `searchBudget_monotone` — **full monotonicity of claims** (no
  sufficiency hypothesis): if the run at budget `b'` makes a claim
  (found/exhausted), then the run at any budget `b ≥ b'` makes the
  same claim.  More budget can change an `unknown` into a claim,
  never a claim into a different claim.
* `restartSearch_sat_sound` — `sat r` means `r` is a complete
  assignment of the slots passing the leaf.
* `restartSearch_unsat_sound` — `unsat` means *every* complete
  assignment fails the leaf (only reachable from a real exhaustion).
* `restartSearch_never_falseUnsat` — **the safety theorem of PLAN
  6.6**: if some complete assignment passes the leaf, the restart
  loop never returns `unsat`.  An interrupted — or even completed —
  search cannot produce a false UNSAT verdict.
* `restartSearch_complete` — the fair-schedule half: any schedule
  containing a budget of at least `searchNodes` returns a decided
  verdict (never `unknown`).
* FlatZinc layer: `solveModelBounded m schedule` mirrors
  `solveModel`'s gates and leaf-check architecture (the leaf is
  the verified checker itself) with `restartSearch`; static
  refusals (unsupported predicates, ill-formed models,
  out-of-fragment or capped domains) also produce `unknown` — no
  verdict — since the `unsat` constructor is reserved for
  certified exhaustion.  The three theorems transfer:
  `solveModelBounded_sat_sound` (a returned text is accepted by
  the verified front door), `solveModelBounded_unsat_sound` (an
  `unsat` verdict excludes every slot assignment),
  `solveModelBounded_never_falseUnsat` (a model with an accepted
  slot assignment is never reported `unsat`).

## Scoping

No learned facts are retained between restarts in this round:
each attempt starts from the untouched original slots, so
"restore the proved root state" holds trivially.  Retention of
globally valid learned facts (NoGoods that filter leaves, pruning
only assignments that provably fail the leaf) composes later with
the Learning module by *leaf conjunction* — a conjunction of the
original leaf with a NoGoods filter that keeps every leaf-passing
assignment leaves all theorems below verbatim — and is out of
scope here.  No heuristic per-attempt reordering is wired in
either; `heuristicSearch` (`solver/Heuristic.lean`) composes with
restarts the same way, by replacing the single-attempt search.
-/

namespace LeanFzn.Solver

open LeanFzn LeanFzn.Solution LeanFzn.Check LeanFzn.Globals

/-! ## The bounded result type

The plan's SAT/UNSAT/unknown discipline for a resource-bounded
solver; the `unknown`/`unsat` split of `SolveResult`'s docstring
note (`solver/Solve.lean`).  `unsat` is only ever produced from an
`exhausted` attempt (a complete-exhaustion certificate); an
interrupted search produces `unknown`. -/

/-- The result of a resource-bounded solve: a solution, a certified
    refutation, or the honest verdict for an interrupted run. -/
inductive BoundedResult (α : Type) where
  /-- A solution was found; the carried value passes the leaf
      predicate (`restartSearch_sat_sound`). -/
  | sat (a : α)
  /-- The search space was *completely exhausted* without a
      solution (`restartSearch_unsat_sound`). -/
  | unsat
  /-- No verdict was reached: the budget ran out (or the model was
      statically refused at the FlatZinc layer); **no claim is
      made**. -/
  | unknown
  deriving Repr, BEq

/-! ## The budgeted search -/

/-- The outcome of one budgeted search attempt: a solution, a real
    complete-exhaustion certificate, or an interruption (no
    claim). -/
inductive BudgetResult (α : Type) where
  /-- A solution was found; carries `search_some`'s guarantee. -/
  | found (a : α)
  /-- The subtree was completely explored empty; carries
      `search_none`'s guarantee (a real UNSAT certificate). -/
  | exhausted
  /-- The budget ran out mid-search; **no** claim is made. -/
  | budgetOut
  deriving Repr, BEq

/-- The sufficient budget for a slot list: the search's own
    termination measure plus one.  A budget of at least
    `searchNodes slots` never runs out mid-search
    (`searchBudget_eq`), so the budgeted search then reproduces
    the reference `search` exactly.  (The budget is consumed once
    per nested call along a branch, so it is the *depth* of the
    search tree that must be covered; `slotsMeasure` strictly
    decreases along every branch, which is `search`'s termination
    argument.) -/
def searchNodes {α : Type} (slots : List (List α)) : Nat :=
  slotsMeasure slots + 1

/-- **The budgeted search.**  The reference `search` of
    `solver/Search.lean` with a node budget: every recursive call
    consumes one unit, and when the counter hits `0` the search
    stops immediately with `budgetOut` (no result claim).
    Otherwise the branching is identical to `search`. -/
def searchBudget {α : Type} (leaf : List α → Bool) :
    Nat → List (List α) → List α → BudgetResult (List α)
  | 0, _, _ => .budgetOut
  | _ + 1, [], acc => if leaf acc then .found acc else .exhausted
  | _ + 1, [] :: _, _ => .exhausted
  | b + 1, (v :: vs) :: rest, acc =>
      match searchBudget leaf b rest (acc ++ [v]) with
      | .found a => .found a
      | .exhausted => searchBudget leaf b (vs :: rest) acc
      | .budgetOut => .budgetOut

/-! ### The reversed-accumulator fast twin (IDEAS 4.5)

`searchBudget` extends its accumulator with `acc ++ [v]` — an O(n)
list copy per tree node, O(n²) per branch (mirroring the reference
`search` of `solver/Search.lean`, whose own twin is IDEAS 4.1).  The
twin below threads the accumulator *reversed* (`v :: racc`, O(1) per
node) and pays the `reverse` back only at the leaves: the leaf
predicate is tested on `racc.reverse` — exactly the slot-order list
the reference tests — and a returned solution is in slot order too.
Budget accounting is unchanged (one unit per nested call), so the
sufficiency and monotonicity theorems transfer verbatim through the
equality `searchBudgetImpl_eq` behind the `implemented_by`
attribute below. -/

/-- The reversed-accumulator budgeted-search loop.  `racc` holds the
    already-fixed values in reverse order (the most recently fixed
    value first); the leaf predicate and the returned assignment are
    in slot order (`racc.reverse`). -/
def searchBudgetGo {α : Type} (leaf : List α → Bool) :
    Nat → List (List α) → List α → BudgetResult (List α)
  | 0, _, _ => .budgetOut
  | _ + 1, [], racc => if leaf racc.reverse then .found racc.reverse else .exhausted
  | _ + 1, [] :: _, _ => .exhausted
  | b + 1, (v :: vs) :: rest, racc =>
      match searchBudgetGo leaf b rest (v :: racc) with
      | .found a => .found a
      | .exhausted => searchBudgetGo leaf b (vs :: rest) racc
      | .budgetOut => .budgetOut

/-- **The bridge**: the reversed-accumulator loop is the reference
    `searchBudget` on the reversed accumulator.  Consing `v` onto
    `racc` mirrors `racc.reverse ++ [v]` (an O(1)
    `List.reverse_cons` step), so the twin tests and returns exactly
    what `searchBudget` would. -/
theorem searchBudgetGo_eq {α : Type} (leaf : List α → Bool) :
    ∀ (b : Nat) (slots : List (List α)) (racc : List α),
      searchBudgetGo leaf b slots racc = searchBudget leaf b slots racc.reverse := by
  intro b
  induction b with
  | zero =>
      intro slots racc
      simp only [searchBudgetGo, searchBudget]
  | succ b ih =>
      intro slots racc
      cases slots with
      | nil => simp only [searchBudgetGo, searchBudget]
      | cons d ds =>
          cases d with
          | nil => simp only [searchBudgetGo, searchBudget]
          | cons v vs =>
              rw [searchBudgetGo, ih, searchBudget, List.reverse_cons]
              cases hs' : searchBudget leaf b ds (racc.reverse ++ [v]) with
              | found a => rfl
              | exhausted => exact ih (vs :: ds) racc
              | budgetOut => rfl

/-- Same-shape fast twin of `searchBudget` (the `implemented_by`
    target): runs the reversed-accumulator loop from the slot-order
    accumulator, so the observable signature (and result) is the
    reference's. -/
def searchBudgetImpl {α : Type} (leaf : List α → Bool)
    (b : Nat) (slots : List (List α)) (acc : List α) : BudgetResult (List α) :=
  searchBudgetGo leaf b slots acc.reverse

/-- **The bridge for the budgeted search**: the fast twin is the
    reference `searchBudget` pointwise (the equality behind the
    `implemented_by` attribute below). -/
theorem searchBudgetImpl_eq {α : Type} (leaf : List α → Bool)
    (b : Nat) (slots : List (List α)) (acc : List α) :
    searchBudgetImpl leaf b slots acc = searchBudget leaf b slots acc := by
  unfold searchBudgetImpl
  rw [searchBudgetGo_eq, List.reverse_reverse]

-- IDEAS 4.5: the compiled `searchBudget` runs the reversed-accumulator
-- twin (equal by `searchBudgetImpl_eq`)
attribute [implemented_by searchBudgetImpl] searchBudget

/-! ### The guarantee of a found solution -/

/-- **Soundness of a found solution**: a `found r` outcome gives
    `search_some`'s conclusion — `r` extends the accumulator to a
    complete assignment of the slots passing the leaf predicate.
    Holds for every budget. -/
theorem searchBudget_found {α : Type} (leaf : List α → Bool) :
    ∀ (b : Nat) (slots : List (List α)) (acc : List α) (r : List α),
      searchBudget leaf b slots acc = .found r →
        ∃ a, a ∈ allAssigns slots ∧ r = acc ++ a ∧ leaf (acc ++ a) = true := by
  intro b
  induction b with
  | zero =>
      intro slots acc r h
      simp only [searchBudget] at h
      exact absurd h (by simp)
  | succ b ih =>
      intro slots acc r h
      cases slots with
      | nil =>
          simp only [searchBudget] at h
          by_cases hleaf : leaf acc = true
          · rw [if_pos hleaf] at h
            have hra : r = acc := by simpa using h.symm
            subst hra
            refine ⟨[], by simp [allAssigns], ?_, ?_⟩
            · rw [List.append_nil]
            · simpa using hleaf
          · rw [if_neg hleaf] at h
            exact absurd h (by simp)
      | cons d ds =>
          cases d with
          | nil =>
              simp only [searchBudget] at h
              exact absurd h (by simp)
          | cons v vs =>
              simp only [searchBudget] at h
              cases hs : searchBudget leaf b ds (acc ++ [v]) with
              | found a =>
                  simp only [hs] at h
                  have hra : a = r := by simpa using h
                  obtain ⟨a', ha', rfl, hleaf⟩ := ih ds (acc ++ [v]) a hs
                  refine ⟨v :: a', ?_, ?_, ?_⟩
                  · rw [mem_allAssigns_singleton]
                    exact ⟨v, List.mem_cons_self, a', ha', rfl⟩
                  · simpa [List.append_assoc, List.cons_append] using hra.symm
                  · simpa [List.append_assoc, List.cons_append] using hleaf
              | exhausted =>
                  simp only [hs] at h
                  obtain ⟨a', ha', hrfl, hleaf⟩ := ih (vs :: ds) acc r h
                  refine ⟨a', allAssigns_subset_cons v vs ds a' ha', hrfl, hleaf⟩
              | budgetOut =>
                  simp only [hs] at h
                  exact absurd h (by simp)

/-! ### The guarantee of an exhaustion -/

/-- **Soundness of an exhaustion**: an `exhausted` outcome gives
    `search_none`'s conclusion — every complete assignment of the
    slots fails the leaf predicate (relative to the accumulator).
    This is what makes `exhausted` a real UNSAT certificate, and
    what the safety theorem below relies on.  Holds for every
    budget. -/
theorem searchBudget_exhausted {α : Type} (leaf : List α → Bool) :
    ∀ (b : Nat) (slots : List (List α)) (acc : List α),
      searchBudget leaf b slots acc = .exhausted →
        ∀ a ∈ allAssigns slots, leaf (acc ++ a) = false := by
  intro b
  induction b with
  | zero =>
      intro slots acc h
      simp only [searchBudget] at h
      exact absurd h (by simp)
  | succ b ih =>
      intro slots acc h
      cases slots with
      | nil =>
          simp only [searchBudget] at h
          by_cases hleaf : leaf acc = true
          · rw [if_pos hleaf] at h
            exact absurd h (by simp)
          · rw [if_neg hleaf] at h
            intro a ha
            have haNil : a = [] := by simpa [allAssigns] using ha
            subst haNil
            rw [List.append_nil]
            simpa using hleaf
      | cons d ds =>
          cases d with
          | nil =>
              intro a ha
              exact absurd ha (by simp [allAssigns])
          | cons v vs =>
              simp only [searchBudget] at h
              cases hs : searchBudget leaf b ds (acc ++ [v]) with
              | found a =>
                  simp only [hs] at h
                  exact absurd h (by simp)
              | exhausted =>
                  simp only [hs] at h
                  intro a ha
                  rw [mem_allAssigns_singleton] at ha
                  obtain ⟨w, hw, a', ha', rfl⟩ := ha
                  by_cases hw' : w = v
                  · have hleaf := ih ds (acc ++ [v]) hs a' ha'
                    rw [hw']
                    simpa [List.append_assoc, List.cons_append] using hleaf
                  · have hex2 : searchBudget leaf b (vs :: ds) acc = .exhausted :=
                      h
                    have hwvs : w ∈ vs := by
                      rcases List.mem_cons.mp hw with heq | hin
                      · exact absurd heq hw'
                      · exact hin
                    have hgen : ∀ (xs : List α) (b' : α),
                        b' ∈ xs → ∀ (r : List (List α)) (t : List α),
                          t ∈ allAssigns r → b' :: t ∈ allAssigns (xs :: r) := by
                      intro xs b' hmem r t ht
                      induction xs generalizing t with
                      | nil => exact absurd hmem (by simp)
                      | cons u us ih' =>
                          by_cases hmemu : u = b'
                          · subst hmemu
                            rw [allAssigns, List.mem_flatMap]
                            exact ⟨t, ht, by
                              have := List.mem_map_of_mem
                                (a := u) (f := fun w => w :: t) (l := u :: us)
                                List.mem_cons_self
                              exact this⟩
                          · have hbus : b' ∈ us := by
                              rcases List.mem_cons.mp hmem with heq | hin
                              · exact absurd heq.symm hmemu
                              · exact hin
                            have hrec : b' :: t ∈ allAssigns (us :: r) := ih' hbus t ht
                            exact allAssigns_subset_cons u us r _ hrec
                    exact ih (vs :: ds) acc hex2 (w :: a')
                      (hgen vs w hwvs ds a' ha')
              | budgetOut =>
                  simp only [hs] at h
                  exact absurd h (by simp)

/-! ### Accounting: sufficient budgets reproduce the reference search

The three-way adapter connecting `Option` outcomes to `BudgetResult`
claims; with a sufficient budget the budgeted search computes
exactly `ofOption (search ...)`. -/

/-- The claim corresponding to a reference-search outcome:
    `some a` is the claim `found a`, `none` is the certificate
    `exhausted`. -/
def ofOption {α : Type} : Option α → BudgetResult α
  | some a => .found a
  | none => .exhausted

/-- **Sufficiency accounting**: with a budget of at least
    `searchNodes slots` (the search's depth ceiling, plus one),
    the budgeted search and the reference search agree exactly —
    the budget is never exhausted, `found` mirrors `some`, and
    `exhausted` mirrors `none`. -/
theorem searchBudget_eq {α : Type} (leaf : List α → Bool) :
    ∀ (b : Nat) (slots : List (List α)) (acc : List α),
      searchNodes slots ≤ b →
        searchBudget leaf b slots acc = ofOption (search leaf slots acc) := by
  intro b
  induction b with
  | zero =>
      intro slots acc hle
      simp only [searchNodes] at hle
      omega
  | succ b ih =>
      intro slots acc hle
      cases slots with
      | nil =>
          simp only [searchBudget, search]
          by_cases hl : leaf acc = true
          · rw [if_pos hl, if_pos hl]
            rfl
          · rw [if_neg hl, if_neg hl]
            rfl
      | cons d ds =>
          cases d with
          | nil => simp only [searchBudget, search, ofOption]
          | cons v vs =>
              have hm : slotsMeasure ((v :: vs) :: ds)
                  = (vs.length + 1 + 1) + slotsMeasure ds := by
                simp only [slotsMeasure, List.foldr_cons, List.length_cons]
              have hm2 : slotsMeasure (vs :: ds)
                  = (vs.length + 1) + slotsMeasure ds := by
                simp only [slotsMeasure, List.foldr_cons]
              simp only [searchNodes] at hle
              rw [hm] at hle
              have hb1 : searchNodes ds ≤ b := by
                simp only [searchNodes]
                omega
              have hb2 : searchNodes (vs :: ds) ≤ b := by
                simp only [searchNodes]
                omega
              simp only [searchBudget, search]
              rw [ih ds (acc ++ [v]) hb1]
              cases hsr : search leaf ds (acc ++ [v]) with
              | some a => rfl
              | none =>
                  rw [ih (vs :: ds) acc hb2]
                  rfl

/-- A sufficient budget is never exhausted mid-search: `budgetOut`
    happens only when the budget was insufficient for the search
    tree. -/
theorem searchBudget_ne_budgetOut {α : Type} (leaf : List α → Bool) (b : Nat)
    (slots : List (List α)) (acc : List α) (hle : searchNodes slots ≤ b) :
    searchBudget leaf b slots acc ≠ .budgetOut := by
  rw [searchBudget_eq leaf b slots acc hle]
  cases hs : search leaf slots acc with
  | some a =>
      simp only [hs] at hs ⊢
      exact fun h => nomatch h
  | none =>
      simp only [hs] at hs ⊢
      exact fun h => nomatch h

/-- **Sufficiency agreement**: with a budget of at least
    `searchNodes slots`, each claim of the budgeted search is
    exactly the corresponding outcome of the reference search —
    `found r` iff `search` returns `some r`, `exhausted` iff
    `search` returns `none`. -/
theorem searchBudget_search {α : Type} (leaf : List α → Bool) (b : Nat)
    (slots : List (List α)) (acc : List α) (hle : searchNodes slots ≤ b) :
    (∀ r, searchBudget leaf b slots acc = .found r ↔
        search leaf slots acc = some r) ∧
    (searchBudget leaf b slots acc = .exhausted ↔
        search leaf slots acc = none) := by
  have heq := searchBudget_eq leaf b slots acc hle
  constructor
  · intro r
    constructor
    · intro h
      rw [heq] at h
      cases hs : search leaf slots acc with
      | some a =>
          rw [hs] at h
          simp only [ofOption] at h
          have har : a = r := BudgetResult.found.inj h
          rw [har]
      | none =>
          rw [hs] at h
          simp only [ofOption] at h
          exact absurd h (by simp)
    · intro h
      rw [heq, h]
      rfl
  · constructor
    · intro h
      rw [heq] at h
      cases hs : search leaf slots acc with
      | some a =>
          rw [hs] at h
          simp only [ofOption] at h
          exact absurd h (by simp)
      | none => rfl
    · intro h
      rw [heq, h]
      rfl

/-- **Monotonicity of claims**: if the run at budget `b'` makes a
    claim — `found r` or `exhausted` — then the run at any budget
    `b ≥ b'` makes the *same* claim.  Growing the budget can turn
    an `unknown` into a claim, never a claim into a different
    claim. -/
theorem searchBudget_monotone {α : Type} (leaf : List α → Bool) :
    ∀ (b' : Nat) (b : Nat) (slots : List (List α)) (acc : List α),
      b' ≤ b →
      (∀ r, searchBudget leaf b' slots acc = .found r →
        searchBudget leaf b slots acc = .found r) ∧
      (searchBudget leaf b' slots acc = .exhausted →
        searchBudget leaf b slots acc = .exhausted) := by
  intro b'
  induction b' with
  | zero =>
      intro b slots acc _
      refine ⟨fun r h => ?_, fun h => ?_⟩
      · simp only [searchBudget] at h
        exact absurd h (by simp)
      · simp only [searchBudget] at h
        exact absurd h (by simp)
  | succ k ih =>
      intro b slots acc hle
      cases b with
      | zero => omega
      | succ j =>
          have hkj : k ≤ j := by omega
          cases slots with
          | nil =>
              simp only [searchBudget]
              exact ⟨fun _ h => h, fun h => h⟩
          | cons d ds =>
              cases d with
              | nil =>
                  simp only [searchBudget]
                  exact ⟨fun _ h => h, fun h => h⟩
              | cons v vs =>
                  refine ⟨fun r h => ?_, fun h => ?_⟩
                  · simp only [searchBudget] at h ⊢
                    cases hs : searchBudget leaf k ds (acc ++ [v]) with
                    | found a =>
                        simp only [hs] at h
                        have hja : searchBudget leaf j ds (acc ++ [v]) = .found a :=
                          (ih j ds (acc ++ [v]) hkj).1 a hs
                        simp only [hja]
                        exact h
                    | exhausted =>
                        simp only [hs] at h
                        have hje : searchBudget leaf j ds (acc ++ [v]) = .exhausted :=
                          (ih j ds (acc ++ [v]) hkj).2 hs
                        simp only [hje]
                        exact (ih j (vs :: ds) acc hkj).1 r h
                    | budgetOut =>
                        simp only [hs] at h
                        exact absurd h (by simp)
                  · simp only [searchBudget] at h ⊢
                    cases hs : searchBudget leaf k ds (acc ++ [v]) with
                    | found a =>
                        simp only [hs] at h
                        have hja : searchBudget leaf j ds (acc ++ [v]) = .found a :=
                          (ih j ds (acc ++ [v]) hkj).1 a hs
                        simp only [hja]
                        exact h
                    | exhausted =>
                        simp only [hs] at h
                        have hje : searchBudget leaf j ds (acc ++ [v]) = .exhausted :=
                          (ih j ds (acc ++ [v]) hkj).2 hs
                        simp only [hje]
                        exact (ih j (vs :: ds) acc hkj).2 h
                    | budgetOut =>
                        simp only [hs] at h
                        exact absurd h (by simp)

/-! ## The restart loop -/

/-- **The resource-bounded solver.**  Try `searchBudget` with the
    schedule's budgets in order, each attempt from a fresh root
    state (the original, untouched slot list — nothing is retained
    between attempts in this round).  The first attempt that makes
    a claim wins: `found` → `sat`, `exhausted` → `unsat`; a
    `budgetOut` attempt claims nothing and retries with the next
    budget.  If every attempt is interrupted, the result is
    `unknown`: no verdict. -/
def restartSearch {α : Type} (leaf : List α → Bool) :
    List Nat → List (List α) → BoundedResult (List α)
  | [], _ => .unknown
  | b :: bs, slots =>
      match searchBudget leaf b slots [] with
      | .found a => .sat a
      | .exhausted => .unsat
      | .budgetOut => restartSearch leaf bs slots

/-- **SAT soundness of the restart loop**: a returned assignment is
    a complete assignment of the slots and passes the leaf
    predicate. -/
theorem restartSearch_sat_sound {α : Type} (leaf : List α → Bool) :
    ∀ (schedule : List Nat) (slots : List (List α)) (r : List α),
      restartSearch leaf schedule slots = .sat r →
        r ∈ allAssigns slots ∧ leaf r = true := by
  intro schedule
  induction schedule with
  | nil =>
      intro slots r h
      simp only [restartSearch] at h
      exact absurd h (by simp)
  | cons b bs ih =>
      intro slots r h
      simp only [restartSearch] at h
      cases hs : searchBudget leaf b slots [] with
      | found a =>
          simp only [hs] at h
          have hra : a = r := BoundedResult.sat.inj h
          obtain ⟨a', ha', hrfl, hleaf⟩ := searchBudget_found leaf b slots [] a hs
          rw [List.nil_append] at hrfl hleaf
          subst hra
          rw [hrfl]
          exact ⟨ha', hleaf⟩
      | exhausted =>
          simp only [hs] at h
          exact absurd h (by simp)
      | budgetOut =>
          simp only [hs] at h
          exact ih slots r h

/-- **UNSAT soundness of the restart loop**: an `unsat` verdict
    means every complete assignment of the slots fails the leaf
    predicate — reachable only from a real exhaustion, never from
    an interruption. -/
theorem restartSearch_unsat_sound {α : Type} (leaf : List α → Bool) :
    ∀ (schedule : List Nat) (slots : List (List α)),
      restartSearch leaf schedule slots = .unsat →
        ∀ a ∈ allAssigns slots, leaf a = false := by
  intro schedule
  induction schedule with
  | nil =>
      intro slots h
      simp only [restartSearch] at h
      exact absurd h (by simp)
  | cons b bs ih =>
      intro slots h
      simp only [restartSearch] at h
      cases hs : searchBudget leaf b slots [] with
      | found a =>
          simp only [hs] at h
          exact absurd h (by simp)
      | exhausted =>
          have hexh : searchBudget leaf b slots [] = .exhausted := hs
          have hnone := searchBudget_exhausted leaf b slots [] hexh
          simpa [List.nil_append] using hnone
      | budgetOut =>
          simp only [hs] at h
          exact ih slots h

/-- **The safety theorem (PLAN 6.6)**: if some complete assignment
    of the slots passes the leaf predicate, the restart loop
    *never* returns `unsat`.  A bounded — interrupted, or even
    completed — run cannot turn a satisfiable instance into a
    false UNSAT verdict; the worst it can do is `unknown`. -/
theorem restartSearch_never_falseUnsat {α : Type} (leaf : List α → Bool)
    (schedule : List Nat) (slots : List (List α))
    (hsat : ∃ a ∈ allAssigns slots, leaf a = true) :
    restartSearch leaf schedule slots ≠ .unsat := by
  intro hcontra
  obtain ⟨a, ha, hleaf⟩ := hsat
  have hnone := restartSearch_unsat_sound leaf schedule slots hcontra a ha
  rw [hleaf] at hnone
  exact absurd hnone (by simp)

/-- **Fairness of a sufficient schedule**: any schedule containing
    a budget of at least `searchNodes slots` returns a decided
    verdict — `sat` or `unsat`, never `unknown`. -/
theorem restartSearch_complete {α : Type} (leaf : List α → Bool) :
    ∀ (schedule : List Nat) (slots : List (List α)) (b : Nat),
      b ∈ schedule → searchNodes slots ≤ b →
      restartSearch leaf schedule slots ≠ .unknown := by
  intro schedule
  induction schedule with
  | nil =>
      intro slots b hmem
      exact absurd hmem (by simp)
  | cons b' bs ih =>
      intro slots b hmem hcalls hcontra
      simp only [restartSearch] at hcontra
      cases hs : searchBudget leaf b' slots [] with
      | found a =>
          simp only [hs] at hcontra
          exact absurd hcontra (by simp)
      | exhausted =>
          simp only [hs] at hcontra
          exact absurd hcontra (by simp)
      | budgetOut =>
          simp only [hs] at hcontra
          by_cases hbin : b ∈ bs
          · exact ih slots b hbin hcalls hcontra
          · have hbb : b = b' := by
              rcases List.mem_cons.mp hmem with heq | hin
              · exact heq
              · exact absurd hin hbin
            rw [hbb] at hcalls
            exact absurd hs (searchBudget_ne_budgetOut leaf b' slots [] hcalls)

/-! ## The FlatZinc layer

`solveModelBounded` mirrors `solveModel`'s gates and leaf-check
architecture (the leaf is the verified checker itself, `solveLeaf`)
with `restartSearch` in place of `search`.  Static refusals
(unsupported predicates, ill-formed models, out-of-fragment or
capped domains) produce `unknown` — no verdict — since `unsat` is
reserved for certified exhaustion. -/

/-- **The resource-bounded FlatZinc solver.**  Runs the restart
    loop over the model's finite search slots with the given
    budget schedule; each leaf's candidate solution text is
    validated by the verified checker (through a `PreparedModel`
    built once per solve — the prepared twin of the leaf is
    `solveLeaf` pointwise by `solveLeafP_eq`) before being
    reported, as in `solveModel`.  Refuses nothing loudly:
    out-of-fragment or ill-formed models yield `unknown` (no
    claim), and an exhausted budget schedule yields `unknown`;
    only a complete exhaustion of the search space yields
    `unsat`. -/
def solveModelBounded (m : Model) (schedule : List Nat) : BoundedResult String :=
  match firstUnsupportedFast m with
  | some _ => .unknown
  | none =>
      if wellFormedFastB m then
        match slotsChecked m with
        | .error _ => .unknown
        | .ok slots =>
            let p := prepareModel m
            match restartSearch (solveLeafP p (slots.map Prod.fst)) schedule
                (slots.map Prod.snd) with
            | .sat asg => .sat (emitAssignment (slots.map Prod.fst) asg)
            | .unsat => .unsat
            | .unknown => .unknown
      else
        .unknown

/-- **SAT soundness**: a solution text returned by
    `solveModelBounded` is accepted by the verified front door.  By
    `checkModelSolution_correct`, the model is well formed, every
    constraint name is checkable, and the parsed entries' completed
    store satisfies `Satisfies fullSig fullInterp`. -/
theorem solveModelBounded_sat_sound {m : Model} {schedule : List Nat}
    {text : String} (h : solveModelBounded m schedule = .sat text) :
    checkModelSolution m text = .accepted := by
  rw [← checkModelSolutionFast_eq]
  simp only [solveModelBounded] at h
  cases huns : firstUnsupportedFast m with
  | some n => rw [huns] at h; exact absurd h (by simp)
  | none =>
      rw [huns] at h
      simp only at h
      cases hwf : wellFormedFastB m with
      | false =>
          rw [if_neg (by simp [hwf])] at h
          exact absurd h (by simp)
      | true =>
          rw [if_pos (by simp [hwf])] at h
          cases hslots : slotsChecked m with
          | error e => rw [hslots] at h; exact absurd h (by simp)
          | ok slots =>
              rw [hslots] at h
              simp only at h
              rw [solveLeafP_eq' m (slots.map Prod.fst)] at h
              cases hres : restartSearch (solveLeaf m (slots.map Prod.fst)) schedule
                  (slots.map Prod.snd) with
              | sat asg =>
                  rw [hres] at h
                  have htext : text = emitAssignment (slots.map Prod.fst) asg :=
                    (BoundedResult.sat.inj h).symm
                  subst htext
                  obtain ⟨_ha, hleaf⟩ :=
                    restartSearch_sat_sound (solveLeaf m (slots.map Prod.fst)) schedule
                      (slots.map Prod.snd) asg hres
                  simp only [solveLeaf, emitAssignment, beq_iff_eq] at hleaf
                  exact hleaf
              | unsat => rw [hres] at h; exact absurd h (by simp)
              | unknown => rw [hres] at h; exact absurd h (by simp)

/-- **UNSAT soundness**: if `solveModelBounded` returns `unsat`,
    then no complete assignment of the model's search-slot domains
    yields an accepted solution — the verdict can only come from a
    real exhaustion, never from an interrupted search. -/
theorem solveModelBounded_unsat_sound {m : Model} {schedule : List Nat}
    (h : solveModelBounded m schedule = .unsat)
    {asg : List Value} (hmem : asg ∈ allAssigns (slotDomains m)) :
    checkModelSolution m (emitAssignment (slotNames m) asg) ≠ .accepted := by
  intro hacc
  rw [← checkModelSolutionFast_eq] at hacc
  simp only [solveModelBounded] at h
  cases huns : firstUnsupportedFast m with
  | some n => rw [huns] at h; exact absurd h (by simp)
  | none =>
      rw [huns] at h
      simp only at h
      cases hwf : wellFormedFastB m with
      | false =>
          rw [if_neg (by simp [hwf])] at h
          exact absurd h (by simp)
      | true =>
          rw [if_pos (by simp [hwf])] at h
          cases hslots : slotsChecked m with
          | error e => rw [hslots] at h; exact absurd h (by simp)
          | ok slots =>
              rw [hslots] at h
              simp only at h
              rw [solveLeafP_eq' m (slots.map Prod.fst)] at h
              cases hres : restartSearch (solveLeaf m (slots.map Prod.fst)) schedule
                  (slots.map Prod.snd) with
              | sat a => rw [hres] at h; exact absurd h (by simp)
              | unknown => rw [hres] at h; exact absurd h (by simp)
              | unsat =>
                  have hnone := restartSearch_unsat_sound
                    (solveLeaf m (slots.map Prod.fst)) schedule (slots.map Prod.snd) hres
                  have hslots' : modelSlots m = some slots :=
                    (modelSlots_eq.mpr hslots)
                  obtain ⟨hnames, hdoms⟩ :=
                    slotNames_domains_of_modelSlots hslots'
                  rw [hdoms] at hmem
                  have hleaf := hnone asg hmem
                  have hleafacc : solveLeaf m (slots.map Prod.fst) asg = true := by
                    simp only [solveLeaf, beq_iff_eq]
                    rw [← hnames]
                    exact hacc
                  rw [hleafacc] at hleaf
                  exact Bool.noConfusion hleaf

/-- **The safety theorem at the FlatZinc layer (PLAN 6.6)**: a
    model with an accepted slot assignment is never reported
    `unsat`, whatever the schedule — the worst a bounded run can do
    is `unknown`. -/
theorem solveModelBounded_never_falseUnsat {m : Model} {schedule : List Nat}
    (hsat : ∃ asg ∈ allAssigns (slotDomains m),
      checkModelSolution m (emitAssignment (slotNames m) asg) = .accepted) :
    solveModelBounded m schedule ≠ .unsat := by
  obtain ⟨asg, hmem, hacc⟩ := hsat
  intro hcontra
  exact solveModelBounded_unsat_sound hcontra hmem hacc

end LeanFzn.Solver

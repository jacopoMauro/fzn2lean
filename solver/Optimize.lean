import solver.Enum

/-!
# Optimization (PLAN.md 6.7, optimization half)

This module delivers the optimization half of PLAN 6.7:
branch-and-bound minimization/maximization whose `optimal` verdicts
carry both satisfaction and the theorem that no satisfying
assignment has a better objective.

## The two entry points

* `optimizeModel` — the *reference optimizer*, correctness-first and
  mirroring `enumModel`'s design: gate exactly like `solveModel`
  (`firstUnsupportedFast`, `wellFormedFastB`, `slotsChecked`), then
  enumerate **all** satisfying assignments once (`enumerateAll` with
  the unchanged leaf `solveLeaf`), pair each with its slot-level
  objective, and pick the best (`pickBest`, a fold with a proved
  minimality lemma).  Its correctness is immediate from
  `enumerateAll_mem_iff_root`: every checker-accepted assignment is
  among the enumerated, so the pick ranges over all of them.

* `optimizeModelBb` — the improving-bound refinement (PLAN 6.7's
  mechanism): rounds of `search`, each with the leaf strengthened by
  the incumbent's value (`bbLeaf`: the checker's leaf *and* the
  objective strictly better than the incumbent, `objBetter`).  A
  found assignment becomes the new incumbent; the next round starts
  over.  The first round uses the *plain* satisfaction leaf (no
  objective conjunct), so an empty first round certifies plain
  unsatisfiability; a later round that finds no improvement
  certifies optimality of the incumbent (via `search_none`: every
  remaining assignment fails the strengthened leaf, i.e. none is
  strictly better).  Rounds are bounded by fuel (`leavesProduct
  doms + 1`, one more than the number of complete assignments — each
  improving round strictly improves the incumbent and incumbents
  come from distinct assignments, so the chain of rounds is at most
  that long); at fuel exhaustion the entry point falls back to the
  reference optimizer's full-enumeration pick, so every returned
  verdict is certified by one of the two arguments, never by "the
  fuel ran out".

## The objective at slot level (scope decision)

The solver is slot-based, so the objective is evaluated on slot
assignments (`slotObjective`): an integer literal evaluates to
itself; an identifier is looked up in the assignment by slot name
(`slotLookup`).  **Compound expressions are not supported** — in this
grammar the objective is a `BasicExpr` (literal or identifier) anyway,
so the residual cases are non-integer literals and identifiers that
are not integer-valued search slots (initialized variables,
parameters, Booleans): the optimizers report
`.unsupported "objective is not an integer literal or an
integer-valued search slot"` for those (the gate is `slotObjFn`,
which for identifiers additionally requires the named slot's values
to be all integers — `objSlotOk` — so that `slotLookup` is *total*
over `allAssigns` of the searched domains, `slotLookup_total`; that
totality is what keeps an `.unsat` verdict sound).  A satisfy model
has no objective; `optimizeModel`/`optimizeModelBb` refuse it with
`.unsupported` (use `solveModel` for satisfaction).

## The master theorems

Both entry points carry the same four theorems (stated at the level
the solver decides: assignments over `allAssigns (slotDomains m)`
whose emitted text the checker accepts, exactly like
`solveModel_unsat_sound` and `enumModel_complete`):

* `optimizeModel_sat_sound` / `optimizeModelBb_sat_sound` — the
  returned text is accepted by the verified front door.

* `optimizeModel_optimal` / `optimizeModelBb_optimal` — **the
  optimality theorem**: for every complete assignment of the slot
  domains whose emitted text is checker-accepted and whose objective
  is defined (`slotObjective m (slotNames m) asg = some v'`), the
  returned value is no worse: `objLeOf m v v'` (for `minimize` this
  is `v ≤ v'`, for `maximize` `v' ≤ v`).  Assignments whose objective
  is *undefined* at slot level are outside the quantification — the
  gate above makes them impossible for gated models anyway.

* `optimizeModel_unsat` / `optimizeModelBb_unsat` — an `.unsat`
  verdict excludes every accepted assignment.

* `optimizeModel_value` / `optimizeModelBb_value` — the returned
  value is the objective of the returned text's assignment.

* `optimizeModelBb_agrees` — the two optimizers agree on the optimal
  *value* whenever both return `.optimal` (a corollary of the two
  optimality theorems: each returned value is at least as good as
  the other).

All theorems are unconditional (no hypotheses beyond the returned
verdict).
-/

namespace LeanFzn.Solver

open LeanFzn LeanFzn.Solution LeanFzn.Check LeanFzn.Globals

/-! ## The objective order

One parameter `min : Bool` selects the direction (`true` =
minimize, `false` = maximize) everywhere below, so the machinery is
written once and instantiated twice.  `objLe` is the propositional
twin ("`a` is at least as good as `b`"), `selLt` the Boolean strict
improvement test used by the pick and the bound. -/

/-- The direction of optimization: `true` for minimize, `false` for
    maximize.  "The first argument is at least as good as the
    second" in that direction. -/
def objLe (min : Bool) (a b : Int) : Prop :=
  match min with
  | true => a ≤ b
  | false => b ≤ a

/-- Reflexivity of the objective order. -/
theorem objLe_refl (min : Bool) (a : Int) : objLe min a a := by
  cases min <;> simp only [objLe] <;> omega

/-- Transitivity of the objective order. -/
theorem objLe_trans (min : Bool) (a b c : Int) (h1 : objLe min a b)
    (h2 : objLe min b c) : objLe min a c := by
  cases min <;> simp only [objLe] at h1 h2 ⊢ <;> omega

/-- The strict improvement test used by the pick and the bound. -/
def selLt (min : Bool) (a b : Int) : Bool :=
  match min with
  | true => a < b
  | false => b < a

/-- A strict improvement is an instance of the objective order. -/
theorem selLt_true_objLe {min : Bool} {a b : Int} (h : selLt min a b = true) :
    objLe min a b := by
  cases min with
  | true =>
      simp only [selLt] at h
      have h2 : a < b := of_decide_eq_true h
      simp only [objLe]
      omega
  | false =>
      simp only [selLt] at h
      have h2 : b < a := of_decide_eq_true h
      simp only [objLe]
      omega

/-- A failed strict improvement reverses into the objective order. -/
theorem selLt_false_objLe {min : Bool} {a b : Int} (h : selLt min a b = false) :
    objLe min b a := by
  cases min with
  | true =>
      simp only [selLt] at h
      cases hd : decide (a < b) with
      | true => rw [hd] at h; exact absurd h (by simp)
      | false =>
          have h2 : ¬ (a < b) := of_decide_eq_false hd
          simp only [objLe]
          omega
  | false =>
      simp only [selLt] at h
      cases hd : decide (b < a) with
      | true => rw [hd] at h; exact absurd h (by simp)
      | false =>
          have h2 : ¬ (b < a) := of_decide_eq_false hd
          simp only [objLe]
          omega

/-- The failed-improvement form of the previous lemma, as it arises
    from a negated `if` condition. -/
theorem selLt_not_objLe {min : Bool} {a b : Int} (h : ¬ (selLt min a b = true)) :
    objLe min b a := by
  cases hs : selLt min a b with
  | true => exact absurd hs h
  | false => exact selLt_false_objLe hs

/-- The objective order of a whole model, matching its solve item:
    `v ≤ v'` under `minimize`, `v' ≤ v` under `maximize`.  The
    `satisfy` case is unreachable for `.optimal` verdicts (the
    optimizers refuse satisfaction models with `.unsupported`). -/
def objLeOf (m : Model) (a b : Int) : Prop :=
  match m.solve with
  | .minimize _ _ => a ≤ b
  | .maximize _ _ => b ≤ a
  | .satisfy _ => a ≤ b

/-! ## The best pick

`pickBest` folds a list of `(text, value)` pairs, keeping the pair
with the best objective (ties keep the tail's winner).  The pick's
minimality (`pickBest_minimal`) is the small standalone lemma the
optimality proofs rest on. -/

/-- Pick the pair with the best objective from a list of
    `(text, value)` pairs; `none` on the empty list. -/
def pickBest (min : Bool) : List (String × Int) → Option (String × Int)
  | [] => none
  | p :: ps =>
      match pickBest min ps with
      | none => some p
      | some b => some (if selLt min p.2 b.2 then p else b)

/-- `pickBest` returns `none` only on the empty list. -/
theorem pickBest_eq_nil {min : Bool} {l : List (String × Int)}
    (h : pickBest min l = none) : l = [] := by
  cases l with
  | nil => rfl
  | cons p ps =>
      simp only [pickBest] at h
      cases hp : pickBest min ps with
      | none => rw [hp] at h; exact absurd h (by simp)
      | some b => rw [hp] at h; exact absurd h (by simp)

/-- The picked pair is a member of the list. -/
theorem pickBest_mem {min : Bool} : ∀ (l : List (String × Int)) (r : String × Int),
    pickBest min l = some r → r ∈ l := by
  intro l
  induction l with
  | nil => intro r h; exact absurd h (by simp [pickBest])
  | cons p ps ih =>
      intro r h
      simp only [pickBest] at h
      cases hp : pickBest min ps with
      | none =>
          rw [hp] at h
          have hr : r = p := (Option.some.inj h).symm
          subst hr
          exact List.mem_cons_self
      | some b =>
          rw [hp] at h
          have hr : r = if selLt min p.2 b.2 then p else b := (Option.some.inj h).symm
          subst hr
          split
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih b hp)

/-- **The pick's minimality**: the picked pair's value is at least as
    good as the value of every list member. -/
theorem pickBest_minimal {min : Bool} :
    ∀ (l : List (String × Int)) (r p : String × Int),
      p ∈ l → pickBest min l = some r → objLe min r.2 p.2 := by
  intro l
  induction l with
  | nil => intro r p hp _; exact absurd hp (by simp)
  | cons q qs ih =>
      intro r p hmem h
      simp only [pickBest] at h
      cases hrec : pickBest min qs with
      | none =>
          have hqs : qs = [] := pickBest_eq_nil hrec
          rw [hrec] at h
          have hr : r = q := (Option.some.inj h).symm
          subst hr
          rw [hqs] at hmem
          rcases List.mem_cons.mp hmem with rfl | hpmem
          · exact objLe_refl min _
          · exact absurd hpmem (by simp)
      | some b =>
          rw [hrec] at h
          have hr : r = if selLt min q.2 b.2 then q else b := (Option.some.inj h).symm
          subst hr
          rcases List.mem_cons.mp hmem with rfl | hpmem
          · split
            · exact objLe_refl min _
            · next hcond => exact selLt_not_objLe hcond
          · have hIH : objLe min b.2 p.2 := ih b p hpmem hrec
            split
            · next hcond => exact objLe_trans min _ _ _ (selLt_true_objLe hcond) hIH
            · exact hIH

/-! ## Objective evaluation over slot assignments -/

/-- The integer content of a value, if any. -/
private def valueInt : Value → Option Int
  | .int i => some i
  | _ => none

/-- Is the value an integer?  (The Boolean twin of `valueInt`
    being defined.) -/
private def isIntValue : Value → Bool
  | .int _ => true
  | _ => false

/-- Look up a slot by name in a parallel (names, assignment) pair of
    lists and take its integer value.  First occurrence wins, exactly
    like the slot extraction takes the first declaration. -/
def slotLookup : List String → List Value → String → Option Int
  | [], _, _ => none
  | _ :: _, [], _ => none
  | n' :: ns, v :: vs, n =>
      if n' == n then valueInt v else slotLookup ns vs n

/-- Does the objective identifier name a slot whose values are all
    integers?  Walks the slot names and domains in lockstep; on the
    first name match, checks that slot's domain.  This is the gate
    that makes `slotLookup` total over `allAssigns` of the searched
    domains (`slotLookup_total`). -/
def objSlotOk : List String → List (List Value) → String → Bool
  | [], _, _ => false
  | _ :: _, [], _ => false
  | n' :: ns, d :: ds, n =>
      if n' == n then d.all isIntValue else objSlotOk ns ds n

/-- **Totality of the slot lookup**: if the objective names a slot
    whose (first-occurrence) domain is all integers, then every
    complete assignment of the domains yields a defined objective. -/
theorem slotLookup_total : ∀ (names : List String) (doms : List (List Value))
    (asg : List Value) (n : String), objSlotOk names doms n = true →
    names.length = doms.length → asg ∈ allAssigns doms →
    ∃ v, slotLookup names asg n = some v := by
  intro names
  induction names with
  | nil => intro doms asg n hok _ _; exact absurd hok (by simp [objSlotOk])
  | cons n' ns ih =>
      intro doms asg n hok hlen hmem
      cases doms with
      | nil =>
          simp only [List.length_cons, List.length_nil] at hlen
          omega
      | cons d ds =>
          cases d with
          | nil =>
              have hnil : allAssigns (([] : List Value) :: ds) = [] := rfl
              rw [hnil] at hmem
              exact absurd hmem (by simp)
          | cons v vs =>
              rw [mem_allAssigns_singleton] at hmem
              obtain ⟨w, hw, asg', hasg', rfl⟩ := hmem
              simp only [objSlotOk] at hok
              split at hok
              · next hn =>
                  have hall := (List.all_eq_true.mp hok) w hw
                  have hlen' : ns.length = ds.length := by
                    simp only [List.length_cons] at hlen
                    omega
                  cases w with
                  | int k =>
                      refine ⟨k, ?_⟩
                      simp only [slotLookup, if_pos hn, valueInt]
                  | bool b => exact absurd hall (by simp [isIntValue])
                  | setOfInt s => exact absurd hall (by simp [isIntValue])
                  | array xs => exact absurd hall (by simp [isIntValue])
              · next hn =>
                  have hlen' : ns.length = ds.length := by
                    simp only [List.length_cons] at hlen
                    omega
                  obtain ⟨v', hv'⟩ := ih ds asg' n hok hlen' hasg'
                  refine ⟨v', ?_⟩
                  simp only [slotLookup, if_neg hn]
                  exact hv'

/-- Evaluate an objective expression on a slot assignment: an
    integer literal is its value; an identifier is looked up by slot
    name; anything else is undefined at slot level. -/
def slotObjectiveExpr (e : BasicExpr) (names : List String) (asg : List Value) :
    Option Int :=
  match e with
  | .lit (.int i) => some i
  | .ident x => slotLookup names asg x.name
  | _ => none

/-- **The slot-level objective of a model**: the solve item's
    objective expression evaluated on a slot assignment (literals
    directly, identifiers by slot lookup; `none` for satisfaction
    models and expressions outside the supported scope). -/
def slotObjective (m : Model) (names : List String) (asg : List Value) :
    Option Int :=
  match m.solve with
  | .minimize _ e => slotObjectiveExpr e names asg
  | .maximize _ e => slotObjectiveExpr e names asg
  | .satisfy _ => none

/-- The sanctioned objective evaluator of a model: `some f` when the
    objective expression is an integer literal (constantly `f`), or
    an identifier naming an all-integer slot (`f` is the slot lookup,
    and `objSlotOk` makes it total); `none` when the objective is
    outside that scope — the optimizers then report `.unsupported`.
    `slotObjFn_eval` and `slotObjFn_total` connect `f` to
    `slotObjective` and to totality. -/
def slotObjFn (names : List String) (doms : List (List Value)) (e : BasicExpr) :
    Option (List Value → Option Int) :=
  match e with
  | .lit (.int i) => some (fun _ => some i)
  | .ident x =>
      if objSlotOk names doms x.name then
        some (fun asg => slotLookup names asg x.name)
      else none
  | _ => none

/-- The sanctioned evaluator agrees with `slotObjective`'s
    expression evaluation on every assignment. -/
theorem slotObjFn_eval {names : List String} {doms : List (List Value)}
    {e : BasicExpr} {f : List Value → Option Int}
    (h : slotObjFn names doms e = some f) (asg : List Value) :
    f asg = slotObjectiveExpr e names asg := by
  cases e with
  | lit l =>
      cases l with
      | int i =>
          have hf : f asg = some i := (congrFun (Option.some.inj h) asg).symm
          show f asg = some i
          exact hf
      | bool b => exact absurd h (by simp [slotObjFn])
      | set s => exact absurd h (by simp [slotObjFn])
  | ident x =>
      simp only [slotObjFn] at h
      split at h
      · next _hok =>
          have hf : f asg = slotLookup names asg x.name :=
            (congrFun (Option.some.inj h) asg).symm
          show f asg = slotLookup names asg x.name
          exact hf
      · next hbad => exact absurd h (by simp)

/-- **Totality of the sanctioned evaluator**: over the complete
    assignments of the searched domains, the objective is always
    defined.  This is what keeps `.unsat` sound (an accepted
    assignment can never be dropped from the pick for having an
    undefined objective). -/
theorem slotObjFn_total {names : List String} {doms : List (List Value)}
    {e : BasicExpr} {f : List Value → Option Int}
    (h : slotObjFn names doms e = some f)
    (hlen : names.length = doms.length) :
    ∀ asg ∈ allAssigns doms, ∃ v, f asg = some v := by
  cases e with
  | lit l =>
      cases l with
      | int i =>
          have hf : ∀ a, f a = some i := fun a => (congrFun (Option.some.inj h) a).symm
          exact fun asg _ => ⟨i, hf asg⟩
      | bool b => exact absurd h (by simp [slotObjFn])
      | set s => exact absurd h (by simp [slotObjFn])
  | ident x =>
      simp only [slotObjFn] at h
      split at h
      · next hok =>
          intro asg hasg
          obtain ⟨v, hv⟩ := slotLookup_total names doms asg x.name hok hlen hasg
          refine ⟨v, ?_⟩
          have hfe : f asg = slotLookup names asg x.name :=
            (congrFun (Option.some.inj h) asg).symm
          rw [hfe]
          exact hv
      · next hbad => exact absurd h (by simp)

/-! ## The result type and the reference optimizer -/

/-- The result of optimization: the winning solution text with its
    objective value, a refutation, or a refusal to run. -/
inductive OptResult where
  /-- An optimal solution was found; the carried text is accepted by
      the verified checker (`optimizeModel_sat_sound` /
      `optimizeModelBb_sat_sound`) and no accepted assignment has a
      better objective (`optimizeModel_optimal` /
      `optimizeModelBb_optimal`). -/
  | optimal (text : String) (value : Int)
  /-- No complete assignment of the slot domains is accepted. -/
  | unsat
  /-- The model is outside the optimized fragment (out-of-fragment
      or capped domains, unsupported predicate, ill-formed,
      satisfaction model, objective outside the slot-level scope). -/
  | unsupported (reason : String)
  deriving Repr, Inhabited

/-- The `(text, value)` pairs of all accepted assignments with
    defined slot-level objectives: enumerate every assignment that
    passes the checker leaf (its prepared twin, over a
    `PreparedModel` built once per enumeration — `solveLeaf`
    pointwise by `solveLeafP_eq`) and pair it with its
    objective. -/
def optPairs (m : Model) (names : List String) (doms : List (List Value))
    (f : List Value → Option Int) : List (String × Int) :=
  (enumerateAll (solveLeafP (prepareModel m) names) doms []).filterMap
    (fun asg => match f asg with
      | some v => some (emitAssignment names asg, v)
      | none => none)

/-- Membership in `optPairs`: a pair is reported exactly when it is
    the emission of an enumerated (leaf-passing, hence
    checker-accepted) assignment with a defined objective. -/
theorem mem_optPairs_iff {m : Model} {names : List String} {doms : List (List Value)}
    {f : List Value → Option Int} {p : String × Int} :
    p ∈ optPairs m names doms f ↔
      ∃ asg, asg ∈ enumerateAll (solveLeaf m names) doms [] ∧
        ∃ v, f asg = some v ∧ p = (emitAssignment names asg, v) := by
  simp only [optPairs, solveLeafP_eq']
  constructor
  · intro hmem
    simp only [List.mem_filterMap] at hmem
    obtain ⟨asg, hasg, hmatch⟩ := hmem
    cases hf : f asg with
    | none => simp only [hf] at hmatch; exact absurd hmatch (by simp)
    | some v =>
        simp only [hf] at hmatch
        exact ⟨asg, hasg, v, hf, (Option.some.inj hmatch).symm⟩
  · rintro ⟨asg, hasg, v, hf, rfl⟩
    simp only [List.mem_filterMap]
    refine ⟨asg, hasg, ?_⟩
    simp only [hf]

/-! ## The streaming best fold (IDEAS 4.5)

`optBody`'s pick materializes the whole `(text, value)` pair list
(`optPairs`) before folding it (`pickBest`): O(n) nodes are kept in
memory at once.  The single-pass fold below, `optBest`, threads the
running best over the *enumerated assignment list* directly and
never materializes the pair list.  It mirrors `pickBest`'s recursion
structurally — ties keep the tail's winner, exactly like `pickBest`
(`optStep` takes the incumbent *from the tail*, so both pick the
same pair) — which is what makes `optBest_eq_pickBest` below a
plain induction.  `optBody` stays the logical reference (it is what
the optimality theorems unfold), and the compiled `optBody` runs
`optBodyFast`, which streams. -/

/-- One fold step: the best of a single candidate `(text, fv)` and
    the tail's incumbent `tailBest`, mirroring `pickBest`'s
    combining step (ties keep `tailBest`). -/
private def optStep (min : Bool) (text : String) (fv : Option Int)
    (tailBest : Option (String × Int)) : Option (String × Int) :=
  match fv with
  | none => tailBest
  | some v =>
      match tailBest with
      | none => some (text, v)
      | some b => some (if selLt min v b.2 then (text, v) else b)

/-- **The streaming best fold**: over the enumerated assignment
    list (no `(text, value)` pair list materialized), one pass,
    keeping the running best — the same pair `pickBest` picks from
    the paired list of the same assignments
    (`optBest_eq_pickBest`). -/
def optBest (min : Bool) (names : List String) (f : List Value → Option Int) :
    List (List Value) → Option (String × Int)
  | [] => none
  | asg :: rest =>
      optStep min (emitAssignment names asg) (f asg) (optBest min names f rest)

/-- The paired list of a suffix of assignments, built in `optPairs`'
    order (the list `optBest` implicitly folds over). -/
private def optPairsOf (names : List String) (f : List Value → Option Int) :
    List (List Value) → List (String × Int)
  | [] => []
  | asg :: rest =>
      match f asg with
      | none => optPairsOf names f rest
      | some v => (emitAssignment names asg, v) :: optPairsOf names f rest

/-- **The bridge**: the streaming fold picks exactly what `pickBest`
    picks from the paired list of the same assignments (structural
    induction, matching the tail-first recursion of both). -/
theorem optBest_eq_pickBest {min : Bool} {names : List String} {f : List Value → Option Int} :
    ∀ (asgs : List (List Value)),
      optBest min names f asgs = pickBest min (optPairsOf names f asgs) := by
  intro asgs
  induction asgs with
  | nil => simp [optBest, optPairsOf, pickBest]
  | cons asg rest ih =>
      simp only [optBest, optPairsOf, optStep, ih]
      cases hf : f asg with
      | none => rfl
      | some v =>
          cases hb : pickBest min (optPairsOf names f rest) with
          | none => rw [pickBest, hb]
          | some b => rw [pickBest, hb]

/-- `optPairsOf` is the same `filterMap` `optPairs` runs, on the
    same assignment list. -/
private theorem optPairsOf_eq_filterMap {names : List String} {f : List Value → Option Int} :
    ∀ (asgs : List (List Value)),
      optPairsOf names f asgs = asgs.filterMap
        (fun asg => match f asg with
          | some v => some (emitAssignment names asg, v)
          | none => none) := by
  intro asgs
  induction asgs with
  | nil => simp [optPairsOf]
  | cons asg rest ih =>
      simp only [optPairsOf, ih]
      cases hf : f asg with
      | none => simp [hf]
      | some v => simp [hf]

/-- At the model level — over the enumerated assignments of a
    prepared model — `optPairsOf` *is* `optPairs`. -/
private theorem optPairsOf_eq_optPairs {m : Model} {names : List String}
    {doms : List (List Value)} {f : List Value → Option Int} :
    optPairsOf names f (enumerateAll (solveLeafP (prepareModel m) names) doms [])
      = optPairs m names doms f := by
  unfold optPairs
  rw [optPairsOf_eq_filterMap]

/-- **The fold equals the pick on the pair list**: the streaming
    `optBest` over the enumerated assignments of `m` and the
    reference pick over `optPairs m names doms f` agree.  This is
    the equality behind the `implemented_by` attribute on `optBody`
    below (and hence on both optimizers' cores). -/
theorem optBest_eq_optPairs {m : Model} {names : List String} {doms : List (List Value)}
    {f : List Value → Option Int} {min : Bool} :
    optBest min names f (enumerateAll (solveLeafP (prepareModel m) names) doms [])
      = pickBest min (optPairs m names doms f) := by
  rw [optBest_eq_pickBest, optPairsOf_eq_optPairs]

/-- **Membership of the streaming pick**: the pair the fold reports
    is one of the reported `optPairs`. -/
theorem optBest_mem {m : Model} {names : List String} {doms : List (List Value)}
    {f : List Value → Option Int} {min : Bool} {p : String × Int}
    (h : optBest min names f (enumerateAll (solveLeafP (prepareModel m) names) doms [])
      = some p) :
    p ∈ optPairs m names doms f := by
  rw [optBest_eq_optPairs] at h
  exact pickBest_mem (optPairs m names doms f) p h

/-- **Extremality of the streaming pick**: the fold's winner is a
    member of `optPairs`, and no accepted assignment achieves a
    better objective — the streaming analogue of
    `pickBest_mem`/`pickBest_minimal` that the optimality theorems
    reduce to. -/
theorem optBest_extremal {m : Model} {names : List String} {doms : List (List Value)}
    {f : List Value → Option Int} {min : Bool} {t : String} {w : Int}
    (h : optBest min names f (enumerateAll (solveLeafP (prepareModel m) names) doms [])
      = some (t, w)) :
    (t, w) ∈ optPairs m names doms f ∧
    ∀ p ∈ optPairs m names doms f, objLe min w p.2 := by
  constructor
  · exact optBest_mem h
  · rw [optBest_eq_optPairs] at h
    intro p hp
    simpa using pickBest_minimal (optPairs m names doms f) (t, w) p hp h

/-- **The reference optimizer's core**: pick the best objective
    among all accepted assignments (the enumeration is the same as
    `enumModel`'s, with the plain satisfaction leaf).  Assumes the
    caller has run the gates and sanctioned the objective
    evaluator.  Its compiled code runs the streaming `optBodyFast`
    (equal by `optBodyFast_eq`). -/
def optBody (m : Model) (names : List String) (doms : List (List Value))
    (f : List Value → Option Int) (min : Bool) : OptResult :=
  match pickBest min (optPairs m names doms f) with
  | none => .unsat
  | some (t, w) => .optimal t w

/-- Same-signature streaming twin of `optBody` (the `implemented_by`
    target): enumerates once and folds the running best, never
    materializing the pair list. -/
def optBodyFast (m : Model) (names : List String) (doms : List (List Value))
    (f : List Value → Option Int) (min : Bool) : OptResult :=
  match optBest min names f (enumerateAll (solveLeafP (prepareModel m) names) doms []) with
  | none => .unsat
  | some (t, w) => .optimal t w

/-- **The bridge for the core**: `optBodyFast` is `optBody`
    pointwise (via `optBest_eq_optPairs`), so the compiled core
    gathers no pair list. -/
theorem optBodyFast_eq {m : Model} {names : List String} {doms : List (List Value)}
    {f : List Value → Option Int} {min : Bool} :
    optBodyFast m names doms f min = optBody m names doms f min := by
  unfold optBodyFast optBody
  rw [optBest_eq_optPairs]

-- IDEAS 4.5: the compiled `optBody` (hence both optimizers' cores)
-- streams the best (`optBodyFast`, equal by `optBodyFast_eq`)
attribute [implemented_by optBodyFast] optBody

/-- **The reference optimizer.**  Gates exactly like `solveModel`
    (`firstUnsupportedFast`, `wellFormedFastB`, `slotsChecked`),
    then: a satisfaction model is refused (use `solveModel`); an
    objective outside the slot-level scope (`slotObjFn`) is refused;
    otherwise enumerate all satisfying assignments and pick the best
    objective. -/
def optimizeModel (m : Model) : OptResult :=
  match firstUnsupportedFast m with
  | some n => .unsupported s!"unsupported predicate: {n}"
  | none =>
      if wellFormedFastB m then
        match slotsChecked m with
        | .error e => .unsupported e
        | .ok slots =>
            match m.solve with
            | .satisfy _ =>
                .unsupported
                  "satisfaction model: no objective (use the satisfaction solver)"
            | .minimize _ e =>
                match slotObjFn (slots.map Prod.fst) (slots.map Prod.snd) e with
                | none =>
                    .unsupported
                      "objective is not an integer literal or an integer-valued search slot"
                | some f =>
                    optBody m (slots.map Prod.fst) (slots.map Prod.snd) f true
            | .maximize _ e =>
                match slotObjFn (slots.map Prod.fst) (slots.map Prod.snd) e with
                | none =>
                    .unsupported
                      "objective is not an integer literal or an integer-valued search slot"
                | some f =>
                    optBody m (slots.map Prod.fst) (slots.map Prod.snd) f false
      else
        .unsupported "model is not well-formed"

/-! ### Leaf conversions

The two directions every master proof starts with: the leaf checks
the emitted text with the verified (fast twin of the) front door. -/

/-- A leaf-passing assignment's emitted text is accepted. -/
private theorem accepted_of_solveLeaf {m : Model} {names : List String}
    {asg : List Value} (h : solveLeaf m names asg = true) :
    checkModelSolution m (emitAssignment names asg) = .accepted := by
  rw [← checkModelSolutionFast_eq]
  simp only [solveLeaf, beq_iff_eq] at h
  exact h

/-- An accepted emitted text passes the leaf. -/
private theorem solveLeaf_of_accepted {m : Model} {names : List String}
    {asg : List Value}
    (h : checkModelSolution m (emitAssignment names asg) = .accepted) :
    solveLeaf m names asg = true := by
  rw [← checkModelSolutionFast_eq] at h
  simp only [solveLeaf, beq_iff_eq]
  exact h

/-- The objective of a minimize model, unfolded to its expression
    evaluation. -/
private theorem slotObjective_min {m : Model} {anns : List Annotation}
    {e : BasicExpr} {names : List String} {asg : List Value}
    (hsolve : m.solve = .minimize anns e) :
    slotObjective m names asg = slotObjectiveExpr e names asg := by
  simp only [slotObjective, hsolve]

/-- The objective of a maximize model, unfolded to its expression
    evaluation. -/
private theorem slotObjective_max {m : Model} {anns : List Annotation}
    {e : BasicExpr} {names : List String} {asg : List Value}
    (hsolve : m.solve = .maximize anns e) :
    slotObjective m names asg = slotObjectiveExpr e names asg := by
  simp only [slotObjective, hsolve]

/-- An `.optimal` verdict of `optBody` picks the reported pair. -/
private theorem optBody_pick_of_optimal {m : Model} {names : List String}
    {doms : List (List Value)} {f : List Value → Option Int} {min : Bool}
    {text : String} {v : Int} (h : optBody m names doms f min = .optimal text v) :
    pickBest min (optPairs m names doms f) = some (text, v) := by
  simp only [optBody] at h
  split at h
  · next hp => exact absurd h (by simp)
  · next t w hp =>
      injection h with ht hv
      subst ht
      subst hv
      exact hp

/-- An `.unsat` verdict of `optBody` empties the pair list. -/
private theorem optBody_nil_of_unsat {m : Model} {names : List String}
    {doms : List (List Value)} {f : List Value → Option Int} {min : Bool}
    (h : optBody m names doms f min = .unsat) :
    optPairs m names doms f = [] := by
  simp only [optBody] at h
  split at h
  · next hp => exact pickBest_eq_nil hp
  · next t w hp => exact absurd h (by simp)

/-! ### The gate dissection of `optimizeModel` -/

/-- The gate structure of `optimizeModel` unfolded: an `.optimal`
    verdict means the gates passed, the solve item is a
    minimize/maximize with a sanctioned objective evaluator, and the
    core returned that verdict. -/
private theorem optimizeModel_gates {m : Model} {text : String} {v : Int}
    (h : optimizeModel m = .optimal text v) :
    (∃ anns e slots f, m.solve = .minimize anns e ∧
        firstUnsupportedFast m = none ∧ wellFormedFastB m = true ∧
        slotsChecked m = .ok slots ∧
        slotObjFn (slots.map Prod.fst) (slots.map Prod.snd) e = some f ∧
        optBody m (slots.map Prod.fst) (slots.map Prod.snd) f true = .optimal text v)
    ∨ (∃ anns e slots f, m.solve = .maximize anns e ∧
        firstUnsupportedFast m = none ∧ wellFormedFastB m = true ∧
        slotsChecked m = .ok slots ∧
        slotObjFn (slots.map Prod.fst) (slots.map Prod.snd) e = some f ∧
        optBody m (slots.map Prod.fst) (slots.map Prod.snd) f false = .optimal text v)
    := by
  cases huns : firstUnsupportedFast m with
  | some n =>
      simp only [optimizeModel, huns] at h
      exact absurd h (by simp)
  | none =>
      cases hwf : wellFormedFastB m with
      | false =>
          simp only [optimizeModel, huns, hwf] at h
          exact absurd h (by simp)
      | true =>
          cases hslots : slotsChecked m with
          | error e =>
              simp only [optimizeModel, huns, hwf, hslots] at h
              exact absurd h (by simp)
          | ok slots =>
              cases hsolve : m.solve with
              | satisfy a =>
                  simp only [optimizeModel, huns, hwf, hslots, hsolve] at h
                  exact absurd h (by simp)
              | minimize a e =>
                  cases hfn : slotObjFn (slots.map Prod.fst) (slots.map Prod.snd) e with
                  | none =>
                      simp only [optimizeModel, huns, hwf, hslots, hsolve, hfn] at h
                      exact absurd h (by simp)
                  | some f =>
                      simp only [optimizeModel, huns, hwf, hslots, hsolve, hfn] at h
                      exact Or.inl ⟨a, e, slots, f, rfl, rfl, rfl, rfl, hfn, h⟩
              | maximize a e =>
                  cases hfn : slotObjFn (slots.map Prod.fst) (slots.map Prod.snd) e with
                  | none =>
                      simp only [optimizeModel, huns, hwf, hslots, hsolve, hfn] at h
                      exact absurd h (by simp)
                  | some f =>
                      simp only [optimizeModel, huns, hwf, hslots, hsolve, hfn] at h
                      exact Or.inr ⟨a, e, slots, f, rfl, rfl, rfl, rfl, hfn, h⟩

/-- Same gate structure for the `.unsat` verdict. -/
private theorem optimizeModel_gates_unsat {m : Model} (h : optimizeModel m = .unsat) :
    (∃ anns e slots f, m.solve = .minimize anns e ∧
        firstUnsupportedFast m = none ∧ wellFormedFastB m = true ∧
        slotsChecked m = .ok slots ∧
        slotObjFn (slots.map Prod.fst) (slots.map Prod.snd) e = some f ∧
        optBody m (slots.map Prod.fst) (slots.map Prod.snd) f true = .unsat)
    ∨ (∃ anns e slots f, m.solve = .maximize anns e ∧
        firstUnsupportedFast m = none ∧ wellFormedFastB m = true ∧
        slotsChecked m = .ok slots ∧
        slotObjFn (slots.map Prod.fst) (slots.map Prod.snd) e = some f ∧
        optBody m (slots.map Prod.fst) (slots.map Prod.snd) f false = .unsat)
    := by
  cases huns : firstUnsupportedFast m with
  | some n =>
      simp only [optimizeModel, huns] at h
      exact absurd h (by simp)
  | none =>
      cases hwf : wellFormedFastB m with
      | false =>
          simp only [optimizeModel, huns, hwf] at h
          exact absurd h (by simp)
      | true =>
          cases hslots : slotsChecked m with
          | error e =>
              simp only [optimizeModel, huns, hwf, hslots] at h
              exact absurd h (by simp)
          | ok slots =>
              cases hsolve : m.solve with
              | satisfy a =>
                  simp only [optimizeModel, huns, hwf, hslots, hsolve] at h
                  exact absurd h (by simp)
              | minimize a e =>
                  cases hfn : slotObjFn (slots.map Prod.fst) (slots.map Prod.snd) e with
                  | none =>
                      simp only [optimizeModel, huns, hwf, hslots, hsolve, hfn] at h
                      exact absurd h (by simp)
                  | some f =>
                      simp only [optimizeModel, huns, hwf, hslots, hsolve, hfn] at h
                      exact Or.inl ⟨a, e, slots, f, rfl, rfl, rfl, rfl, hfn, h⟩
              | maximize a e =>
                  cases hfn : slotObjFn (slots.map Prod.fst) (slots.map Prod.snd) e with
                  | none =>
                      simp only [optimizeModel, huns, hwf, hslots, hsolve, hfn] at h
                      exact absurd h (by simp)
                  | some f =>
                      simp only [optimizeModel, huns, hwf, hslots, hsolve, hfn] at h
                      exact Or.inr ⟨a, e, slots, f, rfl, rfl, rfl, rfl, hfn, h⟩

/-- The gates of a gated model recompute: passing the same gates to
    `optimizeModel` again yields the core's verdict (used by the
    branch-and-bound entry point to reduce its fallback case to the
    reference optimizer's theorems). -/
private theorem optimizeModel_eq_optBody_min {m : Model}
    {anns : List Annotation} {e : BasicExpr} {slots : List (String × List Value)}
    {f : List Value → Option Int}
    (huns : firstUnsupportedFast m = none) (hwf : wellFormedFastB m = true)
    (hslots : slotsChecked m = .ok slots) (hsolve : m.solve = .minimize anns e)
    (hfn : slotObjFn (slots.map Prod.fst) (slots.map Prod.snd) e = some f) :
    optimizeModel m = optBody m (slots.map Prod.fst) (slots.map Prod.snd) f true := by
  simp only [optimizeModel, huns, hwf, hslots, hsolve, hfn, if_true]

/-- The maximize counterpart of `optimizeModel_eq_optBody_min`. -/
private theorem optimizeModel_eq_optBody_max {m : Model}
    {anns : List Annotation} {e : BasicExpr} {slots : List (String × List Value)}
    {f : List Value → Option Int}
    (huns : firstUnsupportedFast m = none) (hwf : wellFormedFastB m = true)
    (hslots : slotsChecked m = .ok slots) (hsolve : m.solve = .maximize anns e)
    (hfn : slotObjFn (slots.map Prod.fst) (slots.map Prod.snd) e = some f) :
    optimizeModel m = optBody m (slots.map Prod.fst) (slots.map Prod.snd) f false := by
  simp only [optimizeModel, huns, hwf, hslots, hsolve, hfn, if_true]

/-! ### The master theorems of the reference optimizer -/

/-- **SAT soundness**: an optimal solution text returned by
    `optimizeModel` is accepted by the verified front door (so by
    `checkModelSolution_correct` the model is well formed and the
    parsed entries' completed store satisfies the declarative
    semantics). -/
theorem optimizeModel_sat_sound {m : Model} {text : String} {v : Int}
    (h : optimizeModel m = .optimal text v) :
    checkModelSolution m text = .accepted := by
  rcases optimizeModel_gates h with
    ⟨anns, e, slots, f, _, _, _, _, _, hbody⟩ |
    ⟨anns, e, slots, f, _, _, _, _, _, hbody⟩
  · have hpick := optBody_pick_of_optimal hbody
    obtain ⟨asg, hasg, v', hf, hpair⟩ :=
      mem_optPairs_iff (p := (text, v)).mp (pickBest_mem _ _ hpick)
    have hleaf := (enumerateAll_mem_iff_root _ _ asg).mp hasg
    obtain ⟨_, hleaf'⟩ := hleaf
    injection hpair with htxt hval
    subst htxt
    subst hval
    exact accepted_of_solveLeaf hleaf'
  · have hpick := optBody_pick_of_optimal hbody
    obtain ⟨asg, hasg, v', hf, hpair⟩ :=
      mem_optPairs_iff (p := (text, v)).mp (pickBest_mem _ _ hpick)
    have hleaf := (enumerateAll_mem_iff_root _ _ asg).mp hasg
    obtain ⟨_, hleaf'⟩ := hleaf
    injection hpair with htxt hval
    subst htxt
    subst hval
    exact accepted_of_solveLeaf hleaf'

/-- **Optimality**: if `optimizeModel` returns `.optimal text v`, then
    for every complete assignment of the model's slot domains whose
    emitted text the checker accepts and whose slot-level objective
    is `v'`, the returned value is at least as good (`v ≤ v'` for
    minimize, `v' ≤ v` for maximize). -/
theorem optimizeModel_optimal {m : Model} {text : String} {v : Int}
    (h : optimizeModel m = .optimal text v) {asg : List Value} {v' : Int}
    (hmem : asg ∈ allAssigns (slotDomains m))
    (hacc : checkModelSolution m (emitAssignment (slotNames m) asg) = .accepted)
    (hobj : slotObjective m (slotNames m) asg = some v') :
    objLeOf m v v' := by
  rcases optimizeModel_gates h with
    ⟨anns, e, slots, f, hsolve, huns, hwf, hslots, hfn, hbody⟩ |
    ⟨anns, e, slots, f, hsolve, huns, hwf, hslots, hfn, hbody⟩
  · have hslots' : modelSlots m = some slots := modelSlots_eq.mpr hslots
    obtain ⟨hnames, hdoms⟩ := slotNames_domains_of_modelSlots hslots'
    rw [hnames] at hacc hobj
    rw [slotObjective_min hsolve] at hobj
    have hfval : f asg = some v' := by
      rw [slotObjFn_eval hfn asg]; exact hobj
    have hleaf : solveLeaf m (slots.map Prod.fst) asg = true :=
      solveLeaf_of_accepted hacc
    have hmem' : asg ∈ allAssigns (slots.map Prod.snd) := by
      rw [← hdoms]; exact hmem
    have hin : asg ∈ enumerateAll (solveLeaf m (slots.map Prod.fst))
        (slots.map Prod.snd) [] :=
      (enumerateAll_mem_iff_root _ _ asg).mpr ⟨hmem', hleaf⟩
    have hpair : (emitAssignment (slots.map Prod.fst) asg, v') ∈
        optPairs m (slots.map Prod.fst) (slots.map Prod.snd) f :=
      mem_optPairs_iff.mpr ⟨asg, hin, v', hfval, rfl⟩
    have hpick := optBody_pick_of_optimal hbody
    have hle := pickBest_minimal (optPairs m (slots.map Prod.fst) (slots.map Prod.snd) f)
      (text, v) (emitAssignment (slots.map Prod.fst) asg, v') hpair hpick
    simp only [objLeOf, hsolve]
    simpa only [objLe] using hle
  · have hslots' : modelSlots m = some slots := modelSlots_eq.mpr hslots
    obtain ⟨hnames, hdoms⟩ := slotNames_domains_of_modelSlots hslots'
    rw [hnames] at hacc hobj
    rw [slotObjective_max hsolve] at hobj
    have hfval : f asg = some v' := by
      rw [slotObjFn_eval hfn asg]; exact hobj
    have hleaf : solveLeaf m (slots.map Prod.fst) asg = true :=
      solveLeaf_of_accepted hacc
    have hmem' : asg ∈ allAssigns (slots.map Prod.snd) := by
      rw [← hdoms]; exact hmem
    have hin : asg ∈ enumerateAll (solveLeaf m (slots.map Prod.fst))
        (slots.map Prod.snd) [] :=
      (enumerateAll_mem_iff_root _ _ asg).mpr ⟨hmem', hleaf⟩
    have hpair : (emitAssignment (slots.map Prod.fst) asg, v') ∈
        optPairs m (slots.map Prod.fst) (slots.map Prod.snd) f :=
      mem_optPairs_iff.mpr ⟨asg, hin, v', hfval, rfl⟩
    have hpick := optBody_pick_of_optimal hbody
    have hle := pickBest_minimal (optPairs m (slots.map Prod.fst) (slots.map Prod.snd) f)
      (text, v) (emitAssignment (slots.map Prod.fst) asg, v') hpair hpick
    simp only [objLeOf, hsolve]
    simpa only [objLe] using hle

/-- **UNSAT soundness**: if `optimizeModel` returns `.unsat`, then no
    complete assignment of the model's slot domains yields an accepted
    solution. -/
theorem optimizeModel_unsat {m : Model} (h : optimizeModel m = .unsat)
    {asg : List Value} (hmem : asg ∈ allAssigns (slotDomains m)) :
    checkModelSolution m (emitAssignment (slotNames m) asg) ≠ .accepted := by
  intro hacc
  rcases optimizeModel_gates_unsat h with
    ⟨anns, e, slots, f, hsolve, huns, hwf, hslots, hfn, hbody⟩ |
    ⟨anns, e, slots, f, hsolve, huns, hwf, hslots, hfn, hbody⟩
  · exfalso
    have hnil := optBody_nil_of_unsat hbody
    have hslots' : modelSlots m = some slots := modelSlots_eq.mpr hslots
    obtain ⟨hnames, hdoms⟩ := slotNames_domains_of_modelSlots hslots'
    rw [hnames] at hacc
    have hleaf : solveLeaf m (slots.map Prod.fst) asg = true :=
      solveLeaf_of_accepted hacc
    have hmem' : asg ∈ allAssigns (slots.map Prod.snd) := by
      rw [← hdoms]; exact hmem
    have hin : asg ∈ enumerateAll (solveLeaf m (slots.map Prod.fst))
        (slots.map Prod.snd) [] :=
      (enumerateAll_mem_iff_root _ _ asg).mpr ⟨hmem', hleaf⟩
    have hlen : (slots.map Prod.fst).length = (slots.map Prod.snd).length := by
      simp only [List.length_map]
    obtain ⟨w, hw⟩ := slotObjFn_total hfn hlen asg hmem'
    have hpair : (emitAssignment (slots.map Prod.fst) asg, w) ∈
        optPairs m (slots.map Prod.fst) (slots.map Prod.snd) f :=
      mem_optPairs_iff.mpr ⟨asg, hin, w, hw, rfl⟩
    rw [hnil] at hpair
    exact absurd hpair (by simp)
  · exfalso
    have hnil := optBody_nil_of_unsat hbody
    have hslots' : modelSlots m = some slots := modelSlots_eq.mpr hslots
    obtain ⟨hnames, hdoms⟩ := slotNames_domains_of_modelSlots hslots'
    rw [hnames] at hacc
    have hleaf : solveLeaf m (slots.map Prod.fst) asg = true :=
      solveLeaf_of_accepted hacc
    have hmem' : asg ∈ allAssigns (slots.map Prod.snd) := by
      rw [← hdoms]; exact hmem
    have hin : asg ∈ enumerateAll (solveLeaf m (slots.map Prod.fst))
        (slots.map Prod.snd) [] :=
      (enumerateAll_mem_iff_root _ _ asg).mpr ⟨hmem', hleaf⟩
    have hlen : (slots.map Prod.fst).length = (slots.map Prod.snd).length := by
      simp only [List.length_map]
    obtain ⟨w, hw⟩ := slotObjFn_total hfn hlen asg hmem'
    have hpair : (emitAssignment (slots.map Prod.fst) asg, w) ∈
        optPairs m (slots.map Prod.fst) (slots.map Prod.snd) f :=
      mem_optPairs_iff.mpr ⟨asg, hin, w, hw, rfl⟩
    rw [hnil] at hpair
    exact absurd hpair (by simp)

/-- **Value pairing**: the value returned with an optimal text is
    the slot-level objective of that text's assignment. -/
theorem optimizeModel_value {m : Model} {text : String} {v : Int}
    (h : optimizeModel m = .optimal text v) :
    ∃ asg, asg ∈ allAssigns (slotDomains m) ∧
      emitAssignment (slotNames m) asg = text ∧
      slotObjective m (slotNames m) asg = some v ∧
      checkModelSolution m text = .accepted := by
  rcases optimizeModel_gates h with
    ⟨anns, e, slots, f, hsolve, _, _, hslots, hfn, hbody⟩ |
    ⟨anns, e, slots, f, hsolve, _, _, hslots, hfn, hbody⟩
  · have hpick := optBody_pick_of_optimal hbody
    obtain ⟨asg, hasg, v', hf, hpair⟩ :=
      mem_optPairs_iff (p := (text, v)).mp (pickBest_mem _ _ hpick)
    have hleaf := (enumerateAll_mem_iff_root _ _ asg).mp hasg
    obtain ⟨hmem, hleaf'⟩ := hleaf
    have hslots' : modelSlots m = some slots := modelSlots_eq.mpr hslots
    obtain ⟨hnames, hdoms⟩ := slotNames_domains_of_modelSlots hslots'
    injection hpair with htxt hval
    subst htxt
    subst hval
    refine ⟨asg, ?_, ?_, ?_, accepted_of_solveLeaf hleaf'⟩
    · rw [hdoms]; exact hmem
    · rw [hnames]
    · rw [hnames]
      simp only [slotObjective, hsolve]
      rw [← slotObjFn_eval hfn asg]
      exact hf
  · have hpick := optBody_pick_of_optimal hbody
    obtain ⟨asg, hasg, v', hf, hpair⟩ :=
      mem_optPairs_iff (p := (text, v)).mp (pickBest_mem _ _ hpick)
    have hleaf := (enumerateAll_mem_iff_root _ _ asg).mp hasg
    obtain ⟨hmem, hleaf'⟩ := hleaf
    have hslots' : modelSlots m = some slots := modelSlots_eq.mpr hslots
    obtain ⟨hnames, hdoms⟩ := slotNames_domains_of_modelSlots hslots'
    injection hpair with htxt hval
    subst htxt
    subst hval
    refine ⟨asg, ?_, ?_, ?_, accepted_of_solveLeaf hleaf'⟩
    · rw [hdoms]; exact hmem
    · rw [hnames]
    · rw [hnames]
      simp only [slotObjective, hsolve]
      rw [← slotObjFn_eval hfn asg]
      exact hf

/-! ## The improving-bound refinement (branch and bound)

The B&B mechanism of PLAN 6.7.  `objBetter` is the improving bound:
with no incumbent everything with a defined objective passes; with an
incumbent, only strictly better objectives pass.  `bbLeaf` conjoins
it with the checker's leaf.  `optRefine` runs the rounds: the *first*
round searches with the plain satisfaction leaf (so an empty first
round is a plain-unsatisfiability certificate, keeping `.unsat`
sound even if objectives were undefined on some assignments); each
later round searches with the incumbent-strengthened leaf and either
improves the incumbent or — on `none` — certifies that nothing
strictly better exists (`search_none`).  Fuel bounds the rounds; at
exhaustion `optBbCore` falls back to the reference optimizer's pick. -/

/-- The improving bound: with `bound = none`, every assignment with a
    defined objective passes; with `bound = some b`, only objectives
    strictly better than `b` (in the direction `min`) pass. -/
def objBetter (f : List Value → Option Int) (min : Bool) (bound : Option Int)
    (asg : List Value) : Bool :=
  match f asg with
  | none => false
  | some v =>
      match bound with
      | none => true
      | some b => selLt min v b

/-- A round's leaf: the checker's leaf (its prepared twin, over a
    `PreparedModel` built once per optimization — `solveLeaf`
    pointwise by `solveLeafP_eq`) *and* the improving bound. -/
def bbLeaf (p : PreparedModel) (names : List String) (f : List Value → Option Int)
    (min : Bool) (bound : Option Int) : List Value → Bool :=
  fun asg => solveLeafP p names asg && objBetter f min bound asg

/-- The outcome of the bounded round loop. -/
inductive OptRefineResult where
  /-- A round found no improvement over the incumbent: the incumbent
      is optimal among accepted assignments with defined objectives
      (`optRefine_done_optimal`). -/
  | done (text : String) (value : Int)
  /-- The first round found no accepted assignment at all. -/
  | noneFound
  /-- The fuel ran out; the caller falls back to the reference
      optimizer's full enumeration. -/
  | exhausted

/-- The round loop.  `fuel` bounds the number of rounds; `inc` is the
    incumbent (text with its objective).  With fuel `leavesProduct
    doms + 1` — one more than the number of complete assignments —
    the loop cannot exhaust while solutions exist: every round after
    the first strictly improves the incumbent, incumbents come from
    distinct assignments, and the chain is therefore shorter than the
    assignment count.  The checker leaf is the prepared twin of
    `solveLeaf` over a `PreparedModel` bound once per optimization. -/
def optRefine (f : List Value → Option Int) (min : Bool) (m : Model)
    (names : List String) (doms : List (List Value)) :
    Nat → Option (String × Int) → OptRefineResult
  | 0, _ => .exhausted
  | fuel + 1, inc =>
      match inc with
      | none =>
          match search (solveLeafP (prepareModel m) names) doms [] with
          | none => .noneFound
          | some asg =>
              match f asg with
              | none => .exhausted
              | some v =>
                  optRefine f min m names doms fuel (some (emitAssignment names asg, v))
      | some (t0, w0) =>
          match search (bbLeaf (prepareModel m) names f min (some w0)) doms [] with
          | none => .done t0 w0
          | some asg =>
              match f asg with
              | none => .exhausted
              | some v =>
                  optRefine f min m names doms fuel (some (emitAssignment names asg, v))

/-- **Soundness of a `.done` verdict**: the incumbent it certifies is
    the emission of a complete assignment that passes the checker's
    leaf with that objective.  The incumbent-invariant hypothesis is
    vacuous at the entry point (`inc = none`). -/
theorem optRefine_done_sound {f : List Value → Option Int} {min : Bool} {m : Model}
    {names : List String} {doms : List (List Value)} :
    ∀ (fuel : Nat) (inc : Option (String × Int)) (t : String) (w : Int),
      (∀ t0 w0, inc = some (t0, w0) →
        checkModelSolution m t0 = .accepted ∧
        ∃ asg, asg ∈ allAssigns doms ∧ emitAssignment names asg = t0 ∧
          f asg = some w0) →
      optRefine f min m names doms fuel inc = .done t w →
      checkModelSolution m t = .accepted ∧
      ∃ asg, asg ∈ allAssigns doms ∧ emitAssignment names asg = t ∧
        f asg = some w := by
  intro fuel
  induction fuel with
  | zero =>
      intro inc t w _ h
      simp only [optRefine] at h
      exact absurd h (by simp)
  | succ fuel ih =>
      intro inc t w hinc h
      simp only [optRefine] at h
      rw [solveLeafP_eq' m names] at h
      match hinc2 : inc with
      | none =>
        cases hsearch : search (solveLeaf m names) doms [] with
        | none => simp only [hsearch] at h; exact absurd h (by simp)
        | some asg =>
            simp only [hsearch] at h
            cases hf : f asg with
            | none => simp only [hf] at h; exact absurd h (by simp)
            | some v =>
                simp only [hf] at h
                have hleaf := search_some (solveLeaf m names) doms [] asg hsearch
                obtain ⟨a, ha, hrfl, hleaf'⟩ := hleaf
                have hasg : asg = a := by
                  simpa [List.nil_append] using hrfl
                subst hasg
                simp only [List.nil_append] at hleaf'
                have haccepted := accepted_of_solveLeaf hleaf'
                refine ih (some (emitAssignment names asg, v)) t w ?_ h
                intro t0 w0 hEq
                have hsplit : t0 = emitAssignment names asg ∧ w0 = v := by
                  have hp := Option.some.inj hEq
                  simp only [Prod.mk.injEq] at hp
                  exact ⟨hp.1.symm, hp.2.symm⟩
                rw [hsplit.1, hsplit.2]
                exact ⟨haccepted, asg, ha, rfl, hf⟩
      | some (t0, w0) =>
        cases hsearch : search (bbLeaf (prepareModel m) names f min (some w0)) doms [] with
        | none =>
            simp only [hsearch] at h
            injection h with h1 h2
            exact hinc _ _ (by simp only [h1, h2])
        | some asg =>
            simp only [hsearch] at h
            cases hf : f asg with
            | none => simp only [hf] at h; exact absurd h (by simp)
            | some v =>
                simp only [hf] at h
                have hleaf := search_some (bbLeaf (prepareModel m) names f min (some w0))
                  doms [] asg hsearch
                obtain ⟨a, ha, hrfl, hleaf'⟩ := hleaf
                have hasg : asg = a := by
                  simpa [List.nil_append] using hrfl
                subst hasg
                simp only [List.nil_append] at hleaf'
                simp only [bbLeaf, Bool.and_eq_true] at hleaf'
                obtain ⟨hleaf1, _⟩ := hleaf'
                rw [solveLeafP_eq] at hleaf1
                have haccepted := accepted_of_solveLeaf hleaf1
                refine ih (some (emitAssignment names asg, v)) t w ?_ h
                intro t1 w1 hEq
                have hsplit : t1 = emitAssignment names asg ∧ w1 = v := by
                  have hp := Option.some.inj hEq
                  simp only [Prod.mk.injEq] at hp
                  exact ⟨hp.1.symm, hp.2.symm⟩
                rw [hsplit.1, hsplit.2]
                exact ⟨haccepted, asg, ha, rfl, hf⟩

/-- **Optimality of a `.done` verdict**: if the loop certifies the
    incumbent `t` with value `w`, then every complete assignment that
    passes the checker's leaf with a defined objective is no better
    than it. -/
theorem optRefine_done_optimal {f : List Value → Option Int} {min : Bool}
    {m : Model} {names : List String} {doms : List (List Value)} :
    ∀ (fuel : Nat) (inc : Option (String × Int)) (t : String) (w : Int)
      (v' : Int) (asg : List Value),
      optRefine f min m names doms fuel inc = .done t w →
      asg ∈ allAssigns doms → solveLeaf m names asg = true →
      f asg = some v' →
      objLe min w v' := by
  intro fuel
  induction fuel with
  | zero =>
      intro inc t w v' asg h
      simp only [optRefine] at h
      exact absurd h (by simp)
  | succ fuel ih =>
      intro inc t w v' asg h hmem hleaf hfval
      simp only [optRefine] at h
      rw [solveLeafP_eq' m names] at h
      match hinc : inc with
      | none =>
        cases hsearch : search (solveLeaf m names) doms [] with
        | none => simp only [hsearch] at h; exact absurd h (by simp)
        | some a =>
            simp only [hsearch] at h
            cases hfa : f a with
            | none => simp only [hfa] at h; exact absurd h (by simp)
            | some w2 =>
                simp only [hfa] at h
                exact ih (some (emitAssignment names a, w2)) t w v' asg h hmem hleaf hfval
      | some p =>
        obtain ⟨t0, w0⟩ := p
        cases hsearch : search (bbLeaf (prepareModel m) names f min (some w0)) doms [] with
        | none =>
            simp only [hsearch] at h
            injection h with h1 h2
            have hnone := search_none
              (bbLeaf (prepareModel m) names f min (some w0)) doms [] hsearch
            have hbb : bbLeaf (prepareModel m) names f min (some w0) asg = false :=
              hnone asg hmem
            simp only [bbLeaf, solveLeafP_eq', hleaf, Bool.true_and] at hbb
            simp only [objBetter, hfval] at hbb
            exact h2 ▸ selLt_false_objLe hbb
        | some a =>
            simp only [hsearch] at h
            cases hfa : f a with
            | none => simp only [hfa] at h; exact absurd h (by simp)
            | some w2 =>
                simp only [hfa] at h
                exact ih (some (emitAssignment names a, w2)) t w v' asg h hmem hleaf hfval

/-- An incumbent round can never report `.noneFound`: the verdict is
    produced only by the first round (the plain satisfaction search). -/
theorem optRefine_some_ne_noneFound {f : List Value → Option Int} {min : Bool}
    {m : Model} {names : List String} {doms : List (List Value)} :
    ∀ (fuel : Nat) (t0 : String) (w0 : Int),
      optRefine f min m names doms fuel (some (t0, w0)) ≠ .noneFound := by
  intro fuel
  induction fuel with
  | zero =>
      intro t0 w0 h
      simp only [optRefine] at h
      exact absurd h (by simp)
  | succ fuel ih =>
      intro t0 w0 h
      simp only [optRefine] at h
      cases hsearch : search (bbLeaf (prepareModel m) names f min (some w0)) doms [] with
      | none => simp only [hsearch] at h; exact absurd h (by simp)
      | some a =>
          simp only [hsearch] at h
          cases hf : f a with
          | none => simp only [hf] at h; exact absurd h (by simp)
          | some v =>
              simp only [hf] at h
              exact ih (emitAssignment names a) v h

/-- **A `.noneFound` verdict is a plain unsatisfiability
    certificate**: the first round searched with the satisfaction
    leaf alone and found nothing, so every complete assignment fails
    the leaf. -/
theorem optRefine_noneFound {f : List Value → Option Int} {min : Bool} {m : Model}
    {names : List String} {doms : List (List Value)} :
    ∀ (fuel : Nat) (inc : Option (String × Int)),
      optRefine f min m names doms fuel inc = .noneFound →
      ∀ asg ∈ allAssigns doms, solveLeaf m names asg = false := by
  intro fuel
  induction fuel with
  | zero =>
      intro inc h
      simp only [optRefine] at h
      exact absurd h (by simp)
  | succ fuel _ih =>
      intro inc h asg hmem
      match hinc : inc with
      | none =>
        simp only [optRefine] at h
        rw [solveLeafP_eq' m names] at h
        cases hsearch : search (solveLeaf m names) doms [] with
        | none =>
            simp only [hsearch] at h
            have hnone := search_none (solveLeaf m names) doms [] hsearch
            have hleaf := hnone asg hmem
            simpa [List.nil_append] using hleaf
        | some a =>
            simp only [hsearch] at h
            cases hfa : f a with
            | none => simp only [hfa] at h; exact absurd h (by simp)
            | some w2 =>
                simp only [hfa] at h
                exact absurd h (optRefine_some_ne_noneFound fuel
                  (emitAssignment names a) w2)
      | some (t0, w0) =>
        simp only [optRefine] at h
        exact absurd h (optRefine_some_ne_noneFound (fuel + 1) t0 w0)


/-- The branch-and-bound core: run the round loop with fuel `one more
    than the number of complete assignments` and map its verdicts,
    falling back to the reference optimizer's pick at fuel
    exhaustion. -/
def optBbCore (m : Model) (names : List String) (doms : List (List Value))
    (f : List Value → Option Int) (min : Bool) : OptResult :=
  match optRefine f min m names doms (leavesProduct doms + 1) none with
  | .done t w => .optimal t w
  | .noneFound => .unsat
  | .exhausted => optBody m names doms f min

/-- The `.optimal` verdicts of the B&B core arise either from a
    `.done` incumbent or from the fallback pick. -/
private theorem optBbCore_optimal_dissect {m : Model} {names : List String}
    {doms : List (List Value)} {f : List Value → Option Int} {min : Bool}
    {text : String} {v : Int} (h : optBbCore m names doms f min = .optimal text v) :
    (∃ t w, optRefine f min m names doms (leavesProduct doms + 1) none = .done t w ∧
        t = text ∧ w = v) ∨
    optBody m names doms f min = .optimal text v := by
  simp only [optBbCore] at h
  split at h
  · next t w hr =>
      injection h with ht hv
      exact Or.inl ⟨t, w, hr, ht, hv⟩
  · next hr => exact absurd h (by simp)
  · next hr => exact Or.inr h

/-- The `.unsat` verdicts of the B&B core arise either from the
    first round's plain-unsatisfiability certificate or from the
    fallback pick. -/
private theorem optBbCore_unsat_dissect {m : Model} {names : List String}
    {doms : List (List Value)} {f : List Value → Option Int} {min : Bool}
    (h : optBbCore m names doms f min = .unsat) :
    optRefine f min m names doms (leavesProduct doms + 1) none = .noneFound ∨
    optBody m names doms f min = .unsat := by
  simp only [optBbCore] at h
  split at h
  · next t w hr => exact absurd h (by simp)
  · next hr => exact Or.inl hr
  · next hr => exact Or.inr h

/-- **The branch-and-bound optimizer** (PLAN 6.7's mechanism, second
    entry point): the same gates and objective scope as
    `optimizeModel`, then rounds of `search` with the
    incumbent-strengthened leaf; on fuel exhaustion it falls back to
    the reference optimizer's full-enumeration pick. -/
def optimizeModelBb (m : Model) : OptResult :=
  match firstUnsupportedFast m with
  | some n => .unsupported s!"unsupported predicate: {n}"
  | none =>
      if wellFormedFastB m then
        match slotsChecked m with
        | .error e => .unsupported e
        | .ok slots =>
            match m.solve with
            | .satisfy _ =>
                .unsupported
                  "satisfaction model: no objective (use the satisfaction solver)"
            | .minimize _ e =>
                match slotObjFn (slots.map Prod.fst) (slots.map Prod.snd) e with
                | none =>
                    .unsupported
                      "objective is not an integer literal or an integer-valued search slot"
                | some f =>
                    optBbCore m (slots.map Prod.fst) (slots.map Prod.snd) f true
            | .maximize _ e =>
                match slotObjFn (slots.map Prod.fst) (slots.map Prod.snd) e with
                | none =>
                    .unsupported
                      "objective is not an integer literal or an integer-valued search slot"
                | some f =>
                    optBbCore m (slots.map Prod.fst) (slots.map Prod.snd) f false
      else
        .unsupported "model is not well-formed"

/-- The gate structure of `optimizeModelBb` unfolded: an `.optimal`
    verdict means the gates passed, the solve item is a
    minimize/maximize with a sanctioned objective evaluator, and the
    B&B core returned that verdict. -/
private theorem optimizeModelBb_gates {m : Model} {text : String} {v : Int}
    (h : optimizeModelBb m = .optimal text v) :
    (∃ anns e slots f, m.solve = .minimize anns e ∧
        firstUnsupportedFast m = none ∧ wellFormedFastB m = true ∧
        slotsChecked m = .ok slots ∧
        slotObjFn (slots.map Prod.fst) (slots.map Prod.snd) e = some f ∧
        optBbCore m (slots.map Prod.fst) (slots.map Prod.snd) f true = .optimal text v)
    ∨ (∃ anns e slots f, m.solve = .maximize anns e ∧
        firstUnsupportedFast m = none ∧ wellFormedFastB m = true ∧
        slotsChecked m = .ok slots ∧
        slotObjFn (slots.map Prod.fst) (slots.map Prod.snd) e = some f ∧
        optBbCore m (slots.map Prod.fst) (slots.map Prod.snd) f false = .optimal text v)
    := by
  cases huns : firstUnsupportedFast m with
  | some n =>
      simp only [optimizeModelBb, huns] at h
      exact absurd h (by simp)
  | none =>
      cases hwf : wellFormedFastB m with
      | false =>
          simp only [optimizeModelBb, huns, hwf] at h
          exact absurd h (by simp)
      | true =>
          cases hslots : slotsChecked m with
          | error e =>
              simp only [optimizeModelBb, huns, hwf, hslots] at h
              exact absurd h (by simp)
          | ok slots =>
              cases hsolve : m.solve with
              | satisfy a =>
                  simp only [optimizeModelBb, huns, hwf, hslots, hsolve] at h
                  exact absurd h (by simp)
              | minimize a e =>
                  cases hfn : slotObjFn (slots.map Prod.fst) (slots.map Prod.snd) e with
                  | none =>
                      simp only [optimizeModelBb, huns, hwf, hslots, hsolve, hfn] at h
                      exact absurd h (by simp)
                  | some f =>
                      simp only [optimizeModelBb, huns, hwf, hslots, hsolve, hfn] at h
                      exact Or.inl ⟨a, e, slots, f, rfl, rfl, rfl, rfl, hfn, h⟩
              | maximize a e =>
                  cases hfn : slotObjFn (slots.map Prod.fst) (slots.map Prod.snd) e with
                  | none =>
                      simp only [optimizeModelBb, huns, hwf, hslots, hsolve, hfn] at h
                      exact absurd h (by simp)
                  | some f =>
                      simp only [optimizeModelBb, huns, hwf, hslots, hsolve, hfn] at h
                      exact Or.inr ⟨a, e, slots, f, rfl, rfl, rfl, rfl, hfn, h⟩

/-- Same gate structure for the `.unsat` verdict. -/
private theorem optimizeModelBb_gates_unsat {m : Model} (h : optimizeModelBb m = .unsat) :
    (∃ anns e slots f, m.solve = .minimize anns e ∧
        firstUnsupportedFast m = none ∧ wellFormedFastB m = true ∧
        slotsChecked m = .ok slots ∧
        slotObjFn (slots.map Prod.fst) (slots.map Prod.snd) e = some f ∧
        optBbCore m (slots.map Prod.fst) (slots.map Prod.snd) f true = .unsat)
    ∨ (∃ anns e slots f, m.solve = .maximize anns e ∧
        firstUnsupportedFast m = none ∧ wellFormedFastB m = true ∧
        slotsChecked m = .ok slots ∧
        slotObjFn (slots.map Prod.fst) (slots.map Prod.snd) e = some f ∧
        optBbCore m (slots.map Prod.fst) (slots.map Prod.snd) f false = .unsat)
    := by
  cases huns : firstUnsupportedFast m with
  | some n =>
      simp only [optimizeModelBb, huns] at h
      exact absurd h (by simp)
  | none =>
      cases hwf : wellFormedFastB m with
      | false =>
          simp only [optimizeModelBb, huns, hwf] at h
          exact absurd h (by simp)
      | true =>
          cases hslots : slotsChecked m with
          | error e =>
              simp only [optimizeModelBb, huns, hwf, hslots] at h
              exact absurd h (by simp)
          | ok slots =>
              cases hsolve : m.solve with
              | satisfy a =>
                  simp only [optimizeModelBb, huns, hwf, hslots, hsolve] at h
                  exact absurd h (by simp)
              | minimize a e =>
                  cases hfn : slotObjFn (slots.map Prod.fst) (slots.map Prod.snd) e with
                  | none =>
                      simp only [optimizeModelBb, huns, hwf, hslots, hsolve, hfn] at h
                      exact absurd h (by simp)
                  | some f =>
                      simp only [optimizeModelBb, huns, hwf, hslots, hsolve, hfn] at h
                      exact Or.inl ⟨a, e, slots, f, rfl, rfl, rfl, rfl, hfn, h⟩
              | maximize a e =>
                  cases hfn : slotObjFn (slots.map Prod.fst) (slots.map Prod.snd) e with
                  | none =>
                      simp only [optimizeModelBb, huns, hwf, hslots, hsolve, hfn] at h
                      exact absurd h (by simp)
                  | some f =>
                      simp only [optimizeModelBb, huns, hwf, hslots, hsolve, hfn] at h
                      exact Or.inr ⟨a, e, slots, f, rfl, rfl, rfl, rfl, hfn, h⟩

/-! ### The master theorems of the branch-and-bound optimizer -/

/-- **SAT soundness of `optimizeModelBb`**: an optimal solution text
    returned by the branch-and-bound optimizer is accepted by the
    verified front door.  (A `.done` incumbent passed a round's leaf,
    which contains the checker's leaf; the fallback case is the
    reference optimizer's `optimizeModel_sat_sound`.) -/
theorem optimizeModelBb_sat_sound {m : Model} {text : String} {v : Int}
    (h : optimizeModelBb m = .optimal text v) :
    checkModelSolution m text = .accepted := by
  rcases optimizeModelBb_gates h with
    ⟨anns, e, slots, f, hsolve, huns, hwf, hslots, hfn, hcore⟩ |
    ⟨anns, e, slots, f, hsolve, huns, hwf, hslots, hfn, hcore⟩
  · rcases optBbCore_optimal_dissect hcore with ⟨t, w, hr, rfl, rfl⟩ | hbody
    · obtain ⟨hacc, _⟩ :=
        optRefine_done_sound (f := f) (min := true) (m := m)
          (names := slots.map Prod.fst) (doms := slots.map Prod.snd)
          (leavesProduct (slots.map Prod.snd) + 1) none _ _
          (by rintro t0 w0 ⟨⟩) hr
      exact hacc
    · have hopt : optimizeModel m = .optimal text v :=
        (optimizeModel_eq_optBody_min huns hwf hslots hsolve hfn).trans hbody
      exact optimizeModel_sat_sound hopt
  · rcases optBbCore_optimal_dissect hcore with ⟨t, w, hr, rfl, rfl⟩ | hbody
    · obtain ⟨hacc, _⟩ :=
        optRefine_done_sound (f := f) (min := false) (m := m)
          (names := slots.map Prod.fst) (doms := slots.map Prod.snd)
          (leavesProduct (slots.map Prod.snd) + 1) none _ _
          (by rintro t0 w0 ⟨⟩) hr
      exact hacc
    · have hopt : optimizeModel m = .optimal text v :=
        (optimizeModel_eq_optBody_max huns hwf hslots hsolve hfn).trans hbody
      exact optimizeModel_sat_sound hopt

/-- **Optimality of `optimizeModelBb`** (same statement as
    `optimizeModel_optimal`): if it returns `.optimal text v`, then
    for every complete assignment of the model's slot domains whose
    emitted text the checker accepts and whose slot-level objective
    is `v'`, the returned value is at least as good.  (A `.done`
    verdict is certified by the final round: `search_none` shows no
    accepted assignment with a defined objective is strictly better
    than the incumbent; the fallback case is the reference
    optimizer's theorem.) -/
theorem optimizeModelBb_optimal {m : Model} {text : String} {v : Int}
    (h : optimizeModelBb m = .optimal text v) {asg : List Value} {v' : Int}
    (hmem : asg ∈ allAssigns (slotDomains m))
    (hacc : checkModelSolution m (emitAssignment (slotNames m) asg) = .accepted)
    (hobj : slotObjective m (slotNames m) asg = some v') :
    objLeOf m v v' := by
  rcases optimizeModelBb_gates h with
    ⟨anns, e, slots, f, hsolve, huns, hwf, hslots, hfn, hcore⟩ |
    ⟨anns, e, slots, f, hsolve, huns, hwf, hslots, hfn, hcore⟩
  · have hslots' : modelSlots m = some slots := modelSlots_eq.mpr hslots
    obtain ⟨hnames, hdoms⟩ := slotNames_domains_of_modelSlots hslots'
    have hacc' : checkModelSolution m (emitAssignment (slots.map Prod.fst) asg)
        = .accepted := by
      rw [← hnames]; exact hacc
    have hobj' : f asg = some v' := by
      rw [slotObjFn_eval hfn asg, ← slotObjective_min hsolve, ← hnames]; exact hobj
    have hleaf : solveLeaf m (slots.map Prod.fst) asg = true :=
      solveLeaf_of_accepted hacc'
    have hmem' : asg ∈ allAssigns (slots.map Prod.snd) := by
      rw [← hdoms]; exact hmem
    rcases optBbCore_optimal_dissect hcore with ⟨t, w, hr, rfl, rfl⟩ | hbody
    · have hle := optRefine_done_optimal (f := f) (min := true) (m := m)
        (names := slots.map Prod.fst) (doms := slots.map Prod.snd)
        (leavesProduct (slots.map Prod.snd) + 1) none _ _ v' asg
        hr hmem' hleaf hobj'
      simp only [objLeOf, hsolve]
      simpa only [objLe] using hle
    · have hopt : optimizeModel m = .optimal text v :=
        (optimizeModel_eq_optBody_min huns hwf hslots hsolve hfn).trans hbody
      exact optimizeModel_optimal hopt hmem hacc hobj
  · have hslots' : modelSlots m = some slots := modelSlots_eq.mpr hslots
    obtain ⟨hnames, hdoms⟩ := slotNames_domains_of_modelSlots hslots'
    have hacc' : checkModelSolution m (emitAssignment (slots.map Prod.fst) asg)
        = .accepted := by
      rw [← hnames]; exact hacc
    have hobj' : f asg = some v' := by
      rw [slotObjFn_eval hfn asg, ← slotObjective_max hsolve, ← hnames]; exact hobj
    have hleaf : solveLeaf m (slots.map Prod.fst) asg = true :=
      solveLeaf_of_accepted hacc'
    have hmem' : asg ∈ allAssigns (slots.map Prod.snd) := by
      rw [← hdoms]; exact hmem
    rcases optBbCore_optimal_dissect hcore with ⟨t, w, hr, rfl, rfl⟩ | hbody
    · have hle := optRefine_done_optimal (f := f) (min := false) (m := m)
        (names := slots.map Prod.fst) (doms := slots.map Prod.snd)
        (leavesProduct (slots.map Prod.snd) + 1) none _ _ v' asg
        hr hmem' hleaf hobj'
      simp only [objLeOf, hsolve]
      simpa only [objLe] using hle
    · have hopt : optimizeModel m = .optimal text v :=
        (optimizeModel_eq_optBody_max huns hwf hslots hsolve hfn).trans hbody
      exact optimizeModel_optimal hopt hmem hacc hobj

/-- **UNSAT soundness of `optimizeModelBb`**: if the branch-and-bound
    optimizer returns `.unsat`, then no complete assignment of the
    model's slot domains yields an accepted solution. -/
theorem optimizeModelBb_unsat {m : Model} (h : optimizeModelBb m = .unsat)
    {asg : List Value} (hmem : asg ∈ allAssigns (slotDomains m)) :
    checkModelSolution m (emitAssignment (slotNames m) asg) ≠ .accepted := by
  intro hacc
  rcases optimizeModelBb_gates_unsat h with
    ⟨anns, e, slots, f, hsolve, huns, hwf, hslots, hfn, hcore⟩ |
    ⟨anns, e, slots, f, hsolve, huns, hwf, hslots, hfn, hcore⟩
  · have hslots' : modelSlots m = some slots := modelSlots_eq.mpr hslots
    obtain ⟨hnames, hdoms⟩ := slotNames_domains_of_modelSlots hslots'
    have hacc' : checkModelSolution m (emitAssignment (slots.map Prod.fst) asg)
        = .accepted := by
      rw [← hnames]; exact hacc
    have hleaf : solveLeaf m (slots.map Prod.fst) asg = true :=
      solveLeaf_of_accepted hacc'
    have hmem' : asg ∈ allAssigns (slots.map Prod.snd) := by
      rw [← hdoms]; exact hmem
    rcases optBbCore_unsat_dissect hcore with hr | hbody
    · have hfalse := optRefine_noneFound (f := f) (min := true) (m := m)
        (names := slots.map Prod.fst) (doms := slots.map Prod.snd)
        (leavesProduct (slots.map Prod.snd) + 1) none hr asg hmem'
      rw [hfalse] at hleaf
      exact Bool.noConfusion hleaf
    · have hopt : optimizeModel m = .unsat :=
        (optimizeModel_eq_optBody_min huns hwf hslots hsolve hfn).trans hbody
      exact optimizeModel_unsat hopt hmem hacc
  · have hslots' : modelSlots m = some slots := modelSlots_eq.mpr hslots
    obtain ⟨hnames, hdoms⟩ := slotNames_domains_of_modelSlots hslots'
    have hacc' : checkModelSolution m (emitAssignment (slots.map Prod.fst) asg)
        = .accepted := by
      rw [← hnames]; exact hacc
    have hleaf : solveLeaf m (slots.map Prod.fst) asg = true :=
      solveLeaf_of_accepted hacc'
    have hmem' : asg ∈ allAssigns (slots.map Prod.snd) := by
      rw [← hdoms]; exact hmem
    rcases optBbCore_unsat_dissect hcore with hr | hbody
    · have hfalse := optRefine_noneFound (f := f) (min := false) (m := m)
        (names := slots.map Prod.fst) (doms := slots.map Prod.snd)
        (leavesProduct (slots.map Prod.snd) + 1) none hr asg hmem'
      rw [hfalse] at hleaf
      exact Bool.noConfusion hleaf
    · have hopt : optimizeModel m = .unsat :=
        (optimizeModel_eq_optBody_max huns hwf hslots hsolve hfn).trans hbody
      exact optimizeModel_unsat hopt hmem hacc

/-- **Value pairing of `optimizeModelBb`**: the value returned with
    an optimal text is the slot-level objective of that text's
    assignment. -/
theorem optimizeModelBb_value {m : Model} {text : String} {v : Int}
    (h : optimizeModelBb m = .optimal text v) :
    ∃ asg, asg ∈ allAssigns (slotDomains m) ∧
      emitAssignment (slotNames m) asg = text ∧
      slotObjective m (slotNames m) asg = some v ∧
      checkModelSolution m text = .accepted := by
  rcases optimizeModelBb_gates h with
    ⟨anns, e, slots, f, hsolve, huns, hwf, hslots, hfn, hcore⟩ |
    ⟨anns, e, slots, f, hsolve, huns, hwf, hslots, hfn, hcore⟩
  · have hslots' : modelSlots m = some slots := modelSlots_eq.mpr hslots
    obtain ⟨hnames, hdoms⟩ := slotNames_domains_of_modelSlots hslots'
    rcases optBbCore_optimal_dissect hcore with ⟨t, w, hr, ht, hv⟩ | hbody
    · obtain ⟨hacc, asg, hmem, hemit, hf⟩ :=
        optRefine_done_sound (f := f) (min := true) (m := m)
          (names := slots.map Prod.fst) (doms := slots.map Prod.snd)
          (leavesProduct (slots.map Prod.snd) + 1) none t w
          (by rintro t0 w0 ⟨⟩) hr
      rw [← ht, ← hv]
      refine ⟨asg, ?_, ?_, ?_, hacc⟩
      · rw [hdoms]; exact hmem
      · rw [hnames]; exact hemit
      · rw [hnames]
        simp only [slotObjective, hsolve]
        rw [← slotObjFn_eval hfn asg]
        exact hf
    · have hopt : optimizeModel m = .optimal text v :=
        (optimizeModel_eq_optBody_min huns hwf hslots hsolve hfn).trans hbody
      exact optimizeModel_value hopt
  · have hslots' : modelSlots m = some slots := modelSlots_eq.mpr hslots
    obtain ⟨hnames, hdoms⟩ := slotNames_domains_of_modelSlots hslots'
    rcases optBbCore_optimal_dissect hcore with ⟨t, w, hr, ht, hv⟩ | hbody
    · obtain ⟨hacc, asg, hmem, hemit, hf⟩ :=
        optRefine_done_sound (f := f) (min := false) (m := m)
          (names := slots.map Prod.fst) (doms := slots.map Prod.snd)
          (leavesProduct (slots.map Prod.snd) + 1) none t w
          (by rintro t0 w0 ⟨⟩) hr
      rw [← ht, ← hv]
      refine ⟨asg, ?_, ?_, ?_, hacc⟩
      · rw [hdoms]; exact hmem
      · rw [hnames]; exact hemit
      · rw [hnames]
        simp only [slotObjective, hsolve]
        rw [← slotObjFn_eval hfn asg]
        exact hf
    · have hopt : optimizeModel m = .optimal text v :=
        (optimizeModel_eq_optBody_max huns hwf hslots hsolve hfn).trans hbody
      exact optimizeModel_value hopt

/-- **Agreement on the optimal value**: whenever the two optimizers
    both return `.optimal`, the returned values are equal (each is at
    least as good as the other, by the two optimality theorems
    applied to the other's value-providing assignment; the `satisfy`
    direction of `objLeOf` makes the impossible satisfaction case
    harmless). -/
theorem optimizeModelBb_agrees {m : Model} {text1 text2 : String} {v1 v2 : Int}
    (h1 : optimizeModelBb m = .optimal text1 v1)
    (h2 : optimizeModel m = .optimal text2 v2) : v1 = v2 := by
  obtain ⟨asg1, hmem1, hemit1, hobj1, _⟩ := optimizeModelBb_value h1
  obtain ⟨asg2, hmem2, hemit2, hobj2, _⟩ := optimizeModel_value h2
  have hacc1' : checkModelSolution m (emitAssignment (slotNames m) asg1) = .accepted :=
    hemit1 ▸ optimizeModelBb_sat_sound h1
  have hacc2' : checkModelSolution m (emitAssignment (slotNames m) asg2) = .accepted :=
    hemit2 ▸ optimizeModel_sat_sound h2
  have hle1 : objLeOf m v1 v2 := optimizeModelBb_optimal h1 hmem2 hacc2' hobj2
  have hle2 : objLeOf m v2 v1 := optimizeModel_optimal h2 hmem1 hacc1' hobj1
  cases hsolve : m.solve with
  | satisfy a =>
      simp only [objLeOf, hsolve] at hle1 hle2
      omega
  | minimize a e =>
      simp only [objLeOf, hsolve] at hle1 hle2
      omega
  | maximize a e =>
      simp only [objLeOf, hsolve] at hle1 hle2
      omega

end LeanFzn.Solver

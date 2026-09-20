import solver.Search
import solver.Emit.Basic
import solver.Domain
import solver.Heuristic
import solver.Propagators
import solver.Fixpoint
import solver.Extract
import LeanFzn.FznCheck

/-!
# The FlatZinc-facing solver (PLAN.md 6.1, 6.2)

`solveModel` turns the generic exhaustive `search` of
`solver/Search.lean` into a FlatZinc solver: extract the finite
search slots (`solver/Domain.lean`), search all their assignments,
and at each leaf *emit the solution text and check it with the
verified checker* (`LeanFzn.Check.checkModelSolutionFast`, proved
equal to the front door by `checkModelSolutionFast_eq`).  The
leaf-check architecture makes SAT soundness almost immediate — a
returned text is accepted precisely because the leaf that produced
it checked it — and routes UNSAT soundness through `search_none`.

## The result type

`SolveResult` distinguishes `sat text` (a solution text the verified
checker accepts), `unsat`, and `unsupported reason`.  PLAN 6.1's
resource-limited `unknown` is folded into `unsupported` in this
phase: the only refusals are static (out-of-fragment domains,
oversized domains, unsupported predicates, ill-formed models), so
no *interrupted* search can be misreported.  When future phases add
node/time/memory limits, `unsupported` must be split so an
interrupted search can be reported as `unknown` without ever
collapsing into `unsat`.

## The master theorems

* `solveModel_sat_sound` (**SAT soundness**, PLAN 6.1): if the
  solver returns `sat text`, then the verified checker accepts
  `text` — `checkModelSolution m text = .accepted` — so by
  `checkModelSolution_correct` the model is well formed and the
  parsed entries' completed store satisfies the declarative
  semantics `Satisfies fullSig fullInterp`.

* `solveModel_unsat_sound` (**UNSAT soundness**, PLAN 6.1): if the
  solver returns `unsat` on a model with finite search slots, then
  *no* assignment of the slot domains is accepted: for every
  `asg ∈ allAssigns (slotDomains m)`, the emitted text is rejected
  by the checker.  Since the emitted text assigns exactly the slot
  names to the slot values, and the extracted domains are exactly
  the declared domains (`varDomain_values_iff`), this covers every
  assignment of the declared finite domains.

* Termination is inherited from `search` (its measure argument is
  discharged in `solver/Search.lean`); no separate corollary is
  needed.

* Completeness: for models in the fragment, the two directions
  combine with the master theorems of `solver/Search.lean` —
  `search_some`/`search_none` make the search sound and complete
  for its leaf predicate — so `solveModel` returns `sat` exactly
  when some slot assignment has an accepted emitted text (a
  half of completeness, the other half — that every satisfying
  *store* arises from some slot assignment — depends on the model's
  initializer structure and is left as the documented scope
  restriction; see the module discussion in
  `solver/Domain.lean`).

The UNSAT statement deliberately quantifies over emitted-and-checked
texts rather than over raw stores: it is exactly the leaf-check
architecture's guarantee, with no admission.  Its checker side is
the verified front door, so the quantification is over the same
`satisfying-assignment` notion the checker certifies.
-/

namespace LeanFzn.Solver

open LeanFzn LeanFzn.Solution LeanFzn.Check LeanFzn.Globals

/-- The result of `solveModel`: a checker-accepted solution text,
    a refutation, or a refusal to run.  PLAN 6.1's `unknown` is
    folded into `unsupported` in this phase (no resource limits
    exist yet, so no run is ever interrupted; see the module doc). -/
inductive SolveResult where
  /-- A solution was found; the carried text is accepted by the
      verified checker (`solveModel_sat_sound`). -/
  | sat (text : String)
  /-- Exhaustive search found no accepted assignment. -/
  | unsat
  /-- The model is outside the searched fragment (out-of-fragment or
      capped domains, unsupported predicate, ill-formed), or — in
      future phases — a resource-limited `unknown`. -/
  | unsupported (reason : String)
  deriving Repr, Inhabited

/-- Build the solution text for one complete slot assignment: pair
    the slot names with the assigned values (both in slot order) and
    emit. -/
def emitAssignment (names : List String) (asg : List Value) : String :=
  emitSolution (names.zip asg)

/-- The leaf predicate of the exhaustive search on one model: pair
    the slot names with a candidate assignment, emit the solution
    text, and check it with the verified front door (fast twin;
    `checkModelSolutionFast_eq` is unconditional). -/
def solveLeaf (m : Model) (names : List String) : List Value → Bool :=
  fun asg => checkModelSolutionFast m (emitAssignment names asg) == .accepted

/-- The prepared twin of the leaf predicate: `solveLeaf` over a
    `PreparedModel` (IDEAS 1.1 + 3), so the two static gates, the
    per-constraint name dispatch, *and* the store base (parameters
    pre-inserted, initializer-only completion plan) are computed once
    per solve instead of once per leaf.  `solveLeafP_eq` proves it is
    `solveLeaf` pointwise, so the leaf-check architecture is
    unchanged. -/
def solveLeafP (p : PreparedModel) (names : List String) : List Value → Bool :=
  fun asg => checkPreparedSolution p (emitAssignment names asg) == .accepted

/-- The prepared leaf is the reference leaf, pointwise: preparing the
    model once and checking through `checkPreparedSolution` returns
    the front door's verdict on every emitted text (by
    `checkPreparedSolution_eq` and `checkModelSolutionFast_eq`). -/
theorem solveLeafP_eq (m : Model) (names : List String) (asg : List Value) :
    solveLeafP (prepareModel m) names asg = solveLeaf m names asg := by
  simp only [solveLeafP, solveLeaf, checkPreparedSolution_eq, checkModelSolutionFast_eq]

/-- The function-level form of `solveLeafP_eq`, used to rewrite an
    entry point's leaf back to `solveLeaf` after unfolding it. -/
theorem solveLeafP_eq' (m : Model) (names : List String) :
    solveLeafP (prepareModel m) names = solveLeaf m names := by
  funext asg
  exact solveLeafP_eq m names asg

/-- **The FlatZinc solver.**  Runs the exhaustive reference search on
    the model's finite search slots; each leaf's candidate solution
    text is validated by the verified checker (through a
    `PreparedModel` built once per solve — the prepared twin of the
    leaf is `solveLeaf` pointwise by `solveLeafP_eq`) before being
    reported.  Refuses models that are ill-formed, use unsupported
    predicates, or fall outside the finite fragment (including the
    per-variable and total-leaf caps of `solver/Domain.lean`). -/
def solveModel (m : Model) : SolveResult :=
  match firstUnsupportedFast m with
  | some n => .unsupported s!"unsupported predicate: {n}"
  | none =>
      if wellFormedFastB m then
        match slotsChecked m with
        | .error e => .unsupported e
        | .ok slots =>
            let p := prepareModel m
            match search (solveLeafP p (slots.map Prod.fst))
                (slots.map Prod.snd) [] with
            | some asg => .sat (emitAssignment (slots.map Prod.fst) asg)
            | none => .unsat
      else
        .unsupported "model is not well-formed"

/-! ## SAT soundness

A returned text was produced by a leaf whose `solveLeaf` the search
certified; unfolding `solveLeaf` and `emitAssignment` (the emitted
text is exactly the leaf's text) turns `search_some`'s guarantee
into acceptance by the verified checker. -/

/-- **SAT soundness**: a solution text returned by `solveModel` is
    accepted by the verified front door.  By
    `checkModelSolution_correct`, the model is well formed, every
    constraint name is checkable, and the parsed entries' completed
    store satisfies `Satisfies fullSig fullInterp`. -/
theorem solveModel_sat_sound {m : Model} {text : String}
    (h : solveModel m = .sat text) : checkModelSolution m text = .accepted := by
  rw [← checkModelSolutionFast_eq]
  -- unfold solveModel down to the search result
  simp only [solveModel] at h
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
              -- the search returned some assignment
              cases hsearch : search (solveLeaf m (slots.map Prod.fst))
                  (slots.map Prod.snd) [] with
              | none => rw [hsearch] at h; exact absurd h (by simp)
              | some asg =>
                  rw [hsearch] at h
                  -- the returned text is the leaf's emitted text
                  have htext : text = emitAssignment (slots.map Prod.fst) asg :=
                    (SolveResult.sat.inj h).symm
                  subst htext
                  -- ... and the leaf certified it
                  obtain ⟨a, _ha, hrfl, hleaf⟩ :=
                    search_some (solveLeaf m (slots.map Prod.fst))
                      (slots.map Prod.snd) [] asg hsearch
                  have hasg : a = asg := by
                    simpa [List.nil_append] using hrfl.symm
                  subst hasg
                  simp only [solveLeaf, emitAssignment, List.nil_append,
                    beq_iff_eq] at hleaf
                  exact hleaf

/-! ## UNSAT soundness

`search_none` certifies that every complete assignment fails the
leaf; the leaf checks the emitted text, so no assignment of the slot
domains has an accepted emitted text. -/

/-- **UNSAT soundness**: if `solveModel` returns `unsat`, then no
    complete assignment of the model's search-slot domains yields an
    accepted solution: for every `asg ∈ allAssigns (slotDomains m)`,
    the checker rejects the emitted text.  (With
    `modelSlots m = some slots`, `slotDomains m` is exactly the
    slots' value lists; by `varDomain_values_iff` those are the
    declared domains, so the quantification covers every assignment
    of the declared finite domains.) -/
theorem solveModel_unsat_sound {m : Model} (h : solveModel m = .unsat)
    {asg : List Value} (hmem : asg ∈ allAssigns (slotDomains m)) :
    checkModelSolution m (emitAssignment (slotNames m) asg) ≠ .accepted := by
  intro hacc
  rw [← checkModelSolutionFast_eq] at hacc
  -- unfold solveModel down to the failed search
  simp only [solveModel] at h
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
              -- the search returned none
              cases hsearch : search (solveLeaf m (slots.map Prod.fst))
                  (slots.map Prod.snd) [] with
              | some a => rw [hsearch] at h; exact absurd h (by simp)
              | none =>
                  -- so every assignment of the slots fails the leaf
                  have hnone := search_none (solveLeaf m (slots.map Prod.fst))
                    (slots.map Prod.snd) [] hsearch
                  -- relate slotDomains/slotNames of m to the extracted slots
                  have hslots' : modelSlots m = some slots :=
                    (modelSlots_eq.mpr hslots)
                  obtain ⟨hnames, hdoms⟩ :=
                    slotNames_domains_of_modelSlots hslots'
                  rw [hdoms] at hmem
                  have hleaf := hnone asg hmem
                  rw [List.nil_append] at hleaf
                  -- the leaf evaluated at asg is the acceptance we assumed
                  have hleafacc : solveLeaf m (slots.map Prod.fst) asg = true := by
                    simp only [solveLeaf, beq_iff_eq]
                    rw [← hnames]
                    exact hacc
                  rw [hleafacc] at hleaf
                  exact Bool.noConfusion hleaf


/-! ## The integrated solver variants (Round 3)

Two further entry points on top of `solveModel`, both keeping the
leaf-check architecture (`solveLeaf` — the verified checker decides
every leaf, exactly as in `solveModel`):

* `solveModelProp fuel` — `solveModel` with the pruning search of
  PLAN 6.3 (`prunedSearch`): before branching, the extracted
  constraint set (`solver/Extract.lean`) is propagated to a fixpoint
  and contradictory subtrees are pruned.  The uniformity is the point:
  `prunedSearch` with an *empty* propagator list is the reference
  search (only with in-place branching), so a model with no
  extractable constraints — e.g. only `fzn_all_different_int`, which
  extraction skips — falls back to exhaustive search through the very
  same code path, with no special case.  The fuel bounds both the
  propagation rounds and the branching levels; every fuel value yields
  a sound search, only with less pruning (the master theorems of
  `solver/Fixpoint.lean` hold for every fuel).

* `solveModelHeur` — `solveModel` with MRV slot selection (PLAN 6.5,
  `mrvSearch` from `solver/Heuristic.lean`): the slot order is sorted
  by ascending domain size, which changes only the branch order of an
  otherwise exhaustive partition.

### The theorems

* `solveModelProp_sat_sound` / `solveModelHeur_sat_sound` — the SAT
  soundness of PLAN 6.1 for both entry points, unconditionally: a
  returned text is accepted by the verified checker (by
  `checkModelSolution_correct`, the parsed entries' completed store
  then satisfies `Satisfies fullSig fullInterp`).

* `solveModelHeur_unsat_sound` — the UNSAT soundness of PLAN 6.1 for
  the MRV entry point, unconditionally: an `unsat` verdict excludes
  every assignment of the slot domains, via `mrvSearch_none`.

* `solveModelProp_unsat_sound` — the UNSAT soundness for the pruning
  entry point, under the explicit pruning licence that
  `prunedSearch_none` needs: every leaf-passing assignment satisfies
  every extracted `DomConstraint`.  The licence is exactly the
  store-level content of `extractConstraints_holds`
  (`solver/Extract.lean`), which proves — unconditionally — that a
  store satisfying the model's constraints under `fullInterp` (the
  constraint half of what `checkModelSolution_correct` certifies for
  every accepted solution) and agreeing with the assignment at the
  slot names satisfies every extracted constraint.  Closing the last
  step — the string round trip "the checker accepted the text emitted
  from `a`, therefore the completed store assigns the slot names
  `a`'s values" — is deliberately out of scope: `completedStore` is
  `opaque` by design (a compilation safeguard,
  `LeanFzn/FznSolution.lean`), so no lemma can see its content.  The
  SAT side and the leaf check are unaffected: the checker itself still
  decides every leaf, so pruning can never *produce* an unjustified
  `sat`.
-/

/-- The propagator list aligned with a list of extracted slot
    constraints — one propagator per `DomConstraint` constructor, as
    the `AllPreserve` alignment of `solver/Fixpoint.lean` requires
    (each propagator's preservation theorem is already proven in
    `solver/Propagators.lean`). -/
def domPropagators : List DomConstraint → List (List (List Value) → PropResult)
  | [] => []
  | .eqSlot i j :: cs => propEqSlot i j :: domPropagators cs
  | .neSlot i j :: cs => propNeSlot i j :: domPropagators cs
  | .leSlot i j :: cs => propLeSlot i j :: domPropagators cs
  | .constEq i v :: cs => propConstEq i v :: domPropagators cs
  | .plusSlot i j k :: cs => propPlusSlot i j k :: domPropagators cs
  | .leConstHi i c :: cs => propLeConstHi i c :: domPropagators cs
  | .leConstLo i c :: cs => propLeConstLo i c :: domPropagators cs
  | .allDiff is :: cs => propAllDiff is :: domPropagators cs
  | .timesSlot i j k :: cs => propTimesSlot i j k :: domPropagators cs
  | .minSlot i j k :: cs => propMinSlot i j k :: domPropagators cs
  | .maxSlot i j k :: cs => propMaxSlot i j k :: domPropagators cs
  | .absSlot i k :: cs => propAbsSlot i k :: domPropagators cs
  | .linEq coeffs is b :: cs => propLinEq coeffs is b :: domPropagators cs
  | .linLe coeffs is b :: cs => propLinLe coeffs is b :: domPropagators cs
  | .ltSlot i j :: cs => propLtSlot i j :: domPropagators cs
  | .ltConstHi i c :: cs => propLtConstHi i c :: domPropagators cs
  | .ltConstLo i c :: cs => propLtConstLo i c :: domPropagators cs
  | .boolNotSlot i j :: cs => propBoolNotSlot i j :: domPropagators cs
  | .boolAndSlot i j k :: cs => propBoolAndSlot i j k :: domPropagators cs
  | .boolOrSlot i j k :: cs => propBoolOrSlot i j k :: domPropagators cs

/-- The propagator list is aligned with the constraint list: every
    propagator meets the Round-1 preservation contract for its
    constraint. -/
theorem domPropagators_preserve : ∀ cs : List DomConstraint,
    AllPreserve cs (domPropagators cs)
  | [] => .nil
  | .eqSlot i j :: cs => .cons (propEqSlot_preserves i j) (domPropagators_preserve cs)
  | .neSlot i j :: cs => .cons (propNeSlot_preserves i j) (domPropagators_preserve cs)
  | .leSlot i j :: cs => .cons (propLeSlot_preserves i j) (domPropagators_preserve cs)
  | .constEq i v :: cs => .cons (propConstEq_preserves i v) (domPropagators_preserve cs)
  | .plusSlot i j k :: cs =>
      .cons (propPlusSlot_preserves i j k) (domPropagators_preserve cs)
  | .leConstHi i c :: cs =>
      .cons (propLeConstHi_preserves i c) (domPropagators_preserve cs)
  | .leConstLo i c :: cs =>
      .cons (propLeConstLo_preserves i c) (domPropagators_preserve cs)
  | .allDiff is :: cs => .cons (propAllDiff_preserves is) (domPropagators_preserve cs)
  | .timesSlot i j k :: cs =>
      .cons (propTimesSlot_preserves i j k) (domPropagators_preserve cs)
  | .minSlot i j k :: cs =>
      .cons (propMinSlot_preserves i j k) (domPropagators_preserve cs)
  | .maxSlot i j k :: cs =>
      .cons (propMaxSlot_preserves i j k) (domPropagators_preserve cs)
  | .absSlot i k :: cs =>
      .cons (propAbsSlot_preserves i k) (domPropagators_preserve cs)
  | .linEq coeffs is b :: cs =>
      .cons (propLinEq_preserves coeffs is b) (domPropagators_preserve cs)
  | .linLe coeffs is b :: cs =>
      .cons (propLinLe_preserves coeffs is b) (domPropagators_preserve cs)
  | .ltSlot i j :: cs =>
      .cons (propLtSlot_preserves i j) (domPropagators_preserve cs)
  | .ltConstHi i c :: cs =>
      .cons (propLtConstHi_preserves i c) (domPropagators_preserve cs)
  | .ltConstLo i c :: cs =>
      .cons (propLtConstLo_preserves i c) (domPropagators_preserve cs)
  | .boolNotSlot i j :: cs =>
      .cons (propBoolNotSlot_preserves i j) (domPropagators_preserve cs)
  | .boolAndSlot i j k :: cs =>
      .cons (propBoolAndSlot_preserves i j k) (domPropagators_preserve cs)
  | .boolOrSlot i j k :: cs =>
      .cons (propBoolOrSlot_preserves i j k) (domPropagators_preserve cs)

/-- **The propagating solver** (PLAN 6.3 + 6.2): `solveModel` with the
    pruning search — at each node the extracted constraints are
    propagated to a fixpoint, contradictory subtrees are pruned, and
    leaves are decided by the same checker leaf as `solveModel`
    (its prepared twin, `solveLeafP` — `solveLeaf` pointwise).  When
    the model has no extractable constraints (or extraction
    fails), the propagator list is empty and `prunedSearch` is the
    reference search through the same code path. -/
def solveModelProp (fuel : Nat) (m : Model) : SolveResult :=
  match firstUnsupportedFast m with
  | some n => .unsupported s!"unsupported predicate: {n}"
  | none =>
      if wellFormedFastB m then
        match slotsChecked m with
        | .error e => .unsupported e
        | .ok slots =>
            let p := prepareModel m
            let names := slots.map Prod.fst
            let cs := match extractConstraints m with
              | .ok cs => cs
              | .error _ => []
            match prunedSearch (solveLeafP p names) (domPropagators cs) fuel
                (slots.map Prod.snd) [] with
            | some asg => .sat (emitAssignment names asg)
            | none => .unsat
      else
        .unsupported "model is not well-formed"

/-- **The MRV solver** (PLAN 6.5 + 6.2): `solveModel` with
    minimum-remaining-values slot selection — the branch order is
    sorted by ascending domain size; the leaf is the same checker
    leaf (its prepared twin, `solveLeafP`). -/
def solveModelHeur (m : Model) : SolveResult :=
  match firstUnsupportedFast m with
  | some n => .unsupported s!"unsupported predicate: {n}"
  | none =>
      if wellFormedFastB m then
        match slotsChecked m with
        | .error e => .unsupported e
        | .ok slots =>
            let p := prepareModel m
            let names := slots.map Prod.fst
            match mrvSearch (solveLeafP p names) (slots.map Prod.snd) with
            | some asg => .sat (emitAssignment names asg)
            | none => .unsat
      else
        .unsupported "model is not well-formed"

/-! ### SAT soundness of the new entry points -/

/-- **SAT soundness of `solveModelProp`**: a solution text returned by
    the propagating solver is accepted by the verified front door (so
    by `checkModelSolution_correct` the model is well formed and the
    parsed entries' completed store satisfies `Satisfies fullSig
    fullInterp`).  Unconditional — the leaf check is the checker
    itself, exactly as in `solveModel_sat_sound`. -/
theorem solveModelProp_sat_sound {m : Model} {fuel : Nat} {text : String}
    (h : solveModelProp fuel m = .sat text) :
    checkModelSolution m text = .accepted := by
  rw [← checkModelSolutionFast_eq]
  simp only [solveModelProp] at h
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
              cases hsearch : prunedSearch (solveLeaf m (slots.map Prod.fst))
                  (domPropagators (match extractConstraints m with
                    | .ok cs => cs
                    | .error _ => [])) fuel (slots.map Prod.snd) [] with
              | none => rw [hsearch] at h; exact absurd h (by simp)
              | some asg =>
                  rw [hsearch] at h
                  have htext : text = emitAssignment (slots.map Prod.fst) asg :=
                    (SolveResult.sat.inj h).symm
                  subst htext
                  obtain ⟨a, _ha, hrfl, hleaf⟩ :=
                    prunedSearch_some (solveLeaf m (slots.map Prod.fst))
                      (domPropagators (match extractConstraints m with
                        | .ok cs => cs
                        | .error _ => []))
                      (match extractConstraints m with
                        | .ok cs => cs
                        | .error _ => [])
                      (domPropagators_preserve
                        (match extractConstraints m with
                          | .ok cs => cs
                          | .error _ => []))
                      fuel (slots.map Prod.snd) [] asg hsearch
                  have hasg : a = asg := by
                    simpa [List.nil_append] using hrfl.symm
                  subst hasg
                  simp only [solveLeaf, emitAssignment, List.nil_append,
                    beq_iff_eq] at hleaf
                  exact hleaf

/-- **SAT soundness of `solveModelHeur`**: a solution text returned by
    the MRV solver is accepted by the verified front door.
    Unconditional. -/
theorem solveModelHeur_sat_sound {m : Model} {text : String}
    (h : solveModelHeur m = .sat text) :
    checkModelSolution m text = .accepted := by
  rw [← checkModelSolutionFast_eq]
  simp only [solveModelHeur] at h
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
              cases hsearch : mrvSearch (solveLeaf m (slots.map Prod.fst))
                  (slots.map Prod.snd) with
              | none => rw [hsearch] at h; exact absurd h (by simp)
              | some asg =>
                  rw [hsearch] at h
                  have htext : text = emitAssignment (slots.map Prod.fst) asg :=
                    (SolveResult.sat.inj h).symm
                  subst htext
                  obtain ⟨_ha, hleaf⟩ :=
                    mrvSearch_some (leaf := solveLeaf m (slots.map Prod.fst))
                      (slots := slots.map Prod.snd) (r := asg) hsearch
                  simp only [solveLeaf, emitAssignment, beq_iff_eq] at hleaf
                  exact hleaf

/-! ### UNSAT soundness of the new entry points -/

/-- **UNSAT soundness of `solveModelHeur`**: if the MRV solver returns
    `unsat`, then no complete assignment of the model's search-slot
    domains yields an accepted solution — the MRV order changes only
    the branch order of an exhaustive partition
    (`mrvSearch_none`). -/
theorem solveModelHeur_unsat_sound {m : Model} (h : solveModelHeur m = .unsat)
    {asg : List Value} (hmem : asg ∈ allAssigns (slotDomains m)) :
    checkModelSolution m (emitAssignment (slotNames m) asg) ≠ .accepted := by
  intro hacc
  rw [← checkModelSolutionFast_eq] at hacc
  simp only [solveModelHeur] at h
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
              cases hsearch : mrvSearch (solveLeaf m (slots.map Prod.fst))
                  (slots.map Prod.snd) with
              | some a => rw [hsearch] at h; exact absurd h (by simp)
              | none =>
                  have hnone := mrvSearch_none (solveLeaf m (slots.map Prod.fst))
                    (slots.map Prod.snd) hsearch
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

/-- **UNSAT soundness of `solveModelProp`**, under the pruning licence:
    if the solver returns `unsat` and every leaf-passing assignment
    satisfies every extracted `DomConstraint` — the hypothesis
    `prunedSearch_none` needs, whose store-level content is
    `extractConstraints_holds` (`solver/Extract.lean`; see the module
    discussion for the one deliberately unproven step) — then no
    complete assignment of the model's search-slot domains yields an
    accepted solution. -/
theorem solveModelProp_unsat_sound {m : Model} {fuel : Nat}
    (h : solveModelProp fuel m = .unsat)
    (hleaf : ∀ a, solveLeaf m (slotNames m) a = true →
      AllSat (extractDomConstraints m) a)
    {asg : List Value} (hmem : asg ∈ allAssigns (slotDomains m)) :
    checkModelSolution m (emitAssignment (slotNames m) asg) ≠ .accepted := by
  intro hacc
  rw [← checkModelSolutionFast_eq] at hacc
  simp only [solveModelProp] at h
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
              cases hsearch : prunedSearch (solveLeaf m (slots.map Prod.fst))
                  (domPropagators (match extractConstraints m with
                    | .ok cs => cs
                    | .error _ => [])) fuel (slots.map Prod.snd) [] with
              | some a => rw [hsearch] at h; exact absurd h (by simp)
              | none =>
                  -- the leaf-implies-constraints licence, in the shape the
                  -- pruning search needs (acc = [])
                  have hslots' : modelSlots m = some slots :=
                    (modelSlots_eq.mpr hslots)
                  obtain ⟨hnames, hdoms⟩ :=
                    slotNames_domains_of_modelSlots hslots'
                  have hlicence : ∀ a, solveLeaf m (slots.map Prod.fst) ([] ++ a) = true →
                      AllSat (match extractConstraints m with
                        | .ok cs => cs
                        | .error _ => []) a := by
                    intro a hleafa
                    simp only [List.nil_append] at hleafa
                    -- the leaf hypothesis in terms of `slotNames m`
                    have hleafa' : solveLeaf m (slotNames m) a = true := by
                      rw [hnames]; exact hleafa
                    have hsame : (match extractConstraints m with
                        | .ok cs => cs
                        | .error _ => []) = extractDomConstraints m := by
                      unfold extractDomConstraints
                      cases extractConstraints m with
                      | error _ => rfl
                      | ok cs => rfl
                    rw [hsame]
                    exact hleaf a hleafa'
                  have hnone := prunedSearch_none (solveLeaf m (slots.map Prod.fst))
                    (domPropagators (match extractConstraints m with
                      | .ok cs => cs
                      | .error _ => []))
                    (match extractConstraints m with
                      | .ok cs => cs
                      | .error _ => [])
                    (domPropagators_preserve
                      (match extractConstraints m with
                        | .ok cs => cs
                        | .error _ => []))
                    [] hlicence fuel (slots.map Prod.snd) hsearch
                  rw [hdoms] at hmem
                  have hleaf := hnone asg hmem
                  rw [List.nil_append] at hleaf
                  have hleafacc : solveLeaf m (slots.map Prod.fst) asg = true := by
                    simp only [solveLeaf, beq_iff_eq]
                    rw [← hnames]
                    exact hacc
                  rw [hleafacc] at hleaf
                  exact Bool.noConfusion hleaf

end LeanFzn.Solver

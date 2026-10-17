import LeanFzn
import solver.Search
import solver.Propagators

/-!
# Propagation fixpoint and pruning search (PLAN.md 6.3, part 2)

Round 1 (`solver/Propagators.lean`) established the per-propagator
contract `Preserves`: one propagator narrows the slot domains while
keeping every assignment that satisfies *its* constraint, or
certifies a contradiction.  This module wires that contract into an
executable solver layer — the propagation fixpoint and the pruning
search that uses it.  The final integration into `solveModel` is a
later round; the leaf stays an opaque `List Value → Bool` parameter,
as `solver/Solve.lean`'s leaf-check architecture requires.

## Design

* `propPass` — one round-robin pass: apply every propagator in
  sequence, threading the domains, stopping at the first certified
  contradiction.
* `fixpointFuel` — iterate passes until a pass narrows nothing
  (detected with the structural equality `domsEqB`) or a propagator
  certifies a contradiction.  The iteration is bounded by a fuel
  parameter, which exists for termination only: the preservation
  theorems below hold for *every* fuel, so a small fuel merely
  weakens pruning, never soundness.  (PLAN 6.3 suggests a decreasing
  measure such as the sum of finite domain cardinalities; such a
  measure cannot be derived from the `Preserves` contract alone,
  because the contract's `DomPointwiseSub` admits duplicate-carrying
  outputs whose slot lists grow — e.g. `[v, v]` is pointwise-subset
  `[v]` — so domain sizes need not decrease across a round.  The
  fuel makes the iteration total without extra assumptions, and
  `fixpoint_stable` proves the semantic idempotence statement that
  once a full pass narrows nothing, further passes narrow nothing
  more: for every remaining fuel the fixpoint returns the input
  unchanged.)
* the composition theorems — preservation is stable under
  conjunction: when the constraint list `cs` and the propagator list
  `props` are aligned (`AllPreserve cs props`), a fixpoint-narrowed
  output keeps every assignment satisfying ALL constraints of `cs`,
  and a fixpoint contradiction excludes every such assignment
  (`fixpointFuel_narrowed`, `fixpointFuel_contradicts`).  The
  P-generalized forms (`fixpointFuel_narrowed_gen`,
  `fixpointFuel_contradicts_gen`) state the same for any predicate
  `P` implied by all aligned constraints — the form the pruning
  search consumes, with `P` = "the leaf accepts the full
  assignment".  Both directions follow the recommended P-shape and
  bridge to the Round-1 `Preserves` contract as-is (no propagator is
  re-proved; alignment packages the per-position theorems).
* `splitBranch` — the branching step: split the first slot with two
  or more values into "one value" versus "the rest", *keeping every
  slot in place*.  Branching in place (rather than consuming the
  first slot the way the exhaustive `search` does) is what makes the
  pruning search sound: `DomConstraint` positions index the original
  slots, so consuming a prefix would silently re-index every later
  constraint onto the wrong domains.
* `prunedSearch` — at each node run the fixpoint; on a certified
  contradiction prune the whole subtree (the composition theorem
  certifies that no assignment below survives); otherwise branch and
  recurse on both halves.  When no slot has two values left, every
  slot is decided (or dead) and the at-most-one remaining assignment
  is handed to the exhaustive reference `search`.  The branching
  fuel decreases per level; a node whose fuel is exhausted falls
  back to the exhaustive reference search, which is sound and
  complete for its leaf — so both master theorems hold for every
  fuel, only with less pruning.

## The master theorems

* `prunedSearch_some` — an assignment returned by the pruning search
  is a complete assignment of the original slot domains and passes
  the leaf predicate.
* `prunedSearch_none` — under the hypothesis that the leaf implies
  the aligned constraints (every leaf-passing assignment satisfies
  every `c ∈ cs` — the pruning licence, since pruning removes
  exactly assignments that violate the constraints), a `none`
  verdict means every complete assignment of the domains fails the
  leaf.  The statement is given for an arbitrary accumulator `acc`;
  at `acc = []` it is precisely the form above.
-/

namespace LeanFzn.Solver

open LeanFzn LeanFzn.Solution

/-! ## Pointwise-subset helpers -/

/-- Pointwise subsetting is transitive: shrinking twice is still a
    shrink. -/
theorem DomPointwiseSub.trans {doms1 doms2 doms3 : List (List Value)}
    (h12 : DomPointwiseSub doms1 doms2) (h23 : DomPointwiseSub doms2 doms3) :
    DomPointwiseSub doms1 doms3 :=
  ⟨h12.1.trans h23.1, fun k v hv => h23.2 k v (h12.2 k v hv)⟩

/-- Prepending the same slot to both sides of a pointwise-subset
    family keeps it pointwise-subset. -/
theorem DomPointwiseSub.cons {d : List Value} {doms1 doms2 : List (List Value)}
    (h : DomPointwiseSub doms1 doms2) :
    DomPointwiseSub (d :: doms1) (d :: doms2) := by
  refine ⟨by
    have hlen := h.1
    simp only [List.length_cons]
    omega, ?_⟩
  intro k v hv
  cases k with
  | zero => exact hv
  | succ k' => exact h.2 k' v hv

/-! ## The conjunction of the aligned constraints -/

/-- `a` satisfies every constraint of `cs` — the property the
    composition theorems preserve. -/
def AllSat (cs : List DomConstraint) (a : List Value) : Prop :=
  ∀ c ∈ cs, c.SatisfiedBy a

/-- Satisfaction of a conjunction is satisfaction of the head and
    of the tail. -/
theorem allSat_cons {c : DomConstraint} {cs : List DomConstraint} {a : List Value} :
    AllSat (c :: cs) a ↔ c.SatisfiedBy a ∧ AllSat cs a := by
  constructor
  · intro h
    exact ⟨h c (by simp), fun c' hc' => h c' (by simp [hc'])⟩
  · rintro ⟨hc, hcs⟩ c' hc'
    rcases List.mem_cons.mp hc' with heq | hin
    · rw [heq]; exact hc
    · exact hcs c' hin

/-! ## Alignment of constraints with propagators -/

/-- The conjunction-composition side condition (index-aligned, as
    an inductive relation): the constraint list and the propagator
    list have the same length, and the propagator at each position
    meets the Round-1 preservation contract for the constraint at
    the same position.  The Round-1 preservation theorems
    (`propEqSlot_preserves`, `propNeSlot_preserves`,
    `propLeSlot_preserves`, `propConstEq_preserves`) package into
    `AllPreserve` directly, position by position. -/
inductive AllPreserve : List DomConstraint → List (List (List Value) → PropResult) → Prop
  /-- Empty constraint list against empty propagator list. -/
  | nil : AllPreserve [] []
  /-- Head propagator preserves the head constraint; the tails are
      aligned. -/
  | cons {c : DomConstraint} {p : List (List Value) → PropResult}
      {cs : List DomConstraint} {ps : List (List (List Value) → PropResult)}
      (h : Preserves c p) (hrest : AllPreserve cs ps) : AllPreserve (c :: cs) (p :: ps)

/-! ## Structural equality of domain lists -/

/-- `valuesEqB` is reflexive (through the reflexivity of
    `Value.eqB`). -/
theorem valuesEqB_refl : ∀ (xs : List Value), valuesEqB xs xs = true := by
  intro xs
  induction xs with
  | nil => rfl
  | cons v vs ih =>
      show (v.eqB v && valuesEqB vs vs) = true
      rw [value_eqB_refl v, ih]
      rfl

/-- `valuesEqB` implies list equality. -/
theorem valuesEqB_eq : ∀ (xs ys : List Value), valuesEqB xs ys = true → xs = ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      cases ys with
      | nil => rfl
      | cons y ys => simp [valuesEqB] at h
  | cons x xs ih =>
      intro ys h
      cases ys with
      | nil => simp [valuesEqB] at h
      | cons y ys =>
          simp only [valuesEqB, Bool.and_eq_true] at h
          obtain ⟨hxy, hxsy⟩ := h
          have h1 : x = y := value_eqB_iff.mp hxy
          have h2 : xs = ys := ih ys hxsy
          rw [h1, h2]

/-- A pair in the zip of a list with itself has equal components. -/
private theorem mem_zip_self : ∀ (ds : List (List Value)) (y1 y2 : List Value),
    (y1, y2) ∈ ds.zip ds → y1 = y2 := by
  intro ds
  induction ds with
  | nil => intro y1 y2 h; simp at h
  | cons e es ih =>
      intro y1 y2 h
      simp only [List.zip_cons_cons, List.mem_cons] at h
      rcases h with heq | hin
      · injection heq with h1 h2
        rw [h1, h2]
      · exact ih y1 y2 hin

/-- An assignment of a singleton-headed slot family picks exactly the
    singleton's value in the head. -/
private theorem singleton_head {v : Value} {ds : List (List Value)} {a : List Value}
    (ha : a ∈ allAssigns ([v] :: ds)) :
    ∃ a' ∈ allAssigns ds, a = v :: a' := by
  obtain ⟨w, hw, a', ha', rfl⟩ := (mem_allAssigns_singleton v [] ds a).mp ha
  have hvw : w = v := List.mem_singleton.mp hw
  subst hvw
  exact ⟨a', ha', rfl⟩

/-- `domsEqB` — the domain-list equality behind the `BEq PropResult`
    instance and the fixpoint's stability test — is reflexive. -/
theorem domsEqB_refl : ∀ (xs : List (List Value)), domsEqB xs xs = true := by
  intro xs
  induction xs with
  | nil => rfl
  | cons d ds ih =>
      have hz : ((d :: ds).zip (d :: ds)).all (fun p => valuesEqB p.1 p.2) = true :=
        List.all_eq_true.mpr
          (by
            rintro ⟨y1, y2⟩ hp
            simp only [List.zip_cons_cons, List.mem_cons] at hp
            rcases hp with heq | hin
            · injection heq with h1 h2
              have hy1 : y1 = d := h1
              have hy2 : y2 = d := h2
              rw [hy1, hy2]
              show valuesEqB (d, d).fst (d, d).snd = true
              exact valuesEqB_refl d
            · have hyy : y1 = y2 := mem_zip_self ds y1 y2 hin
              rw [hyy]
              show valuesEqB (y2, y2).fst (y2, y2).snd = true
              exact valuesEqB_refl y2)
      show ((d :: ds).length == (d :: ds).length &&
        ((d :: ds).zip (d :: ds)).all (fun p => valuesEqB p.1 p.2)) = true
      rw [hz, beq_self_eq_true]
      rfl

/-- `domsEqB` implies list equality. -/
theorem domsEqB_eq : ∀ (xs ys : List (List Value)), domsEqB xs ys = true → xs = ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      cases ys with
      | nil => rfl
      | cons e es =>
          simp only [domsEqB, List.length_nil, List.length_cons] at h
          exact absurd h (by simp)
  | cons d ds ih =>
      intro ys h
      cases ys with
      | nil => simp [domsEqB] at h
      | cons e es =>
          simp only [domsEqB, List.length_cons, List.zip_cons_cons, List.all_cons,
            Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨hlen, hd, hrest⟩ := h
          have hl : ds.length = es.length := by omega
          have hde : d = e := valuesEqB_eq d e hd
          have hds : ds = es := by
            refine ih es ?_
            simp only [domsEqB, Bool.and_eq_true]
            exact ⟨by simp [hl], hrest⟩
          rw [hde, hds]

/-- `domsEqB` decides domain-list equality — the fixpoint's
    stability test is a genuine equality test. -/
theorem domsEqB_iff {xs ys : List (List Value)} :
    domsEqB xs ys = true ↔ xs = ys :=
  ⟨domsEqB_eq xs ys, fun h => h ▸ domsEqB_refl xs⟩

/-! ## One propagation pass -/

/-- One round-robin pass: apply every propagator in sequence,
    threading the domains; the first certified contradiction ends
    the pass. -/
def propPass : List (List (List Value) → PropResult) → List (List Value) → PropResult
  | [], doms => .narrowed doms
  | p :: ps, doms =>
      match p doms with
      | .contradiction => .contradiction
      | .narrowed doms' => propPass ps doms'

/-- **Pass composition, narrowed case**: a pass over aligned
    propagators keeps every assignment satisfying all the aligned
    constraints (preservation is stable under conjunction) and only
    shrinks the domains. -/
theorem propPass_narrowed :
    ∀ (cs : List DomConstraint) (props : List (List (List Value) → PropResult)),
      AllPreserve cs props →
        ∀ doms doms', propPass props doms = .narrowed doms' →
          DomPointwiseSub doms' doms ∧
            ∀ a ∈ allAssigns doms, AllSat cs a → a ∈ allAssigns doms' := by
  intro cs props
  induction props generalizing cs with
  | nil =>
      intro halign doms doms' h
      cases halign with
      | nil =>
          simp only [propPass] at h
          have hd : doms = doms' := PropResult.narrowed.inj h
          subst hd
          exact ⟨DomPointwiseSub.refl doms, fun a ha _ => ha⟩
  | cons p ps ih =>
      intro halign doms doms' h
      cases halign with
      | cons hp halign' =>
          simp only [propPass] at h
          cases hp1 : p doms with
          | contradiction =>
              rw [hp1] at h
              exact absurd h (by simp)
          | narrowed doms1 =>
              rw [hp1] at h
              obtain ⟨hsub2, hkeep2⟩ := ih _ halign' doms1 doms' h
              refine ⟨hsub2.trans (hp.subset hp1), ?_⟩
              intro a ha hall
              obtain ⟨hc, hcs'⟩ := allSat_cons.mp hall
              exact hkeep2 a (hp.narrowed hp1 a ha hc) hcs'

/-- **Pass composition, contradiction case**: a pass ending in a
    certified contradiction excludes every assignment satisfying
    all the aligned constraints. -/
theorem propPass_contradicts :
    ∀ (cs : List DomConstraint) (props : List (List (List Value) → PropResult)),
      AllPreserve cs props →
        ∀ doms, propPass props doms = .contradiction →
          ∀ a ∈ allAssigns doms, ¬ AllSat cs a := by
  intro cs props
  induction props generalizing cs with
  | nil =>
      intro _ doms h
      simp only [propPass] at h
      exact absurd h (by simp)
  | cons p ps ih =>
      intro halign doms h
      cases halign with
      | cons hp halign' =>
          simp only [propPass] at h
          cases hp1 : p doms with
          | contradiction =>
              rw [hp1] at h
              intro a ha hall
              exact hp.contradicts hp1 a ha (allSat_cons.mp hall).1
          | narrowed doms1 =>
              rw [hp1] at h
              intro a ha hall
              obtain ⟨hc, hcs'⟩ := allSat_cons.mp hall
              exact ih _ halign' doms1 h a (hp.narrowed hp1 a ha hc) hcs'

/-! ## Iterating to a fixpoint -/

/-- The propagation fixpoint: apply passes until a pass narrows
    nothing (detected with the structural equality `domsEqB`) or a
    propagator certifies a contradiction.  The fuel bounds the number
    of rounds; it exists for termination (PLAN 6.3's decreasing
    measure made structural), and the preservation theorems below
    hold for every fuel — a small fuel only weakens pruning, never
    soundness. -/
def fixpointFuel (props : List (List (List Value) → PropResult)) :
    Nat → List (List Value) → PropResult
  | 0, doms => .narrowed doms
  | fuel + 1, doms =>
      match propPass props doms with
      | .contradiction => .contradiction
      | .narrowed doms' =>
          if domsEqB doms' doms then .narrowed doms'
          else fixpointFuel props fuel doms'

/-- **Fixpoint composition, narrowed case** — the key composition
    theorem of PLAN 6.3 (preservation is stable under conjunction):
    iterating aligned propagators to a fixpoint keeps every
    assignment satisfying all the aligned constraints, and only
    shrinks the domains — for every fuel. -/
theorem fixpointFuel_narrowed {cs : List DomConstraint}
    {props : List (List (List Value) → PropResult)}
    (halign : AllPreserve cs props) :
    ∀ fuel doms doms', fixpointFuel props fuel doms = .narrowed doms' →
      DomPointwiseSub doms' doms ∧
        ∀ a ∈ allAssigns doms, AllSat cs a → a ∈ allAssigns doms' := by
  intro fuel
  induction fuel with
  | zero =>
      intro doms doms' h
      simp only [fixpointFuel] at h
      have hd : doms = doms' := PropResult.narrowed.inj h
      subst hd
      exact ⟨DomPointwiseSub.refl doms, fun a ha _ => ha⟩
  | succ fuel ih =>
      intro doms doms' h
      simp only [fixpointFuel] at h
      cases hpass : propPass props doms with
      | contradiction =>
          simp only [hpass] at h
          exact absurd h (by simp)
      | narrowed doms1 =>
          simp only [hpass] at h
          by_cases hst : domsEqB doms1 doms = true
          · rw [if_pos hst] at h
            have hd : doms1 = doms' := PropResult.narrowed.inj h
            subst hd
            exact propPass_narrowed cs props halign doms doms1 hpass
          · rw [if_neg hst] at h
            obtain ⟨hsub1, hkeep1⟩ := propPass_narrowed cs props halign doms doms1 hpass
            obtain ⟨hsub2, hkeep2⟩ := ih doms1 doms' h
            exact ⟨hsub2.trans hsub1, fun a ha hall => hkeep2 a (hkeep1 a ha hall) hall⟩

/-- **Fixpoint composition, contradiction case**: a fixpoint ending
    in a certified contradiction excludes every assignment
    satisfying all the aligned constraints — for every fuel. -/
theorem fixpointFuel_contradicts {cs : List DomConstraint}
    {props : List (List (List Value) → PropResult)}
    (halign : AllPreserve cs props) :
    ∀ fuel doms, fixpointFuel props fuel doms = .contradiction →
      ∀ a ∈ allAssigns doms, ¬ AllSat cs a := by
  intro fuel
  induction fuel with
  | zero =>
      intro doms h
      simp only [fixpointFuel] at h
      exact absurd h (by simp)
  | succ fuel ih =>
      intro doms h
      simp only [fixpointFuel] at h
      cases hpass : propPass props doms with
      | contradiction =>
          simp only [hpass] at h
          exact propPass_contradicts cs props halign doms hpass
      | narrowed doms1 =>
          simp only [hpass] at h
          by_cases hst : domsEqB doms1 doms = true
          · rw [if_pos hst] at h
            exact absurd h (by simp)
          · rw [if_neg hst] at h
            intro a ha hall
            exact ih doms1 h a
              ((propPass_narrowed cs props halign doms doms1 hpass).2 a ha hall) hall

/-- **Fixpoint composition, narrowed case, P-form**: for any
    predicate `P` implied by all the aligned constraints, the
    fixpoint keeps every `P`-assignment.  This is the form the
    pruning search consumes (with `P` = "the leaf accepts the full
    assignment"). -/
theorem fixpointFuel_narrowed_gen {cs : List DomConstraint}
    {props : List (List (List Value) → PropResult)}
    (halign : AllPreserve cs props) {P : List Value → Prop}
    (hP : ∀ a, P a → AllSat cs a) :
    ∀ fuel doms doms', fixpointFuel props fuel doms = .narrowed doms' →
      DomPointwiseSub doms' doms ∧
        ∀ a ∈ allAssigns doms, P a → a ∈ allAssigns doms' := by
  intro fuel doms doms' h
  obtain ⟨hsub, hkeep⟩ := fixpointFuel_narrowed halign fuel doms doms' h
  exact ⟨hsub, fun a ha hPa => hkeep a ha (hP a hPa)⟩

/-- **Fixpoint composition, contradiction case, P-form**: for any
    predicate `P` implied by all the aligned constraints, a
    fixpoint contradiction excludes every `P`-assignment. -/
theorem fixpointFuel_contradicts_gen {cs : List DomConstraint}
    {props : List (List (List Value) → PropResult)}
    (halign : AllPreserve cs props) {P : List Value → Prop}
    (hP : ∀ a, P a → AllSat cs a) :
    ∀ fuel doms, fixpointFuel props fuel doms = .contradiction →
      ∀ a ∈ allAssigns doms, ¬ P a := by
  intro fuel doms h a ha hPa
  exact fixpointFuel_contradicts halign fuel doms h a ha (hP a hPa)

/-- **Idempotence at the fixpoint**: once a full pass narrows
    nothing (its output equals its input), every further iteration
    returns the same domains — the loop detects stability and stops,
    whatever fuel remains.  Since a pass is a deterministic function
    of its input domains, further passes would narrow nothing
    more. -/
theorem fixpoint_stable (props : List (List (List Value) → PropResult))
    (fuel : Nat) (doms : List (List Value))
    (h : propPass props doms = .narrowed doms) :
    fixpointFuel props fuel doms = .narrowed doms := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp only [fixpointFuel, h]
      rw [if_pos (domsEqB_refl doms)]

/-! ## Branching -/

/-- The branching step of the pruning search: find the first slot
    with at least two values and split it into "one value" versus
    "the rest", returning the pair of branch domains.  Slots are
    never consumed — `DomConstraint` positions index the original
    slots, so consuming a prefix (the way the exhaustive `search`
    does) would silently re-index every later constraint onto the
    wrong domains. -/
def splitBranch : List (List Value) → Option (List (List Value) × List (List Value))
  | [] => none
  | [] :: ds => (splitBranch ds).map (fun q => ([] :: q.1, [] :: q.2))
  | [v] :: ds => (splitBranch ds).map (fun q => ([v] :: q.1, [v] :: q.2))
  | (v :: w :: ws) :: ds => some ([v] :: ds, (w :: ws) :: ds)

/-- Both branch domains are pointwise-subsets of the input domains:
    branching only removes values. -/
theorem splitBranch_subset :
    ∀ (doms : List (List Value)) (l r : List (List Value)),
      splitBranch doms = some (l, r) →
        DomPointwiseSub l doms ∧ DomPointwiseSub r doms := by
  intro doms
  induction doms with
  | nil =>
      intro l r h
      simp [splitBranch] at h
  | cons d ds ih =>
      intro l r h
      cases d with
      | nil =>
          simp only [splitBranch] at h
          rw [Option.map_eq_some_iff] at h
          obtain ⟨q, hq, hpair⟩ := h
          obtain ⟨q1, q2⟩ := q
          injection hpair with hl hr
          subst hl
          subst hr
          obtain ⟨hsub1, hsub2⟩ := ih q1 q2 hq
          exact ⟨DomPointwiseSub.cons hsub1, DomPointwiseSub.cons hsub2⟩
      | cons v us =>
          cases us with
          | nil =>
              simp only [splitBranch] at h
              rw [Option.map_eq_some_iff] at h
              obtain ⟨q, hq, hpair⟩ := h
              obtain ⟨q1, q2⟩ := q
              injection hpair with hl hr
              subst hl
              subst hr
              obtain ⟨hsub1, hsub2⟩ := ih q1 q2 hq
              exact ⟨DomPointwiseSub.cons hsub1, DomPointwiseSub.cons hsub2⟩
          | cons w ws =>
              simp only [splitBranch] at h
              injection h with h1
              injection h1 with hl hr
              subst hl
              subst hr
              refine ⟨?_, ?_⟩
              · have hself : DomPointwiseSub ((v :: w :: ws) :: ds)
                    ((v :: w :: ws) :: ds) := DomPointwiseSub.refl _
                have heq : [v] :: ds = setSlot ((v :: w :: ws) :: ds) 0 [v] := rfl
                rw [heq]
                exact DomPointwiseSub.setSlot hself (fun v' hv' => by
                  have hvv : v' = v := List.mem_singleton.mp hv'
                  rw [hvv]
                  exact List.mem_cons_self)
              · have hself : DomPointwiseSub ((v :: w :: ws) :: ds)
                    ((v :: w :: ws) :: ds) := DomPointwiseSub.refl _
                have heq : (w :: ws) :: ds = setSlot ((v :: w :: ws) :: ds) 0 (w :: ws) :=
                  rfl
                rw [heq]
                exact DomPointwiseSub.setSlot hself (fun v' hv' =>
                  List.mem_cons_of_mem _ hv')

/-- Every assignment of the input domains survives into at least one
    of the two branch domains — the branching is exhaustive. -/
theorem splitBranch_cover :
    ∀ (doms : List (List Value)) (l r : List (List Value)),
      splitBranch doms = some (l, r) →
        ∀ a ∈ allAssigns doms, a ∈ allAssigns l ∨ a ∈ allAssigns r := by
  intro doms
  induction doms with
  | nil =>
      intro l r h a ha
      simp only [splitBranch] at h
      exact absurd h (by simp)
  | cons d ds ih =>
      intro l r h a ha
      cases d with
      | nil => exact absurd ha (by simp [allAssigns])
      | cons v us =>
          cases us with
          | nil =>
              simp only [splitBranch] at h
              rw [Option.map_eq_some_iff] at h
              obtain ⟨q, hq, hpair⟩ := h
              obtain ⟨q1, q2⟩ := q
              injection hpair with hl hr
              subst hl
              subst hr
              obtain ⟨a', ha', rfl⟩ := singleton_head ha
              rcases ih q1 q2 hq a' ha' with hL | hR
              · exact Or.inl ((mem_allAssigns_singleton v [] q1 (v :: a')).mpr
                  ⟨v, List.mem_cons_self, a', hL, rfl⟩)
              · exact Or.inr ((mem_allAssigns_singleton v [] q2 (v :: a')).mpr
                  ⟨v, List.mem_cons_self, a', hR, rfl⟩)
          | cons w ws =>
              simp only [splitBranch] at h
              injection h with h1
              injection h1 with hl hr
              subst hl
              subst hr
              obtain ⟨x, hx, a', ha', rfl⟩ :=
                (mem_allAssigns_singleton v (w :: ws) ds a).mp ha
              rcases List.mem_cons.mp hx with heq | hin
              · exact Or.inl ((mem_allAssigns_singleton v [] ds (x :: a')).mpr
                  ⟨v, List.mem_cons_self, a', ha', by rw [heq]⟩)
              · exact Or.inr ((mem_allAssigns_singleton w ws ds (x :: a')).mpr
                  ⟨x, hin, a', ha', rfl⟩)

/-! ## The pruning search -/

/-- **The pruning search of PLAN 6.3**: at each node, run the
    propagation fixpoint on the current domains — a certified
    contradiction prunes the whole subtree; otherwise branch on the
    first slot with two or more values (one value versus the rest)
    and recurse on both halves; when no slot has two values left,
    every slot is decided (or dead), and the at-most-one remaining
    assignment is handed to the exhaustive reference `search`.  The
    fuel bounds the number of branching levels (a pure domain
    measure cannot: the `Preserves` contract admits
    duplicate-carrying narrowings whose slot lists grow, so domain
    sizes need not decrease); a node whose fuel is exhausted falls
    back to the exhaustive reference search, which is sound and
    complete for its leaf — so every fuel yields a sound and
    complete search, only with less pruning. -/
def prunedSearch (leaf : List Value → Bool)
    (props : List (List (List Value) → PropResult)) :
    Nat → List (List Value) → List Value → Option (List Value)
  | 0, doms, acc => search leaf doms acc
  | fuel + 1, doms, acc =>
      match fixpointFuel props (fuel + 1) doms with
      | .contradiction => none
      | .narrowed doms' =>
          match splitBranch doms' with
          | none => search leaf doms' acc
          | some (l, r) =>
              match prunedSearch leaf props fuel l acc with
              | some a => some a
              | none => prunedSearch leaf props fuel r acc
termination_by fuel _ _ => fuel

/-- **Soundness of a successful pruning search** (PLAN 6.3's master
    theorem, SAT direction): an assignment returned by the pruning
    search is a complete assignment of the original slot domains and
    passes the leaf predicate — the propagation phase only ever
    removes assignments that fail the constraints, never invents
    values outside the original domains. -/
theorem prunedSearch_some (leaf : List Value → Bool)
    (props : List (List (List Value) → PropResult)) (cs : List DomConstraint)
    (halign : AllPreserve cs props) :
    ∀ (fuel : Nat) (doms : List (List Value)) (acc : List Value) (r : List Value),
      prunedSearch leaf props fuel doms acc = some r →
        ∃ a, a ∈ allAssigns doms ∧ r = acc ++ a ∧ leaf (acc ++ a) = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro doms acc r h
      simp only [prunedSearch] at h
      exact search_some leaf doms acc r h
  | succ fuel ih =>
      intro doms acc r h
      simp only [prunedSearch] at h
      cases hfix : fixpointFuel props (fuel + 1) doms with
      | contradiction =>
          simp only [hfix] at h
          exact absurd h (by simp)
      | narrowed doms' =>
          simp only [hfix] at h
          obtain ⟨hsub, _⟩ := fixpointFuel_narrowed halign (fuel + 1) doms doms' hfix
          cases hbr : splitBranch doms' with
          | none =>
              simp only [hbr] at h
              cases hs : search leaf doms' acc with
              | none =>
                  rw [hs] at h
                  exact absurd h (by simp)
              | some a =>
                  rw [hs] at h
                  have hra : a = r := Option.some.inj h
                  obtain ⟨a', ha', hrfl, hleaf⟩ := search_some leaf doms' acc a hs
                  refine ⟨a', allAssigns_mono doms' doms hsub a' ha', ?_, hleaf⟩
                  rw [← hra, hrfl]
          | some q =>
              obtain ⟨l, r'⟩ := q
              simp only [hbr] at h
              obtain ⟨hsubl, hsubr⟩ := splitBranch_subset doms' l r' hbr
              cases hrec : prunedSearch leaf props fuel l acc with
              | some a =>
                  rw [hrec] at h
                  have hra : a = r := Option.some.inj h
                  obtain ⟨a', ha', hrfl, hleaf⟩ := ih l acc a hrec
                  refine ⟨a', allAssigns_mono l doms (hsubl.trans hsub) a' ha', ?_, hleaf⟩
                  rw [← hra, hrfl]
              | none =>
                  rw [hrec] at h
                  obtain ⟨a', ha', hrfl, hleaf⟩ := ih r' acc r h
                  exact ⟨a', allAssigns_mono r' doms (hsubr.trans hsub) a' ha', hrfl, hleaf⟩

/-- **Soundness of an unsuccessful pruning search** (PLAN 6.3's
    master theorem, UNSAT direction): if every assignment accepted by
    the accumulator-shifted leaf satisfies every aligned constraint
    — the pruning licence, since pruning removes exactly the
    assignments that violate the constraints — then a `none` verdict
    means every complete assignment of the slot domains fails the
    leaf.  At `acc = []` the hypothesis is precisely "every
    leaf-passing assignment satisfies all of `cs`" and the
    conclusion is "every assignment of the original domains fails
    `leaf`". -/
theorem prunedSearch_none (leaf : List Value → Bool)
    (props : List (List (List Value) → PropResult)) (cs : List DomConstraint)
    (halign : AllPreserve cs props) (acc : List Value)
    (hleaf : ∀ a, leaf (acc ++ a) = true → AllSat cs a) :
    ∀ (fuel : Nat) (doms : List (List Value)),
      prunedSearch leaf props fuel doms acc = none →
        ∀ a ∈ allAssigns doms, leaf (acc ++ a) = false := by
  intro fuel
  induction fuel with
  | zero =>
      intro doms h
      simp only [prunedSearch] at h
      exact search_none leaf doms acc h
  | succ fuel ih =>
      intro doms h
      simp only [prunedSearch] at h
      cases hfix : fixpointFuel props (fuel + 1) doms with
      | contradiction =>
          simp only [hfix] at h
          intro a ha
          by_cases hleafa : leaf (acc ++ a) = true
          · exact absurd hleafa
              (fixpointFuel_contradicts_gen halign hleaf (fuel + 1) doms hfix a ha)
          · rw [Bool.not_eq_true] at hleafa
            exact hleafa
      | narrowed doms' =>
          simp only [hfix] at h
          cases hbr : splitBranch doms' with
          | none =>
              simp only [hbr] at h
              cases hs : search leaf doms' acc with
              | some a =>
                  rw [hs] at h
                  exact absurd h (by simp)
              | none =>
                  intro a ha
                  by_cases hleafa : leaf (acc ++ a) = true
                  · have hIn : a ∈ allAssigns doms' :=
                      (fixpointFuel_narrowed_gen halign hleaf
                        (fuel + 1) doms doms' hfix).2 a ha hleafa
                    have hfail := search_none leaf doms' acc hs a hIn
                    rw [hleafa] at hfail
                    exact absurd hfail (by simp)
                  · rw [Bool.not_eq_true] at hleafa
                    exact hleafa
          | some q =>
              obtain ⟨l, r'⟩ := q
              simp only [hbr] at h
              cases hrec : prunedSearch leaf props fuel l acc with
              | some a =>
                  rw [hrec] at h
                  exact absurd h (by simp)
              | none =>
                  rw [hrec] at h
                  intro a ha
                  by_cases hleafa : leaf (acc ++ a) = true
                  · have hIn : a ∈ allAssigns doms' :=
                      (fixpointFuel_narrowed_gen halign hleaf
                        (fuel + 1) doms doms' hfix).2 a ha hleafa
                    rcases splitBranch_cover doms' l r' hbr a hIn with hL | hR
                    · have hf := ih l hrec a hL
                      rw [hleafa] at hf
                      exact absurd hf (by simp)
                    · have hf := ih r' h a hR
                      rw [hleafa] at hf
                      exact absurd hf (by simp)
                  · rw [Bool.not_eq_true] at hleafa
                    exact hleafa

end LeanFzn.Solver

import LeanFzn.Semantics.Globals
import LeanFzn.Semantics.ValueEquality
import LeanFzn.Parser.Parser
import LeanFzn.Solver.Core.Enumerate
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation


/-!
# Verified propagation (PLAN.md 6.3)

This module implements the first milestone of PLAN 6.3: a
*propagation contract* — the local preservation theorem every
propagator must carry — and the first propagators over finite slot
domains.

## Background

The exhaustive reference LeanFzn.Solver (`LeanFzn/Solver/Reference/Enumerate.lean`) enumerates the
complete assignments of a list of finite slot domains (`allAssigns
doms`) and accepts an assignment through a leaf predicate.  Propagation
narrows the domains first so the search enumerates fewer assignments.
Propagation never changes semantics: a propagator must satisfy a local
preservation theorem, and the pruning search (a later round) may rely
only on that generic contract, so a weak propagator can later be
replaced by a stronger one without re-proving the search.

## The propagation contract

A propagator takes the current slot domains — one finite list of
`LeanFzn.Semantics.Value` per slot, the very shape `LeanFzn/Compiler/Domain.lean` extracts
and `search` consumes — and returns:

* `PropResult.contradiction` — the propagator certifies that *no*
  assignment of the current domains can satisfy its constraint; or
* `PropResult.narrowed doms'` — new domains with every
  still-satisfying assignment kept.

Preservation is stated relative to a declarative constraint
representation rather than the opaque leaf predicate, so the contract
is leaf-independent and propagators for different constraints compose.
The representation is:

* `DomConstraint` — an inductive of constraint kinds over slot
  positions: `eqSlot i j` (slots `i`, `j` equal — `int_eq` style),
  `neSlot i j` (they differ — `int_ne` style), `leSlot i j` (slot `i`
  at most slot `j` — `int_le` style), `constEq i v` (slot `i` equals
  the constant `v`, as arises from `int_eq(x, c)` with a constant
  argument), `plusSlot i j k` (slot `i` plus slot `j` equals slot
  `k` — `int_plus` style), `leConstHi i c` / `leConstLo i c` (slot
  `i` at most / at least the constant `c`, as arises from
  `int_le(x, c)` / `int_le(c, x)` with a constant argument),
  `allDiff is` (the slots at the positions of `is` pairwise differ —
  `all_different` style), `timesSlot i j k` (slot `i` times slot `j`
  equals slot `k` — `int_times` style), `minSlot i j k` / `maxSlot i
  j k` (slot `k` is the minimum / maximum of slots `i` and `j` —
  `int_min` / `int_max` style), and `absSlot i k` (slot `k` is the
  absolute value of slot `i` — `int_abs` style);
* `DomConstraint.SatisfiedBy c a` — the declarative semantics: what it
  means, in `Prop`, for a complete assignment `a` to satisfy `c`;
* `DomConstraint.satisfiedB` — the executable Boolean twin, with the
  agreement theorem `DomConstraint.satisfiedB_iff`.

A propagator `p` for `c` meets the contract when it inhabits the
`Preserves c p` structure (below), which packages the two halves of
PLAN 6.3's local preservation theorem:

* **Narrowing soundness** (`Preserves.narrowed`): if `p` returns
  `narrowed doms'`, then every assignment of the input domains that
  satisfies `c` is still an assignment of the output domains —
  "every satisfying assignment compatible with the input domains
  remains compatible with the output domains";
* **Contradiction soundness** (`Preserves.contradicts`): if `p`
  returns `contradiction`, no assignment of the input domains
  satisfies `c`;
* **Shrinking** (`Preserves.subset`): the output domains only shrank —
  `DomPointwiseSub doms' doms`: same slot count, and every value of an
  output slot lies in the corresponding input slot.  This keeps
  `doms'` honest (a propagator may only remove values, never add or
  invent them) and gives a later pruning search its decreasing
  measure.

## The propagators

Every propagator below meets the contract, with its preservation
theorem proved unconditionally:

* `propEqSlot i j` — equality on two slots: both domains narrow to
  their intersection (values equal under the checker's structural
  equality `Value.eqB`); `contradiction` when the intersection is
  empty (`propEqSlot_preserves`);
* `propNeSlot i j` — disequality: if one domain is a singleton, its
  value is removed from the other; `contradiction` when the other
  domain becomes empty.  Boolean channeling (`bool_eq`, `bool_ne`)
  routes through the same value equality, so no separate Boolean
  propagator is needed (`propNeSlot_preserves`);
* `propLeSlot i j` — order: slot `i` keeps values at most the maximum
  integer of slot `j`'s domain, slot `j` keeps values at least the
  minimum integer of slot `i`'s domain; `contradiction` when either
  side becomes empty (`propLeSlot_preserves`);
* `propConstEq i v` — slot `i` equals a constant: the domain becomes
  `{v}` when `v` was present, `contradiction` when absent
  (`propConstEq_preserves`);
* `propPlusSlot i j k` — bounds propagation for `x + y = z`
  (`int_plus` style): each slot narrows to the interval implied by
  the other two slots' extrema — slot `i` keeps values `p` with
  `zmin - ymax ≤ p ≤ zmax - ymin`, slot `j` symmetrically, slot `k`
  keeps `p + q`'s range `xmin + ymin ≤ r ≤ xmax + ymax` — each
  interval filter computed once from the *input* domains (sound even
  when slot positions coincide, because every bound argument holds
  for any satisfying assignment independently);
  `contradiction` when any side empties or a domain has no integers
  (`propPlusSlot_preserves`);
* `propTimesSlot i j k` and `propMinSlot i j k` / `propMaxSlot i j k`
  — bounds propagation for `x * y = z`, `min x y = z`, `max x y = z`
  (`int_times` / `int_min` / `int_max` style): each operand slot keeps
  exactly the values passing the (necessary) interval conditions
  implied by the other operand's extrema and the result interval, and
  the result slot keeps the corresponding interval — the four-corner
  product interval for `times`, `[min xmin ymin, min xmax ymax]` /
  `[max xmin ymin, max xmax ymax]` for `min` / `max`;
  `contradiction` when any side empties or a domain has no integers
  (`propTimesSlot_preserves`, `propMinSlot_preserves`,
  `propMaxSlot_preserves`);
* `propAbsSlot i k` — bounds propagation for `absValue x = r`
  (`int_abs` style): the operand slot keeps exactly the values with
  `rmin ≤ absValue x ≤ rmax`, the result slot keeps `[0, ...]`;
  `contradiction` when any side empties or a domain has no integers
  (`propAbsSlot_preserves`);
* `propLinEq coeffs is b` / `propLinLe coeffs is b` — bounds
  propagation for the linear constraints `Σ cᵢ·xᵢ = b` / `≤ b`
  (`int_lin_eq` / `int_lin_le` style) over the `DomConstraint.linEq`/
  `linLe` constructors: each listed slot keeps the values whose
  term's contribution can be offset by the other terms' extrema
  (`linNarrowAll`, with the totals fixed to the whole triple's
  extrema sums).  The arithmetic core of their preservation
  theorems is proven (`dotLe_eq`, `dotProduct_eq_sum`, `term_bound`,
  `dotSum_bounds`); the master narrowing-soundness induction for
  `linNarrowAll` is future work, so `domPropagators` attaches the
  sound identity placeholder `propIdSlot` for these kinds until it
  lands;
* `propIdSlot` — the identity propagator (narrows nothing): the
  sound placeholder for constraint kinds whose preservation theorem
  is not yet proven (`propIdSlot_preserves`);
* `propLeConstHi i c` — slot `i` at most the constant `c`
  (`int_le(x, c)` style): the domain keeps its integer values `≤ c`;
  `contradiction` when that empties (`propLeConstHi_preserves`);
* `propLeConstLo i c` — slot `i` at least the constant `c`
  (`int_le(c, x)` style): the domain keeps its integer values `≥ c`;
  `contradiction` when that empties (`propLeConstLo_preserves`);
* `propAllDiff is` — pigeonhole counting for pairwise distinctness
  (`all_different` style): if the number of slots whose position is
  in range is greater than the number of distinct values in the union
  of their domains, `contradiction` — by the pigeonhole principle no
  assignment can make them pairwise distinct (any satisfying
  assignment reads pairwise-distinct values at those slots, and each
  read value lies in its slot's domain, so the union must hold at
  least as many distinct values as there are slots).  Otherwise
  nothing is narrowed — the interval/Hall reasoning of real
  `all_different` propagation is future work (`propAllDiff_preserves`).

## Helper theory

`allAssigns` is monotone under pointwise domain shrinking: if every
slot of `doms'` is pointwise-subset the corresponding slot of `doms`,
every assignment of `doms'` is an assignment of `doms`
(`allAssigns_mono`).  The preservation theorems use the constructive
direction `allAssigns_intro` (an assignment picking, per slot, a value
of that slot's narrowed domain, is an assignment of the narrowed
family) together with the spec `allAssigns_spec`; the converse of
monotonicity for *satisfying* assignments is exactly the preservation
content a propagator contributes.

The `allDiff` propagator additionally carries a small list-library
pigeonhole: `dedupVals` (first-occurrence deduplication under the
checker's structural equality) preserves membership and yields a
duplicate-free list, and `nodup_subset_length_le` — a duplicate-free
list whose values all lie in another duplicate-free list is at most as
long — is the counting heart of the contradiction case.
-/

namespace LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.Core
open LeanFzn LeanFzn.Semantics.Evaluation LeanFzn.Solver.Core List

/-! ## Slot access

Domains are positional: `getSlot doms k` is the domain of slot `k`
(the empty domain past the end, so a propagator never crashes on a
short model), and `setSlot doms k d` replaces slot `k`'s domain
(unchanged past the end).  Neither changes the slot count. -/

/-- The domain of slot `k`: the empty domain past the end of the slot
    list. -/
def getSlot : List (List Value) → Nat → List Value
  | [], _ => []
  | d :: _, 0 => d
  | _ :: ds, k + 1 => getSlot ds k

/-- Replace slot `k`'s domain with `d`; past the end, nothing
    changes. -/
def setSlot : List (List Value) → Nat → List Value → List (List Value)
  | [], _, _ => []
  | _ :: ds, 0, d' => d' :: ds
  | e :: ds, k + 1, d' => e :: setSlot ds k d'

/-- `setSlot` never changes the slot count. -/
theorem setSlot_length (doms : List (List Value)) (d : List Value) :
    ∀ (k : Nat), (setSlot doms k d).length = doms.length := by
  induction doms with
  | nil => intro _; rfl
  | cons e es ih =>
      intro k
      cases k with
      | zero => rfl
      | succ k' => simp only [setSlot, List.length_cons, ih k']

/-- Setting a slot past the end of the list changes nothing. -/
theorem setSlot_eq_self_of_le (doms : List (List Value)) (d : List Value) :
    ∀ (k : Nat), doms.length ≤ k → setSlot doms k d = doms := by
  induction doms with
  | nil => intro _ _; rfl
  | cons e es ih =>
      intro k hk
      cases k with
      | zero =>
          simp only [List.length_cons] at hk
          exact absurd hk (by omega)
      | succ k' =>
          simp only [setSlot]
          rw [ih k' (by simp only [List.length_cons] at hk; omega)]

/-- A set slot's new domain is readable back (within bounds). -/
theorem getSlot_setSlot_eq (doms : List (List Value)) (d : List Value) :
    ∀ (k : Nat), k < doms.length → getSlot (setSlot doms k d) k = d := by
  induction doms with
  | nil => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | cons e es ih =>
      intro k hk
      cases k with
      | zero => rfl
      | succ k' =>
          have hk' : k' < es.length := by
            simp only [List.length_cons] at hk; omega
          exact ih k' hk'

/-- Setting one slot leaves every other slot untouched. -/
theorem getSlot_setSlot_of_ne (doms : List (List Value)) (d : List Value) :
    ∀ (k k' : Nat), k' ≠ k → getSlot (setSlot doms k d) k' = getSlot doms k' := by
  induction doms with
  | nil => intro _ _ _; rfl
  | cons e es ih =>
      intro k k' hne
      cases k with
      | zero =>
          cases k' with
          | zero => exact absurd rfl hne
          | succ _ => rfl
      | succ k'' =>
          cases k' with
          | zero => rfl
          | succ k''' =>
              exact ih k'' k''' (fun h => hne (congrArg Nat.succ h))

/-- A value of slot `k`'s domain witnesses that the slot list is long
    enough. -/
theorem lt_length_of_mem_getSlot (doms : List (List Value)) :
    ∀ (k : Nat) (v : Value), v ∈ getSlot doms k → k < doms.length := by
  induction doms with
  | nil => intro k v h; exact absurd h (by simp [getSlot])
  | cons e es ih =>
      intro k v h
      cases k with
      | zero =>
          simp only [List.length_cons]
          omega
      | succ k' => exact Nat.succ_lt_succ (ih k' v h)

/-! ## Pointwise subsetting -/

/-- `doms'` is pointwise-subset `doms`: same slot count, and every
    value of an `doms'` slot lies in the corresponding `doms` slot.
    This is the "domains only shrink" half of the propagation
    contract, in the membership form a pruning search needs. -/
def DomPointwiseSub (doms' doms : List (List Value)) : Prop :=
  doms'.length = doms.length ∧
    ∀ k v, v ∈ getSlot doms' k → v ∈ getSlot doms k

/-- Every domain list is pointwise-subset itself. -/
theorem DomPointwiseSub.refl (doms : List (List Value)) :
    DomPointwiseSub doms doms :=
  ⟨rfl, fun _ _ h => h⟩

/-- Setting one slot of a pointwise-subset family keeps it
    pointwise-subset, provided the new domain's values all come from
    the original slot. -/
theorem DomPointwiseSub.setSlot {doms doms1 : List (List Value)}
    {k : Nat} {d : List Value}
    (h0 : DomPointwiseSub doms1 doms)
    (hsub : ∀ v, v ∈ d → v ∈ getSlot doms k) :
    DomPointwiseSub (setSlot doms1 k d) doms := by
  refine ⟨by rw [setSlot_length, ← h0.1], ?_⟩
  intro k' v hv
  by_cases hkk : k' = k
  · subst hkk
    by_cases hlen : k' < doms1.length
    · rw [getSlot_setSlot_eq doms1 d k' hlen] at hv
      exact hsub v hv
    · have hle : doms1.length ≤ k' := by omega
      rw [setSlot_eq_self_of_le doms1 d k' hle] at hv
      exact h0.2 k' v hv
  · rw [getSlot_setSlot_of_ne doms1 d k k' hkk] at hv
    exact h0.2 k' v hv

/-! ## Assignment-list helpers -/

/-- **Monotonicity of `allAssigns` under pointwise shrinking**: if
    `doms'` is pointwise-subset `doms`, every assignment of `doms'`
    is an assignment of `doms`.  (The converse fails in general — that
    is exactly the preservation content a propagator contributes.) -/
theorem allAssigns_mono (doms' : List (List Value)) :
    ∀ (doms : List (List Value)), DomPointwiseSub doms' doms →
      ∀ (a : List Value), a ∈ allAssigns doms' → a ∈ allAssigns doms := by
  induction doms' with
  | nil =>
      intro doms h a ha
      have h0 : doms.length = 0 := by simpa using h.1.symm
      have hnil : doms = [] := List.length_eq_zero_iff.mp h0
      subst hnil
      have ha' : a = [] := by simpa [allAssigns] using ha
      subst ha'
      exact List.mem_singleton.mpr rfl
  | cons d' ds' ih =>
      intro doms h a ha
      cases d' with
      | nil => exact absurd ha (by simp [allAssigns])
      | cons w' ws' =>
          cases doms with
          | nil =>
              have h1 := h.1
              simp only [List.length_cons, List.length_nil] at h1
              exact absurd h1 (by omega)
          | cons d ds =>
              obtain ⟨z, hz, a', ha', rfl⟩ :=
                (mem_allAssigns_singleton w' ws' ds' a).mp ha
              cases d with
              | nil =>
                  have hw' : w' ∈ getSlot (([] : List Value) :: ds) 0 :=
                    h.2 0 w' (List.mem_cons_self)
                  exact absurd hw' (by simp [getSlot])
              | cons w ws =>
                  have hlen' : ds'.length = ds.length := by
                    have h1 := h.1
                    simp only [List.length_cons] at h1
                    omega
                  refine (mem_allAssigns_singleton w ws ds (z :: a')).mpr
                    ⟨z, h.2 0 z hz, a',
                      ih ds ⟨hlen', fun k v hv => h.2 (k + 1) v hv⟩ a' ha', rfl⟩

/-- **The spec of `allAssigns` membership**: an assignment of `doms`
    has one value per slot (its length is the slot count, and every
    value it picks at position `k` lies in slot `k`'s domain). -/
theorem allAssigns_spec (doms : List (List Value)) :
    ∀ (a : List Value), a ∈ allAssigns doms →
      a.length = doms.length ∧
        ∀ k v, a[k]? = some v → v ∈ getSlot doms k := by
  induction doms with
  | nil =>
      intro a ha
      have ha' : a = [] := by simpa [allAssigns] using ha
      subst ha'
      refine ⟨rfl, ?_⟩
      intro k v hv
      exact absurd hv (by simp)
  | cons d ds ih =>
      intro a ha
      cases d with
      | nil => exact absurd ha (by simp [allAssigns])
      | cons w ws =>
          obtain ⟨z, hz, a', ha', rfl⟩ :=
            (mem_allAssigns_singleton w ws ds a).mp ha
          obtain ⟨hlen, hget⟩ := ih a' ha'
          refine ⟨by simp only [List.length_cons]; omega, ?_⟩
          intro k v hv
          cases k with
          | zero =>
              rw [List.getElem?_cons_zero] at hv
              injection hv with hvz
              subst hvz
              exact hz
          | succ k' =>
              rw [List.getElem?_cons_succ] at hv
              exact hget k' v hv

/-- **The converse direction**: a list of the right length that picks,
    at every position `k`, a value of slot `k`'s domain, is an
    assignment of `doms`.  This is how the preservation theorems
    rebuild assignment membership for the narrowed domains. -/
theorem allAssigns_intro (doms : List (List Value)) :
    ∀ (a : List Value), a.length = doms.length →
      (∀ k v, a[k]? = some v → v ∈ getSlot doms k) →
        a ∈ allAssigns doms := by
  induction doms with
  | nil =>
      intro a hlen _hget
      have ha : a = [] := List.length_eq_zero_iff.mp hlen
      subst ha
      exact List.mem_singleton.mpr rfl
  | cons d ds ih =>
      intro a hlen hget
      cases d with
      | nil =>
          cases a with
          | nil =>
              simp only [List.length_nil, List.length_cons] at hlen
              exact absurd hlen (by omega)
          | cons z a' =>
              exact absurd (hget 0 z List.getElem?_cons_zero) (by simp [getSlot])
      | cons w ws =>
          cases a with
          | nil =>
              simp only [List.length_nil, List.length_cons] at hlen
              exact absurd hlen (by omega)
          | cons z a' =>
              have hlen' : a'.length = ds.length := by
                simp only [List.length_cons] at hlen
                omega
              refine (mem_allAssigns_singleton w ws ds (z :: a')).mpr
                ⟨z, hget 0 z List.getElem?_cons_zero, a',
                  ih a' hlen' (fun k v hv => hget (k + 1) v hv), rfl⟩

/-- An allAssigns assignment's value at an in-range slot is a
    member of that slot's domain. -/
theorem mem_of_assign {doms : List (List Value)} {a : List Value}
    (ha : a ∈ allAssigns doms) {j : Nat} (hlt : j < doms.length) :
    a[j]! ∈ getSlot doms j := by
  obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
  have halt : j < a.length := by rw [hlen]; exact hlt
  have hval : a[j]! = a[j] := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem halt, Option.getD_some]
  have hsome : a[j]? = some (a[j]!) := by
    rw [hval, List.getElem?_eq_getElem halt]
  exact hget j _ hsome

/-! ## Domain and value helpers -/

/-- Membership test of a value in a domain, via the checker's
    structural equality. -/
def valueMemB (v : Value) (l : List Value) : Bool := l.any (fun u => u.eqB v)

/-- `valueMemB` decides membership. -/
theorem valueMemB_iff {v : Value} {l : List Value} :
    valueMemB v l = true ↔ v ∈ l := by
  simp only [valueMemB, List.any_eq_true]
  constructor
  · rintro ⟨u, hu, heq⟩
    rw [value_eqB_iff] at heq
    exact heq ▸ hu
  · intro hmem
    exact ⟨v, hmem, value_eqB_refl v⟩


namespace Internal

/-- Structural value equality is `false` exactly on distinct
    values. -/
theorem eqB_false_iff_ne {x y : Value} : x.eqB y = false ↔ x ≠ y := by
  rw [← Bool.not_eq_true', ne_eq, ← value_eqB_iff]
  simp

/-- The `→` direction of `eqB_false_iff_ne`. -/
theorem eqB_false_of_ne {x y : Value} (hne : x ≠ y) :
    x.eqB y = false := eqB_false_iff_ne.mpr hne

end Internal

open LeanFzn.Solver.Propagation.DomainFiltering.Internal

/-- The values of both `di` and `dj`, in `di`'s order — the
    intersection of two domains under structural value equality. -/
def interVals (di dj : List Value) : List Value :=
  di.filter (fun v => valueMemB v dj)

/-- Intersection membership, one direction: a filtered value lies in
    `di`. -/
theorem mem_interVals_left {v : Value} {di dj : List Value}
    (h : v ∈ interVals di dj) : v ∈ di :=
  (List.mem_filter.mp h).1

/-- Intersection membership, the other direction: a filtered value
    lies in `dj`. -/
theorem mem_interVals_right {v : Value} {di dj : List Value}
    (h : v ∈ interVals di dj) : v ∈ dj := by
  have hb := (List.mem_filter.mp h).2
  exact valueMemB_iff.mp hb

/-- Intersection membership, introduction: a value of both domains
    lies in the intersection. -/
theorem mem_interVals_of {v : Value} {di dj : List Value}
    (h1 : v ∈ di) (h2 : v ∈ dj) : v ∈ interVals di dj :=
  List.mem_filter.mpr ⟨h1, valueMemB_iff.mpr h2⟩

/-- `single? [x] = some x`, and `none` for every other shape. -/
def single? : List Value → Option Value
  | [x] => some x
  | _ => none

/-- `single?` extracts exactly the singleton lists. -/
theorem single?_eq_some_iff {l : List Value} {x : Value} :
    single? l = some x ↔ l = [x] := by
  cases l with
  | nil => simp [single?]
  | cons y ys =>
      cases ys with
      | nil =>
          constructor
          · intro h
            have hsome : some y = some x := h
            rw [Option.some.inj hsome]
          · intro h
            injection h with hyx
            subst hyx
            rfl
      | cons z zs => simp [single?]

/-- Remove every occurrence of `x` from a domain, under structural
    value equality. -/
def removeVal (x : Value) (d : List Value) : List Value :=
  d.filter (fun v => !x.eqB v)

/-- A kept value was in the domain. -/
theorem mem_removeVal {v x : Value} {d : List Value}
    (h : v ∈ removeVal x d) : v ∈ d :=
  (List.mem_filter.mp h).1

/-- A value of the domain distinct from `x` is kept. -/
theorem mem_removeVal_of {v x : Value} {d : List Value}
    (h1 : v ∈ d) (h2 : x.eqB v = false) : v ∈ removeVal x d :=
  List.mem_filter.mpr ⟨h1, by simp [h2]⟩

/-- Keep only the values at most the bound `b`. -/
def atMostVals (b : Int) (d : List Value) : List Value :=
  d.filter (fun v => match v with | .int p => decide (p ≤ b) | _ => false)

/-- Keep only the values at least the bound `b`. -/
def atLeastVals (b : Int) (d : List Value) : List Value :=
  d.filter (fun v => match v with | .int p => decide (b ≤ p) | _ => false)

/-- Membership characterization of `atMostVals`. -/
theorem mem_atMostVals {v : Value} {b : Int} {d : List Value} :
    v ∈ atMostVals b d ↔ v ∈ d ∧ ∃ p, v = .int p ∧ p ≤ b := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := List.mem_filter.mp h
    cases v with
    | int p =>
        rw [decide_eq_true_eq] at h2
        exact ⟨h1, p, rfl, h2⟩
    | bool w => exact absurd h2 (by simp)
    | setOfInt w => exact absurd h2 (by simp)
    | array w => exact absurd h2 (by simp)
  · rintro ⟨h1, p, rfl, hle⟩
    exact List.mem_filter.mpr ⟨h1, by simp [hle]⟩

/-- Membership characterization of `atLeastVals`. -/
theorem mem_atLeastVals {v : Value} {b : Int} {d : List Value} :
    v ∈ atLeastVals b d ↔ v ∈ d ∧ ∃ p, v = .int p ∧ b ≤ p := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := List.mem_filter.mp h
    cases v with
    | int p =>
        rw [decide_eq_true_eq] at h2
        exact ⟨h1, p, rfl, h2⟩
    | bool w => exact absurd h2 (by simp)
    | setOfInt w => exact absurd h2 (by simp)
    | array w => exact absurd h2 (by simp)
  · rintro ⟨h1, p, rfl, hle⟩
    exact List.mem_filter.mpr ⟨h1, by simp [hle]⟩

/-- Membership characterization of the composed interval filter
    `atLeastVals lo (atMostVals hi d)` — the bounds-narrowing step of
    `propPlusSlot` and friends. -/
theorem mem_atLeastVals_atMostVals {v : Value} {lo hi : Int} {d : List Value} :
    v ∈ atLeastVals lo (atMostVals hi d) ↔
      v ∈ d ∧ ∃ p, v = .int p ∧ lo ≤ p ∧ p ≤ hi := by
  rw [mem_atLeastVals]
  constructor
  · rintro ⟨h1, p, rfl, hlo⟩
    obtain ⟨h2, p2, hp2, hhi⟩ := mem_atMostVals.mp h1
    have hpp : p = p2 := by injection hp2
    subst hpp
    exact ⟨h2, p, rfl, hlo, hhi⟩
  · rintro ⟨h1, p, rfl, hlo, hhi⟩
    exact ⟨mem_atMostVals.mpr ⟨h1, p, rfl, hhi⟩, p, rfl, hlo⟩


namespace Internal

/-- The executable order test: `true` exactly on integer pairs with
    `p ≤ q`. -/
def intLEB : Value → Value → Bool
  | .int p, .int q => decide (p ≤ q)
  | _, _ => false

theorem intLEB_iff {x y : Value} :
    intLEB x y = true ↔ ∃ p q, x = .int p ∧ y = .int q ∧ p ≤ q := by
  cases x with
  | int p =>
      cases y with
      | int q =>
          simp only [intLEB, decide_eq_true_eq]
          constructor
          · intro hle
            exact ⟨p, q, rfl, rfl, hle⟩
          · rintro ⟨p', q', hp, hq, hle⟩
            simp only [Value.int.injEq] at hp hq
            omega
      | bool b => simp [intLEB]
      | setOfInt s => simp [intLEB]
      | array ws => simp [intLEB]
  | bool b => simp [intLEB]
  | setOfInt s => simp [intLEB]
  | array ws => simp [intLEB]

/-- Combine a running maximum with a new integer. -/
def maxOpt (o : Option Int) (p : Int) : Option Int :=
  match o with
  | none => some p
  | some m => some (if p < m then m else p)

/-- Combine a running minimum with a new integer. -/
def minOpt (o : Option Int) (p : Int) : Option Int :=
  match o with
  | none => some p
  | some m => some (if p < m then p else m)

def stepMax (v : Value) (o : Option Int) : Option Int :=
  match v with
  | .int p => maxOpt o p
  | _ => o

def stepMin (v : Value) (o : Option Int) : Option Int :=
  match v with
  | .int p => minOpt o p
  | _ => o

end Internal

/-- The largest integer of a domain, if any (non-integer values are
    ignored). -/
def domMax : List Value → Option Int
  | [] => none
  | v :: vs => stepMax v (domMax vs)

/-- The smallest integer of a domain, if any. -/
def domMin : List Value → Option Int
  | [] => none
  | v :: vs => stepMin v (domMin vs)

/-- **`domMax` bounds the domain**: an integer member of the domain is
    at most the reported maximum. -/
theorem domMax_of_mem {p : Int} {l : List Value} (hmem : Value.int p ∈ l) :
    ∃ m, domMax l = some m ∧ p ≤ m := by
  induction l with
  | nil => exact absurd hmem (by simp)
  | cons v vs ih =>
      rcases List.mem_cons.mp hmem with heq | hin
      · subst heq
        cases hrest : domMax vs with
        | none =>
            refine ⟨p, ?_, by omega⟩
            simp only [domMax, stepMax, maxOpt, hrest]
        | some r =>
            refine ⟨if p < r then r else p, ?_, ?_⟩
            · simp only [domMax, stepMax, maxOpt, hrest]
            · split <;> omega
      · obtain ⟨m, hm, hle⟩ := ih hin
        cases v with
        | int q =>
            refine ⟨if q < m then m else q, ?_, ?_⟩
            · simp only [domMax, stepMax, maxOpt, hm]
            · split <;> omega
        | bool b =>
            refine ⟨m, ?_, hle⟩
            simp only [domMax, stepMax, hm]
        | setOfInt s =>
            refine ⟨m, ?_, hle⟩
            simp only [domMax, stepMax, hm]
        | array ws =>
            refine ⟨m, ?_, hle⟩
            simp only [domMax, stepMax, hm]

/-- **`domMin` bounds the domain**: an integer member of the domain is
    at least the reported minimum. -/
theorem domMin_of_mem {p : Int} {l : List Value} (hmem : Value.int p ∈ l) :
    ∃ m, domMin l = some m ∧ m ≤ p := by
  induction l with
  | nil => exact absurd hmem (by simp)
  | cons v vs ih =>
      rcases List.mem_cons.mp hmem with heq | hin
      · subst heq
        cases hrest : domMin vs with
        | none =>
            refine ⟨p, ?_, by omega⟩
            simp only [domMin, stepMin, minOpt, hrest]
        | some r =>
            refine ⟨if p < r then p else r, ?_, ?_⟩
            · simp only [domMin, stepMin, minOpt, hrest]
            · split <;> omega
      · obtain ⟨m, hm, hle⟩ := ih hin
        cases v with
        | int q =>
            refine ⟨if q < m then q else m, ?_, ?_⟩
            · simp only [domMin, stepMin, minOpt, hm]
            · split <;> omega
        | bool b =>
            refine ⟨m, ?_, hle⟩
            simp only [domMin, stepMin, hm]
        | setOfInt s =>
            refine ⟨m, ?_, hle⟩
            simp only [domMin, stepMin, hm]
        | array ws =>
            refine ⟨m, ?_, hle⟩
            simp only [domMin, stepMin, hm]

/-! ## Integer arithmetic helpers for the arithmetic propagators -/


namespace Internal

/-- Local alias for core's transitivity of `Int` order. -/
theorem le_trans {a b c : Int} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  Int.le_trans h1 h2

/-- Local alias for core's reflexivity of `Int` order. -/
theorem le_refl (a : Int) : a ≤ a := Int.le_refl a

/-- Local alias for core's "not `a ≤ b` forces `b ≤ a`". -/
theorem le_of_not_ge {a b : Int} (h : ¬ a ≤ b) : b ≤ a :=
  Int.le_of_not_le h

/-- Local alias for core's left monotonicity of `max`. -/
theorem le_max_left (a b : Int) : a ≤ max a b := Int.le_max_left a b

/-- Local alias for core's right monotonicity of `max`. -/
theorem le_max_right (a b : Int) : b ≤ max a b := Int.le_max_right a b

/-- Local alias for core's left lower bound of `min`. -/
theorem min_le_left (a b : Int) : min a b ≤ a := Int.min_le_left a b

/-- Local alias for core's right lower bound of `min`. -/
theorem min_le_right (a b : Int) : min a b ≤ b := Int.min_le_right a b

/-- Local alias for core's commutativity of `max`. -/
theorem max_comm (a b : Int) : max a b = max b a := Int.max_comm a b

/-- Local alias for core's commutativity of `min`. -/
theorem min_comm (a b : Int) : min a b = min b a := Int.min_comm a b

/-- Local alias for core's `max a b ≤ c` iff-style introduction. -/
theorem max_le {a b c : Int} (h1 : a ≤ c) (h2 : b ≤ c) : max a b ≤ c :=
  Int.max_le.mpr ⟨h1, h2⟩

/-- Monotonicity of `min` in both arguments (there is no core
    `Int.min_le_min`, so this is proved from the `min` definition). -/
theorem min_le_min {a b c d : Int} (h1 : a ≤ c) (h2 : b ≤ d) :
    min a b ≤ min c d := by
  simp only [Int.min_def]
  split
  all_goals split
  all_goals omega

/-- Monotonicity of `max` in both arguments (there is no core
    `Int.max_le_max`, so this is proved from the `max` definition). -/
theorem max_le_max {a b c d : Int} (h1 : a ≤ c) (h2 : b ≤ d) :
    max a b ≤ max c d := by
  simp only [Int.max_def]
  split
  all_goals split
  all_goals omega

/-- `c ≤ min a b` iff `c ≤ a` and `c ≤ b` (there is no core
    `Int.le_min_iff`, so this is proved from the `min` definition). -/
theorem le_min_iff {a b c : Int} : c ≤ min a b ↔ c ≤ a ∧ c ≤ b := by
  simp only [Int.min_def]
  constructor
  · intro h
    split at h
    · exact ⟨h, by omega⟩
    · exact ⟨by omega, h⟩
  · intro ⟨ha, hb⟩
    split
    · exact ha
    · exact hb

/-- Local alias for core's antitone `neg`. -/
theorem neg_le_neg {a b : Int} (h : a ≤ b) : -b ≤ -a := Int.neg_le_neg h

/-- Local alias for core's commutativity of `Int` multiplication. -/
theorem mul_comm (a b : Int) : a * b = b * a := Int.mul_comm a b

/-- Local alias for core's multiplication monotonicity (right factor
    nonnegative). -/
theorem mul_le_mul_of_nonneg_right {a b c : Int} (h1 : a ≤ b) (hc : 0 ≤ c) :
    a * c ≤ b * c := Int.mul_le_mul_of_nonneg_right h1 hc

/-- Local alias for core's multiplication monotonicity (right factor
    nonpositive, reversing). -/
theorem mul_le_mul_of_nonpos_right {a b c : Int} (h : b ≤ a) (hc : c ≤ 0) :
    a * c ≤ b * c := Int.mul_le_mul_of_nonpos_right h hc

/-- Local alias for core's multiplication monotonicity (left factor
    nonnegative). -/
theorem mul_le_mul_of_nonneg_left {a b c : Int} (h1 : a ≤ b) (hc : 0 ≤ c) :
    c * a ≤ c * b := Int.mul_le_mul_of_nonneg_left h1 hc

/-- Local alias for core's multiplication monotonicity (left factor
    nonpositive, reversing). -/
theorem mul_le_mul_of_nonpos_left {a b c : Int} (ha : a ≤ 0) (h : c ≤ b) :
    a * b ≤ a * c := Int.mul_le_mul_of_nonpos_left ha h

end Internal

/-- Integer absolute value as the checker's `int_abs` computes it: `p`
    if `p ≥ 0`, `-p` otherwise. -/
def absValue (p : Int) : Int := if p < 0 then -p else p


namespace Internal

/-- `absValue` is nonnegative. -/
theorem absValue_nonneg (p : Int) : 0 ≤ absValue p := by
  unfold absValue
  by_cases hp : p < 0
  · rw [if_pos hp]
    omega
  · rw [if_neg hp]
    omega

/-- A value is at most its own absolute value. -/
theorem le_absValue (p : Int) : p ≤ absValue p := by
  unfold absValue
  by_cases hp : p < 0
  · rw [if_pos hp]
    omega
  · rw [if_neg hp]
    omega

/-- A value is at least the negation of its own absolute value. -/
theorem neg_absValue_le (p : Int) : -absValue p ≤ p := by
  unfold absValue
  by_cases hp : p < 0
  · rw [if_pos hp]
    omega
  · rw [if_neg hp]
    omega

/-- An integer between `-M` and `M` has absolute value at most `M`. -/
theorem absValue_le_of_bounds {p M : Int} (h1 : -M ≤ p) (h2 : p ≤ M) :
    absValue p ≤ M := by
  unfold absValue
  by_cases hp : p < 0
  · rw [if_pos hp]
    omega
  · rw [if_neg hp]
    exact h2

/-- The absolute value of a member of the integer interval `[ilo, ihi]`
    is at most the larger of the two endpoint absolute values. -/
theorem absValue_le_range {ilo ihi p : Int}
    (h1 : ilo ≤ p) (h2 : p ≤ ihi) :
    absValue p ≤ max (absValue ilo) (absValue ihi) := by
  apply absValue_le_of_bounds
  · have h1' : -absValue ilo ≤ ilo := neg_absValue_le ilo
    have h1'' : -max (absValue ilo) (absValue ihi) ≤ -absValue ilo :=
      neg_le_neg (le_max_left (absValue ilo) (absValue ihi))
    exact le_trans h1'' (le_trans h1' h1)
  · exact le_trans h2 (le_trans (le_absValue ihi) (le_max_right _ _))

/-- Multiplication by a fixed value: a value of `[a, b]` times a fixed
    `c` is at most the larger of the two corner products. -/
theorem mul_le_max_two {a b c x : Int} (hx : a ≤ x) (hx' : x ≤ b) :
    x * c ≤ max (a * c) (b * c) := by
  by_cases hc : 0 ≤ c
  · have h1 : x * c ≤ b * c := mul_le_mul_of_nonneg_right hx' hc
    exact le_trans h1 (le_max_right _ _)
  · have hc' : c ≤ 0 := le_of_not_ge hc
    have h1 : x * c ≤ a * c := mul_le_mul_of_nonpos_right hx hc'
    exact le_trans h1 (le_max_left _ _)

/-- Multiplication by a fixed value: a value of `[a, b]` times a fixed
    `c` is at least the smaller of the two corner products. -/
theorem min_two_le_mul {a b c x : Int} (hx : a ≤ x) (hx' : x ≤ b) :
    min (a * c) (b * c) ≤ x * c := by
  by_cases hc : 0 ≤ c
  · have h1 : a * c ≤ x * c := mul_le_mul_of_nonneg_right hx hc
    exact le_trans (min_le_left _ _) h1
  · have hc' : c ≤ 0 := le_of_not_ge hc
    have h1 : b * c ≤ x * c := mul_le_mul_of_nonpos_right hx' hc'
    exact le_trans (min_le_right _ _) h1

/-- Product with one argument fixed at `p`: as the other argument runs
    over `[jlo, jhi]`, the product stays between the two corner
    products. -/
theorem mul_one_interval {p q jlo jhi : Int} (h1 : jlo ≤ q) (h2 : q ≤ jhi) :
    min (p * jlo) (p * jhi) ≤ p * q ∧ p * q ≤ max (p * jlo) (p * jhi) := by
  constructor
  · by_cases hp : 0 ≤ p
    · have h1' : p * jlo ≤ p * q := mul_le_mul_of_nonneg_left h1 hp
      exact le_trans (min_le_left _ _) h1'
    · have hp' : p ≤ 0 := le_of_not_ge hp
      have h1' : p * jhi ≤ p * q := mul_le_mul_of_nonpos_left hp' h2
      exact le_trans (min_le_right _ _) h1'
  · by_cases hp : 0 ≤ p
    · have h2' : p * q ≤ p * jhi := mul_le_mul_of_nonneg_left h2 hp
      exact le_trans h2' (le_max_right _ _)
    · have hp' : p ≤ 0 := le_of_not_ge hp
      have h2' : p * q ≤ p * jlo := mul_le_mul_of_nonpos_left hp' h1
      exact le_trans h2' (le_max_left _ _)

/-- The four-corner lower product bound of the intervals `[a, b]` and
    `[c, d]`. -/
def cornerMin (a b c d : Int) : Int :=
  min (min (a * c) (a * d)) (min (b * c) (b * d))

/-- The four-corner upper product bound of the intervals `[a, b]` and
    `[c, d]`. -/
def cornerMax (a b c d : Int) : Int :=
  max (max (a * c) (a * d)) (max (b * c) (b * d))

/-- Two values in `[a, b] × [c, d]` have a product at most the largest
    corner product. -/
theorem mul_le_cornerMax {a b c d x y : Int} (hx : a ≤ x) (hx' : x ≤ b)
    (hy : c ≤ y) (hy' : y ≤ d) :
    x * y ≤ cornerMax a b c d := by
  have H1 : x * y ≤ max (a * y) (b * y) := mul_le_max_two hx hx'
  have hc : a * y ≤ cornerMax a b c d := by
    have h2 : y * a ≤ max (c * a) (d * a) := mul_le_max_two hy hy'
    have h2' : a * y ≤ max (a * c) (a * d) := by simpa [mul_comm] using h2
    exact le_trans h2' (le_max_left (max (a * c) (a * d)) (max (b * c) (b * d)))
  have hd : b * y ≤ cornerMax a b c d := by
    have h2 : y * b ≤ max (c * b) (d * b) := mul_le_max_two hy hy'
    have h2' : b * y ≤ max (b * c) (b * d) := by simpa [mul_comm] using h2
    exact le_trans h2' (le_max_right (max (a * c) (a * d)) (max (b * c) (b * d)))
  exact le_trans H1 (max_le hc hd)

/-- Two values in `[a, b] × [c, d]` have a product at least the
    smallest corner product. -/
theorem cornerMin_le_mul {a b c d x y : Int} (hx : a ≤ x) (hx' : x ≤ b)
    (hy : c ≤ y) (hy' : y ≤ d) :
    cornerMin a b c d ≤ x * y := by
  have H1 : min (a * y) (b * y) ≤ x * y := min_two_le_mul hx hx'
  have ha : cornerMin a b c d ≤ a * y := by
    have h2 : min (c * a) (d * a) ≤ y * a := min_two_le_mul hy hy'
    have h2' : min (a * c) (a * d) ≤ a * y := by simpa [mul_comm] using h2
    exact le_trans (min_le_left (min (a * c) (a * d)) (min (b * c) (b * d))) h2'
  have hb : cornerMin a b c d ≤ b * y := by
    have h2 : min (c * b) (d * b) ≤ y * b := min_two_le_mul hy hy'
    have h2' : min (b * c) (b * d) ≤ b * y := by simpa [mul_comm] using h2
    exact le_trans (min_le_right (min (a * c) (a * d)) (min (b * c) (b * d))) h2'
  exact le_trans (le_min_iff.mpr ⟨ha, hb⟩) H1

end Internal

/-! ## Deduplication and the pigeonhole lemma -/

/-- First-occurrence deduplication of a value list under the checker's
    structural equality — the union-of-domains representation of the
    `allDiff` propagator. -/
def dedupVals : List Value → List Value
  | [] => []
  | v :: vs =>
      let rest := dedupVals vs
      if valueMemB v rest then rest else v :: rest

/-- Deduplication preserves membership. -/
theorem mem_dedupVals (v : Value) : ∀ (l : List Value),
    v ∈ dedupVals l ↔ v ∈ l := by
  intro l
  induction l with
  | nil => simp [dedupVals]
  | cons w ws ih =>
      simp only [dedupVals]
      by_cases hc : valueMemB w (dedupVals ws) = true
      · rw [if_pos hc]
        have hwm : w ∈ dedupVals ws := valueMemB_iff.mp hc
        constructor
        · intro h
          exact List.mem_cons.mpr (Or.inr (ih.mp h))
        · intro h
          rcases List.mem_cons.mp h with rfl | hin
          · exact hwm
          · exact ih.mpr hin
      · rw [if_neg hc]
        constructor
        · intro h
          rcases List.mem_cons.mp h with rfl | hin
          · exact List.mem_cons.mpr (Or.inl rfl)
          · exact List.mem_cons.mpr (Or.inr (ih.mp hin))
        · intro h
          rcases List.mem_cons.mp h with rfl | hin
          · exact List.mem_cons.mpr (Or.inl rfl)
          · exact List.mem_cons.mpr (Or.inr (ih.mpr hin))

/-- The deduplicated list is duplicate-free. -/
theorem nodup_dedupVals : ∀ (l : List Value), (dedupVals l).Nodup := by
  intro l
  induction l with
  | nil => exact List.nodup_nil
  | cons v vs ih =>
      simp only [dedupVals]
      by_cases hc : valueMemB v (dedupVals vs) = true
      · rw [if_pos hc]; exact ih
      · rw [if_neg hc, List.nodup_cons]
        exact ⟨fun hmem => absurd (valueMemB_iff.mpr hmem) hc, ih⟩

/-- Removing all occurrences of a member shortens the list by at least
    one. -/
private theorem removeVal_length_le_of_mem {x : Value} : ∀ (w : List Value), x ∈ w →
    (removeVal x w).length + 1 ≤ w.length := by
  intro w
  induction w with
  | nil => intro h; exact absurd h (by simp)
  | cons y ys ih =>
      intro hmem
      by_cases hxy : x = y
      · -- the head equals x: the filter drops it
        subst hxy
        have hnot : ¬((!x.eqB x) = true) := by
          have hd : (!x.eqB x) = false := by
            rw [value_eqB_refl]; rfl
          rw [hd]; intro h; simp at h
        have hstep : removeVal x (x :: ys) = removeVal x ys :=
          List.filter_cons_of_neg hnot
        rw [hstep]
        have hle : (removeVal x ys).length ≤ ys.length := List.length_filter_le _ ys
        simp only [List.length_cons]
        omega
      · -- the head differs from x: the filter keeps it, and x sits in ys
        have hin : x ∈ ys := by
          rcases List.mem_cons.mp hmem with heq | hin
          · exact absurd heq hxy
          · exact hin
        have hpos : (!x.eqB y) = true := by
          have hb : x.eqB y = false := eqB_false_of_ne hxy
          rw [hb]; rfl
        have hstep : removeVal x (y :: ys) = y :: removeVal x ys :=
          List.filter_cons_of_pos hpos
        rw [hstep]
        have hrec := ih hin
        simp only [List.length_cons]
        omega

/-- **The list pigeonhole**: a duplicate-free list whose values all
    lie in another duplicate-free list is at most as long.  This is the
    counting heart of the `allDiff` propagator's contradiction case:
    the pairwise-distinct values read at the slots inject into the
    distinct values of the union of their domains. -/
theorem nodup_subset_length_le : ∀ (l w : List Value), l.Nodup → (∀ x ∈ l, x ∈ w) →
    w.Nodup → l.length ≤ w.length := by
  intro l
  induction l with
  | nil => intro w _ _ _; exact Nat.zero_le _
  | cons x xs ih =>
      intro w hnd hsub hw
      rw [List.nodup_cons] at hnd
      obtain ⟨hxne, hxs⟩ := hnd
      have hxw : x ∈ w := hsub x (by simp)
      have hsub' : ∀ y ∈ xs, y ∈ removeVal x w := by
        intro y hy
        exact mem_removeVal_of (hsub y (by simp [hy]))
          (eqB_false_of_ne (fun h => hxne (h ▸ hy)))
      have hwn : (removeVal x w).Nodup := by
        have hsub2 : removeVal x w <+ w := by
          show (List.filter (fun v => !x.eqB v) w) <+ w
          exact List.filter_sublist
        exact List.Nodup.sublist hsub2 hw
      have hrec := ih (removeVal x w) hxs hsub' hwn
      have hlen := removeVal_length_le_of_mem w hxw
      simp only [List.length_cons]
      omega

/-- **`valuesAllDifferent` decides duplicate-freedom**: the checker's
    quadratic pairwise-distinctness test holds exactly when the value
    list is `Nodup` — the bridge between `all_different`'s semantics
    and the `allDiff` slot constraint. -/
theorem valuesAllDifferent_iff_nodup : ∀ (l : List Value),
    valuesAllDifferent l = true ↔ l.Nodup := by
  intro l
  induction l with
  | nil => exact ⟨fun _ => List.nodup_nil, fun _ => rfl⟩
  | cons x xs ih =>
      rw [valuesAllDifferent, List.nodup_cons, Bool.and_eq_true, Bool.not_eq_true']
      constructor
      · rintro ⟨hany, hxs⟩
        refine ⟨?_, ih.mp hxs⟩
        intro hmem
        have htrue : (xs.any (fun y => x.eqB y)) = true :=
          List.any_eq_true.mpr ⟨x, hmem, value_eqB_refl x⟩
        rw [hany] at htrue
        exact Bool.noConfusion htrue
      · rintro ⟨hnd, hxs⟩
        refine ⟨?_, ih.mpr hxs⟩
        show (xs.any (fun y => x.eqB y)) = false
        cases ha : (xs.any (fun y => x.eqB y)) with
        | false => rfl
        | true =>
            rw [List.any_eq_true] at ha
            obtain ⟨w, hw, hweq⟩ := ha
            rw [value_eqB_iff] at hweq
            exact absurd (hweq ▸ hw) hnd


end LeanFzn.Solver.Propagation.DomainFiltering

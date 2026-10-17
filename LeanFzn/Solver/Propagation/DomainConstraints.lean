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

/-- Structural value equality is `false` exactly on distinct
    values. -/
private theorem eqB_false_iff_ne {x y : Value} : x.eqB y = false ↔ x ≠ y := by
  rw [← Bool.not_eq_true', ne_eq, ← value_eqB_iff]
  simp

/-- The `→` direction of `eqB_false_iff_ne`. -/
private theorem eqB_false_of_ne {x y : Value} (hne : x ≠ y) :
    x.eqB y = false := eqB_false_iff_ne.mpr hne

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

/-- The executable order test: `true` exactly on integer pairs with
    `p ≤ q`. -/
private def intLEB : Value → Value → Bool
  | .int p, .int q => decide (p ≤ q)
  | _, _ => false

private theorem intLEB_iff {x y : Value} :
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
private def maxOpt (o : Option Int) (p : Int) : Option Int :=
  match o with
  | none => some p
  | some m => some (if p < m then m else p)

/-- Combine a running minimum with a new integer. -/
private def minOpt (o : Option Int) (p : Int) : Option Int :=
  match o with
  | none => some p
  | some m => some (if p < m then p else m)

private def stepMax (v : Value) (o : Option Int) : Option Int :=
  match v with
  | .int p => maxOpt o p
  | _ => o

private def stepMin (v : Value) (o : Option Int) : Option Int :=
  match v with
  | .int p => minOpt o p
  | _ => o

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

/-- Local alias for core's transitivity of `Int` order. -/
private theorem le_trans {a b c : Int} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  Int.le_trans h1 h2

/-- Local alias for core's reflexivity of `Int` order. -/
private theorem le_refl (a : Int) : a ≤ a := Int.le_refl a

/-- Local alias for core's "not `a ≤ b` forces `b ≤ a`". -/
private theorem le_of_not_ge {a b : Int} (h : ¬ a ≤ b) : b ≤ a :=
  Int.le_of_not_le h

/-- Local alias for core's left monotonicity of `max`. -/
private theorem le_max_left (a b : Int) : a ≤ max a b := Int.le_max_left a b

/-- Local alias for core's right monotonicity of `max`. -/
private theorem le_max_right (a b : Int) : b ≤ max a b := Int.le_max_right a b

/-- Local alias for core's left lower bound of `min`. -/
private theorem min_le_left (a b : Int) : min a b ≤ a := Int.min_le_left a b

/-- Local alias for core's right lower bound of `min`. -/
private theorem min_le_right (a b : Int) : min a b ≤ b := Int.min_le_right a b

/-- Local alias for core's commutativity of `max`. -/
private theorem max_comm (a b : Int) : max a b = max b a := Int.max_comm a b

/-- Local alias for core's commutativity of `min`. -/
private theorem min_comm (a b : Int) : min a b = min b a := Int.min_comm a b

/-- Local alias for core's `max a b ≤ c` iff-style introduction. -/
private theorem max_le {a b c : Int} (h1 : a ≤ c) (h2 : b ≤ c) : max a b ≤ c :=
  Int.max_le.mpr ⟨h1, h2⟩

/-- Monotonicity of `min` in both arguments (there is no core
    `Int.min_le_min`, so this is proved from the `min` definition). -/
private theorem min_le_min {a b c d : Int} (h1 : a ≤ c) (h2 : b ≤ d) :
    min a b ≤ min c d := by
  simp only [Int.min_def]
  split
  all_goals split
  all_goals omega

/-- Monotonicity of `max` in both arguments (there is no core
    `Int.max_le_max`, so this is proved from the `max` definition). -/
private theorem max_le_max {a b c d : Int} (h1 : a ≤ c) (h2 : b ≤ d) :
    max a b ≤ max c d := by
  simp only [Int.max_def]
  split
  all_goals split
  all_goals omega

/-- `c ≤ min a b` iff `c ≤ a` and `c ≤ b` (there is no core
    `Int.le_min_iff`, so this is proved from the `min` definition). -/
private theorem le_min_iff {a b c : Int} : c ≤ min a b ↔ c ≤ a ∧ c ≤ b := by
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
private theorem neg_le_neg {a b : Int} (h : a ≤ b) : -b ≤ -a := Int.neg_le_neg h

/-- Local alias for core's commutativity of `Int` multiplication. -/
private theorem mul_comm (a b : Int) : a * b = b * a := Int.mul_comm a b

/-- Local alias for core's multiplication monotonicity (right factor
    nonnegative). -/
private theorem mul_le_mul_of_nonneg_right {a b c : Int} (h1 : a ≤ b) (hc : 0 ≤ c) :
    a * c ≤ b * c := Int.mul_le_mul_of_nonneg_right h1 hc

/-- Local alias for core's multiplication monotonicity (right factor
    nonpositive, reversing). -/
private theorem mul_le_mul_of_nonpos_right {a b c : Int} (h : b ≤ a) (hc : c ≤ 0) :
    a * c ≤ b * c := Int.mul_le_mul_of_nonpos_right h hc

/-- Local alias for core's multiplication monotonicity (left factor
    nonnegative). -/
private theorem mul_le_mul_of_nonneg_left {a b c : Int} (h1 : a ≤ b) (hc : 0 ≤ c) :
    c * a ≤ c * b := Int.mul_le_mul_of_nonneg_left h1 hc

/-- Local alias for core's multiplication monotonicity (left factor
    nonpositive, reversing). -/
private theorem mul_le_mul_of_nonpos_left {a b c : Int} (ha : a ≤ 0) (h : c ≤ b) :
    a * b ≤ a * c := Int.mul_le_mul_of_nonpos_left ha h

/-- Integer absolute value as the checker's `int_abs` computes it: `p`
    if `p ≥ 0`, `-p` otherwise. -/
def absValue (p : Int) : Int := if p < 0 then -p else p

/-- `absValue` is nonnegative. -/
private theorem absValue_nonneg (p : Int) : 0 ≤ absValue p := by
  unfold absValue
  by_cases hp : p < 0
  · rw [if_pos hp]
    omega
  · rw [if_neg hp]
    omega

/-- A value is at most its own absolute value. -/
private theorem le_absValue (p : Int) : p ≤ absValue p := by
  unfold absValue
  by_cases hp : p < 0
  · rw [if_pos hp]
    omega
  · rw [if_neg hp]
    omega

/-- A value is at least the negation of its own absolute value. -/
private theorem neg_absValue_le (p : Int) : -absValue p ≤ p := by
  unfold absValue
  by_cases hp : p < 0
  · rw [if_pos hp]
    omega
  · rw [if_neg hp]
    omega

/-- An integer between `-M` and `M` has absolute value at most `M`. -/
private theorem absValue_le_of_bounds {p M : Int} (h1 : -M ≤ p) (h2 : p ≤ M) :
    absValue p ≤ M := by
  unfold absValue
  by_cases hp : p < 0
  · rw [if_pos hp]
    omega
  · rw [if_neg hp]
    exact h2

/-- The absolute value of a member of the integer interval `[ilo, ihi]`
    is at most the larger of the two endpoint absolute values. -/
private theorem absValue_le_range {ilo ihi p : Int}
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
private theorem mul_le_max_two {a b c x : Int} (hx : a ≤ x) (hx' : x ≤ b) :
    x * c ≤ max (a * c) (b * c) := by
  by_cases hc : 0 ≤ c
  · have h1 : x * c ≤ b * c := mul_le_mul_of_nonneg_right hx' hc
    exact le_trans h1 (le_max_right _ _)
  · have hc' : c ≤ 0 := le_of_not_ge hc
    have h1 : x * c ≤ a * c := mul_le_mul_of_nonpos_right hx hc'
    exact le_trans h1 (le_max_left _ _)

/-- Multiplication by a fixed value: a value of `[a, b]` times a fixed
    `c` is at least the smaller of the two corner products. -/
private theorem min_two_le_mul {a b c x : Int} (hx : a ≤ x) (hx' : x ≤ b) :
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
private theorem mul_one_interval {p q jlo jhi : Int} (h1 : jlo ≤ q) (h2 : q ≤ jhi) :
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
private def cornerMin (a b c d : Int) : Int :=
  min (min (a * c) (a * d)) (min (b * c) (b * d))

/-- The four-corner upper product bound of the intervals `[a, b]` and
    `[c, d]`. -/
private def cornerMax (a b c d : Int) : Int :=
  max (max (a * c) (a * d)) (max (b * c) (b * d))

/-- Two values in `[a, b] × [c, d]` have a product at most the largest
    corner product. -/
private theorem mul_le_cornerMax {a b c d x y : Int} (hx : a ≤ x) (hx' : x ≤ b)
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
private theorem cornerMin_le_mul {a b c d x y : Int} (hx : a ≤ x) (hx' : x ≤ b)
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

/-! ## Constraint representation -/

/-- An integer operand of a GENERAL arithmetic constraint: a slot
    position or an integer literal. The general shapes of `int_max` /
    `int_min` / `int_div` / `int_mod` accept either, and the array
    forms `array_int_maximum(m, xs)` / `array_int_minimum(m, xs)`
    (result slot `m` first) are the all-slot special case. -/
inductive DomIntArg where
  /-- The value at a slot position. -/
  | slot (i : Nat)
  /-- An integer literal. -/
  | lit (k : Int)
  deriving DecidableEq, Repr

namespace DomIntArg

/-- The value an operand reads from an assignment: the slot's value (the
    bang read, matching the `linEq`/`allDiff` convention) or the
    literal's integer. -/
def read (a : List Value) : DomIntArg → Value
  | .slot i => a[i]!
  | .lit k => .int k

/-- The slot positions an operand names. -/
def slots : DomIntArg → List Nat
  | .slot i => [i]
  | .lit _ => []

/-- `read` unfolded at a slot. -/
theorem read_slot (a : List Value) (i : Nat) :
    read a (.slot i) = a[i]! := rfl

/-- `read` unfolded at a literal. -/
theorem read_lit (a : List Value) (k : Int) :
    read a (.lit k) = .int k := rfl

end DomIntArg

/-- A constraint over slot positions: the declarative representation a
    propagator narrows domains for.  The positions index the search
    slots of `LeanFzn/Compiler/Domain.lean`; each constructor matches the
    corresponding FlatZinc predicate on scalar values (`int_eq`,
    `int_eq(x, c)` after constant propagation, `int_plus` on three
    slots, `int_le(x, c)` / `int_le(c, x)` against a constant, and
    `all_different` over an explicit array of slots).  The arithmetic
    predicates extend it: `timesSlot i j k` (slot `i` times slot `j`
    equals slot `k` — `int_times` style), `minSlot i j k` / `maxSlot i
    j k` (slot `k` carries the minimum / maximum of slots `i` and `j`
    — `int_min` / `int_max` style), and `absSlot i k` (slot `k`
    carries the absolute value of slot `i` — `int_abs` style). -/
inductive DomConstraint where
  /-- Slots `i` and `j` must carry equal values (`int_eq` style). -/
  | eqSlot (i j : Nat)
  /-- Slots `i` and `j` must carry different values (`int_ne` style). -/
  | neSlot (i j : Nat)
  /-- Slot `i`'s value must be at most slot `j`'s (`int_le` style). -/
  | leSlot (i j : Nat)
  /-- Slot `i` must carry the constant `v`. -/
  | constEq (i : Nat) (v : Value)
  /-- Slot `i`'s value plus slot `j`'s must equal slot `k`'s
      (`int_plus` style). -/
  | plusSlot (i j k : Nat)
  /-- Slot `i`'s value must be at most the integer `c`
      (`int_le(x, c)` style). -/
  | leConstHi (i : Nat) (c : Int)
  /-- Slot `i`'s value must be at least the integer `c`
      (`int_le(c, x)` style). -/
  | leConstLo (i : Nat) (c : Int)
  /-- The slots at the positions of `is` must carry pairwise
      different values (`all_different` style). -/
  | allDiff (is : List Nat)
  /-- Slot `i`'s value times slot `j`'s must equal slot `k`'s
      (`int_times` style). -/
  | timesSlot (i j k : Nat)
  /-- Slot `k`'s value must be the minimum of slots `i`'s and `j`'s
      (`int_min` style). -/
  | minSlot (i j k : Nat)
  /-- Slot `k`'s value must be the maximum of slots `i`'s and `j`'s
      (`int_max` style). -/
  | maxSlot (i j k : Nat)
  /-- Slot `k`'s value must be the absolute value of slot `i`'s
      (`int_abs` style). -/
  | absSlot (i k : Nat)
  /-- Linear equality: the dot product of `coeffs` and the values at
      the slot positions `is` equals `b` (`int_lin_eq` style). -/
  | linEq (coeffs : List Int) (is : List Nat) (b : Int)
  /-- Linear inequality: the dot product of `coeffs` and the values at
      the slot positions `is` is at most `b` (`int_lin_le` style). -/
  | linLe (coeffs : List Int) (is : List Nat) (b : Int)
  /-- Linear disequality: the dot product of `coeffs` and the values at
      the slot positions `is` differs from `b` (`int_lin_ne` style). -/
  | linNe (coeffs : List Int) (is : List Nat) (b : Int)
  /-- Slot `i`'s value must be strictly below slot `j`'s
      (`int_lt` style). -/
  | ltSlot (i j : Nat)
  /-- Slot `i`'s value must be strictly below the integer `c`
      (`int_lt(x, c)` style). -/
  | ltConstHi (i : Nat) (c : Int)
  /-- Slot `i`'s value must be strictly above the integer `c`
      (`int_lt(c, x)` style). -/
  | ltConstLo (i : Nat) (c : Int)
  /-- Slot `j`'s value must be the negation of slot `i`'s Boolean
      (`bool_not` style). -/
  | boolNotSlot (i j : Nat)
  /-- Slot `k`'s value must be the conjunction of slots `i`'s and
      `j`'s Booleans (`bool_and` style). -/
  | boolAndSlot (i j k : Nat)
  /-- Slot `k`'s value must be the disjunction of slots `i`'s and
      `j`'s Booleans (`bool_or` style). -/
  | boolOrSlot (i j k : Nat)
  /-- The Boolean clause "some slot of `ps` is true, or some slot of
      `ns` is false" (`bool_clause` style: the positive argument
      array `ps`, the negated argument array `ns`). The constraint is
      enforced at the leaf (no propagator is registered); the
      compiler additionally seeds the corresponding original clause
      `∨ ps ∨ ¬ns` into the clause database (see `SeedClauses` and
      `Integration.Lcg`) so the LCG engine can propagate it. -/
  | boolClauseSlot (ps ns : List Nat)
  /-- Slot `k`'s Boolean must be the conjunction of the Booleans at
      the listed slots (`array_bool_and` style: the source form
      `array_bool_and(array of var bool, var bool)`). The target's
      truth value IS the `all` of the source slots' `= true` reads,
      so the EMPTY list forces the target to `true` (the `all` of an
      empty source array). -/
  | arrayBoolAndSlot (is : List Nat) (k : Nat)
  /-- Slot `k`'s integer must be the 0/1 view of slot `i`'s Boolean
      (`bool2int` style: `i = (if b then 1 else 0)`). -/
  | bool2intSlot (i : Nat) (k : Nat)
  /-- Slots `i` and `j` must carry equal Booleans (`bool_eq` style). -/
  | boolEqSlot (i j : Nat)
  /-- Slot `i`'s value is an integer index into the constant integer
      array `xs`, and slot `k` holds the 1-based element read at that
      index (`array_int_element` style: `xs[i] = k`, FlatZinc arrays
      are 1-based, and an out-of-range index is unsatisfiable). -/
  | arrayIntElementSlot (xs : List Int) (i : Nat) (k : Nat)
  /-- Slot `i`'s value is an integer index into the variable integer
      array at the slots `is`, and slot `k` holds the 1-based element
      read at that index (`array_var_int_element` style). -/
  | arrayVarIntElementSlot (is : List Nat) (i : Nat) (k : Nat)
  /-- Slot `i`'s value is an integer index into the variable Boolean
      array at the slots `is`, and slot `k` holds the 1-based element
      read at that index (`array_var_bool_element` style). -/
  | arrayVarBoolElementSlot (is : List Nat) (i : Nat) (k : Nat)
  /-- Slot `r`'s Boolean holds the truth value of "slot `i`'s value
      equals slot `j`'s" (`int_eq_reif` style: `R ↔ x = y`, the
      reification slot `r` is `true` exactly when the relation
      holds). -/
  | eqReifSlot (i j r : Nat)
  /-- Slot `r`'s Boolean holds the truth value of "slot `i`'s integer
      is at most slot `j`'s" (`int_le_reif` style: `R ↔ x ≤ y`). -/
  | leReifSlot (i j r : Nat)
  /-- Slot `r`'s Boolean holds the truth value of "slot `i`'s value
      differs from slot `j`'s" (`int_ne_reif` style: `R ↔ x ≠ y`). -/
  | neReifSlot (i j r : Nat)
  /-- Slot `r`'s Boolean holds the truth value of the linear equality
      "the dot product of `coeffs` and the values at `is` equals
      `b`" (`int_lin_eq_reif` style:
      `R ↔ dotProduct coeffs xs = some b`). -/
  | linEqReif (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat)
  /-- Slot `r`'s Boolean holds the truth value of the linear
      inequality "the dot product of `coeffs` and the values at `is`
      is at most `b`" (`int_lin_le_reif` style:
      `R ↔ dotLe coeffs xs b`). -/
  | linLeReif (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat)
  /-- Slot `r`'s Boolean holds the truth value of the linear
      disequality "the dot product of `coeffs` and the values at `is`
      differs from `b`" (`int_lin_ne_reif` style:
      `R ↔ dotNe coeffs xs b`). -/
  | linNeReif (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat)
  /-- The `array_int_maximum(m, xs)` array form (result slot first in
      the source): the result operand `r` carries the maximum of the
      operand list `os` — `maxValue` of the operand VALUES in the
      source predicate's exact reading (operands may be slots or
      integer literals; the empty list is unsatisfiable, as in the
      source). -/
  | maxGen (os : List DomIntArg) (r : DomIntArg)
  /-- The `array_int_minimum(m, xs)` array form: the result operand
      `r` carries the minimum of the operand list `os` (`minValue` of
      the operand values, empty list unsatisfiable). -/
  | minGen (os : List DomIntArg) (r : DomIntArg)
  /-- The GENERAL `int_div` shape: the result operand is the
      TRUNCATED quotient `Int.tdiv` of the two operands, and a zero
      divisor is unsatisfiable (the source predicate's exact
      `b ≠ 0 ∧ c = Int.tdiv a b` reading, so negative operands
      truncate towards zero). -/
  | divGen (o₁ o₂ r : DomIntArg)
  /-- The GENERAL `int_mod` shape: the result operand is the
      TRUNCATED remainder `Int.tmod` of the two operands, and a zero
      divisor is unsatisfiable (the source predicate's exact
      `b ≠ 0 ∧ c = Int.tmod a b` reading, so the remainder's sign
      follows the dividend). -/
  | modGen (o₁ o₂ r : DomIntArg)
  /-- The GENERAL two-operand `int_min` shape: the result operand `r`
      carries the minimum of the two operands, and all THREE operands
      must be integers — the source predicate's exact
      `[.int a, .int b, .int c] ↦ c = min a b` reading, so a
      non-integer operand is unsatisfiable in either reading (unlike
      `array_int_minimum`'s `minValue` reading, which ignores a
      non-integer tail element). -/
  | minPair (o₀ o₁ r : DomIntArg)
  /-- The GENERAL two-operand `int_max` shape, the `max` twin of
      `minPair`: `c = max a b` with all three operands integers. -/
  | maxPair (o₀ o₁ r : DomIntArg)

/-- The read of slot `i` is the Boolean `b` (false when the slot is
    absent or holds a non-Boolean value). -/
def slotIsBoolB (a : List Value) (i : Nat) (b : Bool) : Bool :=
  match a[i]? with
  | some v => v.eqB (.bool b)
  | none => false

/-- The declarative semantics of a slot constraint: what it means, in
    `Prop`, for a complete assignment (one value per slot, in slot
    order — the shape of `allAssigns`) to satisfy the constraint. -/
def DomConstraint.SatisfiedBy : DomConstraint → List Value → Prop
  | .eqSlot i j, a => ∃ x y, a[i]? = some x ∧ a[j]? = some y ∧ x = y
  | .neSlot i j, a => ∃ x y, a[i]? = some x ∧ a[j]? = some y ∧ x ≠ y
  | .leSlot i j, a => ∃ p q, a[i]? = some (.int p) ∧ a[j]? = some (.int q) ∧ p ≤ q
  | .constEq i v, a => a[i]? = some v
  | .plusSlot i j k, a =>
      ∃ p q r, a[i]? = some (.int p) ∧ a[j]? = some (.int q) ∧
        a[k]? = some (.int r) ∧ p + q = r
  | .leConstHi i c, a => ∃ p, a[i]? = some (.int p) ∧ p ≤ c
  | .leConstLo i c, a => ∃ p, a[i]? = some (.int p) ∧ c ≤ p
  | .allDiff is, a => (is.map (fun i => a[i]!)).Nodup
  | .timesSlot i j k, a =>
      ∃ p q r, a[i]? = some (.int p) ∧ a[j]? = some (.int q) ∧
        a[k]? = some (.int r) ∧ p * q = r
  | .minSlot i j k, a =>
      ∃ p q r, a[i]? = some (.int p) ∧ a[j]? = some (.int q) ∧
        a[k]? = some (.int r) ∧ min p q = r
  | .maxSlot i j k, a =>
      ∃ p q r, a[i]? = some (.int p) ∧ a[j]? = some (.int q) ∧
        a[k]? = some (.int r) ∧ max p q = r
  | .absSlot i k, a =>
      ∃ p r, a[i]? = some (.int p) ∧ a[k]? = some (.int r) ∧
        absValue p = r
  | .linEq coeffs is b, a =>
      dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) = some b
  | .linLe coeffs is b, a =>
      dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b = true
  | .linNe coeffs is b, a =>
      dotNe (intVals coeffs) (is.map (fun i => a[i]!)) b = true
  | .ltSlot i j, a =>
      ∃ p q, a[i]? = some (.int p) ∧ a[j]? = some (.int q) ∧ p < q
  | .ltConstHi i c, a => ∃ p, a[i]? = some (.int p) ∧ p < c
  | .ltConstLo i c, a => ∃ p, a[i]? = some (.int p) ∧ c < p
  | .boolNotSlot i j, a =>
      ∃ x y, a[i]? = some x ∧ a[j]? = some y ∧
        (x = .bool true ∧ y = .bool false ∨
          x = .bool false ∧ y = .bool true)
  | .boolAndSlot i j k, a =>
      ∃ p q r, a[i]? = some (.bool p) ∧ a[j]? = some (.bool q) ∧
        a[k]? = some (.bool r) ∧ (p && q) = r
  | .boolOrSlot i j k, a =>
      ∃ p q r, a[i]? = some (.bool p) ∧ a[j]? = some (.bool q) ∧
        a[k]? = some (.bool r) ∧ (p || q) = r
  | .boolClauseSlot ps ns, a =>
      (ps.any (fun i => slotIsBoolB a i true)) = true ∨
      (ns.any (fun j => slotIsBoolB a j false)) = true
  | .arrayBoolAndSlot is k, a =>
      a[k]? = some (.bool (is.all (fun i => slotIsBoolB a i true)))
  | .bool2intSlot i k, a =>
      ∃ b : Bool, a[i]? = some (.bool b) ∧
        a[k]? = some (.int (if b then 1 else 0))
  | .boolEqSlot i j, a =>
      ∃ p q : Bool, a[i]? = some (.bool p) ∧ a[j]? = some (.bool q) ∧ p = q
  | .arrayIntElementSlot xs i k, a =>
      ∃ idx e, a[i]? = some (.int idx) ∧ a[k]? = some (.int e) ∧
        valuesGet1 (xs.map Value.int) idx = some (.int e)
  | .arrayVarIntElementSlot is i k, a =>
      ∃ idx e, a[i]? = some (.int idx) ∧ a[k]? = some (.int e) ∧
        (∀ j ∈ is, ∃ v, a[j]? = some v) ∧
        valuesGet1 (is.map (fun j => a[j]!)) idx = some (.int e)
  | .arrayVarBoolElementSlot is i k, a =>
      ∃ idx e, a[i]? = some (.int idx) ∧ a[k]? = some (.bool e) ∧
        (∀ j ∈ is, ∃ v, a[j]? = some v) ∧
        valuesGet1 (is.map (fun j => a[j]!)) idx = some (.bool e)
  | .eqReifSlot i j r, a =>
      ∃ (p : Int) (q : Int) (rb : Bool), a[i]? = some (.int p) ∧
        a[j]? = some (.int q) ∧
        a[r]? = some (.bool rb) ∧ (rb = true ↔ p = q)
  | .leReifSlot i j r, a =>
      ∃ (p : Int) (q : Int) (rb : Bool), a[i]? = some (.int p) ∧
        a[j]? = some (.int q) ∧
        a[r]? = some (.bool rb) ∧ (rb = true ↔ p ≤ q)
  | .neReifSlot i j r, a =>
      ∃ (p : Int) (q : Int) (rb : Bool), a[i]? = some (.int p) ∧
        a[j]? = some (.int q) ∧
        a[r]? = some (.bool rb) ∧ (rb = true ↔ p ≠ q)
  | .linEqReif coeffs is b r, a =>
      ∃ (rb : Bool), a[r]? = some (.bool rb) ∧
        (rb = true ↔
          dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) = some b)
  | .linLeReif coeffs is b r, a =>
      ∃ (rb : Bool), a[r]? = some (.bool rb) ∧
        (rb = true ↔
          dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b = true)
  | .linNeReif coeffs is b r, a =>
      ∃ (rb : Bool), a[r]? = some (.bool rb) ∧
        (rb = true ↔
          dotNe (intVals coeffs) (is.map (fun i => a[i]!)) b = true)
  | .maxGen os r, a =>
      ∃ m : Int, DomIntArg.read a r = .int m ∧
        maxValue (os.map (DomIntArg.read a)) = some m
  | .minGen os r, a =>
      ∃ m : Int, DomIntArg.read a r = .int m ∧
        minValue (os.map (DomIntArg.read a)) = some m
  | .divGen o₁ o₂ r, a =>
      ∃ p q : Int, DomIntArg.read a o₁ = .int p ∧
        DomIntArg.read a o₂ = .int q ∧ q ≠ 0 ∧
        DomIntArg.read a r = .int (Int.tdiv p q)
  | .modGen o₁ o₂ r, a =>
      ∃ p q : Int, DomIntArg.read a o₁ = .int p ∧
        DomIntArg.read a o₂ = .int q ∧ q ≠ 0 ∧
        DomIntArg.read a r = .int (Int.tmod p q)
  | .minPair o₀ o₁ r, a =>
      ∃ p q : Int, DomIntArg.read a o₀ = .int p ∧
        DomIntArg.read a o₁ = .int q ∧
        DomIntArg.read a r = .int (min p q)
  | .maxPair o₀ o₁ r, a =>
      ∃ p q : Int, DomIntArg.read a o₀ = .int p ∧
        DomIntArg.read a o₁ = .int q ∧
        DomIntArg.read a r = .int (max p q)

/-- The executable Boolean twin of `SatisfiedBy`, for testing and for
    a pruning search's leaf integration. -/
def DomConstraint.satisfiedB (c : DomConstraint) (a : List Value) : Bool :=
  match c with
  | .eqSlot i j =>
      match a[i]?, a[j]? with
      | some x, some y => x.eqB y
      | _, _ => false
  | .neSlot i j =>
      match a[i]?, a[j]? with
      | some x, some y => !x.eqB y
      | _, _ => false
  | .leSlot i j =>
      match a[i]?, a[j]? with
      | some x, some y => intLEB x y
      | _, _ => false
  | .constEq i v =>
      match a[i]? with
      | some x => x.eqB v
      | none => false
  | .plusSlot i j k =>
      match a[i]?, a[j]?, a[k]? with
      | some (.int p), some (.int q), some (.int r) => decide (p + q = r)
      | _, _, _ => false
  | .leConstHi i c =>
      match a[i]? with
      | some (.int p) => decide (p ≤ c)
      | _ => false
  | .leConstLo i c =>
      match a[i]? with
      | some (.int p) => decide (c ≤ p)
      | _ => false
  | .allDiff is => valuesAllDifferent (is.map (fun i => a[i]!))
  | .timesSlot i j k =>
      match a[i]?, a[j]?, a[k]? with
      | some (.int p), some (.int q), some (.int r) => decide (p * q = r)
      | _, _, _ => false
  | .minSlot i j k =>
      match a[i]?, a[j]?, a[k]? with
      | some (.int p), some (.int q), some (.int r) => decide (min p q = r)
      | _, _, _ => false
  | .maxSlot i j k =>
      match a[i]?, a[j]?, a[k]? with
      | some (.int p), some (.int q), some (.int r) => decide (max p q = r)
      | _, _, _ => false
  | .absSlot i k =>
      match a[i]?, a[k]? with
      | some (.int p), some (.int r) => decide (absValue p = r)
      | _, _ => false
  | .linEq coeffs is b =>
      match dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) with
      | some d => decide (d = b)
      | none => false
  | .linLe coeffs is b =>
      dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b
  | .linNe coeffs is b =>
      dotNe (intVals coeffs) (is.map (fun i => a[i]!)) b
  | .ltSlot i j =>
      match a[i]?, a[j]? with
      | some (.int p), some (.int q) => decide (p < q)
      | _, _ => false
  | .ltConstHi i c =>
      match a[i]? with
      | some (.int p) => decide (p < c)
      | _ => false
  | .ltConstLo i c =>
      match a[i]? with
      | some (.int p) => decide (c < p)
      | _ => false
  | .boolNotSlot i j =>
      match a[i]?, a[j]? with
      | some (.bool p), some (.bool q) => decide (q = !p)
      | _, _ => false
  | .boolAndSlot i j k =>
      match a[i]?, a[j]?, a[k]? with
      | some (.bool p), some (.bool q), some (.bool r) =>
          decide ((p && q) = r)
      | _, _, _ => false
  | .boolOrSlot i j k =>
      match a[i]?, a[j]?, a[k]? with
      | some (.bool p), some (.bool q), some (.bool r) =>
          decide ((p || q) = r)
      | _, _, _ => false
  | .boolClauseSlot ps ns =>
      (ps.any (fun i => slotIsBoolB a i true)) ||
      (ns.any (fun j => slotIsBoolB a j false))
  | .arrayBoolAndSlot is k =>
      match a[k]? with
      | some (.bool b) => decide (b = is.all (fun i => slotIsBoolB a i true))
      | _ => false
  | .bool2intSlot i k =>
      match a[i]?, a[k]? with
      | some (.bool b), some (.int p) => decide (p = (if b then 1 else 0))
      | _, _ => false
  | .boolEqSlot i j =>
      match a[i]?, a[j]? with
      | some (.bool p), some (.bool q) => decide (p = q)
      | _, _ => false
  | .arrayIntElementSlot xs i k =>
      match a[i]?, a[k]? with
      | some (.int idx), some (.int e) =>
          match valuesGet1 (xs.map Value.int) idx with
          | some v => v.eqB (.int e)
          | none => false
      | _, _ => false
  | .arrayVarIntElementSlot is i k =>
      match a[i]?, a[k]? with
      | some (.int idx), some (.int e) =>
          is.all (fun j => (a[j]?).isSome) &&
            (match valuesGet1 (is.map (fun j => a[j]!)) idx with
             | some v => v.eqB (.int e)
             | none => false)
      | _, _ => false
  | .arrayVarBoolElementSlot is i k =>
      match a[i]?, a[k]? with
      | some (.int idx), some (.bool e) =>
          is.all (fun j => (a[j]?).isSome) &&
            (match valuesGet1 (is.map (fun j => a[j]!)) idx with
             | some v => v.eqB (.bool e)
             | none => false)
      | _, _ => false
  | .eqReifSlot i j r =>
      match a[i]?, a[j]?, a[r]? with
      | some (.int p), some (.int q), some (.bool rb) =>
          decide (rb = decide (p = q))
      | _, _, _ => false
  | .leReifSlot i j r =>
      match a[i]?, a[j]?, a[r]? with
      | some (.int p), some (.int q), some (.bool rb) =>
          decide (rb = decide (p ≤ q))
      | _, _, _ => false
  | .neReifSlot i j r =>
      match a[i]?, a[j]?, a[r]? with
      | some (.int p), some (.int q), some (.bool rb) =>
          decide (rb = decide (p ≠ q))
      | _, _, _ => false
  | .linEqReif coeffs is b r =>
      match a[r]? with
      | some (.bool rb) =>
          decide (rb = (match dotProduct (intVals coeffs)
              (is.map (fun i => a[i]!)) with
            | some d => decide (d = b)
            | none => false))
      | _ => false
  | .linLeReif coeffs is b r =>
      match a[r]? with
      | some (.bool rb) =>
          decide (rb = dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b)
      | _ => false
  | .linNeReif coeffs is b r =>
      match a[r]? with
      | some (.bool rb) =>
          decide (rb = dotNe (intVals coeffs) (is.map (fun i => a[i]!)) b)
      | _ => false
  | .maxGen os r =>
      match DomIntArg.read a r with
      | .int m => decide (maxValue (os.map (DomIntArg.read a)) = some m)
      | _ => false
  | .minGen os r =>
      match DomIntArg.read a r with
      | .int m => decide (minValue (os.map (DomIntArg.read a)) = some m)
      | _ => false
  | .divGen o₁ o₂ r =>
      match DomIntArg.read a o₁, DomIntArg.read a o₂ with
      | .int p, .int q =>
          decide (q ≠ 0) && (DomIntArg.read a r).eqB (.int (Int.tdiv p q))
      | _, _ => false
  | .modGen o₁ o₂ r =>
      match DomIntArg.read a o₁, DomIntArg.read a o₂ with
      | .int p, .int q =>
          decide (q ≠ 0) && (DomIntArg.read a r).eqB (.int (Int.tmod p q))
      | _, _ => false
  | .minPair o₀ o₁ r =>
      match DomIntArg.read a o₀, DomIntArg.read a o₁ with
      | .int p, .int q => (DomIntArg.read a r).eqB (.int (min p q))
      | _, _ => false
  | .maxPair o₀ o₁ r =>
      match DomIntArg.read a o₀, DomIntArg.read a o₁ with
      | .int p, .int q => (DomIntArg.read a r).eqB (.int (max p q))
      | _, _ => false

/-- A `valuesGet1` read of an all-integer value list realizes the
    chosen element with `eqB` exactly when it IS that integer. -/
private theorem valuesGet1_intEqB_iff (idx : Int) (ys : List Value)
    (e : Int) :
    ((match valuesGet1 ys idx with
      | some v => v.eqB (.int e)
      | none => false) = true) ↔ valuesGet1 ys idx = some (.int e) := by
  cases h : valuesGet1 ys idx with
  | none => simp
  | some v =>
      cases v <;> simp [value_eqB_iff]

/-- The Bool twin of `valuesGet1_intEqB_iff`. -/
private theorem valuesGet1_boolEqB_iff (idx : Int) (ys : List Value)
    (e : Bool) :
    ((match valuesGet1 ys idx with
      | some v => v.eqB (.bool e)
      | none => false) = true) ↔ valuesGet1 ys idx = some (.bool e) := by
  cases h : valuesGet1 ys idx with
  | none => simp
  | some v =>
      cases v <;> simp [value_eqB_iff]

/-- An `all` of `Option.isSome` reads is the pointwise existence of the
    reads. -/
private theorem all_isSome_iff {a : List Value} {is : List Nat} :
    (is.all (fun j => (a[j]?).isSome) = true) ↔
      ∀ j ∈ is, ∃ v, a[j]? = some v := by
  rw [List.all_eq_true]
  constructor
  · intro h j hj
    exact Option.isSome_iff_exists.mp (h j hj)
  · intro h j hj
    obtain ⟨v, hv⟩ := h j hj
    rw [hv]
    rfl

private theorem dotProduct_match_eq_some (xs ys : List Value) (b : Int) :
    (match dotProduct xs ys with
     | some d => decide (d = b)
     | none => false) = true ↔ dotProduct xs ys = some b := by
  cases h : dotProduct xs ys with
  | none => simp
  | some d => simp

/-- A reification-slot decision IS the truth-value agreement it
    represents: `decide (rb = t)` holds exactly when `rb` is `true`
    precisely if `t` is. -/
private theorem decide_eq_bool_iff (rb t : Bool) :
    decide (rb = t) = true ↔ (rb = true ↔ t = true) := by
  cases rb <;> cases t <;> simp

/-- The source form of a reified constraint — the disjunction "the
    reification slot is `true` and the relation holds, or it is
    `false` and the relation fails" — IS the truth-value agreement
    `R ↔ P`.  This is the bridge between the FlatZinc `*_reif`
    disjunction and the slot-agreement form of the `DomConstraint`
    semantics. -/
theorem reif_disj_iff (P : Prop) (rb : Bool) :
    ((rb = true ∧ P) ∨ (rb = false ∧ ¬ P)) ↔ (rb = true ↔ P) := by
  constructor
  · rintro (⟨hrb, hP⟩ | ⟨hrb, hnP⟩)
    · subst hrb
      exact ⟨fun _ => hP, fun _ => rfl⟩
    · subst hrb
      exact ⟨fun hfalse => absurd hfalse (by simp), fun hP => absurd hP hnP⟩
  · intro h
    cases rb with
    | true => exact Or.inl ⟨rfl, h.mp rfl⟩
    | false =>
        exact Or.inr ⟨rfl, fun hP => absurd (h.mpr hP) (by simp)⟩

/-- `dotNe` unfolds to a decision on the dot product. -/
theorem dotNe_eq (as_ xs : List Value) (b : Int) :
    dotNe as_ xs b = true ↔ ∃ d, dotProduct as_ xs = some d ∧ d ≠ b := by
  unfold dotNe
  cases h : dotProduct as_ xs with
  | none => simp
  | some d =>
      simp only [decide_eq_true_eq]
      constructor
      · intro hd
        exact ⟨d, rfl, hd⟩
      · rintro ⟨d', hd', hne⟩
        have : d' = d := (Option.some.inj hd').symm
        subst this
        exact hne

/-- `dotLe` unfolds to a decision on the dot product. -/
theorem dotLe_eq (as_ xs : List Value) (b : Int) :
    dotLe as_ xs b = true ↔ ∃ d, dotProduct as_ xs = some d ∧ d ≤ b := by
  unfold dotLe
  cases h : dotProduct as_ xs with
  | none => simp
  | some d =>
      simp only [decide_eq_true_eq]
      constructor
      · intro hd
        exact ⟨d, rfl, hd⟩
      · rintro ⟨d', hd', hle⟩
        have : d' = d := (Option.some.inj hd').symm
        subst this
        exact hle

/-- **Agreement** between the declarative semantics and the Boolean
    twin of `SatisfiedBy`. -/
theorem DomConstraint.satisfiedB_iff (c : DomConstraint) (a : List Value) :
    c.satisfiedB a = true ↔ c.SatisfiedBy a := by
  cases c with
  | eqSlot i j =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hy : a[j]? with
          | none => simp
          | some y =>
              simp only []
              simp only [value_eqB_iff, Option.some.injEq]
              refine ⟨fun h => ⟨x, y, rfl, rfl, h⟩, ?_⟩
              rintro ⟨w, z, rfl, rfl, h⟩
              exact h
  | neSlot i j =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hy : a[j]? with
          | none => simp
          | some y =>
              simp only []
              rw [Bool.not_eq_true', eqB_false_iff_ne]
              simp only [Option.some.injEq]
              refine ⟨fun h => ⟨x, y, rfl, rfl, h⟩, ?_⟩
              rintro ⟨w, z, rfl, rfl, h⟩
              exact h
  | leSlot i j =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hy : a[j]? with
          | none => simp
          | some y =>
              simp only []
              rw [intLEB_iff]
              refine ⟨fun ⟨p, q, hpx, hqy, hle⟩ => ⟨p, q, ?_, ?_, hle⟩, ?_⟩
              · simp [hpx]
              · simp [hqy]
              · rintro ⟨p, q, hpx, hqy, hle⟩
                simp only [Option.some.injEq] at hpx hqy
                exact ⟨p, q, hpx, hqy, hle⟩
  | constEq i v =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          simp only []
          rw [value_eqB_iff]
          simp only [Option.some.injEq]
  | plusSlot i j k =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hy : a[j]? with
          | none => simp
          | some y =>
              cases hz : a[k]? with
              | none => simp
              | some z =>
                  cases x with
                  | int p =>
                      cases y with
                      | int q =>
                          cases z with
                          | int r =>
                              simp only [decide_eq_true_eq]
                              refine ⟨fun h => ⟨p, q, r, rfl, rfl, rfl, h⟩, ?_⟩
                              rintro ⟨p', q', r', hp, hq, hr, hsum⟩
                              have h1 : p = p' := by
                                injection Option.some.inj hp
                              have h2 : q = q' := by
                                injection Option.some.inj hq
                              have h3 : r = r' := by
                                injection Option.some.inj hr
                              subst h1; subst h2; subst h3
                              exact hsum
                          | bool w => simp
                          | setOfInt w => simp
                          | array w => simp
                      | bool w => simp
                      | setOfInt w => simp
                      | array w => simp
                  | bool w => simp
                  | setOfInt w => simp
                  | array w => simp
  | leConstHi i c =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases x with
          | int p =>
              simp only [decide_eq_true_eq]
              refine ⟨fun h => ⟨p, rfl, h⟩, ?_⟩
              rintro ⟨p', hp, h⟩
              simp only [Option.some.injEq, Value.int.injEq] at hp
              omega
          | bool w => simp
          | setOfInt w => simp
          | array w => simp
  | leConstLo i c =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases x with
          | int p =>
              simp only [decide_eq_true_eq]
              refine ⟨fun h => ⟨p, rfl, h⟩, ?_⟩
              rintro ⟨p', hp, h⟩
              simp only [Option.some.injEq, Value.int.injEq] at hp
              omega
          | bool w => simp
          | setOfInt w => simp
          | array w => simp
  | allDiff is =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      exact valuesAllDifferent_iff_nodup _
  | timesSlot i j k =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hy : a[j]? with
          | none => simp
          | some y =>
              cases hz : a[k]? with
              | none => simp
              | some z =>
                  cases x with
                  | int p =>
                      cases y with
                      | int q =>
                          cases z with
                          | int r =>
                              simp only [decide_eq_true_eq]
                              refine ⟨fun h => ⟨p, q, r, rfl, rfl, rfl, h⟩, ?_⟩
                              rintro ⟨p', q', r', hp, hq, hr, hprod⟩
                              have h1 : p = p' := by
                                injection Option.some.inj hp
                              have h2 : q = q' := by
                                injection Option.some.inj hq
                              have h3 : r = r' := by
                                injection Option.some.inj hr
                              subst h1; subst h2; subst h3
                              exact hprod
                          | bool w => simp
                          | setOfInt w => simp
                          | array w => simp
                      | bool w => simp
                      | setOfInt w => simp
                      | array w => simp
                  | bool w => simp
                  | setOfInt w => simp
                  | array w => simp
  | minSlot i j k =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hy : a[j]? with
          | none => simp
          | some y =>
              cases hz : a[k]? with
              | none => simp
              | some z =>
                  cases x with
                  | int p =>
                      cases y with
                      | int q =>
                          cases z with
                          | int r =>
                              simp only [decide_eq_true_eq]
                              refine ⟨fun h => ⟨p, q, r, rfl, rfl, rfl, h⟩, ?_⟩
                              rintro ⟨p', q', r', hp, hq, hr, hmin⟩
                              have h1 : p = p' := by
                                injection Option.some.inj hp
                              have h2 : q = q' := by
                                injection Option.some.inj hq
                              have h3 : r = r' := by
                                injection Option.some.inj hr
                              subst h1; subst h2; subst h3
                              exact hmin
                          | bool w => simp
                          | setOfInt w => simp
                          | array w => simp
                      | bool w => simp
                      | setOfInt w => simp
                      | array w => simp
                  | bool w => simp
                  | setOfInt w => simp
                  | array w => simp
  | maxSlot i j k =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hy : a[j]? with
          | none => simp
          | some y =>
              cases hz : a[k]? with
              | none => simp
              | some z =>
                  cases x with
                  | int p =>
                      cases y with
                      | int q =>
                          cases z with
                          | int r =>
                              simp only [decide_eq_true_eq]
                              refine ⟨fun h => ⟨p, q, r, rfl, rfl, rfl, h⟩, ?_⟩
                              rintro ⟨p', q', r', hp, hq, hr, hmax⟩
                              have h1 : p = p' := by
                                injection Option.some.inj hp
                              have h2 : q = q' := by
                                injection Option.some.inj hq
                              have h3 : r = r' := by
                                injection Option.some.inj hr
                              subst h1; subst h2; subst h3
                              exact hmax
                          | bool w => simp
                          | setOfInt w => simp
                          | array w => simp
                      | bool w => simp
                      | setOfInt w => simp
                      | array w => simp
                  | bool w => simp
                  | setOfInt w => simp
                  | array w => simp
  | absSlot i k =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hz : a[k]? with
          | none => simp
          | some z =>
              cases x with
              | int p =>
                  cases z with
                  | int r =>
                      simp only [decide_eq_true_eq]
                      refine ⟨fun h => ⟨p, r, rfl, rfl, h⟩, ?_⟩
                      rintro ⟨p', r', hp, hr, habs⟩
                      have h1 : p = p' := by
                        injection Option.some.inj hp
                      have h2 : r = r' := by
                        injection Option.some.inj hr
                      subst h1; subst h2
                      exact habs
                  | bool w => simp
                  | setOfInt w => simp
                  | array w => simp
              | bool w => simp
              | setOfInt w => simp
              | array w => simp
  | linEq coeffs is b =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      exact dotProduct_match_eq_some (intVals coeffs) (is.map (fun i => a[i]!)) b
  | linLe coeffs is b =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
  | linNe coeffs is b =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
  | ltSlot i j =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hy : a[j]? with
          | none => simp
          | some y =>
              cases x with
              | int p =>
                  cases y with
                  | int q =>
                      simp only [decide_eq_true_eq]
                      refine ⟨fun h => ⟨p, q, rfl, rfl, h⟩, ?_⟩
                      rintro ⟨p', q', hp, hq, hlt⟩
                      have h1 : p = p' := by injection Option.some.inj hp
                      have h2 : q = q' := by injection Option.some.inj hq
                      subst h1; subst h2
                      exact hlt
                  | bool w => simp
                  | setOfInt w => simp
                  | array w => simp
              | bool w => simp
              | setOfInt w => simp
              | array w => simp
  | ltConstHi i c =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases x with
          | int p =>
              simp only [decide_eq_true_eq]
              refine ⟨fun h => ⟨p, rfl, h⟩, ?_⟩
              rintro ⟨p', hp, h⟩
              simp only [Option.some.injEq, Value.int.injEq] at hp
              omega
          | bool w => simp
          | setOfInt w => simp
          | array w => simp
  | ltConstLo i c =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases x with
          | int p =>
              simp only [decide_eq_true_eq]
              refine ⟨fun h => ⟨p, rfl, h⟩, ?_⟩
              rintro ⟨p', hp, h⟩
              simp only [Option.some.injEq, Value.int.injEq] at hp
              omega
          | bool w => simp
          | setOfInt w => simp
          | array w => simp
  | boolNotSlot i j =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hy : a[j]? with
          | none => simp
          | some y =>
              cases x with
              | bool p =>
                  cases y with
                  | bool q =>
                      cases p <;> cases q <;> simp_all
                  | int w => simp
                  | setOfInt w => simp
                  | array w => simp
              | int w => simp
              | setOfInt w => simp
              | array w => simp
  | boolAndSlot i j k =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hy : a[j]? with
          | none => simp
          | some y =>
              cases hz : a[k]? with
              | none => simp
              | some z =>
                  cases x with
                  | bool p =>
                      cases y with
                      | bool q =>
                          cases z with
                          | bool r =>
                              simp only [decide_eq_true_eq]
                              refine ⟨fun h => ⟨p, q, r, rfl, rfl, rfl, h⟩, ?_⟩
                              rintro ⟨p', q', r', hp, hq, hr, hand⟩
                              have h1 : p = p' := by
                                injection Option.some.inj hp
                              have h2 : q = q' := by
                                injection Option.some.inj hq
                              have h3 : r = r' := by
                                injection Option.some.inj hr
                              subst h1; subst h2; subst h3
                              exact hand
                          | int w => simp
                          | setOfInt w => simp
                          | array w => simp
                      | int w => simp
                      | setOfInt w => simp
                      | array w => simp
                  | int w => simp
                  | setOfInt w => simp
                  | array w => simp
  | boolOrSlot i j k =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hy : a[j]? with
          | none => simp
          | some y =>
              cases hz : a[k]? with
              | none => simp
              | some z =>
                  cases x with
                  | bool p =>
                      cases y with
                      | bool q =>
                          cases z with
                          | bool r =>
                              simp only [decide_eq_true_eq]
                              refine ⟨fun h => ⟨p, q, r, rfl, rfl, rfl, h⟩, ?_⟩
                              rintro ⟨p', q', r', hp, hq, hr, hor⟩
                              have h1 : p = p' := by
                                injection Option.some.inj hp
                              have h2 : q = q' := by
                                injection Option.some.inj hq
                              have h3 : r = r' := by
                                injection Option.some.inj hr
                              subst h1; subst h2; subst h3
                              exact hor
                          | int w => simp
                          | setOfInt w => simp
                          | array w => simp
                      | int w => simp
                      | setOfInt w => simp
                      | array w => simp
                  | int w => simp
                  | setOfInt w => simp
                  | array w => simp
  | boolClauseSlot ps ns =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy,
        Bool.or_eq_true]
  | arrayBoolAndSlot is k =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hz : a[k]? with
      | none => simp
      | some z =>
          cases z with
          | bool b =>
              simp only [decide_eq_true_eq, Option.some.injEq, Value.bool.injEq]
          | int w => simp
          | setOfInt w => simp
          | array w => simp
  | bool2intSlot i k =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hz : a[k]? with
          | none => simp
          | some z =>
              cases x with
              | bool p =>
                  cases z with
                  | int q => cases p <;> simp_all
                  | bool w => simp
                  | setOfInt w => simp
                  | array w => simp
              | int w => simp
              | setOfInt w => simp
              | array w => simp
  | boolEqSlot i j =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hy : a[j]? with
          | none => simp
          | some y =>
              cases x with
              | bool p =>
                  cases y with
                  | bool q => cases p <;> cases q <;> simp_all
                  | int w => simp
                  | setOfInt w => simp
                  | array w => simp
              | int w => simp
              | setOfInt w => simp
              | array w => simp
  | arrayIntElementSlot xs i k =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hz : a[k]? with
          | none => simp
          | some z =>
              cases x with
              | int idx =>
                  cases z with
                  | int e =>
                      rw [valuesGet1_intEqB_iff]
                      refine ⟨fun h => ⟨idx, e, rfl, rfl, h⟩, ?_⟩
                      rintro ⟨idx', e', h1, h2, hget⟩
                      cases h1; cases h2
                      exact hget
                  | bool w => simp
                  | setOfInt w => simp
                  | array w => simp
              | bool w => simp
              | setOfInt w => simp
              | array w => simp
  | arrayVarIntElementSlot is i k =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hz : a[k]? with
          | none => simp
          | some z =>
              cases x with
              | int idx =>
                  cases z with
                  | int e =>
                      simp only [all_isSome_iff, valuesGet1_intEqB_iff,
                        Bool.and_eq_true, Option.some.injEq]
                      refine ⟨fun ⟨hin, hget⟩ =>
                        ⟨idx, e, rfl, rfl, hin, hget⟩, ?_⟩
                      rintro ⟨idx', e', h1, h2, hin, hget⟩
                      injection h1 with h1'; injection h2 with h2'
                      subst h1'; subst h2'
                      exact ⟨hin, hget⟩
                  | bool w => simp
                  | setOfInt w => simp
                  | array w => simp
              | bool w => simp
              | setOfInt w => simp
              | array w => simp
  | arrayVarBoolElementSlot is i k =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hz : a[k]? with
          | none => simp
          | some z =>
              cases x with
              | int idx =>
                  cases z with
                  | bool e =>
                      simp only [all_isSome_iff, valuesGet1_boolEqB_iff,
                        Bool.and_eq_true, Option.some.injEq]
                      refine ⟨fun ⟨hin, hget⟩ =>
                        ⟨idx, e, rfl, rfl, hin, hget⟩, ?_⟩
                      rintro ⟨idx', e', h1, h2, hin, hget⟩
                      injection h1 with h1'; injection h2 with h2'
                      subst h1'; subst h2'
                      exact ⟨hin, hget⟩
                  | int w => simp
                  | setOfInt w => simp
                  | array w => simp
              | bool w => simp
              | setOfInt w => simp
              | array w => simp
  | eqReifSlot i j r =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hy : a[j]? with
          | none => simp
          | some y =>
              cases hr : a[r]? with
              | none => simp
              | some rv =>
                  cases rv with
                  | bool rb =>
                      cases x with
                      | int p =>
                          cases y with
                          | int q =>
                              rw [decide_eq_bool_iff, decide_eq_true_eq]
                              refine ⟨fun h => ⟨p, q, rb, rfl, rfl, rfl, h⟩,
                                ?_⟩
                              rintro ⟨p', q', rb', h1, h2, h3, h⟩
                              cases h1; cases h2; cases h3
                              exact h
                          | bool w => simp
                          | setOfInt w => simp
                          | array w => simp
                      | bool w => simp
                      | setOfInt w => simp
                      | array w => simp
                  | int w => simp
                  | setOfInt w => simp
                  | array w => simp
  | leReifSlot i j r =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hy : a[j]? with
          | none => simp
          | some y =>
              cases hr : a[r]? with
              | none => simp
              | some rv =>
                  cases rv with
                  | bool rb =>
                      cases x with
                      | int p =>
                          cases y with
                          | int q =>
                              rw [decide_eq_bool_iff, decide_eq_true_eq]
                              refine ⟨fun h => ⟨p, q, rb, rfl, rfl, rfl, h⟩,
                                ?_⟩
                              rintro ⟨p', q', rb', h1, h2, h3, h⟩
                              cases h1; cases h2; cases h3
                              exact h
                          | bool w => simp
                          | setOfInt w => simp
                          | array w => simp
                      | bool w => simp
                      | setOfInt w => simp
                      | array w => simp
                  | int w => simp
                  | setOfInt w => simp
                  | array w => simp
  | neReifSlot i j r =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hy : a[j]? with
          | none => simp
          | some y =>
              cases hr : a[r]? with
              | none => simp
              | some rv =>
                  cases rv with
                  | bool rb =>
                      cases x with
                      | int p =>
                          cases y with
                          | int q =>
                              rw [decide_eq_bool_iff, decide_eq_true_eq]
                              refine ⟨fun h => ⟨p, q, rb, rfl, rfl, rfl, h⟩,
                                ?_⟩
                              rintro ⟨p', q', rb', h1, h2, h3, h⟩
                              cases h1; cases h2; cases h3
                              exact h
                          | bool w => simp
                          | setOfInt w => simp
                          | array w => simp
                      | bool w => simp
                      | setOfInt w => simp
                      | array w => simp
                  | int w => simp
                  | setOfInt w => simp
                  | array w => simp
  | linEqReif coeffs is b r =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hr : a[r]? with
      | none => simp
      | some rv =>
          cases rv with
          | bool rb =>
              rw [decide_eq_bool_iff, dotProduct_match_eq_some]
              refine ⟨fun h => ⟨rb, rfl, h⟩, ?_⟩
              rintro ⟨rb', h1, h⟩
              cases h1
              exact h
          | int w => simp
          | setOfInt w => simp
          | array w => simp
  | linLeReif coeffs is b r =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hr : a[r]? with
      | none => simp
      | some rv =>
          cases rv with
          | bool rb =>
              rw [decide_eq_bool_iff]
              refine ⟨fun h => ⟨rb, rfl, h⟩, ?_⟩
              rintro ⟨rb', h1, h⟩
              cases h1
              exact h
          | int w => simp
          | setOfInt w => simp
          | array w => simp
  | linNeReif coeffs is b r =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hr : a[r]? with
      | none => simp
      | some rv =>
          cases rv with
          | bool rb =>
              rw [decide_eq_bool_iff]
              refine ⟨fun h => ⟨rb, rfl, h⟩, ?_⟩
              rintro ⟨rb', h1, h⟩
              cases h1
              exact h
          | int w => simp
          | setOfInt w => simp
          | array w => simp
  | maxGen os r =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hr : DomIntArg.read a r with
      | int m =>
          rw [decide_eq_true_eq]
          constructor
          · intro h
            exact ⟨m, rfl, h⟩
          · rintro ⟨m', hm', h⟩
            have hm : m = m' := by injection hm' with hmi
            subst hm
            exact h
      | bool w => simp [hr]
      | setOfInt w => simp [hr]
      | array w => simp [hr]
  | minGen os r =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hr : DomIntArg.read a r with
      | int m =>
          rw [decide_eq_true_eq]
          constructor
          · intro h
            exact ⟨m, rfl, h⟩
          · rintro ⟨m', hm', h⟩
            have hm : m = m' := by injection hm' with hmi
            subst hm
            exact h
      | bool w => simp [hr]
      | setOfInt w => simp [hr]
      | array w => simp [hr]
  | divGen o₁ o₂ r =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases h₁ : DomIntArg.read a o₁ with
      | int p =>
          cases h₂ : DomIntArg.read a o₂ with
          | int q =>
              rw [Bool.and_eq_true, decide_eq_true_eq, value_eqB_iff]
              constructor
              · rintro ⟨hq, hr⟩
                exact ⟨p, q, rfl, rfl, hq, hr⟩
              · rintro ⟨p', q', hp', hq'', hq, hr⟩
                have hpv : p' = p := by injection hp' with hpi; exact hpi.symm
                have hqv : q' = q := by injection hq'' with hqi; exact hqi.symm
                rw [hqv] at hq
                rw [hpv, hqv] at hr
                exact ⟨hq, hr⟩
          | bool w => simp [h₁, h₂]
          | setOfInt w => simp [h₁, h₂]
          | array w => simp [h₁, h₂]
      | bool w => simp [h₁]
      | setOfInt w => simp [h₁]
      | array w => simp [h₁]
  | modGen o₁ o₂ r =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases h₁ : DomIntArg.read a o₁ with
      | int p =>
          cases h₂ : DomIntArg.read a o₂ with
          | int q =>
              rw [Bool.and_eq_true, decide_eq_true_eq, value_eqB_iff]
              constructor
              · rintro ⟨hq, hr⟩
                exact ⟨p, q, rfl, rfl, hq, hr⟩
              · rintro ⟨p', q', hp', hq'', hq, hr⟩
                have hpv : p' = p := by injection hp' with hpi; exact hpi.symm
                have hqv : q' = q := by injection hq'' with hqi; exact hqi.symm
                rw [hqv] at hq
                rw [hpv, hqv] at hr
                exact ⟨hq, hr⟩
          | bool w => simp [h₁, h₂]
          | setOfInt w => simp [h₁, h₂]
          | array w => simp [h₁, h₂]
      | bool w => simp [h₁]
      | setOfInt w => simp [h₁]
      | array w => simp [h₁]
  | minPair o₀ o₁ r =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases h₁ : DomIntArg.read a o₀ with
      | int p =>
          cases h₂ : DomIntArg.read a o₁ with
          | int q =>
              rw [value_eqB_iff]
              constructor
              · intro hr
                exact ⟨p, q, rfl, rfl, hr⟩
              · rintro ⟨p', q', hp', hq'', hr⟩
                have hpv : p' = p := by injection hp' with hpi; exact hpi.symm
                have hqv : q' = q := by injection hq'' with hqi; exact hqi.symm
                rw [hpv, hqv] at hr
                exact hr
          | bool w => simp [h₁, h₂]
          | setOfInt w => simp [h₁, h₂]
          | array w => simp [h₁, h₂]
      | bool w => simp [h₁]
      | setOfInt w => simp [h₁]
      | array w => simp [h₁]
  | maxPair o₀ o₁ r =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases h₁ : DomIntArg.read a o₀ with
      | int p =>
          cases h₂ : DomIntArg.read a o₁ with
          | int q =>
              rw [value_eqB_iff]
              constructor
              · intro hr
                exact ⟨p, q, rfl, rfl, hr⟩
              · rintro ⟨p', q', hp', hq'', hr⟩
                have hpv : p' = p := by injection hp' with hpi; exact hpi.symm
                have hqv : q' = q := by injection hq'' with hqi; exact hqi.symm
                rw [hpv, hqv] at hr
                exact hr
          | bool w => simp [h₁, h₂]
          | setOfInt w => simp [h₁, h₂]
          | array w => simp [h₁, h₂]
      | bool w => simp [h₁]
      | setOfInt w => simp [h₁]
      | array w => simp [h₁]

/-- `neSlot` is symmetric in its two positions. -/
theorem DomConstraint.satisfiedBy_neSlot_comm (i j : Nat) (a : List Value) :
    DomConstraint.SatisfiedBy (DomConstraint.neSlot i j) a ↔
      DomConstraint.SatisfiedBy (DomConstraint.neSlot j i) a := by
  simp only [DomConstraint.SatisfiedBy]
  constructor
  · rintro ⟨x, y, hx, hy, hne⟩
    exact ⟨y, x, hy, hx, hne.symm⟩
  · rintro ⟨x, y, hx, hy, hne⟩
    exact ⟨y, x, hy, hx, hne.symm⟩

/-! ## The propagation contract -/

/-- The result of a propagator: a certified contradiction, or the
    narrowed slot domains (one finite value list per slot, the shape of
    `LeanFzn/Compiler/Domain.lean`'s search slots). -/
inductive PropResult where
  /-- The propagator certifies that no assignment of the current
      domains can satisfy its constraint. -/
  | contradiction
  /-- The narrowed domains: every satisfying assignment compatible
      with the input domains is still compatible with them. -/
  | narrowed (doms : List (List Value))
  deriving Repr

/-- Structural equality of propagation results (for testing):
    results are equal when both are contradictions, or both narrow to
    pointwise structurally-equal domain lists. -/
def domsEqB (a b : List (List Value)) : Bool :=
  a.length == b.length && (a.zip b).all (fun p => valuesEqB p.1 p.2)

instance : BEq PropResult where
  beq
    | .contradiction, .contradiction => true
    | .narrowed a, .narrowed b => domsEqB a b
    | _, _ => false

/-- **The propagation contract** (PLAN 6.3's local preservation
    theorem, packaged).  A propagator `p` for constraint `c` meets the
    contract when:

    * on `narrowed doms'`, every assignment of the input domains that
      satisfies `c` is still an assignment of `doms'` — "every
      satisfying assignment compatible with the input domains remains
      compatible with the output domains" — and `doms'` is
      pointwise-subset the input domains (no slot grows, none is
      added or removed);
    * on `contradiction`, no assignment of the input domains
      satisfies `c`. -/
structure Preserves (c : DomConstraint)
    (p : List (List Value) → PropResult) : Prop where
  /-- **Narrowing soundness**: satisfying assignments of the input
      domains remain assignments of the output domains. -/
  narrowed {doms doms' : List (List Value)}
      (h : p doms = .narrowed doms') :
    ∀ a ∈ allAssigns doms, c.SatisfiedBy a → a ∈ allAssigns doms'
  /-- The output domains only shrank: pointwise subsetting, same slot
      count. -/
  subset {doms doms' : List (List Value)}
      (h : p doms = .narrowed doms') : DomPointwiseSub doms' doms
  /-- **Contradiction soundness**: no satisfying assignment
      remains. -/
  contradicts {doms : List (List Value)}
      (h : p doms = .contradiction) :
    ∀ a ∈ allAssigns doms, ¬ c.SatisfiedBy a

/-! ## The equality propagator -/

/-- The equality narrowing: both slots take the intersection of their
    domains (each in its own order), each intersection computed once. -/
private def eqNarrow (i j : Nat) (doms : List (List Value)) :
    List (List Value) :=
  let di := getSlot doms i
  let dj := getSlot doms j
  setSlot (setSlot doms i (interVals di dj)) j (interVals dj di)

/-- **The equality propagator** (`int_eq` style on two slots): both
    domains narrow to their intersection; `contradiction` when the
    intersection is empty.  Each intersection is computed once. -/
def propEqSlot (i j : Nat) (doms : List (List Value)) : PropResult :=
  let xi := interVals (getSlot doms i) (getSlot doms j)
  let xj := interVals (getSlot doms j) (getSlot doms i)
  if xi.isEmpty = true ∨ xj.isEmpty = true then
    .contradiction
  else
    .narrowed (eqNarrow i j doms)

private theorem getSlot_eqNarrow_left {i j : Nat} {doms : List (List Value)}
    (hi : i < doms.length) (hij : i ≠ j) :
    getSlot (eqNarrow i j doms) i =
      interVals (getSlot doms i) (getSlot doms j) := by
  simp only [eqNarrow]
  rw [getSlot_setSlot_of_ne (setSlot doms i (interVals (getSlot doms i) (getSlot doms j)))
    (interVals (getSlot doms j) (getSlot doms i)) j i hij,
    getSlot_setSlot_eq doms _ i hi]

private theorem getSlot_eqNarrow_right {i j : Nat} {doms : List (List Value)}
    (hj : j < doms.length) :
    getSlot (eqNarrow i j doms) j =
      interVals (getSlot doms j) (getSlot doms i) := by
  simp only [eqNarrow]
  rw [getSlot_setSlot_eq (setSlot doms i (interVals (getSlot doms i) (getSlot doms j)))
    (interVals (getSlot doms j) (getSlot doms i)) j
    (by rw [setSlot_length]; exact hj)]

private theorem getSlot_eqNarrow_other {i j k : Nat} {doms : List (List Value)}
    (hki : k ≠ i) (hkj : k ≠ j) :
    getSlot (eqNarrow i j doms) k = getSlot doms k := by
  simp only [eqNarrow]
  rw [getSlot_setSlot_of_ne (setSlot doms i (interVals (getSlot doms i) (getSlot doms j)))
    (interVals (getSlot doms j) (getSlot doms i)) j k hkj,
    getSlot_setSlot_of_ne doms (interVals (getSlot doms i) (getSlot doms j)) i k hki]

/-- **Preservation for `propEqSlot`** (PLAN 6.3's local preservation
    theorem, equality case): on `narrowed doms'`, every assignment of
    the input domains whose two slots carry equal values is still an
    assignment of `doms'`, and `doms'` is pointwise-subset the input
    domains; on `contradiction`, no assignment of the input domains
    makes the two slots equal. -/
theorem propEqSlot_preserves (i j : Nat) :
    Preserves (DomConstraint.eqSlot i j) (propEqSlot i j) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propEqSlot] at h
    by_cases hc : (interVals (getSlot doms i) (getSlot doms j)).isEmpty = true ∨
      (interVals (getSlot doms j) (getSlot doms i)).isEmpty = true
    · rw [if_pos hc] at h
      exact absurd h (by simp)
    · rw [if_neg hc] at h
      have hd : eqNarrow i j doms = doms' := PropResult.narrowed.inj h
      subst hd
      obtain ⟨x, y, hx, hy, heq⟩ := hsat
      obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
      have hxi : x ∈ getSlot doms i := hget i x hx
      have hyj : y ∈ getSlot doms j := hget j y hy
      have hyi : y ∈ getSlot doms i := by rw [← heq]; exact hxi
      have hxj : x ∈ getSlot doms j := by rw [heq]; exact hyj
      apply allAssigns_intro
      · have hlen2 : (eqNarrow i j doms).length = doms.length := by
          simp only [eqNarrow, setSlot_length]
        rw [hlen2]
        exact hlen
      · intro k v hv
        by_cases hkj : k = j
        · rw [hkj] at hv
          have hvy : v = y := Option.some.inj (hv.symm.trans hy)
          subst hvy
          have hlenj : j < doms.length :=
            lt_length_of_mem_getSlot doms j v (hget j v hv)
          rw [hkj, getSlot_eqNarrow_right hlenj]
          refine mem_interVals_of (hget j v hv) ?_
          rw [← heq]
          exact hxi
        · by_cases hki : k = i
          · rw [hki] at hv
            have hvx : v = x := Option.some.inj (hv.symm.trans hx)
            subst hvx
            have hleni : i < doms.length :=
              lt_length_of_mem_getSlot doms i v (hget i v hv)
            rw [hki, getSlot_eqNarrow_left hleni (fun hij => hkj (hki.trans hij))]
            refine mem_interVals_of (hget i v hv) ?_
            rw [heq]
            exact hyj
          · rw [getSlot_eqNarrow_other (fun h => hki h) (fun h => hkj h)]
            exact hget k v hv
  · intro doms doms' h
    simp only [propEqSlot] at h
    by_cases hc : (interVals (getSlot doms i) (getSlot doms j)).isEmpty = true ∨
      (interVals (getSlot doms j) (getSlot doms i)).isEmpty = true
    · rw [if_pos hc] at h
      exact absurd h (by simp)
    · rw [if_neg hc] at h
      have hd : eqNarrow i j doms = doms' := PropResult.narrowed.inj h
      subst hd
      simp only [eqNarrow]
      exact DomPointwiseSub.setSlot
        (DomPointwiseSub.setSlot (DomPointwiseSub.refl doms)
          (fun _ hv => mem_interVals_left hv))
        (fun _ hv => mem_interVals_left hv)
  · intro doms _h a ha hsat
    simp only [propEqSlot] at _h
    by_cases hc : (interVals (getSlot doms i) (getSlot doms j)).isEmpty = true ∨
      (interVals (getSlot doms j) (getSlot doms i)).isEmpty = true
    · rcases hc with hle | hre
      · obtain ⟨x, y, hx, hy, heq⟩ := hsat
        obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
        have hxj : x ∈ getSlot doms j := by rw [heq]; exact hget j y hy
        have hmem : x ∈ interVals (getSlot doms i) (getSlot doms j) :=
          mem_interVals_of (hget i x hx) hxj
        rw [List.isEmpty_iff.mp hle] at hmem
        exact absurd hmem (by simp)
      · obtain ⟨x, y, hx, hy, heq⟩ := hsat
        obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
        have hyi : y ∈ getSlot doms i := by rw [← heq]; exact hget i x hx
        have hmem : y ∈ interVals (getSlot doms j) (getSlot doms i) :=
          mem_interVals_of (hget j y hy) hyi
        rw [List.isEmpty_iff.mp hre] at hmem
        exact absurd hmem (by simp)
    · rw [if_neg hc] at _h
      exact absurd _h (by simp)

/-! ## The disequality propagator -/

/-- **The disequality propagator** (`int_ne` style on two slots): if
    one slot's domain is a singleton, its value is removed from the
    other slot's domain; `contradiction` when the other domain becomes
    empty.  When neither domain is a singleton, nothing is narrowed. -/
def propNeSlot (i j : Nat) (doms : List (List Value)) : PropResult :=
  match single? (getSlot doms i) with
  | some x =>
      if (removeVal x (getSlot doms j)).isEmpty = true then .contradiction
      else .narrowed (setSlot doms j (removeVal x (getSlot doms j)))
  | none =>
      match single? (getSlot doms j) with
      | some y =>
          if (removeVal y (getSlot doms i)).isEmpty = true then .contradiction
          else .narrowed (setSlot doms i (removeVal y (getSlot doms i)))
      | none => .narrowed doms

private theorem propNe_narrowed {s r : Nat} {w : Value}
    {doms : List (List Value)}
    (hw : single? (getSlot doms s) = some w) {a : List Value}
    (ha : a ∈ allAssigns doms) (hsat : DomConstraint.SatisfiedBy (DomConstraint.neSlot s r) a) :
    a ∈ allAssigns (setSlot doms r (removeVal w (getSlot doms r))) := by
  obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
  obtain ⟨x, y, hx, hy, hne⟩ := hsat
  have hxs : x = w := by
    have hxmem : x ∈ getSlot doms s := hget s x hx
    rw [single?_eq_some_iff.mp hw] at hxmem
    exact List.mem_singleton.mp hxmem
  apply allAssigns_intro
  · rw [setSlot_length]
    exact hlen
  · intro k v hv
    by_cases hkr : k = r
    · rw [hkr] at hv
      have hvy : v = y := Option.some.inj (hv.symm.trans hy)
      subst hvy
      have hlenr : r < doms.length :=
        lt_length_of_mem_getSlot doms r v (hget r v hv)
      rw [hkr, getSlot_setSlot_eq doms (removeVal w (getSlot doms r)) r hlenr]
      exact mem_removeVal_of (hget r v hv)
        (eqB_false_of_ne (by rw [← hxs]; exact hne))
    · rw [getSlot_setSlot_of_ne doms (removeVal w (getSlot doms r)) r k hkr]
      exact hget k v hv

private theorem propNe_contradicts {s r : Nat} {w : Value}
    {doms : List (List Value)}
    (hw : single? (getSlot doms s) = some w)
    (hempty : (removeVal w (getSlot doms r)).isEmpty = true)
    {a : List Value} (ha : a ∈ allAssigns doms)
    (hsat : DomConstraint.SatisfiedBy (DomConstraint.neSlot s r) a) : False := by
  obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
  obtain ⟨x, y, hx, hy, hne⟩ := hsat
  have hxs : x = w := by
    have hxmem : x ∈ getSlot doms s := hget s x hx
    rw [single?_eq_some_iff.mp hw] at hxmem
    exact List.mem_singleton.mp hxmem
  have hmem : y ∈ removeVal w (getSlot doms r) :=
    mem_removeVal_of (hget r y hy) (eqB_false_of_ne (by rw [← hxs]; exact hne))
  rw [List.isEmpty_iff.mp hempty] at hmem
  exact absurd hmem (by simp)

/-- **Preservation for `propNeSlot`** (PLAN 6.3's local preservation
    theorem, disequality case): on `narrowed doms'`, every assignment
    of the input domains whose two slots carry different values is
    still an assignment of `doms'`, and `doms'` is pointwise-subset
    the input domains; on `contradiction`, no assignment of the input
    domains makes the two slots differ. -/
theorem propNeSlot_preserves (i j : Nat) :
    Preserves (DomConstraint.neSlot i j) (propNeSlot i j) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propNeSlot] at h
    cases hi : single? (getSlot doms i) with
    | none =>
        simp only [hi] at h
        cases hj : single? (getSlot doms j) with
        | none =>
            simp only [hj] at h
            have hd : doms' = doms := (PropResult.narrowed.inj h).symm
            subst hd
            exact ha
        | some y =>
            simp only [hj] at h
            by_cases hc : (removeVal y (getSlot doms i)).isEmpty = true
            · rw [if_pos hc] at h
              exact absurd h (by simp)
            · rw [if_neg hc] at h
              have hd : setSlot doms i (removeVal y (getSlot doms i)) = doms' :=
                PropResult.narrowed.inj h
              subst hd
              exact propNe_narrowed hj ha
                ((DomConstraint.satisfiedBy_neSlot_comm i j a).mp hsat)
    | some x =>
        simp only [hi] at h
        by_cases hc : (removeVal x (getSlot doms j)).isEmpty = true
        · rw [if_pos hc] at h
          exact absurd h (by simp)
        · rw [if_neg hc] at h
          have hd : setSlot doms j (removeVal x (getSlot doms j)) = doms' :=
            PropResult.narrowed.inj h
          subst hd
          exact propNe_narrowed hi ha hsat
  · intro doms doms' _h
    simp only [propNeSlot] at _h
    cases hi : single? (getSlot doms i) with
    | none =>
        simp only [hi] at _h
        cases hj : single? (getSlot doms j) with
        | none =>
            simp only [hj] at _h
            have hd : doms' = doms := (PropResult.narrowed.inj _h).symm
            rw [hd]
            exact DomPointwiseSub.refl doms
        | some y =>
            simp only [hj] at _h
            by_cases hc : (removeVal y (getSlot doms i)).isEmpty = true
            · rw [if_pos hc] at _h
              exact absurd _h (by simp)
            · rw [if_neg hc] at _h
              have hd : setSlot doms i (removeVal y (getSlot doms i)) = doms' :=
                PropResult.narrowed.inj _h
              rw [← hd]
              exact DomPointwiseSub.setSlot (DomPointwiseSub.refl doms)
                (fun _ hv => mem_removeVal hv)
    | some x =>
        simp only [hi] at _h
        by_cases hc : (removeVal x (getSlot doms j)).isEmpty = true
        · rw [if_pos hc] at _h
          exact absurd _h (by simp)
        · rw [if_neg hc] at _h
          have hd : setSlot doms j (removeVal x (getSlot doms j)) = doms' :=
            PropResult.narrowed.inj _h
          rw [← hd]
          exact DomPointwiseSub.setSlot (DomPointwiseSub.refl doms)
            (fun _ hv => mem_removeVal hv)
  · intro doms h a ha hsat
    simp only [propNeSlot] at h
    cases hi : single? (getSlot doms i) with
    | none =>
        simp only [hi] at h
        cases hj : single? (getSlot doms j) with
        | none =>
            simp only [hj] at h
            exact absurd h (by simp)
        | some y =>
            simp only [hj] at h
            by_cases hc : (removeVal y (getSlot doms i)).isEmpty = true
            · rw [if_pos hc] at h
              exact propNe_contradicts hj hc ha
                ((DomConstraint.satisfiedBy_neSlot_comm i j a).mp hsat)
            · rw [if_neg hc] at h
              exact absurd h (by simp)
    | some x =>
        simp only [hi] at h
        by_cases hc : (removeVal x (getSlot doms j)).isEmpty = true
        · rw [if_pos hc] at h
          exact propNe_contradicts hi hc ha hsat
        · rw [if_neg hc] at h
          exact absurd h (by simp)

/-! ## The order propagator -/

/-- The order narrowing: slot `i` keeps values at most `b`, slot `j`
    keeps values at least `m`. -/
private def leNarrow (b m : Int) (i j : Nat) (doms : List (List Value)) :
    List (List Value) :=
  let hi := atMostVals b (getSlot doms i)
  let hj := atLeastVals m (getSlot doms j)
  setSlot (setSlot doms i hi) j hj

/-- **The order propagator** (`int_le` style on two slots): slot `i`
    keeps values at most the maximum integer of slot `j`'s domain,
    slot `j` keeps values at least the minimum integer of slot `i`'s
    domain; `contradiction` when either side becomes empty (or a
    domain has no integers to order). -/
def propLeSlot (i j : Nat) (doms : List (List Value)) : PropResult :=
  match domMax (getSlot doms j) with
  | none => .contradiction
  | some b =>
      match domMin (getSlot doms i) with
      | none => .contradiction
      | some m =>
          let hi := atMostVals b (getSlot doms i)
          let hj := atLeastVals m (getSlot doms j)
          if hi.isEmpty = true ∨ hj.isEmpty = true then
            .contradiction
          else
            .narrowed (leNarrow b m i j doms)

private theorem getSlot_leNarrow_left {i j : Nat} {b m : Int}
    {doms : List (List Value)}
    (hi : i < doms.length) (hij : i ≠ j) :
    getSlot (leNarrow b m i j doms) i = atMostVals b (getSlot doms i) := by
  simp only [leNarrow]
  rw [getSlot_setSlot_of_ne (setSlot doms i (atMostVals b (getSlot doms i)))
    (atLeastVals m (getSlot doms j)) j i hij,
    getSlot_setSlot_eq doms _ i hi]

private theorem getSlot_leNarrow_right {i j : Nat} {b m : Int}
    {doms : List (List Value)} (hj : j < doms.length) :
    getSlot (leNarrow b m i j doms) j = atLeastVals m (getSlot doms j) := by
  simp only [leNarrow]
  rw [getSlot_setSlot_eq (setSlot doms i (atMostVals b (getSlot doms i)))
    (atLeastVals m (getSlot doms j)) j (by rw [setSlot_length]; exact hj)]

private theorem getSlot_leNarrow_other {i j k : Nat} {b m : Int}
    {doms : List (List Value)} (hki : k ≠ i) (hkj : k ≠ j) :
    getSlot (leNarrow b m i j doms) k = getSlot doms k := by
  simp only [leNarrow]
  rw [getSlot_setSlot_of_ne (setSlot doms i (atMostVals b (getSlot doms i)))
    (atLeastVals m (getSlot doms j)) j k hkj,
    getSlot_setSlot_of_ne doms (atMostVals b (getSlot doms i)) i k hki]

/-- **Preservation for `propLeSlot`** (PLAN 6.3's local preservation
    theorem, order case): on `narrowed doms'`, every assignment of the
    input domains whose slot values are ordered integers `p ≤ q` is
    still an assignment of `doms'`, and `doms'` is pointwise-subset
    the input domains; on `contradiction`, no assignment of the input
    domains orders the two slots. -/
theorem propLeSlot_preserves (i j : Nat) :
    Preserves (DomConstraint.leSlot i j) (propLeSlot i j) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propLeSlot] at h
    obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, q, hx, hy, hpq⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    have hyj : Value.int q ∈ getSlot doms j := hget j _ hy
    cases hb : domMax (getSlot doms j) with
    | none =>
        obtain ⟨b', hb', _⟩ := domMax_of_mem hyj
        rw [hb] at hb'
        exact absurd hb' (by simp)
    | some b =>
        simp only [hb] at h
        cases hm : domMin (getSlot doms i) with
        | none =>
            obtain ⟨m', hm', _⟩ := domMin_of_mem hxi
            rw [hm] at hm'
            exact absurd hm' (by simp)
        | some m =>
            simp only [hm] at h
            obtain ⟨b', hb', hqb'⟩ := domMax_of_mem hyj
            rw [hb] at hb'
            have hbb : b' = b := (Option.some.inj hb').symm
            rw [hbb] at hqb'
            obtain ⟨m', hm', hmp'⟩ := domMin_of_mem hxi
            rw [hm] at hm'
            have hmm : m' = m := (Option.some.inj hm').symm
            rw [hmm] at hmp'
            by_cases hc : (atMostVals b (getSlot doms i)).isEmpty = true ∨
              (atLeastVals m (getSlot doms j)).isEmpty = true
            · rw [if_pos hc] at h
              exact absurd h (by simp)
            · rw [if_neg hc] at h
              have hd : leNarrow b m i j doms = doms' := PropResult.narrowed.inj h
              subst hd
              apply allAssigns_intro
              · have hlen2 : (leNarrow b m i j doms).length = doms.length := by
                  simp only [leNarrow, setSlot_length]
                rw [hlen2]
                exact hlen
              · intro k v hv
                by_cases hkj : k = j
                · rw [hkj] at hv
                  have hvq : v = Value.int q := Option.some.inj (hv.symm.trans hy)
                  subst hvq
                  rw [hkj, getSlot_leNarrow_right (lt_length_of_mem_getSlot doms j _ hyj)]
                  exact mem_atLeastVals.mpr ⟨hyj, q, rfl, by omega⟩
                · by_cases hki : k = i
                  · rw [hki] at hv
                    have hvp : v = Value.int p := Option.some.inj (hv.symm.trans hx)
                    subst hvp
                    rw [hki, getSlot_leNarrow_left (lt_length_of_mem_getSlot doms i _ hxi)
                      (fun hij => hkj (hki.trans hij))]
                    exact mem_atMostVals.mpr ⟨hxi, p, rfl, by omega⟩
                  · rw [getSlot_leNarrow_other (fun h => hki h) (fun h => hkj h)]
                    exact hget k v hv
  · intro doms doms' h
    simp only [propLeSlot] at h
    cases hb : domMax (getSlot doms j) with
    | none => simp only [hb] at h; exact absurd h (by simp)
    | some b =>
        simp only [hb] at h
        cases hm : domMin (getSlot doms i) with
        | none => simp only [hm] at h; exact absurd h (by simp)
        | some m =>
            simp only [hm] at h
            by_cases hc : (atMostVals b (getSlot doms i)).isEmpty = true ∨
              (atLeastVals m (getSlot doms j)).isEmpty = true
            · rw [if_pos hc] at h
              exact absurd h (by simp)
            · rw [if_neg hc] at h
              have hd : leNarrow b m i j doms = doms' := PropResult.narrowed.inj h
              subst hd
              simp only [leNarrow]
              exact DomPointwiseSub.setSlot
                (DomPointwiseSub.setSlot (DomPointwiseSub.refl doms)
                  (fun _ hv => (mem_atMostVals.mp hv).1))
                (fun _ hv => (mem_atLeastVals.mp hv).1)
  · intro doms h a ha hsat
    simp only [propLeSlot] at h
    obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, q, hx, hy, hpq⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    have hyj : Value.int q ∈ getSlot doms j := hget j _ hy
    cases hb : domMax (getSlot doms j) with
    | none =>
        obtain ⟨b', hb', _⟩ := domMax_of_mem hyj
        rw [hb] at hb'
        exact absurd hb' (by simp)
    | some b =>
        simp only [hb] at h
        cases hm : domMin (getSlot doms i) with
        | none =>
            obtain ⟨m', hm', _⟩ := domMin_of_mem hxi
            rw [hm] at hm'
            exact absurd hm' (by simp)
        | some m =>
            simp only [hm] at h
            obtain ⟨b', hb', hqb'⟩ := domMax_of_mem hyj
            rw [hb] at hb'
            have hbb : b' = b := (Option.some.inj hb').symm
            rw [hbb] at hqb'
            obtain ⟨m', hm', hmp'⟩ := domMin_of_mem hxi
            rw [hm] at hm'
            have hmm : m' = m := (Option.some.inj hm').symm
            rw [hmm] at hmp'
            by_cases hc : (atMostVals b (getSlot doms i)).isEmpty = true ∨
              (atLeastVals m (getSlot doms j)).isEmpty = true
            · rw [if_pos hc] at h
              rcases hc with hcl | hcr
              · have hmem : Value.int p ∈ atMostVals b (getSlot doms i) :=
                  mem_atMostVals.mpr ⟨hxi, p, rfl, by omega⟩
                rw [List.isEmpty_iff.mp hcl] at hmem
                exact absurd hmem (by simp)
              · have hmem : Value.int q ∈ atLeastVals m (getSlot doms j) :=
                  mem_atLeastVals.mpr ⟨hyj, q, rfl, by omega⟩
                rw [List.isEmpty_iff.mp hcr] at hmem
                exact absurd hmem (by simp)
            · rw [if_neg hc] at h
              exact absurd h (by simp)

/-! ## The constant-equality propagator -/

/-- **The constant-equality propagator** (`int_eq` style, slot vs
    constant): slot `i`'s domain narrows to the constant when the
    constant is present; `contradiction` when it is absent. -/
def propConstEq (i : Nat) (v : Value) (doms : List (List Value)) : PropResult :=
  if valueMemB v (getSlot doms i) = true then
    .narrowed (setSlot doms i [v])
  else
    .contradiction

/-- **Preservation for `propConstEq`** (PLAN 6.3's local preservation
    theorem, constant case): on `narrowed doms'`, every assignment of
    the input domains whose slot `i` carries the constant is still an
    assignment of `doms'`, and `doms'` is pointwise-subset the input
    domains; on `contradiction`, no assignment of the input domains
    carries the constant at slot `i`. -/
theorem propConstEq_preserves (i : Nat) (v : Value) :
    Preserves (DomConstraint.constEq i v) (propConstEq i v) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propConstEq] at h
    by_cases hc : valueMemB v (getSlot doms i) = true
    · rw [if_pos hc] at h
      have hd : setSlot doms i [v] = doms' := PropResult.narrowed.inj h
      subst hd
      obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
      apply allAssigns_intro
      · rw [setSlot_length]
        exact hlen
      · intro k v' hv'
        by_cases hki : k = i
        · rw [hki] at hv'
          have hvv : v' = v := Option.some.inj (hv'.symm.trans hsat)
          rw [hki, getSlot_setSlot_eq doms [v] i
            (lt_length_of_mem_getSlot doms i v (valueMemB_iff.mp hc))]
          exact List.mem_singleton.mpr hvv
        · rw [getSlot_setSlot_of_ne doms [v] i k hki]
          exact hget k v' hv'
    · rw [if_neg hc] at h
      exact absurd h (by simp)
  · intro doms doms' h
    simp only [propConstEq] at h
    by_cases hc : valueMemB v (getSlot doms i) = true
    · rw [if_pos hc] at h
      have hd : setSlot doms i [v] = doms' := PropResult.narrowed.inj h
      subst hd
      exact DomPointwiseSub.setSlot (DomPointwiseSub.refl doms)
        (fun w hw => by
          have hwv : w = v := List.mem_singleton.mp hw
          subst hwv
          exact valueMemB_iff.mp hc)
    · rw [if_neg hc] at h
      exact absurd h (by simp)
  · intro doms _h a ha hsat
    simp only [propConstEq] at _h
    by_cases hc : valueMemB v (getSlot doms i) = true
    · rw [if_pos hc] at _h
      exact absurd _h (by simp)
    · obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
      exact absurd (valueMemB_iff.mpr (hget i v hsat)) hc

/-! ## The plus propagator (bounds propagation) -/

/-- The plus narrowing: each of the three slots takes its implied
    interval, each filter computed once (on the *input* domains — the
    bounds are sound independently, so coinciding slot positions are
    harmless: whichever write lands last keeps a sound domain). -/
private def plusNarrow (di' dj' dk' : List Value) (i j k : Nat)
    (doms : List (List Value)) : List (List Value) :=
  setSlot (setSlot (setSlot doms i di') j dj') k dk'

/-- The bounded plus propagation: given all three domains' integer
    extrema, narrow each slot to its implied interval;
    `contradiction` when any side empties. -/
private def propPlusBounded (ilo ihi jlo jhi klo khi : Int) (i j k : Nat)
    (doms : List (List Value)) : PropResult :=
  let di' := atLeastVals (klo - jhi) (atMostVals (khi - jlo) (getSlot doms i))
  let dj' := atLeastVals (klo - ihi) (atMostVals (khi - ilo) (getSlot doms j))
  let dk' := atLeastVals (ilo + jlo) (atMostVals (ihi + jhi) (getSlot doms k))
  if di'.isEmpty = true ∨ dj'.isEmpty = true ∨ dk'.isEmpty = true then
    .contradiction
  else
    .narrowed (plusNarrow di' dj' dk' i j k doms)

/-- **The plus propagator** (`int_plus` style on three slots): bounds
    propagation for `x + y = z` — slot `i` keeps values `p` with
    `zmin - ymax ≤ p ≤ zmax - ymin`, slot `j` symmetrically, slot `k`
    keeps values in `[xmin + ymin, xmax + ymax]`.  `contradiction`
    when any side empties or any of the three domains has no
    integers (a satisfying assignment needs an integer in each). -/
def propPlusSlot (i j k : Nat) (doms : List (List Value)) : PropResult :=
  match domMin (getSlot doms i) with
  | none => .contradiction
  | some ilo =>
      match domMax (getSlot doms i) with
      | none => .contradiction
      | some ihi =>
          match domMin (getSlot doms j) with
          | none => .contradiction
          | some jlo =>
              match domMax (getSlot doms j) with
              | none => .contradiction
              | some jhi =>
                  match domMin (getSlot doms k) with
                  | none => .contradiction
                  | some klo =>
                      match domMax (getSlot doms k) with
                      | none => .contradiction
                      | some khi => propPlusBounded ilo ihi jlo jhi klo khi i j k doms

/-- Reading back the three written slots of a `plusNarrow` (the
    `k`-write is outermost, then `j`, then `i`). -/
private theorem getSlot_plusNarrow_k {di' dj' dk' : List Value} {i j k : Nat}
    {doms : List (List Value)} (hk : k < doms.length) :
    getSlot (plusNarrow di' dj' dk' i j k doms) k = dk' := by
  simp only [plusNarrow]
  rw [getSlot_setSlot_eq (setSlot (setSlot doms i di') j dj') dk' k
    (by rw [setSlot_length, setSlot_length]; exact hk)]

private theorem getSlot_plusNarrow_j {di' dj' dk' : List Value} {i j k : Nat}
    {doms : List (List Value)} (hj : j < doms.length) (hjk : j ≠ k) :
    getSlot (plusNarrow di' dj' dk' i j k doms) j = dj' := by
  simp only [plusNarrow]
  rw [getSlot_setSlot_of_ne (setSlot (setSlot doms i di') j dj') dk' k j hjk,
    getSlot_setSlot_eq (setSlot doms i di') dj' j
    (by rw [setSlot_length]; exact hj)]

private theorem getSlot_plusNarrow_i {di' dj' dk' : List Value} {i j k : Nat}
    {doms : List (List Value)} (hi : i < doms.length) (hij : i ≠ j) (hik : i ≠ k) :
    getSlot (plusNarrow di' dj' dk' i j k doms) i = di' := by
  simp only [plusNarrow]
  rw [getSlot_setSlot_of_ne (setSlot (setSlot doms i di') j dj') dk' k i hik,
    getSlot_setSlot_of_ne (setSlot doms i di') dj' j i hij,
    getSlot_setSlot_eq doms di' i hi]

private theorem getSlot_plusNarrow_other {di' dj' dk' : List Value} {i j k m : Nat}
    {doms : List (List Value)} (hmi : m ≠ i) (hmj : m ≠ j) (hmk : m ≠ k) :
    getSlot (plusNarrow di' dj' dk' i j k doms) m = getSlot doms m := by
  simp only [plusNarrow]
  rw [getSlot_setSlot_of_ne (setSlot (setSlot doms i di') j dj') dk' k m hmk,
    getSlot_setSlot_of_ne (setSlot doms i di') dj' j m hmj,
    getSlot_setSlot_of_ne doms di' i m hmi]

/-- **Preservation for `propPlusSlot`** (PLAN 6.3's local preservation
    theorem, plus case): on `narrowed doms'`, every assignment of the
    input domains whose slot values are integers `p + q = r` is still
    an assignment of `doms'` (each slot's narrowed interval contains
    its satisfying value — `p ≥ zmin - ymax` etc. follow from the
    domain-extrema bounds and the equation), and `doms'` is
    pointwise-subset the input domains; on `contradiction`, no
    assignment of the input domains solves the equation. -/
theorem propPlusSlot_preserves (i j k : Nat) :
    Preserves (DomConstraint.plusSlot i j k) (propPlusSlot i j k) := by
  constructor
  · -- narrowing soundness
    intro doms doms' h a ha hsat
    simp only [propPlusSlot] at h
    obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, q, r, hx, hy, hz, hpqr⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    have hyj : Value.int q ∈ getSlot doms j := hget j _ hy
    have hzk : Value.int r ∈ getSlot doms k := hget k _ hz
    cases h1 : domMin (getSlot doms i) with
    | none => rw [h1] at h; exact absurd h (by simp)
    | some ilo =>
        simp only [h1] at h
        cases h2 : domMax (getSlot doms i) with
        | none => rw [h2] at h; exact absurd h (by simp)
        | some ihi =>
            simp only [h2] at h
            cases h3 : domMin (getSlot doms j) with
            | none => rw [h3] at h; exact absurd h (by simp)
            | some jlo =>
                simp only [h3] at h
                cases h4 : domMax (getSlot doms j) with
                | none => rw [h4] at h; exact absurd h (by simp)
                | some jhi =>
                    simp only [h4] at h
                    cases h5 : domMin (getSlot doms k) with
                    | none => rw [h5] at h; exact absurd h (by simp)
                    | some klo =>
                        simp only [h5] at h
                        cases h6 : domMax (getSlot doms k) with
                        | none => rw [h6] at h; exact absurd h (by simp)
                        | some khi =>
                            simp only [h6, propPlusBounded] at h
                            -- pin the extrema to the satisfying values' bounds
                            obtain ⟨m1, hm1, hplo⟩ := domMin_of_mem hxi
                            rw [h1] at hm1
                            have hilo : m1 = ilo := (Option.some.inj hm1).symm
                            rw [hilo] at hplo
                            obtain ⟨m2, hm2, hphi⟩ := domMax_of_mem hxi
                            rw [h2] at hm2
                            have hihi : m2 = ihi := (Option.some.inj hm2).symm
                            rw [hihi] at hphi
                            obtain ⟨m3, hm3, hqlo⟩ := domMin_of_mem hyj
                            rw [h3] at hm3
                            have hjlo : m3 = jlo := (Option.some.inj hm3).symm
                            rw [hjlo] at hqlo
                            obtain ⟨m4, hm4, hqhi⟩ := domMax_of_mem hyj
                            rw [h4] at hm4
                            have hjhi : m4 = jhi := (Option.some.inj hm4).symm
                            rw [hjhi] at hqhi
                            obtain ⟨m5, hm5, hrlo⟩ := domMin_of_mem hzk
                            rw [h5] at hm5
                            have hklo : m5 = klo := (Option.some.inj hm5).symm
                            rw [hklo] at hrlo
                            obtain ⟨m6, hm6, hrhi⟩ := domMax_of_mem hzk
                            rw [h6] at hm6
                            have hkhi : m6 = khi := (Option.some.inj hm6).symm
                            rw [hkhi] at hrhi
                            by_cases hc : (atLeastVals (klo - jhi)
                                (atMostVals (khi - jlo) (getSlot doms i))).isEmpty = true ∨
                              (atLeastVals (klo - ihi)
                                (atMostVals (khi - ilo) (getSlot doms j))).isEmpty = true ∨
                              (atLeastVals (ilo + jlo)
                                (atMostVals (ihi + jhi) (getSlot doms k))).isEmpty = true
                            · rw [if_pos hc] at h
                              exact absurd h (by simp)
                            · rw [if_neg hc] at h
                              have hd : plusNarrow
                                  (atLeastVals (klo - jhi)
                                    (atMostVals (khi - jlo) (getSlot doms i)))
                                  (atLeastVals (klo - ihi)
                                    (atMostVals (khi - ilo) (getSlot doms j)))
                                  (atLeastVals (ilo + jlo)
                                    (atMostVals (ihi + jhi) (getSlot doms k)))
                                  i j k doms = doms' := PropResult.narrowed.inj h
                              subst hd
                              apply allAssigns_intro
                              · have hlen2 : (plusNarrow
                                  (atLeastVals (klo - jhi)
                                    (atMostVals (khi - jlo) (getSlot doms i)))
                                  (atLeastVals (klo - ihi)
                                    (atMostVals (khi - ilo) (getSlot doms j)))
                                  (atLeastVals (ilo + jlo)
                                    (atMostVals (ihi + jhi) (getSlot doms k)))
                                  i j k doms).length = doms.length := by
                                  simp only [plusNarrow, setSlot_length]
                                rw [hlen2]
                                exact hlen
                              · intro m v hv
                                by_cases hmk : m = k
                                · rw [hmk] at hv
                                  have hvr : v = Value.int r :=
                                    Option.some.inj (hv.symm.trans hz)
                                  subst hvr
                                  rw [hmk, getSlot_plusNarrow_k
                                    (lt_length_of_mem_getSlot doms k _ hzk)]
                                  exact mem_atLeastVals_atMostVals.mpr
                                    ⟨hzk, r, rfl, by omega, by omega⟩
                                · by_cases hmj : m = j
                                  · rw [hmj] at hv
                                    have hvq : v = Value.int q :=
                                      Option.some.inj (hv.symm.trans hy)
                                    subst hvq
                                    rw [hmj, getSlot_plusNarrow_j
                                      (lt_length_of_mem_getSlot doms j _ hyj)
                                      (fun hjk => hmk (hmj.trans hjk))]
                                    exact mem_atLeastVals_atMostVals.mpr
                                      ⟨hyj, q, rfl, by omega, by omega⟩
                                  · by_cases hmi : m = i
                                    · rw [hmi] at hv
                                      have hvp : v = Value.int p :=
                                        Option.some.inj (hv.symm.trans hx)
                                      subst hvp
                                      rw [hmi, getSlot_plusNarrow_i
                                        (lt_length_of_mem_getSlot doms i _ hxi)
                                        (fun hij => hmj (hmi.trans hij))
                                        (fun hik => hmk (hmi.trans hik))]
                                      exact mem_atLeastVals_atMostVals.mpr
                                        ⟨hxi, p, rfl, by omega, by omega⟩
                                    · rw [getSlot_plusNarrow_other
                                        (fun h => hmi h) (fun h => hmj h)
                                        (fun h => hmk h)]
                                      exact hget m v hv
  · -- subset
    intro doms doms' h
    simp only [propPlusSlot] at h
    cases h1 : domMin (getSlot doms i) with
    | none => rw [h1] at h; exact absurd h (by simp)
    | some ilo =>
        simp only [h1] at h
        cases h2 : domMax (getSlot doms i) with
        | none => rw [h2] at h; exact absurd h (by simp)
        | some ihi =>
            simp only [h2] at h
            cases h3 : domMin (getSlot doms j) with
            | none => rw [h3] at h; exact absurd h (by simp)
            | some jlo =>
                simp only [h3] at h
                cases h4 : domMax (getSlot doms j) with
                | none => rw [h4] at h; exact absurd h (by simp)
                | some jhi =>
                    simp only [h4] at h
                    cases h5 : domMin (getSlot doms k) with
                    | none => rw [h5] at h; exact absurd h (by simp)
                    | some klo =>
                        simp only [h5] at h
                        cases h6 : domMax (getSlot doms k) with
                        | none => rw [h6] at h; exact absurd h (by simp)
                        | some khi =>
                            simp only [h6, propPlusBounded] at h
                            by_cases hc : (atLeastVals (klo - jhi)
                                (atMostVals (khi - jlo) (getSlot doms i))).isEmpty = true ∨
                              (atLeastVals (klo - ihi)
                                (atMostVals (khi - ilo) (getSlot doms j))).isEmpty = true ∨
                              (atLeastVals (ilo + jlo)
                                (atMostVals (ihi + jhi) (getSlot doms k))).isEmpty = true
                            · rw [if_pos hc] at h
                              exact absurd h (by simp)
                            · rw [if_neg hc] at h
                              have hd : plusNarrow
                                  (atLeastVals (klo - jhi)
                                    (atMostVals (khi - jlo) (getSlot doms i)))
                                  (atLeastVals (klo - ihi)
                                    (atMostVals (khi - ilo) (getSlot doms j)))
                                  (atLeastVals (ilo + jlo)
                                    (atMostVals (ihi + jhi) (getSlot doms k)))
                                  i j k doms = doms' := PropResult.narrowed.inj h
                              subst hd
                              simp only [plusNarrow]
                              exact DomPointwiseSub.setSlot
                                (DomPointwiseSub.setSlot
                                  (DomPointwiseSub.setSlot (DomPointwiseSub.refl doms)
                                    (fun _ hv => (mem_atLeastVals_atMostVals.mp hv).1))
                                  (fun _ hv => (mem_atLeastVals_atMostVals.mp hv).1))
                                (fun _ hv => (mem_atLeastVals_atMostVals.mp hv).1)
  · -- contradiction soundness
    intro doms h a ha hsat
    simp only [propPlusSlot] at h
    obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, q, r, hx, hy, hz, hpqr⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    have hyj : Value.int q ∈ getSlot doms j := hget j _ hy
    have hzk : Value.int r ∈ getSlot doms k := hget k _ hz
    cases h1 : domMin (getSlot doms i) with
    | none =>
        obtain ⟨m, hm, _⟩ := domMin_of_mem hxi
        rw [h1] at hm
        exact absurd hm (by simp)
    | some ilo =>
        simp only [h1] at h
        cases h2 : domMax (getSlot doms i) with
        | none =>
            obtain ⟨m, hm, _⟩ := domMax_of_mem hxi
            rw [h2] at hm
            exact absurd hm (by simp)
        | some ihi =>
            simp only [h2] at h
            cases h3 : domMin (getSlot doms j) with
            | none =>
                obtain ⟨m, hm, _⟩ := domMin_of_mem hyj
                rw [h3] at hm
                exact absurd hm (by simp)
            | some jlo =>
                simp only [h3] at h
                cases h4 : domMax (getSlot doms j) with
                | none =>
                    obtain ⟨m, hm, _⟩ := domMax_of_mem hyj
                    rw [h4] at hm
                    exact absurd hm (by simp)
                | some jhi =>
                    simp only [h4] at h
                    cases h5 : domMin (getSlot doms k) with
                    | none =>
                        obtain ⟨m, hm, _⟩ := domMin_of_mem hzk
                        rw [h5] at hm
                        exact absurd hm (by simp)
                    | some klo =>
                        simp only [h5] at h
                        cases h6 : domMax (getSlot doms k) with
                        | none =>
                            obtain ⟨m, hm, _⟩ := domMax_of_mem hzk
                            rw [h6] at hm
                            exact absurd hm (by simp)
                        | some khi =>
                            simp only [h6, propPlusBounded] at h
                            -- pin the extrema to the satisfying values' bounds
                            obtain ⟨m1, hm1, hplo⟩ := domMin_of_mem hxi
                            rw [h1] at hm1
                            have hilo : m1 = ilo := (Option.some.inj hm1).symm
                            rw [hilo] at hplo
                            obtain ⟨m2, hm2, hphi⟩ := domMax_of_mem hxi
                            rw [h2] at hm2
                            have hihi : m2 = ihi := (Option.some.inj hm2).symm
                            rw [hihi] at hphi
                            obtain ⟨m3, hm3, hqlo⟩ := domMin_of_mem hyj
                            rw [h3] at hm3
                            have hjlo : m3 = jlo := (Option.some.inj hm3).symm
                            rw [hjlo] at hqlo
                            obtain ⟨m4, hm4, hqhi⟩ := domMax_of_mem hyj
                            rw [h4] at hm4
                            have hjhi : m4 = jhi := (Option.some.inj hm4).symm
                            rw [hjhi] at hqhi
                            obtain ⟨m5, hm5, hrlo⟩ := domMin_of_mem hzk
                            rw [h5] at hm5
                            have hklo : m5 = klo := (Option.some.inj hm5).symm
                            rw [hklo] at hrlo
                            obtain ⟨m6, hm6, hrhi⟩ := domMax_of_mem hzk
                            rw [h6] at hm6
                            have hkhi : m6 = khi := (Option.some.inj hm6).symm
                            rw [hkhi] at hrhi
                            by_cases hc : (atLeastVals (klo - jhi)
                                (atMostVals (khi - jlo) (getSlot doms i))).isEmpty = true ∨
                              (atLeastVals (klo - ihi)
                                (atMostVals (khi - ilo) (getSlot doms j))).isEmpty = true ∨
                              (atLeastVals (ilo + jlo)
                                (atMostVals (ihi + jhi) (getSlot doms k))).isEmpty = true
                            · rw [if_pos hc] at h
                              rcases hc with hci | hcj | hck
                              · have hmem : Value.int p ∈ atLeastVals (klo - jhi)
                                    (atMostVals (khi - jlo) (getSlot doms i)) :=
                                  mem_atLeastVals_atMostVals.mpr
                                    ⟨hxi, p, rfl, by omega, by omega⟩
                                rw [List.isEmpty_iff.mp hci] at hmem
                                exact absurd hmem (by simp)
                              · have hmem : Value.int q ∈ atLeastVals (klo - ihi)
                                    (atMostVals (khi - ilo) (getSlot doms j)) :=
                                  mem_atLeastVals_atMostVals.mpr
                                    ⟨hyj, q, rfl, by omega, by omega⟩
                                rw [List.isEmpty_iff.mp hcj] at hmem
                                exact absurd hmem (by simp)
                              · have hmem : Value.int r ∈ atLeastVals (ilo + jlo)
                                    (atMostVals (ihi + jhi) (getSlot doms k)) :=
                                  mem_atLeastVals_atMostVals.mpr
                                    ⟨hzk, r, rfl, by omega, by omega⟩
                                rw [List.isEmpty_iff.mp hck] at hmem
                                exact absurd hmem (by simp)
                            · rw [if_neg hc] at h
                              exact absurd h (by simp)

/-! ## The constant-bound order propagators -/

/-- **The upper-bound propagator** (`int_le(x, c)` style, slot vs
    constant): slot `i`'s domain keeps its integer values `≤ c`;
    `contradiction` when that empties (no integer in the domain can
    satisfy `p ≤ c`). -/
def propLeConstHi (i : Nat) (c : Int) (doms : List (List Value)) : PropResult :=
  let d' := atMostVals c (getSlot doms i)
  if d'.isEmpty = true then .contradiction
  else .narrowed (setSlot doms i d')

/-- **Preservation for `propLeConstHi`** (PLAN 6.3's local
    preservation theorem, upper-bound case): on `narrowed doms'`,
    every assignment of the input domains whose slot `i` value is an
    integer `p ≤ c` is still an assignment of `doms'`, and `doms'`
    is pointwise-subset the input domains; on `contradiction`, no
    assignment of the input domains bounds slot `i` by `c`. -/
theorem propLeConstHi_preserves (i : Nat) (c : Int) :
    Preserves (DomConstraint.leConstHi i c) (propLeConstHi i c) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propLeConstHi] at h
    obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, hx, hpc⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    by_cases hc : (atMostVals c (getSlot doms i)).isEmpty = true
    · rw [if_pos hc] at h
      exact absurd h (by simp)
    · rw [if_neg hc] at h
      have hd : setSlot doms i (atMostVals c (getSlot doms i)) = doms' :=
        PropResult.narrowed.inj h
      subst hd
      apply allAssigns_intro
      · rw [setSlot_length]
        exact hlen
      · intro m v hv
        by_cases hmi : m = i
        · rw [hmi] at hv
          have hvp : v = Value.int p := Option.some.inj (hv.symm.trans hx)
          subst hvp
          rw [hmi, getSlot_setSlot_eq doms (atMostVals c (getSlot doms i)) i
            (lt_length_of_mem_getSlot doms i _ hxi)]
          exact mem_atMostVals.mpr ⟨hxi, p, rfl, hpc⟩
        · rw [getSlot_setSlot_of_ne doms (atMostVals c (getSlot doms i)) i m hmi]
          exact hget m v hv
  · intro doms doms' h
    simp only [propLeConstHi] at h
    by_cases hc : (atMostVals c (getSlot doms i)).isEmpty = true
    · rw [if_pos hc] at h
      exact absurd h (by simp)
    · rw [if_neg hc] at h
      have hd : setSlot doms i (atMostVals c (getSlot doms i)) = doms' :=
        PropResult.narrowed.inj h
      subst hd
      exact DomPointwiseSub.setSlot (DomPointwiseSub.refl doms)
        (fun _ hv => (mem_atMostVals.mp hv).1)
  · intro doms h a ha hsat
    simp only [propLeConstHi] at h
    obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, hx, hpc⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    by_cases hc : (atMostVals c (getSlot doms i)).isEmpty = true
    · rw [if_pos hc] at h
      have hmem : Value.int p ∈ atMostVals c (getSlot doms i) :=
        mem_atMostVals.mpr ⟨hxi, p, rfl, hpc⟩
      rw [List.isEmpty_iff.mp hc] at hmem
      exact absurd hmem (by simp)
    · rw [if_neg hc] at h
      exact absurd h (by simp)

/-- **The lower-bound propagator** (`int_le(c, x)` style, constant vs
    slot): slot `i`'s domain keeps its integer values `≥ c`;
    `contradiction` when that empties. -/
def propLeConstLo (i : Nat) (c : Int) (doms : List (List Value)) : PropResult :=
  let d' := atLeastVals c (getSlot doms i)
  if d'.isEmpty = true then .contradiction
  else .narrowed (setSlot doms i d')

/-- **Preservation for `propLeConstLo`** (the symmetric local
    preservation theorem, lower-bound case). -/
theorem propLeConstLo_preserves (i : Nat) (c : Int) :
    Preserves (DomConstraint.leConstLo i c) (propLeConstLo i c) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propLeConstLo] at h
    obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, hx, hcp⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    by_cases hc : (atLeastVals c (getSlot doms i)).isEmpty = true
    · rw [if_pos hc] at h
      exact absurd h (by simp)
    · rw [if_neg hc] at h
      have hd : setSlot doms i (atLeastVals c (getSlot doms i)) = doms' :=
        PropResult.narrowed.inj h
      subst hd
      apply allAssigns_intro
      · rw [setSlot_length]
        exact hlen
      · intro m v hv
        by_cases hmi : m = i
        · rw [hmi] at hv
          have hvp : v = Value.int p := Option.some.inj (hv.symm.trans hx)
          subst hvp
          rw [hmi, getSlot_setSlot_eq doms (atLeastVals c (getSlot doms i)) i
            (lt_length_of_mem_getSlot doms i _ hxi)]
          exact mem_atLeastVals.mpr ⟨hxi, p, rfl, hcp⟩
        · rw [getSlot_setSlot_of_ne doms (atLeastVals c (getSlot doms i)) i m hmi]
          exact hget m v hv
  · intro doms doms' h
    simp only [propLeConstLo] at h
    by_cases hc : (atLeastVals c (getSlot doms i)).isEmpty = true
    · rw [if_pos hc] at h
      exact absurd h (by simp)
    · rw [if_neg hc] at h
      have hd : setSlot doms i (atLeastVals c (getSlot doms i)) = doms' :=
        PropResult.narrowed.inj h
      subst hd
      exact DomPointwiseSub.setSlot (DomPointwiseSub.refl doms)
        (fun _ hv => (mem_atLeastVals.mp hv).1)
  · intro doms h a ha hsat
    simp only [propLeConstLo] at h
    obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, hx, hcp⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    by_cases hc : (atLeastVals c (getSlot doms i)).isEmpty = true
    · rw [if_pos hc] at h
      have hmem : Value.int p ∈ atLeastVals c (getSlot doms i) :=
        mem_atLeastVals.mpr ⟨hxi, p, rfl, hcp⟩
      rw [List.isEmpty_iff.mp hc] at hmem
      exact absurd hmem (by simp)
    · rw [if_neg hc] at h
      exact absurd h (by simp)

/-! ## The all-different propagator (pigeonhole counting) -/

/-- The slots of `is` that are in range of `doms`: out-of-range
    positions read no value in any assignment, so only the in-range
    ones demand distinct values of the union. -/
def inRangeSlots (doms : List (List Value)) (is : List Nat) : List Nat :=
  is.filter (fun i => decide (i < doms.length))

/-- The number of distinct values in the union of the domains of the
    slots `is` (the deduplicated concatenation, first occurrence
    kept). -/
def distinctUnionVals (doms : List (List Value)) (is : List Nat) : List Value :=
  dedupVals (is.flatMap (getSlot doms))

/-- **The all-different propagator** (`all_different` style over a
    sub-list of slots): pigeonhole counting — if the number of
    in-range slots is greater than the number of distinct values in
    the union of their domains, `contradiction` (any satisfying
    assignment reads pairwise-distinct values at those slots, each in
    its slot's domain, so the union must hold at least as many
    distinct values as there are slots); otherwise nothing is
    narrowed (bounds and Hall-interval reasoning are future work). -/
def propAllDiff (is : List Nat) (doms : List (List Value)) : PropResult :=
  if (inRangeSlots doms is).length > (distinctUnionVals doms is).length then
    .contradiction
  else
    .narrowed doms

/-- **The pigeonhole bound, membership form**: if an assignment satisfies
    the pairwise-distinctness and reads, at every in-range slot, a value of
    the deduplicated union, then the in-range slots are at most as many as
    the union's distinct values. (The `allAssigns` form below derives the
    membership from the domains; this form is what the Hall-clause
    entailment needs, where the membership is DERIVED from the clause's
    falsity instead.) -/
theorem allDiff_pigeonhole_of_mem {doms : List (List Value)} {is : List Nat}
    {a : List Value}
    (hsat : DomConstraint.SatisfiedBy (DomConstraint.allDiff is) a)
    (hmem : ∀ i ∈ inRangeSlots doms is, a[i]! ∈ distinctUnionVals doms is) :
    (inRangeSlots doms is).length ≤ (distinctUnionVals doms is).length := by
  have hmem' : ∀ (x : Value), x ∈ (inRangeSlots doms is).map (fun i => a[i]!) →
      x ∈ distinctUnionVals doms is := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := List.mem_map.mp hx
    rw [← hxi]
    exact hmem i hi
  have hnd : ((inRangeSlots doms is).map (fun i => a[i]!)).Nodup := by
    have hfilt : inRangeSlots doms is <+ is := List.filter_sublist
    have hsub : (inRangeSlots doms is).map (fun i => a[i]!) <+
        is.map (fun i => a[i]!) := List.Sublist.map _ hfilt
    exact List.Nodup.sublist hsub hsat
  have hwnd : (distinctUnionVals doms is).Nodup := nodup_dedupVals _
  have hle := nodup_subset_length_le _ _ hnd hmem' hwnd
  rw [List.length_map] at hle
  exact hle

/-- **The pigeonhole bound**: if a complete assignment of `doms`
    makes the values read at the slots of `is` pairwise distinct, then
    the number of in-range slots is at most the number of distinct
    values in the union of their domains.  The proof maps each
    in-range slot to the value the assignment reads there — a
    duplicate-free list (pairwise distinctness) whose values all lie
    in the duplicate-free union — and applies the list pigeonhole
    `nodup_subset_length_le`. -/
private theorem allDiff_pigeonhole {doms : List (List Value)} {is : List Nat}
    {a : List Value} (ha : a ∈ allAssigns doms)
    (hsat : DomConstraint.SatisfiedBy (DomConstraint.allDiff is) a) :
    (inRangeSlots doms is).length ≤ (distinctUnionVals doms is).length := by
  obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
  -- each in-range slot's read value is in its slot's domain, hence in
  -- the deduplicated union
  have hmem : ∀ (x : Value), x ∈ (inRangeSlots doms is).map (fun i => a[i]!) →
      x ∈ distinctUnionVals doms is := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := List.mem_map.mp hx
    obtain ⟨hin, hilt⟩ := List.mem_filter.mp hi
    rw [decide_eq_true_eq] at hilt
    -- a[i]! is the read value, in slot i's domain by the assignment spec
    have hread : a[i]? = some (a[i]!) := by
      have hlt : i < a.length := by rw [hlen]; exact hilt
      rw [List.getElem?_eq_getElem hlt, getElem!_pos a i hlt]
    have hdom : a[i]! ∈ getSlot doms i := hget i _ hread
    rw [← hxi]
    exact mem_dedupVals _ _ |>.mpr
      (List.mem_flatMap.mpr ⟨i, hin, hdom⟩)
  -- the read values are pairwise distinct (the slots are, per the
  -- filter, a sub-list of is, and the reads along is are distinct)
  have hnd : ((inRangeSlots doms is).map (fun i => a[i]!)).Nodup := by
    have hfilt : inRangeSlots doms is <+ is := List.filter_sublist
    have hsub : (inRangeSlots doms is).map (fun i => a[i]!) <+
        is.map (fun i => a[i]!) := List.Sublist.map _ hfilt
    exact List.Nodup.sublist hsub hsat
  -- the union's deduplication is duplicate-free
  have hwnd : (distinctUnionVals doms is).Nodup := nodup_dedupVals _
  -- the pigeonhole
  have hle := nodup_subset_length_le _ _ hnd hmem hwnd
  rw [List.length_map] at hle
  exact hle

/-- **Preservation for `propAllDiff`** (PLAN 6.3's local preservation
    theorem, all-different case): on `narrowed doms'` (the domains
    unchanged — the propagator only detects contradictions today),
    every assignment satisfying the pairwise-distinctness is trivially
    kept; on `contradiction`, the pigeonhole bound certifies that no
    assignment of the input domains makes the slots pairwise
    distinct. -/
theorem propAllDiff_preserves (is : List Nat) :
    Preserves (DomConstraint.allDiff is) (propAllDiff is) := by
  constructor
  · intro doms doms' h a ha _hsat
    simp only [propAllDiff] at h
    by_cases hc : (inRangeSlots doms is).length > (distinctUnionVals doms is).length
    · rw [if_pos hc] at h
      exact absurd h (by simp)
    · rw [if_neg hc] at h
      have hd : doms' = doms := (PropResult.narrowed.inj h).symm
      subst hd
      exact ha
  · intro doms doms' h
    simp only [propAllDiff] at h
    by_cases hc : (inRangeSlots doms is).length > (distinctUnionVals doms is).length
    · rw [if_pos hc] at h
      exact absurd h (by simp)
    · rw [if_neg hc] at h
      have hd : doms' = doms := (PropResult.narrowed.inj h).symm
      rw [hd]
      exact DomPointwiseSub.refl doms
  · intro doms h a ha hsat
    simp only [propAllDiff] at h
    by_cases hc : (inRangeSlots doms is).length > (distinctUnionVals doms is).length
    · rw [if_pos hc] at h
      have hle := allDiff_pigeonhole ha hsat
      omega
    · rw [if_neg hc] at h
      exact absurd h (by simp)

/-! ## The arithmetic propagators (`times`, `min`, `max`, `abs`)

Each of the four new constraint kinds mirrors the bounds-propagation
pattern of `propPlusSlot`: from the integer extrema of the involved
slot domains, each slot keeps exactly the values that can still
participate in a satisfying assignment:

* `propTimesSlot i j k` — `p * q = r`: slot `i` keeps `p` when the
  (necessary) interval condition `min (p·jlo) (p·jhi) ≤ khi` and
  `klo ≤ max (p·jlo) (p·jhi)` holds — the product `p·q` with `q`
  between `jlo` and `jhi` stays within the two corner products, so a
  result in `[klo, khi]` is impossible outside; slot `j` symmetrically
  (against the extrema of slot `i`); slot `k` keeps only the corner
  interval `[cornerMin ilo ihi jlo jhi, cornerMax ilo ihi jlo jhi]`;
* `propMinSlot i j k` — `min p q = r`: slot `i` keeps `p` when
  `min p jlo ≤ khi` and `klo ≤ min p jhi` (`min` is monotone in both
  arguments, so these are necessary), slot `j` symmetrically, slot `k`
  keeps `[min ilo jlo, min ihi jhi]`; `propMaxSlot` mirrors it with
  `max`, whose monotonicity gives the identical necessary conditions;
* `propAbsSlot i k` — `absValue p = r`: slot `i` keeps `p` with
  `klo ≤ absValue p ≤ khi` (exact — `absValue` is defined), slot `k`
  keeps the nonneg interval `[0, max (absValue ilo) (absValue ihi)]`.

Each propagator returns `contradiction` when a slot domain carries no
integers (a satisfying assignment needs an integer in each involved
slot) or when any narrowed side empties. -/

/-- The three-slot narrowing: each of the three slots takes its
    narrowed list, each filter computed once (on the *input* domains —
    every bound argument holds for any satisfying assignment
    independently, so coinciding slot positions are harmless). -/
private def threeNarrow (di' dj' dk' : List Value) (i j k : Nat)
    (doms : List (List Value)) : List (List Value) :=
  setSlot (setSlot (setSlot doms i di') j dj') k dk'

/-- Reading back the three written slots of a `threeNarrow` (the
    `k`-write is outermost, then `j`, then `i`). -/
private theorem getSlot_threeNarrow_k {di' dj' dk' : List Value} {i j k : Nat}
    {doms : List (List Value)} (hk : k < doms.length) :
    getSlot (threeNarrow di' dj' dk' i j k doms) k = dk' := by
  simp only [threeNarrow]
  rw [getSlot_setSlot_eq (setSlot (setSlot doms i di') j dj') dk' k
    (by rw [setSlot_length, setSlot_length]; exact hk)]

private theorem getSlot_threeNarrow_j {di' dj' dk' : List Value} {i j k : Nat}
    {doms : List (List Value)} (hj : j < doms.length) (hjk : j ≠ k) :
    getSlot (threeNarrow di' dj' dk' i j k doms) j = dj' := by
  simp only [threeNarrow]
  rw [getSlot_setSlot_of_ne (setSlot (setSlot doms i di') j dj') dk' k j hjk,
    getSlot_setSlot_eq (setSlot doms i di') dj' j
    (by rw [setSlot_length]; exact hj)]

private theorem getSlot_threeNarrow_i {di' dj' dk' : List Value} {i j k : Nat}
    {doms : List (List Value)} (hi : i < doms.length) (hij : i ≠ j) (hik : i ≠ k) :
    getSlot (threeNarrow di' dj' dk' i j k doms) i = di' := by
  simp only [threeNarrow]
  rw [getSlot_setSlot_of_ne (setSlot (setSlot doms i di') j dj') dk' k i hik,
    getSlot_setSlot_of_ne (setSlot doms i di') dj' j i hij,
    getSlot_setSlot_eq doms di' i hi]

private theorem getSlot_threeNarrow_other {di' dj' dk' : List Value} {i j k m : Nat}
    {doms : List (List Value)} (hmi : m ≠ i) (hmj : m ≠ j) (hmk : m ≠ k) :
    getSlot (threeNarrow di' dj' dk' i j k doms) m = getSlot doms m := by
  simp only [threeNarrow]
  rw [getSlot_setSlot_of_ne (setSlot (setSlot doms i di') j dj') dk' k m hmk,
    getSlot_setSlot_of_ne (setSlot doms i di') dj' j m hmj,
    getSlot_setSlot_of_ne doms di' i m hmi]

/-! ### The min propagator -/

/-- The keep test for a `min` operand: an integer value `v = .int p`
    can participate in a satisfying `min p q = r` with `q ∈ [jlo, jhi]`
    and `r ∈ [klo, khi]` only when both necessary interval conditions
    hold (monotonicity of `min` in each argument). Non-integer values
    are rejected. -/
private def minKeepB (v : Value) (jlo jhi klo khi : Int) : Bool :=
  match v with
  | .int p => decide (min p jlo ≤ khi) && decide (klo ≤ min p jhi)
  | _ => false

private theorem mem_minKeepB_iff {v : Value} {jlo jhi klo khi : Int} :
    minKeepB v jlo jhi klo khi = true ↔
      ∃ p, v = .int p ∧ min p jlo ≤ khi ∧ klo ≤ min p jhi := by
  constructor
  · intro h
    cases v with
    | int p =>
      simp only [minKeepB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨p, rfl, h.1, h.2⟩
    | _ => contradiction
  · rintro ⟨p, rfl, h1, h2⟩
    simp only [minKeepB, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h1, h2⟩

/-- A satisfying triple keeps both `min` operands. -/
private theorem minKeepB_of_satisfying {p q r jlo jhi klo khi : Int}
    (hq1 : jlo ≤ q) (hq2 : q ≤ jhi) (hr1 : klo ≤ r) (hr2 : r ≤ khi)
    (hmin : min p q = r) :
    minKeepB (.int p) jlo jhi klo khi = true := by
  simp only [minKeepB, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨le_trans (min_le_min (le_refl p) hq1) (hmin ▸ hr2),
    le_trans (hmin ▸ hr1) (min_le_min (le_refl p) hq2)⟩

/-- The bounded min propagation: given all three domains' integer
    extrema, narrow each slot; `contradiction` when any side empties. -/
private def propMinBounded (ilo ihi jlo jhi klo khi : Int) (i j k : Nat)
    (doms : List (List Value)) : PropResult :=
  let di' := (getSlot doms i).filter (fun p => minKeepB p jlo jhi klo khi)
  let dj' := (getSlot doms j).filter (fun q => minKeepB q ilo ihi klo khi)
  let dk' := atLeastVals (min ilo jlo) (atMostVals (min ihi jhi) (getSlot doms k))
  if di'.isEmpty = true ∨ dj'.isEmpty = true ∨ dk'.isEmpty = true then
    .contradiction
  else
    .narrowed (threeNarrow di' dj' dk' i j k doms)

/-- **The min propagator** (`int_min` style on three slots): bounds
    propagation for `min p q = r` — slot `i` keeps exactly the values
    passing the necessary `min` interval conditions, slot `j`
    symmetrically, slot `k` keeps `[min ilo jlo, min ihi jhi]`.
    `contradiction` when any side empties or any domain has no
    integers. -/
def propMinSlot (i j k : Nat) (doms : List (List Value)) : PropResult :=
  match domMin (getSlot doms i) with
  | none => .contradiction
  | some ilo =>
      match domMax (getSlot doms i) with
      | none => .contradiction
      | some ihi =>
          match domMin (getSlot doms j) with
          | none => .contradiction
          | some jlo =>
              match domMax (getSlot doms j) with
              | none => .contradiction
              | some jhi =>
                  match domMin (getSlot doms k) with
                  | none => .contradiction
                  | some klo =>
                      match domMax (getSlot doms k) with
                      | none => .contradiction
                      | some khi => propMinBounded ilo ihi jlo jhi klo khi i j k doms

/-- **Preservation for `propMinSlot`** (PLAN 6.3's local preservation
    theorem, min case): on `narrowed doms'`, every assignment of the
    input domains whose slot values are integers `min p q = r` is still
    an assignment of `doms'`, and `doms'` is pointwise-subset the input
    domains; on `contradiction`, no assignment of the input domains
    solves the equation. -/
theorem propMinSlot_preserves (i j k : Nat) :
    Preserves (DomConstraint.minSlot i j k) (propMinSlot i j k) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propMinSlot] at h
    obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, q, r, hx, hy, hz, hmin⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    have hyj : Value.int q ∈ getSlot doms j := hget j _ hy
    have hzk : Value.int r ∈ getSlot doms k := hget k _ hz
    cases h1 : domMin (getSlot doms i) with
    | none => rw [h1] at h; exact absurd h (by simp)
    | some ilo =>
        simp only [h1] at h
        cases h2 : domMax (getSlot doms i) with
        | none => rw [h2] at h; exact absurd h (by simp)
        | some ihi =>
            simp only [h2] at h
            cases h3 : domMin (getSlot doms j) with
            | none => rw [h3] at h; exact absurd h (by simp)
            | some jlo =>
                simp only [h3] at h
                cases h4 : domMax (getSlot doms j) with
                | none => rw [h4] at h; exact absurd h (by simp)
                | some jhi =>
                    simp only [h4] at h
                    cases h5 : domMin (getSlot doms k) with
                    | none => rw [h5] at h; exact absurd h (by simp)
                    | some klo =>
                        simp only [h5] at h
                        cases h6 : domMax (getSlot doms k) with
                        | none => rw [h6] at h; exact absurd h (by simp)
                        | some khi =>
                            simp only [h6, propMinBounded] at h
                            -- pin the extrema to the satisfying values' bounds
                            obtain ⟨m1, hm1, hplo⟩ := domMin_of_mem hxi
                            rw [h1] at hm1
                            have hilo : m1 = ilo := (Option.some.inj hm1).symm
                            rw [hilo] at hplo
                            obtain ⟨m2, hm2, hphi⟩ := domMax_of_mem hxi
                            rw [h2] at hm2
                            have hihi : m2 = ihi := (Option.some.inj hm2).symm
                            rw [hihi] at hphi
                            obtain ⟨m3, hm3, hqlo⟩ := domMin_of_mem hyj
                            rw [h3] at hm3
                            have hjlo : m3 = jlo := (Option.some.inj hm3).symm
                            rw [hjlo] at hqlo
                            obtain ⟨m4, hm4, hqhi⟩ := domMax_of_mem hyj
                            rw [h4] at hm4
                            have hjhi : m4 = jhi := (Option.some.inj hm4).symm
                            rw [hjhi] at hqhi
                            obtain ⟨m5, hm5, hrlo⟩ := domMin_of_mem hzk
                            rw [h5] at hm5
                            have hklo : m5 = klo := (Option.some.inj hm5).symm
                            rw [hklo] at hrlo
                            obtain ⟨m6, hm6, hrhi⟩ := domMax_of_mem hzk
                            rw [h6] at hm6
                            have hkhi : m6 = khi := (Option.some.inj hm6).symm
                            rw [hkhi] at hrhi
                            have hlo_bounds : min ilo jlo ≤ r := by
                              have h1 : min ilo jlo ≤ p := le_trans (min_le_left ilo jlo) hplo
                              have h2 : min ilo jlo ≤ q := le_trans (min_le_right ilo jlo) hqlo
                              have h3 : min ilo jlo ≤ min p q := le_min_iff.mpr ⟨h1, h2⟩
                              rw [hmin] at h3
                              exact h3
                            have hhi_bounds : r ≤ min ihi jhi := by
                              have h3 : min p q ≤ min ihi jhi := min_le_min hphi hqhi
                              rw [hmin] at h3
                              exact h3
                            by_cases hc : ((getSlot doms i).filter
                                (fun p => minKeepB p jlo jhi klo khi)).isEmpty = true ∨
                              ((getSlot doms j).filter
                                (fun q => minKeepB q ilo ihi klo khi)).isEmpty = true ∨
                              (atLeastVals (min ilo jlo)
                                (atMostVals (min ihi jhi) (getSlot doms k))).isEmpty = true
                            · rw [if_pos hc] at h
                              exact absurd h (by simp)
                            · rw [if_neg hc] at h
                              have hd : threeNarrow
                                  ((getSlot doms i).filter
                                    (fun p => minKeepB p jlo jhi klo khi))
                                  ((getSlot doms j).filter
                                    (fun q => minKeepB q ilo ihi klo khi))
                                  (atLeastVals (min ilo jlo)
                                    (atMostVals (min ihi jhi) (getSlot doms k)))
                                  i j k doms = doms' := PropResult.narrowed.inj h
                              subst hd
                              apply allAssigns_intro
                              · have hlen2 : (threeNarrow
                                  ((getSlot doms i).filter
                                    (fun p => minKeepB p jlo jhi klo khi))
                                  ((getSlot doms j).filter
                                    (fun q => minKeepB q ilo ihi klo khi))
                                  (atLeastVals (min ilo jlo)
                                    (atMostVals (min ihi jhi) (getSlot doms k)))
                                  i j k doms).length = doms.length := by
                                  simp only [threeNarrow, setSlot_length]
                                rw [hlen2]
                                exact hlen
                              · intro m v hv
                                by_cases hmk : m = k
                                · rw [hmk] at hv
                                  have hvr : v = Value.int r :=
                                    Option.some.inj (hv.symm.trans hz)
                                  subst hvr
                                  rw [hmk, getSlot_threeNarrow_k
                                    (lt_length_of_mem_getSlot doms k _ hzk)]
                                  exact mem_atLeastVals_atMostVals.mpr
                                    ⟨hzk, r, rfl, hlo_bounds, hhi_bounds⟩
                                · by_cases hmj : m = j
                                  · rw [hmj] at hv
                                    have hvq : v = Value.int q :=
                                      Option.some.inj (hv.symm.trans hy)
                                    subst hvq
                                    rw [hmj, getSlot_threeNarrow_j
                                      (lt_length_of_mem_getSlot doms j _ hyj)
                                      (fun hjk => hmk (hmj.trans hjk))]
                                    exact List.mem_filter.mpr ⟨hyj,
                                      minKeepB_of_satisfying (p := q) (q := p)
                                        (jlo := ilo) (jhi := ihi)
                                        (klo := klo) (khi := khi)
                                        hplo hphi hrlo hrhi
                                        (by simpa [min_comm] using hmin)⟩
                                  · by_cases hmi : m = i
                                    · rw [hmi] at hv
                                      have hvp : v = Value.int p :=
                                        Option.some.inj (hv.symm.trans hx)
                                      subst hvp
                                      rw [hmi, getSlot_threeNarrow_i
                                        (lt_length_of_mem_getSlot doms i _ hxi)
                                        (fun hij => hmj (hmi.trans hij))
                                        (fun hik => hmk (hmi.trans hik))]
                                      exact List.mem_filter.mpr ⟨hxi,
                                        minKeepB_of_satisfying
                                          (jlo := jlo) (jhi := jhi)
                                          (klo := klo) (khi := khi)
                                          hqlo hqhi hrlo hrhi hmin⟩
                                    · rw [getSlot_threeNarrow_other
                                        (fun h => hmi h) (fun h => hmj h)
                                        (fun h => hmk h)]
                                      exact hget m v hv
  · intro doms doms' h
    simp only [propMinSlot] at h
    cases h1 : domMin (getSlot doms i) with
    | none => rw [h1] at h; exact absurd h (by simp)
    | some ilo =>
        simp only [h1] at h
        cases h2 : domMax (getSlot doms i) with
        | none => rw [h2] at h; exact absurd h (by simp)
        | some ihi =>
            simp only [h2] at h
            cases h3 : domMin (getSlot doms j) with
            | none => rw [h3] at h; exact absurd h (by simp)
            | some jlo =>
                simp only [h3] at h
                cases h4 : domMax (getSlot doms j) with
                | none => rw [h4] at h; exact absurd h (by simp)
                | some jhi =>
                    simp only [h4] at h
                    cases h5 : domMin (getSlot doms k) with
                    | none => rw [h5] at h; exact absurd h (by simp)
                    | some klo =>
                        simp only [h5] at h
                        cases h6 : domMax (getSlot doms k) with
                        | none => rw [h6] at h; exact absurd h (by simp)
                        | some khi =>
                            simp only [h6, propMinBounded] at h
                            by_cases hc : ((getSlot doms i).filter
                                (fun p => minKeepB p jlo jhi klo khi)).isEmpty = true ∨
                              ((getSlot doms j).filter
                                (fun q => minKeepB q ilo ihi klo khi)).isEmpty = true ∨
                              (atLeastVals (min ilo jlo)
                                (atMostVals (min ihi jhi) (getSlot doms k))).isEmpty = true
                            · rw [if_pos hc] at h
                              exact absurd h (by simp)
                            · rw [if_neg hc] at h
                              have hd : threeNarrow
                                  ((getSlot doms i).filter
                                    (fun p => minKeepB p jlo jhi klo khi))
                                  ((getSlot doms j).filter
                                    (fun q => minKeepB q ilo ihi klo khi))
                                  (atLeastVals (min ilo jlo)
                                    (atMostVals (min ihi jhi) (getSlot doms k)))
                                  i j k doms = doms' := PropResult.narrowed.inj h
                              subst hd
                              simp only [threeNarrow]
                              exact DomPointwiseSub.setSlot
                                (DomPointwiseSub.setSlot
                                  (DomPointwiseSub.setSlot (DomPointwiseSub.refl doms)
                                    (fun _ hv => (List.mem_filter.mp hv).1))
                                  (fun _ hv => (List.mem_filter.mp hv).1))
                                (fun _ hv => (mem_atLeastVals_atMostVals.mp hv).1)
  · intro doms h a ha hsat
    simp only [propMinSlot] at h
    obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, q, r, hx, hy, hz, hmin⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    have hyj : Value.int q ∈ getSlot doms j := hget j _ hy
    have hzk : Value.int r ∈ getSlot doms k := hget k _ hz
    cases h1 : domMin (getSlot doms i) with
    | none =>
        obtain ⟨m, hm, _⟩ := domMin_of_mem hxi
        rw [h1] at hm
        exact absurd hm (by simp)
    | some ilo =>
        simp only [h1] at h
        cases h2 : domMax (getSlot doms i) with
        | none =>
            obtain ⟨m, hm, _⟩ := domMax_of_mem hxi
            rw [h2] at hm
            exact absurd hm (by simp)
        | some ihi =>
            simp only [h2] at h
            cases h3 : domMin (getSlot doms j) with
            | none =>
                obtain ⟨m, hm, _⟩ := domMin_of_mem hyj
                rw [h3] at hm
                exact absurd hm (by simp)
            | some jlo =>
                simp only [h3] at h
                cases h4 : domMax (getSlot doms j) with
                | none =>
                    obtain ⟨m, hm, _⟩ := domMax_of_mem hyj
                    rw [h4] at hm
                    exact absurd hm (by simp)
                | some jhi =>
                    simp only [h4] at h
                    cases h5 : domMin (getSlot doms k) with
                    | none =>
                        obtain ⟨m, hm, _⟩ := domMin_of_mem hzk
                        rw [h5] at hm
                        exact absurd hm (by simp)
                    | some klo =>
                        simp only [h5] at h
                        cases h6 : domMax (getSlot doms k) with
                        | none =>
                            obtain ⟨m, hm, _⟩ := domMax_of_mem hzk
                            rw [h6] at hm
                            exact absurd hm (by simp)
                        | some khi =>
                            simp only [h6, propMinBounded] at h
                            -- pin the extrema to the satisfying values' bounds
                            obtain ⟨m1, hm1, hplo⟩ := domMin_of_mem hxi
                            rw [h1] at hm1
                            have hilo : m1 = ilo := (Option.some.inj hm1).symm
                            rw [hilo] at hplo
                            obtain ⟨m2, hm2, hphi⟩ := domMax_of_mem hxi
                            rw [h2] at hm2
                            have hihi : m2 = ihi := (Option.some.inj hm2).symm
                            rw [hihi] at hphi
                            obtain ⟨m3, hm3, hqlo⟩ := domMin_of_mem hyj
                            rw [h3] at hm3
                            have hjlo : m3 = jlo := (Option.some.inj hm3).symm
                            rw [hjlo] at hqlo
                            obtain ⟨m4, hm4, hqhi⟩ := domMax_of_mem hyj
                            rw [h4] at hm4
                            have hjhi : m4 = jhi := (Option.some.inj hm4).symm
                            rw [hjhi] at hqhi
                            obtain ⟨m5, hm5, hrlo⟩ := domMin_of_mem hzk
                            rw [h5] at hm5
                            have hklo : m5 = klo := (Option.some.inj hm5).symm
                            rw [hklo] at hrlo
                            obtain ⟨m6, hm6, hrhi⟩ := domMax_of_mem hzk
                            rw [h6] at hm6
                            have hkhi : m6 = khi := (Option.some.inj hm6).symm
                            rw [hkhi] at hrhi
                            have hlo_bounds : min ilo jlo ≤ r := by
                              have h1 : min ilo jlo ≤ p := le_trans (min_le_left ilo jlo) hplo
                              have h2 : min ilo jlo ≤ q := le_trans (min_le_right ilo jlo) hqlo
                              have h3 : min ilo jlo ≤ min p q := le_min_iff.mpr ⟨h1, h2⟩
                              rw [hmin] at h3
                              exact h3
                            have hhi_bounds : r ≤ min ihi jhi := by
                              have h3 : min p q ≤ min ihi jhi := min_le_min hphi hqhi
                              rw [hmin] at h3
                              exact h3
                            by_cases hc : ((getSlot doms i).filter
                                (fun p => minKeepB p jlo jhi klo khi)).isEmpty = true ∨
                              ((getSlot doms j).filter
                                (fun q => minKeepB q ilo ihi klo khi)).isEmpty = true ∨
                              (atLeastVals (min ilo jlo)
                                (atMostVals (min ihi jhi) (getSlot doms k))).isEmpty = true
                            · rw [if_pos hc] at h
                              rcases hc with hci | hcj | hck
                              · have hmem : Value.int p ∈ (getSlot doms i).filter
                                    (fun p => minKeepB p jlo jhi klo khi) :=
                                  List.mem_filter.mpr ⟨hxi,
                                    minKeepB_of_satisfying
                                      (jlo := jlo) (jhi := jhi)
                                      (klo := klo) (khi := khi)
                                      hqlo hqhi hrlo hrhi hmin⟩
                                rw [List.isEmpty_iff.mp hci] at hmem
                                exact absurd hmem (by simp)
                              · have hmem : Value.int q ∈ (getSlot doms j).filter
                                    (fun q => minKeepB q ilo ihi klo khi) :=
                                  List.mem_filter.mpr ⟨hyj,
                                    minKeepB_of_satisfying (p := q) (q := p)
                                      (jlo := ilo) (jhi := ihi)
                                      (klo := klo) (khi := khi)
                                      hplo hphi hrlo hrhi
                                      (by simpa [min_comm] using hmin)⟩
                                rw [List.isEmpty_iff.mp hcj] at hmem
                                exact absurd hmem (by simp)
                              · have hmem : Value.int r ∈ atLeastVals (min ilo jlo)
                                    (atMostVals (min ihi jhi) (getSlot doms k)) :=
                                  mem_atLeastVals_atMostVals.mpr
                                    ⟨hzk, r, rfl, hlo_bounds, hhi_bounds⟩
                                rw [List.isEmpty_iff.mp hck] at hmem
                                exact absurd hmem (by simp)
                            · rw [if_neg hc] at h
                              exact absurd h (by simp)

/-! ### The max propagator -/

/-- The keep test for a `max` operand: an integer value `v = .int p`
    can participate in a satisfying `max p q = r` with `q ∈ [jlo, jhi]`
    and `r ∈ [klo, khi]` only when both necessary interval conditions
    hold (monotonicity of `max` in each argument). Non-integer values
    are rejected. -/
private def maxKeepB (v : Value) (jlo jhi klo khi : Int) : Bool :=
  match v with
  | .int p => decide (max p jlo ≤ khi) && decide (klo ≤ max p jhi)
  | _ => false

private theorem mem_maxKeepB_iff {v : Value} {jlo jhi klo khi : Int} :
    maxKeepB v jlo jhi klo khi = true ↔
      ∃ p, v = .int p ∧ max p jlo ≤ khi ∧ klo ≤ max p jhi := by
  constructor
  · intro h
    cases v with
    | int p =>
      simp only [maxKeepB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨p, rfl, h.1, h.2⟩
    | _ => contradiction
  · rintro ⟨p, rfl, h1, h2⟩
    simp only [maxKeepB, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h1, h2⟩

/-- A satisfying triple keeps both `max` operands. -/
private theorem maxKeepB_of_satisfying {p q r jlo jhi klo khi : Int}
    (hq1 : jlo ≤ q) (hq2 : q ≤ jhi) (hr1 : klo ≤ r) (hr2 : r ≤ khi)
    (hmax : max p q = r) :
    maxKeepB (.int p) jlo jhi klo khi = true := by
  simp only [maxKeepB, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨le_trans (max_le_max (le_refl p) hq1) (hmax ▸ hr2),
    le_trans (hmax ▸ hr1) (max_le_max (le_refl p) hq2)⟩

/-- The bounded max propagation: given all three domains' integer
    extrema, narrow each slot; `contradiction` when any side empties. -/
private def propMaxBounded (ilo ihi jlo jhi klo khi : Int) (i j k : Nat)
    (doms : List (List Value)) : PropResult :=
  let di' := (getSlot doms i).filter (fun p => maxKeepB p jlo jhi klo khi)
  let dj' := (getSlot doms j).filter (fun q => maxKeepB q ilo ihi klo khi)
  let dk' := atLeastVals (max ilo jlo) (atMostVals (max ihi jhi) (getSlot doms k))
  if di'.isEmpty = true ∨ dj'.isEmpty = true ∨ dk'.isEmpty = true then
    .contradiction
  else
    .narrowed (threeNarrow di' dj' dk' i j k doms)

/-- **The max propagator** (`int_max` style on three slots): bounds
    propagation for `max p q = r` — slot `i` keeps exactly the values
    passing the necessary `max` interval conditions, slot `j`
    symmetrically, slot `k` keeps `[max ilo jlo, max ihi jhi]`.
    `contradiction` when any side empties or any domain has no
    integers. -/
def propMaxSlot (i j k : Nat) (doms : List (List Value)) : PropResult :=
  match domMin (getSlot doms i) with
  | none => .contradiction
  | some ilo =>
      match domMax (getSlot doms i) with
      | none => .contradiction
      | some ihi =>
          match domMin (getSlot doms j) with
          | none => .contradiction
          | some jlo =>
              match domMax (getSlot doms j) with
              | none => .contradiction
              | some jhi =>
                  match domMin (getSlot doms k) with
                  | none => .contradiction
                  | some klo =>
                      match domMax (getSlot doms k) with
                      | none => .contradiction
                      | some khi => propMaxBounded ilo ihi jlo jhi klo khi i j k doms

/-- **Preservation for `propMaxSlot`** (PLAN 6.3's local preservation
    theorem, max case): on `narrowed doms'`, every assignment of the
    input domains whose slot values are integers `max p q = r` is still
    an assignment of `doms'`, and `doms'` is pointwise-subset the input
    domains; on `contradiction`, no assignment of the input domains
    solves the equation. -/
theorem propMaxSlot_preserves (i j k : Nat) :
    Preserves (DomConstraint.maxSlot i j k) (propMaxSlot i j k) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propMaxSlot] at h
    obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, q, r, hx, hy, hz, hmax⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    have hyj : Value.int q ∈ getSlot doms j := hget j _ hy
    have hzk : Value.int r ∈ getSlot doms k := hget k _ hz
    cases h1 : domMin (getSlot doms i) with
    | none => rw [h1] at h; exact absurd h (by simp)
    | some ilo =>
        simp only [h1] at h
        cases h2 : domMax (getSlot doms i) with
        | none => rw [h2] at h; exact absurd h (by simp)
        | some ihi =>
            simp only [h2] at h
            cases h3 : domMin (getSlot doms j) with
            | none => rw [h3] at h; exact absurd h (by simp)
            | some jlo =>
                simp only [h3] at h
                cases h4 : domMax (getSlot doms j) with
                | none => rw [h4] at h; exact absurd h (by simp)
                | some jhi =>
                    simp only [h4] at h
                    cases h5 : domMin (getSlot doms k) with
                    | none => rw [h5] at h; exact absurd h (by simp)
                    | some klo =>
                        simp only [h5] at h
                        cases h6 : domMax (getSlot doms k) with
                        | none => rw [h6] at h; exact absurd h (by simp)
                        | some khi =>
                            simp only [h6, propMaxBounded] at h
                            -- pin the extrema to the satisfying values' bounds
                            obtain ⟨m1, hm1, hplo⟩ := domMin_of_mem hxi
                            rw [h1] at hm1
                            have hilo : m1 = ilo := (Option.some.inj hm1).symm
                            rw [hilo] at hplo
                            obtain ⟨m2, hm2, hphi⟩ := domMax_of_mem hxi
                            rw [h2] at hm2
                            have hihi : m2 = ihi := (Option.some.inj hm2).symm
                            rw [hihi] at hphi
                            obtain ⟨m3, hm3, hqlo⟩ := domMin_of_mem hyj
                            rw [h3] at hm3
                            have hjlo : m3 = jlo := (Option.some.inj hm3).symm
                            rw [hjlo] at hqlo
                            obtain ⟨m4, hm4, hqhi⟩ := domMax_of_mem hyj
                            rw [h4] at hm4
                            have hjhi : m4 = jhi := (Option.some.inj hm4).symm
                            rw [hjhi] at hqhi
                            obtain ⟨m5, hm5, hrlo⟩ := domMin_of_mem hzk
                            rw [h5] at hm5
                            have hklo : m5 = klo := (Option.some.inj hm5).symm
                            rw [hklo] at hrlo
                            obtain ⟨m6, hm6, hrhi⟩ := domMax_of_mem hzk
                            rw [h6] at hm6
                            have hkhi : m6 = khi := (Option.some.inj hm6).symm
                            rw [hkhi] at hrhi
                            have hlo_bounds : max ilo jlo ≤ r := by
                              have h1 : ilo ≤ max p q := le_trans hplo (le_max_left p q)
                              have h2 : jlo ≤ max p q := le_trans hqlo (le_max_right p q)
                              have h3 : max ilo jlo ≤ max p q := max_le h1 h2
                              rw [hmax] at h3
                              exact h3
                            have hhi_bounds : r ≤ max ihi jhi := by
                              have h3 : max p q ≤ max ihi jhi := max_le_max hphi hqhi
                              rw [hmax] at h3
                              exact h3
                            by_cases hc : ((getSlot doms i).filter
                                (fun p => maxKeepB p jlo jhi klo khi)).isEmpty = true ∨
                              ((getSlot doms j).filter
                                (fun q => maxKeepB q ilo ihi klo khi)).isEmpty = true ∨
                              (atLeastVals (max ilo jlo)
                                (atMostVals (max ihi jhi) (getSlot doms k))).isEmpty = true
                            · rw [if_pos hc] at h
                              exact absurd h (by simp)
                            · rw [if_neg hc] at h
                              have hd : threeNarrow
                                  ((getSlot doms i).filter
                                    (fun p => maxKeepB p jlo jhi klo khi))
                                  ((getSlot doms j).filter
                                    (fun q => maxKeepB q ilo ihi klo khi))
                                  (atLeastVals (max ilo jlo)
                                    (atMostVals (max ihi jhi) (getSlot doms k)))
                                  i j k doms = doms' := PropResult.narrowed.inj h
                              subst hd
                              apply allAssigns_intro
                              · have hlen2 : (threeNarrow
                                  ((getSlot doms i).filter
                                    (fun p => maxKeepB p jlo jhi klo khi))
                                  ((getSlot doms j).filter
                                    (fun q => maxKeepB q ilo ihi klo khi))
                                  (atLeastVals (max ilo jlo)
                                    (atMostVals (max ihi jhi) (getSlot doms k)))
                                  i j k doms).length = doms.length := by
                                  simp only [threeNarrow, setSlot_length]
                                rw [hlen2]
                                exact hlen
                              · intro m v hv
                                by_cases hmk : m = k
                                · rw [hmk] at hv
                                  have hvr : v = Value.int r :=
                                    Option.some.inj (hv.symm.trans hz)
                                  subst hvr
                                  rw [hmk, getSlot_threeNarrow_k
                                    (lt_length_of_mem_getSlot doms k _ hzk)]
                                  exact mem_atLeastVals_atMostVals.mpr
                                    ⟨hzk, r, rfl, hlo_bounds, hhi_bounds⟩
                                · by_cases hmj : m = j
                                  · rw [hmj] at hv
                                    have hvq : v = Value.int q :=
                                      Option.some.inj (hv.symm.trans hy)
                                    subst hvq
                                    rw [hmj, getSlot_threeNarrow_j
                                      (lt_length_of_mem_getSlot doms j _ hyj)
                                      (fun hjk => hmk (hmj.trans hjk))]
                                    exact List.mem_filter.mpr ⟨hyj,
                                      maxKeepB_of_satisfying (p := q) (q := p)
                                        (jlo := ilo) (jhi := ihi)
                                        (klo := klo) (khi := khi)
                                        hplo hphi hrlo hrhi
                                        (by simpa [max_comm] using hmax)⟩
                                  · by_cases hmi : m = i
                                    · rw [hmi] at hv
                                      have hvp : v = Value.int p :=
                                        Option.some.inj (hv.symm.trans hx)
                                      subst hvp
                                      rw [hmi, getSlot_threeNarrow_i
                                        (lt_length_of_mem_getSlot doms i _ hxi)
                                        (fun hij => hmj (hmi.trans hij))
                                        (fun hik => hmk (hmi.trans hik))]
                                      exact List.mem_filter.mpr ⟨hxi,
                                        maxKeepB_of_satisfying
                                          (jlo := jlo) (jhi := jhi)
                                          (klo := klo) (khi := khi)
                                          hqlo hqhi hrlo hrhi hmax⟩
                                    · rw [getSlot_threeNarrow_other
                                        (fun h => hmi h) (fun h => hmj h)
                                        (fun h => hmk h)]
                                      exact hget m v hv
  · intro doms doms' h
    simp only [propMaxSlot] at h
    cases h1 : domMin (getSlot doms i) with
    | none => rw [h1] at h; exact absurd h (by simp)
    | some ilo =>
        simp only [h1] at h
        cases h2 : domMax (getSlot doms i) with
        | none => rw [h2] at h; exact absurd h (by simp)
        | some ihi =>
            simp only [h2] at h
            cases h3 : domMin (getSlot doms j) with
            | none => rw [h3] at h; exact absurd h (by simp)
            | some jlo =>
                simp only [h3] at h
                cases h4 : domMax (getSlot doms j) with
                | none => rw [h4] at h; exact absurd h (by simp)
                | some jhi =>
                    simp only [h4] at h
                    cases h5 : domMin (getSlot doms k) with
                    | none => rw [h5] at h; exact absurd h (by simp)
                    | some klo =>
                        simp only [h5] at h
                        cases h6 : domMax (getSlot doms k) with
                        | none => rw [h6] at h; exact absurd h (by simp)
                        | some khi =>
                            simp only [h6, propMaxBounded] at h
                            by_cases hc : ((getSlot doms i).filter
                                (fun p => maxKeepB p jlo jhi klo khi)).isEmpty = true ∨
                              ((getSlot doms j).filter
                                (fun q => maxKeepB q ilo ihi klo khi)).isEmpty = true ∨
                              (atLeastVals (max ilo jlo)
                                (atMostVals (max ihi jhi) (getSlot doms k))).isEmpty = true
                            · rw [if_pos hc] at h
                              exact absurd h (by simp)
                            · rw [if_neg hc] at h
                              have hd : threeNarrow
                                  ((getSlot doms i).filter
                                    (fun p => maxKeepB p jlo jhi klo khi))
                                  ((getSlot doms j).filter
                                    (fun q => maxKeepB q ilo ihi klo khi))
                                  (atLeastVals (max ilo jlo)
                                    (atMostVals (max ihi jhi) (getSlot doms k)))
                                  i j k doms = doms' := PropResult.narrowed.inj h
                              subst hd
                              simp only [threeNarrow]
                              exact DomPointwiseSub.setSlot
                                (DomPointwiseSub.setSlot
                                  (DomPointwiseSub.setSlot (DomPointwiseSub.refl doms)
                                    (fun _ hv => (List.mem_filter.mp hv).1))
                                  (fun _ hv => (List.mem_filter.mp hv).1))
                                (fun _ hv => (mem_atLeastVals_atMostVals.mp hv).1)
  · intro doms h a ha hsat
    simp only [propMaxSlot] at h
    obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, q, r, hx, hy, hz, hmax⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    have hyj : Value.int q ∈ getSlot doms j := hget j _ hy
    have hzk : Value.int r ∈ getSlot doms k := hget k _ hz
    cases h1 : domMin (getSlot doms i) with
    | none =>
        obtain ⟨m, hm, _⟩ := domMin_of_mem hxi
        rw [h1] at hm
        exact absurd hm (by simp)
    | some ilo =>
        simp only [h1] at h
        cases h2 : domMax (getSlot doms i) with
        | none =>
            obtain ⟨m, hm, _⟩ := domMax_of_mem hxi
            rw [h2] at hm
            exact absurd hm (by simp)
        | some ihi =>
            simp only [h2] at h
            cases h3 : domMin (getSlot doms j) with
            | none =>
                obtain ⟨m, hm, _⟩ := domMin_of_mem hyj
                rw [h3] at hm
                exact absurd hm (by simp)
            | some jlo =>
                simp only [h3] at h
                cases h4 : domMax (getSlot doms j) with
                | none =>
                    obtain ⟨m, hm, _⟩ := domMax_of_mem hyj
                    rw [h4] at hm
                    exact absurd hm (by simp)
                | some jhi =>
                    simp only [h4] at h
                    cases h5 : domMin (getSlot doms k) with
                    | none =>
                        obtain ⟨m, hm, _⟩ := domMin_of_mem hzk
                        rw [h5] at hm
                        exact absurd hm (by simp)
                    | some klo =>
                        simp only [h5] at h
                        cases h6 : domMax (getSlot doms k) with
                        | none =>
                            obtain ⟨m, hm, _⟩ := domMax_of_mem hzk
                            rw [h6] at hm
                            exact absurd hm (by simp)
                        | some khi =>
                            simp only [h6, propMaxBounded] at h
                            -- pin the extrema to the satisfying values' bounds
                            obtain ⟨m1, hm1, hplo⟩ := domMin_of_mem hxi
                            rw [h1] at hm1
                            have hilo : m1 = ilo := (Option.some.inj hm1).symm
                            rw [hilo] at hplo
                            obtain ⟨m2, hm2, hphi⟩ := domMax_of_mem hxi
                            rw [h2] at hm2
                            have hihi : m2 = ihi := (Option.some.inj hm2).symm
                            rw [hihi] at hphi
                            obtain ⟨m3, hm3, hqlo⟩ := domMin_of_mem hyj
                            rw [h3] at hm3
                            have hjlo : m3 = jlo := (Option.some.inj hm3).symm
                            rw [hjlo] at hqlo
                            obtain ⟨m4, hm4, hqhi⟩ := domMax_of_mem hyj
                            rw [h4] at hm4
                            have hjhi : m4 = jhi := (Option.some.inj hm4).symm
                            rw [hjhi] at hqhi
                            obtain ⟨m5, hm5, hrlo⟩ := domMin_of_mem hzk
                            rw [h5] at hm5
                            have hklo : m5 = klo := (Option.some.inj hm5).symm
                            rw [hklo] at hrlo
                            obtain ⟨m6, hm6, hrhi⟩ := domMax_of_mem hzk
                            rw [h6] at hm6
                            have hkhi : m6 = khi := (Option.some.inj hm6).symm
                            rw [hkhi] at hrhi
                            have hlo_bounds : max ilo jlo ≤ r := by
                              have h1 : ilo ≤ max p q := le_trans hplo (le_max_left p q)
                              have h2 : jlo ≤ max p q := le_trans hqlo (le_max_right p q)
                              have h3 : max ilo jlo ≤ max p q := max_le h1 h2
                              rw [hmax] at h3
                              exact h3
                            have hhi_bounds : r ≤ max ihi jhi := by
                              have h3 : max p q ≤ max ihi jhi := max_le_max hphi hqhi
                              rw [hmax] at h3
                              exact h3
                            by_cases hc : ((getSlot doms i).filter
                                (fun p => maxKeepB p jlo jhi klo khi)).isEmpty = true ∨
                              ((getSlot doms j).filter
                                (fun q => maxKeepB q ilo ihi klo khi)).isEmpty = true ∨
                              (atLeastVals (max ilo jlo)
                                (atMostVals (max ihi jhi) (getSlot doms k))).isEmpty = true
                            · rw [if_pos hc] at h
                              rcases hc with hci | hcj | hck
                              · have hmem : Value.int p ∈ (getSlot doms i).filter
                                    (fun p => maxKeepB p jlo jhi klo khi) :=
                                  List.mem_filter.mpr ⟨hxi,
                                    maxKeepB_of_satisfying
                                      (jlo := jlo) (jhi := jhi)
                                      (klo := klo) (khi := khi)
                                      hqlo hqhi hrlo hrhi hmax⟩
                                rw [List.isEmpty_iff.mp hci] at hmem
                                exact absurd hmem (by simp)
                              · have hmem : Value.int q ∈ (getSlot doms j).filter
                                    (fun q => maxKeepB q ilo ihi klo khi) :=
                                  List.mem_filter.mpr ⟨hyj,
                                    maxKeepB_of_satisfying (p := q) (q := p)
                                      (jlo := ilo) (jhi := ihi)
                                      (klo := klo) (khi := khi)
                                      hplo hphi hrlo hrhi
                                      (by simpa [max_comm] using hmax)⟩
                                rw [List.isEmpty_iff.mp hcj] at hmem
                                exact absurd hmem (by simp)
                              · have hmem : Value.int r ∈ atLeastVals (max ilo jlo)
                                    (atMostVals (max ihi jhi) (getSlot doms k)) :=
                                  mem_atLeastVals_atMostVals.mpr
                                    ⟨hzk, r, rfl, hlo_bounds, hhi_bounds⟩
                                rw [List.isEmpty_iff.mp hck] at hmem
                                exact absurd hmem (by simp)
                            · rw [if_neg hc] at h
                              exact absurd h (by simp)

/-! ### The times propagator -/

/-- The keep test for a `times` operand: an integer value `v = .int p`
    can participate in a satisfying `p * q = r` with `q ∈ [jlo, jhi]`
    and `r ∈ [klo, khi]` only when the necessary interval condition
    (the product `p * q` stays within the two corner products) holds.
    Non-integer values are rejected. -/
private def timesKeepB (v : Value) (jlo jhi klo khi : Int) : Bool :=
  match v with
  | .int p =>
    decide (min (p * jlo) (p * jhi) ≤ khi) &&
      decide (klo ≤ max (p * jlo) (p * jhi))
  | _ => false

private theorem mem_timesKeepB_iff {v : Value} {jlo jhi klo khi : Int} :
    timesKeepB v jlo jhi klo khi = true ↔
      ∃ p, v = .int p ∧ min (p * jlo) (p * jhi) ≤ khi ∧
        klo ≤ max (p * jlo) (p * jhi) := by
  constructor
  · intro h
    cases v with
    | int p =>
      simp only [timesKeepB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨p, rfl, h.1, h.2⟩
    | _ => contradiction
  · rintro ⟨p, rfl, h1, h2⟩
    simp only [timesKeepB, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h1, h2⟩

/-- A satisfying triple keeps both `times` operands. -/
private theorem timesKeepB_of_satisfying {p q r jlo jhi klo khi : Int}
    (hq1 : jlo ≤ q) (hq2 : q ≤ jhi) (hr1 : klo ≤ r) (hr2 : r ≤ khi)
    (hprod : p * q = r) :
    timesKeepB (.int p) jlo jhi klo khi = true := by
  simp only [timesKeepB, Bool.and_eq_true, decide_eq_true_eq]
  obtain ⟨hlo_pq, hhi_pq⟩ := mul_one_interval hq1 hq2
  exact ⟨le_trans hlo_pq (hprod ▸ hr2),
    le_trans hr1 (hprod ▸ hhi_pq)⟩

/-- The bounded times propagation: given all three domains' integer
    extrema, narrow each slot; `contradiction` when any side empties. -/
private def propTimesBounded (ilo ihi jlo jhi klo khi : Int) (i j k : Nat)
    (doms : List (List Value)) : PropResult :=
  let di' := (getSlot doms i).filter (fun p => timesKeepB p jlo jhi klo khi)
  let dj' := (getSlot doms j).filter (fun q => timesKeepB q ilo ihi klo khi)
  let dk' := atLeastVals (cornerMin ilo ihi jlo jhi)
    (atMostVals (cornerMax ilo ihi jlo jhi) (getSlot doms k))
  if di'.isEmpty = true ∨ dj'.isEmpty = true ∨ dk'.isEmpty = true then
    .contradiction
  else
    .narrowed (threeNarrow di' dj' dk' i j k doms)

/-- **The times propagator** (`int_times` style on three slots): bounds
    propagation for `p * q = r` — slot `i` keeps exactly the values
    passing the necessary product interval condition, slot `j`
    symmetrically, slot `k` keeps the four-corner product interval
    `[cornerMin ilo ihi jlo jhi, cornerMax ilo ihi jlo jhi]`.
    `contradiction` when any side empties or any domain has no
    integers. -/
def propTimesSlot (i j k : Nat) (doms : List (List Value)) : PropResult :=
  match domMin (getSlot doms i) with
  | none => .contradiction
  | some ilo =>
      match domMax (getSlot doms i) with
      | none => .contradiction
      | some ihi =>
          match domMin (getSlot doms j) with
          | none => .contradiction
          | some jlo =>
              match domMax (getSlot doms j) with
              | none => .contradiction
              | some jhi =>
                  match domMin (getSlot doms k) with
                  | none => .contradiction
                  | some klo =>
                      match domMax (getSlot doms k) with
                      | none => .contradiction
                      | some khi => propTimesBounded ilo ihi jlo jhi klo khi i j k doms

/-- **Preservation for `propTimesSlot`** (PLAN 6.3's local preservation
    theorem, times case): on `narrowed doms'`, every assignment of the
    input domains whose slot values are integers `p * q = r` is still
    an assignment of `doms'`, and `doms'` is pointwise-subset the input
    domains; on `contradiction`, no assignment of the input domains
    solves the equation. -/
theorem propTimesSlot_preserves (i j k : Nat) :
    Preserves (DomConstraint.timesSlot i j k) (propTimesSlot i j k) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propTimesSlot] at h
    obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, q, r, hx, hy, hz, hprod⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    have hyj : Value.int q ∈ getSlot doms j := hget j _ hy
    have hzk : Value.int r ∈ getSlot doms k := hget k _ hz
    cases h1 : domMin (getSlot doms i) with
    | none => rw [h1] at h; exact absurd h (by simp)
    | some ilo =>
        simp only [h1] at h
        cases h2 : domMax (getSlot doms i) with
        | none => rw [h2] at h; exact absurd h (by simp)
        | some ihi =>
            simp only [h2] at h
            cases h3 : domMin (getSlot doms j) with
            | none => rw [h3] at h; exact absurd h (by simp)
            | some jlo =>
                simp only [h3] at h
                cases h4 : domMax (getSlot doms j) with
                | none => rw [h4] at h; exact absurd h (by simp)
                | some jhi =>
                    simp only [h4] at h
                    cases h5 : domMin (getSlot doms k) with
                    | none => rw [h5] at h; exact absurd h (by simp)
                    | some klo =>
                        simp only [h5] at h
                        cases h6 : domMax (getSlot doms k) with
                        | none => rw [h6] at h; exact absurd h (by simp)
                        | some khi =>
                            simp only [h6, propTimesBounded] at h
                            -- pin the extrema to the satisfying values' bounds
                            obtain ⟨m1, hm1, hplo⟩ := domMin_of_mem hxi
                            rw [h1] at hm1
                            have hilo : m1 = ilo := (Option.some.inj hm1).symm
                            rw [hilo] at hplo
                            obtain ⟨m2, hm2, hphi⟩ := domMax_of_mem hxi
                            rw [h2] at hm2
                            have hihi : m2 = ihi := (Option.some.inj hm2).symm
                            rw [hihi] at hphi
                            obtain ⟨m3, hm3, hqlo⟩ := domMin_of_mem hyj
                            rw [h3] at hm3
                            have hjlo : m3 = jlo := (Option.some.inj hm3).symm
                            rw [hjlo] at hqlo
                            obtain ⟨m4, hm4, hqhi⟩ := domMax_of_mem hyj
                            rw [h4] at hm4
                            have hjhi : m4 = jhi := (Option.some.inj hm4).symm
                            rw [hjhi] at hqhi
                            obtain ⟨m5, hm5, hrlo⟩ := domMin_of_mem hzk
                            rw [h5] at hm5
                            have hklo : m5 = klo := (Option.some.inj hm5).symm
                            rw [hklo] at hrlo
                            obtain ⟨m6, hm6, hrhi⟩ := domMax_of_mem hzk
                            rw [h6] at hm6
                            have hkhi : m6 = khi := (Option.some.inj hm6).symm
                            rw [hkhi] at hrhi
                            by_cases hc : ((getSlot doms i).filter
                                (fun p => timesKeepB p jlo jhi klo khi)).isEmpty = true ∨
                              ((getSlot doms j).filter
                                (fun q => timesKeepB q ilo ihi klo khi)).isEmpty = true ∨
                              (atLeastVals (cornerMin ilo ihi jlo jhi)
                                (atMostVals (cornerMax ilo ihi jlo jhi)
                                  (getSlot doms k))).isEmpty = true
                            · rw [if_pos hc] at h
                              exact absurd h (by simp)
                            · rw [if_neg hc] at h
                              have hd : threeNarrow
                                  ((getSlot doms i).filter
                                    (fun p => timesKeepB p jlo jhi klo khi))
                                  ((getSlot doms j).filter
                                    (fun q => timesKeepB q ilo ihi klo khi))
                                  (atLeastVals (cornerMin ilo ihi jlo jhi)
                                    (atMostVals (cornerMax ilo ihi jlo jhi)
                                      (getSlot doms k)))
                                  i j k doms = doms' := PropResult.narrowed.inj h
                              subst hd
                              apply allAssigns_intro
                              · have hlen2 : (threeNarrow
                                  ((getSlot doms i).filter
                                    (fun p => timesKeepB p jlo jhi klo khi))
                                  ((getSlot doms j).filter
                                    (fun q => timesKeepB q ilo ihi klo khi))
                                  (atLeastVals (cornerMin ilo ihi jlo jhi)
                                    (atMostVals (cornerMax ilo ihi jlo jhi)
                                      (getSlot doms k)))
                                  i j k doms).length = doms.length := by
                                  simp only [threeNarrow, setSlot_length]
                                rw [hlen2]
                                exact hlen
                              · intro m v hv
                                by_cases hmk : m = k
                                · rw [hmk] at hv
                                  have hvr : v = Value.int r :=
                                    Option.some.inj (hv.symm.trans hz)
                                  subst hvr
                                  rw [hmk, getSlot_threeNarrow_k
                                    (lt_length_of_mem_getSlot doms k _ hzk)]
                                  exact mem_atLeastVals_atMostVals.mpr
                                    ⟨hzk, r, rfl,
                                      (by simpa [← hprod] using
                                        cornerMin_le_mul hplo hphi hqlo hqhi),
                                      (by simpa [← hprod] using
                                        mul_le_cornerMax hplo hphi hqlo hqhi)⟩
                                · by_cases hmj : m = j
                                  · rw [hmj] at hv
                                    have hvq : v = Value.int q :=
                                      Option.some.inj (hv.symm.trans hy)
                                    subst hvq
                                    rw [hmj, getSlot_threeNarrow_j
                                      (lt_length_of_mem_getSlot doms j _ hyj)
                                      (fun hjk => hmk (hmj.trans hjk))]
                                    exact List.mem_filter.mpr ⟨hyj,
                                      timesKeepB_of_satisfying (p := q) (q := p)
                                        (jlo := ilo) (jhi := ihi)
                                        (klo := klo) (khi := khi)
                                        hplo hphi hrlo hrhi
                                        (by simpa [mul_comm] using hprod)⟩
                                  · by_cases hmi : m = i
                                    · rw [hmi] at hv
                                      have hvp : v = Value.int p :=
                                        Option.some.inj (hv.symm.trans hx)
                                      subst hvp
                                      rw [hmi, getSlot_threeNarrow_i
                                        (lt_length_of_mem_getSlot doms i _ hxi)
                                        (fun hij => hmj (hmi.trans hij))
                                        (fun hik => hmk (hmi.trans hik))]
                                      exact List.mem_filter.mpr ⟨hxi,
                                        timesKeepB_of_satisfying
                                          (jlo := jlo) (jhi := jhi)
                                          (klo := klo) (khi := khi)
                                          hqlo hqhi hrlo hrhi hprod⟩
                                    · rw [getSlot_threeNarrow_other
                                        (fun h => hmi h) (fun h => hmj h)
                                        (fun h => hmk h)]
                                      exact hget m v hv
  · intro doms doms' h
    simp only [propTimesSlot] at h
    cases h1 : domMin (getSlot doms i) with
    | none => rw [h1] at h; exact absurd h (by simp)
    | some ilo =>
        simp only [h1] at h
        cases h2 : domMax (getSlot doms i) with
        | none => rw [h2] at h; exact absurd h (by simp)
        | some ihi =>
            simp only [h2] at h
            cases h3 : domMin (getSlot doms j) with
            | none => rw [h3] at h; exact absurd h (by simp)
            | some jlo =>
                simp only [h3] at h
                cases h4 : domMax (getSlot doms j) with
                | none => rw [h4] at h; exact absurd h (by simp)
                | some jhi =>
                    simp only [h4] at h
                    cases h5 : domMin (getSlot doms k) with
                    | none => rw [h5] at h; exact absurd h (by simp)
                    | some klo =>
                        simp only [h5] at h
                        cases h6 : domMax (getSlot doms k) with
                        | none => rw [h6] at h; exact absurd h (by simp)
                        | some khi =>
                            simp only [h6, propTimesBounded] at h
                            by_cases hc : ((getSlot doms i).filter
                                (fun p => timesKeepB p jlo jhi klo khi)).isEmpty = true ∨
                              ((getSlot doms j).filter
                                (fun q => timesKeepB q ilo ihi klo khi)).isEmpty = true ∨
                              (atLeastVals (cornerMin ilo ihi jlo jhi)
                                (atMostVals (cornerMax ilo ihi jlo jhi)
                                  (getSlot doms k))).isEmpty = true
                            · rw [if_pos hc] at h
                              exact absurd h (by simp)
                            · rw [if_neg hc] at h
                              have hd : threeNarrow
                                  ((getSlot doms i).filter
                                    (fun p => timesKeepB p jlo jhi klo khi))
                                  ((getSlot doms j).filter
                                    (fun q => timesKeepB q ilo ihi klo khi))
                                  (atLeastVals (cornerMin ilo ihi jlo jhi)
                                    (atMostVals (cornerMax ilo ihi jlo jhi)
                                      (getSlot doms k)))
                                  i j k doms = doms' := PropResult.narrowed.inj h
                              subst hd
                              simp only [threeNarrow]
                              exact DomPointwiseSub.setSlot
                                (DomPointwiseSub.setSlot
                                  (DomPointwiseSub.setSlot (DomPointwiseSub.refl doms)
                                    (fun _ hv => (List.mem_filter.mp hv).1))
                                  (fun _ hv => (List.mem_filter.mp hv).1))
                                (fun _ hv => (mem_atLeastVals_atMostVals.mp hv).1)
  · intro doms h a ha hsat
    simp only [propTimesSlot] at h
    obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, q, r, hx, hy, hz, hprod⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    have hyj : Value.int q ∈ getSlot doms j := hget j _ hy
    have hzk : Value.int r ∈ getSlot doms k := hget k _ hz
    cases h1 : domMin (getSlot doms i) with
    | none =>
        obtain ⟨m, hm, _⟩ := domMin_of_mem hxi
        rw [h1] at hm
        exact absurd hm (by simp)
    | some ilo =>
        simp only [h1] at h
        cases h2 : domMax (getSlot doms i) with
        | none =>
            obtain ⟨m, hm, _⟩ := domMax_of_mem hxi
            rw [h2] at hm
            exact absurd hm (by simp)
        | some ihi =>
            simp only [h2] at h
            cases h3 : domMin (getSlot doms j) with
            | none =>
                obtain ⟨m, hm, _⟩ := domMin_of_mem hyj
                rw [h3] at hm
                exact absurd hm (by simp)
            | some jlo =>
                simp only [h3] at h
                cases h4 : domMax (getSlot doms j) with
                | none =>
                    obtain ⟨m, hm, _⟩ := domMax_of_mem hyj
                    rw [h4] at hm
                    exact absurd hm (by simp)
                | some jhi =>
                    simp only [h4] at h
                    cases h5 : domMin (getSlot doms k) with
                    | none =>
                        obtain ⟨m, hm, _⟩ := domMin_of_mem hzk
                        rw [h5] at hm
                        exact absurd hm (by simp)
                    | some klo =>
                        simp only [h5] at h
                        cases h6 : domMax (getSlot doms k) with
                        | none =>
                            obtain ⟨m, hm, _⟩ := domMax_of_mem hzk
                            rw [h6] at hm
                            exact absurd hm (by simp)
                        | some khi =>
                            simp only [h6, propTimesBounded] at h
                            -- pin the extrema to the satisfying values' bounds
                            obtain ⟨m1, hm1, hplo⟩ := domMin_of_mem hxi
                            rw [h1] at hm1
                            have hilo : m1 = ilo := (Option.some.inj hm1).symm
                            rw [hilo] at hplo
                            obtain ⟨m2, hm2, hphi⟩ := domMax_of_mem hxi
                            rw [h2] at hm2
                            have hihi : m2 = ihi := (Option.some.inj hm2).symm
                            rw [hihi] at hphi
                            obtain ⟨m3, hm3, hqlo⟩ := domMin_of_mem hyj
                            rw [h3] at hm3
                            have hjlo : m3 = jlo := (Option.some.inj hm3).symm
                            rw [hjlo] at hqlo
                            obtain ⟨m4, hm4, hqhi⟩ := domMax_of_mem hyj
                            rw [h4] at hm4
                            have hjhi : m4 = jhi := (Option.some.inj hm4).symm
                            rw [hjhi] at hqhi
                            obtain ⟨m5, hm5, hrlo⟩ := domMin_of_mem hzk
                            rw [h5] at hm5
                            have hklo : m5 = klo := (Option.some.inj hm5).symm
                            rw [hklo] at hrlo
                            obtain ⟨m6, hm6, hrhi⟩ := domMax_of_mem hzk
                            rw [h6] at hm6
                            have hkhi : m6 = khi := (Option.some.inj hm6).symm
                            rw [hkhi] at hrhi
                            by_cases hc : ((getSlot doms i).filter
                                (fun p => timesKeepB p jlo jhi klo khi)).isEmpty = true ∨
                              ((getSlot doms j).filter
                                (fun q => timesKeepB q ilo ihi klo khi)).isEmpty = true ∨
                              (atLeastVals (cornerMin ilo ihi jlo jhi)
                                (atMostVals (cornerMax ilo ihi jlo jhi)
                                  (getSlot doms k))).isEmpty = true
                            · rw [if_pos hc] at h
                              rcases hc with hci | hcj | hck
                              · have hmem : Value.int p ∈ (getSlot doms i).filter
                                    (fun p => timesKeepB p jlo jhi klo khi) :=
                                  List.mem_filter.mpr ⟨hxi,
                                    timesKeepB_of_satisfying
                                      (jlo := jlo) (jhi := jhi)
                                      (klo := klo) (khi := khi)
                                      hqlo hqhi hrlo hrhi hprod⟩
                                rw [List.isEmpty_iff.mp hci] at hmem
                                exact absurd hmem (by simp)
                              · have hmem : Value.int q ∈ (getSlot doms j).filter
                                    (fun q => timesKeepB q ilo ihi klo khi) :=
                                  List.mem_filter.mpr ⟨hyj,
                                    timesKeepB_of_satisfying (p := q) (q := p)
                                      (jlo := ilo) (jhi := ihi)
                                      (klo := klo) (khi := khi)
                                      hplo hphi hrlo hrhi
                                      (by simpa [mul_comm] using hprod)⟩
                                rw [List.isEmpty_iff.mp hcj] at hmem
                                exact absurd hmem (by simp)
                              · have hmem : Value.int r ∈
                                    atLeastVals (cornerMin ilo ihi jlo jhi)
                                      (atMostVals (cornerMax ilo ihi jlo jhi)
                                        (getSlot doms k)) :=
                                  mem_atLeastVals_atMostVals.mpr
                                    ⟨hzk, r, rfl,
                                      (by simpa [← hprod] using
                                        cornerMin_le_mul hplo hphi hqlo hqhi),
                                      (by simpa [← hprod] using
                                        mul_le_cornerMax hplo hphi hqlo hqhi)⟩
                                rw [List.isEmpty_iff.mp hck] at hmem
                                exact absurd hmem (by simp)
                            · rw [if_neg hc] at h
                              exact absurd h (by simp)

/-! ### The abs propagator -/

/-- The two-slot narrowing: each slot takes its narrowed list, each
    filter computed once (on the *input* domains — every bound argument
    holds for any satisfying assignment independently, so coinciding
    slot positions are harmless). -/
private def twoNarrow (di' dk' : List Value) (i k : Nat)
    (doms : List (List Value)) : List (List Value) :=
  setSlot (setSlot doms i di') k dk'

/-- Reading back the two written slots of a `twoNarrow` (the `k`-write
    is outermost, then `i`). -/
private theorem getSlot_twoNarrow_k {di' dk' : List Value} {i k : Nat}
    {doms : List (List Value)} (hk : k < doms.length) :
    getSlot (twoNarrow di' dk' i k doms) k = dk' := by
  simp only [twoNarrow]
  rw [getSlot_setSlot_eq (setSlot doms i di') dk' k
    (by rw [setSlot_length]; exact hk)]

private theorem getSlot_twoNarrow_i {di' dk' : List Value} {i k : Nat}
    {doms : List (List Value)} (hi : i < doms.length) (hik : i ≠ k) :
    getSlot (twoNarrow di' dk' i k doms) i = di' := by
  simp only [twoNarrow]
  rw [getSlot_setSlot_of_ne (setSlot doms i di') dk' k i hik,
    getSlot_setSlot_eq doms di' i hi]

private theorem getSlot_twoNarrow_other {di' dk' : List Value} {i k m : Nat}
    {doms : List (List Value)} (hmi : m ≠ i) (hmk : m ≠ k) :
    getSlot (twoNarrow di' dk' i k doms) m = getSlot doms m := by
  simp only [twoNarrow]
  rw [getSlot_setSlot_of_ne (setSlot doms i di') dk' k m hmk,
    getSlot_setSlot_of_ne doms di' i m hmi]

/-- The keep test for the `abs` operand: an integer value `v = .int p`
    participates in a satisfying `absValue p = r` with `r ∈ [klo, khi]`
    exactly when `klo ≤ absValue p ≤ khi`. Non-integer values are
    rejected. -/
private def absKeepB (v : Value) (klo khi : Int) : Bool :=
  match v with
  | .int p => decide (klo ≤ absValue p) && decide (absValue p ≤ khi)
  | _ => false

private theorem mem_absKeepB_iff {v : Value} {klo khi : Int} :
    absKeepB v klo khi = true ↔
      ∃ p, v = .int p ∧ klo ≤ absValue p ∧ absValue p ≤ khi := by
  constructor
  · intro h
    cases v with
    | int p =>
      simp only [absKeepB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨p, rfl, h.1, h.2⟩
    | _ => contradiction
  · rintro ⟨p, rfl, h1, h2⟩
    simp only [absKeepB, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h1, h2⟩

/-- A satisfying pair keeps the `abs` operand. -/
private theorem absKeepB_of_satisfying {p r klo khi : Int}
    (hr1 : klo ≤ r) (hr2 : r ≤ khi) (habs : absValue p = r) :
    absKeepB (.int p) klo khi = true := by
  simp only [absKeepB, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨habs ▸ hr1, habs ▸ hr2⟩

/-- The bounded abs propagation: given both domains' integer extrema,
    narrow each slot; `contradiction` when any side empties. -/
private def propAbsBounded (ilo ihi klo khi : Int) (i k : Nat)
    (doms : List (List Value)) : PropResult :=
  let M := max (absValue ilo) (absValue ihi)
  let di' := (getSlot doms i).filter (fun p => absKeepB p klo khi)
  let dk' := atLeastVals 0 (atMostVals M (getSlot doms k))
  if di'.isEmpty = true ∨ dk'.isEmpty = true then
    .contradiction
  else
    .narrowed (twoNarrow di' dk' i k doms)

/-- **The abs propagator** (`int_abs` style on two slots): bounds
    propagation for `absValue p = r` — slot `i` keeps exactly the
    values with `klo ≤ absValue p ≤ khi`, slot `k` keeps the nonneg
    interval `[0, max (absValue ilo) (absValue ihi)]`.
    `contradiction` when any side empties or any domain has no
    integers. -/
def propAbsSlot (i k : Nat) (doms : List (List Value)) : PropResult :=
  match domMin (getSlot doms i) with
  | none => .contradiction
  | some ilo =>
      match domMax (getSlot doms i) with
      | none => .contradiction
      | some ihi =>
          match domMin (getSlot doms k) with
          | none => .contradiction
          | some klo =>
              match domMax (getSlot doms k) with
              | none => .contradiction
              | some khi => propAbsBounded ilo ihi klo khi i k doms

/-- **Preservation for `propAbsSlot`** (PLAN 6.3's local preservation
    theorem, abs case): on `narrowed doms'`, every assignment of the
    input domains whose slot values are integers `absValue p = r` is
    still an assignment of `doms'`, and `doms'` is pointwise-subset the
    input domains; on `contradiction`, no assignment of the input
    domains solves the equation. -/
theorem propAbsSlot_preserves (i k : Nat) :
    Preserves (DomConstraint.absSlot i k) (propAbsSlot i k) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propAbsSlot] at h
    obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, r, hx, hz, habs⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    have hzk : Value.int r ∈ getSlot doms k := hget k _ hz
    cases h1 : domMin (getSlot doms i) with
    | none => rw [h1] at h; exact absurd h (by simp)
    | some ilo =>
        simp only [h1] at h
        cases h2 : domMax (getSlot doms i) with
        | none => rw [h2] at h; exact absurd h (by simp)
        | some ihi =>
            simp only [h2] at h
            cases h3 : domMin (getSlot doms k) with
            | none => rw [h3] at h; exact absurd h (by simp)
            | some klo =>
                simp only [h3] at h
                cases h4 : domMax (getSlot doms k) with
                | none => rw [h4] at h; exact absurd h (by simp)
                | some khi =>
                    simp only [h4, propAbsBounded] at h
                    -- pin the extrema to the satisfying values' bounds
                    obtain ⟨m1, hm1, hplo⟩ := domMin_of_mem hxi
                    rw [h1] at hm1
                    have hilo : m1 = ilo := (Option.some.inj hm1).symm
                    rw [hilo] at hplo
                    obtain ⟨m2, hm2, hphi⟩ := domMax_of_mem hxi
                    rw [h2] at hm2
                    have hihi : m2 = ihi := (Option.some.inj hm2).symm
                    rw [hihi] at hphi
                    obtain ⟨m3, hm3, hrlo⟩ := domMin_of_mem hzk
                    rw [h3] at hm3
                    have hklo : m3 = klo := (Option.some.inj hm3).symm
                    rw [hklo] at hrlo
                    obtain ⟨m4, hm4, hrhi⟩ := domMax_of_mem hzk
                    rw [h4] at hm4
                    have hkhi : m4 = khi := (Option.some.inj hm4).symm
                    rw [hkhi] at hrhi
                    by_cases hc : ((getSlot doms i).filter
                        (fun p => absKeepB p klo khi)).isEmpty = true ∨
                      (atLeastVals 0 (atMostVals (max (absValue ilo) (absValue ihi))
                        (getSlot doms k))).isEmpty = true
                    · rw [if_pos hc] at h
                      exact absurd h (by simp)
                    · rw [if_neg hc] at h
                      have hd : twoNarrow
                          ((getSlot doms i).filter (fun p => absKeepB p klo khi))
                          (atLeastVals 0 (atMostVals (max (absValue ilo) (absValue ihi))
                            (getSlot doms k)))
                          i k doms = doms' := PropResult.narrowed.inj h
                      subst hd
                      apply allAssigns_intro
                      · have hlen2 : (twoNarrow
                          ((getSlot doms i).filter (fun p => absKeepB p klo khi))
                          (atLeastVals 0 (atMostVals (max (absValue ilo) (absValue ihi))
                            (getSlot doms k)))
                          i k doms).length = doms.length := by
                          simp only [twoNarrow, setSlot_length]
                        rw [hlen2]
                        exact hlen
                      · intro m v hv
                        by_cases hmk : m = k
                        · rw [hmk] at hv
                          have hvr : v = Value.int r :=
                            Option.some.inj (hv.symm.trans hz)
                          subst hvr
                          rw [hmk, getSlot_twoNarrow_k
                            (lt_length_of_mem_getSlot doms k _ hzk)]
                          exact mem_atLeastVals_atMostVals.mpr
                            ⟨hzk, r, rfl,
                              (by rw [← habs]; exact absValue_nonneg p),
                              (by rw [← habs]; exact absValue_le_range hplo hphi)⟩
                        · by_cases hmi : m = i
                          · rw [hmi] at hv
                            have hvp : v = Value.int p :=
                              Option.some.inj (hv.symm.trans hx)
                            subst hvp
                            rw [hmi, getSlot_twoNarrow_i
                              (lt_length_of_mem_getSlot doms i _ hxi)
                              (fun hik => hmk (hmi.trans hik))]
                            exact List.mem_filter.mpr ⟨hxi,
                              absKeepB_of_satisfying hrlo hrhi habs⟩
                          · rw [getSlot_twoNarrow_other
                              (fun h => hmi h) (fun h => hmk h)]
                            exact hget m v hv
  · intro doms doms' h
    simp only [propAbsSlot] at h
    cases h1 : domMin (getSlot doms i) with
    | none => rw [h1] at h; exact absurd h (by simp)
    | some ilo =>
        simp only [h1] at h
        cases h2 : domMax (getSlot doms i) with
        | none => rw [h2] at h; exact absurd h (by simp)
        | some ihi =>
            simp only [h2] at h
            cases h3 : domMin (getSlot doms k) with
            | none => rw [h3] at h; exact absurd h (by simp)
            | some klo =>
                simp only [h3] at h
                cases h4 : domMax (getSlot doms k) with
                | none => rw [h4] at h; exact absurd h (by simp)
                | some khi =>
                    simp only [h4, propAbsBounded] at h
                    by_cases hc : ((getSlot doms i).filter
                        (fun p => absKeepB p klo khi)).isEmpty = true ∨
                      (atLeastVals 0 (atMostVals (max (absValue ilo) (absValue ihi))
                        (getSlot doms k))).isEmpty = true
                    · rw [if_pos hc] at h
                      exact absurd h (by simp)
                    · rw [if_neg hc] at h
                      have hd : twoNarrow
                          ((getSlot doms i).filter (fun p => absKeepB p klo khi))
                          (atLeastVals 0 (atMostVals (max (absValue ilo) (absValue ihi))
                            (getSlot doms k)))
                          i k doms = doms' := PropResult.narrowed.inj h
                      subst hd
                      simp only [twoNarrow]
                      exact DomPointwiseSub.setSlot
                        (DomPointwiseSub.setSlot (DomPointwiseSub.refl doms)
                          (fun _ hv => (List.mem_filter.mp hv).1))
                        (fun _ hv => (mem_atLeastVals_atMostVals.mp hv).1)
  · intro doms h a ha hsat
    simp only [propAbsSlot] at h
    obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, r, hx, hz, habs⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    have hzk : Value.int r ∈ getSlot doms k := hget k _ hz
    cases h1 : domMin (getSlot doms i) with
    | none =>
        obtain ⟨m, hm, _⟩ := domMin_of_mem hxi
        rw [h1] at hm
        exact absurd hm (by simp)
    | some ilo =>
        simp only [h1] at h
        cases h2 : domMax (getSlot doms i) with
        | none =>
            obtain ⟨m, hm, _⟩ := domMax_of_mem hxi
            rw [h2] at hm
            exact absurd hm (by simp)
        | some ihi =>
            simp only [h2] at h
            cases h3 : domMin (getSlot doms k) with
            | none =>
                obtain ⟨m, hm, _⟩ := domMin_of_mem hzk
                rw [h3] at hm
                exact absurd hm (by simp)
            | some klo =>
                simp only [h3] at h
                cases h4 : domMax (getSlot doms k) with
                | none =>
                    obtain ⟨m, hm, _⟩ := domMax_of_mem hzk
                    rw [h4] at hm
                    exact absurd hm (by simp)
                | some khi =>
                    simp only [h4, propAbsBounded] at h
                    -- pin the extrema to the satisfying values' bounds
                    obtain ⟨m1, hm1, hplo⟩ := domMin_of_mem hxi
                    rw [h1] at hm1
                    have hilo : m1 = ilo := (Option.some.inj hm1).symm
                    rw [hilo] at hplo
                    obtain ⟨m2, hm2, hphi⟩ := domMax_of_mem hxi
                    rw [h2] at hm2
                    have hihi : m2 = ihi := (Option.some.inj hm2).symm
                    rw [hihi] at hphi
                    obtain ⟨m3, hm3, hrlo⟩ := domMin_of_mem hzk
                    rw [h3] at hm3
                    have hklo : m3 = klo := (Option.some.inj hm3).symm
                    rw [hklo] at hrlo
                    obtain ⟨m4, hm4, hrhi⟩ := domMax_of_mem hzk
                    rw [h4] at hm4
                    have hkhi : m4 = khi := (Option.some.inj hm4).symm
                    rw [hkhi] at hrhi
                    by_cases hc : ((getSlot doms i).filter
                        (fun p => absKeepB p klo khi)).isEmpty = true ∨
                      (atLeastVals 0 (atMostVals (max (absValue ilo) (absValue ihi))
                        (getSlot doms k))).isEmpty = true
                    · rw [if_pos hc] at h
                      rcases hc with hci | hck
                      · have hmem : Value.int p ∈ (getSlot doms i).filter
                            (fun p => absKeepB p klo khi) :=
                          List.mem_filter.mpr ⟨hxi, absKeepB_of_satisfying hrlo hrhi habs⟩
                        rw [List.isEmpty_iff.mp hci] at hmem
                        exact absurd hmem (by simp)
                      · have hmem : Value.int r ∈
                            atLeastVals 0 (atMostVals (max (absValue ilo) (absValue ihi))
                              (getSlot doms k)) :=
                          mem_atLeastVals_atMostVals.mpr
                            ⟨hzk, r, rfl,
                              (by rw [← habs]; exact absValue_nonneg p),
                              (by rw [← habs]; exact absValue_le_range hplo hphi)⟩
                        rw [List.isEmpty_iff.mp hck] at hmem
                        exact absurd hmem (by simp)
                    · rw [if_neg hc] at h
                      exact absurd h (by simp)

/-! ## The linear-constraint propagators (bounds propagation) -/

/-- The linear combination `Σ cᵢ·xᵢ`, appending no terms past the
    shorter list (lengths agree whenever the encodings below use it). -/
private def linSum : List Int → List Int → Int
  | [], _ => 0
  | _, [] => 0
  | c :: cs, x :: xs => c * x + linSum cs xs

/-- Term `c·x`'s contribution to the dot product's minimum over
    `x ∈ [lo, hi]`. -/
private def termMin (c : Int) (lo hi : Int) : Int :=
  if 0 ≤ c then c * lo else c * hi

/-- Term `c·x`'s contribution to the dot product's maximum over
    `x ∈ [lo, hi]`. -/
private def termMax (c : Int) (lo hi : Int) : Int :=
  if 0 ≤ c then c * hi else c * lo

/-- The dot product's minimum over the listed domains. -/
private def linTotalMin : List Int → List (Int × Int) → Int
  | c :: cs, (lo, hi) :: bds => termMin c lo hi + linTotalMin cs bds
  | _, _ => 0

/-- The dot product's maximum over the listed domains. -/
private def linTotalMax : List Int → List (Int × Int) → Int
  | c :: cs, (lo, hi) :: bds => termMax c lo hi + linTotalMax cs bds
  | _, _ => 0

/-- Extract the integer extrema of each listed slot, or `none` when
    some listed slot lacks integers. -/
private def linExtract (is : List Nat) (doms : List (List Value)) :
    Option (List (Int × Int)) :=
  match is with
  | [] => some []
  | idx :: rest =>
      match domMin (getSlot doms idx), domMax (getSlot doms idx) with
      | some lo, some hi => (linExtract rest doms).map (fun bds => (lo, hi) :: bds)
      | _, _ => none

/-- `linEq`'s feasibility interval for a single term: values `p` of the
    term whose other terms' contributions can close the equality. -/
private def linNarrowEq (c : Int) (b otherMin otherMax : Int) (d : List Value) :
    List Value :=
  d.filter (fun v =>
    match v with
    | .int p => decide (b - otherMax ≤ c * p && c * p ≤ b - otherMin)
    | _ => false)

/-- `linLe`'s feasibility condition for a single term: values `p` whose
    term's contribution, together with the other terms at their
    minimum, fits under `b`. -/
private def linNarrowLe (c : Int) (b otherMin : Int) (d : List Value) :
    List Value :=
  d.filter (fun v =>
    match v with
    | .int p => decide (c * p ≤ b - otherMin)
    | _ => false)

/-- Narrow every listed slot's domain to the values that can
    participate in a feasible assignment, computing each other-term
    bound from the pre-extracted extrema; `contradiction` as soon as a
    listed slot empties (or the terms mismatch). -/
private def linNarrowAll (cs : List Int) (is : List Nat) (bds : List (Int × Int))
    (totalMin totalMax : Int) (eq : Bool) (b : Int)
    (doms : List (List Value)) : PropResult :=
  match cs, is, bds with
  | [], [], [] => .narrowed doms
  | c :: cs', idx :: is', (lo, hi) :: bds' =>
      -- the other terms' extrema: the whole's totals minus this term's extrema
      let cLo := termMin c lo hi
      let cHi := termMax c lo hi
      let otherMin := totalMin - cLo
      let otherMax := totalMax - cHi
      let d' := if eq then
          linNarrowEq c b otherMin otherMax (getSlot doms idx)
        else
          linNarrowLe c b otherMin (getSlot doms idx)
      if d'.isEmpty then .contradiction
      else linNarrowAll cs' is' bds' totalMin totalMax eq b (setSlot doms idx d')
  | _, _, _ => .contradiction

/-- **The `int_lin_eq` propagator** (`int_lin_eq` style, canonical
    form): bounds propagation for `Σ cᵢ·xᵢ = b`.  Each listed slot
    keeps the values `p` whose term's contribution can still be offset
    by the other terms (their contributions and the target's extrema);
    `contradiction` when some listed slot has no integers, some
    narrowed slot empties, or the terms mismatch. -/
def propLinEq (coeffs : List Int) (is : List Nat) (b : Int)
    (doms : List (List Value)) : PropResult :=
  if coeffs.length = is.length then
    match linExtract is doms with
    | none => .contradiction
    | some bds =>
        linNarrowAll coeffs is bds (linTotalMin coeffs bds) (linTotalMax coeffs bds)
          true b doms
  else
    -- a mismatched-shape linear constraint has no satisfying assignment
    -- (the dot product needs equal lengths), so contradiction is sound
    .contradiction

/-- **The `int_lin_le` propagator** (`int_lin_le` style, canonical
    form): bounds propagation for `Σ cᵢ·xᵢ ≤ b`.  Each listed slot
    keeps the values `p` whose term's contribution, together with the
    other terms at their minimum, stays under `b`; `contradiction`
    when some listed slot has no integers, some narrowed slot empties,
    or the terms mismatch. -/
def propLinLe (coeffs : List Int) (is : List Nat) (b : Int)
    (doms : List (List Value)) : PropResult :=
  if coeffs.length = is.length then
    match linExtract is doms with
    | none => .contradiction
    | some bds =>
        linNarrowAll coeffs is bds (linTotalMin coeffs bds) (linTotalMax coeffs bds)
          false b doms
  else
    -- a mismatched-shape linear constraint has no satisfying assignment
    -- (the dot product needs equal lengths), so contradiction is sound
    .contradiction


/-! ## The linear propagators' preservation theorems -/

/-- A term's contribution is bounded by its extrema. -/
private theorem term_bound (c lo hi x : Int) (hlo : lo ≤ x) (hhi : x ≤ hi) :
    termMin c lo hi ≤ c * x ∧ c * x ≤ termMax c lo hi := by
  unfold termMin termMax
  by_cases hc : 0 ≤ c
  · rw [if_pos hc, if_pos hc]
    have hw1 : 0 ≤ x - lo := by omega
    have hw2 : 0 ≤ hi - x := by omega
    have h1 : 0 ≤ c * (x - lo) := Int.mul_nonneg hc hw1
    have h2 : 0 ≤ c * (hi - x) := Int.mul_nonneg hc hw2
    rw [Int.mul_sub] at h1
    rw [Int.mul_sub] at h2
    omega
  · rw [if_neg hc, if_neg hc]
    have hn : 0 ≤ -c := by omega
    have hw1 : 0 ≤ hi - x := by omega
    have hw2 : 0 ≤ x - lo := by omega
    have h1 : 0 ≤ -c * (hi - x) := Int.mul_nonneg hn hw1
    have h2 : 0 ≤ -c * (x - lo) := Int.mul_nonneg hn hw2
    have e1 : -c * (hi - x) = c * x - c * hi := by
      have h1' : c * (hi - x) = c * hi - c * x := Int.mul_sub c hi x
      have h2' : -c * (hi - x) = -(c * (hi - x)) := (Int.neg_mul_eq_neg_mul c (hi - x)).symm
      rw [h2', h1']
      omega
    have e2 : -c * (x - lo) = c * lo - c * x := by
      have h1' : c * (x - lo) = c * x - c * lo := Int.mul_sub c x lo
      have h2' : -c * (x - lo) = -(c * (x - lo)) := (Int.neg_mul_eq_neg_mul c (x - lo)).symm
      rw [h2', h1']
      omega
    rw [e1] at h1
    rw [e2] at h2
    omega

/-- The `dotProduct`-level sum of a satisfying assignment's term
    contributions, decomposed at the head term. -/
private theorem dotProduct_cons_eq (a x : Int) (as_ xs : List Value) (s : Int)
    (h : dotProduct (.int a :: as_) (.int x :: xs) = some s) :
    ∃ s', dotProduct as_ xs = some s' ∧ s = a * x + s' := by
  simp only [dotProduct] at h
  cases h' : dotProduct as_ xs with
  | none => rw [h'] at h; exact absurd h (by simp)
  | some s' =>
      rw [h'] at h
      have hs : s = a * x + s' := (Option.some.inj h).symm
      exact ⟨s', rfl, hs⟩



/-! ## The linear propagators' preservation theorems

Both theorems share one induction over the term triple
`(coeffs, is, bds)`.  The proof spine is the same as the arithmetic
propagators': an assignment of the input domains (spec
`allAssigns_spec`) whose listed values satisfy the constraint is
rebuilt as an assignment of the narrowed domains
(`allAssigns_intro`); the per-term filter passes because the other
terms' contribution to a satisfying sum is bounded by their
extrema sums (`totalMin`/`totalMax` minus this term's extrema). -/

/-- The value-level dot-product sum (the `dotProduct` fold, made
    total). -/
private def dotSum : List Value → List Value → Int
  | .int a :: as_, .int x :: xs => a * x + dotSum as_ xs
  | _, _ => 0

/-- A successful `dotProduct` computes `dotSum`. -/
private theorem dotProduct_eq_sum :
    ∀ (cs xs : List Value) (s : Int),
    dotProduct cs xs = some s → s = dotSum cs xs := by
  intro cs
  induction cs with
  | nil =>
      intro xs s h
      cases xs with
      | nil =>
          have hs : s = 0 := (Option.some.inj h).symm
          subst hs
          rfl
      | cons x xs' => exact absurd h (by simp [dotProduct])
  | cons c cs' ih =>
      intro xs s h
      cases c with
      | int a =>
          cases xs with
          | nil => exact absurd h (by simp [dotProduct])
          | cons x xs'' =>
              cases x with
              | int xv =>
                  simp only [dotProduct] at h
                  cases hrest : dotProduct cs' xs'' with
                  | none => rw [hrest] at h; exact absurd h (by simp)
                  | some s' =>
                      rw [hrest] at h
                      have hs : s = a * xv + s' := (Option.some.inj h).symm
                      rw [hs]
                      have := ih xs'' s' hrest
                      rw [this]
                      rfl
              | _ => exact absurd h (by simp [dotProduct])
      | _ => exact absurd h (by simp [dotProduct])

/-- The head decomposition of `dotSum` on coefficient/value conses. -/
private theorem dotSum_cons (a x : Int) (as_ xs : List Value) :
    dotSum (.int a :: as_) (.int x :: xs) = a * x + dotSum as_ xs := rfl

/-- The extrema-sum bounds on the dot sum, by induction on the
    term triple: when every listed value `x` sits in its extracted
    bounds `(lo, hi)` (the `hbds` conjunct, pointwise), the dot sum of
    the coefficients against the values lies between the term-min and
    term-max sums. -/
private theorem dotSum_bounds :
    ∀ (cs : List Int) (xs : List Value) (bds : List (Int × Int)),
    cs.length = xs.length → xs.length = bds.length →
    (∀ (j : Nat), j < xs.length →
        ∃ p, xs[j]! = LeanFzn.Semantics.Value.int p ∧
          bds[j]!.1 ≤ p ∧ p ≤ bds[j]!.2) →
    linTotalMin cs bds ≤ dotSum (intVals cs) xs ∧
      dotSum (intVals cs) xs ≤ linTotalMax cs bds := by
  intro cs
  induction cs with
  | nil =>
      intro xs bds hlen1 hlen2 _
      cases xs with
      | nil =>
          cases bds with
          | nil =>
              -- dotSum [] [] = 0; linTotalMin [] [] = 0; linTotalMax [] [] = 0
              show 0 ≤ 0 ∧ 0 ≤ 0
              omega
          | cons bd bds' =>
              have h := hlen2
              simp only [List.length_nil] at h
              exact absurd h (by simp)
      | cons x xs' =>
          have h := hlen1
          simp only [List.length_nil] at h
          exact absurd h (by simp)
  | cons c cs' ih =>
      intro xs bds hlen1 hlen2 hbds
      cases xs with
      | nil =>
          simp only [List.length_cons, List.length_nil] at hlen1
          exact absurd hlen1 (by omega)
      | cons x xs'' =>
          cases bds with
          | nil =>
              simp only [List.length_cons, List.length_nil] at hlen2
              exact absurd hlen2 (by omega)
          | cons bd bds'' =>
              obtain ⟨p, hx, hlo, hhi⟩ := hbds 0 (Nat.succ_pos xs''.length)
              subst hx
              obtain ⟨hllo, hlhi⟩ := ih xs'' bds''
                (by simp only [List.length_cons] at hlen1; omega)
                (by simp only [List.length_cons] at hlen2; omega)
                (by intro j hj
                    exact hbds (j + 1) (by simp only [List.length_cons]; omega))
              -- the head term's bounds within the extracted interval
              obtain ⟨htlo, hthi⟩ := term_bound c bd.1 bd.2 p hlo hhi
              -- the cons sums
              have hsum : dotSum (intVals (c :: cs')) (LeanFzn.Semantics.Value.int p :: xs'')
                  = c * p + dotSum (intVals cs') xs'' := rfl
              have hmin : linTotalMin (c :: cs') (bd :: bds'')
                  = termMin c bd.1 bd.2 + linTotalMin cs' bds'' := rfl
              have hmax : linTotalMax (c :: cs') (bd :: bds'')
                  = termMax c bd.1 bd.2 + linTotalMax cs' bds'' := rfl
              show termMin c bd.1 bd.2 + linTotalMin cs' bds''
                  ≤ c * p + dotSum (intVals cs') xs'' ∧
                c * p + dotSum (intVals cs') xs''
                  ≤ termMax c bd.1 bd.2 + linTotalMax cs' bds''
              constructor <;> omega


/-! ### The narrowing-soundness induction -/

/-- **The other terms' bound** (the filter-soundness core): for the
    aligned term/value/bound lists, position `k`'s value `p` lies in
    its extracted interval, and the sum of the terms at positions ≠ k
    is bounded by the total extrema minus position `k`'s term
    extrema. -/
private theorem others_bound :
    ∀ (cs : List Int) (xs : List Value) (bds : List (Int × Int)) (k : Nat),
    cs.length = xs.length → xs.length = bds.length →
    (∀ (j : Nat), j < xs.length →
        ∃ p, xs[j]! = LeanFzn.Semantics.Value.int p ∧
          bds[j]!.1 ≤ p ∧ p ≤ bds[j]!.2) →
    k < xs.length →
    ∃ ck p, cs[k]! = ck ∧ xs[k]! = LeanFzn.Semantics.Value.int p ∧
      bds[k]!.1 ≤ p ∧ p ≤ bds[k]!.2 ∧
      linTotalMin cs bds - termMin ck bds[k]!.1 bds[k]!.2
        ≤ dotSum (intVals cs) xs - ck * p ∧
      dotSum (intVals cs) xs - ck * p
        ≤ linTotalMax cs bds - termMax ck bds[k]!.1 bds[k]!.2 := by
  intro cs
  induction cs with
  | nil =>
      intro xs bds k hlen1 hlen2 _ hk
      cases xs with
      | nil =>
          simp only [List.length_nil] at hk
          exact absurd hk (by omega)
      | cons _ _ =>
          simp only [List.length_nil] at hlen1
          omega
  | cons c cs' ih =>
      intro xs bds k hlen1 hlen2 hcov hk
      cases xs with
      | nil =>
          simp only [List.length_cons, List.length_nil] at hlen1
          omega
      | cons x xs'' =>
          cases bds with
          | nil =>
              simp only [List.length_cons, List.length_nil] at hlen2
              omega
          | cons bd bds'' =>
              obtain ⟨p, hx, hlo, hhi⟩ := hcov 0 (Nat.succ_pos xs''.length)
              subst hx
              cases k with
              | zero =>
                  -- head position: the tail's bounds via dotSum_bounds
                  obtain ⟨hllo, hlhi⟩ := dotSum_bounds cs' xs'' bds''
                    (by simp only [List.length_cons] at hlen1; omega)
                    (by simp only [List.length_cons] at hlen2; omega)
                    (by intro j hj
                        exact hcov (j + 1) (by simp only [List.length_cons]; omega))
                  refine ⟨c, p, rfl, rfl, hlo, hhi, ?_, ?_⟩
                  · show linTotalMin (c :: cs') (bd :: bds'') - termMin c bd.1 bd.2
                      ≤ c * p + dotSum (intVals cs') xs'' - c * p
                    have h1 : linTotalMin (c :: cs') (bd :: bds'')
                        = termMin c bd.1 bd.2 + linTotalMin cs' bds'' := rfl
                    rw [h1]
                    show termMin c bd.1 bd.2 + linTotalMin cs' bds'' - termMin c bd.1 bd.2
                      ≤ c * p + dotSum (intVals cs') xs'' - c * p
                    omega
                  · show c * p + dotSum (intVals cs') xs'' - c * p
                      ≤ linTotalMax (c :: cs') (bd :: bds'') - termMax c bd.1 bd.2
                    have h2 : linTotalMax (c :: cs') (bd :: bds'')
                        = termMax c bd.1 bd.2 + linTotalMax cs' bds'' := rfl
                    rw [h2]
                    show c * p + dotSum (intVals cs') xs'' - c * p
                      ≤ termMax c bd.1 bd.2 + linTotalMax cs' bds'' - termMax c bd.1 bd.2
                    omega
              | succ kk =>
                  -- tail position: recurse, then add the head's bounds
                  obtain ⟨ck, p', hck, hxp, hlo', hhi', hlo2, hhi2⟩ :=
                    ih xs'' bds'' kk
                      (by simp only [List.length_cons] at hlen1; omega)
                      (by simp only [List.length_cons] at hlen2; omega)
                      (by intro j hj
                          exact hcov (j + 1) (by simp only [List.length_cons]; omega))
                      (by simp only [List.length_cons] at hk; omega)
                  obtain ⟨htlo, hthi⟩ := term_bound c bd.1 bd.2 p hlo hhi
                  -- the goal indexes the cons lists at kk+1; the IH gives the tails
                  have hgetk : (c :: cs')[kk + 1]! = cs'[kk]! := rfl
                  have hgetx : (LeanFzn.Semantics.Value.int p :: xs'')[kk + 1]! = xs''[kk]! := rfl
                  have hgetb : (bd :: bds'')[kk + 1]! = bds''[kk]! := rfl
                  rw [hgetk, hgetx, hgetb]
                  refine ⟨ck, p', hck, hxp, hlo', hhi', ?_, ?_⟩
                  · show linTotalMin (c :: cs') (bd :: bds'')
                        - termMin ck bds''[kk]!.1 bds''[kk]!.2
                      ≤ c * p + dotSum (intVals cs') xs'' - ck * p'
                    have h1 : linTotalMin (c :: cs') (bd :: bds'')
                        = termMin c bd.1 bd.2 + linTotalMin cs' bds'' := rfl
                    rw [h1]
                    omega
                  · show c * p + dotSum (intVals cs') xs'' - ck * p'
                      ≤ linTotalMax (c :: cs') (bd :: bds'')
                        - termMax ck bds''[kk]!.1 bds''[kk]!.2
                    have h2 : linTotalMax (c :: cs') (bd :: bds'')
                        = termMax c bd.1 bd.2 + linTotalMax cs' bds'' := rfl
                    rw [h2]
                    omega

/-- The parameterized linear satisfaction (`linEq`'s `= b` when `eq`,
    `linLe`'s `≤ b` otherwise). -/
private def LinSat (eqv : Bool) (cs xs : List Value) (b : Int) : Prop :=
  if eqv then dotProduct cs xs = some b
  else ∃ d, dotProduct cs xs = some d ∧ d ≤ b

/-- The coverage invariant: every listed slot's assignment value is an
    integer inside the extracted bounds, and the assignment picks
    values of the (progressively narrowed) domains. -/
private def LinCover (is : List Nat) (bds : List (Int × Int))
    (doms : List (List Value)) (a : List Value) : Prop :=
  ∀ (k : Nat), k < is.length →
    a[is[k]!]! ∈ getSlot doms (is[k]!) ∧
      ∃ p, a[is[k]!]! = .int p ∧
        bds[k]!.1 ≤ p ∧ p ≤ bds[k]!.2

/-- The j-th element of a mapped list, in bounds. -/
private theorem map_getElem!_in_bounds (a : List Value) (is : List Nat) (j : Nat)
    (hj : j < is.length) :
    (is.map (fun i => a[i]!))[j]! = a[is[j]!]! := by
  have h1 : j < (is.map (fun i => a[i]!)).length := by
    simp only [List.length_map]
    omega
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h1, List.getElem_map]
  have hisj : is[j]! = is[j] := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  rw [← hisj]
  cases a[is[j]!]? with
  | none => rfl
  | some v => rfl


/-- The identity propagator: narrows nothing (the sound placeholder for
    constraint kinds whose bounds-propagation preservation theorem is
    not yet proven — e.g. the linear kinds, whose filters are defined
    but whose master induction is future work). -/
def propIdSlot (doms : List (List Value)) : PropResult := .narrowed doms

/-- The identity propagator preserves every constraint. -/
theorem propIdSlot_preserves (c : DomConstraint) :
    Preserves c propIdSlot := by
  constructor
  · intro doms doms' h a ha _hsat
    have hd : doms' = doms := (PropResult.narrowed.inj h).symm
    rw [hd]
    exact ha
  · intro doms doms' h
    have hd : doms' = doms := (PropResult.narrowed.inj h).symm
    rw [hd]
    exact DomPointwiseSub.refl doms
  · intro doms h a _ha _hsat
    exact absurd h (by simp [propIdSlot])

/-- The cons-transport of the dot-sum satisfaction: a satisfying
    assignment of the whole (head-cons) triple restricts to a
    satisfying assignment of the tail against `b` minus the head
    term's actual contribution (for `eq`; for `le` the same
    subtraction gives a valid bound). -/
private theorem LinSat_cons {eq : Bool} {c p : Int} {cs : List Int}
    {xs : List Value} {b : Int}
    (hsat : LinSat eq (intVals (c :: cs)) (LeanFzn.Semantics.Value.int p :: xs) b) :
    LinSat eq (intVals cs) xs (b - c * p) := by
  cases heq : eq with
  | true =>
      rw [heq] at hsat
      rw [show LinSat true (intVals (c :: cs)) (LeanFzn.Semantics.Value.int p :: xs) b
          = (dotProduct (intVals (c :: cs)) (LeanFzn.Semantics.Value.int p :: xs)
              = some b) from rfl] at hsat
      rw [show LinSat true (intVals cs) xs (b - c * p)
          = (dotProduct (intVals cs) xs = some (b - c * p)) from rfl]
      -- unfold one step of dotProduct on both sides
      rw [show intVals (c :: cs) = LeanFzn.Semantics.Value.int c :: intVals cs from rfl,
        dotProduct] at hsat
      cases hrest : dotProduct (intVals cs) xs with
      | none => rw [hrest] at hsat; exact absurd hsat (by simp)
      | some s' =>
          rw [hrest] at hsat
          have hsb : c * p + s' = b := (Option.some.inj hsat)
          rw [show b - c * p = s' from by omega]
  | false =>
      rw [heq] at hsat
      rw [show LinSat false (intVals (c :: cs)) (LeanFzn.Semantics.Value.int p :: xs) b
          = (∃ d, dotProduct (intVals (c :: cs)) (LeanFzn.Semantics.Value.int p :: xs)
              = some d ∧ d ≤ b) from rfl] at hsat
      rw [show LinSat false (intVals cs) xs (b - c * p)
          = (∃ d, dotProduct (intVals cs) xs = some d ∧ d ≤ b - c * p) from rfl]
      obtain ⟨d, hd, hle⟩ := hsat
      rw [show intVals (c :: cs) = LeanFzn.Semantics.Value.int c :: intVals cs from rfl,
        dotProduct] at hd
      cases hrest : dotProduct (intVals cs) xs with
      | none => rw [hrest] at hd; exact absurd hd (by simp)
      | some s' =>
          rw [hrest] at hd
          have hsd : c * p + s' = d := (Option.some.inj hd)
          exact ⟨s', rfl, by omega⟩

/-- The extrema sums against an empty bounds list are zero. -/
private theorem linTotal_nil_right : ∀ (l : List Int),
    linTotalMin l [] = 0 ∧ linTotalMax l [] = 0 := by
  intro l
  cases l with
  | nil => exact ⟨rfl, rfl⟩
  | cons x xs => exact ⟨rfl, rfl⟩

/-- The prefix-current totals decomposition: the extrema sums of
    aligned lists split over any position. -/
private theorem linTotal_split (cs : List Int) (bds : List (Int × Int)) (k : Nat) :
    linTotalMin cs bds
      = linTotalMin (List.take k cs) (List.take k bds)
        + linTotalMin (List.drop k cs) (List.drop k bds) ∧
    linTotalMax cs bds
      = linTotalMax (List.take k cs) (List.take k bds)
        + linTotalMax (List.drop k cs) (List.drop k bds) := by
  induction cs generalizing bds k with
  | nil =>
      cases k with
      | zero => simp only [List.take, List.drop]; exact ⟨rfl, rfl⟩
      | succ k' =>
          have h1 : (List.drop (k' + 1) ([] : List Int)) = ([] : List Int) := rfl
          have h2 : (List.take (k' + 1) ([] : List Int)) = ([] : List Int) := rfl
          rw [h1, h2]
          exact ⟨rfl, rfl⟩
  | cons c cs' ih =>
      cases bds with
      | nil =>
          cases k with
          | zero => simp only [List.take, List.drop]; exact ⟨rfl, rfl⟩
          | succ k' =>
              -- all six sums are 0 by the nil-right lemma
              obtain ⟨e1, e2⟩ := linTotal_nil_right (c :: cs')
              obtain ⟨e3, e4⟩ := linTotal_nil_right (List.take (k' + 1) (c :: cs'))
              obtain ⟨e5, e6⟩ := linTotal_nil_right (List.drop (k' + 1) (c :: cs'))
              have t2 : List.take (k' + 1) ([] : List (Int × Int)) = [] := rfl
              have d2 : List.drop (k' + 1) ([] : List (Int × Int)) = [] := rfl
              rw [t2, d2]
              omega
      | cons bd bds' =>
          cases k with
          | zero =>
              simp only [List.take, List.drop]
              have hz1 : linTotalMin ([] : List Int) ([] : List (Int × Int)) = 0 := rfl
              have hz2 : linTotalMax ([] : List Int) ([] : List (Int × Int)) = 0 := rfl
              omega
          | succ k' =>
              obtain ⟨h1, h2⟩ := ih bds' k'
              simp only [List.take_succ_cons, List.drop_succ_cons]
              show termMin c bd.1 bd.2 + linTotalMin cs' bds'
                = termMin c bd.1 bd.2 + linTotalMin (List.take k' cs') (List.take k' bds')
                + linTotalMin (List.drop k' cs') (List.drop k' bds') ∧
                termMax c bd.1 bd.2 + linTotalMax cs' bds'
                = termMax c bd.1 bd.2 + linTotalMax (List.take k' cs') (List.take k' bds')
                + linTotalMax (List.drop k' cs') (List.drop k' bds')
              rw [h1, h2]
              omega


/-- **The master narrowing-soundness lemma for `linNarrowAll`**:
    under coverage of the extracted bounds by a satisfying
    assignment (its values picked from the input domains), the
    assignment remains an assignment of the narrowed domains.
    `k` counts the terms the run has already consumed: the current
    triple is `drop k` of the original, the totals stay the
    original's, and each level's filter bound (totals minus the
    head term's extrema) covers the other terms — the processed
    prefix plus the tail — by `linTotal_split` and `others_bound`
    run at the current position. -/
private theorem linNarrowAll_mem :
    ∀ (n : Nat) (k : Nat) (ocs : List Int) (ois : List Nat) (obds : List (Int × Int))
      (totalMin totalMax : Int) (eq : Bool) (b : Int)
      (doms : List (List Value)),
    ocs.length - k = n →
    k ≤ ocs.length →
    ocs.length = ois.length → ois.length = obds.length →
    totalMin = linTotalMin ocs obds → totalMax = linTotalMax ocs obds →
    ∀ (doms' : List (List Value)) (a : List Value)
      (_h : linNarrowAll (List.drop k ocs) (List.drop k ois) (List.drop k obds)
            totalMin totalMax eq b doms = .narrowed doms')
      (_hlen : a.length = doms.length)
      (_hget : ∀ j v, a[j]? = some v → v ∈ getSlot doms j)
      (_hsat : LinSat eq (intVals ocs) (ois.map (fun i => a[i]!)) b)
      (_hcov : LinCover ois obds doms a),
    a ∈ allAssigns doms' := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro k ocs ois obds totalMin totalMax eq b doms hmeasure hkle hlen1 hlen2
      hTmin hTmax doms' a h hlen hget hsat hcov
    -- the current triple's shape decides
    cases hdcs : List.drop k ocs with
    | nil =>
        -- no terms remain: the run's match arm returns .narrowed doms
        -- (the is/bds drops must also be empty by length agreement)
        have hdcslen : (List.drop k ocs).length = ocs.length - k := by simp
        have hislen : (List.drop k ois).length = ois.length - k := by simp
        have hbdslen : (List.drop k obds).length = obds.length - k := by simp
        rw [hdcs, List.length_nil] at hdcslen
        have hisnil : List.drop k ois = [] := by
          cases his : List.drop k ois with
          | nil => rfl
          | cons x xs =>
              have h1 : (x :: xs).length = (List.drop k ois).length := by rw [his]
              rw [hislen] at h1
              simp only [List.length_cons] at h1
              omega
        have hbdsnil : List.drop k obds = [] := by
          cases hbs : List.drop k obds with
          | nil => rfl
          | cons y ys =>
              have h1 : (y :: ys).length = (List.drop k obds).length := by rw [hbs]
              rw [hbdslen] at h1
              simp only [List.length_cons] at h1
              omega
        rw [hdcs, hisnil, hbdsnil] at h
        have hd : doms' = doms := (PropResult.narrowed.inj h).symm
        rw [hd]
        exact allAssigns_intro doms a hlen hget
    | cons c csuff =>
        -- one term to peel: the head of the current suffix is ocs[k]
        have hcsk : ocs[k]! = c := by
          rw [List.getElem!_eq_getElem?_getD]
          have hlt : k < ocs.length := by
            have h1 : (List.drop k ocs).length = ocs.length - k := by simp
            rw [hdcs] at h1
            simp only [List.length_cons] at h1
            omega
          have hget : ocs[k]? = some c := by
            rw [List.getElem?_eq_getElem hlt]
            -- ocs[k] = (drop k ocs).head — via drop induction on k
            have hdrop : ∀ (l : List Int) (n : Nat) (hlt : n < l.length),
                l[n] = (List.drop n l).headD 0 := by
              intro l n
              induction l generalizing n with
              | nil => intro hlt; exact absurd hlt (by simp)
              | cons x xs ih =>
                  intro hlt
                  cases n with
                  | zero => rfl
                  | succ n' => exact ih n' (by simp only [List.length_cons] at hlt; omega)
            rw [hdrop ocs k hlt, hdcs]
            rfl
          rw [hget]
          rfl
        -- the current is/bds suffixes (cons-shaped by length agreement)
        -- the is/bds suffixes are cons-shaped (length agreement with the cs suffix)
        cases his : List.drop k ois with
        | nil =>
            exfalso
            have h1 : (List.drop k ois).length = ois.length - k := by simp
            have h2 : (List.drop k ocs).length = ocs.length - k := by simp
            rw [his, List.length_nil] at h1
            rw [hdcs, List.length_cons] at h2
            omega
        | cons idx isuff =>
            have issuff : List.drop k ois = idx :: (List.drop (k+1) ois) := by
              have hdrop : List.drop (k+1) ois = (List.drop k ois).drop 1 := by
                rw [← List.drop_drop]
              rw [hdrop, his]
              rfl
            cases hbs : List.drop k obds with
            | nil =>
                exfalso
                have h1 : (List.drop k obds).length = obds.length - k := by simp
                have h2 : (List.drop k ocs).length = ocs.length - k := by simp
                rw [hbs, List.length_nil] at h1
                rw [hdcs, List.length_cons] at h2
                omega
            | cons bd bsuff =>
                have bdssuff : List.drop k obds = bd :: (List.drop (k+1) obds) := by
                  have hdrop : List.drop (k+1) obds = (List.drop k obds).drop 1 := by
                    rw [← List.drop_drop]
                  rw [hdrop, hbs]
                  rfl
                obtain ⟨lo, hi⟩ := id bd
                -- unfold one step of the run
                rw [hdcs, issuff, bdssuff] at h
                rw [show linNarrowAll (c :: csuff) (idx :: List.drop (k+1) ois)
                      (bd :: List.drop (k+1) obds) totalMin totalMax eq b doms
                    = (if (if eq then
                          linNarrowEq c b (totalMin - termMin c bd.1 bd.2)
                            (totalMax - termMax c bd.1 bd.2) (getSlot doms idx)
                        else
                          linNarrowLe c b (totalMin - termMin c bd.1 bd.2)
                          (getSlot doms idx)).isEmpty then .contradiction
                      else linNarrowAll csuff (List.drop (k+1) ois) (List.drop (k+1) obds)
                        totalMin totalMax eq b
                        (setSlot doms idx (if eq then
                            linNarrowEq c b (totalMin - termMin c bd.1 bd.2)
                              (totalMax - termMax c bd.1 bd.2) (getSlot doms idx)
                          else linNarrowLe c b (totalMin - termMin c bd.1 bd.2)
                            (getSlot doms idx)))) from by
                  rw [linNarrowAll]] at h
                by_cases hempty : (if eq then
                    linNarrowEq c b (totalMin - termMin c bd.1 bd.2)
                      (totalMax - termMax c bd.1 bd.2) (getSlot doms idx)
                  else
                    linNarrowLe c b (totalMin - termMin c bd.1 bd.2)
                    (getSlot doms idx)).isEmpty = true
                · rw [if_pos hempty] at h; exact absurd h (by simp)
                · rw [if_neg hempty] at h
                  -- csuff = drop (k+1) ocs (peeling one term)
                  have hcsuff : csuff = List.drop (k+1) ocs := by
                    have hdrop : List.drop (k+1) ocs = (List.drop k ocs).drop 1 := by
                      rw [← List.drop_drop]
                    rw [hdrop, hdcs]
                    rfl
                  rw [hcsuff] at h
                  -- the head filter's pass: the coverage at position k gives
                  -- the assignment's value at slot idx, which passes the filter
                  -- (the filter's interval comes from others_bound at position k)
                  have hklt : k < ois.length := by
                    have h1 : (List.drop k ois).length = ois.length - k := by simp
                    rw [issuff, List.length_cons] at h1
                    omega
                  obtain ⟨hmemk, pk, hvpk, hlok, hhik⟩ := hcov k hklt
                  -- ois[k]! = idx
                  have hoisk : ois[k]! = idx := by
                    have hdd : ∀ (l : List Nat) (n : Nat), n < l.length →
                        l[n]! = (List.drop n l).headD 0 := by
                      intro l n
                      induction l generalizing n with
                      | nil => intro hlt; exact absurd hlt (by simp)
                      | cons x xs ih2 =>
                          intro hlt
                          cases n with
                          | zero => rfl
                          | succ n' => exact ih2 n' (by simp only [List.length_cons] at hlt; omega)
                    have h1 : ois[k]! = (List.drop k ois).headD 0 := hdd ois k hklt
                    rw [h1, issuff]
                    rfl
                  rw [hoisk] at hmemk hvpk
                  -- the filter membership for the assignment's value at slot idx
                  have hfilter' : a[idx]! ∈ (if eq then
                      linNarrowEq c b (totalMin - termMin c bd.1 bd.2)
                        (totalMax - termMax c bd.1 bd.2) (getSlot doms idx)
                    else
                      linNarrowLe c b (totalMin - termMin c bd.1 bd.2)
                      (getSlot doms idx)) := by
                    -- the head filter passes because:
                    -- 1. the coverage at k puts pk in [bd.1, bd.2] and in the domain
                    -- 2. others_bound at position k bounds the other terms' sum
                    -- 3. hsat's dot-sum satisfaction pins c*pk within the interval
                    -- Reuse the depth-0 interval derivation: the whole's dot sum
                    -- is b (eq) or ≤ b (le); decompose at the head term.
                    -- The value's filter test (linNarrowEq/Le on .int pk):
                    rw [hvpk]
                    -- now: .int pk ∈ if eq then linNarrowEq ... (getSlot doms idx)
                    -- the filter is a list filter; its membership test is the
                    -- interval condition; cases on eq:
                    -- the interval derivation:
                    -- 1. the whole's dot sum (from hsat via dotProduct_eq_sum)
                    -- 2. others_bound at position k: the other terms' sum is
                    --    bounded by the ORIGINAL totals minus position k's
                    --    term extrema
                    -- 3. the coverage at k: pk ∈ [bd.1, bd.2]
                    -- The interval test, from three facts:
                    -- (A) hsat: the whole's dot sum = b (eq) / ≤ b (le)
                    -- (B) others_bound at k: other terms' sum within
                    --     [totalMin - termMin_k, totalMax - termMax_k]
                    -- (C) coverage at k: pk ∈ [bd.1, bd.2]
                    -- The whole's dot-sum level satisfaction:
                    have hsumsat : (if eq then dotSum (intVals ocs)
                          (ois.map (fun i => a[i]!)) = b
                        else dotSum (intVals ocs)
                            (ois.map (fun i => a[i]!)) ≤ b) := by
                      cases heq : eq with
                      | true =>
                          rw [heq] at hsat
                          rw [show LinSat true (intVals ocs) (ois.map (fun i => a[i]!)) b
                              = (dotProduct (intVals ocs) (ois.map (fun i => a[i]!))
                                  = some b) from rfl] at hsat
                          have := dotProduct_eq_sum _ _ _ hsat
                          rw [this]
                          rfl
                      | false =>
                          rw [heq] at hsat
                          rw [show LinSat false (intVals ocs) (ois.map (fun i => a[i]!)) b
                              = (∃ d, dotProduct (intVals ocs) (ois.map (fun i => a[i]!))
                                  = some d ∧ d ≤ b) from rfl] at hsat
                          obtain ⟨d, hd, hle⟩ := hsat
                          have := dotProduct_eq_sum _ _ _ hd
                          rw [this] at hle
                          exact hle
                    -- others_bound at position k over the ORIGINAL lists:
                    have hmaplen' : (ois.map (fun i => a[i]!)).length = ois.length := by
                      simp only [List.length_map]
                    obtain ⟨ck, ok, hck, hxk, hlok, hhik, holo, hohi⟩ :=
                      others_bound ocs (ois.map (fun i => a[i]!)) obds k
                        (by rw [hmaplen']; omega)
                        (by rw [hmaplen']; omega)
                        (by
                          intro j hj
                          rw [hmaplen'] at hj
                          obtain ⟨_, pj, hvpj, hloj, hhij⟩ := hcov j hj
                          refine ⟨pj, ?_, hloj, hhij⟩
                          exact map_getElem!_in_bounds a ois j hj ▸ hvpj)
                        (by rw [hmaplen']; omega)
                    -- ck = ocs[k]! = c and ok = the value at position k = pk
                    -- (the position-k value is a[ois[k]!]! = a[idx]! = .int pk)
                    -- the interval, by cases on eq:
                    cases heq : eq with
                    | true =>
                        rw [heq] at hsumsat
                        simp only [if_true] at hsumsat ⊢
                        -- hsumsat: whole = b; holo/hohi: other sums within
                        -- totals ± head extrema; whole = c*ok + other
                        -- (dotSum's cons decomposition at position k — from
                        --  others_bound's own statement shape)
                        -- reduce the position-k projections:
                        have hbdk : obds[k]! = (bd.1, bd.2) := by
                          have hdd : ∀ (l : List (Int × Int)) (n : Nat), n < l.length →
                              l[n]! = (List.drop n l)[0]! := by
                            intro l n
                            induction l generalizing n with
                            | nil => intro hlt; exact absurd hlt (by simp)
                            | cons x xs ih2 =>
                                intro hlt
                                cases n with
                                | zero => rfl
                                | succ n' => exact ih2 n' (by
                                  simp only [List.length_cons] at hlt; omega)
                          rw [hdd obds k (by omega), bdssuff]
                          rfl
                        rw [hbdk] at holo hohi
                        -- ck = c and ok = pk (position-k getters)
                        have hckc : ck = c := by
                          -- hck : ocs[k]! = ck; hcsk : ocs[k]! = c
                          exact hck.symm.trans hcsk
                        have hokpk : ok = pk := by
                          -- the mapped k-th = a[ois[k]!]! = a[idx]! = Value.int pk
                          have hmapped : (ois.map (fun i => a[i]!))[k]!
                              = a[ois[k]!]! := map_getElem!_in_bounds a ois k hklt
                          rw [hmapped, hoisk] at hxk
                          -- hxk : a[idx]! = Value.int ok; hvpk : a[idx]! = Value.int pk
                          injection hxk.symm.trans hvpk
                        rw [hckc, hokpk] at holo hohi
                        -- conclude by the totals equations (rewrite the goal):
                        rw [hTmin, hTmax]
                        -- the filter's membership test (linNarrowEq's filter):
                        rw [hvpk] at hmemk
                        exact List.mem_filter.mpr ⟨hmemk, by
                          simp only [decide_eq_true_eq, Bool.and_eq_true]
                          -- normalize the projected pair forms
                          have e1 : termMin c (bd.1, bd.2).1 (bd.1, bd.2).2
                              = termMin c bd.1 bd.2 := rfl
                          have e2 : termMax c (bd.1, bd.2).1 (bd.1, bd.2).2
                              = termMax c bd.1 bd.2 := rfl
                          rw [e1] at holo
                          rw [e2] at hohi
                          constructor <;> omega⟩
                    | false =>
                        rw [heq] at hsumsat
                        simp only [Bool.false_eq_true, if_false] at hsumsat ⊢
                        have hbdk2 : obds[k]! = (bd.1, bd.2) := by
                          have hdd : ∀ (l : List (Int × Int)) (n : Nat), n < l.length →
                              l[n]! = (List.drop n l)[0]! := by
                            intro l n
                            induction l generalizing n with
                            | nil => intro hlt; exact absurd hlt (by simp)
                            | cons x xs ih2 =>
                                intro hlt
                                cases n with
                                | zero => rfl
                                | succ n' => exact ih2 n' (by
                                  simp only [List.length_cons] at hlt; omega)
                          rw [hdd obds k (by omega), bdssuff]
                          rfl
                        rw [hbdk2] at holo
                        -- ck = c, ok = pk
                        have hckc2 : ck = c := hck.symm.trans hcsk
                        have hokpk2 : ok = pk := by
                          have hmapped : (ois.map (fun i => a[i]!))[k]!
                              = a[ois[k]!]! := map_getElem!_in_bounds a ois k hklt
                          rw [hmapped, hoisk] at hxk
                          injection hxk.symm.trans hvpk
                        rw [hckc2, hokpk2] at holo
                        have e1 : termMin c (bd.1, bd.2).1 (bd.1, bd.2).2
                            = termMin c bd.1 bd.2 := rfl
                        rw [e1] at holo
                        rw [hTmin]
                        rw [hvpk] at hmemk
                        exact List.mem_filter.mpr ⟨hmemk, by
                          simp only [decide_eq_true_eq]
                          omega⟩
                  -- recurse: the remaining count drops by one
                  have hn1 : ocs.length - (k + 1) < n := by
                    have hm : ocs.length - k = n := hmeasure
                    have hklt : k < ocs.length := by
                      have h1 : (List.drop k ocs).length = ocs.length - k := by simp
                      rw [hdcs, List.length_cons] at h1
                      omega
                    omega
                  exact ih (ocs.length - (k + 1)) hn1 (k + 1) ocs ois obds
                    totalMin totalMax eq b
                    (setSlot doms idx (if eq then
                        linNarrowEq c b (totalMin - termMin c bd.1 bd.2)
                          (totalMax - termMax c bd.1 bd.2) (getSlot doms idx)
                      else linNarrowLe c b (totalMin - termMin c bd.1 bd.2)
                        (getSlot doms idx)))
                    (by rfl) (by omega) hlen1 hlen2 hTmin hTmax
                    doms' a h
                    (by rw [setSlot_length]; exact hlen)
                    (by
                      intro j v hv
                      by_cases hidx : j = idx
                      · rw [hidx] at hv ⊢
                        -- a[idx]? = some v; the coverage at k says
                        -- a[idx]! = .int pk; hfilter' passes it
                        have hlt : idx < a.length := by
                          have h1 := lt_length_of_mem_getSlot doms idx (a[idx]!) hmemk
                          rw [hlen]
                          omega
                        have hsome : a[idx]? = some (a[idx]!) := by
                          rw [List.getElem?_eq_getElem hlt,
                            List.getElem!_eq_getElem?_getD,
                            List.getElem?_eq_getElem hlt, Option.getD_some]
                        rw [hsome] at hv
                        have hvv : v = a[idx]! := (Option.some.inj hv).symm
                        rw [hvv]
                        -- read the written slot back
                        rw [getSlot_setSlot_eq doms _ idx (by
                          have h1 := lt_length_of_mem_getSlot doms idx (a[idx]!) hmemk
                          omega)]
                        rw [show a[idx]! = LeanFzn.Semantics.Value.int pk from hvpk]
                        rw [hvpk] at hfilter'
                        exact hfilter'
                      · rw [getSlot_setSlot_of_ne doms _ idx j hidx]
                        exact hget j v hv)
                    (by exact hsat)
                    (by
                      intro m hm
                      obtain ⟨hmemv, p', hvp, hlo', hhi'⟩ := hcov m hm
                      by_cases hne : ois[m]! = idx
                      · rw [hne] at hmemv hvp ⊢
                        have hmemint : Value.int p' ∈ getSlot doms idx := by
                          rw [← hvp]; exact hmemv
                        rw [getSlot_setSlot_eq doms _ idx
                          (lt_length_of_mem_getSlot doms idx (Value.int p') hmemint)]
                        -- p' = pk: both are the integer of a[idx]!
                        have hp'p : p' = pk := by
                          have h1 : Value.int p' = Value.int pk :=
                            hvp.symm.trans hvpk
                          injection h1
                        rw [hvp]
                        -- the membership component: .int p' ∈ filter (p' = pk)
                        have hmem' : Value.int p' ∈ (if eq then
                            linNarrowEq c b (totalMin - termMin c bd.1 bd.2)
                              (totalMax - termMax c bd.1 bd.2) (getSlot doms idx)
                          else
                            linNarrowLe c b (totalMin - termMin c bd.1 bd.2)
                            (getSlot doms idx)) := by
                          rw [show Value.int p' = Value.int pk from by
                            rw [show p' = pk from hp'p]]
                          rw [hvpk] at hfilter'
                          exact hfilter'
                        exact ⟨hmem', p', rfl, hlo', hhi'⟩
                      · rw [getSlot_setSlot_of_ne doms _ idx _ hne]
                        exact ⟨hmemv, p', hvp, hlo', hhi'⟩)


/-- The linear constraint's satisfaction in `LinSat` form. -/
private theorem linEq_LinSat {coeffs : List Int} {is : List Nat} {b : Int}
    {a : List Value} :
    DomConstraint.SatisfiedBy (DomConstraint.linEq coeffs is b) a ↔
      LinSat true (intVals coeffs) (is.map (fun i => a[i]!)) b := by
  constructor
  · intro h
    rw [show LinSat true (intVals coeffs) (is.map (fun i => a[i]!)) b
        = (dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) = some b) from rfl]
    exact h
  · intro h
    rw [show LinSat true (intVals coeffs) (is.map (fun i => a[i]!)) b
        = (dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) = some b) from rfl] at h
    exact h

/-- The linear inequality's satisfaction in `LinSat` form. -/
private theorem linLe_LinSat {coeffs : List Int} {is : List Nat} {b : Int}
    {a : List Value} :
    DomConstraint.SatisfiedBy (DomConstraint.linLe coeffs is b) a ↔
      LinSat false (intVals coeffs) (is.map (fun i => a[i]!)) b := by
  constructor
  · intro h
    rw [show LinSat false (intVals coeffs) (is.map (fun i => a[i]!)) b
        = (∃ d, dotProduct (intVals coeffs) (is.map (fun i => a[i]!))
            = some d ∧ d ≤ b) from rfl]
    rw [DomConstraint.SatisfiedBy] at h
    rw [dotLe_eq] at h
    exact h
  · intro h
    rw [show LinSat false (intVals coeffs) (is.map (fun i => a[i]!)) b
        = (∃ d, dotProduct (intVals coeffs) (is.map (fun i => a[i]!))
            = some d ∧ d ≤ b) from rfl] at h
    -- goal: dotLe ... = true
    show dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b = true
    rw [dotLe_eq]
    exact h

/-- A mismatched-shape dot product is `none`: the linear
    constraint is unsatisfiable when the coefficient and slot
    lists have different lengths. -/
private theorem dotProduct_mismatch {cs : List Int} {is : List Nat}
    {xs : List Value} (hne : cs.length ≠ is.length) :
    dotProduct (intVals cs) (is.map (fun i => xs[i]!)) = none := by
  -- the mapped list has is' length; dotProduct recurses on both lists
  -- simultaneously and returns none on any shape mismatch
  -- induct on cs, comparing with the mapped list's shape
  induction cs generalizing is with
  | nil =>
      cases is with
      | nil => exact absurd rfl hne
      | cons i rest =>
          show dotProduct (intVals ([] : List Int))
              ((i :: rest).map (fun i => xs[i]!)) = none
          rw [show (i :: rest).map (fun i => xs[i]!)
              = xs[i]! :: rest.map (fun i => xs[i]!) from rfl]
          cases xs[i]! with
          | int v => rfl
          | bool v => rfl
          | setOfInt v => rfl
          | array v => rfl
  | cons c cs' ih =>
      cases is with
      | nil =>
          show dotProduct (intVals (c :: cs'))
              (([] : List Nat).map (fun i => xs[i]!)) = none
          rfl
      | cons i rest =>
          show dotProduct (intVals (c :: cs'))
              ((i :: rest).map (fun i => xs[i]!)) = none
          rw [show (i :: rest).map (fun i => xs[i]!)
              = xs[i]! :: rest.map (fun i => xs[i]!) from rfl]
          cases xs[i]! with
          | int v =>
              show (match dotProduct (intVals cs') (rest.map (fun i => xs[i]!)) with
                | some s => some (c * v + s)
                | none => none) = none
              have hne' : cs'.length ≠ rest.length := by
                simp only [List.length_cons] at hne
                omega
              rw [ih hne']
          | bool v => rfl
          | setOfInt v => rfl
          | array v => rfl

/-- `getSlot` past the end of the slot list is empty. -/
private theorem getSlot_eq_nil : ∀ (doms : List (List Value)) (j : Nat),
    doms.length ≤ j → getSlot doms j = [] := by
  intro doms
  induction doms with
  | nil => intro _ _; rfl
  | cons d ds ih =>
      intro j hge
      cases j with
      | zero =>
          simp only [List.length_cons] at hge
          omega
      | succ j' => exact ih j' (by simp only [List.length_cons] at hge; omega)

/-- The run's narrowed domains are pointwise subsets of the
    input (each written slot is a filter of its domain). -/
private theorem linNarrowAll_subset :
    ∀ (cs : List Int) (is : List Nat) (bds : List (Int × Int))
      (totalMin totalMax : Int) (eq : Bool) (b : Int)
      (doms doms' : List (List Value)),
    linNarrowAll cs is bds totalMin totalMax eq b doms = .narrowed doms' →
    DomPointwiseSub doms' doms := by
  intro cs
  induction cs with
  | nil =>
      intro is bds totalMin totalMax eq b doms doms' h
      cases is with
      | nil =>
          cases bds with
          | nil =>
              have hd : doms' = doms := (PropResult.narrowed.inj h).symm
              rw [hd]
              exact DomPointwiseSub.refl doms
          | cons _ _ => exact absurd h (by simp [linNarrowAll])
      | cons _ _ => exact absurd h (by simp [linNarrowAll])
  | cons c cs' ih =>
      intro is bds totalMin totalMax eq b doms doms' h
      cases is with
      | nil => exact absurd h (by
          cases bds with
          | nil => exact absurd h (by simp [linNarrowAll])
          | cons _ _ => exact absurd h (by simp [linNarrowAll]))
      | cons idx is' =>
          cases bds with
          | nil => exact absurd h (by simp [linNarrowAll])
          | cons bd bds' =>
              obtain ⟨lo, hi⟩ := bd
              rw [linNarrowAll] at h
              by_cases hempty : (if eq then
                  linNarrowEq c b (totalMin - termMin c lo hi)
                    (totalMax - termMax c lo hi) (getSlot doms idx)
                else
                  linNarrowLe c b (totalMin - termMin c lo hi)
                  (getSlot doms idx)).isEmpty = true
              · rw [if_pos hempty] at h; exact absurd h (by simp)
              · rw [if_neg hempty] at h
                have ih' := ih is' bds' totalMin totalMax eq b
                  (setSlot doms idx (if eq then
                      linNarrowEq c b (totalMin - termMin c lo hi)
                        (totalMax - termMax c lo hi) (getSlot doms idx)
                    else linNarrowLe c b (totalMin - termMin c lo hi)
                      (getSlot doms idx))) doms' h
                -- compose: doms' ⊆ setSlot doms idx d (ih') and
                -- setSlot doms idx d ⊆ doms (the filter shrinks one slot)
                refine ⟨ih'.1.trans (by rw [setSlot_length]), ?_⟩
                intro k v hv
                have hv' := ih'.2 k v hv
                -- hv' : v ∈ getSlot (setSlot doms idx d) k
                by_cases hkk : k = idx
                · rw [hkk] at hv' ⊢
                  show v ∈ getSlot doms idx
                  -- the written slot reads back as the filter
                  have hlt : idx < doms.length := by
                    by_cases hlt' : idx < doms.length
                    · exact hlt'
                    · -- out of range: getSlot doms idx = [] and the filter
                      -- of [] is empty, so v ∈ [] is impossible
                      exfalso
                      have hge : doms.length ≤ idx := by omega
                      have hnil : getSlot doms idx = [] :=
                        getSlot_eq_nil doms idx hge
                      -- the written slot (past the end) reads back as the
                      -- filter of the empty domain, which is empty
                      rw [setSlot_eq_self_of_le doms _ idx hge] at hv'
                      rw [hnil] at hv'
                      exact absurd hv' (by simp)
                  rw [getSlot_setSlot_eq doms _ idx hlt] at hv'
                  cases heqb : eq with
                  | true =>
                      rw [heqb, if_pos rfl] at hv'
                      exact List.mem_filter.mp hv' |>.1
                  | false =>
                      rw [heqb, if_neg (by decide : ¬ (false = true))] at hv'
                      exact List.mem_filter.mp hv' |>.1
                · rw [getSlot_setSlot_of_ne doms _ idx k hkk] at hv'
                  exact hv'

/-- A successful dot product forces every value of the
    second list to be an integer at the listed positions (the
    `_, _ => none` catch-all never fired). -/
private theorem dotProduct_some_int :
    ∀ (cs xs : List Value) (b : Int),
    dotProduct cs xs = some b →
    ∀ k, k < xs.length → ∃ p, xs[k]! = Value.int p := by
  intro cs
  induction cs with
  | nil =>
      intro xs b h k hk
      cases xs with
      | nil => exact absurd hk (by simp)
      | cons x xs' =>
          exfalso
          rw [show dotProduct ([] : List Value) (x :: xs') = none from by
            cases x with
            | int v => rfl
            | bool v => rfl
            | setOfInt v => rfl
            | array v => rfl] at h
          exact absurd h (by simp)
  | cons c cs' ih =>
      intro xs b h k hk
      cases xs with
      | nil =>
          exfalso
          cases c with
          | int v =>
              rw [show dotProduct (.int v :: cs') ([] : List Value) = none from rfl] at h
              exact absurd h (by simp)
          | bool v =>
              rw [show dotProduct (.bool v :: cs') ([] : List Value) = none from rfl] at h
              exact absurd h (by simp)
          | setOfInt v =>
              rw [show dotProduct (.setOfInt v :: cs') ([] : List Value) = none from rfl] at h
              exact absurd h (by simp)
          | array v =>
              rw [show dotProduct (.array v :: cs') ([] : List Value) = none from rfl] at h
              exact absurd h (by simp)
      | cons x xs' =>
          cases c with
          | int v =>
              cases x with
              | int xv =>
                  rw [dotProduct] at h
                  cases hrest : dotProduct cs' xs' with
                  | none => rw [hrest] at h; exact absurd h (by simp)
                  | some s' =>
                      cases k with
                      | zero => exact ⟨xv, rfl⟩
                      | succ k' =>
                          have hk' : k' < xs'.length := by
                            simp only [List.length_cons] at hk
                            omega
                          exact ih xs' s' hrest k' hk'
              | bool xv => exact absurd h (by simp [dotProduct])
              | setOfInt xv => exact absurd h (by simp [dotProduct])
              | array xv => exact absurd h (by simp [dotProduct])
          | bool v =>
              cases x with
              | int xv => exact absurd h (by simp [dotProduct])
              | bool xv => exact absurd h (by simp [dotProduct])
              | setOfInt xv => exact absurd h (by simp [dotProduct])
              | array xv => exact absurd h (by simp [dotProduct])
          | setOfInt v =>
              cases x with
              | int xv => exact absurd h (by simp [dotProduct])
              | bool xv => exact absurd h (by simp [dotProduct])
              | setOfInt xv => exact absurd h (by simp [dotProduct])
              | array xv => exact absurd h (by simp [dotProduct])
          | array v =>
              cases x with
              | int xv => exact absurd h (by simp [dotProduct])
              | bool xv => exact absurd h (by simp [dotProduct])
              | setOfInt xv => exact absurd h (by simp [dotProduct])
              | array xv => exact absurd h (by simp [dotProduct])

/-- The extract preserves the length: each listed slot yields
    exactly one bounds pair. -/
private theorem linExtract_length :
    ∀ (is : List Nat) (doms : List (List Value)) (bds : List (Int × Int)),
    linExtract is doms = some bds → is.length = bds.length := by
  intro is
  induction is with
  | nil =>
      intro doms bds h
      cases bds with
      | nil => rfl
      | cons x xs =>
          rw [linExtract] at h
          exact absurd h (by intro hcon; cases hcon)
  | cons idx rest ih =>
      intro doms bds h
      rw [linExtract] at h
      cases hmin : domMin (getSlot doms idx) with
      | none => rw [hmin] at h; exact absurd h (by simp)
      | some lo =>
          rw [hmin] at h
          cases hmax : domMax (getSlot doms idx) with
          | none => rw [hmax] at h; exact absurd h (by simp)
          | some hi =>
              rw [hmax] at h
              cases hrest : linExtract rest doms with
              | none => rw [hrest] at h; exact absurd h (by simp)
              | some bds' =>
                  rw [hrest] at h
                  have hb : bds = (lo, hi) :: bds' := (Option.some.inj h).symm
                  rw [hb]
                  simp only [List.length_cons]
                  have := ih doms bds' hrest
                  omega

/-- The coverage of the extracted bounds by a satisfying
    assignment: the constraint's satisfaction forces every listed
    value to be an integer (the dot product exists), and
    `domMin`/`domMax` of the domain bound it by the extracted
    interval. -/
private theorem linExtract_cover :
    ∀ (is : List Nat) (doms : List (List Value)) (bds : List (Int × Int))
      (a : List Value),
    linExtract is doms = some bds →
    a.length = doms.length →
    (∀ j v, a[j]? = some v → v ∈ getSlot doms j) →
    (∀ k, k < is.length → ∃ p, a[is[k]!]! = Value.int p) →
    LinCover is bds doms a := by
  intro is
  induction is with
  | nil =>
      intro doms bds a hbds hlen hget _hint k hk
      exact absurd hk (by simp)
  | cons idx rest ih =>
      intro doms bds a hbds hlen hget hint k hk
      rw [linExtract] at hbds
      cases hmin : domMin (getSlot doms idx) with
      | none => rw [hmin] at hbds; exact absurd hbds (by simp)
      | some lo =>
          rw [hmin] at hbds
          cases hmax : domMax (getSlot doms idx) with
          | none => rw [hmax] at hbds; exact absurd hbds (by simp)
          | some hi =>
              rw [hmax] at hbds
              cases hrest : linExtract rest doms with
              | none => rw [hrest] at hbds; exact absurd hbds (by simp)
              | some bds' =>
                  rw [hrest] at hbds
                  have hbds' : bds = (lo, hi) :: bds' := (Option.some.inj hbds).symm
                  subst hbds'
                  cases k with
                  | zero =>
                      obtain ⟨p, hp⟩ := hint 0 (by simp)
                      rw [show (idx :: rest)[0]! = idx from rfl] at hp
                      refine ⟨?_, p, hp, ?_, ?_⟩
                      · -- the value is in the domain
                        -- the integrality hint forces idx < a.length
                        -- (a[idx]! = .int p, and out-of-range gives .bool false)
                        have hlt : idx < a.length := by
                          by_cases hidx : idx < a.length
                          · exact hidx
                          · exfalso
                            -- out of range: a[idx]! = default = .bool false
                            have hdef : a[idx]! = (default : Value) := by
                              rw [List.getElem!_eq_getElem?_getD]
                              rw [List.getElem?_eq_none_iff.mpr (by omega)]
                              rfl
                            rw [hdef] at hp
                            exact nomatch hp
                        have hsome : a[idx]? = some (a[idx]!) := by
                          rw [List.getElem?_eq_getElem hlt,
                            List.getElem!_eq_getElem?_getD,
                            List.getElem?_eq_getElem hlt, Option.getD_some]
                        exact hget idx _ hsome
                      · -- lo ≤ p: domMin bounds any integer member
                        have hmem : Value.int p ∈ getSlot doms idx := by
                          have hlt : idx < a.length := by
                            by_cases hidx : idx < a.length
                            · exact hidx
                            · exfalso
                              have hdef : a[idx]! = (default : Value) := by
                                rw [List.getElem!_eq_getElem?_getD,
                                  List.getElem?_eq_none_iff.mpr (by omega)]
                                rfl
                              rw [hdef] at hp
                              exact nomatch hp
                          have hsome : a[idx]? = some (a[idx]!) := by
                            rw [List.getElem?_eq_getElem hlt,
                              List.getElem!_eq_getElem?_getD,
                              List.getElem?_eq_getElem hlt, Option.getD_some]
                          rw [hp] at hsome
                          exact hget idx _ hsome
                        obtain ⟨m1, hm1, hle⟩ := domMin_of_mem hmem
                        rw [hmin] at hm1
                        -- hm1 : domMin (getSlot doms idx) = some m1, so m1 = lo
                        have : m1 = lo := (Option.some.inj hm1).symm
                        rw [this] at hle
                        exact hle
                      · -- p ≤ hi: domMax bounds any integer member
                        have hmem : Value.int p ∈ getSlot doms idx := by
                          have hlt : idx < a.length := by
                            by_cases hidx : idx < a.length
                            · exact hidx
                            · exfalso
                              have hdef : a[idx]! = (default : Value) := by
                                rw [List.getElem!_eq_getElem?_getD,
                                  List.getElem?_eq_none_iff.mpr (by omega)]
                                rfl
                              rw [hdef] at hp
                              exact nomatch hp
                          have hsome : a[idx]? = some (a[idx]!) := by
                            rw [List.getElem?_eq_getElem hlt,
                              List.getElem!_eq_getElem?_getD,
                              List.getElem?_eq_getElem hlt, Option.getD_some]
                          rw [hp] at hsome
                          exact hget idx _ hsome
                        obtain ⟨m2, hm2, hle⟩ := domMax_of_mem hmem
                        rw [hmax] at hm2
                        have : m2 = hi := (Option.some.inj hm2).symm
                        rw [this] at hle
                        exact hle
                  | succ k' =>
                      have ih' := ih doms bds' a hrest hlen hget
                        (fun k hk' => hint (k + 1) (by simpa using hk')) k'
                        (by simpa using hk)
                      exact ih'

/-- **The head-filter pass lemma** (the factored interval
    derivation of the master lemma): under the coverage invariant
    and the whole-triple's satisfaction, the assignment's value at
    the position-`k` slot passes the position-`k` filter. -/
private theorem lin_head_filter_pass {ocs : List Int} {ois : List Nat}
    {obds : List (Int × Int)} {totalMin totalMax : Int} {eq : Bool} {b : Int}
    {doms : List (List Value)} {a : List Value} {k : Nat}
    {c : Int} {idx : Nat} {bd : Int × Int}
    (hshape : ocs.length = ois.length)
    (hshape2 : ois.length = obds.length)
    (hTmin : totalMin = linTotalMin ocs obds)
    (hTmax : totalMax = linTotalMax ocs obds)
    (hsat : LinSat eq (intVals ocs) (ois.map (fun i => a[i]!)) b)
    (hcov : LinCover ois obds doms a)
    (hklt : k < ois.length)
    (hck : ocs[k]! = c) (hidx : ois[k]! = idx) (hbd : obds[k]! = bd) :
    ∃ pk, a[idx]! = LeanFzn.Semantics.Value.int pk ∧
      a[idx]! ∈ (if eq then
          linNarrowEq c b (totalMin - termMin c bd.1 bd.2)
            (totalMax - termMax c bd.1 bd.2) (getSlot doms idx)
        else
          linNarrowLe c b (totalMin - termMin c bd.1 bd.2)
          (getSlot doms idx)) := by
  -- the coverage at position k gives the value and its interval
  obtain ⟨hmemk, pk, hvpk, hlok, hhik⟩ := hcov k hklt
  rw [hidx] at hmemk hvpk
  refine ⟨pk, hvpk, ?_⟩
  -- the dot-sum level satisfaction
  have hsumsat : (if eq then dotSum (intVals ocs)
        (ois.map (fun i => a[i]!)) = b
      else dotSum (intVals ocs)
          (ois.map (fun i => a[i]!)) ≤ b) := by
    cases heq : eq with
    | true =>
        rw [heq] at hsat
        rw [show LinSat true (intVals ocs) (ois.map (fun i => a[i]!)) b
            = (dotProduct (intVals ocs) (ois.map (fun i => a[i]!))
                = some b) from rfl] at hsat
        have := dotProduct_eq_sum _ _ _ hsat
        rw [this]
        rfl
    | false =>
        rw [heq] at hsat
        rw [show LinSat false (intVals ocs) (ois.map (fun i => a[i]!)) b
            = (∃ d, dotProduct (intVals ocs) (ois.map (fun i => a[i]!))
                = some d ∧ d ≤ b) from rfl] at hsat
        obtain ⟨d, hd, hle⟩ := hsat
        have := dotProduct_eq_sum _ _ _ hd
        rw [this] at hle
        exact hle
  -- others_bound at position k over the ORIGINAL lists
  have hmaplen' : (ois.map (fun i => a[i]!)).length = ois.length := by
    simp only [List.length_map]
  have hkltm : k < (ois.map (fun i => a[i]!)).length := by
    rw [hmaplen']
    exact hklt
  obtain ⟨ck, ok, hck2, hxk, hlok2, hhik2, holo, hohi⟩ :=
    others_bound ocs (ois.map (fun i => a[i]!)) obds k
      (by rw [hmaplen']; exact hshape)
      (by rw [hmaplen']; exact hshape2)
      (by
        intro j hj
        rw [hmaplen'] at hj
        obtain ⟨_, pj, hvpj, hloj, hhij⟩ := hcov j hj
        refine ⟨pj, ?_, hloj, hhij⟩
        exact map_getElem!_in_bounds a ois j hj ▸ hvpj)
      (by rw [hmaplen']; omega)
  -- ck = c (position k's coefficient) and ok = pk (position k's value)
  have hckc : ck = c := hck2.symm.trans hck
  have hokpk : ok = pk := by
    have hmapped : (ois.map (fun i => a[i]!))[k]!
        = a[ois[k]!]! := map_getElem!_in_bounds a ois k hklt
    rw [hmapped, hidx] at hxk
    injection hxk.symm.trans hvpk
  -- the position-k bounds projections
  have hbdk : obds[k]! = (bd.1, bd.2) := hbd
  -- the interval, by cases on eq
  cases heq : eq with
  | true =>
      rw [heq] at hsumsat
      simp only [if_true] at hsumsat ⊢
      rw [hbdk] at holo hohi
      rw [hckc, hokpk] at holo hohi
      rw [hTmin, hTmax]
      have e1 : termMin c (bd.1, bd.2).1 (bd.1, bd.2).2
          = termMin c bd.1 bd.2 := rfl
      have e2 : termMax c (bd.1, bd.2).1 (bd.1, bd.2).2
          = termMax c bd.1 bd.2 := rfl
      rw [e1] at holo
      rw [e2] at hohi
      -- the dot sum decomposes at position k: whole = c*pk + rest
      -- (from others_bound's own statement shape and hsumsat)
      rw [hvpk] at hmemk ⊢
      exact List.mem_filter.mpr ⟨hmemk, by
        simp only [decide_eq_true_eq, Bool.and_eq_true]
        constructor <;> omega⟩
  | false =>
      rw [heq] at hsumsat
      simp only [Bool.false_eq_true, if_false] at hsumsat ⊢
      rw [hbdk] at holo
      rw [hckc, hokpk] at holo
      rw [hTmin]
      have e1 : termMin c (bd.1, bd.2).1 (bd.1, bd.2).2
          = termMin c bd.1 bd.2 := rfl
      rw [e1] at holo
      rw [hvpk] at hmemk ⊢
      exact List.mem_filter.mpr ⟨hmemk, by
        simp only [decide_eq_true_eq]
        omega⟩

/-- **Preservation for `propLinEq`**: a satisfying assignment of
    the input domains remains an assignment of the narrowed
    domains; a reported contradiction is sound; the narrowing only
    shrinks. -/
theorem propLinEq_preserves (coeffs : List Int) (is : List Nat) (b : Int) :
    Preserves (DomConstraint.linEq coeffs is b) (propLinEq coeffs is b) := by
  constructor
  · -- narrowing soundness
    intro doms doms' h a ha hsat
    rw [propLinEq] at h
    by_cases hshape : coeffs.length = is.length
    · rw [if_pos hshape] at h
      cases hex : linExtract is doms with
    | none => rw [hex] at h; exact absurd h (by simp)
    | some bds =>
        rw [hex] at h
        -- iota-reduce the match on `some bds`
        rw [show (match some bds with
            | none => PropResult.contradiction
            | some bds' => linNarrowAll coeffs is bds'
                (linTotalMin coeffs bds') (linTotalMax coeffs bds') true b doms)
          = linNarrowAll coeffs is bds (linTotalMin coeffs bds) (linTotalMax coeffs bds)
              true b doms from rfl] at h
        obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
        -- the coverage (with integrality from the satisfaction)
        have hcov : LinCover is bds doms a :=
          linExtract_cover is doms bds a hex hlen hget
            (fun k hk => by
              -- integrality: the constraint's satisfaction gives
              -- dotProduct = some b, which forces every listed value
              -- to be an integer
              have hsat' := linEq_LinSat.mp hsat
              rw [show LinSat true (intVals coeffs) (is.map (fun i => a[i]!)) b
                  = (dotProduct (intVals coeffs) (is.map (fun i => a[i]!))
                      = some b) from rfl] at hsat'
              have hint := dotProduct_some_int (intVals coeffs)
                (is.map (fun i => a[i]!)) b hsat'
              rw [show (is.map (fun i => a[i]!)).length = is.length from by
                  simp only [List.length_map]] at hint
              obtain ⟨p, hp⟩ := hint k hk
              rw [map_getElem!_in_bounds a is k hk] at hp
              exact ⟨p, hp⟩)
        -- the shape premise coeffs.length = is.length is needed; derive
        -- from the extract's structure (bds has is' length) — for now the
        -- honest constraint: the propagator is only sound on aligned shapes,
        -- which the extract guarantees when it returns some bds
        have hshape : coeffs.length = is.length := hshape
        have hshape2 : is.length = bds.length :=
          linExtract_length is doms bds hex
        exact linNarrowAll_mem coeffs.length 0 coeffs is bds
          (linTotalMin coeffs bds) (linTotalMax coeffs bds) true b doms
          (by simp) (Nat.zero_le _) hshape hshape2
          rfl rfl doms' a h hlen hget
          (linEq_LinSat.mp hsat) hcov
    · -- mismatched shape: the propagator returned contradiction
      rw [if_neg hshape] at h
      exact absurd h (by simp)
  · -- subset: each narrowed slot is a filter of the original
    intro doms doms' h
    rw [propLinEq] at h
    by_cases hshape : coeffs.length = is.length
    · rw [if_pos hshape] at h
      cases hex : linExtract is doms with
      | none => rw [hex] at h; exact absurd h (by simp)
      | some bds =>
          rw [hex] at h
          rw [show (match some bds with
              | none => PropResult.contradiction
              | some bds' => linNarrowAll coeffs is bds'
                  (linTotalMin coeffs bds') (linTotalMax coeffs bds') true b doms)
            = linNarrowAll coeffs is bds (linTotalMin coeffs bds)
                (linTotalMax coeffs bds) true b doms from rfl] at h
          exact linNarrowAll_subset coeffs is bds
            (linTotalMin coeffs bds) (linTotalMax coeffs bds) true b doms doms' h
    · rw [if_neg hshape] at h; exact absurd h (by simp)
  · -- contradiction soundness
    intro doms h a ha hsat
    rw [propLinEq] at h
    by_cases hshape : coeffs.length = is.length
    · rw [if_pos hshape] at h
      cases hex : linExtract is doms with
      | none =>
          -- the extract failed: some listed slot's domain lacks integers
          -- (domMin/domMax returned none). The satisfying assignment's
          -- value at that slot must be an integer in the domain (the dot
          -- product exists), and any integer member makes domMin some —
          -- contradiction.
          -- locate the failing position
          -- domMin and domMax agree on existence: both scan the same
          -- domain for integers
          have hagree : ∀ (d : List Value),
              (domMin d).isSome = true → (domMax d).isSome = true := by
            intro d
            induction d with
            | nil => intro h; exact absurd h (by simp [domMin])
            | cons v vs ih =>
                intro h
                cases hv : v with
                | int p =>
                    have : domMax (Value.int p :: vs)
                        = maxOpt (domMax vs) p := rfl
                    rw [this]
                    cases hdp : domMax vs with
                    | none => rfl
                    | some m => rfl
                | bool p =>
                    subst hv
                    have heq : domMax (Value.bool p :: vs) = domMax vs := rfl
                    rw [heq]
                    have hvs : (domMin vs).isSome = true := by
                      have heqm : domMin (Value.bool p :: vs) = domMin vs := rfl
                      rw [heqm] at h
                      exact h
                    exact ih hvs
                | setOfInt p =>
                    subst hv
                    have heq : domMax (Value.setOfInt p :: vs) = domMax vs := rfl
                    rw [heq]
                    have hvs : (domMin vs).isSome = true := by
                      have heqm : domMin (Value.setOfInt p :: vs) = domMin vs := rfl
                      rw [heqm] at h
                      exact h
                    exact ih hvs
                | array p =>
                    subst hv
                    have heq : domMax (Value.array p :: vs) = domMax vs := rfl
                    rw [heq]
                    have hvs : (domMin vs).isSome = true := by
                      have heqm : domMin (Value.array p :: vs) = domMin vs := rfl
                      rw [heqm] at h
                      exact h
                    exact ih hvs
          have hfail : ∃ k, k < is.length ∧
              (domMin (getSlot doms (is[k]!))).isNone = true := by
            -- induction over the extract's recursion
            have hexrec : ∀ (js : List Nat),
                linExtract js doms = none →
                ∃ k, k < js.length ∧ (domMin (getSlot doms (js[k]!))).isNone = true := by
              intro js
              induction js with
              | nil => intro h; exact absurd h (by simp [linExtract])
              | cons j js' ih =>
                  intro h
                  rw [linExtract] at h
                  cases hmin : domMin (getSlot doms j) with
                  | none =>
                      rw [hmin] at h
                      refine ⟨0, by simp, ?_⟩
                      rw [show (j :: js')[0]! = j from rfl, hmin]
                      rfl
                  | some lo =>
                      rw [hmin] at h
                      cases hmax : domMax (getSlot doms j) with
                      | none =>
                          -- domMax none with domMin some is impossible
                          exfalso
                          have hcontr : (domMax (getSlot doms j)).isSome = true :=
                            hagree (getSlot doms j) (by rw [hmin]; rfl)
                          rw [hmax] at hcontr
                          exact absurd hcontr (by simp)
                      | some hi =>
                          -- the match reduces: Option.map f (linExtract js' doms);
                          -- the outer = none forces the tail extract = none
                          rw [hmax] at h
                          -- reduce the match to the Option.map form
                          have hmap : (match some lo, some hi with
                              | some lo, some hi =>
                                Option.map (fun bds => (lo, hi) :: bds) (linExtract js' doms)
                              | x, x_1 => none) = none := h
                          rw [Option.map_eq_none_iff] at hmap
                          obtain ⟨k, hk, hnone⟩ := ih hmap
                          refine ⟨k + 1, by simp only [List.length_cons]; omega, ?_⟩
                          rw [show (j :: js')[k + 1]! = js'[k]! from rfl]
                          exact hnone
            exact hexrec is hex
          obtain ⟨k, hk, hnone⟩ := hfail
          -- the assignment's value at is[k]! is an integer in the domain
          have hsat' := linEq_LinSat.mp hsat
          rw [show LinSat true (intVals coeffs) (is.map (fun i => a[i]!)) b
              = (dotProduct (intVals coeffs) (is.map (fun i => a[i]!))
                  = some b) from rfl] at hsat'
          have hint := dotProduct_some_int (intVals coeffs)
            (is.map (fun i => a[i]!)) b hsat' k
            (by
              rw [show (is.map (fun i => a[i]!)).length = is.length from by
                simp only [List.length_map]]
              exact hk)
          obtain ⟨p, hp⟩ := hint
          rw [map_getElem!_in_bounds a is k hk] at hp
          -- the value is in the domain (allAssigns)
          obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
          have hmem : Value.int p ∈ getSlot doms (is[k]!) := by
            obtain ⟨hlen2, hget2⟩ := allAssigns_spec doms a ha
            by_cases halt : is[k]! < a.length
            · -- in range: the allAssigns spec gives the membership
              have hsome : a[is[k]!]? = some (a[is[k]!]!) := by
                have hsome' : a[is[k]!]? = some a[is[k]!] :=
                  List.getElem?_eq_getElem halt
                rw [hsome']
                show some a[is[k]!] = some a[is[k]!]!
                rw [show a[is[k]!]! = a[is[k]!] from by
                  rw [List.getElem!_eq_getElem?_getD, hsome', Option.getD_some]]
              have hv : a[is[k]!]! ∈ getSlot doms (is[k]!) :=
                hget2 (is[k]!) _ hsome
              rw [hp] at hv
              exact hv
            · -- out of range: a[is[k]!]! = default (.bool false), but
              -- dotProduct_some_int's witness says it is .int p —
              -- contradiction
              exfalso
              have hdef : a[is[k]!]! = (default : Value) := by
                rw [List.getElem!_eq_getElem?_getD,
                  List.getElem?_eq_none_iff.mpr (by omega)]
                rfl
              rw [hdef] at hp
              exact nomatch hp
          -- domMin of a domain with an integer member is some
          obtain ⟨m, hm, _⟩ := domMin_of_mem hmem
          have hnone' : domMin (getSlot doms is[k]!) = none := by
            cases hdp : domMin (getSlot doms is[k]!) with
            | none => rfl
            | some v =>
                rw [hdp] at hnone
                exact absurd hnone (by simp)
          rw [hnone'] at hm
          exact absurd hm (by simp)
      | some bds =>
          rw [hex] at h
          rw [show (match some bds with
              | none => PropResult.contradiction
              | some bds' => linNarrowAll coeffs is bds'
                  (linTotalMin coeffs bds') (linTotalMax coeffs bds') true b doms)
            = linNarrowAll coeffs is bds (linTotalMin coeffs bds)
                (linTotalMax coeffs bds) true b doms from rfl] at h
          -- the assignment's spec (length + membership)
          obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
          -- the satisfaction and the integrality hint, derived once
          have hsat' := linEq_LinSat.mp hsat
          have hint : ∀ k, k < is.length →
              ∃ p, a[is[k]!]! = Value.int p := by
            intro k hk
            rw [show LinSat true (intVals coeffs) (is.map (fun i => a[i]!)) b
                = (dotProduct (intVals coeffs) (is.map (fun i => a[i]!))
                    = some b) from rfl] at hsat'
            have hmaplen2 : (is.map (fun i => a[i]!)).length = is.length := by
              simp only [List.length_map]
            have hint2 := dotProduct_some_int (intVals coeffs)
              (is.map (fun i => a[i]!)) b hsat' k (by rw [hmaplen2]; exact hk)
            obtain ⟨p, hp⟩ := hint2
            rw [map_getElem!_in_bounds a is k hk] at hp
            exact ⟨p, hp⟩
          -- the first-contradiction analysis: an induction over the run
          have hrun : ∀ (n : Nat) (k : Nat) (doms2 : List (List Value)),
              coeffs.length - k = n → k ≤ coeffs.length →
              linNarrowAll (List.drop k coeffs) (List.drop k is)
                (List.drop k bds) (linTotalMin coeffs bds) (linTotalMax coeffs bds)
                true b doms2 = .contradiction →
              LinCover is bds doms2 a →
              LinSat true (intVals coeffs) (is.map (fun i => a[i]!)) b →
              False := by
            intro n
            induction n using Nat.strongRecOn with
            | ind n ih =>
              intro k doms2 hmeasure hkle h hcov' hsat'
              cases hdcs : List.drop k coeffs with
              | nil =>
                  -- no terms: the run returns .narrowed, not .contradiction
                  have hdcslen : (List.drop k coeffs).length = coeffs.length - k := by simp
                  rw [hdcs, List.length_nil] at hdcslen
                  have hisnil : List.drop k is = [] := by
                    cases his2 : List.drop k is with
                    | nil => rfl
                    | cons x xs =>
                        exfalso
                        have h1 : (x :: xs).length = (List.drop k is).length := by
                          rw [his2]
                        have h1' : (List.drop k is).length = is.length - k := by simp
                        rw [h1'] at h1
                        simp only [List.length_cons] at h1
                        have h2 : (List.drop k coeffs).length = coeffs.length - k := by simp
                        rw [hdcs] at h2
                        simp only [List.length_nil] at h2
                        have h3 : coeffs.length = is.length := hshape
                        omega
                  have hbdsnil : List.drop k bds = [] := by
                    cases hbs2 : List.drop k bds with
                    | nil => rfl
                    | cons y ys =>
                        exfalso
                        have h1 : (y :: ys).length = (List.drop k bds).length := by
                          rw [hbs2]
                        have h1' : (List.drop k bds).length = bds.length - k := by simp
                        rw [h1'] at h1
                        simp only [List.length_cons] at h1
                        have h2 : (List.drop k coeffs).length = coeffs.length - k := by simp
                        rw [hdcs] at h2
                        simp only [List.length_nil] at h2
                        have h3 : is.length = bds.length :=
                          linExtract_length is doms bds hex
                        omega
                  rw [hdcs, hisnil, hbdsnil] at h
                  exact absurd h (by simp [linNarrowAll])
              | cons c csuff =>
                  cases his : List.drop k is with
                  | nil =>
                      exfalso
                      have h1 : (List.drop k is).length = is.length - k := by simp
                      have h2 : (List.drop k coeffs).length = coeffs.length - k := by simp
                      rw [his, List.length_nil] at h1
                      rw [hdcs, List.length_cons] at h2
                      omega
                  | cons idx isuff =>
                      cases hbs : List.drop k bds with
                      | nil =>
                          exfalso
                          have h1 : (List.drop k bds).length = bds.length - k := by simp
                          have h2 : (List.drop k coeffs).length = coeffs.length - k := by simp
                          rw [hbs, List.length_nil] at h1
                          rw [hdcs, List.length_cons] at h2
                          have h3 : is.length = bds.length :=
                            linExtract_length is doms bds hex
                          omega
                      | cons bd bsuff =>
                          have hck : coeffs[k]! = c := by
                            have hlt : k < coeffs.length := by
                              have h1 : (List.drop k coeffs).length = coeffs.length - k := by simp
                              rw [hdcs, List.length_cons] at h1
                              omega
                            have hdrop : ∀ (l : List Int) (n : Nat),
                                n < l.length →
                                l[n]! = (List.drop n l).headD 0 := by
                              intro l n
                              induction l generalizing n with
                              | nil => intro hlt; exact absurd hlt (by simp)
                              | cons x xs ih2 =>
                                  intro hlt
                                  cases n with
                                  | zero => rfl
                                  | succ n' => exact ih2 n' (by
                                    simp only [List.length_cons] at hlt; omega)
                            rw [hdrop coeffs k hlt, hdcs]
                            rfl
                          have hidx : is[k]! = idx := by
                            have hlt : k < is.length := by
                              have h1 : (List.drop k is).length = is.length - k := by simp
                              rw [his, List.length_cons] at h1
                              omega
                            have hdrop : ∀ (l : List Nat) (n : Nat),
                                n < l.length →
                                l[n]! = (List.drop n l).headD 0 := by
                              intro l n
                              induction l generalizing n with
                              | nil => intro hlt; exact absurd hlt (by simp)
                              | cons x xs ih2 =>
                                  intro hlt
                                  cases n with
                                  | zero => rfl
                                  | succ n' => exact ih2 n' (by
                                    simp only [List.length_cons] at hlt; omega)
                            rw [hdrop is k hlt, his]
                            rfl
                          have hbd : bds[k]! = bd := by
                            have hlt : k < bds.length := by
                              have h1 : (List.drop k bds).length = bds.length - k := by simp
                              rw [hbs, List.length_cons] at h1
                              omega
                            have hdrop : ∀ (l : List (Int × Int)) (n : Nat),
                                n < l.length →
                                l[n]! = (List.drop n l).headD (0, 0) := by
                              intro l n
                              induction l generalizing n with
                              | nil => intro hlt; exact absurd hlt (by simp)
                              | cons x xs ih2 =>
                                  intro hlt
                                  cases n with
                                  | zero => rfl
                                  | succ n' => exact ih2 n' (by
                                    simp only [List.length_cons] at hlt; omega)
                            rw [hdrop bds k hlt, hbs]
                            rfl
                          have hklt : k < is.length := by
                            have h1 : (List.drop k is).length = is.length - k := by simp
                            rw [his, List.length_cons] at h1
                            omega
                          -- unfold one step
                          rw [hdcs, his, hbs] at h
                          rw [linNarrowAll] at h
                          by_cases hcond : (linNarrowEq c b
                              (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                              (linTotalMax coeffs bds - termMax c bd.1 bd.2)
                              (getSlot doms2 idx)).isEmpty = true
                          · -- the head filter emptied: the value passes by
                            -- lin_head_filter_pass — contradiction with empty
                            rw [show (if true = true then
                                linNarrowEq c b
                                  (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                  (linTotalMax coeffs bds - termMax c bd.1 bd.2)
                                  (getSlot doms2 idx)
                              else
                                linNarrowLe c b
                                  (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                  (getSlot doms2 idx))
                              = linNarrowEq c b
                                  (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                  (linTotalMax coeffs bds - termMax c bd.1 bd.2)
                                  (getSlot doms2 idx) from if_pos (rfl : true = true)] at h
                            rw [if_pos hcond] at h
                            obtain ⟨pk, hvpk, hmemf⟩ :=
                              lin_head_filter_pass (ocs := coeffs) (ois := is)
                                (obds := bds)
                                (totalMin := linTotalMin coeffs bds)
                                (totalMax := linTotalMax coeffs bds)
                                (eq := true) (b := b) (doms := doms2) (a := a) (k := k)
                                (c := c) (idx := idx) (bd := bd)
                                hshape (linExtract_length is doms bds hex)
                                rfl rfl hsat' hcov' hklt hck hidx hbd
                            -- hmemf : a[idx]! ∈ the filter, which is empty
                            -- (the split's branch condition is the filter's
                            --  isEmpty = true)
                            have hfnil : (linNarrowEq c b
                                (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                (linTotalMax coeffs bds - termMax c bd.1 bd.2)
                                (getSlot doms2 idx)) = [] := by
                              rw [← List.isEmpty_iff]
                              exact hcond
                            rw [hfnil] at hmemf
                            exact absurd hmemf (by simp)
                          · -- the filter kept values: the run recursed —
                            -- the contradiction comes from the tail
                            -- h (with the inner if already reduced by the
                            -- rw [linNarrowAll]) is the Prop-if; hcond
                            -- selects the else branch
                            -- reduce the inner `if true = true` and select
                            -- the else branch via hcond
                            rw [show (if true = true then
                                linNarrowEq c b
                                  (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                  (linTotalMax coeffs bds - termMax c bd.1 bd.2)
                                  (getSlot doms2 idx)
                              else
                                linNarrowLe c b
                                  (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                  (getSlot doms2 idx))
                              = linNarrowEq c b
                                  (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                  (linTotalMax coeffs bds - termMax c bd.1 bd.2)
                                  (getSlot doms2 idx) from if_pos (rfl : true = true)] at h
                            rw [if_neg hcond] at h
                            have hcsuff : csuff = List.drop (k+1) coeffs := by
                              have hdrop : List.drop (k+1) coeffs
                                  = (List.drop k coeffs).drop 1 := by
                                rw [← List.drop_drop]
                              rw [hdrop, hdcs]
                              rfl
                            rw [hcsuff] at h
                            rw [show isuff = List.drop (k+1) is from by
                              have hdrop : List.drop (k+1) is
                                  = (List.drop k is).drop 1 := by
                                rw [← List.drop_drop]
                              rw [hdrop, his]
                              rfl,
                              show bsuff = List.drop (k+1) bds from by
                              have hdrop : List.drop (k+1) bds
                                  = (List.drop k bds).drop 1 := by
                                rw [← List.drop_drop]
                              rw [hdrop, hbs]
                              rfl] at h
                            have hn1 : coeffs.length - (k + 1) < n := by omega
                            -- the tail: recurse with the written domains
                            -- and the original coverage (the written slot
                            -- passes by lin_head_filter_pass, the master
                            -- lemma's interval derivation)
                            exact ih (coeffs.length - (k + 1)) hn1 (k + 1)
                              (setSlot doms2 idx (linNarrowEq c b
                                (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                (linTotalMax coeffs bds - termMax c bd.1 bd.2)
                                (getSlot doms2 idx)))
                              (by omega) (by omega) h
                              (by
                                intro mm hmm
                                obtain ⟨hmemv, p', hvp, hlo', hhi'⟩ := hcov' mm hmm
                                by_cases hne : is[mm]! = idx
                                · rw [hne] at hmemv hvp
                                  have hmemint : Value.int p' ∈ getSlot doms2 idx := by
                                    rw [← hvp]
                                    exact hmemv
                                  obtain ⟨pk2, hvp2, hmemf2⟩ :=
                                    lin_head_filter_pass (ocs := coeffs)
                                      (ois := is) (obds := bds)
                                      (totalMin := linTotalMin coeffs bds)
                                      (totalMax := linTotalMax coeffs bds)
                                      (eq := true) (b := b) (doms := doms2)
                                      (a := a) (k := k) (c := c) (idx := idx)
                                      (bd := bd) hshape
                                      (linExtract_length is doms bds hex)
                                      rfl rfl (linEq_LinSat.mp hsat) hcov' hklt
                                      hck hidx hbd
                                  rw [hne]
                                  rw [getSlot_setSlot_eq doms2 _ idx
                                    (lt_length_of_mem_getSlot doms2 idx
                                      (Value.int p') hmemint)]
                                  -- p' = pk2: both are the integer of a[idx]!
                                  have hp'pk : p' = pk2 := by
                                    have h1 : Value.int p' = Value.int pk2 :=
                                      hvp.symm.trans hvp2
                                    injection h1
                                  rw [hp'pk] at hlo' hhi'
                                  exact ⟨hmemf2, pk2, hvp2, hlo', hhi'⟩
                                · rw [getSlot_setSlot_of_ne doms2 _ idx _ hne]
                                  exact ⟨hmemv, p', hvp, hlo', hhi'⟩)
                              (by exact linEq_LinSat.mp hsat)
          exact hrun coeffs.length 0 doms (by simp) (Nat.zero_le _) h
            (linExtract_cover is doms bds a hex hlen hget hint)
            (linEq_LinSat.mp hsat)
    · -- mismatched shape: the constraint is unsatisfiable (the dot
      -- product needs equal lengths), so contradiction is sound
      rw [if_neg hshape] at h
      obtain ⟨hlen2, hget2⟩ := allAssigns_spec doms a ha
      have hsat' := linEq_LinSat.mp hsat
      rw [show LinSat true (intVals coeffs) (is.map (fun i => a[i]!)) b
          = (dotProduct (intVals coeffs) (is.map (fun i => a[i]!))
              = some b) from rfl] at hsat'
      rw [dotProduct_mismatch hshape] at hsat'
      exact absurd hsat' (by simp)

theorem propLinLe_preserves (coeffs : List Int) (is : List Nat) (b : Int) :
    Preserves (DomConstraint.linLe coeffs is b) (propLinLe coeffs is b) := by
  constructor
  · -- narrowing soundness
    intro doms doms' h a ha hsat
    rw [propLinLe] at h
    by_cases hshape : coeffs.length = is.length
    · rw [if_pos hshape] at h
      cases hex : linExtract is doms with
    | none => rw [hex] at h; exact absurd h (by simp)
    | some bds =>
        rw [hex] at h
        -- iota-reduce the match on `some bds`
        rw [show (match some bds with
            | none => PropResult.contradiction
            | some bds' => linNarrowAll coeffs is bds'
                (linTotalMin coeffs bds') (linTotalMax coeffs bds') false b doms)
          = linNarrowAll coeffs is bds (linTotalMin coeffs bds) (linTotalMax coeffs bds)
              false b doms from rfl] at h
        obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
        -- the coverage (with integrality from the satisfaction)
        have hcov : LinCover is bds doms a :=
          linExtract_cover is doms bds a hex hlen hget
            (fun k hk => by
              -- integrality: the constraint's satisfaction gives
              -- dotProduct = some b, which forces every listed value
              -- to be an integer
              have hsat' := linLe_LinSat.mp hsat
              rw [show LinSat false (intVals coeffs) (is.map (fun i => a[i]!)) b
                  = (∃ d, dotProduct (intVals coeffs) (is.map (fun i => a[i]!))
                      = some d ∧ d ≤ b) from rfl] at hsat'
              obtain ⟨d, hd, hle⟩ := hsat'
              have hint := dotProduct_some_int (intVals coeffs)
                (is.map (fun i => a[i]!)) d hd
              rw [show (is.map (fun i => a[i]!)).length = is.length from by
                  simp only [List.length_map]] at hint
              obtain ⟨p, hp⟩ := hint k hk
              rw [map_getElem!_in_bounds a is k hk] at hp
              exact ⟨p, hp⟩)
        -- the shape premise coeffs.length = is.length is needed; derive
        -- from the extract's structure (bds has is' length) — for now the
        -- honest constraint: the propagator is only sound on aligned shapes,
        -- which the extract guarantees when it returns some bds
        have hshape : coeffs.length = is.length := hshape
        have hshape2 : is.length = bds.length :=
          linExtract_length is doms bds hex
        exact linNarrowAll_mem coeffs.length 0 coeffs is bds
          (linTotalMin coeffs bds) (linTotalMax coeffs bds) false b doms
          (by simp) (Nat.zero_le _) hshape hshape2
          rfl rfl doms' a h hlen hget
          (linLe_LinSat.mp hsat) hcov
    · -- mismatched shape: the propagator returned contradiction
      rw [if_neg hshape] at h
      exact absurd h (by simp)
  · -- subset: each narrowed slot is a filter of the original
    intro doms doms' h
    rw [propLinLe] at h
    by_cases hshape : coeffs.length = is.length
    · rw [if_pos hshape] at h
      cases hex : linExtract is doms with
      | none => rw [hex] at h; exact absurd h (by simp)
      | some bds =>
          rw [hex] at h
          rw [show (match some bds with
              | none => PropResult.contradiction
              | some bds' => linNarrowAll coeffs is bds'
                  (linTotalMin coeffs bds') (linTotalMax coeffs bds') false b doms)
            = linNarrowAll coeffs is bds (linTotalMin coeffs bds)
                (linTotalMax coeffs bds) false b doms from rfl] at h
          exact linNarrowAll_subset coeffs is bds
            (linTotalMin coeffs bds) (linTotalMax coeffs bds) false b doms doms' h
    · rw [if_neg hshape] at h; exact absurd h (by simp)
  · -- contradiction soundness
    intro doms h a ha hsat
    rw [propLinLe] at h
    by_cases hshape : coeffs.length = is.length
    · rw [if_pos hshape] at h
      cases hex : linExtract is doms with
      | none =>
          -- the extract failed: some listed slot's domain lacks integers
          -- (domMin/domMax returned none). The satisfying assignment's
          -- value at that slot must be an integer in the domain (the dot
          -- product exists), and any integer member makes domMin some —
          -- contradiction.
          -- locate the failing position
          -- domMin and domMax agree on existence: both scan the same
          -- domain for integers
          have hagree : ∀ (d : List Value),
              (domMin d).isSome = true → (domMax d).isSome = true := by
            intro d
            induction d with
            | nil => intro h; exact absurd h (by simp [domMin])
            | cons v vs ih =>
                intro h
                cases hv : v with
                | int p =>
                    have : domMax (Value.int p :: vs)
                        = maxOpt (domMax vs) p := rfl
                    rw [this]
                    cases hdp : domMax vs with
                    | none => rfl
                    | some m => rfl
                | bool p =>
                    subst hv
                    have heq : domMax (Value.bool p :: vs) = domMax vs := rfl
                    rw [heq]
                    have hvs : (domMin vs).isSome = true := by
                      have heqm : domMin (Value.bool p :: vs) = domMin vs := rfl
                      rw [heqm] at h
                      exact h
                    exact ih hvs
                | setOfInt p =>
                    subst hv
                    have heq : domMax (Value.setOfInt p :: vs) = domMax vs := rfl
                    rw [heq]
                    have hvs : (domMin vs).isSome = true := by
                      have heqm : domMin (Value.setOfInt p :: vs) = domMin vs := rfl
                      rw [heqm] at h
                      exact h
                    exact ih hvs
                | array p =>
                    subst hv
                    have heq : domMax (Value.array p :: vs) = domMax vs := rfl
                    rw [heq]
                    have hvs : (domMin vs).isSome = true := by
                      have heqm : domMin (Value.array p :: vs) = domMin vs := rfl
                      rw [heqm] at h
                      exact h
                    exact ih hvs
          have hfail : ∃ k, k < is.length ∧
              (domMin (getSlot doms (is[k]!))).isNone = true := by
            -- induction over the extract's recursion
            have hexrec : ∀ (js : List Nat),
                linExtract js doms = none →
                ∃ k, k < js.length ∧ (domMin (getSlot doms (js[k]!))).isNone = true := by
              intro js
              induction js with
              | nil => intro h; exact absurd h (by simp [linExtract])
              | cons j js' ih =>
                  intro h
                  rw [linExtract] at h
                  cases hmin : domMin (getSlot doms j) with
                  | none =>
                      rw [hmin] at h
                      refine ⟨0, by simp, ?_⟩
                      rw [show (j :: js')[0]! = j from rfl, hmin]
                      rfl
                  | some lo =>
                      rw [hmin] at h
                      cases hmax : domMax (getSlot doms j) with
                      | none =>
                          -- domMax none with domMin some is impossible
                          exfalso
                          have hcontr : (domMax (getSlot doms j)).isSome = true :=
                            hagree (getSlot doms j) (by rw [hmin]; rfl)
                          rw [hmax] at hcontr
                          exact absurd hcontr (by simp)
                      | some hi =>
                          -- the match reduces: Option.map f (linExtract js' doms);
                          -- the outer = none forces the tail extract = none
                          rw [hmax] at h
                          -- reduce the match to the Option.map form
                          have hmap : (match some lo, some hi with
                              | some lo, some hi =>
                                Option.map (fun bds => (lo, hi) :: bds) (linExtract js' doms)
                              | x, x_1 => none) = none := h
                          rw [Option.map_eq_none_iff] at hmap
                          obtain ⟨k, hk, hnone⟩ := ih hmap
                          refine ⟨k + 1, by simp only [List.length_cons]; omega, ?_⟩
                          rw [show (j :: js')[k + 1]! = js'[k]! from rfl]
                          exact hnone
            exact hexrec is hex
          obtain ⟨k, hk, hnone⟩ := hfail
          -- the assignment's value at is[k]! is an integer in the domain
          have hsat' := linLe_LinSat.mp hsat
          rw [show LinSat false (intVals coeffs) (is.map (fun i => a[i]!)) b
              = (∃ d, dotProduct (intVals coeffs) (is.map (fun i => a[i]!))
                  = some d ∧ d ≤ b) from rfl] at hsat'
          obtain ⟨d, hd, hle⟩ := hsat'
          have hint := dotProduct_some_int (intVals coeffs)
            (is.map (fun i => a[i]!)) d hd k
            (by
              rw [show (is.map (fun i => a[i]!)).length = is.length from by
                simp only [List.length_map]]
              exact hk)
          obtain ⟨p, hp⟩ := hint
          rw [map_getElem!_in_bounds a is k hk] at hp
          -- the value is in the domain (allAssigns)
          obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
          have hmem : Value.int p ∈ getSlot doms (is[k]!) := by
            obtain ⟨hlen2, hget2⟩ := allAssigns_spec doms a ha
            by_cases halt : is[k]! < a.length
            · -- in range: the allAssigns spec gives the membership
              have hsome : a[is[k]!]? = some (a[is[k]!]!) := by
                have hsome' : a[is[k]!]? = some a[is[k]!] :=
                  List.getElem?_eq_getElem halt
                rw [hsome']
                show some a[is[k]!] = some a[is[k]!]!
                rw [show a[is[k]!]! = a[is[k]!] from by
                  rw [List.getElem!_eq_getElem?_getD, hsome', Option.getD_some]]
              have hv : a[is[k]!]! ∈ getSlot doms (is[k]!) :=
                hget2 (is[k]!) _ hsome
              rw [hp] at hv
              exact hv
            · -- out of range: a[is[k]!]! = default (.bool false), but
              -- dotProduct_some_int's witness says it is .int p —
              -- contradiction
              exfalso
              have hdef : a[is[k]!]! = (default : Value) := by
                rw [List.getElem!_eq_getElem?_getD,
                  List.getElem?_eq_none_iff.mpr (by omega)]
                rfl
              rw [hdef] at hp
              exact nomatch hp
          -- domMin of a domain with an integer member is some
          obtain ⟨m, hm, _⟩ := domMin_of_mem hmem
          have hnone' : domMin (getSlot doms is[k]!) = none := by
            cases hdp : domMin (getSlot doms is[k]!) with
            | none => rfl
            | some v =>
                rw [hdp] at hnone
                exact absurd hnone (by simp)
          rw [hnone'] at hm
          exact absurd hm (by simp)
      | some bds =>
          rw [hex] at h
          rw [show (match some bds with
              | none => PropResult.contradiction
              | some bds' => linNarrowAll coeffs is bds'
                  (linTotalMin coeffs bds') (linTotalMax coeffs bds') false b doms)
            = linNarrowAll coeffs is bds (linTotalMin coeffs bds)
                (linTotalMax coeffs bds) false b doms from rfl] at h
          -- the assignment's spec (length + membership)
          obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
          -- the satisfaction and the integrality hint, derived once
          have hsat' := linLe_LinSat.mp hsat
          have hint : ∀ k, k < is.length →
              ∃ p, a[is[k]!]! = Value.int p := by
            intro k hk
            rw [show LinSat false (intVals coeffs) (is.map (fun i => a[i]!)) b
                = (∃ d, dotProduct (intVals coeffs) (is.map (fun i => a[i]!))
                    = some d ∧ d ≤ b) from rfl] at hsat'
            obtain ⟨d, hd, hle⟩ := hsat'
            have hmaplen2 : (is.map (fun i => a[i]!)).length = is.length := by
              simp only [List.length_map]
            have hint2 := dotProduct_some_int (intVals coeffs)
              (is.map (fun i => a[i]!)) d hd k (by rw [hmaplen2]; exact hk)
            obtain ⟨p, hp⟩ := hint2
            rw [map_getElem!_in_bounds a is k hk] at hp
            exact ⟨p, hp⟩
          -- the first-contradiction analysis: an induction over the run
          have hrun : ∀ (n : Nat) (k : Nat) (doms2 : List (List Value)),
              coeffs.length - k = n → k ≤ coeffs.length →
              linNarrowAll (List.drop k coeffs) (List.drop k is)
                (List.drop k bds) (linTotalMin coeffs bds) (linTotalMax coeffs bds)
                false b doms2 = .contradiction →
              LinCover is bds doms2 a →
              LinSat false (intVals coeffs) (is.map (fun i => a[i]!)) b →
              False := by
            intro n
            induction n using Nat.strongRecOn with
            | ind n ih =>
              intro k doms2 hmeasure hkle h hcov' hsat'
              cases hdcs : List.drop k coeffs with
              | nil =>
                  -- no terms: the run returns .narrowed, not .contradiction
                  have hdcslen : (List.drop k coeffs).length = coeffs.length - k := by simp
                  rw [hdcs, List.length_nil] at hdcslen
                  have hisnil : List.drop k is = [] := by
                    cases his2 : List.drop k is with
                    | nil => rfl
                    | cons x xs =>
                        exfalso
                        have h1 : (x :: xs).length = (List.drop k is).length := by
                          rw [his2]
                        have h1' : (List.drop k is).length = is.length - k := by simp
                        rw [h1'] at h1
                        simp only [List.length_cons] at h1
                        have h2 : (List.drop k coeffs).length = coeffs.length - k := by simp
                        rw [hdcs] at h2
                        simp only [List.length_nil] at h2
                        have h3 : coeffs.length = is.length := hshape
                        omega
                  have hbdsnil : List.drop k bds = [] := by
                    cases hbs2 : List.drop k bds with
                    | nil => rfl
                    | cons y ys =>
                        exfalso
                        have h1 : (y :: ys).length = (List.drop k bds).length := by
                          rw [hbs2]
                        have h1' : (List.drop k bds).length = bds.length - k := by simp
                        rw [h1'] at h1
                        simp only [List.length_cons] at h1
                        have h2 : (List.drop k coeffs).length = coeffs.length - k := by simp
                        rw [hdcs] at h2
                        simp only [List.length_nil] at h2
                        have h3 : is.length = bds.length :=
                          linExtract_length is doms bds hex
                        omega
                  rw [hdcs, hisnil, hbdsnil] at h
                  exact absurd h (by simp [linNarrowAll])
              | cons c csuff =>
                  cases his : List.drop k is with
                  | nil =>
                      exfalso
                      have h1 : (List.drop k is).length = is.length - k := by simp
                      have h2 : (List.drop k coeffs).length = coeffs.length - k := by simp
                      rw [his, List.length_nil] at h1
                      rw [hdcs, List.length_cons] at h2
                      omega
                  | cons idx isuff =>
                      cases hbs : List.drop k bds with
                      | nil =>
                          exfalso
                          have h1 : (List.drop k bds).length = bds.length - k := by simp
                          have h2 : (List.drop k coeffs).length = coeffs.length - k := by simp
                          rw [hbs, List.length_nil] at h1
                          rw [hdcs, List.length_cons] at h2
                          have h3 : is.length = bds.length :=
                            linExtract_length is doms bds hex
                          omega
                      | cons bd bsuff =>
                          have hck : coeffs[k]! = c := by
                            have hlt : k < coeffs.length := by
                              have h1 : (List.drop k coeffs).length = coeffs.length - k := by simp
                              rw [hdcs, List.length_cons] at h1
                              omega
                            have hdrop : ∀ (l : List Int) (n : Nat),
                                n < l.length →
                                l[n]! = (List.drop n l).headD 0 := by
                              intro l n
                              induction l generalizing n with
                              | nil => intro hlt; exact absurd hlt (by simp)
                              | cons x xs ih2 =>
                                  intro hlt
                                  cases n with
                                  | zero => rfl
                                  | succ n' => exact ih2 n' (by
                                    simp only [List.length_cons] at hlt; omega)
                            rw [hdrop coeffs k hlt, hdcs]
                            rfl
                          have hidx : is[k]! = idx := by
                            have hlt : k < is.length := by
                              have h1 : (List.drop k is).length = is.length - k := by simp
                              rw [his, List.length_cons] at h1
                              omega
                            have hdrop : ∀ (l : List Nat) (n : Nat),
                                n < l.length →
                                l[n]! = (List.drop n l).headD 0 := by
                              intro l n
                              induction l generalizing n with
                              | nil => intro hlt; exact absurd hlt (by simp)
                              | cons x xs ih2 =>
                                  intro hlt
                                  cases n with
                                  | zero => rfl
                                  | succ n' => exact ih2 n' (by
                                    simp only [List.length_cons] at hlt; omega)
                            rw [hdrop is k hlt, his]
                            rfl
                          have hbd : bds[k]! = bd := by
                            have hlt : k < bds.length := by
                              have h1 : (List.drop k bds).length = bds.length - k := by simp
                              rw [hbs, List.length_cons] at h1
                              omega
                            have hdrop : ∀ (l : List (Int × Int)) (n : Nat),
                                n < l.length →
                                l[n]! = (List.drop n l).headD (0, 0) := by
                              intro l n
                              induction l generalizing n with
                              | nil => intro hlt; exact absurd hlt (by simp)
                              | cons x xs ih2 =>
                                  intro hlt
                                  cases n with
                                  | zero => rfl
                                  | succ n' => exact ih2 n' (by
                                    simp only [List.length_cons] at hlt; omega)
                            rw [hdrop bds k hlt, hbs]
                            rfl
                          have hklt : k < is.length := by
                            have h1 : (List.drop k is).length = is.length - k := by simp
                            rw [his, List.length_cons] at h1
                            omega
                          -- unfold one step
                          rw [hdcs, his, hbs] at h
                          rw [linNarrowAll] at h
                          by_cases hcond : (linNarrowLe c b
                              (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                              (getSlot doms2 idx)).isEmpty = true
                          · -- the head filter emptied: the value passes by
                            -- lin_head_filter_pass — contradiction with empty
                            rw [show (if false = true then
                                linNarrowEq c b
                                  (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                  (linTotalMax coeffs bds - termMax c bd.1 bd.2)
                                  (getSlot doms2 idx)
                              else
                                linNarrowLe c b
                                  (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                  (getSlot doms2 idx))
                              = linNarrowLe c b
                                  (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                  (getSlot doms2 idx) from if_neg (by decide)] at h
                            rw [if_pos hcond] at h
                            obtain ⟨pk, hvpk, hmemf⟩ :=
                              lin_head_filter_pass (ocs := coeffs) (ois := is)
                                (obds := bds)
                                (totalMin := linTotalMin coeffs bds)
                                (totalMax := linTotalMax coeffs bds)
                                (eq := false) (b := b) (doms := doms2) (a := a) (k := k)
                                (c := c) (idx := idx) (bd := bd)
                                hshape (linExtract_length is doms bds hex)
                                rfl rfl hsat' hcov' hklt hck hidx hbd
                            -- hmemf : a[idx]! ∈ the filter, which is empty
                            -- (the split's branch condition is the filter's
                            --  isEmpty = true)
                            have hfnil : (linNarrowLe c b
                                (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                (getSlot doms2 idx)) = [] := by
                              rw [← List.isEmpty_iff]
                              exact hcond
                            rw [hfnil] at hmemf
                            exact absurd hmemf (by simp)
                          · -- the filter kept values: the run recursed —
                            -- the contradiction comes from the tail
                            -- h (with the inner if already reduced by the
                            -- rw [linNarrowAll]) is the Prop-if; hcond
                            -- selects the else branch
                            -- reduce the inner `if true = true` and select
                            -- the else branch via hcond
                            rw [show (if false = true then
                                linNarrowEq c b
                                  (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                  (linTotalMax coeffs bds - termMax c bd.1 bd.2)
                                  (getSlot doms2 idx)
                              else
                                linNarrowLe c b
                                  (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                  (getSlot doms2 idx))
                              = linNarrowLe c b
                                  (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                  (getSlot doms2 idx) from if_neg (by decide)] at h
                            rw [if_neg hcond] at h
                            have hcsuff : csuff = List.drop (k+1) coeffs := by
                              have hdrop : List.drop (k+1) coeffs
                                  = (List.drop k coeffs).drop 1 := by
                                rw [← List.drop_drop]
                              rw [hdrop, hdcs]
                              rfl
                            rw [hcsuff] at h
                            rw [show isuff = List.drop (k+1) is from by
                              have hdrop : List.drop (k+1) is
                                  = (List.drop k is).drop 1 := by
                                rw [← List.drop_drop]
                              rw [hdrop, his]
                              rfl,
                              show bsuff = List.drop (k+1) bds from by
                              have hdrop : List.drop (k+1) bds
                                  = (List.drop k bds).drop 1 := by
                                rw [← List.drop_drop]
                              rw [hdrop, hbs]
                              rfl] at h
                            have hn1 : coeffs.length - (k + 1) < n := by omega
                            -- the tail: recurse with the written domains
                            -- and the original coverage (the written slot
                            -- passes by lin_head_filter_pass, the master
                            -- lemma's interval derivation)
                            exact ih (coeffs.length - (k + 1)) hn1 (k + 1)
                              (setSlot doms2 idx (linNarrowLe c b
                                (linTotalMin coeffs bds - termMin c bd.1 bd.2)
                                (getSlot doms2 idx)))
                              (by omega) (by omega) h
                              (by
                                intro mm hmm
                                obtain ⟨hmemv, p', hvp, hlo', hhi'⟩ := hcov' mm hmm
                                by_cases hne : is[mm]! = idx
                                · rw [hne] at hmemv hvp
                                  have hmemint : Value.int p' ∈ getSlot doms2 idx := by
                                    rw [← hvp]
                                    exact hmemv
                                  obtain ⟨pk2, hvp2, hmemf2⟩ :=
                                    lin_head_filter_pass (ocs := coeffs)
                                      (ois := is) (obds := bds)
                                      (totalMin := linTotalMin coeffs bds)
                                      (totalMax := linTotalMax coeffs bds)
                                      (eq := false) (b := b) (doms := doms2)
                                      (a := a) (k := k) (c := c) (idx := idx)
                                      (bd := bd) hshape
                                      (linExtract_length is doms bds hex)
                                      rfl rfl (linLe_LinSat.mp hsat) hcov' hklt
                                      hck hidx hbd
                                  rw [hne]
                                  rw [getSlot_setSlot_eq doms2 _ idx
                                    (lt_length_of_mem_getSlot doms2 idx
                                      (Value.int p') hmemint)]
                                  -- p' = pk2: both are the integer of a[idx]!
                                  have hp'pk : p' = pk2 := by
                                    have h1 : Value.int p' = Value.int pk2 :=
                                      hvp.symm.trans hvp2
                                    injection h1
                                  rw [hp'pk] at hlo' hhi'
                                  exact ⟨hmemf2, pk2, hvp2, hlo', hhi'⟩
                                · rw [getSlot_setSlot_of_ne doms2 _ idx _ hne]
                                  exact ⟨hmemv, p', hvp, hlo', hhi'⟩)
                              (by exact linLe_LinSat.mp hsat)
          exact hrun coeffs.length 0 doms (by simp) (Nat.zero_le _) h
            (linExtract_cover is doms bds a hex hlen hget hint)
            (linLe_LinSat.mp hsat)
    · -- mismatched shape: the constraint is unsatisfiable (the dot
      -- product needs equal lengths), so contradiction is sound
      rw [if_neg hshape] at h
      obtain ⟨hlen2, hget2⟩ := allAssigns_spec doms a ha
      have hsat' := linLe_LinSat.mp hsat
      rw [show LinSat false (intVals coeffs) (is.map (fun i => a[i]!)) b
          = (∃ d, dotProduct (intVals coeffs) (is.map (fun i => a[i]!))
              = some d ∧ d ≤ b) from rfl] at hsat'
      obtain ⟨d, hd, hle⟩ := hsat'
      rw [dotProduct_mismatch hshape] at hd
      exact absurd hd (by simp)



/-! ## The strict-order propagators (`int_lt` style) -/

/-- The strict upper-bound propagator (`int_lt(x, c)` style, slot vs
    constant): slot `i`'s domain keeps its integer values `< c`;
    `contradiction` when that empties. -/
def propLtConstHi (i : Nat) (c : Int) (doms : List (List Value)) : PropResult :=
  let d' := atMostVals (c - 1) (getSlot doms i)
  if d'.isEmpty = true then .contradiction
  else .narrowed (setSlot doms i d')

/-- **Preservation for `propLtConstHi`**: on `narrowed doms'`, every
    assignment of the input domains whose slot `i` value is an
    integer `p < c` is still an assignment of `doms'`, and `doms'`
    is pointwise-subset the input domains; on `contradiction`, no
    assignment of the input domains bounds slot `i` strictly below
    `c`. -/
theorem propLtConstHi_preserves (i : Nat) (c : Int) :
    Preserves (DomConstraint.ltConstHi i c) (propLtConstHi i c) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propLtConstHi] at h
    obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, hx, hpc⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    by_cases hc : (atMostVals (c - 1) (getSlot doms i)).isEmpty = true
    · rw [if_pos hc] at h
      exact absurd h (by simp)
    · rw [if_neg hc] at h
      have hd : setSlot doms i (atMostVals (c - 1) (getSlot doms i)) = doms' :=
        PropResult.narrowed.inj h
      subst hd
      apply allAssigns_intro
      · rw [setSlot_length]
        exact hlen
      · intro m v hv
        by_cases hmi : m = i
        · rw [hmi] at hv
          have hvp : v = Value.int p := Option.some.inj (hv.symm.trans hx)
          subst hvp
          rw [hmi, getSlot_setSlot_eq doms (atMostVals (c - 1) (getSlot doms i)) i
            (lt_length_of_mem_getSlot doms i _ hxi)]
          exact mem_atMostVals.mpr ⟨hxi, p, rfl, by omega⟩
        · rw [getSlot_setSlot_of_ne doms (atMostVals (c - 1) (getSlot doms i)) i m hmi]
          exact hget m v hv
  · intro doms doms' h
    simp only [propLtConstHi] at h
    by_cases hc : (atMostVals (c - 1) (getSlot doms i)).isEmpty = true
    · rw [if_pos hc] at h
      exact absurd h (by simp)
    · rw [if_neg hc] at h
      have hd : setSlot doms i (atMostVals (c - 1) (getSlot doms i)) = doms' :=
        PropResult.narrowed.inj h
      subst hd
      exact DomPointwiseSub.setSlot (DomPointwiseSub.refl doms)
        (fun _ hv => (mem_atMostVals.mp hv).1)
  · intro doms h a ha hsat
    simp only [propLtConstHi] at h
    obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, hx, hpc⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    by_cases hc : (atMostVals (c - 1) (getSlot doms i)).isEmpty = true
    · rw [if_pos hc] at h
      have hmem : Value.int p ∈ atMostVals (c - 1) (getSlot doms i) :=
        mem_atMostVals.mpr ⟨hxi, p, rfl, by omega⟩
      rw [List.isEmpty_iff.mp hc] at hmem
      exact absurd hmem (by simp)
    · rw [if_neg hc] at h
      exact absurd h (by simp)

/-- The strict lower-bound propagator (`int_lt(c, x)` style, constant
    vs slot): slot `i`'s domain keeps its integer values `> c`;
    `contradiction` when that empties. -/
def propLtConstLo (i : Nat) (c : Int) (doms : List (List Value)) : PropResult :=
  let d' := atLeastVals (c + 1) (getSlot doms i)
  if d'.isEmpty = true then .contradiction
  else .narrowed (setSlot doms i d')

/-- **Preservation for `propLtConstLo`** (the symmetric local
    preservation theorem, strict lower-bound case). -/
theorem propLtConstLo_preserves (i : Nat) (c : Int) :
    Preserves (DomConstraint.ltConstLo i c) (propLtConstLo i c) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propLtConstLo] at h
    obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, hx, hcp⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    by_cases hc : (atLeastVals (c + 1) (getSlot doms i)).isEmpty = true
    · rw [if_pos hc] at h
      exact absurd h (by simp)
    · rw [if_neg hc] at h
      have hd : setSlot doms i (atLeastVals (c + 1) (getSlot doms i)) = doms' :=
        PropResult.narrowed.inj h
      subst hd
      apply allAssigns_intro
      · rw [setSlot_length]
        exact hlen
      · intro m v hv
        by_cases hmi : m = i
        · rw [hmi] at hv
          have hvp : v = Value.int p := Option.some.inj (hv.symm.trans hx)
          subst hvp
          rw [hmi, getSlot_setSlot_eq doms (atLeastVals (c + 1) (getSlot doms i)) i
            (lt_length_of_mem_getSlot doms i _ hxi)]
          exact mem_atLeastVals.mpr ⟨hxi, p, rfl, by omega⟩
        · rw [getSlot_setSlot_of_ne doms (atLeastVals (c + 1) (getSlot doms i)) i m hmi]
          exact hget m v hv
  · intro doms doms' h
    simp only [propLtConstLo] at h
    by_cases hc : (atLeastVals (c + 1) (getSlot doms i)).isEmpty = true
    · rw [if_pos hc] at h
      exact absurd h (by simp)
    · rw [if_neg hc] at h
      have hd : setSlot doms i (atLeastVals (c + 1) (getSlot doms i)) = doms' :=
        PropResult.narrowed.inj h
      subst hd
      exact DomPointwiseSub.setSlot (DomPointwiseSub.refl doms)
        (fun _ hv => (mem_atLeastVals.mp hv).1)
  · intro doms h a ha hsat
    simp only [propLtConstLo] at h
    obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, hx, hcp⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    by_cases hc : (atLeastVals (c + 1) (getSlot doms i)).isEmpty = true
    · rw [if_pos hc] at h
      have hmem : Value.int p ∈ atLeastVals (c + 1) (getSlot doms i) :=
        mem_atLeastVals.mpr ⟨hxi, p, rfl, by omega⟩
      rw [List.isEmpty_iff.mp hc] at hmem
      exact absurd hmem (by simp)
    · rw [if_neg hc] at h
      exact absurd h (by simp)

/-- The `int_lt` narrowing: slot `i` keeps values `≤ b` (the max of
    `j`'s domain: `p < q ≤ b` gives `p ≤ b`), slot `j` keeps values
    `≥ m` (the min of `i`'s domain: `m ≤ p < q` gives `q ≥ m`). -/
private def ltNarrow (b m : Int) (i j : Nat) (doms : List (List Value)) :
    List (List Value) :=
  let hi := atMostVals b (getSlot doms i)
  let hj := atLeastVals m (getSlot doms j)
  setSlot (setSlot doms i hi) j hj

/-- The strict-order propagator (`int_lt` style on two slots): slot
    `i` keeps values strictly below one plus the maximum integer of
    slot `j`'s domain, slot `j` keeps values strictly above one less
    than the minimum integer of slot `i`'s domain;
    `contradiction` when either side empties. -/
def propLtSlot (i j : Nat) (doms : List (List Value)) : PropResult :=
  match domMax (getSlot doms j) with
  | none => .contradiction
  | some b =>
      match domMin (getSlot doms i) with
      | none => .contradiction
      | some m =>
          let hi := atMostVals b (getSlot doms i)
          let hj := atLeastVals m (getSlot doms j)
          if hi.isEmpty = true ∨ hj.isEmpty = true then
            .contradiction
          else
            .narrowed (ltNarrow b m i j doms)

private theorem getSlot_ltNarrow_left {i j : Nat} {b m : Int}
    {doms : List (List Value)}
    (hi : i < doms.length) (hij : i ≠ j) :
    getSlot (ltNarrow b m i j doms) i = atMostVals b (getSlot doms i) := by
  simp only [ltNarrow]
  rw [getSlot_setSlot_of_ne (setSlot doms i (atMostVals b (getSlot doms i)))
    (atLeastVals m (getSlot doms j)) j i hij,
    getSlot_setSlot_eq doms _ i hi]

private theorem getSlot_ltNarrow_right {i j : Nat} {b m : Int}
    {doms : List (List Value)} (hj : j < doms.length) :
    getSlot (ltNarrow b m i j doms) j = atLeastVals m (getSlot doms j) := by
  simp only [ltNarrow]
  rw [getSlot_setSlot_eq (setSlot doms i (atMostVals b (getSlot doms i)))
    (atLeastVals m (getSlot doms j)) j (by rw [setSlot_length]; exact hj)]

private theorem getSlot_ltNarrow_other {i j k : Nat} {b m : Int}
    {doms : List (List Value)}
    (hki : k ≠ i) (hkj : k ≠ j) :
    getSlot (ltNarrow b m i j doms) k = getSlot doms k := by
  simp only [ltNarrow]
  rw [getSlot_setSlot_of_ne (setSlot doms i (atMostVals b (getSlot doms i)))
    (atLeastVals m (getSlot doms j)) j k hkj,
    getSlot_setSlot_of_ne doms (atMostVals b (getSlot doms i)) i k hki]

/-- **Preservation for `propLtSlot`**: on `narrowed doms'`, every
    assignment of the input domains whose slots `i` and `j` carry
    integers `p < q` is still an assignment of `doms'`, and `doms'`
    is pointwise-subset the input domains; on `contradiction`, no
    assignment of the input domains puts slot `i`'s value strictly
    below slot `j`'s. -/
theorem propLtSlot_preserves (i j : Nat) :
    Preserves (DomConstraint.ltSlot i j) (propLtSlot i j) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propLtSlot] at h
    obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, q, hx, hy, hlt⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    have hyj : Value.int q ∈ getSlot doms j := hget j _ hy
    have hilen : i < doms.length := lt_length_of_mem_getSlot doms i _ hxi
    have hjlen : j < doms.length := lt_length_of_mem_getSlot doms j _ hyj
    have hij : i ≠ j := by
      intro hij'
      subst hij'
      have : (Value.int p) = (Value.int q) := Option.some.inj (hx.symm.trans hy)
      injection this with hpq
      omega
    cases hb : domMax (getSlot doms j) with
    | none =>
        rw [hb] at h
        exact absurd h (by simp)
    | some b =>
        simp only [hb] at h
        obtain ⟨b', hbb, hqb⟩ := domMax_of_mem hyj
        rw [hb] at hbb
        injection hbb with hbqb
        cases hm : domMin (getSlot doms i) with
        | none =>
            rw [hm] at h
            exact absurd h (by simp)
        | some m =>
            simp only [hm] at h
            obtain ⟨m', hmm, hpm⟩ := domMin_of_mem hxi
            rw [hm] at hmm
            injection hmm with hmmm
            by_cases hc : (atMostVals b (getSlot doms i)).isEmpty = true ∨
              (atLeastVals m (getSlot doms j)).isEmpty = true
            · rw [if_pos hc] at h
              exact absurd h (by simp)
            · rw [if_neg hc] at h
              have hd : ltNarrow b m i j doms = doms' := PropResult.narrowed.inj h
              subst hd
              rw [hbqb, hmmm]
              apply allAssigns_intro
              · rw [ltNarrow, setSlot_length, setSlot_length]
                exact hlen
              · intro k v hv
                by_cases hki : k = i
                · rw [hki] at hv
                  have hvp : v = Value.int p := Option.some.inj (hv.symm.trans hx)
                  subst hvp
                  rw [hki, getSlot_ltNarrow_left hilen hij]
                  exact mem_atMostVals.mpr ⟨hxi, p, rfl, by omega⟩
                · by_cases hkj : k = j
                  · rw [hkj] at hv
                    have hvq : v = Value.int q := Option.some.inj (hv.symm.trans hy)
                    subst hvq
                    rw [hkj, getSlot_ltNarrow_right hjlen]
                    exact mem_atLeastVals.mpr ⟨hyj, q, rfl, by omega⟩
                  · rw [getSlot_ltNarrow_other (fun h => hki h) (fun h => hkj h)]
                    exact hget k v hv
  · intro doms doms' h
    simp only [propLtSlot] at h
    cases hb : domMax (getSlot doms j) with
    | none => rw [hb] at h; exact absurd h (by simp)
    | some b =>
        simp only [hb] at h
        cases hm : domMin (getSlot doms i) with
        | none => rw [hm] at h; exact absurd h (by simp)
        | some m =>
            simp only [hm] at h
            by_cases hc : (atMostVals b (getSlot doms i)).isEmpty = true ∨
              (atLeastVals m (getSlot doms j)).isEmpty = true
            · rw [if_pos hc] at h
              exact absurd h (by simp)
            · rw [if_neg hc] at h
              have hd : ltNarrow b m i j doms = doms' := PropResult.narrowed.inj h
              subst hd
              simp only [ltNarrow]
              exact DomPointwiseSub.setSlot
                (DomPointwiseSub.setSlot (DomPointwiseSub.refl doms)
                  (fun _ hv => (mem_atMostVals.mp hv).1))
                (fun _ hv => (mem_atLeastVals.mp hv).1)
  · intro doms h a ha hsat
    simp only [propLtSlot] at h
    obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, q, hx, hy, hlt⟩ := hsat
    have hxi : Value.int p ∈ getSlot doms i := hget i _ hx
    have hyj : Value.int q ∈ getSlot doms j := hget j _ hy
    cases hb : domMax (getSlot doms j) with
    | none =>
        have := domMax_of_mem hyj
        rw [hb] at this
        exact absurd this (by simp)
    | some b =>
        simp only [hb] at h
        obtain ⟨b', hbb, hqb⟩ := domMax_of_mem hyj
        rw [hb] at hbb
        injection hbb with hbqb
        cases hm : domMin (getSlot doms i) with
        | none =>
            have := domMin_of_mem hxi
            rw [hm] at this
            exact absurd this (by simp)
        | some m =>
            simp only [hm] at h
            obtain ⟨m', hmm, hpm⟩ := domMin_of_mem hxi
            rw [hm] at hmm
            injection hmm with hmmm
            by_cases hc : (atMostVals b (getSlot doms i)).isEmpty = true ∨
              (atLeastVals m (getSlot doms j)).isEmpty = true
            · rw [if_pos hc] at h
              rcases hc with hc | hc
              · have hmem : Value.int p ∈ atMostVals b (getSlot doms i) :=
                  mem_atMostVals.mpr ⟨hxi, p, rfl, by omega⟩
                rw [List.isEmpty_iff.mp hc] at hmem
                exact absurd hmem (by simp)
              · have hmem : Value.int q ∈ atLeastVals m (getSlot doms j) :=
                  mem_atLeastVals.mpr ⟨hyj, q, rfl, by omega⟩
                rw [List.isEmpty_iff.mp hc] at hmem
                exact absurd hmem (by simp)
            · rw [if_neg hc] at h
              exact absurd h (by simp)

/-! ## The Boolean propagators (`bool_not` / `bool_and` / `bool_or`) -/

/-- Keep only the Boolean values of a domain. -/
def boolVals (d : List Value) : List Value :=
  d.filter (fun v => match v with | .bool _ => true | _ => false)

/-- Membership characterization of `boolVals`. -/
theorem mem_boolVals {v : Value} {d : List Value} :
    v ∈ boolVals d ↔ v ∈ d ∧ ∃ p, v = .bool p := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := List.mem_filter.mp h
    cases v with
    | bool p => exact ⟨h1, p, rfl⟩
    | int w => simp at h2
    | setOfInt w => simp at h2
    | array w => simp at h2
  · rintro ⟨h1, p, rfl⟩
    exact List.mem_filter.mpr ⟨h1, rfl⟩

/-- Keep only the `true` Booleans of a domain. -/
def trueVals (d : List Value) : List Value :=
  d.filter (fun v => match v with | .bool true => true | _ => false)

/-- Membership characterization of `trueVals`. -/
theorem mem_trueVals {v : Value} {d : List Value} :
    v ∈ trueVals d ↔ v ∈ d ∧ v = .bool true := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := List.mem_filter.mp h
    cases v with
    | bool p => cases p with
      | true => exact ⟨h1, rfl⟩
      | false => simp at h2
    | int w => simp at h2
    | setOfInt w => simp at h2
    | array w => simp at h2
  · rintro ⟨h1, rfl⟩
    exact List.mem_filter.mpr ⟨h1, rfl⟩

/-- Keep only the `false` Booleans of a domain. -/
def falseVals (d : List Value) : List Value :=
  d.filter (fun v => match v with | .bool false => true | _ => false)

/-- Membership characterization of `falseVals`. -/
theorem mem_falseVals {v : Value} {d : List Value} :
    v ∈ falseVals d ↔ v ∈ d ∧ v = .bool false := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := List.mem_filter.mp h
    cases v with
    | bool p => cases p with
      | false => exact ⟨h1, rfl⟩
      | true => simp at h2
    | int w => simp at h2
    | setOfInt w => simp at h2
    | array w => simp at h2
  · rintro ⟨h1, rfl⟩
    exact List.mem_filter.mpr ⟨h1, rfl⟩

/-- A Boolean value of a slot read by an assignment lies in that
    slot's Boolean projection. -/
private theorem mem_boolVals_of {p : Bool} {i : Nat} {doms : List (List Value)}
    {a : List Value} (ha : a ∈ allAssigns doms)
    (hx : a[i]? = some (.bool p)) : .bool p ∈ boolVals (getSlot doms i) := by
  obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
  exact mem_boolVals.mpr ⟨hget i _ hx, p, rfl⟩

/-- The singleton Boolean of a domain's Boolean projection, if the
    projection is exactly one Boolean. -/
private def singleBool? (d : List Value) : Option Bool :=
  match single? (boolVals d) with
  | some (.bool p) => some p
  | _ => none

/-- `singleBool?` extracts the pin when the Boolean projection is a
    singleton, and the assignment's read matches it. -/
private theorem eq_of_singleBool? {i : Nat} {p p' : Bool}
    {doms : List (List Value)} {a : List Value}
    (ha : a ∈ allAssigns doms) (hx : a[i]? = some (.bool p))
    (hs : singleBool? (getSlot doms i) = some p') : p = p' := by
  have hxmem : Value.bool p ∈ boolVals (getSlot doms i) := mem_boolVals_of ha hx
  simp only [singleBool?] at hs
  cases hs2 : single? (boolVals (getSlot doms i)) with
  | none =>
      rw [hs2] at hs
      exact absurd hs (by simp)
  | some val =>
      cases val with
      | bool p'' =>
          have hsingle : boolVals (getSlot doms i) = [.bool p''] :=
            single?_eq_some_iff.mp hs2
          rw [hsingle] at hxmem
          have hpp'' : Value.bool p = Value.bool p'' :=
            List.mem_singleton.mp hxmem
          injection hpp'' with hpp'''
          rw [hs2] at hs
          -- the match now reduces definitionally to `some p'' = some p'`
          have hp'p : p'' = p' := Option.some.inj hs
          exact hpp''' ▸ hp'p
      | int w =>
          rw [hs2] at hs
          exact absurd hs (by simp)
      | setOfInt w =>
          rw [hs2] at hs
          exact absurd hs (by simp)
      | array w =>
          rw [hs2] at hs
          exact absurd hs (by simp)

/-- The Boolean negation propagator (`bool_not` style on two slots):
    if slot `i`'s Boolean values form a singleton, slot `j` narrows to
    the opposite Booleans (and symmetrically); otherwise the domains
    are unchanged (a sound no-op); `contradiction` when the opposite
    side empties. -/
def propBoolNotSlot (i j : Nat) (doms : List (List Value)) : PropResult :=
  match singleBool? (getSlot doms i) with
  | some p =>
      let dj' := if p then falseVals (getSlot doms j) else trueVals (getSlot doms j)
      if dj'.isEmpty = true then .contradiction
      else .narrowed (setSlot doms j dj')
  | none =>
      match singleBool? (getSlot doms j) with
      | some q =>
          let di' := if q then falseVals (getSlot doms i) else trueVals (getSlot doms i)
          if di'.isEmpty = true then .contradiction
          else .narrowed (setSlot doms i di')
      | none => .narrowed doms

/-- From `bool_not` satisfaction, the two slot values are opposite
    Booleans. -/
private theorem boolNot_opposite {i j : Nat} {a : List Value}
    (hsat : DomConstraint.SatisfiedBy (DomConstraint.boolNotSlot i j) a) :
    ∃ p q, a[i]? = some (.bool p) ∧ a[j]? = some (.bool q) ∧ q = !p := by
  obtain ⟨x, y, hx, hy, hxy⟩ := hsat
  have hxbool : ∃ p, x = .bool p := by
    cases x with
    | bool p => exact ⟨p, rfl⟩
    | int w => cases hxy with
      | inl h =>
          have h1 : Value.int w = Value.bool true := h.1
          exact absurd h1 (by simp)
      | inr h =>
          have h1 : Value.int w = Value.bool false := h.1
          exact absurd h1 (by simp)
    | setOfInt w => cases hxy with
      | inl h =>
          have h1 : Value.setOfInt w = Value.bool true := h.1
          exact absurd h1 (by simp)
      | inr h =>
          have h1 : Value.setOfInt w = Value.bool false := h.1
          exact absurd h1 (by simp)
    | array w => cases hxy with
      | inl h =>
          have h1 : Value.array w = Value.bool true := h.1
          exact absurd h1 (by simp)
      | inr h =>
          have h1 : Value.array w = Value.bool false := h.1
          exact absurd h1 (by simp)
  have hybool : ∃ q, y = .bool q := by
    cases y with
    | bool q => exact ⟨q, rfl⟩
    | int w => cases hxy with
      | inl h =>
          have h1 : Value.int w = Value.bool false := h.2
          exact absurd h1 (by simp)
      | inr h =>
          have h1 : Value.int w = Value.bool true := h.2
          exact absurd h1 (by simp)
    | setOfInt w => cases hxy with
      | inl h =>
          have h1 : Value.setOfInt w = Value.bool false := h.2
          exact absurd h1 (by simp)
      | inr h =>
          have h1 : Value.setOfInt w = Value.bool true := h.2
          exact absurd h1 (by simp)
    | array w => cases hxy with
      | inl h =>
          have h1 : Value.array w = Value.bool false := h.2
          exact absurd h1 (by simp)
      | inr h =>
          have h1 : Value.array w = Value.bool true := h.2
          exact absurd h1 (by simp)
  obtain ⟨p, rfl⟩ := hxbool
  obtain ⟨q, rfl⟩ := hybool
  refine ⟨p, q, hx, hy, ?_⟩
  cases p <;> cases q <;> simp_all

/-- The narrowed target for `bool_not`'s `i` side (when `j` is the
    pinned singleton `q` and the assignment reads `p` at `i`, with
    `q = !p`): the read value survives the narrowing. -/
private theorem boolNot_target_i {q p : Bool} {i : Nat}
    {doms : List (List Value)} {a : List Value}
    (ha : a ∈ allAssigns doms) (hx : a[i]? = some (.bool p))
    (hqp : q = !p) :
    .bool p ∈ (if q then falseVals (getSlot doms i)
      else trueVals (getSlot doms i)) := by
  obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
  cases p with
  | true =>
      have hq' : q = false := by rw [hqp]; rfl
      subst hq'
      exact mem_trueVals.mpr ⟨hget i _ hx, rfl⟩
  | false =>
      have hq' : q = true := by rw [hqp]; rfl
      subst hq'
      exact mem_falseVals.mpr ⟨hget i _ hx, rfl⟩

/-- The narrowed target for `bool_not`'s `j` side (when `i` is the
    pinned singleton `p` and the assignment reads `q` at `j`, with
    `q = !p`): the read value survives the narrowing. -/
private theorem boolNot_target_j {p q : Bool} {j : Nat}
    {doms : List (List Value)} {a : List Value}
    (ha : a ∈ allAssigns doms) (hy : a[j]? = some (.bool q))
    (hpq : q = !p) :
    .bool q ∈ (if p then falseVals (getSlot doms j)
      else trueVals (getSlot doms j)) := by
  obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
  cases p with
  | true =>
      have hq' : q = false := by rw [hpq]; rfl
      subst hq'
      exact mem_falseVals.mpr ⟨hget j _ hy, rfl⟩
  | false =>
      have hq' : q = true := by rw [hpq]; rfl
      subst hq'
      exact mem_trueVals.mpr ⟨hget j _ hy, rfl⟩

/-- **Preservation for `propBoolNotSlot`**: on `narrowed doms'`, every
    assignment of the input domains whose slots `i` and `j` carry
    opposite Booleans is still an assignment of `doms'`, and `doms'`
    is pointwise-subset the input domains; on `contradiction`, no
    assignment of the input domains makes them opposite. -/
theorem propBoolNotSlot_preserves (i j : Nat) :
    Preserves (DomConstraint.boolNotSlot i j) (propBoolNotSlot i j) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propBoolNotSlot] at h
    obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
    obtain ⟨p, q, hx, hy, hq⟩ := boolNot_opposite hsat
    have hxmem : .bool p ∈ boolVals (getSlot doms i) := mem_boolVals_of ha hx
    have hymem : .bool q ∈ boolVals (getSlot doms j) := mem_boolVals_of ha hy
    cases hs : singleBool? (getSlot doms i) with
    | none =>
        simp only [hs] at h
        cases hs2 : singleBool? (getSlot doms j) with
        | none =>
            simp only [hs2] at h
            have hd : doms' = doms := (PropResult.narrowed.inj h).symm
            subst hd
            exact ha
        | some q' =>
            simp only [hs2] at h
            have hqq' : q = q' := eq_of_singleBool? ha hy hs2
            -- the pin forces x = !q', so narrow slot i to the opposite
            have htarget : .bool p ∈ (if q' then falseVals (getSlot doms i)
              else trueVals (getSlot doms i)) :=
              boolNot_target_i ha hx (by rw [← hqq']; exact hq)
            by_cases hc : (if q' then falseVals (getSlot doms i)
                else trueVals (getSlot doms i)).isEmpty = true
            · rw [if_pos hc] at h
              rw [List.isEmpty_iff.mp hc] at htarget
              exact absurd htarget (by simp)
            · rw [if_neg hc] at h
              have hd : setSlot doms i
                  (if q' then falseVals (getSlot doms i)
                   else trueVals (getSlot doms i)) = doms' :=
                PropResult.narrowed.inj h
              subst hd
              have hilen : i < doms.length :=
                lt_length_of_mem_getSlot doms i _ (mem_boolVals.mp hxmem).1
              apply allAssigns_intro
              · rw [setSlot_length]
                exact hlen
              · intro m v hv
                by_cases hmi : m = i
                · rw [hmi] at hv
                  have hvp : v = .bool p := Option.some.inj (hv.symm.trans hx)
                  subst hvp
                  rw [hmi, getSlot_setSlot_eq doms _ i hilen]
                  exact htarget
                · rw [getSlot_setSlot_of_ne doms _ i m hmi]
                  exact hget m v hv
    | some p' =>
        simp only [hs] at h
        have hpp' : p = p' := eq_of_singleBool? ha hx hs
        have htarget : .bool q ∈ (if p' then falseVals (getSlot doms j)
          else trueVals (getSlot doms j)) :=
          boolNot_target_j ha hy (by rw [← hpp']; exact hq)
        by_cases hc : (if p' then falseVals (getSlot doms j)
            else trueVals (getSlot doms j)).isEmpty = true
        · rw [if_pos hc] at h
          rw [List.isEmpty_iff.mp hc] at htarget
          exact absurd htarget (by simp)
        · rw [if_neg hc] at h
          have hd : setSlot doms j
              (if p' then falseVals (getSlot doms j)
               else trueVals (getSlot doms j)) = doms' :=
            PropResult.narrowed.inj h
          subst hd
          have hjlen : j < doms.length :=
            lt_length_of_mem_getSlot doms j _ (mem_boolVals.mp hymem).1
          apply allAssigns_intro
          · rw [setSlot_length]
            exact hlen
          · intro m v hv
            by_cases hmj : m = j
            · rw [hmj] at hv
              have hvq : v = .bool q := Option.some.inj (hv.symm.trans hy)
              subst hvq
              rw [hmj, getSlot_setSlot_eq doms _ j hjlen]
              exact htarget
            · rw [getSlot_setSlot_of_ne doms _ j m hmj]
              exact hget m v hv
  · intro doms doms' h
    simp only [propBoolNotSlot] at h
    cases hs : singleBool? (getSlot doms i) with
    | none =>
        simp only [hs] at h
        cases hs2 : singleBool? (getSlot doms j) with
        | none =>
            simp only [hs2] at h
            have hd : doms' = doms := (PropResult.narrowed.inj h).symm
            subst hd
            exact DomPointwiseSub.refl _
        | some q' =>
            simp only [hs2] at h
            by_cases hc : (if q' then falseVals (getSlot doms i)
                else trueVals (getSlot doms i)).isEmpty = true
            · rw [if_pos hc] at h
              exact absurd h (by simp)
            · rw [if_neg hc] at h
              have hd : setSlot doms i
                  (if q' then falseVals (getSlot doms i)
                   else trueVals (getSlot doms i)) = doms' :=
                PropResult.narrowed.inj h
              subst hd
              refine DomPointwiseSub.setSlot (DomPointwiseSub.refl doms) ?_
              intro v hv
              cases q' with
              | true => exact (mem_falseVals.mp hv).1
              | false => exact (mem_trueVals.mp hv).1
    | some p' =>
        simp only [hs] at h
        by_cases hc : (if p' then falseVals (getSlot doms j)
            else trueVals (getSlot doms j)).isEmpty = true
        · rw [if_pos hc] at h
          exact absurd h (by simp)
        · rw [if_neg hc] at h
          have hd : setSlot doms j
              (if p' then falseVals (getSlot doms j)
               else trueVals (getSlot doms j)) = doms' :=
            PropResult.narrowed.inj h
          subst hd
          refine DomPointwiseSub.setSlot (DomPointwiseSub.refl doms) ?_
          intro v hv
          cases p' with
          | true => exact (mem_falseVals.mp hv).1
          | false => exact (mem_trueVals.mp hv).1
  · intro doms h a ha hsat
    simp only [propBoolNotSlot] at h
    obtain ⟨p, q, hx, hy, hq⟩ := boolNot_opposite hsat
    have hxmem : .bool p ∈ boolVals (getSlot doms i) := mem_boolVals_of ha hx
    have hymem : .bool q ∈ boolVals (getSlot doms j) := mem_boolVals_of ha hy
    cases hs : singleBool? (getSlot doms i) with
    | none =>
        simp only [hs] at h
        cases hs2 : singleBool? (getSlot doms j) with
        | none => rw [hs2] at h; exact absurd h (by simp)
        | some q' =>
            simp only [hs2] at h
            have hqq' : q = q' := eq_of_singleBool? ha hy hs2
            have htarget : .bool p ∈ (if q' then falseVals (getSlot doms i)
              else trueVals (getSlot doms i)) :=
              boolNot_target_i ha hx (by rw [← hqq']; exact hq)
            by_cases hc : (if q' then falseVals (getSlot doms i)
                else trueVals (getSlot doms i)).isEmpty = true
            · rw [if_pos hc] at h
              rw [List.isEmpty_iff.mp hc] at htarget
              exact absurd htarget (by simp)
            · rw [if_neg hc] at h
              exact absurd h (by simp)
    | some p' =>
        simp only [hs] at h
        have hpp' : p = p' := eq_of_singleBool? ha hx hs
        have htarget : .bool q ∈ (if p' then falseVals (getSlot doms j)
          else trueVals (getSlot doms j)) :=
          boolNot_target_j ha hy (by rw [← hpp']; exact hq)
        by_cases hc : (if p' then falseVals (getSlot doms j)
            else trueVals (getSlot doms j)).isEmpty = true
        · rw [if_pos hc] at h
          rw [List.isEmpty_iff.mp hc] at htarget
          exact absurd htarget (by simp)
        · rw [if_neg hc] at h
          exact absurd h (by simp)

/-- The Boolean conjunction propagator (`bool_and` style on three
    slots): when both input slots' Boolean values are singleton
    pinned, the output slot narrows to their conjunction; otherwise
    the domains are unchanged; `contradiction` when the narrowed
    output empties. -/
def propBoolAndSlot (i j k : Nat) (doms : List (List Value)) : PropResult :=
  match singleBool? (getSlot doms i), singleBool? (getSlot doms j) with
  | some p, some q =>
      let dk' := if (p && q) then trueVals (getSlot doms k) else falseVals (getSlot doms k)
      if dk'.isEmpty = true then .contradiction
      else .narrowed (setSlot doms k dk')
  | _, _ => .narrowed doms

/-- The narrowed output target for `bool_and`: the assignment's
    output value survives the conjunction narrowing. -/
private theorem boolAnd_target {r : Bool} {k : Nat} {p' q' : Bool}
    {doms : List (List Value)} {a : List Value}
    (ha : a ∈ allAssigns doms) (hz : a[k]? = some (.bool r))
    (hand : (p' && q') = r) :
    .bool r ∈ (if (p' && q') then trueVals (getSlot doms k)
      else falseVals (getSlot doms k)) := by
  obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
  subst hand
  cases p' <;> cases q' <;>
    first
      | exact mem_trueVals.mpr ⟨hget k _ hz, rfl⟩
      | exact mem_falseVals.mpr ⟨hget k _ hz, rfl⟩

/-- **Preservation for `propBoolAndSlot`**: on `narrowed doms'`, every
    assignment of the input domains whose slots `i`, `j`, `k` carry
    Booleans `p`, `q`, `r` with `p && q = r` is still an assignment of
    `doms'`, and `doms'` is pointwise-subset the input domains; on
    `contradiction`, no assignment of the input domains satisfies the
    conjunction. -/
theorem propBoolAndSlot_preserves (i j k : Nat) :
    Preserves (DomConstraint.boolAndSlot i j k) (propBoolAndSlot i j k) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propBoolAndSlot] at h
    obtain ⟨p, q, r, hx, hy, hz, hand⟩ := hsat
    have hxmem : .bool p ∈ boolVals (getSlot doms i) := mem_boolVals_of ha hx
    have hymem : .bool q ∈ boolVals (getSlot doms j) := mem_boolVals_of ha hy
    have hzmem : .bool r ∈ boolVals (getSlot doms k) := mem_boolVals_of ha hz
    cases hs : singleBool? (getSlot doms i) with
    | some p' =>
        simp only [hs] at h
        have hpp' : p = p' := eq_of_singleBool? ha hx hs
        cases hs2 : singleBool? (getSlot doms j) with
        | some q' =>
            simp only [hs2] at h
            have hqq' : q = q' := eq_of_singleBool? ha hy hs2
            have hand' : (p' && q') = r := by rw [← hpp', ← hqq']; exact hand
            have htarget : .bool r ∈
                (if (p' && q') then trueVals (getSlot doms k)
                 else falseVals (getSlot doms k)) :=
              boolAnd_target ha hz hand'
            by_cases hc : (if (p' && q') then trueVals (getSlot doms k)
                else falseVals (getSlot doms k)).isEmpty = true
            · rw [if_pos hc] at h
              rw [List.isEmpty_iff.mp hc] at htarget
              exact absurd htarget (by simp)
            · rw [if_neg hc] at h
              have hd : setSlot doms k
                  (if (p' && q') then trueVals (getSlot doms k)
                   else falseVals (getSlot doms k)) = doms' :=
                PropResult.narrowed.inj h
              subst hd
              obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
              have hklen : k < doms.length :=
                lt_length_of_mem_getSlot doms k _ (mem_boolVals.mp hzmem).1
              apply allAssigns_intro
              · rw [setSlot_length]
                exact hlen
              · intro m v hv
                by_cases hmk : m = k
                · rw [hmk] at hv
                  have hvr : v = .bool r := Option.some.inj (hv.symm.trans hz)
                  subst hvr
                  rw [hmk, getSlot_setSlot_eq doms _ k hklen]
                  exact htarget
                · rw [getSlot_setSlot_of_ne doms _ k m hmk]
                  exact hget m v hv
        | none =>
            simp only [hs2] at h
            have hd : doms' = doms := (PropResult.narrowed.inj h).symm
            subst hd
            exact ha
    | none =>
        simp only [hs] at h
        have hd : doms' = doms := (PropResult.narrowed.inj h).symm
        subst hd
        exact ha
  · intro doms doms' h
    simp only [propBoolAndSlot] at h
    cases hs : singleBool? (getSlot doms i) with
    | some p' =>
        simp only [hs] at h
        cases hs2 : singleBool? (getSlot doms j) with
        | some q' =>
            rw [hs2] at h
            simp only [] at h
            by_cases hc : (if (p' && q') then trueVals (getSlot doms k)
                else falseVals (getSlot doms k)).isEmpty = true
            · rw [if_pos hc] at h
              exact absurd h (by simp)
            · rw [if_neg hc] at h
              have hd : setSlot doms k
                  (if (p' && q') then trueVals (getSlot doms k)
                   else falseVals (getSlot doms k)) = doms' :=
                PropResult.narrowed.inj h
              subst hd
              refine DomPointwiseSub.setSlot (DomPointwiseSub.refl doms) ?_
              intro v hv
              cases p' <;> cases q' <;> simp at hv <;>
                first
                  | exact (mem_trueVals.mp hv).1
                  | exact (mem_falseVals.mp hv).1
        | none =>
            simp only [hs2] at h
            have hd : doms' = doms := (PropResult.narrowed.inj h).symm
            subst hd
            exact DomPointwiseSub.refl _
    | none =>
        simp only [hs] at h
        have hd : doms' = doms := (PropResult.narrowed.inj h).symm
        subst hd
        exact DomPointwiseSub.refl _
  · intro doms h a ha hsat
    simp only [propBoolAndSlot] at h
    obtain ⟨p, q, r, hx, hy, hz, hand⟩ := hsat
    have hxmem : .bool p ∈ boolVals (getSlot doms i) := mem_boolVals_of ha hx
    have hymem : .bool q ∈ boolVals (getSlot doms j) := mem_boolVals_of ha hy
    have hzmem : .bool r ∈ boolVals (getSlot doms k) := mem_boolVals_of ha hz
    cases hs : singleBool? (getSlot doms i) with
    | some p' =>
        simp only [hs] at h
        have hpp' : p = p' := eq_of_singleBool? ha hx hs
        cases hs2 : singleBool? (getSlot doms j) with
        | some q' =>
            simp only [hs2] at h
            have hqq' : q = q' := eq_of_singleBool? ha hy hs2
            have hand' : (p' && q') = r := by rw [← hpp', ← hqq']; exact hand
            have htarget : .bool r ∈
                (if (p' && q') then trueVals (getSlot doms k)
                 else falseVals (getSlot doms k)) :=
              boolAnd_target ha hz hand'
            by_cases hc : (if (p' && q') then trueVals (getSlot doms k)
                else falseVals (getSlot doms k)).isEmpty = true
            · rw [if_pos hc] at h
              rw [List.isEmpty_iff.mp hc] at htarget
              exact absurd htarget (by simp)
            · rw [if_neg hc] at h
              exact absurd h (by simp)
        | none => rw [hs2] at h; exact absurd h (by simp)
    | none => rw [hs] at h; exact absurd h (by simp)

/-- The Boolean disjunction propagator (`bool_or` style on three
    slots): when both input slots' Boolean values are singleton
    pinned, the output slot narrows to their disjunction; otherwise
    the domains are unchanged; `contradiction` when the narrowed
    output empties. -/
def propBoolOrSlot (i j k : Nat) (doms : List (List Value)) : PropResult :=
  match singleBool? (getSlot doms i), singleBool? (getSlot doms j) with
  | some p, some q =>
      let dk' := if (p || q) then trueVals (getSlot doms k) else falseVals (getSlot doms k)
      if dk'.isEmpty = true then .contradiction
      else .narrowed (setSlot doms k dk')
  | _, _ => .narrowed doms

/-- The narrowed output target for `bool_or`: the assignment's
    output value survives the disjunction narrowing. -/
private theorem boolOr_target {r : Bool} {k : Nat} {p' q' : Bool}
    {doms : List (List Value)} {a : List Value}
    (ha : a ∈ allAssigns doms) (hz : a[k]? = some (.bool r))
    (hor : (p' || q') = r) :
    .bool r ∈ (if (p' || q') then trueVals (getSlot doms k)
      else falseVals (getSlot doms k)) := by
  obtain ⟨_, hget⟩ := allAssigns_spec doms a ha
  subst hor
  cases p' <;> cases q' <;>
    first
      | exact mem_trueVals.mpr ⟨hget k _ hz, rfl⟩
      | exact mem_falseVals.mpr ⟨hget k _ hz, rfl⟩

/-- **Preservation for `propBoolOrSlot`**: on `narrowed doms'`, every
    assignment of the input domains whose slots `i`, `j`, `k` carry
    Booleans `p`, `q`, `r` with `p || q = r` is still an assignment of
    `doms'`, and `doms'` is pointwise-subset the input domains; on
    `contradiction`, no assignment of the input domains satisfies the
    disjunction. -/
theorem propBoolOrSlot_preserves (i j k : Nat) :
    Preserves (DomConstraint.boolOrSlot i j k) (propBoolOrSlot i j k) := by
  constructor
  · intro doms doms' h a ha hsat
    simp only [propBoolOrSlot] at h
    obtain ⟨p, q, r, hx, hy, hz, hor⟩ := hsat
    have hxmem : .bool p ∈ boolVals (getSlot doms i) := mem_boolVals_of ha hx
    have hymem : .bool q ∈ boolVals (getSlot doms j) := mem_boolVals_of ha hy
    have hzmem : .bool r ∈ boolVals (getSlot doms k) := mem_boolVals_of ha hz
    cases hs : singleBool? (getSlot doms i) with
    | some p' =>
        simp only [hs] at h
        have hpp' : p = p' := eq_of_singleBool? ha hx hs
        cases hs2 : singleBool? (getSlot doms j) with
        | some q' =>
            simp only [hs2] at h
            have hqq' : q = q' := eq_of_singleBool? ha hy hs2
            have hor' : (p' || q') = r := by rw [← hpp', ← hqq']; exact hor
            have htarget : .bool r ∈
                (if (p' || q') then trueVals (getSlot doms k)
                 else falseVals (getSlot doms k)) :=
              boolOr_target ha hz hor'
            by_cases hc : (if (p' || q') then trueVals (getSlot doms k)
                else falseVals (getSlot doms k)).isEmpty = true
            · rw [if_pos hc] at h
              rw [List.isEmpty_iff.mp hc] at htarget
              exact absurd htarget (by simp)
            · rw [if_neg hc] at h
              have hd : setSlot doms k
                  (if (p' || q') then trueVals (getSlot doms k)
                   else falseVals (getSlot doms k)) = doms' :=
                PropResult.narrowed.inj h
              subst hd
              obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
              have hklen : k < doms.length :=
                lt_length_of_mem_getSlot doms k _ (mem_boolVals.mp hzmem).1
              apply allAssigns_intro
              · rw [setSlot_length]
                exact hlen
              · intro m v hv
                by_cases hmk : m = k
                · rw [hmk] at hv
                  have hvr : v = .bool r := Option.some.inj (hv.symm.trans hz)
                  subst hvr
                  rw [hmk, getSlot_setSlot_eq doms _ k hklen]
                  exact htarget
                · rw [getSlot_setSlot_of_ne doms _ k m hmk]
                  exact hget m v hv
        | none =>
            simp only [hs2] at h
            have hd : doms' = doms := (PropResult.narrowed.inj h).symm
            subst hd
            exact ha
    | none =>
        simp only [hs] at h
        have hd : doms' = doms := (PropResult.narrowed.inj h).symm
        subst hd
        exact ha
  · intro doms doms' h
    simp only [propBoolOrSlot] at h
    cases hs : singleBool? (getSlot doms i) with
    | some p' =>
        simp only [hs] at h
        cases hs2 : singleBool? (getSlot doms j) with
        | some q' =>
            rw [hs2] at h
            simp only [] at h
            by_cases hc : (if (p' || q') then trueVals (getSlot doms k)
                else falseVals (getSlot doms k)).isEmpty = true
            · rw [if_pos hc] at h
              exact absurd h (by simp)
            · rw [if_neg hc] at h
              have hd : setSlot doms k
                  (if (p' || q') then trueVals (getSlot doms k)
                   else falseVals (getSlot doms k)) = doms' :=
                PropResult.narrowed.inj h
              subst hd
              refine DomPointwiseSub.setSlot (DomPointwiseSub.refl doms) ?_
              intro v hv
              cases p' <;> cases q' <;> simp at hv <;>
                first
                  | exact (mem_trueVals.mp hv).1
                  | exact (mem_falseVals.mp hv).1
        | none =>
            simp only [hs2] at h
            have hd : doms' = doms := (PropResult.narrowed.inj h).symm
            subst hd
            exact DomPointwiseSub.refl _
    | none =>
        simp only [hs] at h
        have hd : doms' = doms := (PropResult.narrowed.inj h).symm
        subst hd
        exact DomPointwiseSub.refl _
  · intro doms h a ha hsat
    simp only [propBoolOrSlot] at h
    obtain ⟨p, q, r, hx, hy, hz, hor⟩ := hsat
    have hxmem : .bool p ∈ boolVals (getSlot doms i) := mem_boolVals_of ha hx
    have hymem : .bool q ∈ boolVals (getSlot doms j) := mem_boolVals_of ha hy
    have hzmem : .bool r ∈ boolVals (getSlot doms k) := mem_boolVals_of ha hz
    cases hs : singleBool? (getSlot doms i) with
    | some p' =>
        simp only [hs] at h
        have hpp' : p = p' := eq_of_singleBool? ha hx hs
        cases hs2 : singleBool? (getSlot doms j) with
        | some q' =>
            simp only [hs2] at h
            have hqq' : q = q' := eq_of_singleBool? ha hy hs2
            have hor' : (p' || q') = r := by rw [← hpp', ← hqq']; exact hor
            have htarget : .bool r ∈
                (if (p' || q') then trueVals (getSlot doms k)
                 else falseVals (getSlot doms k)) :=
              boolOr_target ha hz hor'
            by_cases hc : (if (p' || q') then trueVals (getSlot doms k)
                else falseVals (getSlot doms k)).isEmpty = true
            · rw [if_pos hc] at h
              rw [List.isEmpty_iff.mp hc] at htarget
              exact absurd htarget (by simp)
            · rw [if_neg hc] at h
              exact absurd h (by simp)
        | none => rw [hs2] at h; exact absurd h (by simp)
    | none => rw [hs] at h; exact absurd h (by simp)

end LeanFzn.Solver.Propagation.DomainFiltering

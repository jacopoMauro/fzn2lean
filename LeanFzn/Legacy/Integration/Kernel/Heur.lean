/-
File: LeanFzn/Integration/Kernel/Heur.lean

Purpose (PLAN task P2): the ACTIVITY-DRIVEN DECISION ORDER for the public LCG
route.

The certified LCG search always pins the HEAD value of the head remaining slot
(`splitData` / `valueLiteral` — the "fixed decision order"). This module
replaces that fixed VALUE order by an activity order: the values of every
domain are presented to the search sorted by

  (a) how often a constraint names the value as a constant at that slot
      (`constHits`: the constant-bound families `constEq`/`leConstHi`/
      `leConstLo`/`ltConstHi`/`ltConstLo`, i.e. the family the branch-and-bound
      bound constraints `improveBound` take), plus
  (b) how often the value's own pin literal — or its negation — occurs in the
      clause database (`pinHits` over the seed clauses),

descending, with ties kept in source order (`mergeSort` on the `(activity,
position)` key, whose output is the unique sorted permutation, hence the
identity whenever all activities agree).

WHY THIS IS CERTIFIED FOR FREE: the presentation is a per-domain VALUE-LIST
PERMUTATION. A domain is a SET of admissible values: reordering a domain's
list changes the order in which the search TRIES values, never the assignment
set the frame denotes (`FrameCovers` is membership-based) nor the leaf's
constraint satisfaction. So the whole certified route is instantiated at the
reordered box and the verdicts transfer back by a `List.Perm` argument: no
scheduler invariant (`LcgRunState`, coverage, ranks) is re-proved, and every
public theorem statement stays byte-identical.

WHAT THIS IS NOT (deferred, see REPORT-P2.md): the decision VARIABLE is forced
to be the head remaining slot by the positional `BranchFrame = List Domain ×
Assignment` representation (`frame.2` is the chosen PREFIX), so
"smallest-domain-first" over SLOTS is out of reach without a frame redesign;
and a per-conflict (VSIDS-style) activity table or an interruptible restart
driver would need the dispatcher's STATE to carry the table. The activity here
is the STATIC projection of those signals (constraint constants + clause
database), which is what the certified route can consume without touching the
scheduler state.

OBJECTIVE BIAS (PLAN task O1, §6-§9): a second presentation, `sortDomBias`,
detects the trailing branch-and-bound bound constraint of an optimization
round (`.leConstHi s k` / `.leConstLo s k` as the LAST constraint, as
`Compiler/Objective.lean`'s `improveBound` appends it) and orders the values
of that slot by extremity — low first for `leConstHi` (minimize), high first
for `leConstLo` (maximize) — while every other slot keeps the activity order.
The transfer is the presentation-generic core `reorderAuxWith` instantiated at
`sortDomBias` (`reorderAuxBias`), and `solveCompiledLcgHeurBias` is the biased
public entry. The measured effect is neutral on the two O1 acceptance cases
(objective slot decided last in both) and large on models declaring the
objective slot early (41 -> 2 improving rounds on the objective-first sum
demo), so the default `lcgVerdict` route remains the unbiased
`solveCompiledLcgHeur`; the biased entry stays as the reference.

DAG: Integration.Lcg (the public route) -> this module -> Integration.Lcg's
public solve definitions.
-/
import LeanFzn.Legacy.Integration.Kernel.Lcg
import LeanFzn.Legacy.Solver.UIP.Runtime.Stats
open LeanFzn.Semantics LeanFzn.Compiler LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP LeanFzn.Solver.UIP.C3b
open LeanFzn.Solver.UIP.LcgEmissionTyped LeanFzn.Solver.UIP.LcgMixedCompiledKit
open LeanFzn.Solver.UIP.LcgMixedPhaseTerminal LeanFzn.Solver.UIP.LcgMixedGood
open LeanFzn.Solver.UIP.LcgPhaseKernel
open LeanFzn.Solver.UIP.LcgSeedClauses

namespace LeanFzn.Integration.LcgHeur

/-! ## §1 The activity signal and the activity order -/

/-- Literal activity in a clause database: how often `l` itself (up to
normalization) or its negation occurs. -/
def pinHits (db : List Clause) (l : Literal) : Nat :=
  (db.map fun c => (c.filter fun x => litEqB x l.norm || litEqB x l.negate.norm).length).sum

/-- The `(slot, constant)` pairs named by the constant-bound constraint
families — the families the branch-and-bound `improveBound` constraint takes,
plus the compiled source bounds. -/
def dcConsts : List DomConstraint → List (Nat × Int)
  | [] => []
  | .constEq i v :: rest =>
      (match v.intView with | some k => [(i, k)] | none => []) ++ dcConsts rest
  | .leConstHi i c :: rest => (i, c) :: dcConsts rest
  | .leConstLo i c :: rest => (i, c) :: dcConsts rest
  | .ltConstHi i c :: rest => (i, c) :: dcConsts rest
  | .ltConstLo i c :: rest => (i, c) :: dcConsts rest
  | _ :: rest => dcConsts rest

/-- How often the constraint list names the constant `k` at slot `s`. -/
def constHits (dcs : List DomConstraint) (s : Nat) (k : Int) : Nat :=
  ((dcConsts dcs).filter fun p => p.1 == s && p.2 == k).length

/-- **THE VALUE ACTIVITY**: the constraint-constant hits at the value's slot
plus the literal-activity hits of its pin literal in the clause database. -/
def valAct (dcs : List DomConstraint) (db : List Clause) (s : Nat) (w : Value) : Nat :=
  (match w.intView with
    | some i => constHits dcs s i
    | none => 0) +
  (match valueLiteral s w with
    | some l => pinHits db l
    | none => 0)

/-- The value list with `(activity, source position, value)` keys.  The
enumeration view of a domain is supplied by the caller, so the presentation
is computed on the `Dom.enum` view and rebuilt with `Dom.ofList`. -/
def keyAux (dcs : List DomConstraint) (db : List Clause) (s : Nat) :
    Nat → List Value → List (Nat × Nat × Value)
  | _, [] => []
  | i, w :: rest => (valAct dcs db s w, i, w) :: keyAux dcs db s (i + 1) rest

/-- The keys of `keyAux` carry the original list: projecting them is the
identity. -/
theorem keyAux_map (dcs : List DomConstraint) (db : List Clause) (s i : Nat)
    (vs : List Value) : (keyAux dcs db s i vs).map (fun p => p.2.2) = vs := by
  induction vs generalizing i with
  | nil => rfl
  | cons w rest ih =>
      simp only [keyAux, List.map_cons]
      rw [ih]

/-- A first-order test for the uniform-activity fast path: every key's first
component equals the first key's. Empty and singleton key lists are uniform
(the test is vacuously true). -/
def uniformKeysB : List (Nat × Nat × Value) → Bool
  | [] => true
  | k :: ks => ks.all fun p => p.1 == k.1

/-- A key list whose first components all equal `k` is pairwise `≤` on first
components — the exact comparator relation `mergeSort` consumes. -/
theorem pairwise_of_all_fst_eq {k : Nat} :
    ∀ {l : List (Nat × Nat × Value)}, (∀ p ∈ l, p.1 = k) →
      l.Pairwise (fun p q => decide (p.1 ≤ q.1) = true)
  | [], _ => List.Pairwise.nil
  | _ :: _, h => by
      rw [List.pairwise_cons]
      exact ⟨fun q hq => by
              rw [h _ (List.mem_cons_self ..), h q (List.mem_cons_of_mem _ hq)]
              exact decide_eq_true (Nat.le_refl _),
            pairwise_of_all_fst_eq fun q hq => h q (List.mem_cons_of_mem _ hq)⟩

/-- `uniformKeysB` is exactly the pairwise-sortedness hypothesis for the
activity comparator. -/
theorem pairwise_of_uniformKeysB {ks : List (Nat × Nat × Value)}
    (h : uniformKeysB ks = true) :
    ks.Pairwise (fun p q => decide (p.1 ≤ q.1) = true) := by
  match ks with
  | [] => exact List.Pairwise.nil
  | k :: ks =>
      have hall : ∀ p ∈ ks, p.1 = k.1 :=
        fun p hp => eq_of_beq ((List.all_eq_true.mp h) p hp)
      rw [List.pairwise_cons]
      exact ⟨fun q hq => by
              rw [hall q hq]
              exact decide_eq_true (Nat.le_refl _),
            pairwise_of_all_fst_eq hall⟩

/-- On a uniform key list the merge sort is the identity, so the old sorted
projection is the original domain: this is the external-equivalence fact the
fast path of `sortDom` replaces by the direct return. -/
theorem mergeSort_uniform (dcs : List DomConstraint) (db : List Clause) (s : Nat)
    (vs : List Value) (h : uniformKeysB (keyAux dcs db s 0 vs) = true) :
    ((keyAux dcs db s 0 vs).mergeSort fun p q => decide (p.1 ≤ q.1)).map
      (fun p => p.2.2) = vs := by
  rw [List.mergeSort_of_pairwise (pairwise_of_uniformKeysB h), keyAux_map]

/-- The enumeration cap of the activity presentation.  The presentation is a
    heuristic; when a domain has more candidate values than this, building the
    `Dom.enum` view and sorting it costs more than the order can plausibly
    save.  It is also a robustness bound: `Dom.enum` of a wide `.holes`
    interval recurses once per value, so an unbounded heuristic enumeration
    exhausts the task stack on models with a declared range in the hundreds of
    millions (gbac's objective is `0..179280830`).  Such a domain is passed
    through unchanged, which is still a permutation of itself. -/
def enumOrderCap : Nat := 65536

/-- Structural "small enumeration" test for the activity presentation.  It
    never takes the `Dom.enum` view: a `.holes` interval wider than the cap is
    rejected by its span, an explicit `.general` list by its length, and the
    bitset cases are always at most 64 values. -/
def enumSmallB (d : Domain) : Bool :=
  match d.rep with
  | .small .. => true
  | .holes lo hi _ => decide ((hi - lo + 1).toNat ≤ enumOrderCap)
  | .general vs => decide (vs.length ≤ enumOrderCap)

/-- ACTIVITY ORDER of one domain: descending activity, ties in source order.
`mergeSort` on the `(activity, position)` key is the (unique) sorted
permutation, so already-key-sorted inputs — in particular all-zero activities,
where the key is the position alone — are left untouched. Uniform keys take the
fast path: by `mergeSort_uniform` the sorted projection would be the domain
itself, so the domain is returned directly and no sorted copy is built.
Domains wider than `enumOrderCap` are returned unchanged instead of being
enumerated and sorted. -/
def sortDom (dcs : List DomConstraint) (db : List Clause) (s : Nat) (d : Domain) : Domain :=
  if enumSmallB d then
    let ks := keyAux dcs db s 0 (Dom.enum d)
    if uniformKeysB ks then d
    else Dom.ofList ((ks.mergeSort fun p q => decide (p.1 ≤ q.1)).map fun p => p.2.2)
  else d

/-- The uniform-activity fast path of `sortDom`: the domain is returned
unchanged. -/
theorem sortDom_uniform (dcs : List DomConstraint) (db : List Clause) (s : Nat)
    (d : Domain) (h : uniformKeysB (keyAux dcs db s 0 (Dom.enum d)) = true) :
    sortDom dcs db s d = d := by
  unfold sortDom
  by_cases hsmall : enumSmallB d = true
  · rw [if_pos hsmall, if_pos h]
  · rw [if_neg hsmall]

/-! ## §1b Structural inactivity and the compiled fast path

`sortDom` currently enumerates the whole domain on every call, even when
every activity at the slot is provably zero.  The sufficient condition below
is purely structural: a slot is *inactive* when no constant-bound constraint
names it and no literal of the clause database has it as its atom slot.  Then
`valAct` is zero on every value, the key list is uniform, and the sorted
projection is the domain itself — so the enumeration can be skipped.  The
condition is conservative (`false` falls back to the old body) and is
installed with `@[implemented_by]`; the kernel statement of `sortDom` is
unchanged. -/

/-- The slots named by the constant-bound constraint families. -/
def constSlots (dcs : List DomConstraint) : List Nat :=
  (dcConsts dcs).map Prod.fst

/-- The slots mentioned by any literal of the clause database. -/
def dbSlots (db : List Clause) : List Nat :=
  db.flatMap fun c => c.map fun l => l.atom.slot

/-- The structural inactivity test on precomputed slot lists: `true` only
when neither list names `s`. -/
def inactiveSlotOfB (cs bs : List Nat) (s : Nat) : Bool :=
  !(cs.contains s) && !(bs.contains s)

/-- **STRUCTURAL INACTIVITY** of a slot: no constant-bound constraint names
`s` and no literal in the clause database has atom slot `s`.  This is a
sufficient (conservative) condition for every activity at the slot to be
zero; `false` falls back to the ordinary `sortDom`. -/
def inactiveSlotB (dcs : List DomConstraint) (db : List Clause) (s : Nat) : Bool :=
  inactiveSlotOfB (constSlots dcs) (dbSlots db) s

/-- A slot list that does not contain `s` has no pair with first component
`s`: the constraint-constant activity at `s` is zero. -/
theorem constHits_eq_zero_of_not_mem (dcs : List DomConstraint) (s : Nat) (k : Int)
    (h : s ∉ constSlots dcs) : constHits dcs s k = 0 := by
  unfold constHits
  have hnil : (dcConsts dcs).filter (fun p => p.1 == s && p.2 == k) = [] := by
    rw [List.filter_eq_nil_iff]
    intro p hp hps
    apply h
    unfold constSlots
    exact List.mem_map.mpr ⟨p, hp, (beq_iff_eq.mp (Bool.and_eq_true_iff.mp hps).1)⟩
  rw [hnil]
  rfl

/-- A clause database whose every literal has a slot outside the slot list
contributes no pin activity: `pinHits` at a literal of slot `s` is zero. -/
theorem pinHits_eq_zero_of_slot_not_mem (db : List Clause) (l : Literal) (s : Nat)
    (hslot : l.atom.slot = s) (h : s ∉ dbSlots db) : pinHits db l = 0 := by
  unfold pinHits
  rw [List.sum_eq_zero_iff_forall_eq_nat]
  intro n hn
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
  have hnil : (c.filter fun x => litEqB x l.norm || litEqB x l.negate.norm) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx hxord
    have hxmem : x.atom.slot ∈ dbSlots db :=
      List.mem_flatMap.mpr ⟨c, hc, List.mem_map.mpr ⟨x, hx, rfl⟩⟩
    have hxne : x.atom.slot ≠ s := fun he => h (he ▸ hxmem)
    rw [Bool.or_eq_true] at hxord
    rcases hxord with hxl | hxn
    · have hxeq : x = l.norm := of_decide_eq_true hxl
      apply hxne
      rw [hxeq, norm_atom_slot, hslot]
    · have hxeq : x = l.negate.norm := of_decide_eq_true hxn
      apply hxne
      rw [hxeq, literal_negate_norm_atom_slot, hslot]
  rw [hnil]
  rfl

/-- Every activity at a structurally inactive slot is zero. -/
theorem valAct_eq_zero_of_inactiveSlotB (dcs : List DomConstraint) (db : List Clause)
    (s : Nat) (h : inactiveSlotB dcs db s = true) (w : Value) :
    valAct dcs db s w = 0 := by
  unfold inactiveSlotB inactiveSlotOfB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hc, hd⟩ := h
  have hcs : (constSlots dcs).contains s = false := by simpa using hc
  have hds : (dbSlots db).contains s = false := by simpa using hd
  have hcs' : s ∉ constSlots dcs := by
    rw [List.contains_eq_mem] at hcs
    simpa using hcs
  have hds' : s ∉ dbSlots db := by
    rw [List.contains_eq_mem] at hds
    simpa using hds
  cases w with
  | bool b =>
      simp only [valAct, Value.intView, valueLiteral]
      rw [constHits_eq_zero_of_not_mem dcs s _ hcs',
        pinHits_eq_zero_of_slot_not_mem db (posBool s b) s rfl hds']
  | int i =>
      simp only [valAct, Value.intView, valueLiteral]
      rw [constHits_eq_zero_of_not_mem dcs s _ hcs',
        pinHits_eq_zero_of_slot_not_mem db (negNe s i) s rfl hds']
  | setOfInt v =>
      simp only [valAct, Value.intView, valueLiteral]
  | array vs =>
      simp only [valAct, Value.intView, valueLiteral]

/-- If every value of the enumeration has zero activity, every key's first
component is zero. -/
theorem keyAux_fst_eq_zero (dcs : List DomConstraint) (db : List Clause) (s : Nat) :
    ∀ (vs : List Value) (i : Nat), (∀ w ∈ vs, valAct dcs db s w = 0) →
      ∀ p ∈ keyAux dcs db s i vs, p.1 = 0 := by
  intro vs
  induction vs with
  | nil =>
      intro i _ p hp
      exact absurd hp (by simp [keyAux])
  | cons w rest ih =>
      intro i h p hp
      simp only [keyAux, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact h w (List.mem_cons_self ..)
      · exact ih (i + 1) (fun x hx => h x (List.mem_cons_of_mem _ hx)) p hp

/-- All-zero activity makes the key list uniform: `uniformKeysB` holds. -/
theorem keyAux_uniform_of_valAct_zero (dcs : List DomConstraint) (db : List Clause)
    (s : Nat) (vs : List Value) (h : ∀ w ∈ vs, valAct dcs db s w = 0) :
    uniformKeysB (keyAux dcs db s 0 vs) = true := by
  cases vs with
  | nil => rfl
  | cons w rest =>
      simp only [keyAux, uniformKeysB, List.all_eq_true]
      intro p hp
      have h0 := keyAux_fst_eq_zero dcs db s rest 1
        (fun x hx => h x (List.mem_cons_of_mem _ hx)) p hp
      have hw := h w (List.mem_cons_self ..)
      show (p.1 == valAct dcs db s w) = true
      rw [h0, hw]
      rfl

/-- Same-signature compiled twin of `sortDom`: on a structurally inactive
slot every activity is zero, so the sorted projection would be the domain
itself and the enumeration is skipped.  The fallback repeats the bounded
`sortDom` body (rather than calling `sortDom`) so the `implemented_by` seam
cannot redirect it back to this twin. -/
def sortDomFast (dcs : List DomConstraint) (db : List Clause) (s : Nat)
    (d : Domain) : Domain :=
  if inactiveSlotB dcs db s then d
  else if enumSmallB d then
    let ks := keyAux dcs db s 0 (Dom.enum d)
    if uniformKeysB ks then d
    else Dom.ofList ((ks.mergeSort fun p q => decide (p.1 ≤ q.1)).map fun p => p.2.2)
  else d

/-- The fast substitution is the old presentation function. -/
theorem sortDomFast_eq (dcs : List DomConstraint) (db : List Clause) (s : Nat)
    (d : Domain) : sortDomFast dcs db s d = sortDom dcs db s d := by
  unfold sortDomFast
  by_cases hin : inactiveSlotB dcs db s = true
  · rw [if_pos hin]
    exact (sortDom_uniform dcs db s d
      (keyAux_uniform_of_valAct_zero dcs db s (Dom.enum d)
        (fun w _ => valAct_eq_zero_of_inactiveSlotB dcs db s hin w))).symm
  · rw [if_neg hin]
    by_cases hsmall : enumSmallB d = true
    · rw [if_pos hsmall]
      unfold sortDom
      rw [if_pos hsmall]
    · rw [if_neg hsmall]
      unfold sortDom
      rw [if_neg hsmall]

attribute [implemented_by sortDomFast] sortDom

/-- The activity order of a whole box, slot-by-slot. -/
def reorderAux (dcs : List DomConstraint) (db : List Clause) :
    Nat → List Domain → List Domain
  | _, [] => []
  | s, d :: rest => sortDom dcs db s d :: reorderAux dcs db (s + 1) rest

/-- The `sortDomFast` step on precomputed structural slot lists. -/
def sortDomFastOf (cs bs : List Nat) (dcs : List DomConstraint) (db : List Clause)
    (s : Nat) (d : Domain) : Domain :=
  if inactiveSlotOfB cs bs s then d else sortDom dcs db s d

/-- The hoisted per-slot step is the old presentation function. -/
theorem sortDomFastOf_eq {cs bs : List Nat} {dcs : List DomConstraint} {db : List Clause}
    (hcs : cs = constSlots dcs) (hbs : bs = dbSlots db) (s : Nat) (d : Domain) :
    sortDomFastOf cs bs dcs db s d = sortDom dcs db s d := by
  unfold sortDomFastOf
  rw [hcs, hbs]
  exact sortDomFast_eq dcs db s d

/-- `reorderAux` with the structural slot lists precomputed once. -/
def reorderAuxFastOf (cs bs : List Nat) (dcs : List DomConstraint) (db : List Clause) :
    Nat → List Domain → List Domain
  | _, [] => []
  | s, d :: rest =>
      sortDomFastOf cs bs dcs db s d :: reorderAuxFastOf cs bs dcs db (s + 1) rest

/-- Same-signature compiled twin of `reorderAux`: the structural slot lists
are computed once, then every structurally inactive slot is copied directly. -/
def reorderAuxFast (dcs : List DomConstraint) (db : List Clause) (s : Nat)
    (ds : List Domain) : List Domain :=
  reorderAuxFastOf (constSlots dcs) (dbSlots db) dcs db s ds

/-- The hoisted twin agrees with `reorderAux` slot-by-slot. -/
theorem reorderAuxFastOf_eq {cs bs : List Nat} {dcs : List DomConstraint} {db : List Clause}
    (hcs : cs = constSlots dcs) (hbs : bs = dbSlots db) :
    ∀ (s : Nat) (ds : List Domain),
      reorderAuxFastOf cs bs dcs db s ds = reorderAux dcs db s ds := by
  intro s ds
  induction ds generalizing s with
  | nil => rfl
  | cons d rest ih =>
      simp only [reorderAuxFastOf, reorderAux]
      rw [sortDomFastOf_eq hcs hbs, ih (s + 1)]

/-- The fast substitution is the old presentation function. -/
theorem reorderAuxFast_eq (dcs : List DomConstraint) (db : List Clause) :
    ∀ (s : Nat) (ds : List Domain),
      reorderAuxFast dcs db s ds = reorderAux dcs db s ds := by
  intro s ds
  exact reorderAuxFastOf_eq rfl rfl s ds

attribute [implemented_by reorderAuxFast] reorderAux

/-- **THE HEURISTIC PRESENTATION** of a box: every domain presented in
activity order. -/
def reorderDomains (dcs : List DomConstraint) (db : List Clause)
    (ds : List Domain) : List Domain :=
  reorderAux dcs db 0 ds

/-! ## §2 Permutation facts of the presentation -/

@[simp] theorem reorderAux_nil (dcs : List DomConstraint) (db : List Clause)
    (s : Nat) : reorderAux dcs db s [] = [] := rfl

@[simp] theorem reorderAux_cons (dcs : List DomConstraint) (db : List Clause)
    (s : Nat) (d : Domain) (rest : List Domain) :
    reorderAux dcs db s (d :: rest)
      = sortDom dcs db s d :: reorderAux dcs db (s + 1) rest := rfl

/-- The activity order of one slot is a permutation of the domain. -/
theorem sortDom_perm (dcs : List DomConstraint) (db : List Clause) (s : Nat)
    (d : Domain) : (sortDom dcs db s d).Perm d := by
  by_cases hsmall : enumSmallB d = true
  · by_cases h : uniformKeysB (keyAux dcs db s 0 (Dom.enum d)) = true
    · rw [sortDom_uniform dcs db s d h]
      exact Dom.Perm.refl d
    · have h' : sortDom dcs db s d
          = Dom.ofList (((keyAux dcs db s 0 (Dom.enum d)).mergeSort
              fun p q => decide (p.1 ≤ q.1)).map (fun p => p.2.2)) := by
        unfold sortDom
        rw [if_pos hsmall, if_neg h]
      rw [h']
      show List.Perm (Dom.enum (Dom.ofList _)) (Dom.enum d)
      rw [Dom.enum_ofList]
      exact ((List.mergeSort_perm _ _).map _).trans (by rw [keyAux_map])
  · have h' : sortDom dcs db s d = d := by
      unfold sortDom
      rw [if_neg hsmall]
    rw [h']
    exact Dom.Perm.refl d

/-- The presentation does not change the number of slots. -/
theorem reorderAux_length (dcs : List DomConstraint) (db : List Clause) :
    ∀ (s : Nat) (ds : List Domain), (reorderAux dcs db s ds).length = ds.length := by
  intro s ds
  induction ds generalizing s with
  | nil => rfl
  | cons d rest ih =>
      change (sortDom dcs db s d :: reorderAux dcs db (s + 1) rest).length
        = (d :: rest).length
      simp only [List.length_cons, ih]

/-- The presentation does not change the value multiset of any slot: the
`i`-th domain of the reordered box is the activity order of the `i`-th domain
of the original box. -/
theorem reorderAux_getElem? (dcs : List DomConstraint) (db : List Clause)
    (s : Nat) : ∀ (ds : List Domain) (i : Nat),
    (reorderAux dcs db s ds)[i]? = (ds[i]?).map (sortDom dcs db (s + i)) := by
  intro ds
  induction ds generalizing s with
  | nil => intro i; rfl
  | cons d rest ih =>
      intro i
      cases i with
      | zero =>
          change (sortDom dcs db s d :: reorderAux dcs db (s + 1) rest)[0]?
            = ((d :: rest)[0]?).map (sortDom dcs db (s + 0))
          rw [List.getElem?_cons_zero]
          rw [List.getElem?_cons_zero]
          rw [show s + 0 = s by omega]
          rfl
      | succ j =>
          change (sortDom dcs db s d :: reorderAux dcs db (s + 1) rest)[j + 1]?
            = ((d :: rest)[j + 1]?).map (sortDom dcs db (s + (j + 1)))
          rw [List.getElem?_cons_succ]
          rw [List.getElem?_cons_succ]
          rw [ih (s + 1) j]
          rw [show s + (j + 1) = s + 1 + j by omega]

/-- Every domain of the reordered box is a permutation of a domain of the
original box. -/
theorem mem_reorderAux_perm (dcs : List DomConstraint) (db : List Clause)
    (s : Nat) : ∀ (ds : List Domain) {d' : Domain},
    d' ∈ reorderAux dcs db s ds → ∃ d ∈ ds, d'.Perm d := by
  intro ds
  induction ds generalizing s with
  | nil => intro d' h; exact absurd h (by simp)
  | cons d rest ih =>
      intro d' h
      change d' ∈ sortDom dcs db s d :: reorderAux dcs db (s + 1) rest at h
      rw [List.mem_cons] at h
      rcases h with h | h
      · exact ⟨d, List.mem_cons_self .., h ▸ sortDom_perm dcs db s d⟩
      · obtain ⟨d₀, hd₀, hp⟩ := ih (s + 1) h
        exact ⟨d₀, List.mem_cons_of_mem _ hd₀, hp⟩

/-- Every domain of the original box has a permutation-copy in the reordered
box. -/
theorem mem_reorderAux_exists (dcs : List DomConstraint) (db : List Clause)
    (s : Nat) (ds : List Domain) {d : Domain} (h : d ∈ ds) :
    ∃ d' ∈ reorderAux dcs db s ds, d'.Perm d := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
  refine ⟨sortDom dcs db (s + i) d, ?_, sortDom_perm dcs db (s + i) d⟩
  rw [List.mem_iff_getElem?]
  exact ⟨i, by rw [reorderAux_getElem?, hi]; rfl⟩

/-- PROPERTY TRANSFER (forward): a per-domain property invariant under
permutation holds of the reordered box. -/
theorem forall_mem_reorderAux {dcs : List DomConstraint} {db : List Clause}
    {φ : Domain → Prop} (hφ : ∀ {d d' : Domain}, d'.Perm d → φ d → φ d')
    (s : Nat) (ds : List Domain) (h : ∀ d ∈ ds, φ d) :
    ∀ d' ∈ reorderAux dcs db s ds, φ d' := by
  intro d' hd'
  obtain ⟨d₀, hd₀, hp⟩ := mem_reorderAux_perm dcs db s ds hd'
  exact hφ hp (h d₀ hd₀)

/-- PROPERTY TRANSFER (backward): the same in the other direction, for the
definitions the route consumes at the reordered box. -/
theorem forall_mem_reorderAux' {dcs : List DomConstraint} {db : List Clause}
    {φ : Domain → Prop} (hφ : ∀ {d d' : Domain}, d'.Perm d → φ d' → φ d)
    (s : Nat) (ds : List Domain) (h : ∀ d' ∈ reorderAux dcs db s ds, φ d') :
    ∀ d ∈ ds, φ d := by
  intro d₀ hd₀
  obtain ⟨d', hd', hp⟩ := mem_reorderAux_exists dcs db s ds hd₀
  exact hφ hp (h d' hd')

/-- BOOL-PREDICATE TRANSFER (forward): the executable gates are `List.all`
over per-domain Bool predicates, so their truth transfers along the
presentation. -/
theorem all_reorderAux {dcs : List DomConstraint} {db : List Clause}
    {f : Domain → Bool} (hf : ∀ {d d' : Domain}, d'.Perm d → f d = f d')
    (s : Nat) : ∀ (ds : List Domain), ds.all f = true →
    (reorderAux dcs db s ds).all f = true := by
  intro ds
  induction ds generalizing s with
  | nil => intro _; rfl
  | cons d rest ih =>
      intro h
      change (sortDom dcs db s d :: reorderAux dcs db (s + 1) rest).all f = true
      rw [List.all_cons, Bool.and_eq_true]
      rw [List.all_cons, Bool.and_eq_true] at h
      exact ⟨hf (sortDom_perm dcs db s d) ▸ h.1, ih (s + 1) h.2⟩


/-! ## §3 Permutation transfer of the route's per-domain predicates

Every executable gate and every alignment/type predicate the route consumes is
a `List.all` over per-domain conditions (plus slot-range conditions, which only
read the slot COUNT). Those transfer along the presentation by `List.Perm`
alone. -/

/-- A `List.all` implication transfers along a permutation. -/
theorem perm_all_imp {f : α → Bool} {l₁ l₂ : List α} (h : List.Perm l₁ l₂)
    (h₁ : l₂.all f = true) : l₁.all f = true := by
  rw [List.all_eq_true] at h₁ ⊢
  intro x hx
  exact h₁ x (h.mem_iff.mp hx)

/-- `List.all` congruence restricted to the list's elements. -/
theorem all_congr_mem {f g : α → Bool} : ∀ {l : List α},
    (∀ x ∈ l, f x = g x) → l.all f = l.all g
  | [], _ => rfl
  | x :: xs, h => by
      rw [List.all_cons, List.all_cons,
        h x (List.mem_cons_self ..),
        all_congr_mem (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- `valueMemB` is a membership test, hence permutation-invariant. -/
theorem valueMemB_perm {d d' : Domain} (h : d'.Perm d) (v : Value) :
    valueMemB v (Dom.enum d') = valueMemB v (Dom.enum d) := by
  rw [Bool.eq_iff_iff, valueMemB_iff, valueMemB_iff, h.mem_iff]

/-- The activity order of the empty domain is empty. -/
theorem sortDom_nil (dcs : List DomConstraint) (db : List Clause) (s : Nat) :
    sortDom dcs db s Dom.empty = Dom.empty := by
  simp [sortDom, enumSmallB, enumOrderCap, keyAux, Dom.empty]

/-- The `i`-th domain of a presented box: the reordered box's `getD` is the
activity order of the original box's `getD`. -/
theorem getD_reorderAux {dcs : List DomConstraint} {db : List Clause} (s : Nat)
    (ds : List Domain) (i : Nat) :
    (reorderAux dcs db s ds).getD i Dom.empty
      = sortDom dcs db (s + i) (ds.getD i Dom.empty) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    reorderAux_getElem?]
  cases ds[i]? with
  | none => simp [sortDom_nil]
  | some d => rfl

/-- `fitsB` reads the box only through membership at each slot, so it is
invariant under the presentation. -/
theorem fitsB_reorderAux {dcs : List DomConstraint} {db : List Clause}
    (s : Nat) (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit)
    (a : Assignment) :
    fitsB { problem with domains := reorderAux dcs db s problem.domains } a
      = fitsB problem a := by
  unfold fitsB
  dsimp only
  rw [reorderAux_length]
  rw [all_congr_mem (fun i _ => ?_)]
  by_cases hv : a[i]? = none
  · rw [hv]
  · obtain ⟨v, hv'⟩ := Option.ne_none_iff_exists'.mp hv
    rw [hv']
    change valueMemB v (Dom.enum ((reorderAux dcs db s problem.domains).getD i Dom.empty))
      = valueMemB v (Dom.enum (problem.domains.getD i Dom.empty))
    rw [getD_reorderAux,
      valueMemB_perm (sortDom_perm dcs db (s + i) (problem.domains.getD i Dom.empty)) v]

/-- `Fits` (the Prop-level box membership) is invariant under the
presentation. -/
theorem Fits_reorderAux {dcs : List DomConstraint} {db : List Clause}
    (s : Nat) (ds : List Domain) (a : Assignment) :
    a.Fits (reorderAux dcs db s ds) ↔ a.Fits ds := by
  constructor
  · rintro ⟨hlen, hmem⟩
    refine ⟨by rw [reorderAux_length] at hlen; exact hlen, ?_⟩
    intro i v hv
    have h' : v ∈ (reorderAux dcs db s ds).getD i Dom.empty := by
      simpa only [LeanFzn.Solver.Propagation.domEmpty_eq] using hmem i v hv
    rw [getD_reorderAux] at h'
    exact (sortDom_perm dcs db (s + i) (ds.getD i Dom.empty)).dom_mem_iff.mp h'
  · rintro ⟨hlen, hmem⟩
    refine ⟨by rw [reorderAux_length]; exact hlen, ?_⟩
    intro i v hv
    have h' : v ∈ ds.getD i Dom.empty := by
      simpa only [LeanFzn.Solver.Propagation.domEmpty_eq] using hmem i v hv
    have h2 : v ∈ (reorderAux dcs db s ds).getD i Dom.empty := by
      rw [getD_reorderAux]
      exact (sortDom_perm dcs db (s + i) (ds.getD i Dom.empty)).dom_mem_iff.mpr h'
    simpa only [LeanFzn.Solver.Propagation.domEmpty_eq] using h2

/-- `SlotOK` (the gate's slot-range fact) only reads the slot count and the
domain's non-emptiness. -/
theorem SlotOK_reorderAux {dcs : List DomConstraint} {db : List Clause}
    (s : Nat) (ds : List Domain) (i : Nat) (h : SlotOK ds i) :
    SlotOK (reorderAux dcs db s ds) i := by
  obtain ⟨d, hd, hne⟩ := h
  refine ⟨sortDom dcs db (s + i) d, ?_, ?_⟩
  · rw [reorderAux_getElem?, hd]; rfl
  · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil (Dom.enum d) hne
    exact fun he => by
      simpa [he] using (sortDom_perm dcs db (s + i) d).symm.subset hx

/-- The executable source gate `gateOk` transfers along the presentation. -/
theorem gateOk_reorderAux {dcs : List DomConstraint} {db : List Clause}
    (s : Nat) {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (h : gateOk problem = true) :
    gateOk { problem with domains := reorderAux dcs db s problem.domains } = true := by
  simp only [gateOk, List.all_eq_true, Bool.and_eq_true] at h ⊢
  intro d' hd'
  obtain ⟨d, hd, hp⟩ := mem_reorderAux_perm dcs db s problem.domains hd'
  have hdd := h d hd
  have hlen : d'.length = d.length := hp.length_eq
  refine ⟨?_, ?_⟩
  · simpa [hlen] using hdd.1
  · intro x hx
    exact hdd.2 x (hp.mem_iff.mp hx)

/-- An all-Boolean domain stays all-Boolean under a permutation. -/
theorem aba_all_bool_perm {d' d : Domain} (hp : d'.Perm d)
    (h : (Dom.enum d).all (fun v => match v with | .bool _ => true | _ => false) = true) :
    (Dom.enum d').all (fun v => match v with | .bool _ => true | _ => false) = true := by
  rw [List.all_eq_true] at h ⊢
  intro v hv
  exact h v (hp.mem_iff.mp hv)

/-- The pruning kit gate `domPruningOkB` transfers along the presentation. -/
theorem domPruningOkB_reorderAux {dcs : List DomConstraint} {db : List Clause}
    (s : Nat) {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (h : domPruningOkB problem = true) :
    domPruningOkB { problem with domains := reorderAux dcs db s problem.domains }
      = true := by
  simp only [domPruningOkB, Bool.and_eq_true, List.all_eq_true] at h ⊢
  obtain ⟨⟨hview, hlin⟩, hshape⟩ := h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro d' hd' v hv
    obtain ⟨d, hd, hp⟩ := mem_reorderAux_perm dcs db s problem.domains hd'
    exact hview d hd v (hp.mem_iff.mp hv)
  · intro c hc
    have hc' := hlin c hc
    by_cases haba : ∃ is k, c = DomConstraint.arrayBoolAndSlot is k
    · obtain ⟨is, k, rfl⟩ := haba
      change (is.all (fun i => decide (i < problem.domains.length) &&
          (Dom.enum (problem.domains.getD i Dom.empty)).all (fun v => match v with
            | .bool _ => true | _ => false))) = true at hc'
      rw [List.all_eq_true] at hc' ⊢
      intro i hi
      have h1 := hc' i hi
      rw [Bool.and_eq_true] at h1 ⊢
      obtain ⟨hlen, hbool⟩ := h1
      refine ⟨by rw [reorderAux_length]; exact hlen, ?_⟩
      rw [getD_reorderAux]
      exact aba_all_bool_perm
        (sortDom_perm dcs db (s + i) (problem.domains.getD i Dom.empty)) hbool
    · cases c with
      | arrayBoolAndSlot is k => exact absurd ⟨is, k, rfl⟩ haba
      | _ =>
          first
            | exact hc'
            | (rw [reorderAux_length] at ⊢
               exact hc')
  · intro d' hd'
    obtain ⟨d, hd, hp⟩ := mem_reorderAux_perm dcs db s problem.domains hd'
    have hd3 := hshape d hd
    rw [Bool.or_eq_true] at hd3 ⊢
    rcases hd3 with h3 | h3
    · left
      rw [List.all_eq_true] at h3 ⊢
      intro x hx
      exact h3 x (hp.mem_iff.mp hx)
    · right
      rw [List.all_eq_true] at h3 ⊢
      intro x hx
      exact h3 x (hp.mem_iff.mp hx)

/-- The mixed kit gate transfers along the presentation. -/
theorem mixedKitGateB_reorderAux {dcs : List DomConstraint} {db : List Clause}
    (s : Nat) {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (h : mixedKitGateB problem = true) :
    mixedKitGateB { problem with domains := reorderAux dcs db s problem.domains }
      = true := by
  simp only [mixedKitGateB, Bool.and_eq_true, List.all_eq_true] at h ⊢
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨?_, ?_⟩
  · intro d' hd'
    obtain ⟨d, hd, hp⟩ := mem_reorderAux_perm dcs db s problem.domains hd'
    obtain ⟨hint, hkind, hnodup⟩ := h₁ d hd
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      exact hint x (hp.mem_iff.mp hx)
    · rw [Bool.or_eq_true] at hkind ⊢
      rcases hkind with h3 | h3
      · left
        rw [List.all_eq_true] at h3 ⊢
        intro x hx
        exact h3 x (hp.mem_iff.mp hx)
      · right
        rw [List.all_eq_true] at h3 ⊢
        intro x hx
        exact h3 x (hp.mem_iff.mp hx)
    · rw [decide_eq_true_eq] at hnodup ⊢
      exact (hp.map Value.intView).nodup_iff.mpr hnodup
  · intro c hc
    have hc' := h₂ c hc
    rwa [reorderAux_length]


/-! ## §4 The activity-ordered route and its certified transfer -/

/-- The clause database the activity is read off: the run's own seed clauses. -/
def actDb (p : CompiledProblem DomConstraint) : List Clause :=
  seedClauses p.constraints

/-- The activity-ordered presentation of the compiled problem's box. -/
def heurDomains (p : CompiledProblem DomConstraint) : List Domain :=
  reorderAux p.constraints (actDb p) 0 p.domains

/-- **THE ACTIVITY-ORDERED PROBLEM**: the LCG problem with its domains
presented in activity order. -/
def heurProblem (p : CompiledProblem DomConstraint) :
    LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
  { lcgProblem p with domains := heurDomains p }

/-- The clamped propagator list at the activity-ordered box. -/
def heurProps (p : CompiledProblem DomConstraint) : List Propagator :=
  clampProps (heurDomains p) (p.constraints.filterMap propagatorOfProved)

theorem heurDomains_eq (p : CompiledProblem DomConstraint) :
    heurDomains p = reorderAux p.constraints (actDb p) 0 p.domains := rfl

/-- `fitsB` at the activity-ordered problem is the compiled problem's
`fitsB`. -/
theorem fitsB_heur (p : CompiledProblem DomConstraint) (a : Assignment) :
    fitsB (heurProblem p) a = fitsB (lcgProblem p) a := by
  rw [Bool.eq_iff_iff, fitsB_iff, fitsB_iff]
  show a.Fits (heurDomains p) ↔ a.Fits p.domains
  exact Fits_reorderAux 0 p.domains a

/-- The compiled leaf is unchanged by the presentation: `chronologicalLeaf`
reads the box only through `fitsB`, and the presentation preserves
`fitsB`. -/
theorem heurLeaf_eq (p : CompiledProblem DomConstraint) :
    lcgLeaf p = chronologicalLeaf (heurProblem p) DomConstraint.satisfiedB := by
  funext a
  simp only [lcgLeaf, chronologicalLeaf]
  rw [fitsB_heur p a]
  rfl

/-- The compiled input gate transfers to the activity-ordered box. -/
theorem heurCompiledInput {p : CompiledProblem DomConstraint}
    (h : lcgRouteGateMixed p = true) : CompiledInput (lcgLeaf p) (heurProblem p) := by
  simp only [lcgRouteGateMixed, Bool.and_eq_true] at h
  exact ⟨heurLeaf_eq p,
    gateOk_reorderAux 0 (problem := lcgProblem p) h.1.1,
    domPruningOkB_reorderAux 0 (problem := lcgProblem p) h.1.2⟩

/-- The mixed kit gate transfers to the activity-ordered box. -/
theorem heurGate {p : CompiledProblem DomConstraint}
    (h : lcgRouteGateMixed p = true) : mixedKitGateB (heurProblem p) = true := by
  simp only [lcgRouteGateMixed, Bool.and_eq_true,
    LcgMixedCompiledKit.mixedKitGateFastB_eq] at h
  exact mixedKitGateB_reorderAux 0 (problem := lcgProblem p) h.2

/-- The seed database stays pool-aligned at the activity-ordered box. -/
theorem heurAligned {p : CompiledProblem DomConstraint}
    (h : lcgRouteGateMixed p = true) :
    DatabaseAligned (heurDomains p) (seedClauses p.constraints) := by
  have hslot := slots_of_mixedGate (lcgInputMixed h)
    (by simp only [lcgRouteGateMixed, Bool.and_eq_true,
      LcgMixedCompiledKit.mixedKitGateFastB_eq] at h; exact h.2)
  refine seedClauses_aligned_of_slotOK fun dc hdc s hs => ?_
  exact SlotOK_reorderAux 0 (lcgProblem p).domains s (hslot dc hdc s hs)

/-- **THE ACTIVITY-ORDERED MIXED KIT**: every kit obligation at the
activity-ordered box is derived from the same gates, so the certified
semantic theorems apply to the activity-ordered run. -/
theorem heurKit {p : CompiledProblem DomConstraint}
    (h : lcgRouteGateMixed p = true) :
    MixedLcgKit (lcgLeaf p) (heurDomains p) (seedClauses p.constraints)
      p.constraints (p.constraints.filterMap propagatorOfProved)
      (heurProps p) :=
  kit_of_compiled_mixed (heurCompiledInput h) (heurGate h)
    (lcgSeedCanonical p) (heurAligned h)

/-- The route gate supplies the sparse frame gate at the activity-ordered box. -/
theorem heurFrameGate {p : CompiledProblem DomConstraint}
    (h : lcgRouteGateMixed p = true) :
    ∀ {cfg : SchedulerConfig (lcgLeaf p)},
      SupportedReach (heurDomains p) (seedClauses p.constraints) (heurProps p) cfg →
        FrameNonempty cfg := by
  intro cfg hreach
  exact LeanFzn.Solver.UIP.FrameLive.frameNonempty_of_gateOk (problem := heurProblem p)
    (heurCompiledInput h).gate (by rfl) hreach

/-- **THE ACTIVITY-ORDERED SCHEDULED RUN**: the certified scheduled LCG entry
on the activity-ordered presentation of the compiled problem. -/
def lcgRunHeur (p : CompiledProblem DomConstraint)
    (hgate : ∀ {cfg : SchedulerConfig (lcgLeaf p)},
      SupportedReach (heurDomains p) (seedClauses p.constraints) (heurProps p) cfg →
        FrameNonempty cfg) (prio : List Nat := []) (actBump : Bool := false) :
    DriverResult (lcgLeaf p) :=
  solve_sched (heurDomains p) (seedClauses p.constraints) (heurProps p)
    (lcgSeedEntailed p) (PropScheduler.init (heurProps p))
    (clampProps_local (heurDomains p) p.constraints)
    (PropSchedulerOK.init (heurProps p)) hgate prio actBump

/-- The activity-ordered run is the certified kernel at the activity-ordered
box. -/
theorem lcgRunHeur_eq_solve (p : CompiledProblem DomConstraint)
    (hgate : ∀ {cfg : SchedulerConfig (lcgLeaf p)},
      SupportedReach (heurDomains p) (seedClauses p.constraints) (heurProps p) cfg →
        FrameNonempty cfg) (prio : List Nat := []) (actBump : Bool := false) :
    lcgRunHeur p hgate prio actBump = LcgPhaseKernel.solve (heurDomains p)
      (seedClauses p.constraints) (heurProps p) (lcgSeedEntailed p) hgate prio actBump :=
  solve_sched_eq _ _ _ _ _ _ _ hgate prio actBump

/-- **SAT SOUNDNESS AT THE ORIGINAL BOX**: the activity-ordered run reports a
witness that is a genuine solution of the compiled problem as given. -/
theorem lcgRunHeur_sat {p : CompiledProblem DomConstraint} {prio : List Nat} {actBump : Bool}
    (h : lcgRouteGateMixed p = true) {a : List Value}
    (hrun : lcgRunHeur p (heurFrameGate h) prio actBump = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  have hr := hrun
  rw [lcgRunHeur_eq_solve p (heurFrameGate h) prio actBump] at hr
  have hs := solve_sat_solution_of_kit_mixed (heurKit h) (lcgSeedEntailed p)
    (heurFrameGate h) hr
  have hl := hs.1
  simp only [lcgLeaf, chronologicalLeaf, lcgProblem, Bool.and_eq_true] at hl
  refine ⟨LeanFzn.Solver.UIP.fits_mem_allAssigns ?_, hl.2.1⟩
  exact (Fits_reorderAux 0 (lcgProblem p).domains a).mp hs.2

/-- **UNSAT COMPLETENESS AT THE ORIGINAL BOX**: the activity-ordered run's
refutation excludes every solution of the compiled problem as given. -/
theorem lcgRunHeur_unsat {p : CompiledProblem DomConstraint} {prio : List Nat} {actBump : Bool}
    (h : lcgRouteGateMixed p = true)
    (hrun : lcgRunHeur p (heurFrameGate h) prio actBump = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  have hex : ∀ b, b ∈ allAssigns p.domains → accepts p b = true → False := by
    intro b hb ha
    have hr := hrun
    rw [lcgRunHeur_eq_solve p (heurFrameGate h) prio actBump] at hr
    have hn := solve_unsat_excludes_of_kit_mixed (heurKit h) (lcgSeedEntailed p)
      (heurFrameGate h) hr
    apply hn b
    have hf : Assignment.Fits p.domains b :=
      LeanFzn.Solver.Propagation.allAssigns_fits p.domains b hb
    refine ⟨?_, (Fits_reorderAux 0 (lcgProblem p).domains b).mpr hf⟩
    simp only [lcgLeaf, chronologicalLeaf, lcgProblem, Bool.and_eq_true]
    exact ⟨fitsB_iff.mpr hf, ha,
      List.all_eq_true.mpr fun c hc =>
        seedClauses_any_satisfiedB (fun dc hdc => List.all_eq_true.mp ha dc hdc) c hc⟩
  intro b hb
  cases ha : accepts p b with
  | false => rfl
  | true => exact False.elim (hex b hb ha)

/-- **TOTALITY**: the activity-ordered run always reports a verdict (the
driver is a total well-founded function, so the compiled entry never falls
through to `unknown`). -/
theorem lcgRunHeur_verdict (p : CompiledProblem DomConstraint)
    (hgate : ∀ {cfg : SchedulerConfig (lcgLeaf p)},
      SupportedReach (heurDomains p) (seedClauses p.constraints) (heurProps p) cfg →
        FrameNonempty cfg) (prio : List Nat := []) (actBump : Bool := false) :
    (∃ a, lcgRunHeur p hgate prio actBump = .sat a) ∨
      lcgRunHeur p hgate prio actBump = .unsat := by
  cases h : lcgRunHeur p hgate prio actBump with
  | sat a => exact Or.inl ⟨a, rfl⟩
  | unsat => exact Or.inr rfl


/-! ## §5 The activity-ordered public entry

`solveCompiledLcgHeur` is the public compiled entry with the activity-ordered
LCG branch; its SAT/UNSAT/totality statements are the ones the CLI and the
branch-and-bound solver consume, and they are stated at the problem AS GIVEN
(the presentation is invisible above this entry). -/

/-- **THE ACTIVITY-ORDERED COMPILED ENTRY**: the same route as
`solveCompiledLcgMixed`, with the LCG branch running on the activity-ordered
presentation (`lcgRunHeur`). -/
def solveCompiledLcgHeur (p : CompiledProblem DomConstraint)
    (prio : List Nat := []) (actBump : Bool := false) : SearchResult :=
  if hg : lcgRouteGateMixed p = true then
    match lcgRunHeur p (heurFrameGate hg) prio actBump with
    | .sat a => .sat a
    | .unsat => .unsat
  else
    LeanFzn.Solver.Chronological.solve (lcgProblem p) DomConstraint.satisfiedB
      (p.constraints.filterMap propagatorOfProved) (domPruningKit (lcgProblem p))

/-- The activity-ordered entry reports source solutions. -/
theorem solveCompiledLcgHeur_sat {p : CompiledProblem DomConstraint}
    {prio : List Nat} {actBump : Bool}
    {a : List Value} (h : solveCompiledLcgHeur p prio actBump = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  unfold solveCompiledLcgHeur at h
  split at h
  · rename_i hg
    split at h
    · rename_i hr
      cases h
      exact lcgRunHeur_sat hg hr
    · cases h
  · have hs := LeanFzn.Solver.Chronological.solve_sat_correct
      (fun c a => DomConstraint.satisfiedB_iff c a) h
    exact ⟨LeanFzn.Solver.UIP.fits_mem_allAssigns hs.1,
      List.all_eq_true.mpr (fun c hc =>
        (DomConstraint.satisfiedB_iff c a).mpr (hs.2 c hc))⟩

/-- The activity-ordered entry's refutation excludes every source solution. -/
theorem solveCompiledLcgHeur_unsat {p : CompiledProblem DomConstraint}
    {prio : List Nat} {actBump : Bool}
    (h : solveCompiledLcgHeur p prio actBump = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  unfold solveCompiledLcgHeur at h
  split at h
  · rename_i hg
    split at h
    · cases h
    · rename_i hr
      exact lcgRunHeur_unsat hg hr
  · have hn := LeanFzn.Solver.Chronological.solve_pruned_unsat_correct
      (fun c a => DomConstraint.satisfiedB_iff c a)
      (fun c hc _ hsol => seedClauses_satisfiedBy
        (fun dc hdc => hsol.2 dc hdc) c hc) h
    intro b hb
    cases ha : accepts p b with
    | false => rfl
    | true =>
        refine absurd ?_ hn
        exact ⟨b, LeanFzn.Solver.Propagation.allAssigns_fits p.domains b hb,
          fun c hc => (DomConstraint.satisfiedB_iff c b).mp
            (List.all_eq_true.mp ha c hc)⟩

/-- The activity-ordered entry is total: it never reports `unknown`. -/
theorem solveCompiledLcgHeur_verdict (p : CompiledProblem DomConstraint)
    (prio : List Nat := []) (actBump : Bool := false) :
    solveCompiledLcgHeur p prio actBump ≠ .unknown := by
  unfold solveCompiledLcgHeur
  split
  · rename_i hg
    cases lcgRunHeur p (heurFrameGate hg) prio actBump <;> simp
  · exact LeanFzn.Solver.Chronological.solve_total _ _ _ _


/-! ## §6 The objective-biased presentation (PLAN task O1)

The optimization driver (`LeanFzn.Integration.Optimize.optLoop`) re-solves
`curP p0 spec bo = p0.addConstraint (spec.improveBound b)`, so every
improving round carries its bound as the LAST constraint: `.leConstHi s (b-1)`
(minimize) or `.leConstLo s (b+1)` (maximize) at the objective slot `s`
(`Compiler/Objective.lean`). When that trailing bound is present, the biased
presentation puts the values at slot `s` in OBJECTIVE EXTREMITY order: low
values first for `leConstHi`, high values first for `leConstLo`, so the
round's first solution is the round's best (the driver then re-solves under
the tightened bound), while every other slot keeps the activity order. Values
on the improving side sort first automatically: ascending by value puts
`v ≤ b-1` ahead of the rest, descending puts `v ≥ b+1` ahead.

The bias is still a per-domain value-list PERMUTATION, so the certified
transfer below mirrors §2/§3 exactly: `reorderAuxWith` is the
presentation-generic core of the existing transfer, instantiated at
`sortDomBias` for the biased route; the activity-ordered route itself is
untouched and remains the unbiased reference. -/

/-- The objective-bias signal of a constraint list: the trailing constraint
names the biased slot and the preferred extremity when it is a branch-and-bound
improving bound — `leConstHi s k` (minimize: low values first) or
`leConstLo s k` (maximize: high values first). -/
def biasSlot? (dcs : List DomConstraint) : Option (Nat × Bool) :=
  match dcs.getLast? with
  | some (.leConstHi s _) => some (s, true)
  | some (.leConstLo s _) => some (s, false)
  | _ => none

/-- The bias at one slot: `some true` prefers low values, `some false` high
values, `none` keeps the activity order. -/
def biasAt (dcs : List DomConstraint) (s : Nat) : Option Bool :=
  match biasSlot? dcs with
  | some (s', low) => if s' == s then some low else none
  | none => none

/-- The extremity score of a value: lower is tried first. Low-first scores
the integer itself, high-first its negation; a non-integer value scores `0`
(the objective slot of a compiled optimization always holds integers). -/
def biasScore (lowFirst : Bool) (w : Value) : Int :=
  match w.intView with
  | some v => if lowFirst then v else -v
  | none => 0

/-- The value list with `(score, source position, value)` keys at the biased
slot. -/
def keyBiasAux (lowFirst : Bool) : Nat → List Value → List (Int × Nat × Value)
  | _, [] => []
  | i, w :: rest => (biasScore lowFirst w, i, w) :: keyBiasAux lowFirst (i + 1) rest

/-- The keys of `keyBiasAux` carry the original list: projecting them is the
identity. -/
theorem keyBiasAux_map (lowFirst : Bool) (i : Nat) (vs : List Value) :
    (keyBiasAux lowFirst i vs).map (fun p => p.2.2) = vs := by
  induction vs generalizing i with
  | nil => rfl
  | cons w rest ih =>
      simp only [keyBiasAux, List.map_cons]
      rw [ih]

/-- OBJECTIVE-BIASED ORDER of one domain: at the biased slot the values are
sorted by extremity score (`mergeSort` on the `(score, position)` key is the
unique sorted permutation, with ties in source order); every other slot keeps
the activity order of `sortDom`.  A domain wider than `enumOrderCap` is
returned unchanged, as in `sortDom`. -/
def sortDomBias (dcs : List DomConstraint) (db : List Clause)
    (s : Nat) (d : Domain) : Domain :=
  if enumSmallB d then
    match biasAt dcs s with
    | none => sortDom dcs db s d
    | some lowFirst =>
        Dom.ofList (((keyBiasAux lowFirst 0 (Dom.enum d)).mergeSort
          fun p q => decide (p.1 ≤ q.1)).map fun p => p.2.2)
  else d

/-- The biased order of one slot is still a permutation of the domain. -/
theorem sortDomBias_perm (dcs : List DomConstraint) (db : List Clause)
    (s : Nat) (d : Domain) : (sortDomBias dcs db s d).Perm d := by
  unfold sortDomBias
  by_cases hsmall : enumSmallB d = true
  · rw [if_pos hsmall]
    split
    · exact sortDom_perm dcs db s d
    · show List.Perm (Dom.enum (Dom.ofList _)) (Dom.enum d)
      rw [Dom.enum_ofList]
      exact ((List.mergeSort_perm _ _).map _).trans (by rw [keyBiasAux_map])
  · rw [if_neg hsmall]
    exact Dom.Perm.refl d

/-- The biased order of the empty domain is empty. -/
theorem sortDomBias_nil (dcs : List DomConstraint) (db : List Clause) (s : Nat) :
    sortDomBias dcs db s Dom.empty = Dom.empty := by
  unfold sortDomBias
  by_cases hsmall : enumSmallB Dom.empty = true
  · rw [if_pos hsmall]
    split
    · exact sortDom_nil dcs db s
    · simp [keyBiasAux, Dom.empty]
  · rw [if_neg hsmall]


/-! ## §7 The presentation-generic transfer core

`reorderAuxWith σ` is the §2/§3 machinery with the per-slot sort left
abstract: every transfer fact below uses only that `σ` permutes each domain.
`reorderAux` (activity order) and `reorderAuxBias` (objective bias) are its
two instances, so the certified route transfers along the bias in exactly the
style the activity order does. -/

/-- The presentation induced by a per-slot value-list transformation. -/
def reorderAuxWith (σ : Nat → Domain → Domain) : Nat → List Domain → List Domain
  | _, [] => []
  | s, d :: rest => σ s d :: reorderAuxWith σ (s + 1) rest

@[simp] theorem reorderAuxWith_nil (σ : Nat → Domain → Domain) (s : Nat) :
    reorderAuxWith σ s [] = [] := rfl

@[simp] theorem reorderAuxWith_cons (σ : Nat → Domain → Domain) (s : Nat)
    (d : Domain) (rest : List Domain) :
    reorderAuxWith σ s (d :: rest)
      = σ s d :: reorderAuxWith σ (s + 1) rest := rfl

/-- The presentation does not change the number of slots. -/
theorem reorderAuxWith_length (σ : Nat → Domain → Domain) :
    ∀ (s : Nat) (ds : List Domain), (reorderAuxWith σ s ds).length = ds.length := by
  intro s ds
  induction ds generalizing s with
  | nil => rfl
  | cons d rest ih =>
      change (σ s d :: reorderAuxWith σ (s + 1) rest).length = (d :: rest).length
      simp only [List.length_cons, ih]

/-- The `i`-th domain of the presented box is the transformed `i`-th domain
of the original box. -/
theorem reorderAuxWith_getElem? (σ : Nat → Domain → Domain) (s : Nat) :
    ∀ (ds : List Domain) (i : Nat),
    (reorderAuxWith σ s ds)[i]? = (ds[i]?).map (σ (s + i)) := by
  intro ds
  induction ds generalizing s with
  | nil => intro i; rfl
  | cons d rest ih =>
      intro i
      cases i with
      | zero =>
          change (σ s d :: reorderAuxWith σ (s + 1) rest)[0]?
            = ((d :: rest)[0]?).map (σ (s + 0))
          rw [List.getElem?_cons_zero]
          rw [List.getElem?_cons_zero]
          rw [show s + 0 = s by omega]
          rfl
      | succ j =>
          change (σ s d :: reorderAuxWith σ (s + 1) rest)[j + 1]?
            = ((d :: rest)[j + 1]?).map (σ (s + (j + 1)))
          rw [List.getElem?_cons_succ]
          rw [List.getElem?_cons_succ]
          rw [ih (s + 1) j]
          rw [show s + (j + 1) = s + 1 + j by omega]

/-- Every domain of the presented box is a permutation of a domain of the
original box. -/
theorem mem_reorderAuxWith_perm {σ : Nat → Domain → Domain}
    (hσ : ∀ s d, (σ s d).Perm d) (s : Nat) : ∀ (ds : List Domain) {d' : Domain},
    d' ∈ reorderAuxWith σ s ds → ∃ d ∈ ds, d'.Perm d := by
  intro ds
  induction ds generalizing s with
  | nil => intro d' h; exact absurd h (by simp)
  | cons d rest ih =>
      intro d' h
      change d' ∈ σ s d :: reorderAuxWith σ (s + 1) rest at h
      rw [List.mem_cons] at h
      rcases h with h | h
      · exact ⟨d, List.mem_cons_self .., h ▸ hσ s d⟩
      · obtain ⟨d₀, hd₀, hp⟩ := ih (s + 1) h
        exact ⟨d₀, List.mem_cons_of_mem _ hd₀, hp⟩

/-- A permuting presentation maps the empty domain to the empty domain.  The
empty-domain fixpoint is carried explicitly: `Dom` values need not be
canonical, so permutation alone does not identify two empty-enumeration
carriers, while `Dom.empty` is the value the route's `getD` defaults use. -/
theorem reorderAuxWith_nil_of_perm {σ : Nat → Domain → Domain}
    (hσ0 : ∀ s, σ s Dom.empty = Dom.empty) (s : Nat) :
    σ s Dom.empty = Dom.empty :=
  hσ0 s

/-- The presented box's `getD` is the transformed original `getD`. -/
theorem reorderAuxWith_getD {σ : Nat → Domain → Domain}
    (_hσ : ∀ s d, (σ s d).Perm d) (hσ0 : ∀ s, σ s Dom.empty = Dom.empty)
    (s : Nat) (ds : List Domain) (i : Nat) :
    (reorderAuxWith σ s ds).getD i Dom.empty
      = σ (s + i) (ds.getD i Dom.empty) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    reorderAuxWith_getElem?]
  cases ds[i]? with
  | none => simp [reorderAuxWith_nil_of_perm hσ0]
  | some d => rfl

/-- `fitsB` reads the box only through membership at each slot, so it is
invariant under a permuting presentation. -/
theorem fitsB_reorderAuxWith {σ : Nat → Domain → Domain}
    (hσ : ∀ s d, (σ s d).Perm d) (hσ0 : ∀ s, σ s Dom.empty = Dom.empty)
    (s : Nat)
    (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit)
    (a : Assignment) :
    fitsB { problem with domains := reorderAuxWith σ s problem.domains } a
      = fitsB problem a := by
  unfold fitsB
  dsimp only
  rw [reorderAuxWith_length]
  rw [all_congr_mem (fun i _ => ?_)]
  by_cases hv : a[i]? = none
  · rw [hv]
  · obtain ⟨v, hv'⟩ := Option.ne_none_iff_exists'.mp hv
    rw [hv']
    change valueMemB v (Dom.enum ((reorderAuxWith σ s problem.domains).getD i Dom.empty))
      = valueMemB v (Dom.enum (problem.domains.getD i Dom.empty))
    rw [reorderAuxWith_getD hσ hσ0,
      valueMemB_perm (hσ (s + i) (problem.domains.getD i Dom.empty)) v]

/-- `Fits` (the Prop-level box membership) is invariant under a permuting
presentation. -/
theorem Fits_reorderAuxWith {σ : Nat → Domain → Domain}
    (hσ : ∀ s d, (σ s d).Perm d) (hσ0 : ∀ s, σ s Dom.empty = Dom.empty)
    (s : Nat) (ds : List Domain) (a : Assignment) :
    a.Fits (reorderAuxWith σ s ds) ↔ a.Fits ds := by
  constructor
  · rintro ⟨hlen, hmem⟩
    refine ⟨by rw [reorderAuxWith_length] at hlen; exact hlen, ?_⟩
    intro i v hv
    have h' : v ∈ (reorderAuxWith σ s ds).getD i Dom.empty := by
      simpa only [LeanFzn.Solver.Propagation.domEmpty_eq] using hmem i v hv
    rw [reorderAuxWith_getD hσ hσ0] at h'
    exact (hσ (s + i) (ds.getD i Dom.empty)).dom_mem_iff.mp h'
  · rintro ⟨hlen, hmem⟩
    refine ⟨by rw [reorderAuxWith_length]; exact hlen, ?_⟩
    intro i v hv
    have h' : v ∈ ds.getD i Dom.empty := by
      simpa only [LeanFzn.Solver.Propagation.domEmpty_eq] using hmem i v hv
    have h2 : v ∈ (reorderAuxWith σ s ds).getD i Dom.empty := by
      rw [reorderAuxWith_getD hσ hσ0]
      exact (hσ (s + i) (ds.getD i Dom.empty)).dom_mem_iff.mpr h'
    simpa only [LeanFzn.Solver.Propagation.domEmpty_eq] using h2

/-- `SlotOK` (the gate's slot-range fact) only reads the slot count and the
domain's non-emptiness. -/
theorem SlotOK_reorderAuxWith {σ : Nat → Domain → Domain}
    (hσ : ∀ s d, (σ s d).Perm d) (s : Nat) (ds : List Domain) (i : Nat)
    (h : SlotOK ds i) : SlotOK (reorderAuxWith σ s ds) i := by
  obtain ⟨d, hd, hne⟩ := h
  refine ⟨σ (s + i) d, ?_, ?_⟩
  · rw [reorderAuxWith_getElem?, hd]; rfl
  · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil (Dom.enum d) hne
    exact fun he => by
      simpa [he] using (hσ (s + i) d).symm.subset hx

/-- The executable source gate `gateOk` transfers along a permuting
presentation. -/
theorem gateOk_reorderAuxWith {σ : Nat → Domain → Domain}
    (hσ : ∀ s d, (σ s d).Perm d) (s : Nat)
    {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (h : gateOk problem = true) :
    gateOk { problem with domains := reorderAuxWith σ s problem.domains } = true := by
  simp only [gateOk, List.all_eq_true, Bool.and_eq_true] at h ⊢
  intro d' hd'
  obtain ⟨d, hd, hp⟩ := mem_reorderAuxWith_perm hσ s problem.domains hd'
  have hdd := h d hd
  have hlen : d'.length = d.length := hp.length_eq
  refine ⟨?_, ?_⟩
  · simpa [hlen] using hdd.1
  · intro x hx
    exact hdd.2 x (hp.mem_iff.mp hx)

/-- The pruning kit gate `domPruningOkB` transfers along a permuting
presentation. -/
theorem domPruningOkB_reorderAuxWith {σ : Nat → Domain → Domain}
    (hσ : ∀ s d, (σ s d).Perm d) (s : Nat)
    {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (h : domPruningOkB problem = true) :
    domPruningOkB { problem with domains := reorderAuxWith σ s problem.domains }
      = true := by
  simp only [domPruningOkB, Bool.and_eq_true, List.all_eq_true] at h ⊢
  obtain ⟨⟨hview, hlin⟩, hshape⟩ := h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro d' hd' v hv
    obtain ⟨d, hd, hp⟩ := mem_reorderAuxWith_perm hσ s problem.domains hd'
    exact hview d hd v (hp.mem_iff.mp hv)
  · intro c hc
    have hc' := hlin c hc
    by_cases haba : ∃ is k, c = DomConstraint.arrayBoolAndSlot is k
    · obtain ⟨is, k, rfl⟩ := haba
      change (is.all (fun i => decide (i < problem.domains.length) &&
          (Dom.enum (problem.domains.getD i Dom.empty)).all (fun v => match v with
            | .bool _ => true | _ => false))) = true at hc'
      rw [List.all_eq_true] at hc' ⊢
      intro i hi
      have h1 := hc' i hi
      rw [Bool.and_eq_true] at h1 ⊢
      obtain ⟨hlen, hbool⟩ := h1
      refine ⟨by rw [reorderAuxWith_length]; exact hlen, ?_⟩
      have hget : (reorderAuxWith σ s problem.domains).getD i Dom.empty =
          σ (s + i) (problem.domains.getD i Dom.empty) := by
        rw [List.getD_eq_getElem?_getD, reorderAuxWith_getElem?,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (of_decide_eq_true hlen)]
        rfl
      rw [hget]
      exact aba_all_bool_perm
        (hσ (s + i) (problem.domains.getD i Dom.empty)) hbool
    · cases c with
      | arrayBoolAndSlot is k => exact absurd ⟨is, k, rfl⟩ haba
      | _ =>
          first
            | exact hc'
            | (rw [reorderAuxWith_length] at ⊢
               exact hc')
  · intro d' hd'
    obtain ⟨d, hd, hp⟩ := mem_reorderAuxWith_perm hσ s problem.domains hd'
    have hd3 := hshape d hd
    rw [Bool.or_eq_true] at hd3 ⊢
    rcases hd3 with h3 | h3
    · left
      rw [List.all_eq_true] at h3 ⊢
      intro x hx
      exact h3 x (hp.mem_iff.mp hx)
    · right
      rw [List.all_eq_true] at h3 ⊢
      intro x hx
      exact h3 x (hp.mem_iff.mp hx)

/-- The mixed kit gate transfers along a permuting presentation. -/
theorem mixedKitGateB_reorderAuxWith {σ : Nat → Domain → Domain}
    (hσ : ∀ s d, (σ s d).Perm d) (s : Nat)
    {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (h : mixedKitGateB problem = true) :
    mixedKitGateB { problem with domains := reorderAuxWith σ s problem.domains }
      = true := by
  simp only [mixedKitGateB, Bool.and_eq_true, List.all_eq_true] at h ⊢
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨?_, ?_⟩
  · intro d' hd'
    obtain ⟨d, hd, hp⟩ := mem_reorderAuxWith_perm hσ s problem.domains hd'
    obtain ⟨hint, hkind, hnodup⟩ := h₁ d hd
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      exact hint x (hp.mem_iff.mp hx)
    · rw [Bool.or_eq_true] at hkind ⊢
      rcases hkind with h3 | h3
      · left
        rw [List.all_eq_true] at h3 ⊢
        intro x hx
        exact h3 x (hp.mem_iff.mp hx)
      · right
        rw [List.all_eq_true] at h3 ⊢
        intro x hx
        exact h3 x (hp.mem_iff.mp hx)
    · rw [decide_eq_true_eq] at hnodup ⊢
      exact (hp.map Value.intView).nodup_iff.mpr hnodup
  · intro c hc
    have hc' := h₂ c hc
    rwa [reorderAuxWith_length]


/-! ## §8 The objective-biased route and its certified transfer -/

/-- The objective-biased presentation of a box: the `reorderAuxWith` instance
at `sortDomBias`. -/
def reorderAuxBias (dcs : List DomConstraint) (db : List Clause) :
    Nat → List Domain → List Domain :=
  reorderAuxWith (sortDomBias dcs db)

/-- The biased presentation does not change the number of slots. -/
theorem reorderAuxBias_length (dcs : List DomConstraint) (db : List Clause) :
    ∀ (s : Nat) (ds : List Domain),
      (reorderAuxBias dcs db s ds).length = ds.length :=
  reorderAuxWith_length (sortDomBias dcs db)

/-- The `i`-th domain of the biased box is the biased order of the `i`-th
domain of the original box. -/
theorem reorderAuxBias_getElem? (dcs : List DomConstraint) (db : List Clause)
    (s : Nat) : ∀ (ds : List Domain) (i : Nat),
    (reorderAuxBias dcs db s ds)[i]? = (ds[i]?).map (sortDomBias dcs db (s + i)) :=
  reorderAuxWith_getElem? (sortDomBias dcs db) s

/-- Every domain of the biased box is a permutation of a domain of the
original box. -/
theorem mem_reorderAuxBias_perm (dcs : List DomConstraint) (db : List Clause)
    (s : Nat) : ∀ (ds : List Domain) {d' : Domain},
    d' ∈ reorderAuxBias dcs db s ds → ∃ d ∈ ds, d'.Perm d :=
  mem_reorderAuxWith_perm (sortDomBias_perm dcs db) s

/-- The biased box's `getD` is the biased order of the original `getD`. -/
theorem getD_reorderAuxBias (dcs : List DomConstraint) (db : List Clause)
    (s : Nat) (ds : List Domain) (i : Nat) :
    (reorderAuxBias dcs db s ds).getD i Dom.empty
      = sortDomBias dcs db (s + i) (ds.getD i Dom.empty) :=
  reorderAuxWith_getD (sortDomBias_perm dcs db) (sortDomBias_nil dcs db) s ds i

/-- `fitsB` at the biased box is the original `fitsB`. -/
theorem fitsB_reorderAuxBias (dcs : List DomConstraint) (db : List Clause)
    (s : Nat) (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit)
    (a : Assignment) :
    fitsB { problem with domains := reorderAuxBias dcs db s problem.domains } a
      = fitsB problem a :=
  fitsB_reorderAuxWith (sortDomBias_perm dcs db) (sortDomBias_nil dcs db) s problem a

/-- `Fits` (the Prop-level box membership) is invariant under the biased
presentation. -/
theorem Fits_reorderAuxBias (dcs : List DomConstraint) (db : List Clause)
    (s : Nat) (ds : List Domain) (a : Assignment) :
    a.Fits (reorderAuxBias dcs db s ds) ↔ a.Fits ds :=
  Fits_reorderAuxWith (sortDomBias_perm dcs db) (sortDomBias_nil dcs db) s ds a

/-- `SlotOK` transfers along the biased presentation. -/
theorem SlotOK_reorderAuxBias (dcs : List DomConstraint) (db : List Clause)
    (s : Nat) (ds : List Domain) (i : Nat) (h : SlotOK ds i) :
    SlotOK (reorderAuxBias dcs db s ds) i :=
  SlotOK_reorderAuxWith (sortDomBias_perm dcs db) s ds i h

/-- The executable source gate `gateOk` transfers along the biased
presentation. -/
theorem gateOk_reorderAuxBias (dcs : List DomConstraint) (db : List Clause)
    (s : Nat) {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (h : gateOk problem = true) :
    gateOk { problem with domains := reorderAuxBias dcs db s problem.domains }
      = true :=
  gateOk_reorderAuxWith (sortDomBias_perm dcs db) s h

/-- The pruning kit gate `domPruningOkB` transfers along the biased
presentation. -/
theorem domPruningOkB_reorderAuxBias (dcs : List DomConstraint) (db : List Clause)
    (s : Nat) {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (h : domPruningOkB problem = true) :
    domPruningOkB { problem with domains := reorderAuxBias dcs db s problem.domains }
      = true :=
  domPruningOkB_reorderAuxWith (sortDomBias_perm dcs db) s h

/-- The mixed kit gate transfers along the biased presentation. -/
theorem mixedKitGateB_reorderAuxBias (dcs : List DomConstraint) (db : List Clause)
    (s : Nat) {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (h : mixedKitGateB problem = true) :
    mixedKitGateB { problem with domains := reorderAuxBias dcs db s problem.domains }
      = true :=
  mixedKitGateB_reorderAuxWith (sortDomBias_perm dcs db) s h

/-- With no trailing bound the biased presentation is exactly the
unbiased one: `sortDomBias` falls back to `sortDom` at every slot. -/
theorem reorderAuxBias_eq_reorderAux_of_noBias (dcs : List DomConstraint)
    (db : List Clause) (h : ∀ s, biasAt dcs s = none) :
    ∀ (s : Nat) (ds : List Domain),
      reorderAuxBias dcs db s ds = reorderAux dcs db s ds := by
  intro s ds
  induction ds generalizing s with
  | nil => rfl
  | cons d rest ih =>
      have hhead : sortDomBias dcs db s d = sortDom dcs db s d := by
        unfold sortDomBias
        rw [h s]
        by_cases hsmall : enumSmallB d = true
        · rw [if_pos hsmall]
        · rw [if_neg hsmall]
          unfold sortDom
          rw [if_neg hsmall]
      change sortDomBias dcs db s d :: reorderAuxBias dcs db (s + 1) rest
        = sortDom dcs db s d :: reorderAux dcs db (s + 1) rest
      rw [hhead, ih (s + 1)]

/-- **THE OBJECTIVE-BIASED PRESENTATION**: every domain in the biased order
(the activity-ordered presentation is the fallback when no trailing bound is
detected). -/
def heurDomainsBias (p : CompiledProblem DomConstraint) : List Domain :=
  reorderAuxBias p.constraints (actDb p) 0 p.domains

/-- The unbiased reference: without a trailing bound the biased presentation
is the activity-ordered presentation of §4. -/
theorem heurDomainsBias_eq_heurDomains_of_noBias (p : CompiledProblem DomConstraint)
    (h : biasSlot? p.constraints = none) :
    heurDomainsBias p = heurDomains p := by
  unfold heurDomainsBias heurDomains
  exact reorderAuxBias_eq_reorderAux_of_noBias p.constraints (actDb p)
    (by intro s; simp [biasAt, h]) 0 p.domains

/-- **THE OBJECTIVE-BIASED PROBLEM**: the LCG problem with its domains
presented in objective-biased order. -/
def heurProblemBias (p : CompiledProblem DomConstraint) :
    LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
  { lcgProblem p with domains := heurDomainsBias p }

/-- The clamped propagator list at the objective-biased box. -/
def heurPropsBias (p : CompiledProblem DomConstraint) : List Propagator :=
  clampProps (heurDomainsBias p) (p.constraints.filterMap propagatorOfProved)

/-- `fitsB` at the objective-biased problem is the compiled problem's
`fitsB`. -/
theorem fitsB_heurBias (p : CompiledProblem DomConstraint) (a : Assignment) :
    fitsB (heurProblemBias p) a = fitsB (lcgProblem p) a := by
  rw [Bool.eq_iff_iff, fitsB_iff, fitsB_iff]
  show a.Fits (heurDomainsBias p) ↔ a.Fits p.domains
  exact Fits_reorderAuxBias p.constraints (actDb p) 0 p.domains a

/-- The compiled leaf is unchanged by the biased presentation. -/
theorem heurLeafBias_eq (p : CompiledProblem DomConstraint) :
    lcgLeaf p = chronologicalLeaf (heurProblemBias p) DomConstraint.satisfiedB := by
  funext a
  simp only [lcgLeaf, chronologicalLeaf]
  rw [fitsB_heurBias p a]
  rfl

/-- The compiled input gate transfers to the objective-biased box. -/
theorem heurCompiledInputBias {p : CompiledProblem DomConstraint}
    (h : lcgRouteGateMixed p = true) : CompiledInput (lcgLeaf p) (heurProblemBias p) := by
  simp only [lcgRouteGateMixed, Bool.and_eq_true] at h
  exact ⟨heurLeafBias_eq p,
    gateOk_reorderAuxBias p.constraints (actDb p) 0 (problem := lcgProblem p) h.1.1,
    domPruningOkB_reorderAuxBias p.constraints (actDb p) 0
      (problem := lcgProblem p) h.1.2⟩

/-- The mixed kit gate transfers to the objective-biased box. -/
theorem heurGateBias {p : CompiledProblem DomConstraint}
    (h : lcgRouteGateMixed p = true) : mixedKitGateB (heurProblemBias p) = true := by
  simp only [lcgRouteGateMixed, Bool.and_eq_true,
    LcgMixedCompiledKit.mixedKitGateFastB_eq] at h
  exact mixedKitGateB_reorderAuxBias p.constraints (actDb p) 0
    (problem := lcgProblem p) h.2

/-- The seed database stays pool-aligned at the objective-biased box. -/
theorem heurAlignedBias {p : CompiledProblem DomConstraint}
    (h : lcgRouteGateMixed p = true) :
    DatabaseAligned (heurDomainsBias p) (seedClauses p.constraints) := by
  have hslot := slots_of_mixedGate (lcgInputMixed h)
    (by simp only [lcgRouteGateMixed, Bool.and_eq_true,
      LcgMixedCompiledKit.mixedKitGateFastB_eq] at h; exact h.2)
  refine seedClauses_aligned_of_slotOK fun dc hdc s hs => ?_
  exact SlotOK_reorderAuxBias p.constraints (actDb p) 0 (lcgProblem p).domains s
    (hslot dc hdc s hs)

/-- **THE OBJECTIVE-BIASED MIXED KIT**: every kit obligation at the biased box
is derived from the same gates. -/
theorem heurKitBias {p : CompiledProblem DomConstraint}
    (h : lcgRouteGateMixed p = true) :
    MixedLcgKit (lcgLeaf p) (heurDomainsBias p) (seedClauses p.constraints)
      p.constraints (p.constraints.filterMap propagatorOfProved)
      (heurPropsBias p) :=
  kit_of_compiled_mixed (heurCompiledInputBias h) (heurGateBias h)
    (lcgSeedCanonical p) (heurAlignedBias h)

/-- The route gate supplies the sparse frame gate at the biased box. -/
theorem heurFrameGateBias {p : CompiledProblem DomConstraint}
    (h : lcgRouteGateMixed p = true) :
    ∀ {cfg : SchedulerConfig (lcgLeaf p)},
      SupportedReach (heurDomainsBias p) (seedClauses p.constraints) (heurPropsBias p) cfg →
        FrameNonempty cfg := by
  intro cfg hreach
  exact LeanFzn.Solver.UIP.FrameLive.frameNonempty_of_gateOk (problem := heurProblemBias p)
    (heurCompiledInputBias h).gate (by rfl) hreach

/-- **THE OBJECTIVE-BIASED SCHEDULED RUN**: the certified scheduled LCG entry
on the objective-biased presentation of the compiled problem. -/
def lcgRunHeurBias (p : CompiledProblem DomConstraint)
    (hgate : ∀ {cfg : SchedulerConfig (lcgLeaf p)},
      SupportedReach (heurDomainsBias p) (seedClauses p.constraints)
        (heurPropsBias p) cfg → FrameNonempty cfg) (prio : List Nat := []) (actBump : Bool := false) :
    DriverResult (lcgLeaf p) :=
  solve_sched (heurDomainsBias p) (seedClauses p.constraints) (heurPropsBias p)
    (lcgSeedEntailed p) (PropScheduler.init (heurPropsBias p))
    (clampProps_local (heurDomainsBias p) p.constraints)
    (PropSchedulerOK.init (heurPropsBias p)) hgate prio actBump

/-- The objective-biased run is the certified kernel at the biased box. -/
theorem lcgRunHeurBias_eq_solve (p : CompiledProblem DomConstraint)
    (hgate : ∀ {cfg : SchedulerConfig (lcgLeaf p)},
      SupportedReach (heurDomainsBias p) (seedClauses p.constraints)
        (heurPropsBias p) cfg → FrameNonempty cfg) (prio : List Nat := []) (actBump : Bool := false) :
    lcgRunHeurBias p hgate prio actBump = LcgPhaseKernel.solve (heurDomainsBias p)
      (seedClauses p.constraints) (heurPropsBias p) (lcgSeedEntailed p) hgate prio actBump :=
  solve_sched_eq _ _ _ _ _ _ _ hgate prio actBump

/-- **SAT SOUNDNESS AT THE ORIGINAL BOX**: the broadly biased run reports a
witness that is a genuine solution of the compiled problem as given. -/
theorem lcgRunHeurBias_sat {p : CompiledProblem DomConstraint} {prio : List Nat} {actBump : Bool}
    (h : lcgRouteGateMixed p = true) {a : List Value}
    (hrun : lcgRunHeurBias p (heurFrameGateBias h) prio actBump = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  have hr := hrun
  rw [lcgRunHeurBias_eq_solve p (heurFrameGateBias h) prio actBump] at hr
  have hs := solve_sat_solution_of_kit_mixed (heurKitBias h) (lcgSeedEntailed p)
    (heurFrameGateBias h) hr
  have hl := hs.1
  simp only [lcgLeaf, chronologicalLeaf, lcgProblem, Bool.and_eq_true] at hl
  refine ⟨LeanFzn.Solver.UIP.fits_mem_allAssigns ?_, hl.2.1⟩
  exact (Fits_reorderAuxBias p.constraints (actDb p) 0 (lcgProblem p).domains a).mp hs.2

/-- **UNSAT COMPLETENESS AT THE ORIGINAL BOX**: the biased run's refutation
excludes every solution of the compiled problem as given. -/
theorem lcgRunHeurBias_unsat {p : CompiledProblem DomConstraint} {prio : List Nat} {actBump : Bool}
    (h : lcgRouteGateMixed p = true)
    (hrun : lcgRunHeurBias p (heurFrameGateBias h) prio actBump = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  have hex : ∀ b, b ∈ allAssigns p.domains → accepts p b = true → False := by
    intro b hb ha
    have hr := hrun
    rw [lcgRunHeurBias_eq_solve p (heurFrameGateBias h) prio actBump] at hr
    have hn := solve_unsat_excludes_of_kit_mixed (heurKitBias h) (lcgSeedEntailed p)
      (heurFrameGateBias h) hr
    apply hn b
    have hf : Assignment.Fits p.domains b :=
      LeanFzn.Solver.Propagation.allAssigns_fits p.domains b hb
    refine ⟨?_, (Fits_reorderAuxBias p.constraints (actDb p) 0
      (lcgProblem p).domains b).mpr hf⟩
    simp only [lcgLeaf, chronologicalLeaf, lcgProblem, Bool.and_eq_true]
    exact ⟨fitsB_iff.mpr hf, ha,
      List.all_eq_true.mpr fun c hc =>
        seedClauses_any_satisfiedB (fun dc hdc => List.all_eq_true.mp ha dc hdc) c hc⟩
  intro b hb
  cases ha : accepts p b with
  | false => rfl
  | true => exact False.elim (hex b hb ha)

/-- **TOTALITY**: the objective-biased run always reports a verdict. -/
theorem lcgRunHeurBias_verdict (p : CompiledProblem DomConstraint)
    (hgate : ∀ {cfg : SchedulerConfig (lcgLeaf p)},
      SupportedReach (heurDomainsBias p) (seedClauses p.constraints)
        (heurPropsBias p) cfg → FrameNonempty cfg) (prio : List Nat := []) (actBump : Bool := false) :
    (∃ a, lcgRunHeurBias p hgate prio actBump = .sat a) ∨
      lcgRunHeurBias p hgate prio actBump = .unsat := by
  cases h : lcgRunHeurBias p hgate prio actBump with
  | sat a => exact Or.inl ⟨a, rfl⟩
  | unsat => exact Or.inr rfl

/-! ## §9 The objective-biased public entry

`solveCompiledLcgHeurBias` is the public compiled entry with the
objective-biased LCG branch; its SAT/UNSAT/totality statements are the ones
the branch-and-bound solver consumes, and they are stated at the problem AS
GIVEN. The activity-ordered `solveCompiledLcgHeur` of §5 remains available as
the unbiased reference. -/

/-- **THE OBJECTIVE-BIASED COMPILED ENTRY**: the same route as
`solveCompiledLcgHeur`, with the LCG branch running on the objective-biased
presentation (`lcgRunHeurBias`). -/
def solveCompiledLcgHeurBias (p : CompiledProblem DomConstraint)
    (prio : List Nat := []) (actBump : Bool := false) : SearchResult :=
  if hg : lcgRouteGateMixed p = true then
    match lcgRunHeurBias p (heurFrameGateBias hg) prio actBump with
    | .sat a => .sat a
    | .unsat => .unsat
  else
    LeanFzn.Solver.Chronological.solve (lcgProblem p) DomConstraint.satisfiedB
      (p.constraints.filterMap propagatorOfProved) (domPruningKit (lcgProblem p))

/-- The objective-biased entry reports source solutions. -/
theorem solveCompiledLcgHeurBias_sat {p : CompiledProblem DomConstraint}
    {prio : List Nat} {actBump : Bool}
    {a : List Value} (h : solveCompiledLcgHeurBias p prio actBump = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  unfold solveCompiledLcgHeurBias at h
  split at h
  · rename_i hg
    split at h
    · rename_i hr
      cases h
      exact lcgRunHeurBias_sat hg hr
    · cases h
  · have hs := LeanFzn.Solver.Chronological.solve_sat_correct
      (fun c a => DomConstraint.satisfiedB_iff c a) h
    exact ⟨LeanFzn.Solver.UIP.fits_mem_allAssigns hs.1,
      List.all_eq_true.mpr (fun c hc =>
        (DomConstraint.satisfiedB_iff c a).mpr (hs.2 c hc))⟩

/-- The objective-biased entry's refutation excludes every source solution. -/
theorem solveCompiledLcgHeurBias_unsat {p : CompiledProblem DomConstraint}
    {prio : List Nat} {actBump : Bool}
    (h : solveCompiledLcgHeurBias p prio actBump = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  unfold solveCompiledLcgHeurBias at h
  split at h
  · rename_i hg
    split at h
    · cases h
    · rename_i hr
      exact lcgRunHeurBias_unsat hg hr
  · have hn := LeanFzn.Solver.Chronological.solve_pruned_unsat_correct
      (fun c a => DomConstraint.satisfiedB_iff c a)
      (fun c hc _ hsol => seedClauses_satisfiedBy
        (fun dc hdc => hsol.2 dc hdc) c hc) h
    intro b hb
    cases ha : accepts p b with
    | false => rfl
    | true =>
        refine absurd ?_ hn
        exact ⟨b, LeanFzn.Solver.Propagation.allAssigns_fits p.domains b hb,
          fun c hc => (DomConstraint.satisfiedB_iff c b).mp
            (List.all_eq_true.mp ha c hc)⟩

/-- The objective-biased entry is total: it never reports `unknown`. -/
theorem solveCompiledLcgHeurBias_verdict (p : CompiledProblem DomConstraint)
    (prio : List Nat := []) (actBump : Bool := false) :
    solveCompiledLcgHeurBias p prio actBump ≠ .unknown := by
  unfold solveCompiledLcgHeurBias
  split
  · rename_i hg
    cases lcgRunHeurBias p (heurFrameGateBias hg) prio actBump <;> simp
  · exact LeanFzn.Solver.Chronological.solve_total _ _ _ _

/-! ## §10 Search-heuristic options (PLAN §3.0 item 5)

`HeurOpts` selects the heuristic inputs of the LCG branch independently, so
each can be A/B-measured on its own:

* `objPrio` (O1 slot priority): when the problem carries a trailing
  branch-and-bound bound (`biasSlot?`), the objective slot gets the initial
  priority `OBJ_SCORE`, so the S2 rule decides it first while it is live;
* `objBias` (O1 value order): run the objective-biased presentation
  (`solveCompiledLcgHeurBias`) instead of the activity-ordered one;
* `actBump` (S2 dynamic activity): every learn/backjump bumps the learned
  clause's slots (`SelectPolicy.bumpPrio`).

The options only choose the priority vector and the presentation; every
choice runs a certified entry, so the SAT/UNSAT/totality statements below
hold for all options. The default `{}` is exactly `solveCompiledLcgHeur p`. -/

/-- Independent heuristic toggles of the LCG branch (all off by default). -/
structure HeurOpts where
  objPrio : Bool := false
  objBias : Bool := false
  actBump : Bool := false
  deriving Repr, Inhabited

/-- The initial priority of the objective slot under `objPrio`. -/
def OBJ_SCORE : Nat := 512

/-- The initial slot-priority vector: `[]` (the S1 rule) unless a heuristic
needs scores; then one score per slot, `OBJ_SCORE` at the objective slot when
`objPrio` is on and the problem carries an improving bound, `0` elsewhere. -/
def heurPrio (o : HeurOpts) (p : CompiledProblem DomConstraint) : List Nat :=
  if o.objPrio || o.actBump then
    let base := List.replicate p.domains.length 0
    match (if o.objPrio then biasSlot? p.constraints else none) with
    | some (s, _) => base.set s OBJ_SCORE
    | none => base
  else []

/-- **THE OPTIONED COMPILED ENTRY**: the activity-ordered (or, under
`objBias`, the objective-biased) certified entry run with the options'
priority vector and activity toggle. -/
def solveCompiledLcgHeurOpts (o : HeurOpts) (p : CompiledProblem DomConstraint) :
    SearchResult :=
  if o.objBias then solveCompiledLcgHeurBias p (heurPrio o p) o.actBump
  else solveCompiledLcgHeur p (heurPrio o p) o.actBump

/-- The default options are the unchanged public entry. -/
theorem solveCompiledLcgHeurOpts_default (p : CompiledProblem DomConstraint) :
    solveCompiledLcgHeurOpts {} p = solveCompiledLcgHeur p := rfl

/-- The optioned entry reports source solutions. -/
theorem solveCompiledLcgHeurOpts_sat {o : HeurOpts} {p : CompiledProblem DomConstraint}
    {a : List Value} (h : solveCompiledLcgHeurOpts o p = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  unfold solveCompiledLcgHeurOpts at h
  split at h
  · exact solveCompiledLcgHeurBias_sat h
  · exact solveCompiledLcgHeur_sat h

/-- The optioned entry's refutation excludes every source solution. -/
theorem solveCompiledLcgHeurOpts_unsat {o : HeurOpts} {p : CompiledProblem DomConstraint}
    (h : solveCompiledLcgHeurOpts o p = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  unfold solveCompiledLcgHeurOpts at h
  split at h
  · exact solveCompiledLcgHeurBias_unsat h
  · exact solveCompiledLcgHeur_unsat h

/-- The optioned entry is total. -/
theorem solveCompiledLcgHeurOpts_verdict (o : HeurOpts) (p : CompiledProblem DomConstraint) :
    solveCompiledLcgHeurOpts o p ≠ .unknown := by
  unfold solveCompiledLcgHeurOpts
  split
  · exact solveCompiledLcgHeurBias_verdict _ _ _
  · exact solveCompiledLcgHeur_verdict _ _ _

/-! ## §11 Return-beside stats twins (K0)

`--stats` engine counters. These wrappers return the certified verdict
together with the terminal `SearchStats` of the identical run; their first
component is proved equal to the corresponding certified entry, so no claim
changes. The counters are observations only and never feed back into search. -/

/-- Stats twin of `lcgRunHeur`: the activity-ordered scheduled run with its
terminal work counters. -/
def lcgRunHeurStats (p : CompiledProblem DomConstraint)
    (hgate : ∀ {cfg : SchedulerConfig (lcgLeaf p)},
      SupportedReach (heurDomains p) (seedClauses p.constraints) (heurProps p) cfg →
        FrameNonempty cfg) (prio : List Nat := []) (actBump : Bool := false) :
    DriverResult (lcgLeaf p) × SearchStats :=
  solve_schedStats (heurDomains p) (seedClauses p.constraints) (heurProps p)
    (lcgSeedEntailed p) (PropScheduler.init (heurProps p))
    (clampProps_local (heurDomains p) p.constraints)
    (PropSchedulerOK.init (heurProps p)) hgate prio actBump

/-- The instrumented activity-ordered run decides exactly `lcgRunHeur`. -/
theorem lcgRunHeurStats_fst (p : CompiledProblem DomConstraint)
    (hgate : ∀ {cfg : SchedulerConfig (lcgLeaf p)},
      SupportedReach (heurDomains p) (seedClauses p.constraints) (heurProps p) cfg →
        FrameNonempty cfg) (prio : List Nat := []) (actBump : Bool := false) :
    (lcgRunHeurStats p hgate prio actBump).1 = lcgRunHeur p hgate prio actBump :=
  solve_schedStats_fst _ _ _ _ _ _ _ hgate prio actBump

/-- Stats twin of `lcgRunHeurBias`. -/
def lcgRunHeurBiasStats (p : CompiledProblem DomConstraint)
    (hgate : ∀ {cfg : SchedulerConfig (lcgLeaf p)},
      SupportedReach (heurDomainsBias p) (seedClauses p.constraints)
        (heurPropsBias p) cfg → FrameNonempty cfg) (prio : List Nat := []) (actBump : Bool := false) :
    DriverResult (lcgLeaf p) × SearchStats :=
  solve_schedStats (heurDomainsBias p) (seedClauses p.constraints) (heurPropsBias p)
    (lcgSeedEntailed p) (PropScheduler.init (heurPropsBias p))
    (clampProps_local (heurDomainsBias p) p.constraints)
    (PropSchedulerOK.init (heurPropsBias p)) hgate prio actBump

/-- The instrumented objective-biased run decides exactly `lcgRunHeurBias`. -/
theorem lcgRunHeurBiasStats_fst (p : CompiledProblem DomConstraint)
    (hgate : ∀ {cfg : SchedulerConfig (lcgLeaf p)},
      SupportedReach (heurDomainsBias p) (seedClauses p.constraints)
        (heurPropsBias p) cfg → FrameNonempty cfg) (prio : List Nat := []) (actBump : Bool := false) :
    (lcgRunHeurBiasStats p hgate prio actBump).1
      = lcgRunHeurBias p hgate prio actBump :=
  solve_schedStats_fst _ _ _ _ _ _ _ hgate prio actBump

/-- Stats twin of `solveCompiledLcgHeur` (gate branch + chronological
fallback). -/
def solveCompiledLcgHeurStats (p : CompiledProblem DomConstraint)
    (prio : List Nat := []) (actBump : Bool := false) :
    SearchResult × SearchStats :=
  if hg : lcgRouteGateMixed p = true then
    match lcgRunHeurStats p (heurFrameGate hg) prio actBump with
    | (.sat a, st) => (.sat a, st)
    | (.unsat, st) => (.unsat, st)
  else
    LeanFzn.Solver.Chronological.solveWithStats (lcgProblem p) DomConstraint.satisfiedB
      (p.constraints.filterMap propagatorOfProved) (domPruningKit (lcgProblem p))

/-- The instrumented activity-ordered entry decides exactly
`solveCompiledLcgHeur`. -/
theorem solveCompiledLcgHeurStats_fst (p : CompiledProblem DomConstraint)
    (prio : List Nat := []) (actBump : Bool := false) :
    (solveCompiledLcgHeurStats p prio actBump).1
      = solveCompiledLcgHeur p prio actBump := by
  unfold solveCompiledLcgHeurStats solveCompiledLcgHeur
  by_cases hg : lcgRouteGateMixed p = true
  · rw [dif_pos hg, dif_pos hg]
    cases h : lcgRunHeur p (heurFrameGate hg) prio actBump with
    | sat a =>
        have hs := lcgRunHeurStats_fst p (heurFrameGate hg) prio actBump
        rw [h] at hs
        cases hstats : lcgRunHeurStats p (heurFrameGate hg) prio actBump with
        | mk d st =>
            rw [hstats] at hs
            subst hs
            rfl
    | unsat =>
        have hs := lcgRunHeurStats_fst p (heurFrameGate hg) prio actBump
        rw [h] at hs
        cases hstats : lcgRunHeurStats p (heurFrameGate hg) prio actBump with
        | mk d st =>
            rw [hstats] at hs
            subst hs
            rfl
  · rw [dif_neg hg, dif_neg hg]
    rfl

/-- Stats twin of `solveCompiledLcgHeurBias`. -/
def solveCompiledLcgHeurBiasStats (p : CompiledProblem DomConstraint)
    (prio : List Nat := []) (actBump : Bool := false) :
    SearchResult × SearchStats :=
  if hg : lcgRouteGateMixed p = true then
    match lcgRunHeurBiasStats p (heurFrameGateBias hg) prio actBump with
    | (.sat a, st) => (.sat a, st)
    | (.unsat, st) => (.unsat, st)
  else
    LeanFzn.Solver.Chronological.solveWithStats (lcgProblem p) DomConstraint.satisfiedB
      (p.constraints.filterMap propagatorOfProved) (domPruningKit (lcgProblem p))

/-- The instrumented objective-biased entry decides exactly
`solveCompiledLcgHeurBias`. -/
theorem solveCompiledLcgHeurBiasStats_fst (p : CompiledProblem DomConstraint)
    (prio : List Nat := []) (actBump : Bool := false) :
    (solveCompiledLcgHeurBiasStats p prio actBump).1
      = solveCompiledLcgHeurBias p prio actBump := by
  unfold solveCompiledLcgHeurBiasStats solveCompiledLcgHeurBias
  by_cases hg : lcgRouteGateMixed p = true
  · rw [dif_pos hg, dif_pos hg]
    cases h : lcgRunHeurBias p (heurFrameGateBias hg) prio actBump with
    | sat a =>
        have hs := lcgRunHeurBiasStats_fst p (heurFrameGateBias hg) prio actBump
        rw [h] at hs
        cases hstats : lcgRunHeurBiasStats p (heurFrameGateBias hg) prio actBump with
        | mk d st =>
            rw [hstats] at hs
            subst hs
            rfl
    | unsat =>
        have hs := lcgRunHeurBiasStats_fst p (heurFrameGateBias hg) prio actBump
        rw [h] at hs
        cases hstats : lcgRunHeurBiasStats p (heurFrameGateBias hg) prio actBump with
        | mk d st =>
            rw [hstats] at hs
            subst hs
            rfl
  · rw [dif_neg hg, dif_neg hg]
    rfl

/-- Stats twin of `solveCompiledLcgHeurOpts`. -/
def solveCompiledLcgHeurOptsStats (o : HeurOpts) (p : CompiledProblem DomConstraint) :
    SearchResult × SearchStats :=
  if o.objBias then solveCompiledLcgHeurBiasStats p (heurPrio o p) o.actBump
  else solveCompiledLcgHeurStats p (heurPrio o p) o.actBump

/-- The instrumented optioned entry decides exactly
`solveCompiledLcgHeurOpts`. -/
theorem solveCompiledLcgHeurOptsStats_fst (o : HeurOpts)
    (p : CompiledProblem DomConstraint) :
    (solveCompiledLcgHeurOptsStats o p).1 = solveCompiledLcgHeurOpts o p := by
  unfold solveCompiledLcgHeurOptsStats solveCompiledLcgHeurOpts
  split
  · rw [solveCompiledLcgHeurBiasStats_fst p (heurPrio o p) o.actBump]
  · rw [solveCompiledLcgHeurStats_fst p (heurPrio o p) o.actBump]

end LeanFzn.Integration.LcgHeur

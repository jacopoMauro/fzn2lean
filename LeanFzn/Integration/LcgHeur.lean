/-
File: LeanFzn/Integration/LcgHeur.lean

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

DAG: Integration.Lcg (the public route) -> this module -> Integration.Lcg's
public solve definitions.
-/
import LeanFzn.Integration.Lcg
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

/-- The value list with `(activity, source position, value)` keys. -/
def keyAux (dcs : List DomConstraint) (db : List Clause) (s : Nat) :
    Nat → Domain → List (Nat × Nat × Value)
  | _, [] => []
  | i, w :: rest => (valAct dcs db s w, i, w) :: keyAux dcs db s (i + 1) rest

/-- The keys of `keyAux` carry the original list: projecting them is the
identity. -/
theorem keyAux_map (dcs : List DomConstraint) (db : List Clause) (s i : Nat)
    (d : Domain) : (keyAux dcs db s i d).map (fun p => p.2.2) = d := by
  induction d generalizing i with
  | nil => rfl
  | cons w rest ih =>
      simp only [keyAux, List.map_cons]
      rw [ih]

/-- ACTIVITY ORDER of one domain: descending activity, ties in source order.
`mergeSort` on the `(activity, position)` key is the (unique) sorted
permutation, so already-key-sorted inputs — in particular all-zero activities,
where the key is the position alone — are left untouched. -/
def sortDom (dcs : List DomConstraint) (db : List Clause) (s : Nat) (d : Domain) : Domain :=
  ((keyAux dcs db s 0 d).mergeSort fun p q => decide (p.1 ≤ q.1)).map fun p => p.2.2

/-- The activity order of a whole box, slot-by-slot. -/
def reorderAux (dcs : List DomConstraint) (db : List Clause) :
    Nat → List Domain → List Domain
  | _, [] => []
  | s, d :: rest => sortDom dcs db s d :: reorderAux dcs db (s + 1) rest

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
    (d : Domain) : (sortDom dcs db s d).Perm d :=
  ((List.mergeSort_perm _ _).map _).trans (by rw [keyAux_map])

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
    valueMemB v d' = valueMemB v d := by
  rw [Bool.eq_iff_iff, valueMemB_iff, valueMemB_iff, h.mem_iff]

/-- The activity order of the empty domain is empty. -/
theorem sortDom_nil (dcs : List DomConstraint) (db : List Clause) (s : Nat) :
    sortDom dcs db s ([] : Domain) = [] := by
  simp only [sortDom, keyAux, List.mergeSort_nil, List.map_nil]

/-- The `i`-th domain of a presented box: the reordered box's `getD` is the
activity order of the original box's `getD`. -/
theorem getD_reorderAux {dcs : List DomConstraint} {db : List Clause} (s : Nat)
    (ds : List Domain) (i : Nat) :
    (reorderAux dcs db s ds).getD i []
      = sortDom dcs db (s + i) (ds.getD i []) := by
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
    change valueMemB v ((reorderAux dcs db s problem.domains).getD i [])
      = valueMemB v (problem.domains.getD i [])
    rw [getD_reorderAux,
      valueMemB_perm (sortDom_perm dcs db (s + i) (problem.domains.getD i [])) v]

/-- `Fits` (the Prop-level box membership) is invariant under the
presentation. -/
theorem Fits_reorderAux {dcs : List DomConstraint} {db : List Clause}
    (s : Nat) (ds : List Domain) (a : Assignment) :
    a.Fits (reorderAux dcs db s ds) ↔ a.Fits ds := by
  constructor
  · rintro ⟨hlen, hmem⟩
    refine ⟨by rw [reorderAux_length] at hlen; exact hlen, ?_⟩
    intro i v hv
    have h' := hmem i v hv
    rw [getD_reorderAux] at h'
    exact (sortDom_perm dcs db (s + i) (ds.getD i [])).mem_iff.mp h'
  · rintro ⟨hlen, hmem⟩
    refine ⟨by rw [reorderAux_length]; exact hlen, ?_⟩
    intro i v hv
    have h' := hmem i v hv
    rw [getD_reorderAux]
    exact (sortDom_perm dcs db (s + i) (ds.getD i [])).mem_iff.mpr h'

/-- `SlotOK` (the gate's slot-range fact) only reads the slot count and the
domain's non-emptiness. -/
theorem SlotOK_reorderAux {dcs : List DomConstraint} {db : List Clause}
    (s : Nat) (ds : List Domain) (i : Nat) (h : SlotOK ds i) :
    SlotOK (reorderAux dcs db s ds) i := by
  obtain ⟨d, hd, hne⟩ := h
  refine ⟨sortDom dcs db (s + i) d, ?_, ?_⟩
  · rw [reorderAux_getElem?, hd]; rfl
  · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil d hne
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
    rwa [reorderAux_length]
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

/-- **THE ACTIVITY-ORDERED SCHEDULED RUN**: the certified scheduled LCG entry
on the activity-ordered presentation of the compiled problem. -/
def lcgRunHeur (p : CompiledProblem DomConstraint) : DriverResult (lcgLeaf p) :=
  solve_sched (heurDomains p) (seedClauses p.constraints) (heurProps p)
    (lcgSeedEntailed p) (PropScheduler.init (heurProps p))
    (clampProps_local (heurDomains p) p.constraints)
    (PropSchedulerOK.init (heurProps p))

/-- The activity-ordered run is the certified kernel at the activity-ordered
box. -/
theorem lcgRunHeur_eq_solve (p : CompiledProblem DomConstraint) :
    lcgRunHeur p = LcgPhaseKernel.solve (heurDomains p)
      (seedClauses p.constraints) (heurProps p) (lcgSeedEntailed p) :=
  solve_sched_eq _ _ _ _ _ _ _

/-- **SAT SOUNDNESS AT THE ORIGINAL BOX**: the activity-ordered run reports a
witness that is a genuine solution of the compiled problem as given. -/
theorem lcgRunHeur_sat {p : CompiledProblem DomConstraint}
    (h : lcgRouteGateMixed p = true) {a : List Value}
    (hrun : lcgRunHeur p = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  have hr := hrun
  rw [lcgRunHeur_eq_solve p] at hr
  have hs := solve_sat_solution_of_kit_mixed (heurKit h) (lcgSeedEntailed p) hr
  have hl := hs.1
  simp only [lcgLeaf, chronologicalLeaf, lcgProblem, Bool.and_eq_true] at hl
  refine ⟨fits_mem_allAssigns p.domains a ?_, hl.2.1⟩
  exact (Fits_reorderAux 0 (lcgProblem p).domains a).mp hs.2

/-- **UNSAT COMPLETENESS AT THE ORIGINAL BOX**: the activity-ordered run's
refutation excludes every solution of the compiled problem as given. -/
theorem lcgRunHeur_unsat {p : CompiledProblem DomConstraint}
    (h : lcgRouteGateMixed p = true) (hrun : lcgRunHeur p = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  have hex : ∀ b, b ∈ allAssigns p.domains → accepts p b = true → False := by
    intro b hb ha
    have hr := hrun
    rw [lcgRunHeur_eq_solve p] at hr
    have hn := solve_unsat_excludes_of_kit_mixed (heurKit h) (lcgSeedEntailed p) hr
    apply hn b
    have hf : Assignment.Fits p.domains b :=
      ⟨mem_allAssigns_length p.domains b hb,
        fun i v hv => mem_allAssigns_fits p.domains b hb i v hv⟩
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
theorem lcgRunHeur_verdict (p : CompiledProblem DomConstraint) :
    (∃ a, lcgRunHeur p = .sat a) ∨ lcgRunHeur p = .unsat := by
  cases h : lcgRunHeur p with
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
def solveCompiledLcgHeur (p : CompiledProblem DomConstraint) : SearchResult :=
  if lcgRouteGateMixed p then
    match lcgRunHeur p with
    | .sat a => .sat a
    | .unsat => .unsat
  else
    LeanFzn.Solver.Chronological.solve (lcgProblem p) DomConstraint.satisfiedB
      (p.constraints.filterMap propagatorOfProved) (domPruningKit (lcgProblem p))

/-- The activity-ordered entry reports source solutions. -/
theorem solveCompiledLcgHeur_sat {p : CompiledProblem DomConstraint}
    {a : List Value} (h : solveCompiledLcgHeur p = .sat a) :
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
    exact ⟨fits_mem_allAssigns p.domains a hs.1,
      List.all_eq_true.mpr (fun c hc =>
        (DomConstraint.satisfiedB_iff c a).mpr (hs.2 c hc))⟩

/-- The activity-ordered entry's refutation excludes every source solution. -/
theorem solveCompiledLcgHeur_unsat {p : CompiledProblem DomConstraint}
    (h : solveCompiledLcgHeur p = .unsat) :
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
        exact ⟨b, ⟨mem_allAssigns_length p.domains b hb,
          fun i v hv => mem_allAssigns_fits p.domains b hb i v hv⟩,
          fun c hc => (DomConstraint.satisfiedB_iff c b).mp
            (List.all_eq_true.mp ha c hc)⟩

/-- The activity-ordered entry is total: it never reports `unknown`. -/
theorem solveCompiledLcgHeur_verdict (p : CompiledProblem DomConstraint) :
    solveCompiledLcgHeur p ≠ .unknown := by
  unfold solveCompiledLcgHeur
  split
  · cases lcgRunHeur p <;> simp
  · exact LeanFzn.Solver.Chronological.solve_total _ _ _ _

end LeanFzn.Integration.LcgHeur

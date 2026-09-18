import LeanFzn
import solver.Search
import solver.Propagators
import solver.Enum

/-!
# NoGood learning (PLAN.md 6.6, learning half)

This module implements the learning half of PLAN 6.6: decision-trail
NoGoods with the guarantee the plan demands — *before a NoGood may
prune search, prove that it is entailed by the original model and the
decisions above its valid scope*.

## The declarative clause semantics

A `NoGood` is a list of (slot index, value) pairs.  Its meaning is
the classical one: an assignment *violates* the NoGood when it fixes
every one of the pairs (all decisions match) — such an assignment is
excluded.

* `NoGood.Violated ng asg : Prop` — every pair `(i, v) ∈ ng` has
  `asg[i]? = some v`;
* `NoGood.violatedB` — the executable Boolean twin (via the checker's
  structural `Value.eqB`, whose `BEq` instance comes from
  `solver/Enum.lean`), with the agreement theorem `violatedB_iff`;
* `NoGood.EntailedOn ng leaf doms : Prop` — every leaf-passing
  assignment of `allAssigns doms` is *not* violated by `ng`.  This is
  the scope-limited entailment of PLAN 6.6: at the root it reads
  "entailed by the original model" (the leaf is the checker-validated
  model semantics); learning deeper in the tree yields NoGoods
  entailed over the same root scope because the decision trail they
  record is a prefix of every assignment they exclude.

## Learning from failed subtrees

The learned fact is the decision trail itself (`pairsOf`): when the
subtree below the decision prefix `pre` is exhausted fruitlessly, the
NoGood `pairsOf pre` is entailed at the root scope — no complete
assignment of the original domains that agrees with `pre` on all its
decisions can pass the leaf (`failedSubtree_entailed`).  This is
Sabori's weak decision-trail learning, at the verified level.

## NoGood-checked search

`nogoodSearch leaf ngs` is *exactly* leaf composition: the reference
`search` on `leaf && no learned NoGood violated`.  Because an entailed
NoGood excludes only leaf-rejecting assignments, the composed leaf
agrees with the original on every complete assignment, so the pruning
changes nothing semantically — the agreement theorem
`nogoodSearch_agrees` (PLAN 6.6's requirement: learning is
correctness-neutral when entailed).  The technical core is
`search_agree_aux`: two leaves that agree on `allAssigns doms` produce
the same search result from the root — the reference search only ever
evaluates its leaf at complete assignments of progressively shrunk
copies of the original domains.

## The learning loop

`learnSearch fuel leaf slots` is the executable learning search:
structurally the reference search, but when a first-branch subtree
fails, the decision trail `pairsOf (acc ++ [v])` is learned and prunes
the rest of the search.  The fuel bounds the number of learning steps
(a pure termination device: a smaller fuel weakens pruning, never
soundness); fuel 0 is the plain reference search (`learnSearch_zero`).
Its master theorems:

* `learnSearch_some` — a returned assignment is a complete assignment
  of the original domains passing the leaf (unconditional);
* `learnSearch_none` — a `none` verdict means every complete
  assignment fails the leaf (unconditional at the wrapper's entry:
  the NoGood set starts empty and every NoGood added during the run
  carries its own failed-subtree evidence inside the induction).
-/

namespace LeanFzn.Solver

open LeanFzn LeanFzn.Solution

/-! ## The NoGood representation and its semantics -/

/-- A NoGood over slot assignments: a set of (slot index, value)
    pairs.  An assignment that fixes *all* of the pairs violates the
    NoGood and is thereby excluded. -/
abbrev NoGood := List (Nat × Value)

/-- One pair of a NoGood matches an assignment: the assignment fixes
    slot `i` to `v`. -/
def pairMatchesB (asg : List Value) (p : Nat × Value) : Bool :=
  match asg[p.1]? with
  | some v => v.eqB p.2
  | none => false

namespace NoGood

/-- **The declarative clause semantics**: the assignment fixes every
    pair of the NoGood — all decisions match — so the assignment is
    excluded. -/
def Violated (ng : NoGood) (asg : List Value) : Prop :=
  ∀ p ∈ ng, asg[p.1]? = some p.2

/-- **The executable violated test**: every pair matches (via the
    checker's structural value equality). -/
def violatedB (ng : NoGood) (asg : List Value) : Bool :=
  ng.all (pairMatchesB asg)

/-- **The agreement theorem**: `violatedB` decides `Violated`. -/
theorem violatedB_iff {ng : NoGood} {asg : List Value} :
    violatedB ng asg = true ↔ ng.Violated asg := by
  simp only [violatedB, List.all_eq_true, pairMatchesB]
  constructor
  · intro h p hp
    have hh := h p hp
    cases hget : asg[p.1]? with
    | none => rw [hget] at hh; simp at hh
    | some v =>
        rw [hget] at hh
        have hv : v = p.2 := value_eqB_iff.mp hh
        rw [hv]
  · intro h p hp
    have hget : asg[p.1]? = some p.2 := h p hp
    show (match asg[p.1]? with
      | some v => v.eqB p.2
      | none => false) = true
    rw [hget]
    exact value_eqB_refl p.2

/-- **The scope-limited entailment** (PLAN 6.6: "entailed by the
    original model and the decisions above its valid scope"): every
    leaf-passing assignment of the scope `doms` is *not* violated by
    the NoGood — pruning with an entailed NoGood can only exclude
    assignments that already fail the leaf.  The leaf is the
    checker-validated model semantics, so entailment over
    `allAssigns doms` (the root scope) is entailment by the original
    model. -/
def EntailedOn (ng : NoGood) (leaf : List Value → Bool)
    (doms : List (List Value)) : Prop :=
  ∀ asg ∈ allAssigns doms, leaf asg = true → ¬ ng.Violated asg

end NoGood

/-! ## Decision trails -/

/-- The decision trail of a prefix assignment: one (position, value)
    pair per fixed decision, positions counted from `i`. -/
def pairsAux : Nat → List Value → NoGood
  | _, [] => []
  | i, v :: rest => (i, v) :: pairsAux (i+1) rest

/-- The decision trail of a prefix assignment: one (position, value)
    pair per fixed decision. -/
def pairsOf (l : List Value) : NoGood := pairsAux 0 l

/-- Membership in a decision trail: the pairs are exactly the prefix's
    (position, value) pairs. -/
theorem mem_pairsAux_iff : ∀ (pre : List Value) (p : Nat × Value) (i : Nat),
    p ∈ pairsAux i pre ↔
      ∃ k, k < pre.length ∧ p.1 = i + k ∧ pre[k]? = some p.2 := by
  intro pre
  induction pre with
  | nil => intro p i; simp [pairsAux]
  | cons w ws ih =>
      intro p i
      constructor
      · intro h
        simp only [pairsAux, List.mem_cons] at h
        rcases h with heq | hin
        · have hp1 : p.1 = i := congrArg Prod.fst heq
          have hp2 : p.2 = w := congrArg Prod.snd heq
          subst hp1
          subst hp2
          exact ⟨0, by simp, by omega, by simp⟩
        · obtain ⟨k, hk1, hk2, hk3⟩ := (ih p (i+1)).mp hin
          exact ⟨k+1, by simpa using hk1, by omega, hk3⟩
      · rintro ⟨k, hk1, hk2, hk3⟩
        cases k with
        | zero =>
            subst hk2
            have hpre : p.2 = w := by
              simpa [List.getElem?_cons_zero] using hk3.symm
            subst hpre
            exact List.mem_cons_self
        | succ k' =>
            simp only [pairsAux, List.mem_cons]
            right
            refine (ih p (i+1)).mpr ⟨k', by simpa using hk1, by omega, ?_⟩
            simpa using hk3

/-- **Violating a decision trail is agreeing with it**: an assignment
    violates `pairsAux i pre` exactly when it agrees with `pre`
    pointwise at the positions `i, i+1, …, i + pre.length - 1`. -/
theorem violated_pairsAux_iff {pre asg : List Value} {i : Nat} :
    (pairsAux i pre).Violated asg ↔
      ∀ k, k < pre.length → asg[i + k]? = pre[k]? := by
  constructor
  · intro h k hk
    have hp : (i + k, pre[k]'hk) ∈ pairsAux i pre := by
      refine (mem_pairsAux_iff pre _ i).mpr ⟨k, hk, by omega, ?_⟩
      rw [List.getElem?_eq_some_iff]
      exact ⟨hk, rfl⟩
    have hget := h _ hp
    show asg[i + k]? = pre[k]?
    have hproj1 : (i + k, pre[k]'hk).1 = i + k := rfl
    have hproj2 : (i + k, pre[k]'hk).2 = pre[k]'hk := rfl
    rw [hproj1, hproj2] at hget
    have hget2 : asg[i + k]? = some pre[k] := hget
    rw [hget2]
    exact (List.getElem?_eq_some_iff.mpr ⟨hk, rfl⟩).symm
  · intro h p hp
    obtain ⟨k, hk1, hk2, hk3⟩ := (mem_pairsAux_iff pre p i).mp hp
    have hagree := h k hk1
    show asg[p.1]? = some p.2
    rw [hk2]
    have hpre : pre[k]? = some p.2 := by
      rw [List.getElem?_eq_some_iff] at hk3 ⊢
      exact ⟨hk1, hk3.2 ▸ rfl⟩
    rw [hagree, hpre]

/-- An assignment violating the decision trail of a prefix extends
    that prefix. -/
theorem violated_pairsOf_split {pre asg : List Value}
    (h : (pairsOf pre).Violated asg) (_hlen : pre.length ≤ asg.length) :
    ∃ suf, asg = pre ++ suf := by
  have h2 : ∀ k, k < pre.length → asg[k]? = pre[k]? := by
    intro k hk
    have := (violated_pairsAux_iff (pre := pre) (asg := asg) (i := 0)).mp h k hk
    simpa using this
  refine ⟨asg.drop pre.length, ?_⟩
  apply List.ext_getElem?
  intro j
  by_cases hj : j < pre.length
  · rw [List.getElem?_append, if_pos hj]
    exact h2 j hj
  · rw [List.getElem?_append, if_neg (by omega : ¬ j < pre.length),
      List.getElem?_drop]
    have h3 : pre.length + (j - pre.length) = j := by omega
    rw [h3]

/-! ## Search agreement on complete assignments -/

/-- The reachable-search invariant: `slots` is the remaining suffix of
    a shrunk copy `doms` of the full slot family (same length, every
    domain pointwise-subset), and `acc` is a complete assignment of
    the consumed prefix. -/
def SearchInv (full : List (List Value)) (slots : List (List Value))
    (acc : List Value) : Prop :=
  ∃ doms : List (List Value),
    doms.length = full.length ∧
      (∀ k v, v ∈ getSlot doms k → v ∈ getSlot full k) ∧
      slots = doms.drop acc.length ∧
      acc ∈ allAssigns (doms.take acc.length)

/-- The invariant holds at the root. -/
theorem searchInv_root (full : List (List Value)) :
    SearchInv full full [] := by
  refine ⟨full, rfl, fun _ _ h => h, ?_, ?_⟩
  · simp
  · simp [allAssigns]

/-- `take` of a list longer than the bound is the whole list. -/
theorem take_all_le : ∀ {α : Type} (l : List α) (k : Nat), l.length ≤ k → l.take k = l := by
  intro α l
  induction l with
  | nil => intro k _; cases k with
    | zero => rfl
    | succ k' => rw [List.take_nil]
  | cons e es ih =>
      intro k hk
      cases k with
      | zero => simp at hk
      | succ k' =>
          have h' : es.length ≤ k' := by simpa using hk
          show List.take (k'+1) (e :: es) = e :: es
          rw [List.take_cons (by omega), Nat.succ_sub_one, ih k' h']

/-- `getSlot` of a dropped list at the head. -/
theorem getSlot_drop_zero : ∀ (doms : List (List Value)) (k : Nat),
    getSlot (doms.drop k) 0 = getSlot doms k := by
  intro doms k
  induction doms generalizing k with
  | nil => cases k with
    | zero => rfl
    | succ k' => rfl
  | cons e es ih =>
      cases k with
      | zero => rfl
      | succ k' =>
          show getSlot (es.drop k') 0 = getSlot (e :: es) (k'+1)
          simp only [getSlot]
          exact ih k'

/-- `getSlot` is the list index in range. -/
theorem getSlot_eq_getElem : ∀ (doms : List (List Value)) (k : Nat) (h : k < doms.length),
    getSlot doms k = doms[k]'h := by
  intro doms
  induction doms with
  | nil => intro k h; exact absurd h (by simp)
  | cons e es ih =>
      intro k h
      cases k with
      | zero => rfl
      | succ k' =>
          have h' : k' < es.length := by simpa using h
          calc getSlot (e :: es) (k'+1) = getSlot es k' := rfl
            _ = es[k'] := ih k' h'
            _ = (e :: es)[k'+1] := rfl

/-- Membership in the assignments of a single-slot family. -/
theorem mem_allAssigns_single {d : List Value} {a : List Value} :
    a ∈ allAssigns [d] ↔ ∃ v, v ∈ d ∧ a = [v] := by
  cases d with
  | nil => simp [allAssigns]
  | cons w ws =>
      constructor
      · intro h
        obtain ⟨x, hx, a', ha', heq⟩ := (mem_allAssigns_singleton w ws [] a).mp h
        have : a' = [] := by simpa [allAssigns] using ha'
        subst this
        exact ⟨x, hx, heq⟩
      · rintro ⟨v, hv, rfl⟩
        exact (mem_allAssigns_singleton w ws [] [v]).mpr ⟨v, hv, [], by simp [allAssigns], rfl⟩

/-- A dropped-slot list starting with a cons has the drop position in
    range. -/
theorem drop_nonempty_of_cons {doms : List (List Value)} {acc : List Value}
    {rest : List (List Value)} {v : Value} {vs : List Value}
    (hslotstruct : (v :: vs) :: rest = doms.drop acc.length) :
    acc.length < doms.length := by
  cases hlt : Nat.decLt acc.length doms.length with
  | isTrue h => exact h
  | isFalse _ =>
      have hle : doms.length ≤ acc.length := by omega
      have hnil : doms.drop acc.length = [] := List.drop_eq_nil_iff.mpr hle
      rw [hnil] at hslotstruct
      exact absurd hslotstruct (by simp)

/-- Setting a slot and dropping to it: the head of the drop is the new
    domain. -/
theorem drop_setSlot : ∀ (doms : List (List Value)) (k : Nat) (d : List Value),
    k < doms.length → (setSlot doms k d).drop k = d :: doms.drop (k + 1) := by
  intro doms
  induction doms with
  | nil => intro k d h; exact absurd h (by simp)
  | cons e es ih =>
      intro k d h
      cases k with
      | zero => rfl
      | succ k' =>
          have h' : k' < es.length := by simpa using h
          show (e :: setSlot es k' d).drop (k'+1) = d :: (e :: es).drop (k'+1+1)
          rw [List.drop_succ_cons, List.drop_succ_cons]
          exact ih k' d h'

/-- Taking a prefix below the set position ignores the set. -/
theorem take_setSlot_ge : ∀ (doms : List (List Value)) (k : Nat) (d : List Value),
    doms.take k = (setSlot doms k d).take k := by
  intro doms
  induction doms with
  | nil => intro k d; cases k with
    | zero => rfl
    | succ k' => rfl
  | cons e es ih =>
      intro k d
      cases k with
      | zero => rfl
      | succ k' =>
          show e :: es.take k' = e :: (setSlot es k' d).take k'
          rw [ih k' d]

/-- Values of a set slot either come from the set domain or from the
    untouched positions. -/
theorem mem_getSlot_setSlot {doms : List (List Value)} (k : Nat) (d : List Value)
    (hsub : ∀ v, v ∈ d → v ∈ getSlot doms k) :
    ∀ j w, w ∈ getSlot (setSlot doms k d) j → w ∈ getSlot doms j := by
  intro j w hw
  by_cases hjk : j = k
  · subst hjk
    by_cases hlen : j < doms.length
    · rw [getSlot_setSlot_eq doms d j hlen] at hw
      exact hsub w hw
    · have hle : doms.length ≤ j := by omega
      rw [setSlot_eq_self_of_le doms d j hle] at hw
      exact hw
  · rw [getSlot_setSlot_of_ne doms d k j hjk] at hw
    exact hw

/-- **Search agreement** (the technical core): if two leaves agree on
    every complete assignment of the full domains, then the reference
    search produces the same result at every reachable state — the
    search only evaluates its leaf at complete assignments of shrunk
    copies of the full domains. -/
theorem search_agree_aux {f g : List Value → Bool} {full : List (List Value)}
    (hagree : ∀ asg ∈ allAssigns full, f asg = g asg) :
    ∀ (slots : List (List Value)) (acc : List Value),
      SearchInv full slots acc → search f slots acc = search g slots acc := by
  have inv_acc_mem : ∀ {slots : List (List Value)} {acc : List Value},
      slots = [] → SearchInv full slots acc → acc ∈ allAssigns full := by
    intro slots acc hslots ⟨doms, hlen, hsub, hslots', hacc⟩
    have hdropnil : doms.drop acc.length = [] := by rw [← hslots', hslots]
    have hle : doms.length ≤ acc.length := List.drop_eq_nil_iff.mp hdropnil
    have htake : doms.take acc.length = doms := take_all_le _ _ hle
    exact allAssigns_mono doms full ⟨hlen, hsub⟩ acc (htake ▸ hacc)
  intro slots acc
  induction slots, acc using search.induct (leaf := f) with
  | case1 acc hleaf =>
      intro hinv
      have haccfull := inv_acc_mem rfl hinv
      have hfg : g acc = true := by rw [← hagree acc haccfull]; exact hleaf
      show search f [] acc = search g [] acc
      simp only [search, hleaf, hfg]
  | case2 acc hleaf =>
      intro hinv
      have haccfull := inv_acc_mem rfl hinv
      cases hf : f acc with
      | true => exact absurd hf hleaf
      | false =>
          have hfg : g acc = false := by rw [← hagree acc haccfull]; exact hf
          show search f [] acc = search g [] acc
          simp only [search, hf, hfg]
  | case3 tail x => intro _; simp only [search]
  | case4 v vs rest acc a hs ih1 =>
      intro hinv
      obtain ⟨doms, hlen, hsub, hslots, hacc⟩ := hinv
      have hslotstruct : (v :: vs) :: rest = doms.drop acc.length := hslots
      have hlenacc : acc.length < doms.length := drop_nonempty_of_cons hslotstruct
      have hget : getSlot doms acc.length = v :: vs := by
        have h1 : getSlot (doms.drop acc.length) 0 = v :: vs := by
          rw [← hslotstruct]; rfl
        rw [getSlot_drop_zero] at h1
        exact h1
      have hv : v ∈ getSlot doms acc.length := by rw [hget]; exact List.mem_cons_self
      have hlenaccv : (acc ++ [v]).length = acc.length + 1 := by
        rw [List.length_append, List.length_singleton]
      have haccv : (acc ++ [v]) ∈ allAssigns (doms.take (acc ++ [v]).length) := by
        rw [hlenaccv]
        have h1 : doms.take (acc.length + 1) =
            doms.take acc.length ++ doms[acc.length]?.toList := List.take_add_one
        have h2 : doms[acc.length]? = some (getSlot doms acc.length) := by
          rw [List.getElem?_eq_some_iff]
          exact ⟨hlenacc, (getSlot_eq_getElem doms acc.length hlenacc).symm⟩
        rw [h1, h2, Option.toList_some, allAssigns_append]
        exact ⟨acc, hacc, [v], mem_allAssigns_single.mpr ⟨v, hv, rfl⟩, rfl⟩
      have hdrop : rest = doms.drop (acc ++ [v]).length := by
        rw [List.length_append, List.length_singleton]
        show rest = doms.drop (acc.length + 1)
        rw [← List.drop_drop (i := 1) (j := acc.length), ← hslotstruct]
        rfl
      have hinv1 : SearchInv full rest (acc ++ [v]) :=
        ⟨doms, hlen, hsub, hdrop, haccv⟩
      have hg : search g rest (acc ++ [v]) = some a := by rw [← ih1 hinv1]; exact hs
      show search f ((v :: vs) :: rest) acc = search g ((v :: vs) :: rest) acc
      simp only [search, hs, hg]
  | case5 v vs rest acc hnone ih1 ih2 =>
      intro hinv
      obtain ⟨doms, hlen, hsub, hslots, hacc⟩ := hinv
      have hslotstruct : (v :: vs) :: rest = doms.drop acc.length := hslots
      have hlenacc : acc.length < doms.length := drop_nonempty_of_cons hslotstruct
      have hget : getSlot doms acc.length = v :: vs := by
        have h1 : getSlot (doms.drop acc.length) 0 = v :: vs := by
          rw [← hslotstruct]; rfl
        rw [getSlot_drop_zero] at h1
        exact h1
      have hv : v ∈ getSlot doms acc.length := by rw [hget]; exact List.mem_cons_self
      have hlenaccv : (acc ++ [v]).length = acc.length + 1 := by
        rw [List.length_append, List.length_singleton]
      have haccv : (acc ++ [v]) ∈ allAssigns (doms.take (acc ++ [v]).length) := by
        rw [hlenaccv]
        have h1 : doms.take (acc.length + 1) =
            doms.take acc.length ++ doms[acc.length]?.toList := List.take_add_one
        have h2 : doms[acc.length]? = some (getSlot doms acc.length) := by
          rw [List.getElem?_eq_some_iff]
          exact ⟨hlenacc, (getSlot_eq_getElem doms acc.length hlenacc).symm⟩
        rw [h1, h2, Option.toList_some, allAssigns_append]
        exact ⟨acc, hacc, [v], mem_allAssigns_single.mpr ⟨v, hv, rfl⟩, rfl⟩
      have hdrop : rest = doms.drop (acc ++ [v]).length := by
        rw [List.length_append, List.length_singleton]
        show rest = doms.drop (acc.length + 1)
        rw [← List.drop_drop (i := 1) (j := acc.length), ← hslotstruct]
        rfl
      have hinv1 : SearchInv full rest (acc ++ [v]) :=
        ⟨doms, hlen, hsub, hdrop, haccv⟩
      have hg1 : search g rest (acc ++ [v]) = none := by rw [← ih1 hinv1]; exact hnone
      have hdrop' : (setSlot doms acc.length vs).drop acc.length = vs :: rest := by
        rw [drop_setSlot doms acc.length vs hlenacc]
        congr 1
        rw [← hlenaccv]
        exact hdrop.symm
      have htake' : (setSlot doms acc.length vs).take acc.length = doms.take acc.length :=
        (take_setSlot_ge doms acc.length vs).symm
      have hsub' : ∀ k w, w ∈ getSlot (setSlot doms acc.length vs) k → w ∈ getSlot full k := by
        intro k w hw
        have hw' : w ∈ getSlot doms k :=
          mem_getSlot_setSlot acc.length vs
            (doms := doms) (fun v' hv' => by
              rw [hget]; exact List.mem_cons_of_mem _ hv') k w hw
        exact hsub k w hw'
      have hinv2 : SearchInv full (vs :: rest) acc :=
        ⟨setSlot doms acc.length vs, by rw [setSlot_length]; exact hlen, hsub',
          hdrop'.symm, htake' ▸ hacc⟩
      show search f ((v :: vs) :: rest) acc = search g ((v :: vs) :: rest) acc
      simp only [search, hnone, hg1]
      exact ih2 hinv2

/-- **Root agreement**: two leaves agreeing on every complete
    assignment of the slots produce the same reference search from
    the root. -/
theorem search_agree_root {f g : List Value → Bool} (slots : List (List Value))
    (h : ∀ asg ∈ allAssigns slots, f asg = g asg) :
    search f slots [] = search g slots [] :=
  search_agree_aux h slots [] (searchInv_root slots)

/-! ## NoGood-checked search (the pruning consumer) -/

/-- The leaf composed with a NoGood list: the original leaf, minus
    assignments violated by some learned NoGood. -/
def ngLeaf (leaf : List Value → Bool) (ngs : List NoGood) (asg : List Value) : Bool :=
  leaf asg && !(ngs.any (fun ng => ng.violatedB asg))

/-- **The NoGood-checked search**: exactly the reference search on the
    leaf composed with the NoGood list (a wrapper — soundness needs no
    new induction). -/
def nogoodSearch (leaf : List Value → Bool) (ngs : List NoGood) :
    List (List Value) → List Value → Option (List Value) :=
  search (ngLeaf leaf ngs)

/-- Entailed NoGoods leave the composed leaf unchanged on the scope:
    the pruning is correctness-neutral exactly when every NoGood of
    the list is entailed. -/
theorem ngLeaf_eq_of_entailed {leaf : List Value → Bool} {ngs : List NoGood}
    {slots : List (List Value)}
    (hent : ∀ ng ∈ ngs, ng.EntailedOn leaf slots) :
    ∀ asg ∈ allAssigns slots, ngLeaf leaf ngs asg = leaf asg := by
  intro asg hasg
  unfold ngLeaf
  cases hleaf : leaf asg with
  | false => rfl
  | true =>
      rw [Bool.true_and]
      cases hany : (ngs.any (fun ng => ng.violatedB asg)) with
      | true =>
          obtain ⟨ng, hng, hvio⟩ := List.any_eq_true.mp hany
          have hv : ng.Violated asg := NoGood.violatedB_iff.mp hvio
          exact absurd hv (hent ng hng asg hasg hleaf)
      | false => rfl

/-- **The agreement theorem** (PLAN 6.6's requirement: learning is
    correctness-neutral when entailed): if every NoGood of the list
    is entailed by the leaf over the slot domains, the NoGood-checked
    search is *exactly* the reference search — the pruning changes
    nothing semantically. -/
theorem nogoodSearch_agrees {leaf : List Value → Bool} {ngs : List NoGood}
    {slots : List (List Value)}
    (hent : ∀ ng ∈ ngs, ng.EntailedOn leaf slots) :
    nogoodSearch leaf ngs slots [] = search leaf slots [] := by
  unfold nogoodSearch
  exact search_agree_root slots (ngLeaf_eq_of_entailed hent)

/-- A non-entailed NoGood can prune a leaf-passing assignment — the
    reason the entailment discipline matters.  (Used by the test
    suite to witness that the agreement theorem's hypothesis is not
    vacuous.) -/
theorem ngLeaf_prunes_of_violated {leaf : List Value → Bool} {ng : NoGood}
    {asg : List Value} (hleaf : leaf asg = true) (hvio : ng.Violated asg) :
    ngLeaf leaf [ng] asg = false := by
  unfold ngLeaf
  rw [hleaf, Bool.true_and]
  have hany : ([ng].any (fun ng' => ng'.violatedB asg)) = true :=
    List.any_eq_true.mpr ⟨ng, List.mem_singleton.mpr rfl, NoGood.violatedB_iff.mpr hvio⟩
  rw [hany]
  rfl

/-! ## Learning from failed subtrees -/

/-- Membership in `getSlot` of the dropped family: a value of slot
    `n + j` of the full family is a value of slot `j` of the dropped
    family. -/
theorem getSlot_drop_mem : ∀ (ds : List (List Value)) (n j : Nat) (w : Value),
    w ∈ getSlot ds (n + j) → w ∈ getSlot (ds.drop n) j := by
  intro ds
  induction ds with
  | nil =>
      intro n j w hw
      cases n with
      | zero => exact hw
      | succ n' =>
          show w ∈ getSlot (List.drop (n' + 1) []) j
          rw [List.drop_nil]
          exact hw
  | cons e es ih =>
      intro n j w hw
      cases n with
      | zero =>
          show w ∈ getSlot ((e :: es).drop 0) j
          rw [Nat.zero_add] at hw
          rw [List.drop_zero]
          exact hw
      | succ n' =>
          show w ∈ getSlot ((e :: es).drop (n' + 1)) j
          rw [List.drop_succ_cons]
          have hgs : getSlot (e :: es) (n' + 1 + j) = getSlot es (n' + j) := by
            have h : n' + 1 + j = (n' + j) + 1 := by omega
            rw [h]
            rfl
          rw [hgs] at hw
          exact ih n' j w hw

/-- **The subtree entailment theorem** (the learning half's deliverable):
    when the subtree below the decision prefix `pre` is exhausted
    fruitlessly — every completion of `pre` over the remaining slots
    fails the leaf — the decision-trail NoGood `pairsOf pre` is
    entailed by the leaf over the root scope: no leaf-passing complete
    assignment of the full domains agrees with all of `pre`'s
    decisions.  This is exactly PLAN 6.6's "entailed by the original
    model and the decisions above its valid scope" for the root scope:
    the decisions above are empty, and the subtree failure is the
    model-entailment evidence.  The remaining slots must be the *tail*
    of the full slot family (`rest = full.drop pre.length`): the
    searched subtree is a subtree of the original search space, which
    is how the learning search below calls it. -/
theorem failedSubtree_entailed {leaf : List Value → Bool}
    {full : List (List Value)} {pre : List Value}
    (hfail : ∀ a ∈ allAssigns (full.drop pre.length), leaf (pre ++ a) = false)
    (asg : List Value) (hasg : asg ∈ allAssigns full) (hleaf : leaf asg = true) :
    ¬ (pairsOf pre).Violated asg := by
  intro hvio
  obtain ⟨hspec1, hspec2⟩ := allAssigns_spec full asg hasg
  have hvio' : ∀ k, k < pre.length → asg[k]? = pre[k]? := by
    intro k hk
    have := (violated_pairsAux_iff (pre := pre) (asg := asg) (i := 0)).mp hvio k hk
    simpa using this
  have hlenle : pre.length ≤ asg.length := by
    cases Nat.decLt asg.length pre.length with
    | isFalse h => omega
    | isTrue hlt =>
      have hcon : ¬ (pre.length ≤ asg.length) := by omega
      have hpos := hvio' asg.length (by omega)
      have hnone : asg[asg.length]? = none := List.getElem?_eq_none_iff.mpr (by omega)
      rw [hnone] at hpos
      have hw : pre[asg.length]? = some (pre[asg.length]'(by omega)) :=
        List.getElem?_eq_some_iff.mpr ⟨by omega, rfl⟩
      rw [hpos.symm] at hw
      exact absurd hw (by simp)
  obtain ⟨suf, rfl⟩ := violated_pairsOf_split hvio hlenle
  -- suf is a complete assignment of full.drop pre.length
  have hdroplen : (full.drop pre.length).length = full.length - pre.length := by
    rw [List.length_drop]
  have hsuf : suf ∈ allAssigns (full.drop pre.length) := by
    refine allAssigns_intro (full.drop pre.length) suf ?_ ?_
    · rw [List.length_append] at hspec1
      rw [List.length_drop]
      omega
    · intro k v hv
      -- v was picked by asg at position pre.length + k, so v ∈ getSlot full (pre.length + k);
      -- and getSlot (full.drop pre.length) k = getSlot full (pre.length + k) when in range,
      -- [] (= getSlot full position) when out of range — in that case v ∈ [] is absurd, so
      -- we first establish v ∈ getSlot full (pre.length + k) and then bridge.
      have hget2 : (pre ++ suf)[pre.length + k]? = some v := by
        rw [List.getElem?_append, if_neg (by omega : ¬ pre.length + k < pre.length),
          Nat.add_sub_cancel_left]
        exact hv
      have hval : v ∈ getSlot full (pre.length + k) := hspec2 _ v hget2
      -- bridge: membership in getSlot full (pre.length + k) implies membership in
      -- getSlot (full.drop pre.length) k — via the drop structure of getSlot.
      exact getSlot_drop_mem full pre.length k v hval
  -- the completion fails the leaf — contradiction with hleaf
  have hfailasg : leaf (pre ++ suf) = false := hfail suf hsuf
  rw [hleaf] at hfailasg
  exact absurd hfailasg (by simp)

/-! ## The learning loop -/

/-- Entailment at a search node: every leaf-passing assignment of the
    node's scope — the completions `acc ++ a` with `a` a complete
    assignment of the remaining slots — is not violated by the
    NoGood.  This is PLAN 6.6's "the decisions above its valid scope"
    made precise: the entry NoGoods of the learning search are
    entailed at the root node (no decisions above), and the theorem
    below transports that along the search tree. -/
def NoGood.EntailedAt (ng : NoGood) (leaf : List Value → Bool)
    (slots : List (List Value)) (acc : List Value) : Prop :=
  ∀ a ∈ allAssigns slots, leaf (acc ++ a) = true → ¬ ng.Violated (acc ++ a)

/-- Split of an assignment of a cons-headed slot family. -/
theorem mem_allAssigns_cons_split {vs : List Value} {rest : List (List Value)}
    {a : List Value} (ha : a ∈ allAssigns (vs :: rest)) :
    ∃ w, w ∈ vs ∧ ∃ tail, tail ∈ allAssigns rest ∧ a = w :: tail := by
  cases vs with
  | nil => exact absurd ha (by simp [allAssigns])
  | cons u us =>
      obtain ⟨x, hx, a', ha', heq⟩ := (mem_allAssigns_singleton u us rest a).mp ha
      refine ⟨x, ?_, a', ha', heq⟩
      rcases List.mem_cons.mp hx with heq2 | hin
      · exact heq2 ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ hin

/-- Entry NoGoods remain entailed at the first-branch child node. -/
theorem entailedAt_first {ng : NoGood} {leaf : List Value → Bool}
    {v : Value} {vs : List Value} {rest : List (List Value)} {acc : List Value}
    (h : ng.EntailedAt leaf ((v :: vs) :: rest) acc) :
    ng.EntailedAt leaf rest (acc ++ [v]) := by
  intro a ha hleaf
  have hmem : (v :: a) ∈ allAssigns ((v :: vs) :: rest) :=
    (mem_allAssigns_singleton v vs rest (v :: a)).mpr
      ⟨v, List.mem_cons_self, a, ha, rfl⟩
  have haccv : acc ++ [v] ++ a = acc ++ v :: a := by
    simp [List.append_assoc]
  rw [haccv]
  exact h (v :: a) hmem (by
    show leaf (acc ++ v :: a) = true
    rw [← haccv]
    exact hleaf)

/-- Entry NoGoods remain entailed at the retry node (the domain
    shrank but its assignments are assignments of the parent). -/
theorem entailedAt_retry {ng : NoGood} {leaf : List Value → Bool}
    {v : Value} {vs : List Value} {rest : List (List Value)} {acc : List Value}
    (h : ng.EntailedAt leaf ((v :: vs) :: rest) acc) :
    ng.EntailedAt leaf (vs :: rest) acc := by
  intro a ha hleaf
  exact h a (allAssigns_subset_cons v vs rest a ha) hleaf

/-- **The learned NoGood is entailed at the retry scope**: given the
    failed-subtree evidence (every completion below `acc ++ [v]` fails
    the leaf), the decision-trail NoGood `pairsOf (acc ++ [v])`
    excludes no leaf-passing assignment of the retry node — PLAN
    6.6's pruning licence, produced by the learning itself. -/
theorem learned_entailed {leaf : List Value → Bool} {v : Value} {vs : List Value}
    {rest : List (List Value)} {acc : List Value}
    (hsub : ∀ a ∈ allAssigns rest, leaf ((acc ++ [v]) ++ a) = false) :
    (pairsOf (acc ++ [v])).EntailedAt leaf (vs :: rest) acc := by
  intro a ha hleaf hvio
  obtain ⟨w, hw, tail, htail, heq⟩ := mem_allAssigns_cons_split ha
  subst heq
  have hget : (acc ++ w :: tail)[acc.length]? = some w := by
    rw [List.getElem?_append, if_neg (by simp : ¬ acc.length < acc.length),
      Nat.sub_self]
    rfl
  have hagree : ∀ k, k < (acc ++ [v]).length → (acc ++ w :: tail)[k]? = (acc ++ [v])[k]? :=
    fun k hk => by
      simpa using
        (violated_pairsAux_iff (pre := acc ++ [v]) (asg := acc ++ w :: tail) (i := 0)).mp hvio k hk
  have h1 := hagree acc.length (by
    rw [List.length_append, List.length_singleton]; omega)
  rw [hget] at h1
  have hgetv : (acc ++ [v])[acc.length]? = some v := by
    rw [List.getElem?_append, if_neg (by simp : ¬ acc.length < acc.length),
      Nat.sub_self]
    rfl
  rw [hgetv] at h1
  have hwv : w = v := Option.some.inj h1
  subst hwv
  have hfalse : leaf (acc ++ [w] ++ tail) = false := hsub tail htail
  have heq : acc ++ [w] ++ tail = acc ++ w :: tail := by
    simp [List.append_assoc]
  rw [heq] at hfalse
  rw [hleaf] at hfalse
  exact absurd hfalse (by simp)

/-- **The learning search**: structurally the reference `search`, but
    carrying a NoGood list: at a leaf the composed leaf is checked
    (the leaf *and* no learned NoGood violated); when a first-branch
    subtree fails, its decision trail `pairsOf (acc ++ [v])` is learned
    and prunes the remainder of the search.  The fuel bounds the
    number of learning steps — a pure termination device (a smaller
    fuel weakens pruning, never soundness): fuel 0 delegates to the
    NoGood-checked reference search. -/
def lsearch (leaf : List Value → Bool) :
    Nat → List (List Value) → List Value → List NoGood → Option (List Value)
  | _, [], acc, ngs =>
      if leaf acc && !(ngs.any (fun ng => ng.violatedB acc)) then some acc else none
  | _, [] :: _, _, _ => none
  | 0, (v :: vs) :: rest, acc, ngs =>
      search (ngLeaf leaf ngs) ((v :: vs) :: rest) acc
  | fuel + 1, (v :: vs) :: rest, acc, ngs =>
      match lsearch leaf fuel rest (acc ++ [v]) ngs with
      | some a => some a
      | none => lsearch leaf fuel (vs :: rest) acc (pairsOf (acc ++ [v]) :: ngs)
termination_by fuel' slots _ _ => (fuel', slotsMeasure slots)
decreasing_by
  all_goals
    simp only [slotsMeasure, List.foldr_cons, List.length_cons]
    omega

/-- **The fuel-0 wrapper**: with the learning budget exhausted, the
    learning search is exactly the reference search on the plain leaf
    (the entry NoGood list is empty at the wrapper). -/
def learnSearch (fuel : Nat) (leaf : List Value → Bool)
    (slots : List (List Value)) : Option (List Value) :=
  lsearch leaf fuel slots [] []

/-- The composed leaf only tightens the original. -/
theorem ngLeaf_passes {leaf : List Value → Bool} {ngs : List NoGood} {asg : List Value}
    (h : ngLeaf leaf ngs asg = true) : leaf asg = true := by
  unfold ngLeaf at h
  rw [Bool.and_eq_true] at h
  exact h.1

/-- **SAT soundness of the learning search** (unconditional, for
    every fuel, accumulator, and entry NoGood list): any returned
    assignment passes the leaf — the composed leaf only tightens the
    original, and the learned NoGoods only remove candidates. -/
theorem lsearch_some (leaf : List Value → Bool) :
    ∀ (fuel : Nat) (slots : List (List Value)) (acc : List Value) (ngs : List NoGood)
      (r : List Value),
      lsearch leaf fuel slots acc ngs = some r → leaf r = true := by
  intro fuel slots acc ngs
  induction fuel, slots, acc, ngs using lsearch.induct (leaf := leaf) with
  | case1 x acc' ngs' hcheck =>
      intro r h
      simp only [lsearch] at h
      rw [if_pos hcheck] at h
      have hleaf : leaf acc' = true := by
        rw [Bool.and_eq_true] at hcheck; exact hcheck.1
      rw [Option.some.inj h] at hleaf
      exact hleaf
  | case2 x acc' ngs' hcheck =>
      intro r h
      simp only [lsearch, if_neg hcheck] at h
      exact absurd h (by simp)
  | case3 x tail y z => intro r h; simp only [lsearch] at h; exact absurd h (by simp)
  | case4 v vs rest acc' ngs' =>
      intro r h
      simp only [lsearch] at h
      obtain ⟨a, ha, hrfl, hleaf2⟩ :=
        search_some (ngLeaf leaf ngs') ((v :: vs) :: rest) acc' r h
      unfold ngLeaf at hleaf2
      rw [Bool.and_eq_true] at hleaf2
      rw [hrfl]
      exact hleaf2.1
  | case5 fuel' v vs rest acc' ngs' a hs ih1 =>
      intro r h
      simp only [lsearch] at h
      rw [hs] at h
      have hra : a = r := Option.some.inj h
      subst hra
      exact ih1 a hs
  | case6 fuel' v vs rest acc' ngs' hnone ih1 ih2 =>
      intro r h
      simp only [lsearch] at h
      rw [hnone] at h
      exact ih2 r h

/-- **The none-side master theorem of the learning search** (the
    entailment discipline internalized): a `none` verdict at a node
    whose entry NoGoods are entailed there means every completion of
    the node fails the leaf.  The proof transports the entailment
    along the search tree (`entailedAt_first`, `entailedAt_retry`)
    and — the heart — shows each *learned* NoGood is entailed at the
    retry node from the failed-subtree evidence (`learned_entailed`).
    At the wrapper's entry the NoGood list is empty, so the
    entailment hypothesis is vacuous and the top-level theorem is
    unconditional. -/
def LSNone (leaf : List Value → Bool) (slots : List (List Value))
    (acc : List Value) (ngs : List NoGood) : Prop :=
  (∀ ng ∈ ngs, ng.EntailedAt leaf slots acc) →
    ∀ a ∈ allAssigns slots, leaf (acc ++ a) = false

theorem lsearch_none' (leaf : List Value → Bool) :
    ∀ (fuel : Nat) (slots : List (List Value)) (acc : List Value) (ngs : List NoGood),
      lsearch leaf fuel slots acc ngs = none → LSNone leaf slots acc ngs := by
  intro fuel slots acc ngs
  induction fuel, slots, acc, ngs using lsearch.induct (leaf := leaf) with
  | case1 x acc' ngs' hcheck =>
      intro hnone
      simp only [lsearch, if_pos hcheck] at hnone
      exact absurd hnone (by simp)
  | case2 x acc' ngs' hcheck =>
      intro hnone
      unfold LSNone
      intro hent a ha
      have haNil : a = [] := by simpa [allAssigns] using ha
      subst haNil
      have hleaf : leaf acc' = false := by
        cases hleaf : leaf acc' with
        | false => rfl
        | true =>
            exfalso
            have hany : (ngs'.any (fun ng => ng.violatedB acc')) = true := by
              cases hany : (ngs'.any (fun ng => ng.violatedB acc')) with
              | true => rfl
              | false =>
                  have hcomp : (leaf acc' && !(ngs'.any (fun ng => ng.violatedB acc'))) = true := by
                    rw [hleaf, hany]; rfl
                  exact absurd hcomp hcheck
            obtain ⟨ng, hng, hvio⟩ := List.any_eq_true.mp hany
            have hv : ng.Violated acc' := NoGood.violatedB_iff.mp hvio
            have hleaf2 : leaf (acc' ++ []) = true := by rw [List.append_nil]; exact hleaf
            have hcontra : ¬ ng.Violated (acc' ++ []) :=
              hent ng hng [] (by simp [allAssigns]) hleaf2
            rw [List.append_nil] at hcontra
            exact absurd hv hcontra
      show leaf (acc' ++ []) = false
      rw [List.append_nil]
      exact hleaf
  | case3 x tail y z =>
      intro _
      unfold LSNone
      intro _ a ha
      exact absurd ha (by simp [allAssigns])
  | case4 v vs rest acc' ngs' =>
      intro hnone
      unfold LSNone
      intro hent a ha
      simp only [lsearch] at hnone
      have hsn := search_none (ngLeaf leaf ngs') ((v :: vs) :: rest) acc' hnone a ha
      cases hleaf : leaf (acc' ++ a) with
      | false => rfl
      | true =>
          exfalso
          have hany : (ngs'.any (fun ng => ng.violatedB (acc' ++ a))) = true := by
            cases hany : (ngs'.any (fun ng => ng.violatedB (acc' ++ a))) with
            | true => rfl
            | false =>
                have hcomp : ngLeaf leaf ngs' (acc' ++ a) = true := by
                  unfold ngLeaf
                  rw [hleaf, hany]; rfl
                rw [hsn] at hcomp
                exact absurd hcomp (by simp)
          obtain ⟨ng, hng, hvio⟩ := List.any_eq_true.mp hany
          have hv : ng.Violated (acc' ++ a) := NoGood.violatedB_iff.mp hvio
          exact absurd hv (hent ng hng a ha hleaf)
  | case5 fuel' v vs rest acc' ngs' a hs ih1 =>
      intro hnone
      simp only [lsearch] at hnone
      rw [hs] at hnone
      exact absurd hnone (by simp)
  | case6 fuel' v vs rest acc' ngs' hnone ih1 ih2 =>
      intro hnodeNone hnodeEnt
      -- the node's none forces the retry's none
      have hretry : lsearch leaf fuel' (vs :: rest) acc'
          (pairsOf (acc' ++ [v]) :: ngs') = none := by
        simp only [lsearch, hnone] at hnodeNone
        exact hnodeNone
      -- the entry entailment transports to both children
      have hent1 : ∀ ng ∈ ngs', ng.EntailedAt leaf rest (acc' ++ [v]) :=
        fun ng hng => entailedAt_first (hnodeEnt ng hng)
      have hall1 : ∀ a' ∈ allAssigns rest, leaf ((acc' ++ [v]) ++ a') = false :=
        fun a' ha' => ih1 hnone hent1 a' ha'
      have hent2 : ∀ ng ∈ (pairsOf (acc' ++ [v]) :: ngs'),
          ng.EntailedAt leaf (vs :: rest) acc' := by
        intro ng hng
        rcases List.mem_cons.mp hng with heq | hin
        · subst heq
          exact learned_entailed hall1
        · exact entailedAt_retry (hnodeEnt ng hin)
      have hres2 := ih2 hretry hent2
      -- conclude at the parent scope: split the assignment and merge the two halves
      unfold LSNone at hres2
      intro a ha
      obtain ⟨w, hw, tail, htail, heq⟩ := (mem_allAssigns_singleton v vs rest a).mp ha
      subst heq
      rcases List.mem_cons.mp hw with rfl | hwin
      · -- w = v: the assignment is a completion below the failed subtree
        have hfalse : leaf ((acc' ++ [w]) ++ tail) = false := hall1 tail htail
        have hconv : acc' ++ [w] ++ tail = acc' ++ w :: tail := by
          simp [List.append_assoc]
        show leaf (acc' ++ w :: tail) = false
        rw [← hconv]
        exact hfalse
      · -- w ∈ vs: the retry's conclusion covers it
        have hmem : (w :: tail) ∈ allAssigns (vs :: rest) := by
          cases vs with
          | nil => exact absurd hwin (by simp)
          | cons u us =>
              exact (mem_allAssigns_singleton u us rest (w :: tail)).mpr
                ⟨w, hwin, tail, htail, rfl⟩
        exact hres2 (w :: tail) hmem

/-- **UNSAT soundness of the learning search at the wrapper**
    (unconditional: the entry NoGood list is empty, so the entailment
    discipline holds vacuously, and every learned NoGood is entailed
    by construction inside `lsearch_none'`): a `none` verdict means
    every complete assignment of the slot domains fails the leaf. -/
theorem learnSearch_none (fuel : Nat) (leaf : List Value → Bool)
    (slots : List (List Value))
    (h : learnSearch fuel leaf slots = none) :
    ∀ a ∈ allAssigns slots, leaf a = false := by
  have h' := lsearch_none' leaf fuel slots [] [] h
  intro a ha
  have := h' (fun ng hng => absurd hng (by simp)) a (by
    show a ∈ allAssigns ([] ++ slots)
    simp only [List.nil_append]
    exact ha)
  simpa using this

/-- **SAT soundness of `learnSearch`** (wrapper form). -/
theorem learnSearch_some (fuel : Nat) (leaf : List Value → Bool)
    (slots : List (List Value)) (r : List Value)
    (h : learnSearch fuel leaf slots = some r) :
    leaf r = true :=
  lsearch_some leaf fuel slots [] [] r h

/-- **Fuel 0 is the plain reference search**: the learning loop with
    its learning budget exhausted does not check or learn any NoGood
    (the wrapper enters with an empty list). -/
theorem learnSearch_zero (leaf : List Value → Bool) (slots : List (List Value)) :
    learnSearch 0 leaf slots = search leaf slots [] := by
  unfold learnSearch lsearch
  have hfun : (fun asg => leaf asg && !(([] : List NoGood).any (fun ng => ng.violatedB asg))) = leaf := by
    funext asg
    show (leaf asg && !(([] : List NoGood).any (fun ng => ng.violatedB asg))) = leaf asg
    cases hleaf : leaf asg with
    | false => rfl
    | true => rfl
  cases slots with
  | nil =>
      have h1 : (fun (asg : List Value) => leaf asg && !(([] : List NoGood).any (fun ng => ng.violatedB asg))) [] = leaf [] := by
        show (leaf [] && !(([] : List NoGood).any (fun ng => ng.violatedB []))) = leaf []
        cases hleaf : leaf [] with
        | false => rfl
        | true => rfl
      show (if leaf [] && !(([] : List NoGood).any (fun ng => ng.violatedB [])) then some [] else none) = search leaf [] []
      simp only [search, h1]
  | cons d ds =>
      cases d with
      | nil =>
          show (none : Option (List Value)) = search leaf (([] : List Value) :: ds) []
          simp only [search]
      | cons v vs =>
          show search (fun asg => leaf asg && !(([] : List NoGood).any (fun ng => ng.violatedB asg))) ((v :: vs) :: ds) [] = search leaf ((v :: vs) :: ds) []
          rw [hfun]

end LeanFzn.Solver
